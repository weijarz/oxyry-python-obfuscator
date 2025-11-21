#!/usr/bin/env python3
import sys
if sys.implementation.name != 'cpython' or sys.version_info.major != 3 or \
        sys.version_info.minor != 12: # pragma: no cover
    print('error: CPython 3.7.x is required to run this program', file=sys.stderr)
    sys.exit(1)

import ast
import io
import os
import symtable
import warnings
import tokenize
import itertools
import argparse
import unicodedata
import logging
from keyword import iskeyword
import random
from collections import namedtuple
import base64
import re
from pathlib import Path


__all__ = ['ObfuscateOptions', 'obfuscate', 'main', 'DEBUG', 'SRC_INFO']
SRC_INFO = True
DEBUG = int(os.environ.get('OXYRYPYOB_DEBUG', 0))

logging.basicConfig(
    level=os.environ.get('OXYRYPYOB_LOG', 'ERROR'),
    format='[%(levelname)s]%(message)s'
)

BUILTINS = (
    # from https://docs.python.org/3/library

    # functions
    'abs', 'delattr', 'hash', 'memoryview', 'set',
    'all', 'dict', 'help', 'min', 'setattr',
    'any', 'dir', 'hex', 'next', 'slice',
    'ascii', 'divmod', 'id', 'object', 'sorted',
    'bin', 'enumerate', 'input', 'oct', 'staticmethod',
    'bool', 'eval', 'int', 'open', 'str',
    'breakpoint', 'exec', 'isinstance', 'ord', 'sum',
    'bytearray', 'filter', 'issubclass', 'pow', 'super',
    'bytes', 'float', 'iter', 'print', 'tuple',
    'callable', 'format', 'len', 'property', 'type',
    'chr', 'frozenset', 'list', 'range', 'vars',
    'classmethod', 'getattr', 'locals', 'repr', 'zip',
    'compile', 'globals', 'map', 'reversed', '__import__',
    'complex', 'hasattr', 'max', 'round', 'breakpoint',

    # constants
    'False', 'True', 'None', 'NotImplemented', 'Ellipsis', '__debug__', 'quit',
    'exit', 'copyright', 'credits', 'license',

    # exceptions
    'BaseException', 'SystemExit', 'KeyboardInterrupt', 'GeneratorExit', 'Exception',
    'StopIteration', 'ArithmeticError', 'FloatingPointError', 'OverflowError',
    'ZeroDivisionError', 'AssertionError', 'AttributeError', 'BufferError', 'EOFError',
    'ImportError', 'LookupError', 'IndexError', 'KeyError', 'MemoryError', 'NameError',
    'UnboundLocalError', 'OSError', 'BlockingIOError', 'ChildProcessError',
    'ConnectionError', 'BrokenPipeError', 'ConnectionAbortedError',
    'ConnectionRefusedError', 'ConnectionResetError', 'FileExistsError',
    'FileNotFoundError', 'InterruptedError', 'IsADirectoryError', 'NotADirectoryError',
    'PermissionError', 'ProcessLookupError', 'TimeoutError', 'ReferenceError',
    'RuntimeError', 'NotImplementedError', 'SyntaxError', 'IndentationError', 'TabError',
    'SystemError', 'TypeError', 'ValueError', 'UnicodeError', 'UnicodeDecodeError',
    'UnicodeEncodeError', 'UnicodeTranslateError', 'Warning', 'DeprecationWarning',
    'PendingDeprecationWarning', 'RuntimeWarning', 'SyntaxWarning', 'UserWarning',
    'FutureWarning', 'ImportWarning', 'UnicodeWarning', 'BytesWarning', 'ResourceWarning',

    # special
    '_', '__',
)

class NodeVisitorMetaclass(type):

     def __new__(cls, name, bases, namespace, **kwds):
        result = type.__new__(cls, name, bases, namespace)
        for funcname in dir(result):
            match = re.match(r'on_([\w]+)$', funcname)
            if match:
                node_classname = match.group(1)
                assert hasattr(ast, node_classname), node_classname
        return result

class NodeVisitor(metaclass=NodeVisitorMetaclass):

    def visit(self, node):
        method = 'on_' + node.__class__.__name__
        visitor = getattr(self, method, self.on)
        return visitor(node)

    def on(self, node):
        for field, value in ast.iter_fields(node):
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.AST):
                        self.visit(item)
            elif isinstance(value, ast.AST):
                self.visit(value)

Position = namedtuple('Position', 'lineno col_offset')

class ObName:

    def __init__(self, name, nsid, node, start, keyword, offset, in_formatted_string):
        self.name = name
        self.nsid = nsid # scope key for this name
        self.node = node # main node

        # Position of this name
        # for source: from foo import bar as bar2
        #     start, keyword, offset => name
        #     ((1, 0), None, 0) ==> 'foo'
        #     ((1, 0), 'as', 0) ==> 'bar2'
        #     ((1, 0), None, 1) ==> 'bar'
        self.start = start # in byte offset
        self.keyword = keyword
        self.offset = offset
        self.abspos = None
        self.in_formatted_string = in_formatted_string

        self.translated = False

    def __str__(self): # pragma: no cover
        return str(self.__dict__)

class ObNameCollector(NodeVisitor):

    def __init__(self, tables, module_public_names, options):
        self.__tables = tables
        self.__module_public_names = module_public_names
        self.__options = options
        self.__table_index = 0
        self.__scope = [] # (node, table)...; current scope
        self.__current_class = [] # (class_name, id)...
        self.__preserved_args = {} # table -> set(name: str...)
        self.__obnames = []
        self.__in_formatted_string = 0

    def get_result(self):
        assert self.__table_index == len(self.__tables)
        return self.__obnames

    def on_Module(self, module):
        table = self.__next_table(module)
        assert table.get_type() == 'module'
        self.__top_table = table
        self.__push_table(module, table)
        self.on(module)
        self.__pop_table()

    def on_ClassDef(self, classdef):
        # table order: bases > keywords > starargs > kwargs > decorators

        self.__visit_list(classdef.bases)
        self.__visit_list(classdef.keywords)
        # self.__visit_if_presents(classdef.starargs)
        # self.__visit_if_presents(classdef.kwargs)
        self.__visit_list(classdef.decorator_list)

        self.__add_name(classdef.name, classdef, keyword='class')

        table = self.__next_table(classdef)
        assert table.get_type() == 'class'
        self.__push_table(classdef, table)
        self.__current_class.append((classdef.name, table.get_id()))
        self.__visit_list(classdef.body)
        self.__current_class.pop()
        self.__pop_table()

    def on_FunctionDef(self, funcdef):
        # table order: defaults > kw_defaults > arg_annotations > returns >
        #              func_decorators > body

        is_lambda = isinstance(funcdef, ast.Lambda)

        if not is_lambda:
            self.__add_name(funcdef.name, funcdef, keyword='def') # use keyword to skip decorators

        all_args = []
        all_args.extend(funcdef.args.args)
        if funcdef.args.vararg:
            all_args.append(funcdef.args.vararg)
        if funcdef.args.kwarg:
            all_args.append(funcdef.args.kwarg)
        all_args.extend(funcdef.args.kwonlyargs)

        self.__visit_list(funcdef.args.defaults)
        self.__visit_list(funcdef.args.kw_defaults)
        if not is_lambda:
            for arg in all_args:
                self.__visit_if_presents(arg.annotation)
            self.__visit_if_presents(funcdef.returns)
            self.__visit_list(funcdef.decorator_list)

        table = self.__next_table(funcdef)
        assert table.get_type() == 'function'
        self.__push_table(funcdef, table)
        self.__preserved_args[table] = self.__get_preserved_args(funcdef.args)
        for arg in all_args:
            self.__add_name(arg.arg, arg)
        if is_lambda:
            self.visit(funcdef.body)
        else:
            self.__visit_list(funcdef.body)
        self.__pop_table()

    on_Lambda = on_FunctionDef
    on_AsyncFunctionDef = on_FunctionDef

    def __on_comprehension(self, comp):
        # visit top layer generators
        if comp.generators:
            self.visit(comp.generators[0].iter)

        table = self.__next_table(comp)
        self.__push_table(comp, table)
        for nest_level, nest_comp in enumerate(comp.generators):
            if nest_level > 0:
                self.visit(nest_comp.iter)
            self.visit(nest_comp.target)
            self.__visit_list(nest_comp.ifs)
        if isinstance(comp, ast.DictComp):
            self.visit(comp.key)
            self.visit(comp.value)
        else:
            self.visit(comp.elt)
        self.__pop_table()

    on_ListComp = on_DictComp = on_SetComp = on_GeneratorExp = __on_comprehension

    def on_Try(self, node):
        self.__visit_list(node.body)
        self.__visit_list(node.orelse)
        self.__visit_list(node.handlers)
        self.__visit_list(node.finalbody)

    def on_ExceptHandler(self, node):
        self.__visit_if_presents(node.type)
        self.__visit_list(node.body)
        if node.name:
            self.__add_name(node.name, node, keyword='as')

    def on_Name(self, name):
        self.__add_name(name.id, name)

    def on_FormattedValue(self, value):
        self.__in_formatted_string += 1
        self.visit(value.value)
        self.__in_formatted_string -= 1
        assert self.__in_formatted_string >= 0

    def on_Global(self, node):
        for offset, name in enumerate(node.names):
            self.__add_name(name, node, offset=offset)

    def on_Nonlocal(self, node):
        for offset, name in enumerate(node.names):
            self.__add_name(name, node, offset=offset)

    def __next_table(self, node):
        table = self.__tables[self.__table_index]
        self.__table_index += 1
        if not isinstance(node, ast.Module):
            assert node.lineno == table.get_lineno(), (table.get_name(), table.get_lineno(),
                                                       node.__class__.__name__, node.lineno)
        return table

    def __push_table(self, node, table):
        self.__scope.append((node, table))

    def __pop_table(self):
        self.__scope.pop()

    def __add_name(self, name, node, *, keyword=None, offset=0):
        obname = None
        if self.__is_class_private_name(name):
            obfuscate = False
        else:
            obfuscate, table = self.__should_obfuscate(name, len(self.__scope) - 1)
            if obfuscate:
                nsid = table.get_id() if not DEBUG else table.get_name().strip('_')[:3]
                obname = ObName(name, nsid, node,
                                Position(node.lineno, node.col_offset),
                                keyword, offset, self.__in_formatted_string)
                self.__obnames.append(obname)
        logging.info('found name: %s, obname=%s', name, obname)

    def __should_obfuscate(self, name, scope_level):
        if is_preserved_name(name, self.__options):
            return False, None

        node, table = self.__scope[scope_level]
        symbol = table.lookup(name)

        if symbol.is_imported():
            return False, None

        if symbol.is_free():
            assert scope_level != 0
            return self.__should_obfuscate(name,
                    self.__get_defining_scope_level_of_free_symbol(name, scope_level))

        elif symbol.is_global() or scope_level == 0:
            if name in BUILTINS:
                return False, None

            if scope_level == 0:
                if not symbol.is_declared_global() and symbol.is_global():
                    return False, None
            else:
                try:
                    symbol = self.__top_table.lookup(name)
                    if symbol.is_imported():
                        return False, None
                except KeyError: # builtins
                    assert not symbol.is_declared_global()
                    return False, None

            if not self.__options.rename_module_private_names:
                return False, None

            if self.__module_public_names == 'INVALID':
                return False, None
            elif self.__module_public_names == 'DEFAULT':
                if not name.startswith('_'):
                    return False, None
            else:
                assert isinstance(self.__module_public_names, set)
                if name in self.__module_public_names:
                    return False, None

            return True, self.__top_table

        elif table.get_type() == 'class':
            assert symbol.is_local()
            return False, None

        else:
            assert table.get_type() == 'function' and symbol.is_local()
            if name in self.__preserved_args.get(table, ()):
                return False, None
            return True, table

    def __get_defining_scope_level_of_free_symbol(self, name, current_level):
        for level in range(current_level - 1, 0, -1):
            table = self.__scope[level][1]
            if table.get_type() == 'class':
                continue
            symbol = table.lookup(name)
            if symbol.is_local():
                assert not symbol.is_global()
                return level

    def __is_class_private_name(self, name):
        return self.__current_class and name.startswith('__') and not name.endswith('__')

    def __get_preserved_args(self, args):
        preserved = set()

        if not self.__options.rename_nondefault_parameters:
            non_default_args = args.args if not args.defaults else \
                               args.args[:-len(args.defaults)]
            for arg in non_default_args:
                preserved.add(arg.arg)

        if not self.__options.rename_default_parameters and args.defaults:
            for arg in args.args[-len(args.defaults):]:
                preserved.add(arg.arg)

        for arg in args.kwonlyargs:
            preserved.add(arg.arg)

        return preserved

    def __visit_list(self, nodes):
        for node in nodes:
            if isinstance(node, ast.AST):
                self.visit(node)

    def __visit_if_presents(self, node):
        if node is not None:
            self.visit(node)

def flatten_tables(top_table):
    tables = []
    def visit_table(table):
        tables.append(table)
        for child in table.get_children():
            visit_table(child)
    visit_table(top_table)
    return tables

def is_preserved_name(name, options):
    if name.startswith('__') and name.endswith('__'):
        return True
    if re.search('(Error|Exception|Warning)$', name):
        return True
    if name in options.preserve:
        return True

class PublicNameListWarning(SyntaxWarning): pass

class ModulePublicNameExtractor(NodeVisitor):

    def __init__(self):
        self.__name_list_defined = False
        self.__invalid = False
        self.__names = set()

    def get_result(self):
        if self.__invalid:
            warnings.warn(PublicNameListWarning('__all__ is not a list of constants, '
                          'renaming of module level names will be disabled'))
            return 'INVALID'
        elif self.__name_list_defined:
            return self.__names
        else:
            return 'DEFAULT'

    def on_Assign(self, node):
        if len(node.targets) == 1 and \
                isinstance(node.targets[0], ast.Name) and \
                node.targets[0].id == '__all__':
            self.__name_list_defined = True
            if not isinstance(node.value, (ast.List, ast.Tuple)):
                self.__invalid = True
                return
            for elt in node.value.elts:
                if not isinstance(elt, ast.Str):
                    self.__invalid = True
                    return
                self.__names.add(elt.s)

    def __skip(self, node): pass
    on_ClassDef = on_FunctionDef = __skip

def populate_obname_abspos(obnames, tokens):
    pos_obnames = {}
    for obname in obnames:
        pos_obnames.setdefault(obname.start, []).append(obname)

    def populate(obname, token_index):
        if obname.keyword:
            while True:
                token = tokens[token_index]
                token_index += 1
                if token.type == tokenize.NAME and token.string == obname.keyword:
                    break

        offset = -1
        while True:
            token = tokens[token_index]
            if token.type == tokenize.NAME and not iskeyword(token.string):
                offset += 1
                if offset == obname.offset:
                    break
            token_index += 1

        obname.abspos = token.start

    for token_index, token in enumerate(tokens):
        token_start_in_bytes = Position(token.start[0],
                                        char_offset_to_byte_offset(token.line, token.start[1]))
        for obname in pos_obnames.get(token_start_in_bytes, ()):
            populate(obname, token_index)

    abspos_obnames = {}
    for obname in obnames:
        if not obname.in_formatted_string:
            assert obname.abspos, f'obname no pos: {obname}'
            assert obname.abspos not in abspos_obnames, obname
            abspos_obnames[obname.abspos] = obname
    return abspos_obnames

def char_offset_to_byte_offset(s, char_offset):
    return len(s[:char_offset].encode())

class DocStringCollector(NodeVisitor):

    def __init__(self):
        self.linenos = set()

    def on_Module(self, node):
        if node.body:
            if isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Str):
                self.linenos.add(node.body[0].lineno)
        super().on(node)

    on_ClassDef = on_FunctionDef = on_Module

def get_docstring_linenos(ast_module):
    visitor = DocStringCollector()
    visitor.visit(ast_module)
    return visitor.linenos

class NameTranslator:

    def __init__(self, options):
        self.__options = options
        self.__realnames = {} # (name, nsid) -> obfuscated_name

    def get_name(self, name, nsid=None):
        return self.__realnames.setdefault((name, nsid), self.__encrypt_name(name, nsid))

    def __encrypt_name(self, name, nsid):
        leading_underscores = re.search('^_*', name).group()
        if DEBUG:
            nsid_s = '_' + nsid if nsid else ''
            return leading_underscores + 'ob{}_{}'.format(nsid_s, name.lstrip('_'))
        else:
            return leading_underscores + self.__gen_unique_name()

    def __gen_unique_name(self):
        gen_name = lambda: 'O' + ''.join(random.choice(['O', '0']) for i in range(16))
        while True:
            name = gen_name()
            if name not in self.__realnames.values():
                return name


class TokenTransformer:

    def __init__(self, tokens):
        self.current = None
        self.result = []
        self.__tokens = tokens
        self.__index = -1

    def next(self):
        self.__index += 1
        token = self.current = self.__tokens[self.__index]
        return token

    @property
    def previous(self):
        return self.__tokens[self.__index - 1] if self.__index > 0 else None

    @property
    def peek(self):
        return self.__tokens[self.__index + 1] if self.__index < len(self.__tokens) - 1 else None

    def skip(self, add_to_result):
        token = self.next()
        if add_to_result:
            self.add_to_result(token)
        return token

    def add_to_result(self, *tokens):
        for token in tokens:
            self.result.append(token[:2])

    def get_result(self):
        return tokenize.untokenize(self.result)

def get_class_private_names(tokens):
    class_stack = []
    is_class_private_name = lambda name: class_stack and name.startswith('__') and not name.endswith('__')
    curr_indent_level = 0
    tokens = TokenTransformer(tokens)
    state = None
    private_names = {} # token => {'class': CLASS_NAME}
    while tokens.peek:
        token = tokens.next()

        if token.type == tokenize.NAME and token.string == 'class':
            name_tok = tokens.next()
            class_stack.append({'name': name_tok.string, 'indent_level': curr_indent_level})
            state = 'CLASS_HEAD'

        elif token.type == tokenize.INDENT:
            curr_indent_level += 1
            if state == 'CLASS_HEAD':
                state = 'CLASS_BODY'

        elif token.type == tokenize.DEDENT:
            curr_indent_level -= 1
            if class_stack and curr_indent_level == class_stack[-1]['indent_level']:
                class_stack.pop()

        elif token.type == tokenize.NAME and state == 'CLASS_BODY' and \
                is_class_private_name(token.string):
            private_names[token] = {'class': class_stack[-1]['name']}

    logging.info('class_private_names: %s', private_names)
    return private_names

def transform_source(tokens, obnames, obnames_in_formatted_string,
                     name_translator, docstring_linenos, class_private_names,
                     options):
    trans = TokenTransformer(tokens)
    while trans.peek:
        token = trans.next()

        if token.type == tokenize.NEWLINE:
            if SRC_INFO:
                src_info = '#line:{}'.format(token.start[0])
                if options.append_source:
                    src_info += ':' + token.line.strip()
                trans.add_to_result((tokenize.COMMENT, src_info))

            trans.add_to_result(token)

        elif token.type == tokenize.NL:
            pass # drop the NLs

        elif token.type == tokenize.NAME:
            if token in class_private_names:
                class_name = class_private_names[token]['class']
                mangled_name = '__{}{}'.format(class_name, token.string)
                new_name = name_translator.get_name(mangled_name)
                trans.add_to_result((tokenize.NAME, new_name))
            elif token.start in obnames:
                obname = obnames[token.start]
                assert unicodedata.normalize('NFKC', token.string) == obname.name, \
                        [token.string, obname.name]
                assert obname.name == unicodedata.normalize('NFKC', obname.name)
                new_name = name_translator.get_name(obname.name, obname.nsid)
                obname.translated = True

                trans.add_to_result((tokenize.NAME, new_name))
            else:
                trans.add_to_result(token)

        elif token.type == tokenize.STRING:
            if token.end[0] in docstring_linenos and \
                    trans.previous and trans.previous.type in (tokenize.ENCODING,
                            tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT) and \
                    trans.peek and trans.peek.type == tokenize.NEWLINE:
                trans.add_to_result((tokenize.STRING, '""'))
            else:
                if re.match(r'\w*f', token.string, re.I):
                    trans.add_to_result((tokenize.STRING,
                        transform_formatted_string(token, obnames_in_formatted_string,
                            name_translator)))
                else:
                    trans.add_to_result(token)

        elif token.type == tokenize.COMMENT:
            comment = token.string.lstrip('#').lstrip()
            if comment.startswith('!'):
                trans.add_to_result(token)
                if trans.peek and trans.peek.type == tokenize.NL:
                    trans.skip(True)

        else:
            trans.add_to_result(token)

    for obname in itertools.chain(obnames.values(), obnames_in_formatted_string.values()):
        assert obname.translated, f'leaving untranslated name: {obname}'

    return trans.get_result()

def transform_formatted_string(token, obnames_in_formatted_string, name_translator):
    lines = token.string.encode().splitlines(keepends=True)
    assert len(lines) == token.end[0] - token.start[0] + 1
    row = token.start[0]
    col = char_offset_to_byte_offset(token.line, token.start[1])
    pop = lambda arr, count: bytearray(arr.pop(0) for i in range(count))
    result = bytearray()
    for line in lines:
        line = bytearray(line)
        while line:
            pos = (row, col)
            obname = obnames_in_formatted_string.get(pos)
            if obname:
                bits = pop(line, len(obname.name))
                assert bits.decode() == obname.name, bits.decode() + '==' + obname.name
                new_name = name_translator.get_name(obname.name, obname.nsid)
                obname.translated = True
                result += new_name.encode()
                col += len(bits)
            else:
                result += pop(line, 1)
                col += 1

        row += 1
        col = 0
    return result.decode()

class ObfuscateOptions:

    def __init__(self):
        self.remove_docstrings = False
        self.rename_module_private_names = False
        self.rename_nondefault_parameters = False
        self.rename_default_parameters = False
        self.preserve = set()
        self.append_source = False

def obfuscate(source, *, filename='-', options=None):
    if isinstance(source, bytes):
        encoding = tokenize.detect_encoding(io.BytesIO(source).readline)[0]
        source = source.decode(encoding)
    source = drop_encoding_comment(source)

    tokens = tuple(tokenize.tokenize(io.BytesIO(source.encode()).readline))

    options = options or ObfuscateOptions()
    ast_module = ast.parse(source, filename)
    symbol_table = symtable.symtable(source, filename, 'exec')

    visitor = ModulePublicNameExtractor()
    visitor.visit(ast_module)
    module_public_name_list = visitor.get_result()

    visitor = ObNameCollector(flatten_tables(symbol_table),
                              module_public_name_list, options)
    visitor.visit(ast_module)
    obnames = visitor.get_result()
    obnames_in_formatted_string = {n.start: n for n in obnames}
    obnames = populate_obname_abspos(obnames, tokens)

    if options.remove_docstrings:
        docstring_linenos = get_docstring_linenos(ast_module)
        logging.debug('docstrings:', docstring_linenos)
    else:
        docstring_linenos = ()

    class_private_names = get_class_private_names(tokens)

    ob_source = transform_source(tokens, obnames, obnames_in_formatted_string,
                                 NameTranslator(options), docstring_linenos,
                                 class_private_names, options)
    ob_source = ob_source.decode()

    return ob_source

def drop_encoding_comment(src):
    assert isinstance(src, str)
    lines = src.splitlines(keepends=True)
    for lineno, line in enumerate(lines):
        if line.strip().startswith('#'):
            if re.search(r'coding[:=]\s*([-\w.]+)', line): # see pep-0263
                lines[lineno] = line.replace('coding', 'xxxxxx')
                break
        else:
            break
    return ''.join(lines)

def obfuscate_file(src, dest, options):
    if src == '-':
        src_content = sys.stdin.buffer.read()
    else:
        if not os.path.exists(src):
            print('error: source file not found:', src, file=sys.stderr)
            sys.exit(1)

        with open(src, 'rb') as f:
            src_content = f.read()

    try:
        obsrc = obfuscate(src_content, filename=src, options=options)
    except SyntaxError as e:
        print('error: syntax error in file \'{}\': {}'.format(src, e), file=sys.stderr)
        sys.exit(1)

    if dest:
        try:
            with open(dest, 'wb') as f:
                f.write(obsrc.encode())
        except IOError as e:
            print('error: can not write to output file \'{}\': {}'.format(dest, e), file=sys.stderr)
            sys.exit(1)
    else:
        sys.stdout.write(obsrc)

# =================
# cmdline
# =================

def parse_args(args):
    parser = argparse.ArgumentParser(description='Oxyry python obfuscator '
                                     '(http://pyob.oxyry.com)')
    parser.add_argument('source', metavar='SOURCE', help='Source file path. '
                        'To read content from stdin instead of a file, use "-" instead.')
    parser.add_argument('--output', '-o', metavar='FILE',
                        help='''Output file path. If no file specified, the output will be
                        written to stdout.''')
    parser.add_argument('--append-source', action='store_true')
    parser.add_argument('--remove-docstrings', '-d', action='store_true')
    parser.add_argument('--rename-module-private-names', '-g', action='store_true')
    parser.add_argument('--rename-nondefault-parameters', '-p', action='store_true')
    parser.add_argument('--rename-default-parameters', action='store_true')
    parser.add_argument('--preserve', nargs='+', metavar='NAME', default=(),
                        help='')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='''If file path specified on the command line is a directory,
                        obfuscator will descend into the directory and obfuscate all the
                        files it finds there (WARNING: the source files will be overridden!).''')
    return parser.parse_args(args)

def main(args=None):
    args = parse_args(args)

    options = ObfuscateOptions()
    options.append_source = args.append_source
    options.remove_docstrings = args.remove_docstrings
    options.rename_module_private_names = args.rename_module_private_names
    options.rename_nondefault_parameters = args.rename_nondefault_parameters
    options.rename_default_parameters = args.rename_default_parameters
    options.preserve = set(args.preserve)

    if os.path.isdir(args.source):
        if not args.recursive:
            print('error: cannot obfuscate \'{}\': is a directory'.format(args.source),
                  file=sys.stderr)
            sys.exit(1)

        path = Path(args.source)
        for pyfile in path.rglob('*.py'):
            print('Obfuscating \'{}\'...'.format(pyfile.as_posix()))
            obfuscate_file(pyfile.as_posix(), pyfile.as_posix(), options)
    else:
        obfuscate_file(args.source, args.output, options)

if __name__ == '__main__':
    main()

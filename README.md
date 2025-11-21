# Oxyry Python Obfuscator

The most reliable python obfuscator in the world.

# Features

- Rename symbol names, includes variables, functions, classes, arguments,
  class private methods. The name replacer avoids a 1:1 mapping of cleartext names
  to obfuscated names, the same name may be converted to several different names
  within different scopes. 
- Remove documentation strings.
- Remove comments.
- Python 3.3 - 3.7 are supported.

# Unsupported python language features

Functions that access runtime namespace ( [exec](https://docs.python.org/3/library/functions.html#exec), [dir](https://docs.python.org/3/library/functions.html#dir), [locals](https://docs.python.org/3/library/functions.html#locals), [globals](https://docs.python.org/3/library/functions.html#globals) ) may go wrong because of accessing objects that has been renamed. 

# Recommendations to achieve best results

- Define export list (a variable named __all__) for each module.
- Use positional arguments as much as possible.
- Add double underscore prefix (e.g. __private) to class private attributes/methods.

# Module level names

Every name except the names listed in module variable __all__ are all considered private and will be renamed. If __all__ is not defined, the set of private names includes all names found in the module’s namespace which begin with underscore character ('_'). 

# It's safe to rename function parameters?

If you open options for rename parameters, you need to make sure that do not use them as keyword arguments in function call.

# Submitting bugs and feedback

Access [Issue List](https://github.com/weijarz/oxyry-python-obfuscator/issues)

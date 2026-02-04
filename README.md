This repository contains the code artifacts for the Software Engineering coursework "Category theory applications in computer science" by Laurynas Žukauskas. The code consists mainly of the Haskell to Python transpiler created for the coursework and code examples that showcase the transpiler's capabilities.

The code of the transpiler is contained in files "haskell_to_python.py" and "transpiler_main.py". A Haskell file can be translated by running "transpiler_main.py" in the command line with the path to the input file as an argument.

The original Rocq files are contained in "rocq_files". Their extracted Haskell versions are contained in "haskell_files". Python files transpiled from Haskell are contained in "python_files".

Code examples created:<br>
"btree.v" - A binary tree data structure defined as a functor and monad.<br>
"exception.v" - A monadic data structure that contains either the successful result of an expected type or a string error message. This example showcases a monadic way of handling exceptions.<br>
"maybe_list.v" - A list data structure defined as a functor, a nullable type defined as a functor and monad. The "maybe_head" showcases a natural transformation between list and maybe.<br>
"quicksort.v" - A quicksort algorithm implementation in Rocq. Source code from https://stackoverflow.com/questions/10056782/quicksort-proof-using-coq.<br>
"state.v" - A state monad implementation in Rocq. Its Python translation will cause a runtime error, which shows one of the flaws of the transpiler: the lack of currying.<br>
"writer.v" - A writer monad implementation in Rocq. This example showcases a monadic way of handling system logging.<br>

The "sort_test.py" and "test_main.py" files are an empiric test of the Python translated version of the quicksort function. "sort_test.py" demonstrates examples of helper functions that are needed to make transpiled code interoperate with native Python code.

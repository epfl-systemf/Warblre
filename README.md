# Warblre: A Coq mechanization of ECMAScript regexes

![*Curruca communis* perched on a branch](etc/warblre.webp)

The repository is structured as follows:

```
.
├── mechanization
│   ├── spec
│   │   └── base
│   ├── props
│   ├── tactics
│   └── utils
├── engines
│   ├── common
│   ├── ocaml
│   └── js
├── examples
│   ├── browser_playground
│   └── ocaml_example
├── fuzzer
├── tests
└── test262
```

In this file, we detail this architecture below.
A description of the executables implemented in this repository can also be found in [`doc/Executables.md`](doc/Executables.md); each section includes a tag indicating which engine it targets.



## Mechanization

Contains the Coq code mechanizing the subset of the ECMAScript specification which describes regexes and their semantics.
It is based on the 14th edition from June 2023, available [here](https://262.ecma-international.org/14.0/).
Regexes are described in chapter [22.1](https://262.ecma-international.org/14.0/#sec-regexp-regular-expression-objects).

The way regexes work can be described using the following pipeline:

![The matching pipeline](doc/matching_pipeline/picture.svg)

A regex is first parsed; 
it is then checked for *early errors*, and rejected if any are found; 
it is then compiled into a *matcher*;
it is finally called with a concrete input string and start position, and yield a match if one is found.

The mechanization covers the last three phases; parsing is not included.

Files are organized as follows:
- `spec`: the mechanization in itself, translating the paper specification into Coq.
- `props`: proofs about the specification. The main proofs are
    - **Compilation failure-free**: if a regex if early-errors-free, then its compilation into a matcher does not raise an error.
    - **Matching failure-free**: if a matcher is provided with valid inputs, then the matching process does not raise an error.
    - **Matching termination**: if a matcher is provided with valid inputs, then the matching process terminates.
    - **Strictly nullable optimisation**: Replacing the regex `r*` by the empty regex when `r` is a strictly nullable regex is a correct optimization.
- `tactics`: some general purpose tactics.
- `utils`: auxiliary definitions, such as extra operations and proofs on lists, the error monad, typeclasses, ...

### Differences with the ECMAScript specification and other implementation choices

The mechanization leaves some operations abstract (e.g. character canonicalization).
All of these operations are bundled with a functor, whose module parameter provides the missing types and operations.

Another difference between the ECMAScript specification and our mechanization is the handling of unicode mode.
In the specification, unicode mode is implemented by delegating some low-level operations (e.g. character canonicalization, string decoding) to different functions, one for each mode, e.g.
```
if flags.unicode then do_unicode () else do_utf ()
```
These operations overlap with the operations we would typically leave abstract, so the two modes are instead implemented as two different instantiations of the aforementioned functor:
```
Parameters.do ()
```

## Engines

In the `engines` directory, we include the code needed to turn the extracted code into two fully featured engines, one in OCaml and one in JavaScript.
For instance, this is where we need to provide implementations for the abstract types and Unicode operations of the functor discussed above.
Some of this code is common to the both engines, for instance a pretty-printer for regexes, and is stored in the `common` subdirectory.

The `ocaml` subdirectory contains code specific to the OCaml engine.
This includes functions to manipulate unicode characters, using library `uucp`.

The `js` subdirectory contains code specific to the JavaScript engine.
This also includes functions to manipulate unicode characters, as well as some functions to work with [array exotic objects](https://262.ecma-international.org/14.0/#sec-array-exotic-objects) (see [`ArrayExotic.ml`](engines/js/ArrayExotic.ml)) or a parser for regexes, based on [regexpp](https://github.com/eslint-community/regexpp).
	



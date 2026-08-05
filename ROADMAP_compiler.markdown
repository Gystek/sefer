Compiler Roadmap
================

The elements listed below should be more or less in the order they
appear in in the compiling pipeline.


Frontend
--------

- [ ] Lexing
- [ ] Parsing
- [ ] Operators elimination
- [ ] Statement storage/expression extraction (replace constructor
      names)
- [ ] Type aliases elimination
- [ ] Basic bidirectional typechecking
- [ ] Pattern matching
- [ ] Algebraic data types

Middle-end
----------

- [ ] η-expansion (functions and constructors)
- [ ] Constructor type variables elimination (`Maybe Int` -> `MaybeInt`)
- [ ] Compiling pattern matching to good decision trees

- [ ] Continuation-passing style
- [ ] Closure conversion

- [ ] Iterator optimisation

Backend
-------

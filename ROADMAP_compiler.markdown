Compiler Roadmap
================

The elements listed be low should be more or less in the order they
appear in in the compiling pipeline.

- [ ] Lexing
- [ ] Parsing
- [ ] Operators elimination
- [ ] Statement storage/expression extraction (replace constructor
      names)
- [ ] Type aliases elimination
- [ ] Currying emulation (constructors & functions) & argument count checking
- [ ] Bidirectional typechecking
- [ ] Polymorphism
- [ ] Constructor type variables elimination (`Maybe Int` -> `MaybeInt`)
- [ ] Compiling pattern matching to good decision trees

- [ ] Iterator folding

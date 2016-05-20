## Compilation
Known to compile with Coq 8.4.pl3.

## Directory structure
### categories/
Proofs that certain structures form categories.

### functors/

### interfaces/
Definitions of abstract interfaces/structures.

### implementations/
Definitions of concrete data structures and algorithms, and proofs that they are instances of certain structures (i.e. implement certain interfaces).

### misc/
Miscellaneous things.

### orders/
Theory about orders on different structures.

### quote/
Prototype implementation of type class based quoting. To be integrated.

### theory/
Proofs of properties of structures.

### varieties/
Proofs that certain structures are varieties, and translation to/from type classes dedicated to these structures (defined in interfaces/).

The reason we treat categories and varieties differently from other structures
(like groups and rings) is that they are like meta-interfaces whose implementations
are not concrete data structures and algorithms but are themselves abstract structures.

To be able to distinguish the various arrows, we recommend using a variable width font.

# Math Classes

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[travis-shield]: https://travis-ci.com/coq-community/math-classes.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/math-classes/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

[doi-shield]: https://zenodo.org/badge/DOI/10.1017/S0960129511000119.svg
[doi-link]: https://doi.org/10.1017/S0960129511000119

A library of abstract interfaces for mathematical structures in Coq.


More details about the project can be found in the paper
[Type Classes for Mathematics in Type Theory](https://arxiv.org/abs/1102.1323).

## Meta

- Author(s):
  - Eelis van der Weegen (initial)
  - Bas Spitters (initial)
  - Robbert Krebbers (initial)
- Coq-community maintainer(s):
  - Bas Spitters ([**@spitters**](https://github.com/spitters))
- License: [Public Domain](LICENSE)
- Compatible Coq versions: Coq 8.6 or later (use releases for other Coq versions)
- Additional Coq dependencies:
  - [BigNums](https://github.com/coq/bignums)

## Building and installation instructions

The easiest way to install the latest released version of Math Classes
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-math-classes
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/math-classes
cd math-classes
./configure.sh
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `MathClasses` namespace.


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


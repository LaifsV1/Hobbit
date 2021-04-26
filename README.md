# Hobbit
Higher-Order Bounded Bisimulation Tool

## Installation

Dependencies:
- OCaml 4.08+ with `ocamlbuild`
- Menhir
- Z3 with OCaml bindings

All dependencies are obtainable through [opam](http://opam.ocaml.org/doc/Install.html):
```
opam install ocamlbuild
opam install menhir
opam install z3
```

Call the make file:
```
make
```
This produces a `hobbit.native` binary.

## Usage

Use the `-i` option to select an input file. Use `-b` to specify a bound; the default is 6. To view all available options, use the `--help` option.

e.g.
```
./hobbit.native -i programs/equiv/meyer-sieber-e1.bils 
****************
Debug mode: 
Input file: programs/equiv/meyer-sieber-e1.bils
LTS implementation: immutable list
Bound: 6
Traversal: BFS
Max Pending Confs: 1000000
Memoisation cache size: 10000 
Up-to techniques: ngsrialfzue
****************
END! Nothing more to explore; no difference was found between the terms with bound = 6. The bound was not exceded - the terms are indeed equivalent!
```

A script is also provided to run all the example programs.
```
bash run-tests.sh
```
Note that this script requires `timeout` from GNU Coreutils.
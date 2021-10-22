# Hobbit
Higher-Order Bounded Bisimulation Tool

## Installation

Instructions below were tested for Linux and macOS. opam is not yet officially supported for Windows.

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

A script is also provided to run all the example programs. The script produces log files.
```
bash run-tests.sh
```
Note that this script requires `timeout` from GNU Coreutils.

For the SyTeCi example programs, the translated files can be found under the `experiments/syteci_experiments` directory. Result tables can be found in the `experiments/` drectory under their correspondingly named directories.

### Tool Options

The primary options necessary for usage are:

- `-i <input file path>`: selects a files to check; otherwise, Hobbit expects input via `stdin`
- `-b <integer bound>`: number of function applications Hobbit is allowed to perform
- `-u <string>`: turns on up-to techniques; each character in the string provided turns on an up-to technique associated to that character

Advanced options:

- `-t <0|1>`: 0 for BFS and 1 for DFS traversal
- `-p <integer>`: provides a maximum number of configurations pending to be explored in the frontier; upon exceeding this, the tool stops
- `-m <integer>`: provides a maximum number of configurations remembered; upon exceeding this number, the newest configuration added replaces the oldest one remembered

Others options:

- `-d <string>`: similar to `-u`, but turns on printing debug information depending on the characters present in the string
- `-l <integer>`: used to select other LTS implementation; unused in this version of the tool

For list of options available under each parameter, use `--help`.

## Up-to Techniques Available

Novel techniques presented:

- separation: up-to separation; prunes names from the knowledge environments if they only manipulate local references.
- generalisation: up-to state invariants; generalises store values using a given invariant
- reentry: up-to proponent function re-entry; prevents reentry of functions if the store has not changed between calls

Other Techniques:

- normalisation: normalises configurations memoised
- identity: prunes path if the configurations checked for equivalence are structurally identical
- name reuse: reuses opponent names that are no longer in use
- remove gamma duplicates: removes duplicate names in the opponent knowledge environment (gamma) provided they occur in the same index on both sides
- garbage collection: garbage collects unused store locations in configurations
- sigma normalisation: normalises the symbolic environment (sigma)
- sigma simplification: runs simplification procedure over the symbolic environment (sigma) 
- sigma garbage collection: removes constraints involving redundant variables in the symbolic environment (sigma)

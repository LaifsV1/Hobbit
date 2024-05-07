[![DOI](https://zenodo.org/badge/361406257.svg)](https://zenodo.org/doi/10.5281/zenodo.7864658)

# Hobbit
Hobbit (Higher-Order Bounded Bisimulation Tool) is a higher-order contextual equivalence checking tool that combines Bounded Model Checking and Up-To Techniques to verify equivalences and find inequivalences.

Publication: [10.1007/978-3-030-99527-0_10](https://doi.org/10.1007/978-3-030-99527-0_10)

## Directory Structure

Directories present under the main `Hobbit` directory:
- `experiments`: experimental data as recorded for the submitted paper, also attached here
- `programs`: our testsuite, which is divided into subdirectories for equivalences `equiv`, inequivalences `inequiv`, and debugging `misc`
- `src`: source files of Hobbit

## Installation

Instructions below were tested for Linux and macOS. `opam` is not yet officially supported for Windows.

Dependencies:
- OCaml 4.08+ with `ocamlbuild`
- Opam
- Menhir
- Z3 with OCaml bindings

### Installing OCaml's Package Manager `opam`

All dependencies are obtainable through OCaml's official package manager [`opam`](http://opam.ocaml.org/doc/Install.html). Installation of `opam` is system specific so you may need to refer to their website linked above. Instructions for some popular systems are listed below:
#### Ubuntu
```
add-apt-repository ppa:avsm/ppa
apt update
apt install opam
```
#### Fedora, CentOS and RHEL
```
dnf install opam
```
#### macOS
```
# Homebrew
brew install gpatch
brew install opam

# MacPort
port install opam
```

### Initialising `opam`

`opam` needs to be set up after installation, and this may be system dependent. First one needs to initialise it:
```
opam init
```
After initialisation, one has to create the switch to a specific compiler. Any version 4.08 and over works. The command below uses `4.08.1`, but one can use the latest version listed.
```
opam switch create 4.08.1
```
If this does not work, it could be because `opam` is missing a dependency. Depending on how minimal the installation of the system is, one may have to install many dependencies. You may need to check the error messages to know what is missing. In our experience, these are the dependencies typically missing e.g. for Ubuntu:
```
apt install build-essential
apt install gcc
apt install bubblewrap
```
The above correspond to `make`, `gcc` and `bwrap`, which are often missing in fresh installations.

Finally, initialising `opam` updates your `~/.profile` file, so you may have to source it on e.g. Ubuntu:
```
source ~/.profile
```

### Installing Hobbit's dependencies

With `opam` set up, installing Hobbit's dependencies becomes very easy.
```
opam install ocamlbuild
opam install menhir
opam install z3
```
Note that Z3 takes a long time to install.

With all dependencies installed and `~/.profile` sourced, call the make file:
```
make
```
This produces a `hobbit.native` binary.

## Usage

Hobbit inputs a file containing two program expressions, written in Hobbit’s input language which is based on ML. Hobbit attempts to (dis-)prove that the expressions are contextually equivalent. That is, replacing one for another in any possible program context does not change the observable behaviour of the program. See the paper for more details on contextual equivalence.

### Tool Options

The primary options necessary for usage are:

- `-i <input file path>`: selects a file to check; otherwise, Hobbit expects input via `stdin`
- `-b <integer bound>`: number of function applications Hobbit is allowed to perform before returning an "incoclusive" result to the user
- `-u <string>`: turns on up-to techniques; each character in the string provided turns on an up-to technique associated to that character; e.g. "ngsrialfzue" for [n]ormalisation [g]arbage-collection up-to-[s]eparation up-to-name-[r]euse up-to-[i]dentity sigma-g[a]rbage-collection sigma-norma[l]isation sigma-simpli[f]ication generali[z]ation remove-gamma-d[u]plicates up-to-re[e]ntry (default: ngsrialfzue)

Advanced options:

- `-t <0|1>`: 0 for BFS and 1 for DFS traversal
- `-p <integer>`: provides a maximum number of configurations pending to be explored in the frontier; upon exceeding this, the tool stops
- `-m <integer>`: provides a maximum number of configurations remembered; upon exceeding this number, the newest configuration added replaces the oldest one remembered

Developer options:

- `-d <string>`: similar to `-u`, but turns on printing debug information depending on the characters present in the string
- `-l <integer>`: used to select other LTS implementation; unused in this version of the tool

For list of options available under each parameter, use `--help`.

### Up-to Techniques

Techniques presented in the paper:

- separation: up-to separation (see paper sec.5); prunes names from the knowledge environments if they only manipulate local references.
- generalisation: up-to state invariants (see paper sec.5); generalises store values using a given invariant
- reentry: up-to proponent function re-entry (see paper sec.7); prevents reentry of functions if the store has not changed between calls

Other Techniques, more standard techniques:

- normalisation: normalises configurations memoised
- identity: prunes path if the configurations checked for equivalence are structurally identical
- name reuse: reuses opponent names that are no longer in use
- remove gamma duplicates: removes duplicate names in the opponent knowledge environment (gamma) provided they occur in the same index on both sides
- garbage collection: garbage collects unused store locations in configurations
- sigma normalisation: normalises the symbolic environment (sigma)
- sigma simplification: runs simplification procedure over the symbolic environment (sigma) 
- sigma garbage collection: removes constraints involving redundant variables in the symbolic environment (sigma)

### Input

Many example input files, also used in the experimental evaluation section of the paper, can be found in the ‘programs’ directory with the following subdirectories:
- `programs/equiv` examples of equivalent expressions;
- `programs/inequiv` examples of inequivalent expressions;
- `programs/misc` a number of examples used for sanity-checking Hobbit.

An input file has the structure:

```
<pgm expression> ||| <pgm expression>
```

when the top-level types of the program expressions can be completely inferred by Hobbit’s type inference system or

```
<pgm expression> |||_<type> <pgm expression>
```
when Hobbit's type inference cannot fully infer types and the user has to provide the types of the expressions. Both expressions should have the same type.

Use the `-i <filename>` option to select an input file. When omitting the `-i` option Hobbit will read from the standard input, which can be useful with shell piping. For example:

```
./hobbit.native -i programs/equiv/meyer-sieber-e1.bils 
```

### Bounded Model Checking Bisimulation Equivalence

Hobbit is primarily a bounded model-checker for bisimulation equivalence over the transition system described in detail in the research paper. As such a bound must be provided to limit the exploration of the explored (potentially infinite) state-space. This is provided with the `-b` parameter. The default bound is 6, which is sufficient for many examples. However several examples require a larger bound. For example the following example requires a bound of 332 or more:

```
./hobbit.native -i programs/equiv/list-qsort-N6.bils -b 332
```

### Limiting Memory Usage

Hobbit uses memory to store the number of pending bisimulation states (pairs of program configurations) that are still to be explored and the number of previous bisimulation states memoised. The former are created by a single step of Hobbit's exploration approach (DFS or BFS) and exceeding this limit will result in a runtime error. The latter is used to detect already explored states which is crucial for Hobbit to avoid exploring the same states multiple times and terminate. Limits to pending and memoised states are provided with the command line options `-p` and `-m`, respectively. Defaults are
1000000 and 10000 respectively.

### Output

Hobbit outputs both in the standard output and the standard error. The latter is used when input files fail to parse/typecheck or when an unexpected runtime error occurs. Standard output contains information about the equivalence checking functionality. For example:

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

In order, each line of this output informs the user of the following:
- Hobbit was **not** in debug mode (used during Hobbit's development);
- the input file;
- an implementation-specific detail about the representation of the stack/queue used for pending states;
- the exploration traversal used;
- The limit in pending bisimulation states (pairs of configurations);
- the limit in memoised bisimulation states;
- the up-to techniques used in this run (see description below).
- The outcome of equivalence checking -- here the programs were indeed found to be equivalent.

The following example shows the output for an inequivalence example:

```
****************
Debug mode: 
Input file: programs/inequiv/symb-const-4.bils
LTS implementation: immutable list
Bound: 6
Traversal: BFS
Max Pending Confs: 1000000
Memoisation cache size: 10000 
Up-to techniques: ngsrialfzue
****************
Bisimulation failed! Failing trace:
 -pr_ret _idx_1_->-op_call _idx_1_ ((ac9: Bool), (ac8: Bool))->-pr_ret _idx_1_->-op_call _idx_1_ (ac18: Bool)->-[ RHS=bot ]->-pr_ret (w17: Bool)->-[ only LHS terminates ]->

Symbolic Environment:
 (w_17 <> true) and 
(w_17 = (ac_9 = ac_8))

Satisfying Assignment:
(define-fun ac_9 () Bool
  true)
(define-fun ac_8 () Bool
  false)
(define-fun w_17 () Bool
  false)
```
Here the user is informed that the program expressions were found to be inequivalent, together with a  distinguishing trace in the Labelled Transition System described in the research paper, and the symbolic environment of the final configuration. More specifically this trace shows the sequence of transitions:

The trace above reports that the program expressions were inequivalent under the model `{ac9 := true; ac8 := false; w17 := false}`. The `ac` names are abstract constants provided by the opponent, while the `w` name is a symbolic constant resulting from evaluating a symbolic arithmetic expression. The discrepancy in the `_` present in the names is due to a difference in how Z3 and Hobbit print names; internally, names `ac_9` and `ac9` are both the same abstract constant with index `9`. Briefly, the trace reports:
1. `-pr_ret _idx_1_->`: both initial configurations performed a proponent-return transition, which returned a function to the opponent, this function was indexed under position 1 of an environment called Gamma in the research paper;
2. `-op_call _idx_1_ ((ac9: Bool), (ac8: Bool))->`: the opponent calls this function given to it at `1` with the pair of constants `ac9, ac8`, and because the function at index `1` is never called again, it is garbage collected;
3. `-pr_ret _idx_1_->`: proponent then returns another function, which takes up position `1` in Gamma which was just freed;
4. `-op_call _idx_1_ (ac18: Bool)->`: the opponent then calls this new function at `1` with some new constant `ac18`;
5. `-[ RHS=bot ]->-pr_ret (w17: Bool)->`: at this point, the left-hand-side returns the result of an arithmetic expression `w17` which the right-hand-side cannot match, resulting in the RHS becoming a special `bot` configuration (`RHS=bot`) which by the rules of the labelled transition system cannot terminate;
6. `-[ only LHS terminates ]->`: the opponent is able to observe termination of the left-hand-side only, thus verifying the inequivalence.

The symbolic environment printed here shows that in this distinguishing trace, the value `w17` returned by the LHS, is false and was the result of `ac_9 = ac_8`. In other words the program expressions can be distinguished when the first opponent call provides a pair of unequal booleans, which the satisfying assignment produced by Z3 instantiates to `ac9 = true` and `ac8 = false`.

## Experiments

Experimental data used in the paper is provided in the directory `experiments`. There are two main sub-directories:
- `hobbit_experiments`: this contains the output of the `run-tests.sh` used for the table in Section 8 of the paper.
- `syteci_experiments`: this contains the programs used for comparing Hobbit with the related tool called SyTeCi, described in Section 9.


Directory structure for the experiments is as follows:
```
experiments
|
└───hobbit_experiments  <experiments benchmarking Hobbit>
|   |   bfs_equiv.ods           <spreadsheet recording all output for experiments for equivalences>
|   |   bfs_inequiv.ods         <spreadsheet recording all output for experiments for inequivalences>
|   |   bfs_equiv.txt.csv       <csv file for equivalences produced by processing all raw data using a script>
|   |   bfs_inequiv.txt.csv     <csv file for inequivalences produced by processing all raw data using a script>
|   |   make_csv.sh             <script we used to collect the raw data into csv files>
|   |
|   └───default         <directory containing our logs for default mode> 
|   └───no_sep          <directory containing our logs for no-separation mode>
|   └───no_gen          <directory containing our logs for no-invariants mode>
|   └───no_reentry      <directory containing our logs for no-reentry mode>
|   └───no_all          <directory containing our logs for all-up-to-techniques-off mode>
|
└───syteci_experiments  <experiments to compare Hobbit and SyTeCi>
    |   table.ods       <spreadsheet recording all results of the comparison experiments>
    |
    └───hobbit_progs
    |   |
    |   └───from_hobbit        <programs chosen from Hobbit's testsuite in Hobbit syntax>
    |   |   |   run-tests.sh   <copy of `run-tests.sh` added to aid reproduceability tests>
    |   |   └───programs
    |   |        └───equiv   <equivalence programs from Hobbit's testsuite>
    |   |        └───ineq    <inequivalence programs from Hobbit's testsuite>
    |   |
    |   └───from_syteci      <programs from SyTeCi's testsuite in Hobbit syntax>
    |       | ...            <same directory structure as `from_hobbit`>
    |
    └───syteci_progs
        |
        └───from_hobbit           <programs chosen from Hobbit's testsuite in SyTeCi syntax>
        |   └───eq                <equivalence programs from Hobbit's testsuite>
        |   |   |   results.txt   <text file with our results>
        |   |   |   scale.sh      <script that produced results.txt, requires SyTeCi's binaries>
        |   |
        |   └───ineq         <inequivalence programs from Hobbit's testsuite>
        |       | ...        <same directory structure as `eq`>
        |
        └───from_syteci      <programs from SyTeCi's testsuite in SyTeCi syntax>
            | ...            <same directory structure as `syteci_progs/from_hobbit`>
```
In the directories above, `hobbit_experiments/bfs_equiv.ods` and `hobbit_experiments/bfs_inequiv.ods` collect all benchmarking done on Hobbit, and `syteci_experimenets/table.ods` record all data from the comparison.

### Testing Script

A script is provided to run our experiments as described in the paper.

Note that this script requires `timeout` from GNU Coreutils. All files checked are set to time out after 150s. Also note that the compiled binary `hobbit.native` needs to be in the main directory (with the script) for the script to work.

The script can be called as follows:

```
bash run-tests.sh
```

The script runs Hobbit on all files in the `programs/` subdirectories in batches. Each batch corresponds to an experiment in which the tool is run with options specified in the paper. These are:
- `default`: all up-to techniques on
- `no_sep`: up to separation off
- `no_gen`: up to invariants off
- `no_reentry`: up to reentrancy off
- `no_all`: all up-to techniques off

Every batch contains two sets of files: equivalences and inequivalences. On the terminal, at the bottom of a batch, you can see the result of that batch. e.g. for the default batch:

```
BFS Inequivalence Checks result in file: logs/default/out_bfs_inequiv.txt
*** 72 equivalences proved
*** 68 inequivalences proved
*** 33 inconclusive examples
*** 0 error(s) in programs
*** 173 files checked
```

The script produces log files with the following structure:
```
logs
|
└───default
|   |   files_bfs_equiv.txt     <equivalences: files checked, one per line>
|   |   err_bfs_equiv.txt       <equivalences: stderr stream, collects all the times and errors in every line; synchronised with the files_bfs_equiv.txt file>
|   |   out_bfs_equiv.txt       <equivalences: stdout stream, collects standard output of the tool>
|   |   status_bfs_equiv.txt    <equivalences: collects parsed exit status: yes,no,N/A,error; synchronised with the files_bfs_equiv.txt file>
|   |   files_bfs_inequiv.txt   <inequivalences: files checked, ...>
|   |   err_bfs_inequiv.txt     <inequivalences: stderr stream, ...>
|   |   out_bfs_inequiv.txt     <inequivalences: stdout stream, ...>
|   |   status_bfs_inequiv.txt  <inequivalences: parsed exit status, ...>
|   
└───no_sep
|   | ... <same structure as default>
|
└───no_gen
|   | ... <same structure as default>
|
└───no_reentry
|   | ... <same structure as default>
|
└───no_all
|   | ... <same structure as default>
```

To relate the files, err and status messages use the paste command; e.g.:

```
paste logs/default/files_bfs_equiv.txt logs/default/err_bfs_equiv.txt logs/default/status_bfs_equiv.txt 
```

As the script progresses, testing batches should slow down drammatically and `error` messages start popping up. These are expected timeouts and show that up-to techniques work. With all techniques turned off, Hobbit should fail to prove all but 3 trivial equivalences, and be very slow at proving inequivalences. You can verify the error messages are indeed timeouts by checking the logs, which shall be explained following this.

The script can output 1 of 4 messages for every file:
- `equivalent`: the terms have been proven contextually equivalent
- `inequivalent`: the terms have been proven contextually inequivalent
- `inconclusive`: Hobbit reached the bound and could not prove equivalence or inequivalence
- `error`: Hobbit stopped unexpectedly, which can be for the following reasons:
  - **message is present in the log files**: Hobbit crashed and the message details the reasons. None of the provided examples in our experiments produce this case.

  - **message is not present in the log files**: Hobbit was stopped by the script itself due to timeout, which is expected to happen after 150s. For example, after running the `no_sep` batch of experiments on an average laptop, the file `/programs/equiv/hector-bsort-CN5-sorted.bils` is likely to timeout. One could then observe the following line in the combined log files with the command:

    ```
    paste logs/no_sep/files_bfs_equiv.txt logs/no_sep/err_bfs_equiv.txt logs/no_sep/status_bfs_equiv.txt | grep hector-bsort-CN5-sorted.bils
    hector-bsort-CN5-sorted.bils   150.080   error
    ```

    showing that this program timed out at 150s.

### SyTeCi comparison

A copy of `run-tests.sh` is provided in the Hobbit directories to aid reproduceability tests for the Hobbit side of the comparison. To use the scripts, a copy of `hobbit.native` is required in the same directory as the scripts being run. After building Hobbit, one can copy the symbolic link in the main directory into `syteci_experiments/hobbit_progs/` and `syteci_experiments/`. Alternatively, one could add `hobbit.native` in the `_build` directory produced to `PATH` environment. To run the SyTeCi side of the comparison, a copy of SyTeCi's binaries is needed.

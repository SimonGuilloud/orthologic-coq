# Verified and Optimized Implementation of Orthologic Proof Search
This repository contains the formalization in Coq of the main result of [Orthologic with Axioms](https://infoscience.epfl.ch/entities/publication/0bf03832-b873-44e1-8286-4301ecc42709) (the cut elimination theorem for orthologic), and the implementation of an algorithm deciding orthologic inequalities, optimized using memoization and reference equality: The optimized algorithm is proven correct, and lifted to a Coq tactic using reflection. Independent proof search and normalization tactic implmented directly in OCaml are also provided.

The theorems and tactics are available as a plugin.

### Requirements:
This formalization has been carried using Coq 8.18, [Ocaml](https://ocaml.org/docs/installing-ocaml) 5.3 and [Dune](https://dune.build/install) 3.8. Using opam, run:
```shell
$ opam install dune.3.8.2 coq.8.18.0
```

### Building the project
Build and verify the project using (takes a couple minutes):

```shell
$ dune build
```
You can also try the plugin by running:
```shell
$ coqtop -R _build/default/theories/ OLCoq -I _build/default/src/
```
and then
```coq
Coq < Require Import OLCoq.OLPlugin.
```

### Installing the plugin
To install the plugin locally on your machine and use it in your own projects, run
```shell
$ opam pin --yes git@github.com:SimonGuilloud/orthologic-coq.git#main
```
or clone the repository and run at root
```shell
$ opam pin --yes ./
```

### Tutorial
A short introduction to the plugin can be found in [theories/Tutorial.v](theories/Tutorial.v). 

### Reference Paper
[Verified and Optimized Implementation of Orthologic Proof Search](https://infoscience.epfl.ch/entities/publication/398b9d7c-1bd9-4570-9c12-7214e12d9caf) (Preprint, CAV 2025)

### Benchmarks
Benchmarks where generated according to [Main.scala](generation/src/main/scala/Main.scala) using [Scala](https://www.scala-lang.org/download/) and can be regenerated using `sbt run`. Benchmarks can be found in [theories/olsolve_bench](theories/olsolve_bench) and [theories/oltauto_bench](theories/oltauto_bench).
The raw results of the benchmarks are in [bench.2025-01-31](bench.2025-01-31) and [oltauto.bench.2025-02-01](oltauto.bench.2025-02-01). They can be reevaluated with (takes arround 1 hour on a Intel Core i9-13900K CPU with 64GB RAM)
```shell
make solve-bench
```
and 
```shell
make tauto-bench
```
To ease replication, this will run each benchmark only once. The results we report in the paper are the median of 5 runs. This can be changed line 82 of the [theories/OL_Bench.v](theories/OL_Bench.v) file. 

Plots are plotted using [plot.py](plot.py).

Note that the objective of the first benchmark is to demonstrate that the asymptotic behaviour is as expected from the theory (results in [lines.pdf](lines.pdf)) and the objective of the second benchmark is to show practical improvements over Coq's built-in solver for propositional logic, `btauto` (results in [OCaml+n+btauto.pdf](OCaml+n+btauto.pdf)). The key corectness property of the artifact is validation by Coq, which is verified with `dune build`.

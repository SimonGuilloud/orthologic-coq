# Verified and Optimized Implementation of Orthologic Proof Search
This repository contains the formalization in Coq of the main result of [Orthologic with Axioms](https://infoscience.epfl.ch/entities/publication/0bf03832-b873-44e1-8286-4301ecc42709) (the cut elimination theorem for orthologic), and the implementation of an algorithm deciding orthologic inequalities, optimized using memoization and reference equality: The optimized algorithm is proven correct, and lifted to a Coq tactic using reflection. Independent proof search and normalization tactic implmented directly in OCaml are also provided.

The theorems and tactics are available as a plugin.

### Requirements:
This formalization has been carried using Coq 8.18, [Ocaml](https://ocaml.org/docs/installing-ocaml) 5.3 and [Dune](https://dune.build/install) 3.8. Using opam, run:
```shell
$ opam install dune.3.8.2 coq.8.18.0
```
Alternatively, you can use the Docker image provided in this repository using:
```shell
$ docker load < orthologic-coq.tar.gz
```
To run the image, use:
```shell
$ docker run -it orthologic-coq:latest
```

### Building the project
Build and verify the entire project using (takes a couple minutes):

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


### Tutorial
A short introduction to the plugin can be found in [theories/Tutorial.v](theories/Tutorial.v). 

### Reference Paper
[Verified and Optimized Implementation of Orthologic Proof Search](https://infoscience.epfl.ch/entities/publication/398b9d7c-1bd9-4570-9c12-7214e12d9caf) (Preprint, CAV 2025)

### Benchmarks
Benchmarks where generated according to [Main.scala](generation/src/main/scala/Main.scala) using [Scala](https://www.scala-lang.org/download/). Regenerate using `sbt run`. Benchmarks can be found in [theories/olsolve_bench](theories/olsolve_bench) and [theories/oltauto_bench](theories/oltauto_bench).
The raw results of the benchmarks are in [bench.2025-01-31](bench.2025-01-31) and [oltauto.bench.2025-02-01](oltauto.bench.2025-02-01). They can be reevaluated with (takes arround 12 hours on a desktop machine)
```shell
make tauto-bench
```
and 
```shell
make solve-bench
```
Plots are plotted using [plot.py](plot.py).

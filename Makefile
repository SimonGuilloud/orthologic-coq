COQC ?= coqc

solve_bench_v := $(wildcard theories/olsolve_bench/*.v)
solve_bench = $(solve_bench_v:.v=.bench)

tauto_bench_v := $(wildcard theories/oltauto_bench/*.v)
tauto_bench = $(tauto_bench_v:.v=.bench)

bench_vo := _build/default/theories/OL_Bench.vo

$(bench_vo): FORCE
	rm -f theories/bench/*.vo theories/bench/*.vos theories/bench/*.vok theories/bench/*.glob theories/bench/*.aux
	dune build

%.bench: %.v $(bench_vo)
	$(COQC) -R _build/default/theories OLCoq -I _build/default/src $< | tee $@

tauto-bench: $(tauto_bench) FORCE
	echo $(tauto_bench)

solve-bench: $(solve_bench) FORCE
	echo $(solve_bench)

bench-clean:
	rm -f $(tauto_bench)

FORCE:

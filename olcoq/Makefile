COQC ?= coqc
ALL_BENCH_V := $(wildcard theories/bench/*.v)
ALL_BENCH = $(ALL_BENCH_V:.v=.bench)

bench_vo := _build/default/theories/OL_Bench.vo

$(bench_vo):
	dune build

theories/bench/%.bench: theories/bench/%.v $(bench_vo)
	$(COQC) -R _build/default/theories OLCoq -I _build/default/src $< | tee $@

bench: $(ALL_BENCH) FORCE
	echo $(ALL_BENCH)

bench-clean:
	rm -f $(ALL_BENCH)

FORCE:

COQC=coqc

ALL_VO := theories/OL_Theory.vo \
	theories/OL_Reflection_1_base.vo theories/OL_Reflection_2_memo.vo \
	theories/OL_Reflection_3_fmap.vo theories/OL_Reflection_4_pointers.vo \
	theories/OL_Bench.vo

coq: $(ALL_VO)

clean:
	rm -f *.vo *.glob *.vok *.vos .*.aux

OL_Reflection_1_base.vo: theories/OL_Theory.vo
OL_Reflection_2_opti.vo: theories/OL_Theory.vo theories/OL_Reflection_1_base.vo
OL_Reflection_3_memo.vo: theories/OL_Theory.vo theories/OL_Reflection_1_base.vo theories/OL_Reflection_2_opti.vo
OL_Reflection_4_fmap.vo: theories/OL_Theory.vo theories/OL_Reflection_1_base.vo theories/OL_Reflection_2_opti.vo
OL_Reflection_5_pointers.vo: theories/OL_Theory.vo theories/OL_Reflection_1_base.vo theories/OL_Reflection_2_opti.vo theories/OL_Reflection_4_fmap.vo
OL_Bench.vo: theories/OL_Theory.vo \
	theories/OL_Reflection_1_base.vo theories/OL_Reflection_2_opti.vo theories/OL_Reflection_3_memo.vo \
	theories/OL_Reflection_4_fmap.vo theories/OL_Reflection_4_pointers.vo

ALL_BENCH_V := $(wildcard bench/*.v)
ALL_BENCH = $(ALL_BENCH_V:.v=.bench)

bench/%.bench: bench/%.v OL_Bench.vo
	$(COQC) $< | tee $@

bench: $(ALL_BENCH) FORCE
	echo $(ALL_BENCH)

bench-clean:
	rm -f $(ALL_BENCH)

FORCE:

%.vo: %.v
	$(COQC) $<

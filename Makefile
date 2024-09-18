COQC=coqc

ALL_VO := OL_Theory.vo \
	OL_Reflection_1_base.vo OL_Reflection_2_memo.vo \
	OL_Reflection_3_fmap.vo OL_Reflection_4_pointers.vo \
	OL_Bench.vo

coq: $(ALL_VO)

clean:
	rm -f *.vo *.glob *.vok *.vos

OL_Reflection_1_base.vo: OL_Theory.vo
OL_Reflection_2_memo.vo: OL_Theory.vo OL_Reflection_1_base.vo
OL_Reflection_3_fmap.vo: OL_Theory.vo OL_Reflection_1_base.vo
OL_Reflection_4_pointers.vo: OL_Theory.vo OL_Reflection_1_base.vo OL_Reflection_3_fmap.vo
OL_Bench.vo: OL_Theory.vo \
	OL_Reflection_1_base.vo OL_Reflection_2_memo.vo \
	OL_Reflection_3_fmap.vo OL_Reflection_4_pointers.vo

bench/%.bench: bench/%.v
	$(COQC) $< | tee $@

%.vo: %.v
	$(COQC) $<

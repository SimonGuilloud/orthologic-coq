COQC=coqc

ALL_VO := OL_Theory.vo \
	OL_Reflection_1_base.vo OL_Reflection_2_memo.vo \
	OL_Reflection_3_fmap.vo OL_Reflection_4_pointers.vo

coq: $(ALL_VO)

clean:
	rm -f *.vo *.glob *.vok *.vos

OL_Reflection_1_base.v: OL_Theory.vo
OL_Reflection_2_memo.v: OL_Theory.vo OL_Reflection_1_base.vo
OL_Reflection_3_fmap.v: OL_Theory.vo OL_Reflection_1_base.vo
OL_Reflection_4_pointers.v: OL_Theory.vo OL_Reflection_1_base.vo OL_Reflection_3_fmap.vo
OL_bench.txt: OL_Theory.vo \
	OL_Reflection_1_base.vo OL_Reflection_2_memo.vo \
	OL_Reflection_3_fmap.vo OL_Reflection_4_pointers.vo
	$(COQC) OL_Tests.v | tee $@

%.vo: %.v
	$(COQC) $<

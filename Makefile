
#.PHONY: coq clean
COQC=coqc

coq:
	$(COQC) OL_Theory.v
#	$(COQC) OL_Reflection.v
	$(COQC) OL_Reflection_1_base.v
	$(COQC) OL_Reflection_2_memo.v
	$(COQC) OL_Reflection_3_fmap.v
#	$(COQC) OL_Reflection_4_pointer.v

clean:
	rm -f *.vo *.glob *.vok *.vos

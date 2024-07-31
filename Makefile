#.PHONY: coq clean

COQC=coqc

coq:
	$(COQC) OL_Theory.v
	$(COQC) OL_Reflection.v

clean:
	rm -f *.vo *.glob *.vok *.vos

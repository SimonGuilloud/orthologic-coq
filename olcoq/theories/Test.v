Require Import OLPlugin.
Require Import OL_Reflection_5_pointers.
Require Import OL_Reflection_1_base.
Require Import OL_Theory.

Open Scope bool_scope.
Require Import Bool.
Require Import Btauto.




(*
Example test0 a b c: (negb (a && (b || c))) ||  ((a && b) || (a && c)) = true.
Proof.
  oltauto.
Qed.

Example test0_cert a b c: (negb (a && (b || c))) ||  ((a && b) || (a && c)) = true.
Proof.
  oltauto_cert.
Qed.
*)












Require Extraction.

Extraction "extractedCode" decideOL_pointers.
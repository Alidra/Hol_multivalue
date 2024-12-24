Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098917_spec.
Lemma lem1098919 {_25251 : Type'} : (@List.removelast _25251 (@nil _25251)) = (@nil _25251).
Proof. exact (proj1 (@lem1098917 _25251)). Qed.

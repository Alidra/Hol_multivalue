Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6904577 {_126180 : Type'} : (@iterate int _126180 int_mul) = (@iterate int _126180 int_mul).
Proof. exact (eq_refl (@iterate int _126180 int_mul)). Qed.

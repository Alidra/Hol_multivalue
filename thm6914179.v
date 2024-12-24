Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6914179 {_126338 : Type'} : (@iterate int _126338 int_add) = (@iterate int _126338 int_add).
Proof. exact (eq_refl (@iterate int _126338 int_add)). Qed.

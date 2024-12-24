Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6904578 {_126180 : Type'} : (@iproduct _126180) = (@iterate int _126180 int_mul).
Proof. exact (@iproduct_def _126180). Qed.

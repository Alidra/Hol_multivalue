Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6910045 {_126259 : Type'} : (@product _126259) = (@iterate real _126259 real_mul).
Proof. exact (@product_def _126259). Qed.

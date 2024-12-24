Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6898569 {_126105 : Type'} : (@nproduct _126105) = (@iterate nat _126105 Nat.mul).
Proof. exact (@nproduct_def _126105). Qed.

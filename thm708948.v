Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm708868_spec.
Lemma lem708948 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem708868)). Qed.

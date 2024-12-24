Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483529_term_abbrevs.
Require Import thm1483526_spec.
Lemma lem1483529 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (proj1 (@lem1483526 x y)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483568_term_abbrevs.
Require Import thm1483566_spec.
Lemma lem1483568 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483566 x y)). Qed.
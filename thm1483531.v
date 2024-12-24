Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483531_term_abbrevs.
Require Import thm1483528_spec.
Lemma lem1483531 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (proj1 (@lem1483528 x y)). Qed.

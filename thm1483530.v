Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483530_term_abbrevs.
Require Import thm1483528_spec.
Lemma lem1483530 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483528 x y)). Qed.
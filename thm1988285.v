Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988285_term_abbrevs.
Require Import thm1386559_spec.
Lemma lem1988285 (y : real) (x : real) : (real_lt x y) = (term0 y x).
Proof. exact (proj1 (@lem1386559 x y)). Qed.

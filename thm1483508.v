Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483508_term_abbrevs.
Require Import thm1483505_spec.
Lemma lem1483508 (y : real) (x : real) (z : real) : (term0 x y z) = (term1 y x z).
Proof. exact (proj1 (@lem1483505 y z x (@el nat))). Qed.
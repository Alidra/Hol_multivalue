Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483535_term_abbrevs.
Require Import thm1483532_spec.
Lemma lem1483535 (y : real) (x : real) : (term0 x y) = (term1 y x).
Proof. exact (proj1 (@lem1483532 x y)). Qed.

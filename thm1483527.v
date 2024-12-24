Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483527_term_abbrevs.
Require Import thm1483524_spec.
Lemma lem1483527 (x : real) (y : real) : (real_ge x y) = (term0 x y).
Proof. exact (proj1 (@lem1483524 x y)). Qed.

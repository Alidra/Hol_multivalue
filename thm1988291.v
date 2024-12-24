Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988291_term_abbrevs.
Require Import thm1988288_spec.
Lemma lem1988291 (x : real) (y : real) : (real_ge x y) = (term0 x y).
Proof. exact (proj1 (@lem1988288 x y)). Qed.

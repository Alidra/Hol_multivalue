Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988189_term_abbrevs.
Lemma lem1988189 (x : real) (y : real) : (term0 x y) = ((term1 x y) = (term2 x y)).
Proof. exact (eq_refl (term0 x y)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841616_term_abbrevs.
Lemma lem2841616 (x : int) (y : int) : (term0 x y) = ((int_le x y) = (term1 x y)).
Proof. exact (eq_refl (term0 x y)). Qed.

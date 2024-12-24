Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299931_term_abbrevs.
Lemma lem2299931 (x : int) (y : int) : (term0 x y) = ((term1 x y) = (int_ge x y)).
Proof. exact (eq_refl (term0 x y)). Qed.

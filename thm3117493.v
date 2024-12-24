Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117493_term_abbrevs.
Lemma lem3117493 (a : nat) (b : nat) : (term0 a b) = ((term1 a b) = (term2 a b)).
Proof. exact (eq_refl (term0 a b)). Qed.

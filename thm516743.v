Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516743_term_abbrevs.
Lemma lem516743 (m : nat) (n : nat) (p : nat) : (term0 m n p) = ((term1 n m p) = (term2 m n p)).
Proof. exact (eq_refl (term0 m n p)). Qed.

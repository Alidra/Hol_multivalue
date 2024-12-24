Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3116350_term_abbrevs.
Lemma lem3116350 (n : nat) (m : nat) : (term0 m n) = ((m = n) = (term1 n m)).
Proof. exact (eq_refl (term0 m n)). Qed.

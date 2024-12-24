Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516837_term_abbrevs.
Lemma lem516837 (m : nat) (n : nat) : (term0 m n) = (((Nat.mul m n) = 0) = (term1 m n)).
Proof. exact (eq_refl (term0 m n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299877_term_abbrevs.
Lemma lem2299877 (x : int) (n : nat) : (term0 x n) = ((term1 x n) = (term2 x n)).
Proof. exact (eq_refl (term0 x n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841378_term_abbrevs.
Lemma lem2841378 (k : nat) (n : nat) : (term0 k n) = ((term1 k n) = (term2 k n)).
Proof. exact (eq_refl (term0 k n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528241_term_abbrevs.
Lemma lem528241 (n : nat) : (term0 n) = ((term1 n) = (BIT1 n)).
Proof. exact (eq_refl (term0 n)). Qed.
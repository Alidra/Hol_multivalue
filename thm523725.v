Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm523725_term_abbrevs.
Lemma lem523725 (n : nat) : (term0 n) = ((term1 n) = True).
Proof. exact (eq_refl (term0 n)). Qed.

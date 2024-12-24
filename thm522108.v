Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522108_term_abbrevs.
Lemma lem522108 (m : nat) (n : nat) : (term0 m n) = ((term1 n m) = n).
Proof. exact (eq_refl (term0 m n)). Qed.

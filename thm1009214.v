Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009214_term_abbrevs.
Lemma lem1009214 (m : nat) (n : nat) : ((term0 m n) = (Nat.pow m n)) = ((term0 m n) = (Nat.pow m n)).
Proof. exact (eq_refl ((term0 m n) = (Nat.pow m n))). Qed.

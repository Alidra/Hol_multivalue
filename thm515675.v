Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515675_term_abbrevs.
Lemma lem515675 (n : nat) : (term0 n) = ((Nat.mul 0 n) = 0).
Proof. exact (eq_refl (term0 n)). Qed.

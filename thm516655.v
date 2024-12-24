Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516655_term_abbrevs.
Require Import thm516627_spec.
Lemma lem516653 (n : nat) : term0 n.
Proof. exact (@lem516627 n). Qed.
Lemma lem516654 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516655 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem516654 n) (@lem516653 n)). Qed.

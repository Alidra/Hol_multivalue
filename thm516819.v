Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516819_term_abbrevs.
Require Import thm516788_spec.
Lemma lem516817 (n : nat) : term0 n.
Proof. exact (@lem516788 n). Qed.
Lemma lem516818 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem516819 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem516818 n) (@lem516817 n)). Qed.

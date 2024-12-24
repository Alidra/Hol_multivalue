Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm521123_term_abbrevs.
Require Import LET_ANTISYM_spec.
Lemma lem521118 (m : nat) : term0 m.
Proof. exact (@lem93009 m). Qed.
Lemma lem521119 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem521120 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem521119 m) (@lem521118 m)). Qed.
Lemma lem521121 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem521120 m n). Qed.
Lemma lem521122 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem521123 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem521122 n m) (@lem521121 m n)). Qed.

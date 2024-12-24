Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111466_term_abbrevs.
Require Import thm1111458_spec.
Lemma lem1111463 {A : Type'} (s : nat -> A) : term0 A s.
Proof. exact (@lem1111458 A s). Qed.
Lemma lem1111464 {A : Type'} (s : nat -> A) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem1111465 {A : Type'} (s : nat -> A) : term1 A s.
Proof. exact (EQ_MP (@lem1111464 A s) (@lem1111463 A s)). Qed.
Lemma lem1111466 {A : Type'} (s : nat -> A) (n : nat) : term2 A s n.
Proof. exact (@lem1111465 A s n). Qed.

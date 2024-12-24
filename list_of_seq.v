Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import list_of_seq_term_abbrevs.
Require Import thm1111462_spec.
Require Import thm1111466_spec.
Require Import thm1111467_spec.
Lemma lem1111468 {A : Type'} (s : nat -> A) (n : nat) : (term0 A s n) = (term1 A s n).
Proof. exact (EQ_MP (@lem1111467 A s n) (@lem1111466 A s n)). Qed.
Lemma lem1111469 {A : Type'} (s : nat -> A) (n : nat) : term2 A s n.
Proof. exact (conj (@lem1111462 A s) (@lem1111468 A s n)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7603427_term_abbrevs.
Require Import thm7594702_spec.
Require Import thm7598119_spec.
Lemma lem7603425 {A : Type'} (n : nat) : term0 A n.
Proof. exact (EQ_MP (@lem7594702 A n) (@lem7598119 A n)). Qed.
Lemma lem7603426 (n : nat) : term1 n.
Proof. exact (@lem7603425 unit n). Qed.
Lemma lem7603427 : term2.
Proof. exact (@lem7603426 term3). Qed.

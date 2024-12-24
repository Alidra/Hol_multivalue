Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm159520_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem159518 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem159519 (n : nat) (m : nat) : ((term1 m n) = m) = (term2 n m).
Proof. exact (@lem159518 ((term1 m n) = m)). Qed.
Lemma lem159520 (n : nat) (m : nat) : (term2 n m) = ((term1 m n) = m).
Proof. exact (SYM (@lem159519 n m)). Qed.

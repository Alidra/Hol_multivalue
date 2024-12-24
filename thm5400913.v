Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400913_term_abbrevs.
Require Import thm5400787_spec.
Require Import thm5400788_spec.
Lemma lem5400910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem5400788 A s t) (@lem5400787 A s t)). Qed.
Lemma lem5400911 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term1 s t).
Proof. exact (@lem5400910 nat s t). Qed.
Lemma lem5400912 (m : nat) (n : nat) : ((term2 m n) = (dotdot m n)) = (term3 m n).
Proof. exact (@lem5400911 (term2 m n) (dotdot m n)). Qed.
Lemma lem5400913 (m : nat) (n : nat) : (term3 m n) = ((term2 m n) = (dotdot m n)).
Proof. exact (SYM (@lem5400912 m n)). Qed.

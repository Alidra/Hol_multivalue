Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400908_term_abbrevs.
Require Import thm5400787_spec.
Require Import thm5400788_spec.
Lemma lem5400905 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem5400788 A s t) (@lem5400787 A s t)). Qed.
Lemma lem5400906 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term1 s t).
Proof. exact (@lem5400905 nat s t). Qed.
Lemma lem5400907 (m : nat) (n : nat) : ((term2 m n) = (term3 m n)) = (term4 m n).
Proof. exact (@lem5400906 (term2 m n) (term3 m n)). Qed.
Lemma lem5400908 (m : nat) (n : nat) : (term4 m n) = ((term2 m n) = (term3 m n)).
Proof. exact (SYM (@lem5400907 m n)). Qed.

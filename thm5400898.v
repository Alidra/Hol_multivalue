Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400898_term_abbrevs.
Require Import thm5400787_spec.
Require Import thm5400788_spec.
Lemma lem5400895 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem5400788 A s t) (@lem5400787 A s t)). Qed.
Lemma lem5400896 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term1 s t).
Proof. exact (@lem5400895 nat s t). Qed.
Lemma lem5400897 (m : nat) : ((term2 m) = term3) = (term4 m).
Proof. exact (@lem5400896 (term2 m) term3). Qed.
Lemma lem5400898 (m : nat) : (term4 m) = ((term2 m) = term3).
Proof. exact (SYM (@lem5400897 m)). Qed.

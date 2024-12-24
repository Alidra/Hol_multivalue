Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418304_term_abbrevs.
Require Import thm5400859_spec.
Require Import thm5400860_spec.
Require Import thm5400877_spec.
Require Import thm5400908_spec.
Require Import thm5400913_spec.
Require Import thm5418287_spec.
Require Import thm5418288_spec.
Lemma lem5418295 (m : nat) (n : nat) (h1 : term0 m n) : (term1 m n) = (dotdot m n).
Proof. exact (EQ_MP (@lem5400913 m n) (@lem5418287 m n h1)). Qed.
Lemma lem5418296 (m : nat) (n : nat) (h1 : term0 m n) : (term0 m n) = ((term1 m n) = (dotdot m n)).
Proof. exact (prop_ext (fun h2 : term0 m n => @lem5418295 m n h1) (fun h2 : (term1 m n) = (dotdot m n) => @lem5400877 m n h1)). Qed.
Lemma lem5418297 (m : nat) (n : nat) (h1 : term0 m n) : (term1 m n) = (dotdot m n).
Proof. exact (EQ_MP (@lem5418296 m n h1) (@lem5400877 m n h1)). Qed.
Lemma lem5418298 (m : nat) (n : nat) : term2 m n.
Proof. exact (fun h0 : term0 m n => @lem5418297 m n h0). Qed.
Lemma lem5418299 (m : nat) (n : nat) (h1 : term3 m n) : (term1 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem5400908 m n) (@lem5418288 m n h1)). Qed.
Lemma lem5418300 (m : nat) (n : nat) (h1 : term3 m n) : (term3 m n) = ((term1 m n) = (term4 m n)).
Proof. exact (prop_ext (fun h2 : term3 m n => @lem5418299 m n h1) (fun h2 : (term1 m n) = (term4 m n) => @lem5400860 m n h1)). Qed.
Lemma lem5418301 (m : nat) (n : nat) (h1 : term3 m n) : (term1 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem5418300 m n h1) (@lem5400860 m n h1)). Qed.
Lemma lem5418302 (m : nat) (n : nat) : term5 m n.
Proof. exact (fun h0 : term3 m n => @lem5418301 m n h0). Qed.
Lemma lem5418303 (m : nat) (n : nat) : term6 m n.
Proof. exact (conj (@lem5418302 m n) (@lem5418298 m n)). Qed.
Lemma lem5418304 (m : nat) (n : nat) : (term1 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem5400859 m n) (@lem5418303 m n)). Qed.

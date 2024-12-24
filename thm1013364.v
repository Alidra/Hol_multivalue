Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1013354 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1013355 (n : nat) : (((NUMERAL n) = (NUMERAL n)) = True) = ((NUMERAL n) = (NUMERAL n)).
Proof. exact (@lem1013354 ((NUMERAL n) = (NUMERAL n))). Qed.
Lemma lem1013357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1013358 (x : nat) : (x = x) = True.
Proof. exact (@lem1013357 nat x). Qed.
Lemma lem1013359 (n : nat) : ((NUMERAL n) = (NUMERAL n)) = True.
Proof. exact (@lem1013358 (NUMERAL n)). Qed.
Lemma lem1013360 (n : nat) : (((NUMERAL n) = (NUMERAL n)) = True) = True.
Proof. exact (TRANS (@lem1013355 n) (@lem1013359 n)). Qed.
Lemma lem1013361 (n : nat) : True = (((NUMERAL n) = (NUMERAL n)) = True).
Proof. exact (SYM (@lem1013360 n)). Qed.
Lemma lem1013364 (n : nat) : ((NUMERAL n) = (NUMERAL n)) = True.
Proof. exact (EQ_MP (@lem1013361 n) (@lem0)). Qed.

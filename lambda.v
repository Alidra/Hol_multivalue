Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import lambda_term_abbrevs.
Lemma lem7618314 {A B : Type'} : (@lambda A B) = (term0 A B).
Proof. exact (@lambda_def A B). Qed.
Lemma lem7618315 {A : Type'} (_98065 : nat -> A) : _98065 = _98065.
Proof. exact (eq_refl _98065). Qed.
Lemma lem7618316 {A B : Type'} (_98065 : nat -> A) : (@lambda A B _98065) = (term1 A B _98065).
Proof. exact (MK_COMB (@lem7618314 A B) (@lem7618315 A _98065)). Qed.
Lemma lem7618317 {A B : Type'} (_98065 : nat -> A) : (term1 A B _98065) = (term2 A B _98065).
Proof. exact (eq_refl (term1 A B _98065)). Qed.
Lemma lem7618318 {A B : Type'} (_98065 : nat -> A) : (@lambda A B _98065) = (term2 A B _98065).
Proof. exact (TRANS (@lem7618316 A B _98065) (@lem7618317 A B _98065)). Qed.
Lemma lem7618319 {A B : Type'} : term3 A B.
Proof. exact (fun _98065 : nat -> A => @lem7618318 A B _98065). Qed.
Lemma lem7618320 {A B : Type'} (_98065 : nat -> A) : term4 A B _98065.
Proof. exact (@lem7618319 A B _98065). Qed.
Lemma lem7618321 {A B : Type'} (_98065 : nat -> A) : (term4 A B _98065) = ((@lambda A B _98065) = (term2 A B _98065)).
Proof. exact (eq_refl (term4 A B _98065)). Qed.
Lemma lem7618322 {A B : Type'} (_98065 : nat -> A) : (@lambda A B _98065) = (term2 A B _98065).
Proof. exact (EQ_MP (@lem7618321 A B _98065) (@lem7618320 A B _98065)). Qed.
Lemma lem7618352 {A B : Type'} (g : nat -> A) : (@lambda A B g) = (term2 A B g).
Proof. exact (@lem7618322 A B g). Qed.
Lemma lem7618353 {A B : Type'} : term3 A B.
Proof. exact (fun g : nat -> A => @lem7618352 A B g). Qed.

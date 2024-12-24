Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_DEF_term_abbrevs.
Lemma lem3186477 {A : Type'} : (@INSERT A) = (term0 A).
Proof. exact (@INSERT_def A). Qed.
Lemma lem3186478 {A : Type'} (_32739 : A) : _32739 = _32739.
Proof. exact (eq_refl _32739). Qed.
Lemma lem3186479 {A : Type'} (_32739 : A) : (@INSERT A _32739) = (term1 A _32739).
Proof. exact (MK_COMB (@lem3186477 A) (@lem3186478 A _32739)). Qed.
Lemma lem3186480 {A : Type'} (_32739 : A) : (term1 A _32739) = (term2 A _32739).
Proof. exact (eq_refl (term1 A _32739)). Qed.
Lemma lem3186481 {A : Type'} (_32739 : A) : (@INSERT A _32739) = (term2 A _32739).
Proof. exact (TRANS (@lem3186479 A _32739) (@lem3186480 A _32739)). Qed.
Lemma lem3186482 {A : Type'} (_32740 : A -> Prop) : _32740 = _32740.
Proof. exact (eq_refl _32740). Qed.
Lemma lem3186483 {A : Type'} (_32739 : A) (_32740 : A -> Prop) : (@INSERT A _32739 _32740) = (term3 A _32739 _32740).
Proof. exact (MK_COMB (@lem3186481 A _32739) (@lem3186482 A _32740)). Qed.
Lemma lem3186484 {A : Type'} (_32740 : A -> Prop) (_32739 : A) : (term3 A _32739 _32740) = (term4 A _32740 _32739).
Proof. exact (eq_refl (term3 A _32739 _32740)). Qed.
Lemma lem3186485 {A : Type'} (_32740 : A -> Prop) (_32739 : A) : (@INSERT A _32739 _32740) = (term4 A _32740 _32739).
Proof. exact (TRANS (@lem3186483 A _32739 _32740) (@lem3186484 A _32740 _32739)). Qed.
Lemma lem3186486 {A : Type'} (_32739 : A) : term5 A _32739.
Proof. exact (fun _32740 : A -> Prop => @lem3186485 A _32740 _32739). Qed.
Lemma lem3186487 {A : Type'} : term6 A.
Proof. exact (fun _32739 : A => @lem3186486 A _32739). Qed.
Lemma lem3186488 {A : Type'} (_32739 : A) : term7 A _32739.
Proof. exact (@lem3186487 A _32739). Qed.
Lemma lem3186489 {A : Type'} (_32739 : A) : (term7 A _32739) = (term5 A _32739).
Proof. exact (eq_refl (term7 A _32739)). Qed.
Lemma lem3186490 {A : Type'} (_32739 : A) : term5 A _32739.
Proof. exact (EQ_MP (@lem3186489 A _32739) (@lem3186488 A _32739)). Qed.
Lemma lem3186491 {A : Type'} (_32739 : A) (_32740 : A -> Prop) : term8 A _32739 _32740.
Proof. exact (@lem3186490 A _32739 _32740). Qed.
Lemma lem3186492 {A : Type'} (_32740 : A -> Prop) (_32739 : A) : (term8 A _32739 _32740) = ((@INSERT A _32739 _32740) = (term4 A _32740 _32739)).
Proof. exact (eq_refl (term8 A _32739 _32740)). Qed.
Lemma lem3186493 {A : Type'} (_32740 : A -> Prop) (_32739 : A) : (@INSERT A _32739 _32740) = (term4 A _32740 _32739).
Proof. exact (EQ_MP (@lem3186492 A _32740 _32739) (@lem3186491 A _32739 _32740)). Qed.
Lemma lem3186536 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term4 A s x).
Proof. exact (@lem3186493 A s x). Qed.
Lemma lem3186537 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (fun x : A => @lem3186536 A s x). Qed.
Lemma lem3186538 {A : Type'} : term10 A.
Proof. exact (fun s : A -> Prop => @lem3186537 A s). Qed.

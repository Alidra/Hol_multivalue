Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOICE_term_abbrevs.
Lemma lem3203661 {A : Type'} : (@CHOICE A) = (term0 A).
Proof. exact (@CHOICE_def A). Qed.
Lemma lem3203662 {A : Type'} (_32934 : A -> Prop) : _32934 = _32934.
Proof. exact (eq_refl _32934). Qed.
Lemma lem3203663 {A : Type'} (_32934 : A -> Prop) : (@CHOICE A _32934) = (term1 A _32934).
Proof. exact (MK_COMB (@lem3203661 A) (@lem3203662 A _32934)). Qed.
Lemma lem3203664 {A : Type'} (_32934 : A -> Prop) : (term1 A _32934) = (term2 A _32934).
Proof. exact (eq_refl (term1 A _32934)). Qed.
Lemma lem3203665 {A : Type'} (_32934 : A -> Prop) : (@CHOICE A _32934) = (term2 A _32934).
Proof. exact (TRANS (@lem3203663 A _32934) (@lem3203664 A _32934)). Qed.
Lemma lem3203666 {A : Type'} : term3 A.
Proof. exact (fun _32934 : A -> Prop => @lem3203665 A _32934). Qed.
Lemma lem3203667 {A : Type'} (_32934 : A -> Prop) : term4 A _32934.
Proof. exact (@lem3203666 A _32934). Qed.
Lemma lem3203668 {A : Type'} (_32934 : A -> Prop) : (term4 A _32934) = ((@CHOICE A _32934) = (term2 A _32934)).
Proof. exact (eq_refl (term4 A _32934)). Qed.
Lemma lem3203669 {A : Type'} (_32934 : A -> Prop) : (@CHOICE A _32934) = (term2 A _32934).
Proof. exact (EQ_MP (@lem3203668 A _32934) (@lem3203667 A _32934)). Qed.
Lemma lem3203699 {A : Type'} (s : A -> Prop) : (@CHOICE A s) = (term2 A s).
Proof. exact (@lem3203669 A s). Qed.
Lemma lem3203700 {A : Type'} : term3 A.
Proof. exact (fun s : A -> Prop => @lem3203699 A s). Qed.

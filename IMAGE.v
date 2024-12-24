Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_term_abbrevs.
Lemma lem3199485 {A B : Type'} : (@IMAGE A B) = (term0 A B).
Proof. exact (@IMAGE_def A B). Qed.
Lemma lem3199486 {A B : Type'} (_32859 : A -> B) : _32859 = _32859.
Proof. exact (eq_refl _32859). Qed.
Lemma lem3199487 {A B : Type'} (_32859 : A -> B) : (@IMAGE A B _32859) = (term1 A B _32859).
Proof. exact (MK_COMB (@lem3199485 A B) (@lem3199486 A B _32859)). Qed.
Lemma lem3199488 {A B : Type'} (_32859 : A -> B) : (term1 A B _32859) = (term2 A B _32859).
Proof. exact (eq_refl (term1 A B _32859)). Qed.
Lemma lem3199489 {A B : Type'} (_32859 : A -> B) : (@IMAGE A B _32859) = (term2 A B _32859).
Proof. exact (TRANS (@lem3199487 A B _32859) (@lem3199488 A B _32859)). Qed.
Lemma lem3199490 {A : Type'} (_32860 : A -> Prop) : _32860 = _32860.
Proof. exact (eq_refl _32860). Qed.
Lemma lem3199491 {A B : Type'} (_32859 : A -> B) (_32860 : A -> Prop) : (@IMAGE A B _32859 _32860) = (term3 A B _32859 _32860).
Proof. exact (MK_COMB (@lem3199489 A B _32859) (@lem3199490 A _32860)). Qed.
Lemma lem3199492 {A B : Type'} (_32860 : A -> Prop) (_32859 : A -> B) : (term3 A B _32859 _32860) = (term4 A B _32860 _32859).
Proof. exact (eq_refl (term3 A B _32859 _32860)). Qed.
Lemma lem3199493 {A B : Type'} (_32860 : A -> Prop) (_32859 : A -> B) : (@IMAGE A B _32859 _32860) = (term4 A B _32860 _32859).
Proof. exact (TRANS (@lem3199491 A B _32859 _32860) (@lem3199492 A B _32860 _32859)). Qed.
Lemma lem3199494 {A B : Type'} (_32859 : A -> B) : term5 A B _32859.
Proof. exact (fun _32860 : A -> Prop => @lem3199493 A B _32860 _32859). Qed.
Lemma lem3199495 {A B : Type'} : term6 A B.
Proof. exact (fun _32859 : A -> B => @lem3199494 A B _32859). Qed.
Lemma lem3199496 {A B : Type'} (_32859 : A -> B) : term7 A B _32859.
Proof. exact (@lem3199495 A B _32859). Qed.
Lemma lem3199497 {A B : Type'} (_32859 : A -> B) : (term7 A B _32859) = (term5 A B _32859).
Proof. exact (eq_refl (term7 A B _32859)). Qed.
Lemma lem3199498 {A B : Type'} (_32859 : A -> B) : term5 A B _32859.
Proof. exact (EQ_MP (@lem3199497 A B _32859) (@lem3199496 A B _32859)). Qed.
Lemma lem3199499 {A B : Type'} (_32859 : A -> B) (_32860 : A -> Prop) : term8 A B _32859 _32860.
Proof. exact (@lem3199498 A B _32859 _32860). Qed.
Lemma lem3199500 {A B : Type'} (_32860 : A -> Prop) (_32859 : A -> B) : (term8 A B _32859 _32860) = ((@IMAGE A B _32859 _32860) = (term4 A B _32860 _32859)).
Proof. exact (eq_refl (term8 A B _32859 _32860)). Qed.
Lemma lem3199501 {A B : Type'} (_32860 : A -> Prop) (_32859 : A -> B) : (@IMAGE A B _32859 _32860) = (term4 A B _32860 _32859).
Proof. exact (EQ_MP (@lem3199500 A B _32860 _32859) (@lem3199499 A B _32859 _32860)). Qed.
Lemma lem3199544 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term4 A B s f).
Proof. exact (@lem3199501 A B s f). Qed.
Lemma lem3199545 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (fun f : A -> B => @lem3199544 A B s f). Qed.
Lemma lem3199546 {A B : Type'} : term10 A B.
Proof. exact (fun s : A -> Prop => @lem3199545 A B s). Qed.

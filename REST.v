Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REST_term_abbrevs.
Lemma lem3204688 {A : Type'} : (@REST A) = (term0 A).
Proof. exact (@REST_def A). Qed.
Lemma lem3204689 {A : Type'} (_32939 : A -> Prop) : _32939 = _32939.
Proof. exact (eq_refl _32939). Qed.
Lemma lem3204690 {A : Type'} (_32939 : A -> Prop) : (@REST A _32939) = (term1 A _32939).
Proof. exact (MK_COMB (@lem3204688 A) (@lem3204689 A _32939)). Qed.
Lemma lem3204691 {A : Type'} (_32939 : A -> Prop) : (term1 A _32939) = (term2 A _32939).
Proof. exact (eq_refl (term1 A _32939)). Qed.
Lemma lem3204692 {A : Type'} (_32939 : A -> Prop) : (@REST A _32939) = (term2 A _32939).
Proof. exact (TRANS (@lem3204690 A _32939) (@lem3204691 A _32939)). Qed.
Lemma lem3204693 {A : Type'} : term3 A.
Proof. exact (fun _32939 : A -> Prop => @lem3204692 A _32939). Qed.
Lemma lem3204694 {A : Type'} (_32939 : A -> Prop) : term4 A _32939.
Proof. exact (@lem3204693 A _32939). Qed.
Lemma lem3204695 {A : Type'} (_32939 : A -> Prop) : (term4 A _32939) = ((@REST A _32939) = (term2 A _32939)).
Proof. exact (eq_refl (term4 A _32939)). Qed.
Lemma lem3204696 {A : Type'} (_32939 : A -> Prop) : (@REST A _32939) = (term2 A _32939).
Proof. exact (EQ_MP (@lem3204695 A _32939) (@lem3204694 A _32939)). Qed.
Lemma lem3204726 {A : Type'} (s : A -> Prop) : (@REST A s) = (term2 A s).
Proof. exact (@lem3204696 A s). Qed.
Lemma lem3204727 {A : Type'} : term3 A.
Proof. exact (fun s : A -> Prop => @lem3204726 A s). Qed.

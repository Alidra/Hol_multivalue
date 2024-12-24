Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BETA_THM_term_abbrevs.
Lemma lem404 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = (f y).
Proof. exact (eq_refl (term0 A B f y)). Qed.
Lemma lem405 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem406 {A B : Type'} (f : A -> B) (y : A) : (term1 A B f y) = (term2 A B f y).
Proof. exact (MK_COMB (@lem405 B) (@lem404 A B f y)). Qed.
Lemma lem407 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem408 {A B : Type'} (f : A -> B) (y : A) : ((term0 A B f y) = (f y)) = ((f y) = (f y)).
Proof. exact (MK_COMB (@lem406 A B f y) (@lem407 A B f y)). Qed.
Lemma lem409 {A B : Type'} (f : A -> B) (y : A) : ((f y) = (f y)) = ((term0 A B f y) = (f y)).
Proof. exact (SYM (@lem408 A B f y)). Qed.
Lemma lem410 {A B : Type'} (f : A -> B) (y : A) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem411 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = (f y).
Proof. exact (EQ_MP (@lem409 A B f y) (@lem410 A B f y)). Qed.
Lemma lem416 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (fun y : A => @lem411 A B f y). Qed.
Lemma lem421 {A B : Type'} : term4 A B.
Proof. exact (fun f : A -> B => @lem416 A B f). Qed.

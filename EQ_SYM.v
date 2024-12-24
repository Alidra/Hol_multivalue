Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_SYM_term_abbrevs.
Lemma lem318 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem319 {A : Type'} (x : A) (y : A) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem318 A x y h1)). Qed.
Lemma lem320 {A : Type'} (y : A) (x : A) : term0 A y x.
Proof. exact (fun h0 : x = y => @lem319 A x y h0). Qed.
Lemma lem325 {A : Type'} (x : A) : term1 A x.
Proof. exact (fun y : A => @lem320 A y x). Qed.
Lemma lem330 {A : Type'} : term2 A.
Proof. exact (fun x : A => @lem325 A x). Qed.

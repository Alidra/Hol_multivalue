Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COMMA_DEF_term_abbrevs.
Lemma lem45456 {A B : Type'} : (@pair A B) = (term0 A B).
Proof. exact (@pair_def A B). Qed.
Lemma lem45457 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem45458 {A B : Type'} (x : A) : (@pair A B x) = (term1 A B x).
Proof. exact (MK_COMB (@lem45456 A B) (@lem45457 A x)). Qed.
Lemma lem45459 {A B : Type'} (x : A) : (term1 A B x) = (term2 A B x).
Proof. exact (eq_refl (term1 A B x)). Qed.
Lemma lem45460 {A B : Type'} (x : A) : (@pair A B x) = (term2 A B x).
Proof. exact (TRANS (@lem45458 A B x) (@lem45459 A B x)). Qed.
Lemma lem45461 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem45462 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term3 A B x y).
Proof. exact (MK_COMB (@lem45460 A B x) (@lem45461 B y)). Qed.
Lemma lem45463 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = (term4 A B x y).
Proof. exact (eq_refl (term3 A B x y)). Qed.
Lemma lem45464 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term4 A B x y).
Proof. exact (TRANS (@lem45462 A B x y) (@lem45463 A B x y)). Qed.
Lemma lem45465 {A B : Type'} (x : A) : term5 A B x.
Proof. exact (fun y : B => @lem45464 A B x y). Qed.
Lemma lem45466 {A B : Type'} : term6 A B.
Proof. exact (fun x : A => @lem45465 A B x). Qed.

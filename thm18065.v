Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18065_term_abbrevs.
Require Import thm0_spec.
Require Import thm17963_spec.
Require Import thm17964_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem18045 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem17964 A P) (@lem17963 A P)). Qed.
Lemma lem18046 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (@lem18045 A P). Qed.
Lemma lem18051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18052 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem18051) (@lem18046 A P)). Qed.
Lemma lem18057 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem18058 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = ((term1 A P) = (term1 A P)).
Proof. exact (MK_COMB (@lem18052 A P) (@lem18057 A P)). Qed.
Lemma lem18060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem18061 (x : Prop) : (x = x) = True.
Proof. exact (@lem18060 Prop x). Qed.
Lemma lem18062 {A : Type'} (P : A -> Prop) : ((term1 A P) = (term1 A P)) = True.
Proof. exact (@lem18061 (term1 A P)). Qed.
Lemma lem18063 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = True.
Proof. exact (TRANS (@lem18058 A P) (@lem18062 A P)). Qed.
Lemma lem18064 {A : Type'} (P : A -> Prop) : True = ((term0 A P) = (term1 A P)).
Proof. exact (SYM (@lem18063 A P)). Qed.
Lemma lem18065 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem18064 A P) (@lem0)). Qed.

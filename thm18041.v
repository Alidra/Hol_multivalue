Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18041_term_abbrevs.
Require Import thm0_spec.
Require Import thm17960_spec.
Require Import thm17961_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem18021 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem17961 A P) (@lem17960 A P)). Qed.
Lemma lem18022 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (@lem18021 A P). Qed.
Lemma lem18027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18028 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (MK_COMB (@lem18027) (@lem18022 A P)). Qed.
Lemma lem18033 {A : Type'} (P : A -> Prop) : (term1 A P) = (term1 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem18034 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = ((term1 A P) = (term1 A P)).
Proof. exact (MK_COMB (@lem18028 A P) (@lem18033 A P)). Qed.
Lemma lem18036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem18037 (x : Prop) : (x = x) = True.
Proof. exact (@lem18036 Prop x). Qed.
Lemma lem18038 {A : Type'} (P : A -> Prop) : ((term1 A P) = (term1 A P)) = True.
Proof. exact (@lem18037 (term1 A P)). Qed.
Lemma lem18039 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = True.
Proof. exact (TRANS (@lem18034 A P) (@lem18038 A P)). Qed.
Lemma lem18040 {A : Type'} (P : A -> Prop) : True = ((term0 A P) = (term1 A P)).
Proof. exact (SYM (@lem18039 A P)). Qed.
Lemma lem18041 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem18040 A P) (@lem0)). Qed.

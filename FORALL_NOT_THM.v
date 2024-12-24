Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_NOT_THM_term_abbrevs.
Require Import NOT_EXISTS_THM_spec.
Lemma lem10886 {A : Type'} (P : A -> Prop) (h1 : (term0 A P) = (term1 A P)) : (term0 A P) = (term1 A P).
Proof. exact (h1). Qed.
Lemma lem10887 {A : Type'} (P : A -> Prop) (h1 : (term0 A P) = (term1 A P)) : (term1 A P) = (term0 A P).
Proof. exact (SYM (@lem10886 A P h1)). Qed.
Lemma lem10888 {A : Type'} (P : A -> Prop) (h1 : (term1 A P) = (term0 A P)) : (term1 A P) = (term0 A P).
Proof. exact (h1). Qed.
Lemma lem10889 {A : Type'} (P : A -> Prop) (h1 : (term1 A P) = (term0 A P)) : (term0 A P) = (term1 A P).
Proof. exact (SYM (@lem10888 A P h1)). Qed.
Lemma lem10890 {A : Type'} (P : A -> Prop) : ((term0 A P) = (term1 A P)) = ((term1 A P) = (term0 A P)).
Proof. exact (prop_ext (fun h1 : (term0 A P) = (term1 A P) => @lem10887 A P h1) (fun h1 : (term1 A P) = (term0 A P) => @lem10889 A P h1)). Qed.
Lemma lem10891 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem10890 A P)). Qed.
Lemma lem10892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem10893 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem10892 A) (@lem10891 A)). Qed.
Lemma lem10894 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem10893 A) (@lem10660 A)). Qed.
Lemma lem10895 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (@lem10894 A P). Qed.
Lemma lem10896 {A : Type'} (P : A -> Prop) : (term6 A P) = ((term1 A P) = (term0 A P)).
Proof. exact (eq_refl (term6 A P)). Qed.
Lemma lem10899 {A : Type'} (P : A -> Prop) : (term1 A P) = (term0 A P).
Proof. exact (EQ_MP (@lem10896 A P) (@lem10895 A P)). Qed.
Lemma lem10900 {A : Type'} (P : A -> Prop) : (term1 A P) = (term0 A P).
Proof. exact (@lem10899 A P). Qed.
Lemma lem10905 {A : Type'} : term5 A.
Proof. exact (fun P : A -> Prop => @lem10900 A P). Qed.

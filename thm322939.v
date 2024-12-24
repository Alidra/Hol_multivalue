Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm322939_term_abbrevs.
Require Import thm307612_spec.
Require Import thm309905_spec.
Lemma lem322861 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem322862 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (@lem322861 A lt2). Qed.
Lemma lem322885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem322886 {A : Type'} (lt2 : type1402 A) : (term1 A lt2) = (term2 A lt2).
Proof. exact (MK_COMB (@lem322885) (@lem322862 A lt2)). Qed.
Lemma lem322935 {A B : Type'} (lt2 : type1402 A) : (term3 A B lt2) = (term3 A B lt2).
Proof. exact (eq_refl (term3 A B lt2)). Qed.
Lemma lem322936 {A B : Type'} (lt2 : type1402 A) : (term4 A B lt2) = (term5 A B lt2).
Proof. exact (MK_COMB (@lem322886 A lt2) (@lem322935 A B lt2)). Qed.
Lemma lem322939 {A B : Type'} (lt2 : type1402 A) : (term5 A B lt2) = (term4 A B lt2).
Proof. exact (SYM (@lem322936 A B lt2)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GEQ_DEF_term_abbrevs.
Lemma lem44146 {A : Type'} : (@GEQ A) = (term0 A).
Proof. exact (@GEQ_def A). Qed.
Lemma lem44147 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem44148 {A : Type'} (a : A) : (@GEQ A a) = (term1 A a).
Proof. exact (MK_COMB (@lem44146 A) (@lem44147 A a)). Qed.
Lemma lem44149 {A : Type'} (a : A) : (term1 A a) = (term2 A a).
Proof. exact (eq_refl (term1 A a)). Qed.
Lemma lem44150 {A : Type'} (a : A) : (@GEQ A a) = (term2 A a).
Proof. exact (TRANS (@lem44148 A a) (@lem44149 A a)). Qed.
Lemma lem44151 {A : Type'} (b : A) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem44152 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (term3 A a b).
Proof. exact (MK_COMB (@lem44150 A a) (@lem44151 A b)). Qed.
Lemma lem44153 {A : Type'} (a : A) (b : A) : (term3 A a b) = (a = b).
Proof. exact (eq_refl (term3 A a b)). Qed.
Lemma lem44154 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (TRANS (@lem44152 A a b) (@lem44153 A a b)). Qed.
Lemma lem44155 {A : Type'} (a : A) : term4 A a.
Proof. exact (fun b : A => @lem44154 A a b). Qed.
Lemma lem44156 {A : Type'} : term5 A.
Proof. exact (fun a : A => @lem44155 A a). Qed.

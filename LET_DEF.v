Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LET_DEF_term_abbrevs.
Lemma lem44123 {A B : Type'} : (@LET A B) = (term0 A B).
Proof. exact (@LET_def A B). Qed.
Lemma lem44124 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem44125 {A B : Type'} (f : A -> B) : (@LET A B f) = (term1 A B f).
Proof. exact (MK_COMB (@lem44123 A B) (@lem44124 A B f)). Qed.
Lemma lem44126 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem44127 {A B : Type'} (f : A -> B) : (@LET A B f) = (term2 A B f).
Proof. exact (TRANS (@lem44125 A B f) (@lem44126 A B f)). Qed.
Lemma lem44128 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem44129 {A B : Type'} (f : A -> B) (x : A) : (@LET A B f x) = (term3 A B f x).
Proof. exact (MK_COMB (@lem44127 A B f) (@lem44128 A x)). Qed.
Lemma lem44130 {A B : Type'} (f : A -> B) (x : A) : (term3 A B f x) = (f x).
Proof. exact (eq_refl (term3 A B f x)). Qed.
Lemma lem44131 {A B : Type'} (f : A -> B) (x : A) : (@LET A B f x) = (f x).
Proof. exact (TRANS (@lem44129 A B f x) (@lem44130 A B f x)). Qed.
Lemma lem44132 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (fun x : A => @lem44131 A B f x). Qed.
Lemma lem44133 {A B : Type'} : term5 A B.
Proof. exact (fun f : A -> B => @lem44132 A B f). Qed.

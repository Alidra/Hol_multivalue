Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import mk_pair_def_term_abbrevs.
Lemma lem44162 {A B : Type'} : (@mk_pair A B) = (term0 A B).
Proof. exact (@mk_pair_def A B). Qed.
Lemma lem44163 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem44164 {A B : Type'} (x : A) : (@mk_pair A B x) = (term1 A B x).
Proof. exact (MK_COMB (@lem44162 A B) (@lem44163 A x)). Qed.
Lemma lem44165 {A B : Type'} (x : A) : (term1 A B x) = (term2 A B x).
Proof. exact (eq_refl (term1 A B x)). Qed.
Lemma lem44166 {A B : Type'} (x : A) : (@mk_pair A B x) = (term2 A B x).
Proof. exact (TRANS (@lem44164 A B x) (@lem44165 A B x)). Qed.
Lemma lem44167 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem44168 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term3 A B x y).
Proof. exact (MK_COMB (@lem44166 A B x) (@lem44167 B y)). Qed.
Lemma lem44169 {A B : Type'} (x : A) (y : B) : (term3 A B x y) = (term4 A B x y).
Proof. exact (eq_refl (term3 A B x y)). Qed.
Lemma lem44170 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (term4 A B x y).
Proof. exact (TRANS (@lem44168 A B x y) (@lem44169 A B x y)). Qed.
Lemma lem44171 {A B : Type'} (x : A) : term5 A B x.
Proof. exact (fun y : B => @lem44170 A B x y). Qed.
Lemma lem44172 {A B : Type'} : term6 A B.
Proof. exact (fun x : A => @lem44171 A B x). Qed.

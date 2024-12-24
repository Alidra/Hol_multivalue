Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import one_RECURSION_term_abbrevs.
Lemma lem16019 {A : Type'} (e : A) : (term0 A e) = e.
Proof. exact (eq_refl (term0 A e)). Qed.
Lemma lem16020 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem16021 {A : Type'} (e : A) : (term1 A e) = (@eq A e).
Proof. exact (MK_COMB (@lem16020 A) (@lem16019 A e)). Qed.
Lemma lem16022 {A : Type'} (e : A) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem16023 {A : Type'} (e : A) : ((term0 A e) = e) = (e = e).
Proof. exact (MK_COMB (@lem16021 A e) (@lem16022 A e)). Qed.
Lemma lem16024 {A : Type'} (e : A) : (e = e) = ((term0 A e) = e).
Proof. exact (SYM (@lem16023 A e)). Qed.
Lemma lem16025 {A : Type'} (e : A) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem16026 {A : Type'} (e : A) : (term0 A e) = e.
Proof. exact (EQ_MP (@lem16024 A e) (@lem16025 A e)). Qed.
Lemma lem16027 {A : Type'} (e : A) : term2 A e.
Proof. exact (ex_intro (term3 A e) (term4 A e) (@lem16026 A e)). Qed.
Lemma lem16032 {A : Type'} : term5 A.
Proof. exact (fun e : A => @lem16027 A e). Qed.

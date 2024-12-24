Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import minimal_term_abbrevs.
Lemma lem273021 : minimal = term0.
Proof. exact (@minimal_def). Qed.
Lemma lem273022 (_6373 : nat -> Prop) : _6373 = _6373.
Proof. exact (eq_refl _6373). Qed.
Lemma lem273023 (_6373 : nat -> Prop) : (minimal _6373) = (term1 _6373).
Proof. exact (MK_COMB (@lem273021) (@lem273022 _6373)). Qed.
Lemma lem273024 (_6373 : nat -> Prop) : (term1 _6373) = (term2 _6373).
Proof. exact (eq_refl (term1 _6373)). Qed.
Lemma lem273025 (_6373 : nat -> Prop) : (minimal _6373) = (term2 _6373).
Proof. exact (TRANS (@lem273023 _6373) (@lem273024 _6373)). Qed.
Lemma lem273026 : term3.
Proof. exact (fun _6373 : nat -> Prop => @lem273025 _6373). Qed.
Lemma lem273027 (_6373 : nat -> Prop) : term4 _6373.
Proof. exact (@lem273026 _6373). Qed.
Lemma lem273028 (_6373 : nat -> Prop) : (term4 _6373) = ((minimal _6373) = (term2 _6373)).
Proof. exact (eq_refl (term4 _6373)). Qed.
Lemma lem273029 (_6373 : nat -> Prop) : (minimal _6373) = (term2 _6373).
Proof. exact (EQ_MP (@lem273028 _6373) (@lem273027 _6373)). Qed.
Lemma lem273059 (P : nat -> Prop) : (minimal P) = (term2 P).
Proof. exact (@lem273029 P). Qed.
Lemma lem273060 : term3.
Proof. exact (fun P : nat -> Prop => @lem273059 P). Qed.

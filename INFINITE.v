Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_term_abbrevs.
Lemma lem3198504 {A : Type'} : (@INFINITE A) = (term0 A).
Proof. exact (@INFINITE_def A). Qed.
Lemma lem3198505 {A : Type'} (_32854 : A -> Prop) : _32854 = _32854.
Proof. exact (eq_refl _32854). Qed.
Lemma lem3198506 {A : Type'} (_32854 : A -> Prop) : (@INFINITE A _32854) = (term1 A _32854).
Proof. exact (MK_COMB (@lem3198504 A) (@lem3198505 A _32854)). Qed.
Lemma lem3198507 {A : Type'} (_32854 : A -> Prop) : (term1 A _32854) = (term2 A _32854).
Proof. exact (eq_refl (term1 A _32854)). Qed.
Lemma lem3198508 {A : Type'} (_32854 : A -> Prop) : (@INFINITE A _32854) = (term2 A _32854).
Proof. exact (TRANS (@lem3198506 A _32854) (@lem3198507 A _32854)). Qed.
Lemma lem3198509 {A : Type'} : term3 A.
Proof. exact (fun _32854 : A -> Prop => @lem3198508 A _32854). Qed.
Lemma lem3198510 {A : Type'} (_32854 : A -> Prop) : term4 A _32854.
Proof. exact (@lem3198509 A _32854). Qed.
Lemma lem3198511 {A : Type'} (_32854 : A -> Prop) : (term4 A _32854) = ((@INFINITE A _32854) = (term2 A _32854)).
Proof. exact (eq_refl (term4 A _32854)). Qed.
Lemma lem3198512 {A : Type'} (_32854 : A -> Prop) : (@INFINITE A _32854) = (term2 A _32854).
Proof. exact (EQ_MP (@lem3198511 A _32854) (@lem3198510 A _32854)). Qed.
Lemma lem3198542 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term2 A s).
Proof. exact (@lem3198512 A s). Qed.
Lemma lem3198543 {A : Type'} : term3 A.
Proof. exact (fun s : A -> Prop => @lem3198542 A s). Qed.

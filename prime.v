Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import prime_term_abbrevs.
Lemma lem3137958 : prime = term0.
Proof. exact (@prime_def). Qed.
Lemma lem3137959 (_32468 : nat) : _32468 = _32468.
Proof. exact (eq_refl _32468). Qed.
Lemma lem3137960 (_32468 : nat) : (prime _32468) = (term1 _32468).
Proof. exact (MK_COMB (@lem3137958) (@lem3137959 _32468)). Qed.
Lemma lem3137961 (_32468 : nat) : (term1 _32468) = (term2 _32468).
Proof. exact (eq_refl (term1 _32468)). Qed.
Lemma lem3137962 (_32468 : nat) : (prime _32468) = (term2 _32468).
Proof. exact (TRANS (@lem3137960 _32468) (@lem3137961 _32468)). Qed.
Lemma lem3137963 : term3.
Proof. exact (fun _32468 : nat => @lem3137962 _32468). Qed.
Lemma lem3137964 (_32468 : nat) : term4 _32468.
Proof. exact (@lem3137963 _32468). Qed.
Lemma lem3137965 (_32468 : nat) : (term4 _32468) = ((prime _32468) = (term2 _32468)).
Proof. exact (eq_refl (term4 _32468)). Qed.
Lemma lem3137966 (_32468 : nat) : (prime _32468) = (term2 _32468).
Proof. exact (EQ_MP (@lem3137965 _32468) (@lem3137964 _32468)). Qed.
Lemma lem3137996 (p : nat) : (prime p) = (term2 p).
Proof. exact (@lem3137966 p). Qed.
Lemma lem3137997 : term3.
Proof. exact (fun p : nat => @lem3137996 p). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931603_term_abbrevs.
Lemma lem7931590 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))).
Proof. exact (h1). Qed.
Lemma lem7931591 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7931592 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (term1 A) = (term2 A).
Proof. exact (MK_COMB (@lem7931591 A) (@lem7931590 A h1)). Qed.
Lemma lem7931593 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem7931594 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7931595 {A : Type'} : ((term1 A) = (term2 A)) = ((term1 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7931594 A) (@lem7931593 A)). Qed.
Lemma lem7931596 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7931597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7931598 {A : Type'} : (term4 A) = (term6 A).
Proof. exact (MK_COMB (@lem7931597) (@lem7931596 A)). Qed.
Lemma lem7931599 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7931600 {A : Type'} : ((term1 A) = (term3 A)) = ((term5 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7931598 A) (@lem7931599 A)). Qed.
Lemma lem7931601 {A : Type'} : ((term1 A) = (term2 A)) = ((term5 A) = (term3 A)).
Proof. exact (TRANS (@lem7931595 A) (@lem7931600 A)). Qed.
Lemma lem7931602 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (term5 A) = (term3 A).
Proof. exact (EQ_MP (@lem7931601 A) (@lem7931592 A h1)). Qed.
Lemma lem7931603 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : (term3 A) = (term5 A).
Proof. exact (SYM (@lem7931602 A h1)). Qed.

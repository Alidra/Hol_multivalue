Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932405_term_abbrevs.
Lemma lem7932392 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))).
Proof. exact (h1). Qed.
Lemma lem7932393 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7932394 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (term1 A) = (term2 A).
Proof. exact (MK_COMB (@lem7932393 A) (@lem7932392 A h1)). Qed.
Lemma lem7932395 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem7932396 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7932397 {A : Type'} : ((term1 A) = (term2 A)) = ((term1 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7932396 A) (@lem7932395 A)). Qed.
Lemma lem7932398 {A : Type'} : (term1 A) = (term5 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7932399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7932400 {A : Type'} : (term4 A) = (term6 A).
Proof. exact (MK_COMB (@lem7932399) (@lem7932398 A)). Qed.
Lemma lem7932401 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7932402 {A : Type'} : ((term1 A) = (term3 A)) = ((term5 A) = (term3 A)).
Proof. exact (MK_COMB (@lem7932400 A) (@lem7932401 A)). Qed.
Lemma lem7932403 {A : Type'} : ((term1 A) = (term2 A)) = ((term5 A) = (term3 A)).
Proof. exact (TRANS (@lem7932397 A) (@lem7932402 A)). Qed.
Lemma lem7932404 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (term5 A) = (term3 A).
Proof. exact (EQ_MP (@lem7932403 A) (@lem7932394 A h1)). Qed.
Lemma lem7932405 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (term3 A) = (term5 A).
Proof. exact (SYM (@lem7932404 A h1)). Qed.

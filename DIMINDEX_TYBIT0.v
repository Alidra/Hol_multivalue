Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_TYBIT0_term_abbrevs.
Require Import DIMINDEX_UNIQUE_spec.
Require Import thm7932146_spec.
Require Import thm7932263_spec.
Lemma lem7933088 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (h1). Qed.
Lemma lem7933089 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (h1). Qed.
Lemma lem7933090 {A : Type'} (n : nat) (h1 : term0 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933088 A n h1 (@lem7933089 A n h2)). Qed.
Lemma lem7933091 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : term1 A n.
Proof. exact (fun h0 : term0 A n => @lem7933090 A n h0 h1). Qed.
Lemma lem7933092 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (h1). Qed.
Lemma lem7933093 {A : Type'} (n : nat) (h1 : term0 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933091 A n h2 (@lem7933092 A n h1)). Qed.
Lemma lem7933094 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (fun h0 : @HAS_SIZE A (@UNIV A) n => @lem7933093 A n h1 h0). Qed.
Lemma lem7933095 {A : Type'} (n : nat) : term2 A n.
Proof. exact (fun h0 : term0 A n => @lem7933094 A n h0). Qed.
Lemma lem7933098 {A : Type'} (n : nat) : term0 A n.
Proof. exact (@lem7933095 A n (@lem7598120 A n)). Qed.
Lemma lem7933099 {A : Type'} (n : nat) : term3 A n.
Proof. exact (@lem7933098 (tybit0 A) n). Qed.
Lemma lem7933100 {A : Type'} : term4 A.
Proof. exact (@lem7933099 A (term5 A)). Qed.
Lemma lem7933102 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem7932263 A) (@lem7932146 A)). Qed.
Lemma lem7933103 {A : Type'} : (@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (term5 A).
Proof. exact (@lem7933100 A (@lem7933102 A)). Qed.

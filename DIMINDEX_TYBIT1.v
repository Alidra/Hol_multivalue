Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_TYBIT1_term_abbrevs.
Require Import DIMINDEX_UNIQUE_spec.
Require Import thm7932948_spec.
Require Import thm7933086_spec.
Lemma lem7933104 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (h1). Qed.
Lemma lem7933105 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : @HAS_SIZE A (@UNIV A) n.
Proof. exact (h1). Qed.
Lemma lem7933106 {A : Type'} (n : nat) (h1 : term0 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933104 A n h1 (@lem7933105 A n h2)). Qed.
Lemma lem7933107 {A : Type'} (n : nat) (h1 : @HAS_SIZE A (@UNIV A) n) : term1 A n.
Proof. exact (fun h0 : term0 A n => @lem7933106 A n h0 h1). Qed.
Lemma lem7933108 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (h1). Qed.
Lemma lem7933109 {A : Type'} (n : nat) (h1 : term0 A n) (h2 : @HAS_SIZE A (@UNIV A) n) : (@dimindex A (@UNIV A)) = n.
Proof. exact (@lem7933107 A n h2 (@lem7933108 A n h1)). Qed.
Lemma lem7933110 {A : Type'} (n : nat) (h1 : term0 A n) : term0 A n.
Proof. exact (fun h0 : @HAS_SIZE A (@UNIV A) n => @lem7933109 A n h1 h0). Qed.
Lemma lem7933111 {A : Type'} (n : nat) : term2 A n.
Proof. exact (fun h0 : term0 A n => @lem7933110 A n h0). Qed.
Lemma lem7933114 {A : Type'} (n : nat) : term0 A n.
Proof. exact (@lem7933111 A n (@lem7598120 A n)). Qed.
Lemma lem7933115 {A : Type'} (n : nat) : term3 A n.
Proof. exact (@lem7933114 (tybit1 A) n). Qed.
Lemma lem7933116 {A : Type'} : term4 A.
Proof. exact (@lem7933115 A (term5 A)). Qed.
Lemma lem7933118 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem7933086 A) (@lem7932948 A)). Qed.
Lemma lem7933119 {A : Type'} : (@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (term5 A).
Proof. exact (@lem7933116 A (@lem7933118 A)). Qed.

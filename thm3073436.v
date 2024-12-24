Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3073436_term_abbrevs.
Require Import int_divides_spec.
Require Import num_divides_spec.
Lemma lem3073398 (b : int) : term0 b.
Proof. exact (@lem2429416 b). Qed.
Lemma lem3073399 (b : int) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem3073400 (b : int) : term1 b.
Proof. exact (EQ_MP (@lem3073399 b) (@lem3073398 b)). Qed.
Lemma lem3073401 (b : int) (a : int) : term2 b a.
Proof. exact (@lem3073400 b a). Qed.
Lemma lem3073402 (b : int) (a : int) : (term2 b a) = ((int_divides a b) = (term3 b a)).
Proof. exact (eq_refl (term2 b a)). Qed.
Lemma lem3073404 (a : nat) : term4 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3073405 (a : nat) : (term4 a) = (term5 a).
Proof. exact (eq_refl (term4 a)). Qed.
Lemma lem3073406 (a : nat) : term5 a.
Proof. exact (EQ_MP (@lem3073405 a) (@lem3073404 a)). Qed.
Lemma lem3073407 (a : nat) (b : nat) : term6 a b.
Proof. exact (@lem3073406 a b). Qed.
Lemma lem3073408 (a : nat) (b : nat) : (term6 a b) = ((num_divides a b) = (term7 a b)).
Proof. exact (eq_refl (term6 a b)). Qed.
Lemma lem3073413 (a : nat) (b : nat) : (num_divides a b) = (term7 a b).
Proof. exact (EQ_MP (@lem3073408 a b) (@lem3073407 a b)). Qed.
Lemma lem3073415 (b : int) (a : int) : (int_divides a b) = (term3 b a).
Proof. exact (EQ_MP (@lem3073402 b a) (@lem3073401 b a)). Qed.
Lemma lem3073416 (b : nat) (a : nat) : (term7 a b) = (term8 b a).
Proof. exact (@lem3073415 (int_of_num b) (int_of_num a)). Qed.
Lemma lem3073421 (b : nat) (a : nat) : (num_divides a b) = (term8 b a).
Proof. exact (TRANS (@lem3073413 a b) (@lem3073416 b a)). Qed.
Lemma lem3073424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3073425 (b : nat) (a : nat) : (term9 a b) = (term10 b a).
Proof. exact (MK_COMB (@lem3073424) (@lem3073421 b a)). Qed.
Lemma lem3073432 (b : nat) (a : nat) : (term11 b a) = (term11 b a).
Proof. exact (eq_refl (term11 b a)). Qed.
Lemma lem3073433 (b : nat) (a : nat) : ((num_divides a b) = (term11 b a)) = ((term8 b a) = (term11 b a)).
Proof. exact (MK_COMB (@lem3073425 b a) (@lem3073432 b a)). Qed.
Lemma lem3073436 (b : nat) (a : nat) : ((term8 b a) = (term11 b a)) = ((num_divides a b) = (term11 b a)).
Proof. exact (SYM (@lem3073433 b a)). Qed.

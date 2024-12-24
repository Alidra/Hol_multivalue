Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_POW_term_abbrevs.
Require Import REAL_OF_NUM_POW_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307382 (x : nat) : term0 x.
Proof. exact (@lem1362595 x). Qed.
Lemma lem2307383 (x : nat) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307384 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem2307383 x) (@lem2307382 x)). Qed.
Lemma lem2307385 (x : nat) (n : nat) : term2 x n.
Proof. exact (@lem2307384 x n). Qed.
Lemma lem2307386 (x : nat) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2307387 (x : nat) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem2307386 x n) (@lem2307385 x n)). Qed.
Lemma lem2307389 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307390 (x : nat) : (real_of_num x) = (term5 x).
Proof. exact (@lem2307389 x). Qed.
Lemma lem2307391 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2307392 (x : nat) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2307391) (@lem2307390 x)). Qed.
Lemma lem2307393 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2307394 (x : nat) (n : nat) : (term3 x n) = (term8 x n).
Proof. exact (MK_COMB (@lem2307392 x) (@lem2307393 n)). Qed.
Lemma lem2307396 (x : int) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307397 (x : nat) (n : nat) : (term8 x n) = (term11 x n).
Proof. exact (@lem2307396 (int_of_num x) n). Qed.
Lemma lem2307398 (x : nat) (n : nat) : (term3 x n) = (term11 x n).
Proof. exact (TRANS (@lem2307394 x n) (@lem2307397 x n)). Qed.
Lemma lem2307399 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307400 (x : nat) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (MK_COMB (@lem2307399) (@lem2307398 x n)). Qed.
Lemma lem2307402 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307403 (x : nat) (n : nat) : (term4 x n) = (term14 x n).
Proof. exact (@lem2307402 (Nat.pow x n)). Qed.
Lemma lem2307404 (x : nat) (n : nat) : ((term3 x n) = (term4 x n)) = ((term11 x n) = (term14 x n)).
Proof. exact (MK_COMB (@lem2307400 x n) (@lem2307403 x n)). Qed.
Lemma lem2307406 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307407 (x : nat) (n : nat) : ((term11 x n) = (term14 x n)) = ((term15 x n) = (term16 x n)).
Proof. exact (@lem2307406 (term15 x n) (term16 x n)). Qed.
Lemma lem2307408 (x : nat) (n : nat) : ((term3 x n) = (term4 x n)) = ((term15 x n) = (term16 x n)).
Proof. exact (TRANS (@lem2307404 x n) (@lem2307407 x n)). Qed.
Lemma lem2307409 (x : nat) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (EQ_MP (@lem2307408 x n) (@lem2307387 x n)). Qed.
Lemma lem2307410 (x : nat) : term17 x.
Proof. exact (fun n : nat => @lem2307409 x n). Qed.
Lemma lem2307411 : term18.
Proof. exact (fun x : nat => @lem2307410 x). Qed.

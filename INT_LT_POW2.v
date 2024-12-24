Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_POW2_term_abbrevs.
Require Import REAL_LT_POW2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304635 (n : nat) : term0 n.
Proof. exact (@lem1642681 n). Qed.
Lemma lem2304636 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2304637 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2304636 n) (@lem2304635 n)). Qed.
Lemma lem2304639 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304640 : term3 = term4.
Proof. exact (@lem2304639 (NUMERAL 0)). Qed.
Lemma lem2304641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304642 : term5 = term6.
Proof. exact (MK_COMB (@lem2304641) (@lem2304640)). Qed.
Lemma lem2304644 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304645 : term7 = term8.
Proof. exact (@lem2304644 term9). Qed.
Lemma lem2304646 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2304647 : term10 = term11.
Proof. exact (MK_COMB (@lem2304646) (@lem2304645)). Qed.
Lemma lem2304648 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2304649 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem2304647) (@lem2304648 n)). Qed.
Lemma lem2304651 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2304652 (n : nat) : (term13 n) = (term16 n).
Proof. exact (@lem2304651 term17 n). Qed.
Lemma lem2304653 (n : nat) : (term12 n) = (term16 n).
Proof. exact (TRANS (@lem2304649 n) (@lem2304652 n)). Qed.
Lemma lem2304654 (n : nat) : (term1 n) = (term18 n).
Proof. exact (MK_COMB (@lem2304642) (@lem2304653 n)). Qed.
Lemma lem2304656 (x : int) (y : int) : (term19 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304657 (n : nat) : (term18 n) = (term20 n).
Proof. exact (@lem2304656 term21 (term22 n)). Qed.
Lemma lem2304658 (n : nat) : (term1 n) = (term20 n).
Proof. exact (TRANS (@lem2304654 n) (@lem2304657 n)). Qed.
Lemma lem2304659 (n : nat) : term20 n.
Proof. exact (EQ_MP (@lem2304658 n) (@lem2304637 n)). Qed.
Lemma lem2304660 : term23.
Proof. exact (fun n : nat => @lem2304659 n). Qed.

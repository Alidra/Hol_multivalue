Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_POW2_term_abbrevs.
Require Import REAL_LE_POW2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303030 (n : nat) : term0 n.
Proof. exact (@lem1643457 n). Qed.
Lemma lem2303031 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2303032 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2303031 n) (@lem2303030 n)). Qed.
Lemma lem2303034 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303035 : term3 = term4.
Proof. exact (@lem2303034 term5). Qed.
Lemma lem2303036 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303037 : term6 = term7.
Proof. exact (MK_COMB (@lem2303036) (@lem2303035)). Qed.
Lemma lem2303039 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303040 : term8 = term9.
Proof. exact (@lem2303039 term10). Qed.
Lemma lem2303041 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2303042 : term11 = term12.
Proof. exact (MK_COMB (@lem2303041) (@lem2303040)). Qed.
Lemma lem2303043 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2303044 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem2303042) (@lem2303043 n)). Qed.
Lemma lem2303046 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2303047 (n : nat) : (term14 n) = (term17 n).
Proof. exact (@lem2303046 term18 n). Qed.
Lemma lem2303048 (n : nat) : (term13 n) = (term17 n).
Proof. exact (TRANS (@lem2303044 n) (@lem2303047 n)). Qed.
Lemma lem2303049 (n : nat) : (term1 n) = (term19 n).
Proof. exact (MK_COMB (@lem2303037) (@lem2303048 n)). Qed.
Lemma lem2303051 (x : int) (y : int) : (term20 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303052 (n : nat) : (term19 n) = (term21 n).
Proof. exact (@lem2303051 term22 (term23 n)). Qed.
Lemma lem2303053 (n : nat) : (term1 n) = (term21 n).
Proof. exact (TRANS (@lem2303049 n) (@lem2303052 n)). Qed.
Lemma lem2303054 (n : nat) : term21 n.
Proof. exact (EQ_MP (@lem2303053 n) (@lem2303032 n)). Qed.
Lemma lem2303055 : term24.
Proof. exact (fun n : nat => @lem2303054 n). Qed.

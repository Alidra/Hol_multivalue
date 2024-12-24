Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE_1_term_abbrevs.
Require Import REAL_POW_LE_1_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308380 (n : nat) : term0 n.
Proof. exact (@lem1636789 n). Qed.
Lemma lem2308381 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308382 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308381 n) (@lem2308380 n)). Qed.
Lemma lem2308383 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308382 n (real_of_int x)). Qed.
Lemma lem2308384 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308385 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308384 x n) (@lem2308383 n x)). Qed.
Lemma lem2308387 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308388 : term5 = term6.
Proof. exact (@lem2308387 term7). Qed.
Lemma lem2308389 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308390 : term8 = term9.
Proof. exact (MK_COMB (@lem2308389) (@lem2308388)). Qed.
Lemma lem2308391 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308392 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2308390) (@lem2308391 x)). Qed.
Lemma lem2308394 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308395 (x : int) : (term11 x) = (term13 x).
Proof. exact (@lem2308394 term14 x). Qed.
Lemma lem2308396 (x : int) : (term10 x) = (term13 x).
Proof. exact (TRANS (@lem2308392 x) (@lem2308395 x)). Qed.
Lemma lem2308397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308398 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2308397) (@lem2308396 x)). Qed.
Lemma lem2308400 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308401 : term5 = term6.
Proof. exact (@lem2308400 term7). Qed.
Lemma lem2308402 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308403 : term8 = term9.
Proof. exact (MK_COMB (@lem2308402) (@lem2308401)). Qed.
Lemma lem2308405 (x : int) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308406 (x : int) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem2308403) (@lem2308405 x n)). Qed.
Lemma lem2308408 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308409 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (@lem2308408 term14 (int_pow x n)). Qed.
Lemma lem2308410 (x : int) (n : nat) : (term19 x n) = (term21 x n).
Proof. exact (TRANS (@lem2308406 x n) (@lem2308409 x n)). Qed.
Lemma lem2308411 (x : int) (n : nat) : (term3 x n) = (term22 x n).
Proof. exact (MK_COMB (@lem2308398 x) (@lem2308410 x n)). Qed.
Lemma lem2308412 (x : int) (n : nat) : term22 x n.
Proof. exact (EQ_MP (@lem2308411 x n) (@lem2308385 x n)). Qed.
Lemma lem2308413 (n : nat) : term23 n.
Proof. exact (fun x : int => @lem2308412 x n). Qed.
Lemma lem2308414 : term24.
Proof. exact (fun n : nat => @lem2308413 n). Qed.

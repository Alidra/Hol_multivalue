Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LT_term_abbrevs.
Require Import REAL_POW_LT_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2308415 (x : int) : term0 x.
Proof. exact (@lem1582551 (real_of_int x)). Qed.
Lemma lem2308416 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308417 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308416 x) (@lem2308415 x)). Qed.
Lemma lem2308418 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2308417 x n). Qed.
Lemma lem2308419 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2308420 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2308419 x n) (@lem2308418 x n)). Qed.
Lemma lem2308422 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308423 : term5 = term6.
Proof. exact (@lem2308422 (NUMERAL 0)). Qed.
Lemma lem2308424 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308425 : term7 = term8.
Proof. exact (MK_COMB (@lem2308424) (@lem2308423)). Qed.
Lemma lem2308426 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308427 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2308425) (@lem2308426 x)). Qed.
Lemma lem2308429 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308430 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2308429 term13 x). Qed.
Lemma lem2308431 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2308427 x) (@lem2308430 x)). Qed.
Lemma lem2308432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308433 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2308432) (@lem2308431 x)). Qed.
Lemma lem2308435 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308436 : term5 = term6.
Proof. exact (@lem2308435 (NUMERAL 0)). Qed.
Lemma lem2308437 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308438 : term7 = term8.
Proof. exact (MK_COMB (@lem2308437) (@lem2308436)). Qed.
Lemma lem2308440 (x : int) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308441 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem2308438) (@lem2308440 x n)). Qed.
Lemma lem2308443 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308444 (x : int) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (@lem2308443 term13 (int_pow x n)). Qed.
Lemma lem2308445 (x : int) (n : nat) : (term18 x n) = (term20 x n).
Proof. exact (TRANS (@lem2308441 x n) (@lem2308444 x n)). Qed.
Lemma lem2308446 (x : int) (n : nat) : (term3 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2308433 x) (@lem2308445 x n)). Qed.
Lemma lem2308447 (x : int) (n : nat) : term21 x n.
Proof. exact (EQ_MP (@lem2308446 x n) (@lem2308420 x n)). Qed.
Lemma lem2308448 (x : int) : term22 x.
Proof. exact (fun n : nat => @lem2308447 x n). Qed.
Lemma lem2308449 : term23.
Proof. exact (fun x : int => @lem2308448 x). Qed.

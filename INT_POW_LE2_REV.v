Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_LE2_REV_term_abbrevs.
Require Import REAL_POW_LE2_REV_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2308334 (n : nat) : term0 n.
Proof. exact (@lem1650795 n). Qed.
Lemma lem2308335 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308336 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308335 n) (@lem2308334 n)). Qed.
Lemma lem2308337 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308336 n (real_of_int x)). Qed.
Lemma lem2308338 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308339 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308338 n x) (@lem2308337 n x)). Qed.
Lemma lem2308340 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308339 n x (real_of_int y)). Qed.
Lemma lem2308341 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308342 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2308341 n x y) (@lem2308340 n x y)). Qed.
Lemma lem2308344 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308345 : term7 = term8.
Proof. exact (@lem2308344 (NUMERAL 0)). Qed.
Lemma lem2308346 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308347 : term9 = term10.
Proof. exact (MK_COMB (@lem2308346) (@lem2308345)). Qed.
Lemma lem2308348 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2308349 (y : int) : (term11 y) = (term12 y).
Proof. exact (MK_COMB (@lem2308347) (@lem2308348 y)). Qed.
Lemma lem2308351 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308352 (y : int) : (term12 y) = (term14 y).
Proof. exact (@lem2308351 term15 y). Qed.
Lemma lem2308353 (y : int) : (term11 y) = (term14 y).
Proof. exact (TRANS (@lem2308349 y) (@lem2308352 y)). Qed.
Lemma lem2308354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2308355 (y : int) : (term16 y) = (term17 y).
Proof. exact (MK_COMB (@lem2308354) (@lem2308353 y)). Qed.
Lemma lem2308357 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308358 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2308359 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2308358) (@lem2308357 x n)). Qed.
Lemma lem2308361 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308362 (y : int) (n : nat) : (term18 y n) = (term19 y n).
Proof. exact (@lem2308361 y n). Qed.
Lemma lem2308363 (x : int) (y : int) (n : nat) : (term22 x y n) = (term23 x y n).
Proof. exact (MK_COMB (@lem2308359 x n) (@lem2308362 y n)). Qed.
Lemma lem2308365 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308366 (x : int) (y : int) (n : nat) : (term23 x y n) = (term24 x y n).
Proof. exact (@lem2308365 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308367 (x : int) (y : int) (n : nat) : (term22 x y n) = (term24 x y n).
Proof. exact (TRANS (@lem2308363 x y n) (@lem2308366 x y n)). Qed.
Lemma lem2308368 (x : int) (y : int) (n : nat) : (term25 x y n) = (term26 x y n).
Proof. exact (MK_COMB (@lem2308355 y) (@lem2308367 x y n)). Qed.
Lemma lem2308369 (n : nat) : (term27 n) = (term27 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2308370 (x : int) (y : int) (n : nat) : (term28 x y n) = (term29 x y n).
Proof. exact (MK_COMB (@lem2308369 n) (@lem2308368 x y n)). Qed.
Lemma lem2308371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2308372 (x : int) (y : int) (n : nat) : (term30 x y n) = (term31 x y n).
Proof. exact (MK_COMB (@lem2308371) (@lem2308370 x y n)). Qed.
Lemma lem2308374 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2308375 (n : nat) (x : int) (y : int) : (term5 n x y) = (term32 n x y).
Proof. exact (MK_COMB (@lem2308372 x y n) (@lem2308374 x y)). Qed.
Lemma lem2308376 (n : nat) (x : int) (y : int) : term32 n x y.
Proof. exact (EQ_MP (@lem2308375 n x y) (@lem2308342 n x y)). Qed.
Lemma lem2308377 (n : nat) (x : int) : term33 n x.
Proof. exact (fun y : int => @lem2308376 n x y). Qed.
Lemma lem2308378 (n : nat) : term34 n.
Proof. exact (fun x : int => @lem2308377 n x). Qed.
Lemma lem2308379 : term35.
Proof. exact (fun n : nat => @lem2308378 n). Qed.

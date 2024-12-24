Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_MUL_term_abbrevs.
Require Import REAL_LT_MUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304345 (x : int) : term0 x.
Proof. exact (@lem1487565 (real_of_int x)). Qed.
Lemma lem2304346 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304347 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304346 x) (@lem2304345 x)). Qed.
Lemma lem2304348 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304347 x (real_of_int y)). Qed.
Lemma lem2304349 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304350 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304349 x y) (@lem2304348 x y)). Qed.
Lemma lem2304352 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304353 : term5 = term6.
Proof. exact (@lem2304352 (NUMERAL 0)). Qed.
Lemma lem2304354 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304355 : term7 = term8.
Proof. exact (MK_COMB (@lem2304354) (@lem2304353)). Qed.
Lemma lem2304356 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304357 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2304355) (@lem2304356 x)). Qed.
Lemma lem2304359 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304360 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2304359 term13 x). Qed.
Lemma lem2304361 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2304357 x) (@lem2304360 x)). Qed.
Lemma lem2304362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304363 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2304362) (@lem2304361 x)). Qed.
Lemma lem2304365 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304366 : term5 = term6.
Proof. exact (@lem2304365 (NUMERAL 0)). Qed.
Lemma lem2304367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304368 : term7 = term8.
Proof. exact (MK_COMB (@lem2304367) (@lem2304366)). Qed.
Lemma lem2304369 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304370 (y : int) : (term9 y) = (term10 y).
Proof. exact (MK_COMB (@lem2304368) (@lem2304369 y)). Qed.
Lemma lem2304372 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304373 (y : int) : (term10 y) = (term12 y).
Proof. exact (@lem2304372 term13 y). Qed.
Lemma lem2304374 (y : int) : (term9 y) = (term12 y).
Proof. exact (TRANS (@lem2304370 y) (@lem2304373 y)). Qed.
Lemma lem2304375 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2304363 x) (@lem2304374 y)). Qed.
Lemma lem2304376 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304377 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2304376) (@lem2304375 x y)). Qed.
Lemma lem2304379 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304380 : term5 = term6.
Proof. exact (@lem2304379 (NUMERAL 0)). Qed.
Lemma lem2304381 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304382 : term7 = term8.
Proof. exact (MK_COMB (@lem2304381) (@lem2304380)). Qed.
Lemma lem2304384 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304385 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2304382) (@lem2304384 x y)). Qed.
Lemma lem2304387 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304388 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (@lem2304387 term13 (int_mul x y)). Qed.
Lemma lem2304389 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (TRANS (@lem2304385 x y) (@lem2304388 x y)). Qed.
Lemma lem2304390 (x : int) (y : int) : (term3 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2304377 x y) (@lem2304389 x y)). Qed.
Lemma lem2304391 (x : int) (y : int) : term25 x y.
Proof. exact (EQ_MP (@lem2304390 x y) (@lem2304350 x y)). Qed.
Lemma lem2304392 (x : int) : term26 x.
Proof. exact (fun y : int => @lem2304391 x y). Qed.
Lemma lem2304393 : term27.
Proof. exact (fun x : int => @lem2304392 x). Qed.

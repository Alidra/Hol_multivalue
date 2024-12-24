Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIFFSQ_term_abbrevs.
Require Import REAL_DIFFSQ_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301399 (x : int) : term0 x.
Proof. exact (@lem1524301 (real_of_int x)). Qed.
Lemma lem2301400 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301401 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301400 x) (@lem2301399 x)). Qed.
Lemma lem2301402 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301401 x (real_of_int y)). Qed.
Lemma lem2301403 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301404 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2301403 x y) (@lem2301402 x y)). Qed.
Lemma lem2301406 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301407 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2301408 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2301407) (@lem2301406 x y)). Qed.
Lemma lem2301410 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301411 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2301408 x y) (@lem2301410 x y)). Qed.
Lemma lem2301413 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301414 (x : int) (y : int) : (term11 x y) = (term14 x y).
Proof. exact (@lem2301413 (int_add x y) (int_sub x y)). Qed.
Lemma lem2301415 (x : int) (y : int) : (term3 x y) = (term14 x y).
Proof. exact (TRANS (@lem2301411 x y) (@lem2301414 x y)). Qed.
Lemma lem2301416 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301417 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2301416) (@lem2301415 x y)). Qed.
Lemma lem2301419 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301420 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2301419 x x). Qed.
Lemma lem2301421 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2301422 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2301421) (@lem2301420 x)). Qed.
Lemma lem2301424 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301425 (y : int) : (term17 y) = (term18 y).
Proof. exact (@lem2301424 y y). Qed.
Lemma lem2301426 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2301422 x) (@lem2301425 y)). Qed.
Lemma lem2301428 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301429 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2301428 (int_mul x x) (int_mul y y)). Qed.
Lemma lem2301430 (x : int) (y : int) : (term4 x y) = (term22 x y).
Proof. exact (TRANS (@lem2301426 x y) (@lem2301429 x y)). Qed.
Lemma lem2301431 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term14 x y) = (term22 x y)).
Proof. exact (MK_COMB (@lem2301417 x y) (@lem2301430 x y)). Qed.
Lemma lem2301433 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301434 (x : int) (y : int) : ((term14 x y) = (term22 x y)) = ((term23 x y) = (term24 x y)).
Proof. exact (@lem2301433 (term23 x y) (term24 x y)). Qed.
Lemma lem2301435 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term23 x y) = (term24 x y)).
Proof. exact (TRANS (@lem2301431 x y) (@lem2301434 x y)). Qed.
Lemma lem2301436 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2301435 x y) (@lem2301404 x y)). Qed.
Lemma lem2301437 (x : int) : term25 x.
Proof. exact (fun y : int => @lem2301436 x y). Qed.
Lemma lem2301438 : term26.
Proof. exact (fun x : int => @lem2301437 x). Qed.

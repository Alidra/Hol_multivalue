Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ENTIRE_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301439 (x : int) : term0 x.
Proof. exact (@lem1382769 (real_of_int x)). Qed.
Lemma lem2301440 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301441 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301440 x) (@lem2301439 x)). Qed.
Lemma lem2301442 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301441 x (real_of_int y)). Qed.
Lemma lem2301443 (x : int) (y : int) : (term2 x y) = (((term3 x y) = term4) = (term5 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301444 (x : int) (y : int) : ((term3 x y) = term4) = (term5 x y).
Proof. exact (EQ_MP (@lem2301443 x y) (@lem2301442 x y)). Qed.
Lemma lem2301446 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301447 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301448 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2301447) (@lem2301446 x y)). Qed.
Lemma lem2301450 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301451 : term4 = term10.
Proof. exact (@lem2301450 (NUMERAL 0)). Qed.
Lemma lem2301452 (x : int) (y : int) : ((term3 x y) = term4) = ((term6 x y) = term10).
Proof. exact (MK_COMB (@lem2301448 x y) (@lem2301451)). Qed.
Lemma lem2301454 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301455 (x : int) (y : int) : ((term6 x y) = term10) = ((int_mul x y) = term11).
Proof. exact (@lem2301454 (int_mul x y) term11). Qed.
Lemma lem2301456 (x : int) (y : int) : ((term3 x y) = term4) = ((int_mul x y) = term11).
Proof. exact (TRANS (@lem2301452 x y) (@lem2301455 x y)). Qed.
Lemma lem2301457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301458 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2301457) (@lem2301456 x y)). Qed.
Lemma lem2301460 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301461 : term4 = term10.
Proof. exact (@lem2301460 (NUMERAL 0)). Qed.
Lemma lem2301462 (x : int) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2301463 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term10).
Proof. exact (MK_COMB (@lem2301462 x) (@lem2301461)). Qed.
Lemma lem2301465 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301466 (x : int) : ((real_of_int x) = term10) = (x = term11).
Proof. exact (@lem2301465 x term11). Qed.
Lemma lem2301467 (x : int) : ((real_of_int x) = term4) = (x = term11).
Proof. exact (TRANS (@lem2301463 x) (@lem2301466 x)). Qed.
Lemma lem2301468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2301469 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2301468) (@lem2301467 x)). Qed.
Lemma lem2301471 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301472 : term4 = term10.
Proof. exact (@lem2301471 (NUMERAL 0)). Qed.
Lemma lem2301473 (y : int) : (term14 y) = (term14 y).
Proof. exact (eq_refl (term14 y)). Qed.
Lemma lem2301474 (y : int) : ((real_of_int y) = term4) = ((real_of_int y) = term10).
Proof. exact (MK_COMB (@lem2301473 y) (@lem2301472)). Qed.
Lemma lem2301476 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301477 (y : int) : ((real_of_int y) = term10) = (y = term11).
Proof. exact (@lem2301476 y term11). Qed.
Lemma lem2301478 (y : int) : ((real_of_int y) = term4) = (y = term11).
Proof. exact (TRANS (@lem2301474 y) (@lem2301477 y)). Qed.
Lemma lem2301479 (x : int) (y : int) : (term5 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2301469 x) (@lem2301478 y)). Qed.
Lemma lem2301480 (x : int) (y : int) : (((term3 x y) = term4) = (term5 x y)) = (((int_mul x y) = term11) = (term17 x y)).
Proof. exact (MK_COMB (@lem2301458 x y) (@lem2301479 x y)). Qed.
Lemma lem2301481 (x : int) (y : int) : ((int_mul x y) = term11) = (term17 x y).
Proof. exact (EQ_MP (@lem2301480 x y) (@lem2301444 x y)). Qed.
Lemma lem2301482 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2301481 x y). Qed.
Lemma lem2301483 : term19.
Proof. exact (fun x : int => @lem2301482 x). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_SUB_LADD_term_abbrevs.
Require Import REAL_LE_SUB_LADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303336 (x : int) : term0 x.
Proof. exact (@lem1516197 (real_of_int x)). Qed.
Lemma lem2303337 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303338 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303337 x) (@lem2303336 x)). Qed.
Lemma lem2303339 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303338 x (real_of_int y)). Qed.
Lemma lem2303340 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303341 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303340 x y) (@lem2303339 x y)). Qed.
Lemma lem2303342 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303341 x y (real_of_int z)). Qed.
Lemma lem2303343 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303344 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2303343 x z y) (@lem2303342 x y z)). Qed.
Lemma lem2303346 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2303347 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2303346 y z). Qed.
Lemma lem2303348 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2303349 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2303348 x) (@lem2303347 y z)). Qed.
Lemma lem2303351 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303352 (x : int) (y : int) (z : int) : (term10 x y z) = (term12 x y z).
Proof. exact (@lem2303351 x (int_sub y z)). Qed.
Lemma lem2303353 (x : int) (y : int) (z : int) : (term5 x y z) = (term12 x y z).
Proof. exact (TRANS (@lem2303349 x y z) (@lem2303352 x y z)). Qed.
Lemma lem2303354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303355 (x : int) (y : int) (z : int) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem2303354) (@lem2303353 x y z)). Qed.
Lemma lem2303357 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303358 (x : int) (z : int) : (term15 x z) = (term16 x z).
Proof. exact (@lem2303357 x z). Qed.
Lemma lem2303359 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303360 (x : int) (z : int) : (term17 x z) = (term18 x z).
Proof. exact (MK_COMB (@lem2303359) (@lem2303358 x z)). Qed.
Lemma lem2303361 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2303362 (x : int) (z : int) (y : int) : (term6 x z y) = (term19 x z y).
Proof. exact (MK_COMB (@lem2303360 x z) (@lem2303361 y)). Qed.
Lemma lem2303364 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303365 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (@lem2303364 (int_add x z) y). Qed.
Lemma lem2303366 (x : int) (z : int) (y : int) : (term6 x z y) = (term20 x z y).
Proof. exact (TRANS (@lem2303362 x z y) (@lem2303365 x z y)). Qed.
Lemma lem2303367 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term12 x y z) = (term20 x z y)).
Proof. exact (MK_COMB (@lem2303355 x y z) (@lem2303366 x z y)). Qed.
Lemma lem2303368 (x : int) (z : int) (y : int) : (term12 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem2303367 x z y) (@lem2303344 x z y)). Qed.
Lemma lem2303369 (x : int) (y : int) : term21 x y.
Proof. exact (fun z : int => @lem2303368 x z y). Qed.
Lemma lem2303370 (x : int) : term22 x.
Proof. exact (fun y : int => @lem2303369 x y). Qed.
Lemma lem2303371 : term23.
Proof. exact (fun x : int => @lem2303370 x). Qed.

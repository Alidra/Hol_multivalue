Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_RDISTRIB_term_abbrevs.
Require Import REAL_SUB_RDISTRIB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310337 (x : int) : term0 x.
Proof. exact (@lem1526749 (real_of_int x)). Qed.
Lemma lem2310338 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310339 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310338 x) (@lem2310337 x)). Qed.
Lemma lem2310340 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310339 x (real_of_int y)). Qed.
Lemma lem2310341 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310342 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2310341 x y) (@lem2310340 x y)). Qed.
Lemma lem2310343 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2310342 x y (real_of_int z)). Qed.
Lemma lem2310344 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2310345 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2310344 x y z) (@lem2310343 x y z)). Qed.
Lemma lem2310347 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310348 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2310349 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2310348) (@lem2310347 x y)). Qed.
Lemma lem2310350 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2310351 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2310349 x y) (@lem2310350 z)). Qed.
Lemma lem2310353 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310354 (x : int) (y : int) (z : int) : (term11 x y z) = (term14 x y z).
Proof. exact (@lem2310353 (int_sub x y) z). Qed.
Lemma lem2310355 (x : int) (y : int) (z : int) : (term5 x y z) = (term14 x y z).
Proof. exact (TRANS (@lem2310351 x y z) (@lem2310354 x y z)). Qed.
Lemma lem2310356 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310357 (x : int) (y : int) (z : int) : (term15 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2310356) (@lem2310355 x y z)). Qed.
Lemma lem2310359 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310360 (x : int) (z : int) : (term12 x z) = (term13 x z).
Proof. exact (@lem2310359 x z). Qed.
Lemma lem2310361 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310362 (x : int) (z : int) : (term17 x z) = (term18 x z).
Proof. exact (MK_COMB (@lem2310361) (@lem2310360 x z)). Qed.
Lemma lem2310364 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310365 (y : int) (z : int) : (term12 y z) = (term13 y z).
Proof. exact (@lem2310364 y z). Qed.
Lemma lem2310366 (x : int) (y : int) (z : int) : (term6 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2310362 x z) (@lem2310365 y z)). Qed.
Lemma lem2310368 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310369 (x : int) (y : int) (z : int) : (term19 x y z) = (term20 x y z).
Proof. exact (@lem2310368 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2310370 (x : int) (y : int) (z : int) : (term6 x y z) = (term20 x y z).
Proof. exact (TRANS (@lem2310366 x y z) (@lem2310369 x y z)). Qed.
Lemma lem2310371 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term14 x y z) = (term20 x y z)).
Proof. exact (MK_COMB (@lem2310357 x y z) (@lem2310370 x y z)). Qed.
Lemma lem2310373 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310374 (x : int) (y : int) (z : int) : ((term14 x y z) = (term20 x y z)) = ((term21 x y z) = (term22 x y z)).
Proof. exact (@lem2310373 (term21 x y z) (term22 x y z)). Qed.
Lemma lem2310375 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term21 x y z) = (term22 x y z)).
Proof. exact (TRANS (@lem2310371 x y z) (@lem2310374 x y z)). Qed.
Lemma lem2310376 (x : int) (y : int) (z : int) : (term21 x y z) = (term22 x y z).
Proof. exact (EQ_MP (@lem2310375 x y z) (@lem2310345 x y z)). Qed.
Lemma lem2310377 (x : int) (y : int) : term23 x y.
Proof. exact (fun z : int => @lem2310376 x y z). Qed.
Lemma lem2310378 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2310377 x y). Qed.
Lemma lem2310379 : term25.
Proof. exact (fun x : int => @lem2310378 x). Qed.

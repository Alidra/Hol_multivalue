Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_SUB_RADD_term_abbrevs.
Require Import REAL_LE_SUB_RADD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303372 (x : int) : term0 x.
Proof. exact (@lem1517224 (real_of_int x)). Qed.
Lemma lem2303373 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303374 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303373 x) (@lem2303372 x)). Qed.
Lemma lem2303375 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303374 x (real_of_int y)). Qed.
Lemma lem2303376 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303377 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303376 x y) (@lem2303375 x y)). Qed.
Lemma lem2303378 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303377 x y (real_of_int z)). Qed.
Lemma lem2303379 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 x y z) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303380 (x : int) (z : int) (y : int) : (term5 x y z) = (term6 x z y).
Proof. exact (EQ_MP (@lem2303379 x z y) (@lem2303378 x y z)). Qed.
Lemma lem2303382 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2303383 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303384 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2303383) (@lem2303382 x y)). Qed.
Lemma lem2303385 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303386 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2303384 x y) (@lem2303385 z)). Qed.
Lemma lem2303388 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303389 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2303388 (int_sub x y) z). Qed.
Lemma lem2303390 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2303386 x y z) (@lem2303389 x y z)). Qed.
Lemma lem2303391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303392 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2303391) (@lem2303390 x y z)). Qed.
Lemma lem2303394 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303395 (z : int) (y : int) : (term16 z y) = (term17 z y).
Proof. exact (@lem2303394 z y). Qed.
Lemma lem2303396 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2303397 (x : int) (z : int) (y : int) : (term6 x z y) = (term19 x z y).
Proof. exact (MK_COMB (@lem2303396 x) (@lem2303395 z y)). Qed.
Lemma lem2303399 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303400 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (@lem2303399 x (int_add z y)). Qed.
Lemma lem2303401 (x : int) (z : int) (y : int) : (term6 x z y) = (term20 x z y).
Proof. exact (TRANS (@lem2303397 x z y) (@lem2303400 x z y)). Qed.
Lemma lem2303402 (x : int) (z : int) (y : int) : ((term5 x y z) = (term6 x z y)) = ((term13 x y z) = (term20 x z y)).
Proof. exact (MK_COMB (@lem2303392 x y z) (@lem2303401 x z y)). Qed.
Lemma lem2303403 (x : int) (z : int) (y : int) : (term13 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem2303402 x z y) (@lem2303380 x z y)). Qed.
Lemma lem2303404 (x : int) (y : int) : term21 x y.
Proof. exact (fun z : int => @lem2303403 x z y). Qed.
Lemma lem2303405 (x : int) : term22 x.
Proof. exact (fun y : int => @lem2303404 x y). Qed.
Lemma lem2303406 : term23.
Proof. exact (fun x : int => @lem2303405 x). Qed.

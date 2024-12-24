Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_LT_term_abbrevs.
Require Import REAL_MAX_LT_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2305317 (x : int) : term0 x.
Proof. exact (@lem1569954 (real_of_int x)). Qed.
Lemma lem2305318 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305319 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305318 x) (@lem2305317 x)). Qed.
Lemma lem2305320 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305319 x (real_of_int y)). Qed.
Lemma lem2305321 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305322 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305321 x y) (@lem2305320 x y)). Qed.
Lemma lem2305323 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305322 x y (real_of_int z)). Qed.
Lemma lem2305324 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305325 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305324 x y z) (@lem2305323 x y z)). Qed.
Lemma lem2305327 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305328 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2305329 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2305328) (@lem2305327 x y)). Qed.
Lemma lem2305330 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305331 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2305329 x y) (@lem2305330 z)). Qed.
Lemma lem2305333 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305334 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2305333 (int_max x y) z). Qed.
Lemma lem2305335 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2305331 x y z) (@lem2305334 x y z)). Qed.
Lemma lem2305336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2305337 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2305336) (@lem2305335 x y z)). Qed.
Lemma lem2305339 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305340 (x : int) (z : int) : (term12 x z) = (int_lt x z).
Proof. exact (@lem2305339 x z). Qed.
Lemma lem2305341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2305342 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (MK_COMB (@lem2305341) (@lem2305340 x z)). Qed.
Lemma lem2305344 (x : int) (y : int) : (term12 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305345 (y : int) (z : int) : (term12 y z) = (int_lt y z).
Proof. exact (@lem2305344 y z). Qed.
Lemma lem2305346 (x : int) (y : int) (z : int) : (term6 x y z) = (term18 x y z).
Proof. exact (MK_COMB (@lem2305342 x z) (@lem2305345 y z)). Qed.
Lemma lem2305347 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term13 x y z) = (term18 x y z)).
Proof. exact (MK_COMB (@lem2305337 x y z) (@lem2305346 x y z)). Qed.
Lemma lem2305348 (x : int) (y : int) (z : int) : (term13 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem2305347 x y z) (@lem2305325 x y z)). Qed.
Lemma lem2305349 (x : int) (y : int) : term19 x y.
Proof. exact (fun z : int => @lem2305348 x y z). Qed.
Lemma lem2305350 (x : int) : term20 x.
Proof. exact (fun y : int => @lem2305349 x y). Qed.
Lemma lem2305351 : term21.
Proof. exact (fun x : int => @lem2305350 x). Qed.

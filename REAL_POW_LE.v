Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE_term_abbrevs.
Require Import REAL_POS_spec.
Require Import thm0_spec.
Require Import thm1340049_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1582314 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1582315 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1582314 h1 x). Qed.
Lemma lem1582316 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1582317 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1582316 x) (@lem1582315 x h1)). Qed.
Lemma lem1582318 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1582317 x h1 y). Qed.
Lemma lem1582319 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1582320 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1582319 x y) (@lem1582318 x y h1)). Qed.
Lemma lem1582321 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1582322 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1582320 x y h1 (@lem1582321 x y h2)). Qed.
Lemma lem1582323 (x : real) (y : real) (h1 : term5 x y) : term7 x y.
Proof. exact (fun h0 : term0 => @lem1582322 x y h0 h1). Qed.
Lemma lem1582324 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1582325 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1582323 x y h2 (@lem1582324 h1)). Qed.
Lemma lem1582326 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : term5 x y => @lem1582325 x y h1 h0). Qed.
Lemma lem1582327 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1582326 x y h1). Qed.
Lemma lem1582328 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1582327 x h1). Qed.
Lemma lem1582329 : term8.
Proof. exact (fun h0 : term0 => @lem1582328 h0). Qed.
Lemma lem1582330 : term0.
Proof. exact (@lem1582329 (@lem1340049)). Qed.
Lemma lem1582331 (x : real) : term1 x.
Proof. exact (@lem1582330 x). Qed.
Lemma lem1582332 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1582333 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1582332 x) (@lem1582331 x)). Qed.
Lemma lem1582334 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1582333 x y). Qed.
Lemma lem1582335 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1582337 (n : nat) : term9 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1582338 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem1582339 (n : nat) : term10 n.
Proof. exact (EQ_MP (@lem1582338 n) (@lem1582337 n)). Qed.
Lemma lem1582340 (n : nat) : (term10 n) = ((term10 n) = True).
Proof. exact (@lem7 (term10 n)). Qed.
Lemma lem1582342 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1582343 (x : real) (n : nat) : term12 x n.
Proof. exact (@lem1582342 x n). Qed.
Lemma lem1582344 (x : real) (n : nat) : (term12 x n) = ((term13 x n) = (term14 x n)).
Proof. exact (eq_refl (term12 x n)). Qed.
Lemma lem1582347 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1582349 (P : nat -> Prop) : term16 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1582350 (x : real) : term17 x.
Proof. exact (@lem1582349 (term18 x)). Qed.
Lemma lem1582351 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1582352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582353 (x : real) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1582352) (@lem1582351 x)). Qed.
Lemma lem1582354 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1582355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582356 (x : real) (n : nat) : (term25 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem1582355) (@lem1582354 x n)). Qed.
Lemma lem1582357 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (eq_refl (term27 x n)). Qed.
Lemma lem1582358 (x : real) (n : nat) : (term29 x n) = (term30 x n).
Proof. exact (MK_COMB (@lem1582356 x n) (@lem1582357 x n)). Qed.
Lemma lem1582359 (x : real) : (term31 x) = (term32 x).
Proof. exact (fun_ext (fun n : nat => @lem1582358 x n)). Qed.
Lemma lem1582360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582361 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1582360) (@lem1582359 x)). Qed.
Lemma lem1582362 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1582353 x) (@lem1582361 x)). Qed.
Lemma lem1582363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582364 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1582363) (@lem1582362 x)). Qed.
Lemma lem1582365 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1582366 (x : real) : (term39 x) = (term18 x).
Proof. exact (fun_ext (fun n : nat => @lem1582365 x n)). Qed.
Lemma lem1582367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582368 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1582367) (@lem1582366 x)). Qed.
Lemma lem1582369 (x : real) : (term17 x) = (term42 x).
Proof. exact (MK_COMB (@lem1582364 x) (@lem1582368 x)). Qed.
Lemma lem1582370 (x : real) : term42 x.
Proof. exact (EQ_MP (@lem1582369 x) (@lem1582350 x)). Qed.
Lemma lem1582371 (x : real) (n : nat) (h1 : term24 x n) : term24 x n.
Proof. exact (h1). Qed.
Lemma lem1582373 (x : real) : (term43 x) = term44.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1582374 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1582375 (x : real) : (term20 x) = term46.
Proof. exact (MK_COMB (@lem1582374) (@lem1582373 x)). Qed.
Lemma lem1582377 (n : nat) : (term10 n) = True.
Proof. exact (EQ_MP (@lem1582340 n) (@lem1582339 n)). Qed.
Lemma lem1582378 : term46 = True.
Proof. exact (@lem1582377 term47). Qed.
Lemma lem1582379 (x : real) : (term20 x) = True.
Proof. exact (TRANS (@lem1582375 x) (@lem1582378)). Qed.
Lemma lem1582380 (x : real) : True = (term20 x).
Proof. exact (SYM (@lem1582379 x)). Qed.
Lemma lem1582381 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem1582380 x) (@lem0)). Qed.
Lemma lem1582383 (x : real) (n : nat) : (term13 x n) = (term14 x n).
Proof. exact (EQ_MP (@lem1582344 x n) (@lem1582343 x n)). Qed.
Lemma lem1582384 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1582385 (x : real) (n : nat) : (term28 x n) = (term48 x n).
Proof. exact (MK_COMB (@lem1582384) (@lem1582383 x n)). Qed.
Lemma lem1582386 (x : real) (n : nat) : (term48 x n) = (term28 x n).
Proof. exact (SYM (@lem1582385 x n)). Qed.
Lemma lem1582388 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1582335 x y) (@lem1582334 x y)). Qed.
Lemma lem1582389 (x : real) (n : nat) : term49 x n.
Proof. exact (@lem1582388 x (real_pow x n)). Qed.
Lemma lem1582390 (x : real) : (term15 x) = ((term15 x) = True).
Proof. exact (@lem7 (term15 x)). Qed.
Lemma lem1582392 (x : real) (n : nat) : (term24 x n) = ((term24 x n) = True).
Proof. exact (@lem7 (term24 x n)). Qed.
Lemma lem1582397 (x : real) (h1 : term15 x) : (term15 x) = True.
Proof. exact (EQ_MP (@lem1582390 x) (@lem1582347 x h1)). Qed.
Lemma lem1582398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582399 (x : real) (h1 : term15 x) : (term50 x) = (and True).
Proof. exact (MK_COMB (@lem1582398) (@lem1582397 x h1)). Qed.
Lemma lem1582401 (x : real) (n : nat) (h1 : term24 x n) : (term24 x n) = True.
Proof. exact (EQ_MP (@lem1582392 x n) (@lem1582371 x n h1)). Qed.
Lemma lem1582402 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : (term51 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1582399 x h1) (@lem1582401 x n h2)). Qed.
Lemma lem1582404 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1582405 : (True /\ True) = True.
Proof. exact (@lem1582404 True). Qed.
Lemma lem1582406 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : (term51 x n) = True.
Proof. exact (TRANS (@lem1582402 x n h1 h2) (@lem1582405)). Qed.
Lemma lem1582407 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : True = (term51 x n).
Proof. exact (SYM (@lem1582406 x n h1 h2)). Qed.
Lemma lem1582408 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : term51 x n.
Proof. exact (EQ_MP (@lem1582407 x n h1 h2) (@lem0)). Qed.
Lemma lem1582409 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : term48 x n.
Proof. exact (@lem1582389 x n (@lem1582408 x n h1 h2)). Qed.
Lemma lem1582410 (x : real) (n : nat) (h1 : term15 x) (h2 : term24 x n) : term28 x n.
Proof. exact (EQ_MP (@lem1582386 x n) (@lem1582409 x n h1 h2)). Qed.
Lemma lem1582411 (n : nat) (x : real) (h1 : term15 x) : term30 x n.
Proof. exact (fun h0 : term24 x n => @lem1582410 x n h1 h0). Qed.
Lemma lem1582416 (x : real) (h1 : term15 x) : term34 x.
Proof. exact (fun n : nat => @lem1582411 n x h1). Qed.
Lemma lem1582417 (x : real) (h1 : term15 x) : term36 x.
Proof. exact (conj (@lem1582381 x) (@lem1582416 x h1)). Qed.
Lemma lem1582418 (x : real) (h1 : term15 x) : term41 x.
Proof. exact (@lem1582370 x (@lem1582417 x h1)). Qed.
Lemma lem1582419 (n : nat) (x : real) (h1 : term15 x) : term23 x n.
Proof. exact (@lem1582418 x h1 n). Qed.
Lemma lem1582420 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1582421 (n : nat) (x : real) (h1 : term15 x) : term24 x n.
Proof. exact (EQ_MP (@lem1582420 x n) (@lem1582419 n x h1)). Qed.
Lemma lem1582422 (n : nat) (x : real) (h1 : term15 x) : (term15 x) = (term24 x n).
Proof. exact (prop_ext (fun h2 : term15 x => @lem1582421 n x h1) (fun h2 : term24 x n => @lem1582347 x h1)). Qed.
Lemma lem1582423 (n : nat) (x : real) (h1 : term15 x) : term24 x n.
Proof. exact (EQ_MP (@lem1582422 n x h1) (@lem1582347 x h1)). Qed.
Lemma lem1582424 (x : real) (n : nat) : term52 x n.
Proof. exact (fun h0 : term15 x => @lem1582423 n x h0). Qed.
Lemma lem1582429 (x : real) : term53 x.
Proof. exact (fun n : nat => @lem1582424 x n). Qed.
Lemma lem1582434 : term54.
Proof. exact (fun x : real => @lem1582429 x). Qed.

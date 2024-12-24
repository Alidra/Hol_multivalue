Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_ZERO_term_abbrevs.
Require Import EXP_EQ_0_spec.
Require Import EXP_EQ_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem87288 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term0 _476 _475 _474 _477) = (term1 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem87289 (_474 : nat) (_475 : Prop) (n : nat) (_477 : nat) : (term2 n _475 _474 _477) = (term3 _474 _475 n _477).
Proof. exact (@lem87288 _474 _475 (term4 n) _477). Qed.
Lemma lem87290 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem87289 term7 (n = (NUMERAL 0)) n (NUMERAL 0)). Qed.
Lemma lem87291 (n : nat) : (term8 n) = ((term9 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem87292 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem87293 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem87292 n) (@lem87291 n)). Qed.
Lemma lem87294 (n : nat) : (term13 n) = ((term9 n) = term7).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem87295 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem87296 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem87295 n) (@lem87294 n)). Qed.
Lemma lem87297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem87298 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem87297) (@lem87296 n)). Qed.
Lemma lem87299 (n : nat) : (term6 n) = (term19 n).
Proof. exact (MK_COMB (@lem87298 n) (@lem87293 n)). Qed.
Lemma lem87300 (n : nat) : (term5 n) = ((term9 n) = (term20 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem87301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem87302 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem87301) (@lem87300 n)). Qed.
Lemma lem87303 (n : nat) : ((term5 n) = (term6 n)) = (((term9 n) = (term20 n)) = (term19 n)).
Proof. exact (MK_COMB (@lem87302 n) (@lem87299 n)). Qed.
Lemma lem87304 (n : nat) : ((term9 n) = (term20 n)) = (term19 n).
Proof. exact (EQ_MP (@lem87303 n) (@lem87290 n)). Qed.
Lemma lem87305 (n : nat) : (term19 n) = ((term9 n) = (term20 n)).
Proof. exact (SYM (@lem87304 n)). Qed.
Lemma lem87306 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem87323 (n : nat) (h1 : term23 n) : term23 n.
Proof. exact (h1). Qed.
Lemma lem87340 (x : nat) : term24 x.
Proof. exact (@lem87287 x). Qed.
Lemma lem87341 (x : nat) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem87342 (x : nat) : term25 x.
Proof. exact (EQ_MP (@lem87341 x) (@lem87340 x)). Qed.
Lemma lem87343 (x : nat) (n : nat) : term26 x n.
Proof. exact (@lem87342 x n). Qed.
Lemma lem87344 (x : nat) (n : nat) : (term26 x n) = (((Nat.pow x n) = term7) = (term27 x n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem87353 (x : nat) (n : nat) : ((Nat.pow x n) = term7) = (term27 x n).
Proof. exact (EQ_MP (@lem87344 x n) (@lem87343 x n)). Qed.
Lemma lem87354 (n : nat) : ((term9 n) = term7) = (term28 n).
Proof. exact (@lem87353 (NUMERAL 0) n). Qed.
Lemma lem87362 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem87363 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87364 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term29.
Proof. exact (MK_COMB (@lem87363) (@lem87362 n h1)). Qed.
Lemma lem87365 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem87366 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem87364 n h1) (@lem87365)). Qed.
Lemma lem87368 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87369 (x : nat) : (x = x) = True.
Proof. exact (@lem87368 nat x). Qed.
Lemma lem87370 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem87369 (NUMERAL 0)). Qed.
Lemma lem87371 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem87366 n h1) (@lem87370)). Qed.
Lemma lem87372 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem87373 (n : nat) (h1 : n = (NUMERAL 0)) : (term28 n) = term31.
Proof. exact (MK_COMB (@lem87372) (@lem87371 n h1)). Qed.
Lemma lem87375 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem87376 : term31 = True.
Proof. exact (@lem87375 ((NUMERAL 0) = term7)). Qed.
Lemma lem87377 (n : nat) (h1 : n = (NUMERAL 0)) : (term28 n) = True.
Proof. exact (TRANS (@lem87373 n h1) (@lem87376)). Qed.
Lemma lem87378 (n : nat) (h1 : n = (NUMERAL 0)) : ((term9 n) = term7) = True.
Proof. exact (TRANS (@lem87354 n) (@lem87377 n h1)). Qed.
Lemma lem87379 (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term9 n) = term7).
Proof. exact (SYM (@lem87378 n h1)). Qed.
Lemma lem87387 (m : nat) : term32 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem87388 (m : nat) : (term32 m) = (term33 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem87389 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem87388 m) (@lem87387 m)). Qed.
Lemma lem87390 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem87389 m n). Qed.
Lemma lem87391 (m : nat) (n : nat) : (term34 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term35 m n)).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem87393 (n : nat) : term36 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem87407 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term35 m n).
Proof. exact (EQ_MP (@lem87391 m n) (@lem87390 m n)). Qed.
Lemma lem87408 (n : nat) : ((term9 n) = (NUMERAL 0)) = (term37 n).
Proof. exact (@lem87407 (NUMERAL 0) n). Qed.
Lemma lem87412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87413 (x : nat) : (x = x) = True.
Proof. exact (@lem87412 nat x). Qed.
Lemma lem87414 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem87413 (NUMERAL 0)). Qed.
Lemma lem87415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem87416 : term38 = (and True).
Proof. exact (MK_COMB (@lem87415) (@lem87414)). Qed.
Lemma lem87418 (n : nat) (h1 : term23 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem87393 n (@lem87323 n h1)). Qed.
Lemma lem87419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem87420 (n : nat) (h1 : term23 n) : (term23 n) = (~ False).
Proof. exact (MK_COMB (@lem87419) (@lem87418 n h1)). Qed.
Lemma lem87422 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem87423 (n : nat) (h1 : term23 n) : (term23 n) = True.
Proof. exact (TRANS (@lem87420 n h1) (@lem87422)). Qed.
Lemma lem87424 (n : nat) (h1 : term23 n) : (term37 n) = (True /\ True).
Proof. exact (MK_COMB (@lem87416) (@lem87423 n h1)). Qed.
Lemma lem87426 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem87427 : (True /\ True) = True.
Proof. exact (@lem87426 True). Qed.
Lemma lem87428 (n : nat) (h1 : term23 n) : (term37 n) = True.
Proof. exact (TRANS (@lem87424 n h1) (@lem87427)). Qed.
Lemma lem87429 (n : nat) (h1 : term23 n) : ((term9 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem87408 n) (@lem87428 n h1)). Qed.
Lemma lem87430 (n : nat) (h1 : term23 n) : True = ((term9 n) = (NUMERAL 0)).
Proof. exact (SYM (@lem87429 n h1)). Qed.
Lemma lem87432 (n : nat) (h1 : term23 n) : (term9 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem87430 n h1) (@lem0)). Qed.
Lemma lem87433 (n : nat) (h1 : term23 n) : (term23 n) = ((term9 n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : term23 n => @lem87432 n h1) (fun h2 : (term9 n) = (NUMERAL 0) => @lem87323 n h1)). Qed.
Lemma lem87434 (n : nat) (h1 : term23 n) : (term9 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem87433 n h1) (@lem87323 n h1)). Qed.
Lemma lem87435 (n : nat) : term12 n.
Proof. exact (fun h0 : term23 n => @lem87434 n h0). Qed.
Lemma lem87436 (n : nat) (h1 : n = (NUMERAL 0)) : (term9 n) = term7.
Proof. exact (EQ_MP (@lem87379 n h1) (@lem0)). Qed.
Lemma lem87437 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((term9 n) = term7).
Proof. exact (prop_ext (fun h2 : n = (NUMERAL 0) => @lem87436 n h1) (fun h2 : (term9 n) = term7 => @lem87306 n h1)). Qed.
Lemma lem87438 (n : nat) (h1 : n = (NUMERAL 0)) : (term9 n) = term7.
Proof. exact (EQ_MP (@lem87437 n h1) (@lem87306 n h1)). Qed.
Lemma lem87439 (n : nat) : term16 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem87438 n h0). Qed.
Lemma lem87440 (n : nat) : term19 n.
Proof. exact (conj (@lem87439 n) (@lem87435 n)). Qed.
Lemma lem87441 (n : nat) : (term9 n) = (term20 n).
Proof. exact (EQ_MP (@lem87305 n) (@lem87440 n)). Qed.
Lemma lem87446 : term39.
Proof. exact (fun n : nat => @lem87441 n). Qed.

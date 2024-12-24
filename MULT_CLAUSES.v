Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_CLAUSES_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT1_THM_spec.
Require Import MULT_0_spec.
Require Import MULT_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80977_spec.
Lemma lem81332 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem81348 : term1.
Proof. exact (proj1 (@lem81332)). Qed.
Lemma lem81349 (m : nat) : term2 m.
Proof. exact (@lem81348 m). Qed.
Lemma lem81350 (m : nat) : (term2 m) = ((term3 m) = m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem81352 : term4.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem81353 (n : nat) : term5 n.
Proof. exact (@lem81352 n). Qed.
Lemma lem81354 (n : nat) : (term5 n) = ((term6 n) = n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem81356 (m : nat) : term7 m.
Proof. exact (@lem81331 m). Qed.
Lemma lem81357 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem81358 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem81357 m) (@lem81356 m)). Qed.
Lemma lem81359 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem81358 m n). Qed.
Lemma lem81360 (m : nat) (n : nat) : (term9 m n) = ((term10 m n) = (term11 m n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem81362 (m : nat) : term12 m.
Proof. exact (@lem81121 m). Qed.
Lemma lem81363 (m : nat) : (term12 m) = ((term13 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem81365 : term14.
Proof. exact (proj2 (@lem80977)). Qed.
Lemma lem81366 (m : nat) : term15 m.
Proof. exact (@lem81365 m). Qed.
Lemma lem81367 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem81368 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem81367 m) (@lem81366 m)). Qed.
Lemma lem81369 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem81368 m n). Qed.
Lemma lem81370 (m : nat) (n : nat) : (term17 m n) = ((term18 m n) = (term19 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem81372 : term20.
Proof. exact (proj1 (@lem80977)). Qed.
Lemma lem81373 (n : nat) : term21 n.
Proof. exact (@lem81372 n). Qed.
Lemma lem81374 (n : nat) : (term21 n) = ((term22 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem81376 (n : nat) : term23 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem81377 (n : nat) : (term23 n) = ((term24 n) = (term25 n)).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem81388 (n : nat) : (term22 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81374 n) (@lem81373 n)). Qed.
Lemma lem81389 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81390 (n : nat) : (term26 n) = term27.
Proof. exact (MK_COMB (@lem81389) (@lem81388 n)). Qed.
Lemma lem81391 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem81392 (n : nat) : ((term22 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81390 n) (@lem81391)). Qed.
Lemma lem81394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81395 (x : nat) : (x = x) = True.
Proof. exact (@lem81394 nat x). Qed.
Lemma lem81396 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81395 (NUMERAL 0)). Qed.
Lemma lem81397 (n : nat) : ((term22 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem81392 n) (@lem81396)). Qed.
Lemma lem81398 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem81397 n)). Qed.
Lemma lem81399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81400 : term20 = term30.
Proof. exact (MK_COMB (@lem81399) (@lem81398)). Qed.
Lemma lem81402 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81403 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81402 nat t). Qed.
Lemma lem81404 : term30 = True.
Proof. exact (@lem81403 True). Qed.
Lemma lem81405 : term20 = True.
Proof. exact (TRANS (@lem81400) (@lem81404)). Qed.
Lemma lem81406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81407 : term33 = (and True).
Proof. exact (MK_COMB (@lem81406) (@lem81405)). Qed.
Lemma lem81417 (m : nat) : (term13 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81363 m) (@lem81362 m)). Qed.
Lemma lem81418 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81419 (m : nat) : (term34 m) = term27.
Proof. exact (MK_COMB (@lem81418) (@lem81417 m)). Qed.
Lemma lem81420 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem81421 (m : nat) : ((term13 m) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81419 m) (@lem81420)). Qed.
Lemma lem81423 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81424 (x : nat) : (x = x) = True.
Proof. exact (@lem81423 nat x). Qed.
Lemma lem81425 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81424 (NUMERAL 0)). Qed.
Lemma lem81426 (m : nat) : ((term13 m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem81421 m) (@lem81425)). Qed.
Lemma lem81427 : term35 = term29.
Proof. exact (fun_ext (fun m : nat => @lem81426 m)). Qed.
Lemma lem81428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81429 : term36 = term30.
Proof. exact (MK_COMB (@lem81428) (@lem81427)). Qed.
Lemma lem81431 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81432 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81431 nat t). Qed.
Lemma lem81433 : term30 = True.
Proof. exact (@lem81432 True). Qed.
Lemma lem81434 : term36 = True.
Proof. exact (TRANS (@lem81429) (@lem81433)). Qed.
Lemma lem81435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81436 : term37 = (and True).
Proof. exact (MK_COMB (@lem81435) (@lem81434)). Qed.
Lemma lem81446 (n : nat) : (term24 n) = (term25 n).
Proof. exact (EQ_MP (@lem81377 n) (@lem81376 n)). Qed.
Lemma lem81447 : term38 = term39.
Proof. exact (@lem81446 0). Qed.
Lemma lem81449 (n : nat) : (term6 n) = n.
Proof. exact (EQ_MP (@lem81354 n) (@lem81353 n)). Qed.
Lemma lem81450 : term40 = (NUMERAL 0).
Proof. exact (@lem81449 (NUMERAL 0)). Qed.
Lemma lem81451 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem81452 : term39 = term41.
Proof. exact (MK_COMB (@lem81451) (@lem81450)). Qed.
Lemma lem81453 : term38 = term41.
Proof. exact (TRANS (@lem81447) (@lem81452)). Qed.
Lemma lem81454 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem81455 : term42 = term43.
Proof. exact (MK_COMB (@lem81454) (@lem81453)). Qed.
Lemma lem81456 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem81457 (n : nat) : (term44 n) = (term45 n).
Proof. exact (MK_COMB (@lem81455) (@lem81456 n)). Qed.
Lemma lem81459 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem81370 m n) (@lem81369 m n)). Qed.
Lemma lem81460 (n : nat) : (term45 n) = (term46 n).
Proof. exact (@lem81459 (NUMERAL 0) n). Qed.
Lemma lem81462 (n : nat) : (term22 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81374 n) (@lem81373 n)). Qed.
Lemma lem81463 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem81464 (n : nat) : (term47 n) = term48.
Proof. exact (MK_COMB (@lem81463) (@lem81462 n)). Qed.
Lemma lem81465 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem81466 (n : nat) : (term46 n) = (term6 n).
Proof. exact (MK_COMB (@lem81464 n) (@lem81465 n)). Qed.
Lemma lem81468 (n : nat) : (term6 n) = n.
Proof. exact (EQ_MP (@lem81354 n) (@lem81353 n)). Qed.
Lemma lem81469 (n : nat) : (term46 n) = n.
Proof. exact (TRANS (@lem81466 n) (@lem81468 n)). Qed.
Lemma lem81470 (n : nat) : (term45 n) = n.
Proof. exact (TRANS (@lem81460 n) (@lem81469 n)). Qed.
Lemma lem81471 (n : nat) : (term44 n) = n.
Proof. exact (TRANS (@lem81457 n) (@lem81470 n)). Qed.
Lemma lem81472 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81473 (n : nat) : (term49 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem81472) (@lem81471 n)). Qed.
Lemma lem81474 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem81475 (n : nat) : ((term44 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem81473 n) (@lem81474 n)). Qed.
Lemma lem81477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81478 (x : nat) : (x = x) = True.
Proof. exact (@lem81477 nat x). Qed.
Lemma lem81479 (n : nat) : (n = n) = True.
Proof. exact (@lem81478 n). Qed.
Lemma lem81480 (n : nat) : ((term44 n) = n) = True.
Proof. exact (TRANS (@lem81475 n) (@lem81479 n)). Qed.
Lemma lem81481 : term50 = term29.
Proof. exact (fun_ext (fun n : nat => @lem81480 n)). Qed.
Lemma lem81482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81483 : term51 = term30.
Proof. exact (MK_COMB (@lem81482) (@lem81481)). Qed.
Lemma lem81485 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81486 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81485 nat t). Qed.
Lemma lem81487 : term30 = True.
Proof. exact (@lem81486 True). Qed.
Lemma lem81488 : term51 = True.
Proof. exact (TRANS (@lem81483) (@lem81487)). Qed.
Lemma lem81489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81490 : term52 = (and True).
Proof. exact (MK_COMB (@lem81489) (@lem81488)). Qed.
Lemma lem81500 (n : nat) : (term24 n) = (term25 n).
Proof. exact (EQ_MP (@lem81377 n) (@lem81376 n)). Qed.
Lemma lem81501 : term38 = term39.
Proof. exact (@lem81500 0). Qed.
Lemma lem81503 (n : nat) : (term6 n) = n.
Proof. exact (EQ_MP (@lem81354 n) (@lem81353 n)). Qed.
Lemma lem81504 : term40 = (NUMERAL 0).
Proof. exact (@lem81503 (NUMERAL 0)). Qed.
Lemma lem81505 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem81506 : term39 = term41.
Proof. exact (MK_COMB (@lem81505) (@lem81504)). Qed.
Lemma lem81507 : term38 = term41.
Proof. exact (TRANS (@lem81501) (@lem81506)). Qed.
Lemma lem81508 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem81509 (m : nat) : (term53 m) = (term54 m).
Proof. exact (MK_COMB (@lem81508 m) (@lem81507)). Qed.
Lemma lem81511 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (EQ_MP (@lem81360 m n) (@lem81359 m n)). Qed.
Lemma lem81512 (m : nat) : (term54 m) = (term55 m).
Proof. exact (@lem81511 m (NUMERAL 0)). Qed.
Lemma lem81514 (m : nat) : (term13 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81363 m) (@lem81362 m)). Qed.
Lemma lem81515 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem81516 (m : nat) : (term55 m) = (term3 m).
Proof. exact (MK_COMB (@lem81515 m) (@lem81514 m)). Qed.
Lemma lem81518 (m : nat) : (term3 m) = m.
Proof. exact (EQ_MP (@lem81350 m) (@lem81349 m)). Qed.
Lemma lem81519 (m : nat) : (term55 m) = m.
Proof. exact (TRANS (@lem81516 m) (@lem81518 m)). Qed.
Lemma lem81520 (m : nat) : (term54 m) = m.
Proof. exact (TRANS (@lem81512 m) (@lem81519 m)). Qed.
Lemma lem81521 (m : nat) : (term53 m) = m.
Proof. exact (TRANS (@lem81509 m) (@lem81520 m)). Qed.
Lemma lem81522 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81523 (m : nat) : (term56 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem81522) (@lem81521 m)). Qed.
Lemma lem81524 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem81525 (m : nat) : ((term53 m) = m) = (m = m).
Proof. exact (MK_COMB (@lem81523 m) (@lem81524 m)). Qed.
Lemma lem81527 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81528 (x : nat) : (x = x) = True.
Proof. exact (@lem81527 nat x). Qed.
Lemma lem81529 (m : nat) : (m = m) = True.
Proof. exact (@lem81528 m). Qed.
Lemma lem81530 (m : nat) : ((term53 m) = m) = True.
Proof. exact (TRANS (@lem81525 m) (@lem81529 m)). Qed.
Lemma lem81531 : term57 = term29.
Proof. exact (fun_ext (fun m : nat => @lem81530 m)). Qed.
Lemma lem81532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81533 : term58 = term30.
Proof. exact (MK_COMB (@lem81532) (@lem81531)). Qed.
Lemma lem81535 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81536 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81535 nat t). Qed.
Lemma lem81537 : term30 = True.
Proof. exact (@lem81536 True). Qed.
Lemma lem81538 : term58 = True.
Proof. exact (TRANS (@lem81533) (@lem81537)). Qed.
Lemma lem81539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81540 : term59 = (and True).
Proof. exact (MK_COMB (@lem81539) (@lem81538)). Qed.
Lemma lem81554 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem81370 m n) (@lem81369 m n)). Qed.
Lemma lem81555 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81556 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem81555) (@lem81554 m n)). Qed.
Lemma lem81557 (m : nat) (n : nat) : (term19 m n) = (term19 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem81558 (m : nat) (n : nat) : ((term18 m n) = (term19 m n)) = ((term19 m n) = (term19 m n)).
Proof. exact (MK_COMB (@lem81556 m n) (@lem81557 m n)). Qed.
Lemma lem81560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81561 (x : nat) : (x = x) = True.
Proof. exact (@lem81560 nat x). Qed.
Lemma lem81562 (m : nat) (n : nat) : ((term19 m n) = (term19 m n)) = True.
Proof. exact (@lem81561 (term19 m n)). Qed.
Lemma lem81563 (m : nat) (n : nat) : ((term18 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem81558 m n) (@lem81562 m n)). Qed.
Lemma lem81564 (m : nat) : (term62 m) = term29.
Proof. exact (fun_ext (fun n : nat => @lem81563 m n)). Qed.
Lemma lem81565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81566 (m : nat) : (term16 m) = term30.
Proof. exact (MK_COMB (@lem81565) (@lem81564 m)). Qed.
Lemma lem81568 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81569 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81568 nat t). Qed.
Lemma lem81570 : term30 = True.
Proof. exact (@lem81569 True). Qed.
Lemma lem81571 (m : nat) : (term16 m) = True.
Proof. exact (TRANS (@lem81566 m) (@lem81570)). Qed.
Lemma lem81572 : term63 = term29.
Proof. exact (fun_ext (fun m : nat => @lem81571 m)). Qed.
Lemma lem81573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81574 : term14 = term30.
Proof. exact (MK_COMB (@lem81573) (@lem81572)). Qed.
Lemma lem81576 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81577 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81576 nat t). Qed.
Lemma lem81578 : term30 = True.
Proof. exact (@lem81577 True). Qed.
Lemma lem81579 : term14 = True.
Proof. exact (TRANS (@lem81574) (@lem81578)). Qed.
Lemma lem81580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81581 : term64 = (and True).
Proof. exact (MK_COMB (@lem81580) (@lem81579)). Qed.
Lemma lem81593 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (EQ_MP (@lem81360 m n) (@lem81359 m n)). Qed.
Lemma lem81594 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81595 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem81594) (@lem81593 m n)). Qed.
Lemma lem81596 (m : nat) (n : nat) : (term11 m n) = (term11 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem81597 (m : nat) (n : nat) : ((term10 m n) = (term11 m n)) = ((term11 m n) = (term11 m n)).
Proof. exact (MK_COMB (@lem81595 m n) (@lem81596 m n)). Qed.
Lemma lem81599 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81600 (x : nat) : (x = x) = True.
Proof. exact (@lem81599 nat x). Qed.
Lemma lem81601 (m : nat) (n : nat) : ((term11 m n) = (term11 m n)) = True.
Proof. exact (@lem81600 (term11 m n)). Qed.
Lemma lem81602 (m : nat) (n : nat) : ((term10 m n) = (term11 m n)) = True.
Proof. exact (TRANS (@lem81597 m n) (@lem81601 m n)). Qed.
Lemma lem81603 (m : nat) : (term67 m) = term29.
Proof. exact (fun_ext (fun n : nat => @lem81602 m n)). Qed.
Lemma lem81604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81605 (m : nat) : (term8 m) = term30.
Proof. exact (MK_COMB (@lem81604) (@lem81603 m)). Qed.
Lemma lem81607 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81608 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81607 nat t). Qed.
Lemma lem81609 : term30 = True.
Proof. exact (@lem81608 True). Qed.
Lemma lem81610 (m : nat) : (term8 m) = True.
Proof. exact (TRANS (@lem81605 m) (@lem81609)). Qed.
Lemma lem81611 : term68 = term29.
Proof. exact (fun_ext (fun m : nat => @lem81610 m)). Qed.
Lemma lem81612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81613 : term69 = term30.
Proof. exact (MK_COMB (@lem81612) (@lem81611)). Qed.
Lemma lem81615 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81616 (t : Prop) : (term32 t) = t.
Proof. exact (@lem81615 nat t). Qed.
Lemma lem81617 : term30 = True.
Proof. exact (@lem81616 True). Qed.
Lemma lem81618 : term69 = True.
Proof. exact (TRANS (@lem81613) (@lem81617)). Qed.
Lemma lem81619 : term70 = (True /\ True).
Proof. exact (MK_COMB (@lem81581) (@lem81618)). Qed.
Lemma lem81621 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem81622 : (True /\ True) = True.
Proof. exact (@lem81621 True). Qed.
Lemma lem81623 : term70 = True.
Proof. exact (TRANS (@lem81619) (@lem81622)). Qed.
Lemma lem81624 : term71 = (True /\ True).
Proof. exact (MK_COMB (@lem81540) (@lem81623)). Qed.
Lemma lem81626 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem81627 : (True /\ True) = True.
Proof. exact (@lem81626 True). Qed.
Lemma lem81628 : term71 = True.
Proof. exact (TRANS (@lem81624) (@lem81627)). Qed.
Lemma lem81629 : term72 = (True /\ True).
Proof. exact (MK_COMB (@lem81490) (@lem81628)). Qed.
Lemma lem81631 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem81632 : (True /\ True) = True.
Proof. exact (@lem81631 True). Qed.
Lemma lem81633 : term72 = True.
Proof. exact (TRANS (@lem81629) (@lem81632)). Qed.
Lemma lem81634 : term73 = (True /\ True).
Proof. exact (MK_COMB (@lem81436) (@lem81633)). Qed.
Lemma lem81636 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem81637 : (True /\ True) = True.
Proof. exact (@lem81636 True). Qed.
Lemma lem81638 : term73 = True.
Proof. exact (TRANS (@lem81634) (@lem81637)). Qed.
Lemma lem81639 : term74 = (True /\ True).
Proof. exact (MK_COMB (@lem81407) (@lem81638)). Qed.
Lemma lem81641 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem81642 : (True /\ True) = True.
Proof. exact (@lem81641 True). Qed.
Lemma lem81643 : term74 = True.
Proof. exact (TRANS (@lem81639) (@lem81642)). Qed.
Lemma lem81644 : True = term74.
Proof. exact (SYM (@lem81643)). Qed.
Lemma lem81645 : term74.
Proof. exact (EQ_MP (@lem81644) (@lem0)). Qed.

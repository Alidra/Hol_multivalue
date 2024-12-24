Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_ABS_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_POS_spec.
Require Import REAL_ABS_POW_spec.
Require Import REAL_POW_EQ_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1653386 (x : real) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term0 x n) = (term1 x n).
Proof. exact (h1). Qed.
Lemma lem1653387 (x : real) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term1 x n) = (term0 x n).
Proof. exact (SYM (@lem1653386 x n h1)). Qed.
Lemma lem1653388 (x : real) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term1 x n) = (term0 x n).
Proof. exact (h1). Qed.
Lemma lem1653389 (x : real) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term0 x n) = (term1 x n).
Proof. exact (SYM (@lem1653388 x n h1)). Qed.
Lemma lem1653390 (x : real) (n : nat) : ((term0 x n) = (term1 x n)) = ((term1 x n) = (term0 x n)).
Proof. exact (prop_ext (fun h1 : (term0 x n) = (term1 x n) => @lem1653387 x n h1) (fun h1 : (term1 x n) = (term0 x n) => @lem1653389 x n h1)). Qed.
Lemma lem1653391 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun n : nat => @lem1653390 x n)). Qed.
Lemma lem1653392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1653393 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1653392) (@lem1653391 x)). Qed.
Lemma lem1653394 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1653393 x)). Qed.
Lemma lem1653395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1653396 : term8 = term9.
Proof. exact (MK_COMB (@lem1653395) (@lem1653394)). Qed.
Lemma lem1653397 : term9.
Proof. exact (EQ_MP (@lem1653396) (@lem1582667)). Qed.
Lemma lem1653398 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1653399 (n : nat) (h1 : term10) : term11 n.
Proof. exact (@lem1653398 h1 n). Qed.
Lemma lem1653400 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem1653401 (n : nat) (h1 : term10) : term12 n.
Proof. exact (EQ_MP (@lem1653400 n) (@lem1653399 n h1)). Qed.
Lemma lem1653402 (n : nat) (x : real) (h1 : term10) : term13 n x.
Proof. exact (@lem1653401 n h1 x). Qed.
Lemma lem1653403 (n : nat) (x : real) : (term13 n x) = (term14 n x).
Proof. exact (eq_refl (term13 n x)). Qed.
Lemma lem1653404 (n : nat) (x : real) (h1 : term10) : term14 n x.
Proof. exact (EQ_MP (@lem1653403 n x) (@lem1653402 n x h1)). Qed.
Lemma lem1653405 (n : nat) (x : real) (y : real) (h1 : term10) : term15 n x y.
Proof. exact (@lem1653404 n x h1 y). Qed.
Lemma lem1653406 (n : nat) (x : real) (y : real) : (term15 n x y) = (term16 n x y).
Proof. exact (eq_refl (term15 n x y)). Qed.
Lemma lem1653407 (n : nat) (x : real) (y : real) (h1 : term10) : term16 n x y.
Proof. exact (EQ_MP (@lem1653406 n x y) (@lem1653405 n x y h1)). Qed.
Lemma lem1653408 (x : real) (y : real) (n : nat) (h1 : term17 x y n) : term17 x y n.
Proof. exact (h1). Qed.
Lemma lem1653409 (x : real) (y : real) (n : nat) (h1 : term10) (h2 : term17 x y n) : x = y.
Proof. exact (@lem1653407 n x y h1 (@lem1653408 x y n h2)). Qed.
Lemma lem1653410 (x : real) (y : real) (n : nat) (h1 : term17 x y n) : term18 x y.
Proof. exact (fun h0 : term10 => @lem1653409 x y n h0 h1). Qed.
Lemma lem1653411 (x : real) (y : real) (h1 : term19 x y) : term19 x y.
Proof. exact (h1). Qed.
Lemma lem1653412 (x : real) (y : real) (h1 : term19 x y) : term18 x y.
Proof. exact (ex_elim (@lem1653411 x y h1) (fun n : nat => fun h0 : term20 x y n => @lem1653410 x y n h0)). Qed.
Lemma lem1653413 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1653414 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : x = y.
Proof. exact (@lem1653412 x y h2 (@lem1653413 h1)). Qed.
Lemma lem1653415 (x : real) (y : real) (h1 : term10) : term21 x y.
Proof. exact (fun h0 : term19 x y => @lem1653414 x y h1 h0). Qed.
Lemma lem1653416 (x : real) (h1 : term10) : term22 x.
Proof. exact (fun y : real => @lem1653415 x y h1). Qed.
Lemma lem1653417 (h1 : term10) : term23.
Proof. exact (fun x : real => @lem1653416 x h1). Qed.
Lemma lem1653418 : term24.
Proof. exact (fun h0 : term10 => @lem1653417 h0). Qed.
Lemma lem1653419 : term23.
Proof. exact (@lem1653418 (@lem1653383)). Qed.
Lemma lem1653420 (x : real) : term25 x.
Proof. exact (@lem1653419 x). Qed.
Lemma lem1653421 (x : real) : (term25 x) = (term22 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1653422 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1653421 x) (@lem1653420 x)). Qed.
Lemma lem1653423 (x : real) (y : real) : term26 x y.
Proof. exact (@lem1653422 x y). Qed.
Lemma lem1653424 (x : real) (y : real) : (term26 x y) = (term21 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1653426 (x : real) (y : real) (n : nat) (h1 : term27 x y n) : term27 x y n.
Proof. exact (h1). Qed.
Lemma lem1653427 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (real_pow x n) = (real_pow y n).
Proof. exact (h1). Qed.
Lemma lem1653428 (n : nat) (h1 : term28 n) : term28 n.
Proof. exact (h1). Qed.
Lemma lem1653430 (x : real) (y : real) : term21 x y.
Proof. exact (EQ_MP (@lem1653424 x y) (@lem1653423 x y)). Qed.
Lemma lem1653431 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1653430 (real_abs x) (real_abs y)). Qed.
Lemma lem1653432 (x : real) : term30 x.
Proof. exact (@lem1653397 x). Qed.
Lemma lem1653433 (x : real) : (term30 x) = (term5 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1653434 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1653433 x) (@lem1653432 x)). Qed.
Lemma lem1653435 (x : real) (n : nat) : term31 x n.
Proof. exact (@lem1653434 x n). Qed.
Lemma lem1653436 (x : real) (n : nat) : (term31 x n) = ((term1 x n) = (term0 x n)).
Proof. exact (eq_refl (term31 x n)). Qed.
Lemma lem1653438 (x : real) : term32 x.
Proof. exact (@lem1532076 x). Qed.
Lemma lem1653439 (x : real) : (term32 x) = (term33 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1653440 (x : real) : term33 x.
Proof. exact (EQ_MP (@lem1653439 x) (@lem1653438 x)). Qed.
Lemma lem1653441 (x : real) : (term33 x) = ((term33 x) = True).
Proof. exact (@lem7 (term33 x)). Qed.
Lemma lem1653443 (n : nat) : term34 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1653459 (n : nat) (h1 : term28 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1653443 n (@lem1653428 n h1)). Qed.
Lemma lem1653460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1653461 (n : nat) (h1 : term28 n) : (term28 n) = (~ False).
Proof. exact (MK_COMB (@lem1653460) (@lem1653459 n h1)). Qed.
Lemma lem1653463 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1653464 (n : nat) (h1 : term28 n) : (term28 n) = True.
Proof. exact (TRANS (@lem1653461 n h1) (@lem1653463)). Qed.
Lemma lem1653465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653466 (n : nat) (h1 : term28 n) : (term35 n) = (and True).
Proof. exact (MK_COMB (@lem1653465) (@lem1653464 n h1)). Qed.
Lemma lem1653470 (x : real) : (term33 x) = True.
Proof. exact (EQ_MP (@lem1653441 x) (@lem1653440 x)). Qed.
Lemma lem1653471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653472 (x : real) : (term36 x) = (and True).
Proof. exact (MK_COMB (@lem1653471) (@lem1653470 x)). Qed.
Lemma lem1653476 (x : real) : (term33 x) = True.
Proof. exact (EQ_MP (@lem1653441 x) (@lem1653440 x)). Qed.
Lemma lem1653477 (y : real) : (term33 y) = True.
Proof. exact (@lem1653476 y). Qed.
Lemma lem1653478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653479 (y : real) : (term36 y) = (and True).
Proof. exact (MK_COMB (@lem1653478) (@lem1653477 y)). Qed.
Lemma lem1653483 (x : real) (n : nat) : (term1 x n) = (term0 x n).
Proof. exact (EQ_MP (@lem1653436 x n) (@lem1653435 x n)). Qed.
Lemma lem1653485 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (real_pow x n) = (real_pow y n).
Proof. exact (h1). Qed.
Lemma lem1653486 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1653487 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term0 x n) = (term0 y n).
Proof. exact (MK_COMB (@lem1653486) (@lem1653485 x y n h1)). Qed.
Lemma lem1653488 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term1 x n) = (term0 y n).
Proof. exact (TRANS (@lem1653483 x n) (@lem1653487 x y n h1)). Qed.
Lemma lem1653489 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1653490 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term37 x n) = (term38 y n).
Proof. exact (MK_COMB (@lem1653489) (@lem1653488 x y n h1)). Qed.
Lemma lem1653492 (x : real) (n : nat) : (term1 x n) = (term0 x n).
Proof. exact (EQ_MP (@lem1653436 x n) (@lem1653435 x n)). Qed.
Lemma lem1653493 (y : real) (n : nat) : (term1 y n) = (term0 y n).
Proof. exact (@lem1653492 y n). Qed.
Lemma lem1653494 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : ((term1 x n) = (term1 y n)) = ((term0 y n) = (term0 y n)).
Proof. exact (MK_COMB (@lem1653490 x y n h1) (@lem1653493 y n)). Qed.
Lemma lem1653496 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1653497 (x : real) : (x = x) = True.
Proof. exact (@lem1653496 real x). Qed.
Lemma lem1653498 (y : real) (n : nat) : ((term0 y n) = (term0 y n)) = True.
Proof. exact (@lem1653497 (term0 y n)). Qed.
Lemma lem1653499 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : ((term1 x n) = (term1 y n)) = True.
Proof. exact (TRANS (@lem1653494 x y n h1) (@lem1653498 y n)). Qed.
Lemma lem1653500 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term39 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem1653479 y) (@lem1653499 x y n h1)). Qed.
Lemma lem1653502 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1653503 : (True /\ True) = True.
Proof. exact (@lem1653502 True). Qed.
Lemma lem1653504 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term39 x y n) = True.
Proof. exact (TRANS (@lem1653500 x y n h1) (@lem1653503)). Qed.
Lemma lem1653505 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term40 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem1653472 x) (@lem1653504 x y n h1)). Qed.
Lemma lem1653507 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1653508 : (True /\ True) = True.
Proof. exact (@lem1653507 True). Qed.
Lemma lem1653509 (x : real) (y : real) (n : nat) (h1 : (real_pow x n) = (real_pow y n)) : (term40 x y n) = True.
Proof. exact (TRANS (@lem1653505 x y n h1) (@lem1653508)). Qed.
Lemma lem1653510 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (term41 x y n) = (True /\ True).
Proof. exact (MK_COMB (@lem1653466 n h1) (@lem1653509 x y n h2)). Qed.
Lemma lem1653512 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1653513 : (True /\ True) = True.
Proof. exact (@lem1653512 True). Qed.
Lemma lem1653514 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (term41 x y n) = True.
Proof. exact (TRANS (@lem1653510 x y n h1 h2) (@lem1653513)). Qed.
Lemma lem1653515 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : True = (term41 x y n).
Proof. exact (SYM (@lem1653514 x y n h1 h2)). Qed.
Lemma lem1653516 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : term41 x y n.
Proof. exact (EQ_MP (@lem1653515 x y n h1 h2) (@lem0)). Qed.
Lemma lem1653517 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : term42 x y.
Proof. exact (ex_intro (term43 x y) n (@lem1653516 x y n h1 h2)). Qed.
Lemma lem1653518 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (real_abs x) = (real_abs y).
Proof. exact (@lem1653431 x y (@lem1653517 x y n h1 h2)). Qed.
Lemma lem1653519 (x : real) (y : real) (n : nat) (h1 : term27 x y n) : (real_pow x n) = (real_pow y n).
Proof. exact (proj2 (@lem1653426 x y n h1)). Qed.
Lemma lem1653520 (x : real) (y : real) (n : nat) (h1 : term27 x y n) : term28 n.
Proof. exact (proj1 (@lem1653426 x y n h1)). Qed.
Lemma lem1653521 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : ((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y)).
Proof. exact (prop_ext (fun h3 : (real_pow x n) = (real_pow y n) => @lem1653518 x y n h1 h2) (fun h3 : (real_abs x) = (real_abs y) => @lem1653427 x y n h2)). Qed.
Lemma lem1653522 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1653521 x y n h1 h2) (@lem1653427 x y n h2)). Qed.
Lemma lem1653523 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (term28 n) = ((real_abs x) = (real_abs y)).
Proof. exact (prop_ext (fun h3 : term28 n => @lem1653522 x y n h1 h2) (fun h3 : (real_abs x) = (real_abs y) => @lem1653428 n h1)). Qed.
Lemma lem1653524 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : (real_pow x n) = (real_pow y n)) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1653523 x y n h1 h2) (@lem1653428 n h1)). Qed.
Lemma lem1653525 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : term27 x y n) : ((real_pow x n) = (real_pow y n)) = ((real_abs x) = (real_abs y)).
Proof. exact (prop_ext (fun h3 : (real_pow x n) = (real_pow y n) => @lem1653524 x y n h1 h3) (fun h3 : (real_abs x) = (real_abs y) => @lem1653519 x y n h2)). Qed.
Lemma lem1653526 (x : real) (y : real) (n : nat) (h1 : term28 n) (h2 : term27 x y n) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1653525 x y n h1 h2) (@lem1653519 x y n h2)). Qed.
Lemma lem1653527 (x : real) (y : real) (n : nat) (h1 : term27 x y n) : (term28 n) = ((real_abs x) = (real_abs y)).
Proof. exact (prop_ext (fun h2 : term28 n => @lem1653526 x y n h2 h1) (fun h2 : (real_abs x) = (real_abs y) => @lem1653520 x y n h1)). Qed.
Lemma lem1653528 (x : real) (y : real) (n : nat) (h1 : term27 x y n) : (real_abs x) = (real_abs y).
Proof. exact (EQ_MP (@lem1653527 x y n h1) (@lem1653520 x y n h1)). Qed.
Lemma lem1653529 (n : nat) (x : real) (y : real) : term44 n x y.
Proof. exact (fun h0 : term27 x y n => @lem1653528 x y n h0). Qed.
Lemma lem1653534 (n : nat) (x : real) : term45 n x.
Proof. exact (fun y : real => @lem1653529 n x y). Qed.
Lemma lem1653539 (n : nat) : term46 n.
Proof. exact (fun x : real => @lem1653534 n x). Qed.
Lemma lem1653544 : term47.
Proof. exact (fun n : nat => @lem1653539 n). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MONO_EQ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXP_MONO_LE_spec.
Require Import LE_ANTISYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem153350 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (term0 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem153351 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (m = n) = (term0 n m).
Proof. exact (SYM (@lem153350 m n h1)). Qed.
Lemma lem153352 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (m = n) = (term0 n m).
Proof. exact (h1). Qed.
Lemma lem153353 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (term0 n m) = (m = n).
Proof. exact (SYM (@lem153352 n m h1)). Qed.
Lemma lem153354 (n : nat) (m : nat) : ((term0 n m) = (m = n)) = ((m = n) = (term0 n m)).
Proof. exact (prop_ext (fun h1 : (term0 n m) = (m = n) => @lem153351 m n h1) (fun h1 : (m = n) = (term0 n m) => @lem153353 n m h1)). Qed.
Lemma lem153355 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem153354 n m)). Qed.
Lemma lem153356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153357 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem153356) (@lem153355 m)). Qed.
Lemma lem153358 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem153357 m)). Qed.
Lemma lem153359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153360 : term7 = term8.
Proof. exact (MK_COMB (@lem153359) (@lem153358)). Qed.
Lemma lem153361 : term8.
Proof. exact (EQ_MP (@lem153360) (@lem92426)). Qed.
Lemma lem153362 (x : nat) : term9 x.
Proof. exact (@lem153228 x). Qed.
Lemma lem153363 (x : nat) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem153364 (x : nat) : term10 x.
Proof. exact (EQ_MP (@lem153363 x) (@lem153362 x)). Qed.
Lemma lem153365 (x : nat) (y : nat) : term11 x y.
Proof. exact (@lem153364 x y). Qed.
Lemma lem153366 (x : nat) (y : nat) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem153367 (x : nat) (y : nat) : term12 x y.
Proof. exact (EQ_MP (@lem153366 x y) (@lem153365 x y)). Qed.
Lemma lem153368 (x : nat) (y : nat) (n : nat) : term13 x y n.
Proof. exact (@lem153367 x y n). Qed.
Lemma lem153369 (x : nat) (y : nat) (n : nat) : (term13 x y n) = ((term14 x y n) = (term15 x y n)).
Proof. exact (eq_refl (term13 x y n)). Qed.
Lemma lem153371 (m : nat) : term16 m.
Proof. exact (@lem153361 m). Qed.
Lemma lem153372 (m : nat) : (term16 m) = (term4 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem153373 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem153372 m) (@lem153371 m)). Qed.
Lemma lem153374 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem153373 m n). Qed.
Lemma lem153375 (n : nat) (m : nat) : (term17 m n) = ((m = n) = (term0 n m)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem153396 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem153375 n m) (@lem153374 m n)). Qed.
Lemma lem153397 (y : nat) (x : nat) (n : nat) : ((Nat.pow x n) = (Nat.pow y n)) = (term18 y x n).
Proof. exact (@lem153396 (Nat.pow y n) (Nat.pow x n)). Qed.
Lemma lem153401 (x : nat) (y : nat) (n : nat) : (term14 x y n) = (term15 x y n).
Proof. exact (EQ_MP (@lem153369 x y n) (@lem153368 x y n)). Qed.
Lemma lem153407 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem153375 n m) (@lem153374 m n)). Qed.
Lemma lem153408 (n : nat) : (n = (NUMERAL 0)) = (term19 n).
Proof. exact (@lem153407 (NUMERAL 0) n). Qed.
Lemma lem153411 (x : nat) (y : nat) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem153412 (x : nat) (y : nat) (n : nat) : (term15 x y n) = (term21 x y n).
Proof. exact (MK_COMB (@lem153411 x y) (@lem153408 n)). Qed.
Lemma lem153415 (x : nat) (y : nat) (n : nat) : (term14 x y n) = (term21 x y n).
Proof. exact (TRANS (@lem153401 x y n) (@lem153412 x y n)). Qed.
Lemma lem153416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153417 (x : nat) (y : nat) (n : nat) : (term22 x y n) = (term23 x y n).
Proof. exact (MK_COMB (@lem153416) (@lem153415 x y n)). Qed.
Lemma lem153419 (x : nat) (y : nat) (n : nat) : (term14 x y n) = (term15 x y n).
Proof. exact (EQ_MP (@lem153369 x y n) (@lem153368 x y n)). Qed.
Lemma lem153420 (y : nat) (x : nat) (n : nat) : (term14 y x n) = (term15 y x n).
Proof. exact (@lem153419 y x n). Qed.
Lemma lem153426 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem153375 n m) (@lem153374 m n)). Qed.
Lemma lem153427 (n : nat) : (n = (NUMERAL 0)) = (term19 n).
Proof. exact (@lem153426 (NUMERAL 0) n). Qed.
Lemma lem153430 (y : nat) (x : nat) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem153431 (y : nat) (x : nat) (n : nat) : (term15 y x n) = (term21 y x n).
Proof. exact (MK_COMB (@lem153430 y x) (@lem153427 n)). Qed.
Lemma lem153434 (y : nat) (x : nat) (n : nat) : (term14 y x n) = (term21 y x n).
Proof. exact (TRANS (@lem153420 y x n) (@lem153431 y x n)). Qed.
Lemma lem153435 (y : nat) (x : nat) (n : nat) : (term18 y x n) = (term24 y x n).
Proof. exact (MK_COMB (@lem153417 x y n) (@lem153434 y x n)). Qed.
Lemma lem153438 (y : nat) (x : nat) (n : nat) : ((Nat.pow x n) = (Nat.pow y n)) = (term24 y x n).
Proof. exact (TRANS (@lem153397 y x n) (@lem153435 y x n)). Qed.
Lemma lem153439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153440 (y : nat) (x : nat) (n : nat) : (term25 x y n) = (term26 y x n).
Proof. exact (MK_COMB (@lem153439) (@lem153438 y x n)). Qed.
Lemma lem153446 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem153375 n m) (@lem153374 m n)). Qed.
Lemma lem153447 (y : nat) (x : nat) : (x = y) = (term0 y x).
Proof. exact (@lem153446 y x). Qed.
Lemma lem153450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem153451 (y : nat) (x : nat) : (term27 x y) = (term28 y x).
Proof. exact (MK_COMB (@lem153450) (@lem153447 y x)). Qed.
Lemma lem153455 (n : nat) (m : nat) : (m = n) = (term0 n m).
Proof. exact (EQ_MP (@lem153375 n m) (@lem153374 m n)). Qed.
Lemma lem153456 (n : nat) : (n = (NUMERAL 0)) = (term19 n).
Proof. exact (@lem153455 (NUMERAL 0) n). Qed.
Lemma lem153459 (y : nat) (x : nat) (n : nat) : (term29 x y n) = (term30 y x n).
Proof. exact (MK_COMB (@lem153451 y x) (@lem153456 n)). Qed.
Lemma lem153462 (y : nat) (x : nat) (n : nat) : (((Nat.pow x n) = (Nat.pow y n)) = (term29 x y n)) = ((term24 y x n) = (term30 y x n)).
Proof. exact (MK_COMB (@lem153440 y x n) (@lem153459 y x n)). Qed.
Lemma lem153467 (y : nat) (x : nat) : (term31 x y) = (term32 y x).
Proof. exact (fun_ext (fun n : nat => @lem153462 y x n)). Qed.
Lemma lem153468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153469 (y : nat) (x : nat) : (term33 x y) = (term34 y x).
Proof. exact (MK_COMB (@lem153468) (@lem153467 y x)). Qed.
Lemma lem153474 (x : nat) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun y : nat => @lem153469 y x)). Qed.
Lemma lem153475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153476 (x : nat) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem153475) (@lem153474 x)). Qed.
Lemma lem153481 : term39 = term40.
Proof. exact (fun_ext (fun x : nat => @lem153476 x)). Qed.
Lemma lem153482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153483 : term41 = term42.
Proof. exact (MK_COMB (@lem153482) (@lem153481)). Qed.
Lemma lem153488 : term42 = term41.
Proof. exact (SYM (@lem153483)). Qed.
Lemma lem153509 (x : nat) (y : nat) : term43 x y.
Proof. exact (@lem9851 (Peano.le x y)). Qed.
Lemma lem153510 (x : nat) (y : nat) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem153511 (x : nat) (y : nat) : term44 x y.
Proof. exact (EQ_MP (@lem153510 x y) (@lem153509 x y)). Qed.
Lemma lem153512 (x : nat) (y : nat) (h1 : (Peano.le x y) = True) : (Peano.le x y) = True.
Proof. exact (h1). Qed.
Lemma lem153513 (x : nat) (y : nat) (h1 : (Peano.le x y) = False) : (Peano.le x y) = False.
Proof. exact (h1). Qed.
Lemma lem153534 (y : nat) (x : nat) (n : nat) : (term45 y x n) = (term45 y x n).
Proof. exact (eq_refl (term45 y x n)). Qed.
Lemma lem153535 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = True) : (term46 n x y) = (term47 y x n).
Proof. exact (MK_COMB (@lem153534 y x n) (@lem153512 x y h1)). Qed.
Lemma lem153536 (y : nat) (x : nat) (n : nat) : (term47 y x n) = ((term48 y x n) = (term49 y x n)).
Proof. exact (eq_refl (term47 y x n)). Qed.
Lemma lem153537 (n : nat) (x : nat) (y : nat) : (term50 n x y) = (term50 n x y).
Proof. exact (eq_refl (term50 n x y)). Qed.
Lemma lem153538 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = (term47 y x n)) = ((term46 n x y) = ((term48 y x n) = (term49 y x n))).
Proof. exact (MK_COMB (@lem153537 n x y) (@lem153536 y x n)). Qed.
Lemma lem153539 (y : nat) (x : nat) (n : nat) : (term46 n x y) = ((term24 y x n) = (term30 y x n)).
Proof. exact (eq_refl (term46 n x y)). Qed.
Lemma lem153540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153541 (y : nat) (x : nat) (n : nat) : (term50 n x y) = (term51 y x n).
Proof. exact (MK_COMB (@lem153540) (@lem153539 y x n)). Qed.
Lemma lem153542 (y : nat) (x : nat) (n : nat) : ((term48 y x n) = (term49 y x n)) = ((term48 y x n) = (term49 y x n)).
Proof. exact (eq_refl ((term48 y x n) = (term49 y x n))). Qed.
Lemma lem153543 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = ((term48 y x n) = (term49 y x n))) = (((term24 y x n) = (term30 y x n)) = ((term48 y x n) = (term49 y x n))).
Proof. exact (MK_COMB (@lem153541 y x n) (@lem153542 y x n)). Qed.
Lemma lem153544 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = (term47 y x n)) = (((term24 y x n) = (term30 y x n)) = ((term48 y x n) = (term49 y x n))).
Proof. exact (TRANS (@lem153538 y x n) (@lem153543 y x n)). Qed.
Lemma lem153545 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = True) : ((term24 y x n) = (term30 y x n)) = ((term48 y x n) = (term49 y x n)).
Proof. exact (EQ_MP (@lem153544 y x n) (@lem153535 n x y h1)). Qed.
Lemma lem153546 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = True) : ((term48 y x n) = (term49 y x n)) = ((term24 y x n) = (term30 y x n)).
Proof. exact (SYM (@lem153545 n x y h1)). Qed.
Lemma lem153547 (y : nat) (x : nat) (n : nat) : (term45 y x n) = (term45 y x n).
Proof. exact (eq_refl (term45 y x n)). Qed.
Lemma lem153548 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = False) : (term46 n x y) = (term52 y x n).
Proof. exact (MK_COMB (@lem153547 y x n) (@lem153513 x y h1)). Qed.
Lemma lem153549 (y : nat) (x : nat) (n : nat) : (term52 y x n) = ((term53 y x n) = (term54 y x n)).
Proof. exact (eq_refl (term52 y x n)). Qed.
Lemma lem153550 (n : nat) (x : nat) (y : nat) : (term50 n x y) = (term50 n x y).
Proof. exact (eq_refl (term50 n x y)). Qed.
Lemma lem153551 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = (term52 y x n)) = ((term46 n x y) = ((term53 y x n) = (term54 y x n))).
Proof. exact (MK_COMB (@lem153550 n x y) (@lem153549 y x n)). Qed.
Lemma lem153552 (y : nat) (x : nat) (n : nat) : (term46 n x y) = ((term24 y x n) = (term30 y x n)).
Proof. exact (eq_refl (term46 n x y)). Qed.
Lemma lem153553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153554 (y : nat) (x : nat) (n : nat) : (term50 n x y) = (term51 y x n).
Proof. exact (MK_COMB (@lem153553) (@lem153552 y x n)). Qed.
Lemma lem153555 (y : nat) (x : nat) (n : nat) : ((term53 y x n) = (term54 y x n)) = ((term53 y x n) = (term54 y x n)).
Proof. exact (eq_refl ((term53 y x n) = (term54 y x n))). Qed.
Lemma lem153556 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = ((term53 y x n) = (term54 y x n))) = (((term24 y x n) = (term30 y x n)) = ((term53 y x n) = (term54 y x n))).
Proof. exact (MK_COMB (@lem153554 y x n) (@lem153555 y x n)). Qed.
Lemma lem153557 (y : nat) (x : nat) (n : nat) : ((term46 n x y) = (term52 y x n)) = (((term24 y x n) = (term30 y x n)) = ((term53 y x n) = (term54 y x n))).
Proof. exact (TRANS (@lem153551 y x n) (@lem153556 y x n)). Qed.
Lemma lem153558 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = False) : ((term24 y x n) = (term30 y x n)) = ((term53 y x n) = (term54 y x n)).
Proof. exact (EQ_MP (@lem153557 y x n) (@lem153548 n x y h1)). Qed.
Lemma lem153559 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = False) : ((term53 y x n) = (term54 y x n)) = ((term24 y x n) = (term30 y x n)).
Proof. exact (SYM (@lem153558 n x y h1)). Qed.
Lemma lem153565 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem153566 (n : nat) : (term55 n) = True.
Proof. exact (@lem153565 (term19 n)). Qed.
Lemma lem153567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153568 (n : nat) : (term56 n) = (and True).
Proof. exact (MK_COMB (@lem153567) (@lem153566 n)). Qed.
Lemma lem153573 (y : nat) (x : nat) (n : nat) : (term21 y x n) = (term21 y x n).
Proof. exact (eq_refl (term21 y x n)). Qed.
Lemma lem153574 (y : nat) (x : nat) (n : nat) : (term48 y x n) = (term57 y x n).
Proof. exact (MK_COMB (@lem153568 n) (@lem153573 y x n)). Qed.
Lemma lem153576 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153577 (y : nat) (x : nat) (n : nat) : (term57 y x n) = (term21 y x n).
Proof. exact (@lem153576 (term21 y x n)). Qed.
Lemma lem153582 (y : nat) (x : nat) (n : nat) : (term48 y x n) = (term21 y x n).
Proof. exact (TRANS (@lem153574 y x n) (@lem153577 y x n)). Qed.
Lemma lem153583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153584 (y : nat) (x : nat) (n : nat) : (term58 y x n) = (term59 y x n).
Proof. exact (MK_COMB (@lem153583) (@lem153582 y x n)). Qed.
Lemma lem153588 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153589 (y : nat) (x : nat) : (term60 y x) = (Peano.le y x).
Proof. exact (@lem153588 (Peano.le y x)). Qed.
Lemma lem153590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem153591 (y : nat) (x : nat) : (term61 y x) = (term20 y x).
Proof. exact (MK_COMB (@lem153590) (@lem153589 y x)). Qed.
Lemma lem153594 (n : nat) : (term19 n) = (term19 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem153595 (y : nat) (x : nat) (n : nat) : (term49 y x n) = (term21 y x n).
Proof. exact (MK_COMB (@lem153591 y x) (@lem153594 n)). Qed.
Lemma lem153598 (y : nat) (x : nat) (n : nat) : ((term48 y x n) = (term49 y x n)) = ((term21 y x n) = (term21 y x n)).
Proof. exact (MK_COMB (@lem153584 y x n) (@lem153595 y x n)). Qed.
Lemma lem153600 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem153601 (x : Prop) : (x = x) = True.
Proof. exact (@lem153600 Prop x). Qed.
Lemma lem153602 (y : nat) (x : nat) (n : nat) : ((term21 y x n) = (term21 y x n)) = True.
Proof. exact (@lem153601 (term21 y x n)). Qed.
Lemma lem153603 (y : nat) (x : nat) (n : nat) : ((term48 y x n) = (term49 y x n)) = True.
Proof. exact (TRANS (@lem153598 y x n) (@lem153602 y x n)). Qed.
Lemma lem153604 (y : nat) (x : nat) (n : nat) : True = ((term48 y x n) = (term49 y x n)).
Proof. exact (SYM (@lem153603 y x n)). Qed.
Lemma lem153605 (y : nat) (x : nat) (n : nat) : (term48 y x n) = (term49 y x n).
Proof. exact (EQ_MP (@lem153604 y x n) (@lem0)). Qed.
Lemma lem153611 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem153612 (n : nat) : (term62 n) = (term19 n).
Proof. exact (@lem153611 (term19 n)). Qed.
Lemma lem153615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153616 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem153615) (@lem153612 n)). Qed.
Lemma lem153621 (y : nat) (x : nat) (n : nat) : (term21 y x n) = (term21 y x n).
Proof. exact (eq_refl (term21 y x n)). Qed.
Lemma lem153622 (y : nat) (x : nat) (n : nat) : (term53 y x n) = (term65 y x n).
Proof. exact (MK_COMB (@lem153616 n) (@lem153621 y x n)). Qed.
Lemma lem153625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153626 (y : nat) (x : nat) (n : nat) : (term66 y x n) = (term67 y x n).
Proof. exact (MK_COMB (@lem153625) (@lem153622 y x n)). Qed.
Lemma lem153630 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153631 (y : nat) (x : nat) : (term68 y x) = False.
Proof. exact (@lem153630 (Peano.le y x)). Qed.
Lemma lem153632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem153633 (y : nat) (x : nat) : (term69 y x) = (or False).
Proof. exact (MK_COMB (@lem153632) (@lem153631 y x)). Qed.
Lemma lem153636 (n : nat) : (term19 n) = (term19 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem153637 (y : nat) (x : nat) (n : nat) : (term54 y x n) = (term62 n).
Proof. exact (MK_COMB (@lem153633 y x) (@lem153636 n)). Qed.
Lemma lem153639 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem153640 (n : nat) : (term62 n) = (term19 n).
Proof. exact (@lem153639 (term19 n)). Qed.
Lemma lem153643 (y : nat) (x : nat) (n : nat) : (term54 y x n) = (term19 n).
Proof. exact (TRANS (@lem153637 y x n) (@lem153640 n)). Qed.
Lemma lem153644 (y : nat) (x : nat) (n : nat) : ((term53 y x n) = (term54 y x n)) = ((term65 y x n) = (term19 n)).
Proof. exact (MK_COMB (@lem153626 y x n) (@lem153643 y x n)). Qed.
Lemma lem153647 (y : nat) (x : nat) (n : nat) : ((term65 y x n) = (term19 n)) = ((term53 y x n) = (term54 y x n)).
Proof. exact (SYM (@lem153644 y x n)). Qed.
Lemma lem153648 (n : nat) : term70 n.
Proof. exact (@lem9851 (term71 n)). Qed.
Lemma lem153649 (n : nat) : (term70 n) = (term72 n).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem153650 (n : nat) : term72 n.
Proof. exact (EQ_MP (@lem153649 n) (@lem153648 n)). Qed.
Lemma lem153651 (n : nat) (h1 : (term71 n) = True) : (term71 n) = True.
Proof. exact (h1). Qed.
Lemma lem153652 (n : nat) (h1 : (term71 n) = False) : (term71 n) = False.
Proof. exact (h1). Qed.
Lemma lem153667 (y : nat) (x : nat) (n : nat) : (term73 y x n) = (term73 y x n).
Proof. exact (eq_refl (term73 y x n)). Qed.
Lemma lem153668 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = True) : (term74 y x n) = (term75 y x n).
Proof. exact (MK_COMB (@lem153667 y x n) (@lem153651 n h1)). Qed.
Lemma lem153669 (y : nat) (x : nat) (n : nat) : (term75 y x n) = ((term76 y x n) = (term77 n)).
Proof. exact (eq_refl (term75 y x n)). Qed.
Lemma lem153670 (y : nat) (x : nat) (n : nat) : (term78 y x n) = (term78 y x n).
Proof. exact (eq_refl (term78 y x n)). Qed.
Lemma lem153671 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = (term75 y x n)) = ((term74 y x n) = ((term76 y x n) = (term77 n))).
Proof. exact (MK_COMB (@lem153670 y x n) (@lem153669 y x n)). Qed.
Lemma lem153672 (y : nat) (x : nat) (n : nat) : (term74 y x n) = ((term65 y x n) = (term19 n)).
Proof. exact (eq_refl (term74 y x n)). Qed.
Lemma lem153673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153674 (y : nat) (x : nat) (n : nat) : (term78 y x n) = (term79 y x n).
Proof. exact (MK_COMB (@lem153673) (@lem153672 y x n)). Qed.
Lemma lem153675 (y : nat) (x : nat) (n : nat) : ((term76 y x n) = (term77 n)) = ((term76 y x n) = (term77 n)).
Proof. exact (eq_refl ((term76 y x n) = (term77 n))). Qed.
Lemma lem153676 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = ((term76 y x n) = (term77 n))) = (((term65 y x n) = (term19 n)) = ((term76 y x n) = (term77 n))).
Proof. exact (MK_COMB (@lem153674 y x n) (@lem153675 y x n)). Qed.
Lemma lem153677 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = (term75 y x n)) = (((term65 y x n) = (term19 n)) = ((term76 y x n) = (term77 n))).
Proof. exact (TRANS (@lem153671 y x n) (@lem153676 y x n)). Qed.
Lemma lem153678 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = True) : ((term65 y x n) = (term19 n)) = ((term76 y x n) = (term77 n)).
Proof. exact (EQ_MP (@lem153677 y x n) (@lem153668 y x n h1)). Qed.
Lemma lem153679 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = True) : ((term76 y x n) = (term77 n)) = ((term65 y x n) = (term19 n)).
Proof. exact (SYM (@lem153678 y x n h1)). Qed.
Lemma lem153680 (y : nat) (x : nat) (n : nat) : (term73 y x n) = (term73 y x n).
Proof. exact (eq_refl (term73 y x n)). Qed.
Lemma lem153681 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = False) : (term74 y x n) = (term80 y x n).
Proof. exact (MK_COMB (@lem153680 y x n) (@lem153652 n h1)). Qed.
Lemma lem153682 (y : nat) (x : nat) (n : nat) : (term80 y x n) = ((term81 y x n) = (term82 n)).
Proof. exact (eq_refl (term80 y x n)). Qed.
Lemma lem153683 (y : nat) (x : nat) (n : nat) : (term78 y x n) = (term78 y x n).
Proof. exact (eq_refl (term78 y x n)). Qed.
Lemma lem153684 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = (term80 y x n)) = ((term74 y x n) = ((term81 y x n) = (term82 n))).
Proof. exact (MK_COMB (@lem153683 y x n) (@lem153682 y x n)). Qed.
Lemma lem153685 (y : nat) (x : nat) (n : nat) : (term74 y x n) = ((term65 y x n) = (term19 n)).
Proof. exact (eq_refl (term74 y x n)). Qed.
Lemma lem153686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153687 (y : nat) (x : nat) (n : nat) : (term78 y x n) = (term79 y x n).
Proof. exact (MK_COMB (@lem153686) (@lem153685 y x n)). Qed.
Lemma lem153688 (y : nat) (x : nat) (n : nat) : ((term81 y x n) = (term82 n)) = ((term81 y x n) = (term82 n)).
Proof. exact (eq_refl ((term81 y x n) = (term82 n))). Qed.
Lemma lem153689 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = ((term81 y x n) = (term82 n))) = (((term65 y x n) = (term19 n)) = ((term81 y x n) = (term82 n))).
Proof. exact (MK_COMB (@lem153687 y x n) (@lem153688 y x n)). Qed.
Lemma lem153690 (y : nat) (x : nat) (n : nat) : ((term74 y x n) = (term80 y x n)) = (((term65 y x n) = (term19 n)) = ((term81 y x n) = (term82 n))).
Proof. exact (TRANS (@lem153684 y x n) (@lem153689 y x n)). Qed.
Lemma lem153691 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = False) : ((term65 y x n) = (term19 n)) = ((term81 y x n) = (term82 n)).
Proof. exact (EQ_MP (@lem153690 y x n) (@lem153681 y x n h1)). Qed.
Lemma lem153692 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = False) : ((term81 y x n) = (term82 n)) = ((term65 y x n) = (term19 n)).
Proof. exact (SYM (@lem153691 y x n h1)). Qed.
Lemma lem153698 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153699 (n : nat) : (term77 n) = (term83 n).
Proof. exact (@lem153698 (term83 n)). Qed.
Lemma lem153700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153701 (n : nat) : (term84 n) = (term85 n).
Proof. exact (MK_COMB (@lem153700) (@lem153699 n)). Qed.
Lemma lem153705 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153706 (n : nat) : (term77 n) = (term83 n).
Proof. exact (@lem153705 (term83 n)). Qed.
Lemma lem153707 (y : nat) (x : nat) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem153708 (y : nat) (x : nat) (n : nat) : (term86 y x n) = (term87 y x n).
Proof. exact (MK_COMB (@lem153707 y x) (@lem153706 n)). Qed.
Lemma lem153711 (y : nat) (x : nat) (n : nat) : (term76 y x n) = (term88 y x n).
Proof. exact (MK_COMB (@lem153701 n) (@lem153708 y x n)). Qed.
Lemma lem153714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153715 (y : nat) (x : nat) (n : nat) : (term89 y x n) = (term90 y x n).
Proof. exact (MK_COMB (@lem153714) (@lem153711 y x n)). Qed.
Lemma lem153717 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153718 (n : nat) : (term77 n) = (term83 n).
Proof. exact (@lem153717 (term83 n)). Qed.
Lemma lem153719 (y : nat) (x : nat) (n : nat) : ((term76 y x n) = (term77 n)) = ((term88 y x n) = (term83 n)).
Proof. exact (MK_COMB (@lem153715 y x n) (@lem153718 n)). Qed.
Lemma lem153722 (y : nat) (x : nat) (n : nat) : ((term88 y x n) = (term83 n)) = ((term76 y x n) = (term77 n)).
Proof. exact (SYM (@lem153719 y x n)). Qed.
Lemma lem153723 (n : nat) : term91 n.
Proof. exact (@lem9851 (term83 n)). Qed.
Lemma lem153724 (n : nat) : (term91 n) = (term92 n).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem153725 (n : nat) : term92 n.
Proof. exact (EQ_MP (@lem153724 n) (@lem153723 n)). Qed.
Lemma lem153726 (n : nat) (h1 : (term83 n) = True) : (term83 n) = True.
Proof. exact (h1). Qed.
Lemma lem153727 (n : nat) (h1 : (term83 n) = False) : (term83 n) = False.
Proof. exact (h1). Qed.
Lemma lem153736 (y : nat) (x : nat) : (term93 y x) = (term93 y x).
Proof. exact (eq_refl (term93 y x)). Qed.
Lemma lem153737 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = True) : (term94 y x n) = (term95 y x).
Proof. exact (MK_COMB (@lem153736 y x) (@lem153726 n h1)). Qed.
Lemma lem153738 (y : nat) (x : nat) : (term95 y x) = ((term96 y x) = True).
Proof. exact (eq_refl (term95 y x)). Qed.
Lemma lem153739 (y : nat) (x : nat) (n : nat) : (term97 y x n) = (term97 y x n).
Proof. exact (eq_refl (term97 y x n)). Qed.
Lemma lem153740 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = (term95 y x)) = ((term94 y x n) = ((term96 y x) = True)).
Proof. exact (MK_COMB (@lem153739 y x n) (@lem153738 y x)). Qed.
Lemma lem153741 (y : nat) (x : nat) (n : nat) : (term94 y x n) = ((term88 y x n) = (term83 n)).
Proof. exact (eq_refl (term94 y x n)). Qed.
Lemma lem153742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153743 (y : nat) (x : nat) (n : nat) : (term97 y x n) = (term98 y x n).
Proof. exact (MK_COMB (@lem153742) (@lem153741 y x n)). Qed.
Lemma lem153744 (y : nat) (x : nat) : ((term96 y x) = True) = ((term96 y x) = True).
Proof. exact (eq_refl ((term96 y x) = True)). Qed.
Lemma lem153745 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = ((term96 y x) = True)) = (((term88 y x n) = (term83 n)) = ((term96 y x) = True)).
Proof. exact (MK_COMB (@lem153743 y x n) (@lem153744 y x)). Qed.
Lemma lem153746 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = (term95 y x)) = (((term88 y x n) = (term83 n)) = ((term96 y x) = True)).
Proof. exact (TRANS (@lem153740 n y x) (@lem153745 n y x)). Qed.
Lemma lem153747 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = True) : ((term88 y x n) = (term83 n)) = ((term96 y x) = True).
Proof. exact (EQ_MP (@lem153746 n y x) (@lem153737 y x n h1)). Qed.
Lemma lem153748 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = True) : ((term96 y x) = True) = ((term88 y x n) = (term83 n)).
Proof. exact (SYM (@lem153747 y x n h1)). Qed.
Lemma lem153749 (y : nat) (x : nat) : (term93 y x) = (term93 y x).
Proof. exact (eq_refl (term93 y x)). Qed.
Lemma lem153750 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = False) : (term94 y x n) = (term99 y x).
Proof. exact (MK_COMB (@lem153749 y x) (@lem153727 n h1)). Qed.
Lemma lem153751 (y : nat) (x : nat) : (term99 y x) = ((term100 y x) = False).
Proof. exact (eq_refl (term99 y x)). Qed.
Lemma lem153752 (y : nat) (x : nat) (n : nat) : (term97 y x n) = (term97 y x n).
Proof. exact (eq_refl (term97 y x n)). Qed.
Lemma lem153753 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = (term99 y x)) = ((term94 y x n) = ((term100 y x) = False)).
Proof. exact (MK_COMB (@lem153752 y x n) (@lem153751 y x)). Qed.
Lemma lem153754 (y : nat) (x : nat) (n : nat) : (term94 y x n) = ((term88 y x n) = (term83 n)).
Proof. exact (eq_refl (term94 y x n)). Qed.
Lemma lem153755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153756 (y : nat) (x : nat) (n : nat) : (term97 y x n) = (term98 y x n).
Proof. exact (MK_COMB (@lem153755) (@lem153754 y x n)). Qed.
Lemma lem153757 (y : nat) (x : nat) : ((term100 y x) = False) = ((term100 y x) = False).
Proof. exact (eq_refl ((term100 y x) = False)). Qed.
Lemma lem153758 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = ((term100 y x) = False)) = (((term88 y x n) = (term83 n)) = ((term100 y x) = False)).
Proof. exact (MK_COMB (@lem153756 y x n) (@lem153757 y x)). Qed.
Lemma lem153759 (n : nat) (y : nat) (x : nat) : ((term94 y x n) = (term99 y x)) = (((term88 y x n) = (term83 n)) = ((term100 y x) = False)).
Proof. exact (TRANS (@lem153753 n y x) (@lem153758 n y x)). Qed.
Lemma lem153760 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = False) : ((term88 y x n) = (term83 n)) = ((term100 y x) = False).
Proof. exact (EQ_MP (@lem153759 n y x) (@lem153750 y x n h1)). Qed.
Lemma lem153761 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = False) : ((term100 y x) = False) = ((term88 y x n) = (term83 n)).
Proof. exact (SYM (@lem153760 y x n h1)). Qed.
Lemma lem153763 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem153764 (y : nat) (x : nat) : ((term96 y x) = True) = (term96 y x).
Proof. exact (@lem153763 (term96 y x)). Qed.
Lemma lem153766 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem153767 (y : nat) (x : nat) : (term96 y x) = (term101 y x).
Proof. exact (@lem153766 (term101 y x)). Qed.
Lemma lem153769 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem153770 (y : nat) (x : nat) : (term101 y x) = True.
Proof. exact (@lem153769 (Peano.le y x)). Qed.
Lemma lem153771 (y : nat) (x : nat) : (term96 y x) = True.
Proof. exact (TRANS (@lem153767 y x) (@lem153770 y x)). Qed.
Lemma lem153772 (y : nat) (x : nat) : ((term96 y x) = True) = True.
Proof. exact (TRANS (@lem153764 y x) (@lem153771 y x)). Qed.
Lemma lem153773 (y : nat) (x : nat) : True = ((term96 y x) = True).
Proof. exact (SYM (@lem153772 y x)). Qed.
Lemma lem153774 (y : nat) (x : nat) : (term96 y x) = True.
Proof. exact (EQ_MP (@lem153773 y x) (@lem0)). Qed.
Lemma lem153776 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem153777 (y : nat) (x : nat) : ((term100 y x) = False) = (term102 y x).
Proof. exact (@lem153776 (term100 y x)). Qed.
Lemma lem153779 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153780 (y : nat) (x : nat) : (term100 y x) = False.
Proof. exact (@lem153779 (term103 y x)). Qed.
Lemma lem153781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem153782 (y : nat) (x : nat) : (term102 y x) = (~ False).
Proof. exact (MK_COMB (@lem153781) (@lem153780 y x)). Qed.
Lemma lem153784 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem153785 (y : nat) (x : nat) : (term102 y x) = True.
Proof. exact (TRANS (@lem153782 y x) (@lem153784)). Qed.
Lemma lem153786 (y : nat) (x : nat) : ((term100 y x) = False) = True.
Proof. exact (TRANS (@lem153777 y x) (@lem153785 y x)). Qed.
Lemma lem153787 (y : nat) (x : nat) : True = ((term100 y x) = False).
Proof. exact (SYM (@lem153786 y x)). Qed.
Lemma lem153788 (y : nat) (x : nat) : (term100 y x) = False.
Proof. exact (EQ_MP (@lem153787 y x) (@lem0)). Qed.
Lemma lem153789 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = False) : (term88 y x n) = (term83 n).
Proof. exact (EQ_MP (@lem153761 y x n h1) (@lem153788 y x)). Qed.
Lemma lem153790 (y : nat) (x : nat) (n : nat) (h1 : (term83 n) = True) : (term88 y x n) = (term83 n).
Proof. exact (EQ_MP (@lem153748 y x n h1) (@lem153774 y x)). Qed.
Lemma lem153792 (y : nat) (x : nat) (n : nat) : (term88 y x n) = (term83 n).
Proof. exact (or_elim (@lem153725 n) (fun h0 : (term83 n) = True => @lem153790 y x n h0) (fun h0 : (term83 n) = False => @lem153789 y x n h0)). Qed.
Lemma lem153793 (y : nat) (x : nat) (n : nat) : (term76 y x n) = (term77 n).
Proof. exact (EQ_MP (@lem153722 y x n) (@lem153792 y x n)). Qed.
Lemma lem153799 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153800 (n : nat) : (term82 n) = False.
Proof. exact (@lem153799 (term83 n)). Qed.
Lemma lem153801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153802 (n : nat) : (term104 n) = (and False).
Proof. exact (MK_COMB (@lem153801) (@lem153800 n)). Qed.
Lemma lem153806 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153807 (n : nat) : (term82 n) = False.
Proof. exact (@lem153806 (term83 n)). Qed.
Lemma lem153808 (y : nat) (x : nat) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem153809 (n : nat) (y : nat) (x : nat) : (term105 y x n) = (term103 y x).
Proof. exact (MK_COMB (@lem153808 y x) (@lem153807 n)). Qed.
Lemma lem153811 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem153812 (y : nat) (x : nat) : (term103 y x) = (Peano.le y x).
Proof. exact (@lem153811 (Peano.le y x)). Qed.
Lemma lem153813 (n : nat) (y : nat) (x : nat) : (term105 y x n) = (Peano.le y x).
Proof. exact (TRANS (@lem153809 n y x) (@lem153812 y x)). Qed.
Lemma lem153814 (n : nat) (y : nat) (x : nat) : (term81 y x n) = (term68 y x).
Proof. exact (MK_COMB (@lem153802 n) (@lem153813 n y x)). Qed.
Lemma lem153816 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153817 (y : nat) (x : nat) : (term68 y x) = False.
Proof. exact (@lem153816 (Peano.le y x)). Qed.
Lemma lem153818 (y : nat) (x : nat) (n : nat) : (term81 y x n) = False.
Proof. exact (TRANS (@lem153814 n y x) (@lem153817 y x)). Qed.
Lemma lem153819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153820 (y : nat) (x : nat) (n : nat) : (term106 y x n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem153819) (@lem153818 y x n)). Qed.
Lemma lem153822 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem153823 (n : nat) : (term82 n) = False.
Proof. exact (@lem153822 (term83 n)). Qed.
Lemma lem153824 (y : nat) (x : nat) (n : nat) : ((term81 y x n) = (term82 n)) = (False = False).
Proof. exact (MK_COMB (@lem153820 y x n) (@lem153823 n)). Qed.
Lemma lem153826 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem153827 : (False = False) = (~ False).
Proof. exact (@lem153826 False). Qed.
Lemma lem153829 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem153830 : (False = False) = True.
Proof. exact (TRANS (@lem153827) (@lem153829)). Qed.
Lemma lem153831 (y : nat) (x : nat) (n : nat) : ((term81 y x n) = (term82 n)) = True.
Proof. exact (TRANS (@lem153824 y x n) (@lem153830)). Qed.
Lemma lem153832 (y : nat) (x : nat) (n : nat) : True = ((term81 y x n) = (term82 n)).
Proof. exact (SYM (@lem153831 y x n)). Qed.
Lemma lem153833 (y : nat) (x : nat) (n : nat) : (term81 y x n) = (term82 n).
Proof. exact (EQ_MP (@lem153832 y x n) (@lem0)). Qed.
Lemma lem153834 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = False) : (term65 y x n) = (term19 n).
Proof. exact (EQ_MP (@lem153692 y x n h1) (@lem153833 y x n)). Qed.
Lemma lem153835 (y : nat) (x : nat) (n : nat) (h1 : (term71 n) = True) : (term65 y x n) = (term19 n).
Proof. exact (EQ_MP (@lem153679 y x n h1) (@lem153793 y x n)). Qed.
Lemma lem153837 (y : nat) (x : nat) (n : nat) : (term65 y x n) = (term19 n).
Proof. exact (or_elim (@lem153650 n) (fun h0 : (term71 n) = True => @lem153835 y x n h0) (fun h0 : (term71 n) = False => @lem153834 y x n h0)). Qed.
Lemma lem153838 (y : nat) (x : nat) (n : nat) : (term53 y x n) = (term54 y x n).
Proof. exact (EQ_MP (@lem153647 y x n) (@lem153837 y x n)). Qed.
Lemma lem153839 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = False) : (term24 y x n) = (term30 y x n).
Proof. exact (EQ_MP (@lem153559 n x y h1) (@lem153838 y x n)). Qed.
Lemma lem153840 (n : nat) (x : nat) (y : nat) (h1 : (Peano.le x y) = True) : (term24 y x n) = (term30 y x n).
Proof. exact (EQ_MP (@lem153546 n x y h1) (@lem153605 y x n)). Qed.
Lemma lem153843 (y : nat) (x : nat) (n : nat) : (term24 y x n) = (term30 y x n).
Proof. exact (or_elim (@lem153511 x y) (fun h0 : (Peano.le x y) = True => @lem153840 n x y h0) (fun h0 : (Peano.le x y) = False => @lem153839 n x y h0)). Qed.
Lemma lem153848 (y : nat) (x : nat) : term34 y x.
Proof. exact (fun n : nat => @lem153843 y x n). Qed.
Lemma lem153853 (x : nat) : term38 x.
Proof. exact (fun y : nat => @lem153848 y x). Qed.
Lemma lem153858 : term42.
Proof. exact (fun x : nat => @lem153853 x). Qed.
Lemma lem153859 : term41.
Proof. exact (EQ_MP (@lem153488) (@lem153858)). Qed.

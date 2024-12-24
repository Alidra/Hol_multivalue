Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032044_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_CLAUSES_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1031360_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm86199_spec.
Lemma lem1031362 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1031366 (n : nat) (m : nat) (p : nat) : term1 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1031370 (m : nat) : term2 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1031371 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1031372 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1031371 m) (@lem1031370 m)). Qed.
Lemma lem1031373 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1031372 m n). Qed.
Lemma lem1031374 (n : nat) (m : nat) : (term4 m n) = (term5 n m).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1031375 (n : nat) (m : nat) : term5 n m.
Proof. exact (EQ_MP (@lem1031374 n m) (@lem1031373 m n)). Qed.
Lemma lem1031376 (n : nat) (m : nat) (p : nat) : term6 n m p.
Proof. exact (@lem1031375 n m p). Qed.
Lemma lem1031377 (n : nat) (m : nat) (p : nat) : (term6 n m p) = ((term7 m n p) = (term8 n m p)).
Proof. exact (eq_refl (term6 n m p)). Qed.
Lemma lem1031399 : term9.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1031400 (n : nat) : term10 n.
Proof. exact (@lem1031399 n). Qed.
Lemma lem1031401 (n : nat) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1031403 : term12.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1031404 : term13.
Proof. exact (proj2 (@lem1031403)). Qed.
Lemma lem1031425 : term14.
Proof. exact (proj1 (@lem1031404)). Qed.
Lemma lem1031426 (n : nat) : term15 n.
Proof. exact (@lem1031425 n). Qed.
Lemma lem1031427 (n : nat) : (term15 n) = ((term16 n) = n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem1031433 : term17.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1031434 (n : nat) : term18 n.
Proof. exact (@lem1031433 n). Qed.
Lemma lem1031435 (n : nat) : (term18 n) = ((term19 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem1031437 : term20.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1031438 (m : nat) : term21 m.
Proof. exact (@lem1031437 m). Qed.
Lemma lem1031439 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1031440 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1031439 m) (@lem1031438 m)). Qed.
Lemma lem1031441 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1031440 m n). Qed.
Lemma lem1031442 (m : nat) (n : nat) : (term23 m n) = ((term24 m n) = (term25 m n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1031444 : term26.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem1031445 (m : nat) : term27 m.
Proof. exact (@lem1031444 m). Qed.
Lemma lem1031446 (m : nat) : (term27 m) = ((term28 m) = term29).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1031485 (n : nat) : (term11 n) = n.
Proof. exact (EQ_MP (@lem1031401 n) (@lem1031400 n)). Qed.
Lemma lem1031486 (x : nat) : (term11 x) = x.
Proof. exact (@lem1031485 x). Qed.
Lemma lem1031487 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031488 (x : nat) : (term30 x) = (@eq nat x).
Proof. exact (MK_COMB (@lem1031487) (@lem1031486 x)). Qed.
Lemma lem1031489 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1031490 (x : nat) : ((term11 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1031488 x) (@lem1031489 x)). Qed.
Lemma lem1031492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031493 (x : nat) : (x = x) = True.
Proof. exact (@lem1031492 nat x). Qed.
Lemma lem1031494 (x : nat) : ((term11 x) = x) = True.
Proof. exact (TRANS (@lem1031490 x) (@lem1031493 x)). Qed.
Lemma lem1031495 : term31 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031494 x)). Qed.
Lemma lem1031496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031497 : term9 = term33.
Proof. exact (MK_COMB (@lem1031496) (@lem1031495)). Qed.
Lemma lem1031499 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031500 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031499 nat t). Qed.
Lemma lem1031501 : term33 = True.
Proof. exact (@lem1031500 True). Qed.
Lemma lem1031502 : term9 = True.
Proof. exact (TRANS (@lem1031497) (@lem1031501)). Qed.
Lemma lem1031503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031504 : term36 = (and True).
Proof. exact (MK_COMB (@lem1031503) (@lem1031502)). Qed.
Lemma lem1031542 (n : nat) : (term16 n) = n.
Proof. exact (EQ_MP (@lem1031427 n) (@lem1031426 n)). Qed.
Lemma lem1031543 (x : nat) : (term16 x) = x.
Proof. exact (@lem1031542 x). Qed.
Lemma lem1031544 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031545 (x : nat) : (term37 x) = (@eq nat x).
Proof. exact (MK_COMB (@lem1031544) (@lem1031543 x)). Qed.
Lemma lem1031546 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1031547 (x : nat) : ((term16 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1031545 x) (@lem1031546 x)). Qed.
Lemma lem1031549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031550 (x : nat) : (x = x) = True.
Proof. exact (@lem1031549 nat x). Qed.
Lemma lem1031551 (x : nat) : ((term16 x) = x) = True.
Proof. exact (TRANS (@lem1031547 x) (@lem1031550 x)). Qed.
Lemma lem1031552 : term38 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031551 x)). Qed.
Lemma lem1031553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031554 : term14 = term33.
Proof. exact (MK_COMB (@lem1031553) (@lem1031552)). Qed.
Lemma lem1031556 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031557 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031556 nat t). Qed.
Lemma lem1031558 : term33 = True.
Proof. exact (@lem1031557 True). Qed.
Lemma lem1031559 : term14 = True.
Proof. exact (TRANS (@lem1031554) (@lem1031558)). Qed.
Lemma lem1031560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031561 : term39 = (and True).
Proof. exact (MK_COMB (@lem1031560) (@lem1031559)). Qed.
Lemma lem1031571 (n : nat) : (term19 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1031435 n) (@lem1031434 n)). Qed.
Lemma lem1031572 (x : nat) : (term19 x) = (NUMERAL 0).
Proof. exact (@lem1031571 x). Qed.
Lemma lem1031573 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031574 (x : nat) : (term40 x) = term41.
Proof. exact (MK_COMB (@lem1031573) (@lem1031572 x)). Qed.
Lemma lem1031575 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1031576 (x : nat) : ((term19 x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1031574 x) (@lem1031575)). Qed.
Lemma lem1031578 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031579 (x : nat) : (x = x) = True.
Proof. exact (@lem1031578 nat x). Qed.
Lemma lem1031580 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1031579 (NUMERAL 0)). Qed.
Lemma lem1031581 (x : nat) : ((term19 x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1031576 x) (@lem1031580)). Qed.
Lemma lem1031582 : term42 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031581 x)). Qed.
Lemma lem1031583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031584 : term17 = term33.
Proof. exact (MK_COMB (@lem1031583) (@lem1031582)). Qed.
Lemma lem1031586 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031587 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031586 nat t). Qed.
Lemma lem1031588 : term33 = True.
Proof. exact (@lem1031587 True). Qed.
Lemma lem1031589 : term17 = True.
Proof. exact (TRANS (@lem1031584) (@lem1031588)). Qed.
Lemma lem1031590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031591 : term43 = (and True).
Proof. exact (MK_COMB (@lem1031590) (@lem1031589)). Qed.
Lemma lem1031609 (n : nat) (m : nat) (p : nat) : (term7 m n p) = (term8 n m p).
Proof. exact (EQ_MP (@lem1031377 n m p) (@lem1031376 n m p)). Qed.
Lemma lem1031610 (y : nat) (x : nat) (z : nat) : (term7 x y z) = (term8 y x z).
Proof. exact (@lem1031609 y x z). Qed.
Lemma lem1031611 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031612 (y : nat) (x : nat) (z : nat) : (term44 x y z) = (term45 y x z).
Proof. exact (MK_COMB (@lem1031611) (@lem1031610 y x z)). Qed.
Lemma lem1031613 (y : nat) (x : nat) (z : nat) : (term8 y x z) = (term8 y x z).
Proof. exact (eq_refl (term8 y x z)). Qed.
Lemma lem1031614 (y : nat) (x : nat) (z : nat) : ((term7 x y z) = (term8 y x z)) = ((term8 y x z) = (term8 y x z)).
Proof. exact (MK_COMB (@lem1031612 y x z) (@lem1031613 y x z)). Qed.
Lemma lem1031616 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031617 (x : nat) : (x = x) = True.
Proof. exact (@lem1031616 nat x). Qed.
Lemma lem1031618 (y : nat) (x : nat) (z : nat) : ((term8 y x z) = (term8 y x z)) = True.
Proof. exact (@lem1031617 (term8 y x z)). Qed.
Lemma lem1031619 (y : nat) (x : nat) (z : nat) : ((term7 x y z) = (term8 y x z)) = True.
Proof. exact (TRANS (@lem1031614 y x z) (@lem1031618 y x z)). Qed.
Lemma lem1031620 (y : nat) (x : nat) : (term46 y x) = term32.
Proof. exact (fun_ext (fun z : nat => @lem1031619 y x z)). Qed.
Lemma lem1031621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031622 (y : nat) (x : nat) : (term5 y x) = term33.
Proof. exact (MK_COMB (@lem1031621) (@lem1031620 y x)). Qed.
Lemma lem1031624 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031625 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031624 nat t). Qed.
Lemma lem1031626 : term33 = True.
Proof. exact (@lem1031625 True). Qed.
Lemma lem1031627 (y : nat) (x : nat) : (term5 y x) = True.
Proof. exact (TRANS (@lem1031622 y x) (@lem1031626)). Qed.
Lemma lem1031628 (x : nat) : (term47 x) = term32.
Proof. exact (fun_ext (fun y : nat => @lem1031627 y x)). Qed.
Lemma lem1031629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031630 (x : nat) : (term3 x) = term33.
Proof. exact (MK_COMB (@lem1031629) (@lem1031628 x)). Qed.
Lemma lem1031632 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031633 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031632 nat t). Qed.
Lemma lem1031634 : term33 = True.
Proof. exact (@lem1031633 True). Qed.
Lemma lem1031635 (x : nat) : (term3 x) = True.
Proof. exact (TRANS (@lem1031630 x) (@lem1031634)). Qed.
Lemma lem1031636 : term48 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031635 x)). Qed.
Lemma lem1031637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031638 : term49 = term33.
Proof. exact (MK_COMB (@lem1031637) (@lem1031636)). Qed.
Lemma lem1031640 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031641 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031640 nat t). Qed.
Lemma lem1031642 : term33 = True.
Proof. exact (@lem1031641 True). Qed.
Lemma lem1031643 : term49 = True.
Proof. exact (TRANS (@lem1031638) (@lem1031642)). Qed.
Lemma lem1031644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031645 : term50 = (and True).
Proof. exact (MK_COMB (@lem1031644) (@lem1031643)). Qed.
Lemma lem1031655 (m : nat) : (term28 m) = term29.
Proof. exact (EQ_MP (@lem1031446 m) (@lem1031445 m)). Qed.
Lemma lem1031656 (x : nat) : (term28 x) = term29.
Proof. exact (@lem1031655 x). Qed.
Lemma lem1031657 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031658 (x : nat) : (term51 x) = term52.
Proof. exact (MK_COMB (@lem1031657) (@lem1031656 x)). Qed.
Lemma lem1031659 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1031660 (x : nat) : ((term28 x) = term29) = (term29 = term29).
Proof. exact (MK_COMB (@lem1031658 x) (@lem1031659)). Qed.
Lemma lem1031662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031663 (x : nat) : (x = x) = True.
Proof. exact (@lem1031662 nat x). Qed.
Lemma lem1031664 : (term29 = term29) = True.
Proof. exact (@lem1031663 term29). Qed.
Lemma lem1031665 (x : nat) : ((term28 x) = term29) = True.
Proof. exact (TRANS (@lem1031660 x) (@lem1031664)). Qed.
Lemma lem1031666 : term53 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031665 x)). Qed.
Lemma lem1031667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031668 : term26 = term33.
Proof. exact (MK_COMB (@lem1031667) (@lem1031666)). Qed.
Lemma lem1031670 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031671 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031670 nat t). Qed.
Lemma lem1031672 : term33 = True.
Proof. exact (@lem1031671 True). Qed.
Lemma lem1031673 : term26 = True.
Proof. exact (TRANS (@lem1031668) (@lem1031672)). Qed.
Lemma lem1031674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031675 : term54 = (and True).
Proof. exact (MK_COMB (@lem1031674) (@lem1031673)). Qed.
Lemma lem1031687 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem1031442 m n) (@lem1031441 m n)). Qed.
Lemma lem1031688 (x : nat) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (@lem1031687 x n). Qed.
Lemma lem1031689 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1031690 (x : nat) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem1031689) (@lem1031688 x n)). Qed.
Lemma lem1031691 (x : nat) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem1031692 (x : nat) (n : nat) : ((term24 x n) = (term25 x n)) = ((term25 x n) = (term25 x n)).
Proof. exact (MK_COMB (@lem1031690 x n) (@lem1031691 x n)). Qed.
Lemma lem1031694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031695 (x : nat) : (x = x) = True.
Proof. exact (@lem1031694 nat x). Qed.
Lemma lem1031696 (x : nat) (n : nat) : ((term25 x n) = (term25 x n)) = True.
Proof. exact (@lem1031695 (term25 x n)). Qed.
Lemma lem1031697 (x : nat) (n : nat) : ((term24 x n) = (term25 x n)) = True.
Proof. exact (TRANS (@lem1031692 x n) (@lem1031696 x n)). Qed.
Lemma lem1031698 (x : nat) : (term57 x) = term32.
Proof. exact (fun_ext (fun n : nat => @lem1031697 x n)). Qed.
Lemma lem1031699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031700 (x : nat) : (term22 x) = term33.
Proof. exact (MK_COMB (@lem1031699) (@lem1031698 x)). Qed.
Lemma lem1031702 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031703 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031702 nat t). Qed.
Lemma lem1031704 : term33 = True.
Proof. exact (@lem1031703 True). Qed.
Lemma lem1031705 (x : nat) : (term22 x) = True.
Proof. exact (TRANS (@lem1031700 x) (@lem1031704)). Qed.
Lemma lem1031706 : term58 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031705 x)). Qed.
Lemma lem1031707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031708 : term20 = term33.
Proof. exact (MK_COMB (@lem1031707) (@lem1031706)). Qed.
Lemma lem1031710 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031711 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031710 nat t). Qed.
Lemma lem1031712 : term33 = True.
Proof. exact (@lem1031711 True). Qed.
Lemma lem1031713 : term20 = True.
Proof. exact (TRANS (@lem1031708) (@lem1031712)). Qed.
Lemma lem1031714 : term59 = (True /\ True).
Proof. exact (MK_COMB (@lem1031675) (@lem1031713)). Qed.
Lemma lem1031716 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1031717 : (True /\ True) = True.
Proof. exact (@lem1031716 True). Qed.
Lemma lem1031718 : term59 = True.
Proof. exact (TRANS (@lem1031714) (@lem1031717)). Qed.
Lemma lem1031719 : term60 = (True /\ True).
Proof. exact (MK_COMB (@lem1031645) (@lem1031718)). Qed.
Lemma lem1031721 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1031722 : (True /\ True) = True.
Proof. exact (@lem1031721 True). Qed.
Lemma lem1031723 : term60 = True.
Proof. exact (TRANS (@lem1031719) (@lem1031722)). Qed.
Lemma lem1031724 : term61 = (True /\ True).
Proof. exact (MK_COMB (@lem1031591) (@lem1031723)). Qed.
Lemma lem1031726 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1031727 : (True /\ True) = True.
Proof. exact (@lem1031726 True). Qed.
Lemma lem1031728 : term61 = True.
Proof. exact (TRANS (@lem1031724) (@lem1031727)). Qed.
Lemma lem1031729 : term62 = (True /\ True).
Proof. exact (MK_COMB (@lem1031561) (@lem1031728)). Qed.
Lemma lem1031731 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1031732 : (True /\ True) = True.
Proof. exact (@lem1031731 True). Qed.
Lemma lem1031733 : term62 = True.
Proof. exact (TRANS (@lem1031729) (@lem1031732)). Qed.
Lemma lem1031734 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem1031735 : term64 = term65.
Proof. exact (MK_COMB (@lem1031734) (@lem1031733)). Qed.
Lemma lem1031737 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1031738 : term65 = term66.
Proof. exact (@lem1031737 term66). Qed.
Lemma lem1031749 : term64 = term66.
Proof. exact (TRANS (@lem1031735) (@lem1031738)). Qed.
Lemma lem1031750 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem1031751 : term68 = term69.
Proof. exact (MK_COMB (@lem1031750) (@lem1031749)). Qed.
Lemma lem1031754 : term70 = term71.
Proof. exact (MK_COMB (@lem1031504) (@lem1031751)). Qed.
Lemma lem1031756 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1031757 : term71 = term69.
Proof. exact (@lem1031756 term69). Qed.
Lemma lem1031784 : term70 = term69.
Proof. exact (TRANS (@lem1031754) (@lem1031757)). Qed.
Lemma lem1031785 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem1031786 : term73 = term74.
Proof. exact (MK_COMB (@lem1031785) (@lem1031784)). Qed.
Lemma lem1031789 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1031790 : term76 = term77.
Proof. exact (MK_COMB (@lem1031789) (@lem1031786)). Qed.
Lemma lem1031793 : term77 = term76.
Proof. exact (SYM (@lem1031790)). Qed.
Lemma lem1031820 (m : nat) (n : nat) (p : nat) : (term78 m n p) = (term79 m n p).
Proof. exact (proj1 (@lem1031366 n m p)). Qed.
Lemma lem1031821 (x : nat) (y : nat) (z : nat) : (term78 x y z) = (term79 x y z).
Proof. exact (@lem1031820 x y z). Qed.
Lemma lem1031831 (x : nat) (y : nat) (z : nat) : (term80 x y z) = (term80 x y z).
Proof. exact (eq_refl (term80 x y z)). Qed.
Lemma lem1031832 (x : nat) (y : nat) (z : nat) : ((term79 x y z) = (term78 x y z)) = ((term79 x y z) = (term79 x y z)).
Proof. exact (MK_COMB (@lem1031831 x y z) (@lem1031821 x y z)). Qed.
Lemma lem1031834 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031835 (x : nat) : (x = x) = True.
Proof. exact (@lem1031834 nat x). Qed.
Lemma lem1031836 (x : nat) (y : nat) (z : nat) : ((term79 x y z) = (term79 x y z)) = True.
Proof. exact (@lem1031835 (term79 x y z)). Qed.
Lemma lem1031837 (x : nat) (y : nat) (z : nat) : ((term79 x y z) = (term78 x y z)) = True.
Proof. exact (TRANS (@lem1031832 x y z) (@lem1031836 x y z)). Qed.
Lemma lem1031838 (x : nat) (y : nat) : (term81 x y) = term32.
Proof. exact (fun_ext (fun z : nat => @lem1031837 x y z)). Qed.
Lemma lem1031839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031840 (x : nat) (y : nat) : (term82 x y) = term33.
Proof. exact (MK_COMB (@lem1031839) (@lem1031838 x y)). Qed.
Lemma lem1031842 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031843 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031842 nat t). Qed.
Lemma lem1031844 : term33 = True.
Proof. exact (@lem1031843 True). Qed.
Lemma lem1031845 (x : nat) (y : nat) : (term82 x y) = True.
Proof. exact (TRANS (@lem1031840 x y) (@lem1031844)). Qed.
Lemma lem1031846 (x : nat) : (term83 x) = term32.
Proof. exact (fun_ext (fun y : nat => @lem1031845 x y)). Qed.
Lemma lem1031847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031848 (x : nat) : (term84 x) = term33.
Proof. exact (MK_COMB (@lem1031847) (@lem1031846 x)). Qed.
Lemma lem1031850 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031851 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031850 nat t). Qed.
Lemma lem1031852 : term33 = True.
Proof. exact (@lem1031851 True). Qed.
Lemma lem1031853 (x : nat) : (term84 x) = True.
Proof. exact (TRANS (@lem1031848 x) (@lem1031852)). Qed.
Lemma lem1031854 : term85 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031853 x)). Qed.
Lemma lem1031855 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031856 : term86 = term33.
Proof. exact (MK_COMB (@lem1031855) (@lem1031854)). Qed.
Lemma lem1031858 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031859 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031858 nat t). Qed.
Lemma lem1031860 : term33 = True.
Proof. exact (@lem1031859 True). Qed.
Lemma lem1031861 : term86 = True.
Proof. exact (TRANS (@lem1031856) (@lem1031860)). Qed.
Lemma lem1031862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031863 : term75 = (and True).
Proof. exact (MK_COMB (@lem1031862) (@lem1031861)). Qed.
Lemma lem1031880 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1031881 (x : nat) (y : nat) : (Nat.add y x) = (Nat.add x y).
Proof. exact (@lem1031880 x y). Qed.
Lemma lem1031885 (x : nat) (y : nat) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1031886 (x : nat) (y : nat) : ((Nat.add x y) = (Nat.add y x)) = ((Nat.add x y) = (Nat.add x y)).
Proof. exact (MK_COMB (@lem1031885 x y) (@lem1031881 x y)). Qed.
Lemma lem1031888 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031889 (x : nat) : (x = x) = True.
Proof. exact (@lem1031888 nat x). Qed.
Lemma lem1031890 (x : nat) (y : nat) : ((Nat.add x y) = (Nat.add x y)) = True.
Proof. exact (@lem1031889 (Nat.add x y)). Qed.
Lemma lem1031891 (y : nat) (x : nat) : ((Nat.add x y) = (Nat.add y x)) = True.
Proof. exact (TRANS (@lem1031886 x y) (@lem1031890 x y)). Qed.
Lemma lem1031892 (x : nat) : (term88 x) = term32.
Proof. exact (fun_ext (fun y : nat => @lem1031891 y x)). Qed.
Lemma lem1031893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031894 (x : nat) : (term89 x) = term33.
Proof. exact (MK_COMB (@lem1031893) (@lem1031892 x)). Qed.
Lemma lem1031896 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031897 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031896 nat t). Qed.
Lemma lem1031898 : term33 = True.
Proof. exact (@lem1031897 True). Qed.
Lemma lem1031899 (x : nat) : (term89 x) = True.
Proof. exact (TRANS (@lem1031894 x) (@lem1031898)). Qed.
Lemma lem1031900 : term90 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031899 x)). Qed.
Lemma lem1031901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031902 : term91 = term33.
Proof. exact (MK_COMB (@lem1031901) (@lem1031900)). Qed.
Lemma lem1031904 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031905 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031904 nat t). Qed.
Lemma lem1031906 : term33 = True.
Proof. exact (@lem1031905 True). Qed.
Lemma lem1031907 : term91 = True.
Proof. exact (TRANS (@lem1031902) (@lem1031906)). Qed.
Lemma lem1031908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031909 : term72 = (and True).
Proof. exact (MK_COMB (@lem1031908) (@lem1031907)). Qed.
Lemma lem1031936 (m : nat) (n : nat) (p : nat) : (term92 m n p) = (term93 m n p).
Proof. exact (proj1 (@lem1031362 n m p)). Qed.
Lemma lem1031937 (x : nat) (y : nat) (z : nat) : (term92 x y z) = (term93 x y z).
Proof. exact (@lem1031936 x y z). Qed.
Lemma lem1031947 (x : nat) (y : nat) (z : nat) : (term94 x y z) = (term94 x y z).
Proof. exact (eq_refl (term94 x y z)). Qed.
Lemma lem1031948 (x : nat) (y : nat) (z : nat) : ((term93 x y z) = (term92 x y z)) = ((term93 x y z) = (term93 x y z)).
Proof. exact (MK_COMB (@lem1031947 x y z) (@lem1031937 x y z)). Qed.
Lemma lem1031950 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031951 (x : nat) : (x = x) = True.
Proof. exact (@lem1031950 nat x). Qed.
Lemma lem1031952 (x : nat) (y : nat) (z : nat) : ((term93 x y z) = (term93 x y z)) = True.
Proof. exact (@lem1031951 (term93 x y z)). Qed.
Lemma lem1031953 (x : nat) (y : nat) (z : nat) : ((term93 x y z) = (term92 x y z)) = True.
Proof. exact (TRANS (@lem1031948 x y z) (@lem1031952 x y z)). Qed.
Lemma lem1031954 (x : nat) (y : nat) : (term95 x y) = term32.
Proof. exact (fun_ext (fun z : nat => @lem1031953 x y z)). Qed.
Lemma lem1031955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031956 (x : nat) (y : nat) : (term96 x y) = term33.
Proof. exact (MK_COMB (@lem1031955) (@lem1031954 x y)). Qed.
Lemma lem1031958 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031959 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031958 nat t). Qed.
Lemma lem1031960 : term33 = True.
Proof. exact (@lem1031959 True). Qed.
Lemma lem1031961 (x : nat) (y : nat) : (term96 x y) = True.
Proof. exact (TRANS (@lem1031956 x y) (@lem1031960)). Qed.
Lemma lem1031962 (x : nat) : (term97 x) = term32.
Proof. exact (fun_ext (fun y : nat => @lem1031961 x y)). Qed.
Lemma lem1031963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031964 (x : nat) : (term98 x) = term33.
Proof. exact (MK_COMB (@lem1031963) (@lem1031962 x)). Qed.
Lemma lem1031966 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031967 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031966 nat t). Qed.
Lemma lem1031968 : term33 = True.
Proof. exact (@lem1031967 True). Qed.
Lemma lem1031969 (x : nat) : (term98 x) = True.
Proof. exact (TRANS (@lem1031964 x) (@lem1031968)). Qed.
Lemma lem1031970 : term99 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1031969 x)). Qed.
Lemma lem1031971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1031972 : term100 = term33.
Proof. exact (MK_COMB (@lem1031971) (@lem1031970)). Qed.
Lemma lem1031974 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1031975 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1031974 nat t). Qed.
Lemma lem1031976 : term33 = True.
Proof. exact (@lem1031975 True). Qed.
Lemma lem1031977 : term100 = True.
Proof. exact (TRANS (@lem1031972) (@lem1031976)). Qed.
Lemma lem1031978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1031979 : term67 = (and True).
Proof. exact (MK_COMB (@lem1031978) (@lem1031977)). Qed.
Lemma lem1031994 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1031995 (x : nat) (y : nat) : (Nat.mul y x) = (Nat.mul x y).
Proof. exact (@lem1031994 x y). Qed.
Lemma lem1031999 (x : nat) (y : nat) : (term101 x y) = (term101 x y).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1032000 (x : nat) (y : nat) : ((Nat.mul x y) = (Nat.mul y x)) = ((Nat.mul x y) = (Nat.mul x y)).
Proof. exact (MK_COMB (@lem1031999 x y) (@lem1031995 x y)). Qed.
Lemma lem1032002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1032003 (x : nat) : (x = x) = True.
Proof. exact (@lem1032002 nat x). Qed.
Lemma lem1032004 (x : nat) (y : nat) : ((Nat.mul x y) = (Nat.mul x y)) = True.
Proof. exact (@lem1032003 (Nat.mul x y)). Qed.
Lemma lem1032005 (y : nat) (x : nat) : ((Nat.mul x y) = (Nat.mul y x)) = True.
Proof. exact (TRANS (@lem1032000 x y) (@lem1032004 x y)). Qed.
Lemma lem1032006 (x : nat) : (term102 x) = term32.
Proof. exact (fun_ext (fun y : nat => @lem1032005 y x)). Qed.
Lemma lem1032007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1032008 (x : nat) : (term103 x) = term33.
Proof. exact (MK_COMB (@lem1032007) (@lem1032006 x)). Qed.
Lemma lem1032010 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032011 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1032010 nat t). Qed.
Lemma lem1032012 : term33 = True.
Proof. exact (@lem1032011 True). Qed.
Lemma lem1032013 (x : nat) : (term103 x) = True.
Proof. exact (TRANS (@lem1032008 x) (@lem1032012)). Qed.
Lemma lem1032014 : term104 = term32.
Proof. exact (fun_ext (fun x : nat => @lem1032013 x)). Qed.
Lemma lem1032015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1032016 : term66 = term33.
Proof. exact (MK_COMB (@lem1032015) (@lem1032014)). Qed.
Lemma lem1032018 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032019 (t : Prop) : (term35 t) = t.
Proof. exact (@lem1032018 nat t). Qed.
Lemma lem1032020 : term33 = True.
Proof. exact (@lem1032019 True). Qed.
Lemma lem1032021 : term66 = True.
Proof. exact (TRANS (@lem1032016) (@lem1032020)). Qed.
Lemma lem1032022 : term69 = (True /\ True).
Proof. exact (MK_COMB (@lem1031979) (@lem1032021)). Qed.
Lemma lem1032024 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1032025 : (True /\ True) = True.
Proof. exact (@lem1032024 True). Qed.
Lemma lem1032026 : term69 = True.
Proof. exact (TRANS (@lem1032022) (@lem1032025)). Qed.
Lemma lem1032027 : term74 = (True /\ True).
Proof. exact (MK_COMB (@lem1031909) (@lem1032026)). Qed.
Lemma lem1032029 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1032030 : (True /\ True) = True.
Proof. exact (@lem1032029 True). Qed.
Lemma lem1032031 : term74 = True.
Proof. exact (TRANS (@lem1032027) (@lem1032030)). Qed.
Lemma lem1032032 : term77 = (True /\ True).
Proof. exact (MK_COMB (@lem1031863) (@lem1032031)). Qed.
Lemma lem1032034 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1032035 : (True /\ True) = True.
Proof. exact (@lem1032034 True). Qed.
Lemma lem1032036 : term77 = True.
Proof. exact (TRANS (@lem1032032) (@lem1032035)). Qed.
Lemma lem1032037 : True = term77.
Proof. exact (SYM (@lem1032036)). Qed.
Lemma lem1032038 : term77.
Proof. exact (EQ_MP (@lem1032037) (@lem0)). Qed.
Lemma lem1032039 : term76.
Proof. exact (EQ_MP (@lem1031793) (@lem1032038)). Qed.
Lemma lem1032041 {A : Type'} (m : A) (r0 : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (r1 : A) (add : type1400 A) (y : A) (z : A) (mul : type1400 A) (pwr : type1423 A) (x : A) (q : nat) : term105 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (fun h0 : term106 A r0 add r1 mul pwr => @lem1031360 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h0). Qed.
Lemma lem1032042 (m : nat) (r0 : nat) (ly : nat) (rx : nat) (lx : nat) (ry : nat) (b : nat) (a : nat) (c : nat) (d : nat) (p : nat) (r1 : nat) (add : type1606) (y : nat) (z : nat) (mul : type1606) (pwr : type1606) (x : nat) (q : nat) : term107 m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (@lem1032041 nat m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q). Qed.
Lemma lem1032043 (m : nat) (ly : nat) (rx : nat) (lx : nat) (ry : nat) (b : nat) (a : nat) (c : nat) (d : nat) (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term108 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem1032042 m (NUMERAL 0) ly rx lx ry b a c d p term29 Nat.add y z Nat.mul Nat.pow x q). Qed.
Lemma lem1032044 (m : nat) (ly : nat) (rx : nat) (lx : nat) (ry : nat) (b : nat) (a : nat) (c : nat) (d : nat) (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term109 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem1032043 m ly rx lx ry b a c d p y z x q (@lem1032039)). Qed.

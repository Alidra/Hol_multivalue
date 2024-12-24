Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_IMP_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1523469 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17362 (x = y) (real_le x y)). Qed.
Lemma lem1523470 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523471 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1523470 (term6 x)). Qed.
Lemma lem1523472 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1523473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523474 (x : real) (y : real) : (term9 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1523473) (@lem1523472 x y)). Qed.
Lemma lem1523475 (x : real) (y : real) : (term9 x y) = (term1 x y).
Proof. exact (TRANS (@lem1523474 x y) (@lem1523469 x y)). Qed.
Lemma lem1523476 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1523475 x y)). Qed.
Lemma lem1523477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523478 (x : real) : (term5 x) = (term12 x).
Proof. exact (MK_COMB (@lem1523477) (@lem1523476 x)). Qed.
Lemma lem1523479 (x : real) : (term4 x) = (term12 x).
Proof. exact (TRANS (@lem1523471 x) (@lem1523478 x)). Qed.
Lemma lem1523480 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1523481 : term13 = term14.
Proof. exact (@lem1523480 term15). Qed.
Lemma lem1523482 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1523483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1523484 (x : real) : (term18 x) = (term4 x).
Proof. exact (MK_COMB (@lem1523483) (@lem1523482 x)). Qed.
Lemma lem1523485 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1523484 x) (@lem1523479 x)). Qed.
Lemma lem1523486 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1523485 x)). Qed.
Lemma lem1523487 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523488 : term14 = term21.
Proof. exact (MK_COMB (@lem1523487) (@lem1523486)). Qed.
Lemma lem1523490 : term13 = term21.
Proof. exact (TRANS (@lem1523481) (@lem1523488)). Qed.
Lemma lem1523497 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1523498 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1523497 x y)). Qed.
Lemma lem1523499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523500 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1523499) (@lem1523498 x)). Qed.
Lemma lem1523501 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1523500 x)). Qed.
Lemma lem1523502 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523503 : term21 = term21.
Proof. exact (MK_COMB (@lem1523502) (@lem1523501)). Qed.
Lemma lem1523504 : term13 = term21.
Proof. exact (TRANS (@lem1523490) (@lem1523503)). Qed.
Lemma lem1523505 (x : real) (y : real) : (x = y) = ((real_sub x y) = term22).
Proof. exact (@lem1483529 x y). Qed.
Lemma lem1523518 (x : real) (y : real) : (real_sub x y) = (term23 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1523519 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1523520 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1523519) (@lem1523518 x y)). Qed.
Lemma lem1523521 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1523522 (x : real) (y : real) : ((real_sub x y) = term22) = ((term23 x y) = term22).
Proof. exact (MK_COMB (@lem1523520 x y) (@lem1523521)). Qed.
Lemma lem1523523 (x : real) (y : real) : (x = y) = ((term23 x y) = term22).
Proof. exact (TRANS (@lem1523505 x y) (@lem1523522 x y)). Qed.
Lemma lem1523524 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483533 x y). Qed.
Lemma lem1523537 (x : real) (y : real) : (real_sub x y) = (term23 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1523538 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523539 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1523538) (@lem1523537 x y)). Qed.
Lemma lem1523540 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1523541 (x : real) (y : real) : (term27 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1523539 x y) (@lem1523540)). Qed.
Lemma lem1523542 (x : real) (y : real) : (term26 x y) = (term30 x y).
Proof. exact (TRANS (@lem1523524 x y) (@lem1523541 x y)). Qed.
Lemma lem1523543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1523544 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1523543) (@lem1523523 x y)). Qed.
Lemma lem1523545 (x : real) (y : real) : (term1 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1523544 x y) (@lem1523542 x y)). Qed.
Lemma lem1523546 (x : real) : (term11 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1523545 x y)). Qed.
Lemma lem1523547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523548 (x : real) : (term12 x) = (term35 x).
Proof. exact (MK_COMB (@lem1523547) (@lem1523546 x)). Qed.
Lemma lem1523549 : term20 = term36.
Proof. exact (fun_ext (fun x : real => @lem1523548 x)). Qed.
Lemma lem1523550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523551 : term21 = term37.
Proof. exact (MK_COMB (@lem1523550) (@lem1523549)). Qed.
Lemma lem1523610 : term13 = term37.
Proof. exact (TRANS (@lem1523504) (@lem1523551)). Qed.
Lemma lem1523617 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1523618 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1523617 x y)). Qed.
Lemma lem1523619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523620 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1523619) (@lem1523618 x)). Qed.
Lemma lem1523621 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1523620 x)). Qed.
Lemma lem1523622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523623 : term37 = term37.
Proof. exact (MK_COMB (@lem1523622) (@lem1523621)). Qed.
Lemma lem1523624 : term13 = term37.
Proof. exact (TRANS (@lem1523610) (@lem1523623)). Qed.
Lemma lem1523628 (x : real) (y : real) (h1 : term33 x y) : term33 x y.
Proof. exact (h1). Qed.
Lemma lem1523629 (x : real) (y : real) (h1 : term33 x y) : term30 x y.
Proof. exact (proj2 (@lem1523628 x y h1)). Qed.
Lemma lem1523630 (x : real) (y : real) (h1 : term33 x y) : (term23 x y) = term22.
Proof. exact (proj1 (@lem1523628 x y h1)). Qed.
Lemma lem1523632 (n : nat) (m : nat) : (term38 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523633 : term39 = term40.
Proof. exact (@lem1523632 (NUMERAL 0) term41). Qed.
Lemma lem1523634 : term42 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1523635 (h1 : term42 = (BIT1 0)) : term40 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1523636 : (term42 = (BIT1 0)) = (term40 = True).
Proof. exact (prop_ext (fun h1 : term42 = (BIT1 0) => @lem1523635 h1) (fun h1 : term40 = True => @lem1523634)). Qed.
Lemma lem1523637 : term40 = True.
Proof. exact (EQ_MP (@lem1523636) (@lem1523634)). Qed.
Lemma lem1523638 : term39 = True.
Proof. exact (TRANS (@lem1523633) (@lem1523637)). Qed.
Lemma lem1523639 : True = term39.
Proof. exact (SYM (@lem1523638)). Qed.
Lemma lem1523640 : term39.
Proof. exact (EQ_MP (@lem1523639) (@lem0)). Qed.
Lemma lem1523641 (x : real) (y : real) (h1 : term33 x y) : term43 x y.
Proof. exact (conj (@lem1523640) (@lem1523629 x y h1)). Qed.
Lemma lem1523643 (x : real) (y : real) : term44 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1523644 (x : real) (y : real) : term45 x y.
Proof. exact (@lem1523643 term46 (term23 x y)). Qed.
Lemma lem1523645 (x : real) (y : real) (h1 : term33 x y) : term47 x y.
Proof. exact (@lem1523644 x y (@lem1523641 x y h1)). Qed.
Lemma lem1523646 (x : real) (y : real) : (term48 x y) = (term23 x y).
Proof. exact (@lem1483460 (term23 x y)). Qed.
Lemma lem1523647 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523648 (x : real) (y : real) : (term49 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1523647) (@lem1523646 x y)). Qed.
Lemma lem1523649 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1523650 (x : real) (y : real) : (term47 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1523648 x y) (@lem1523649)). Qed.
Lemma lem1523651 (x : real) (y : real) (h1 : term33 x y) : term30 x y.
Proof. exact (EQ_MP (@lem1523650 x y) (@lem1523645 x y h1)). Qed.
Lemma lem1523653 (y : real) : term50 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1523654 (x : real) (y : real) : term51 x y.
Proof. exact (@lem1523653 (term23 x y)). Qed.
Lemma lem1523655 (x : real) (y : real) (h1 : term33 x y) : term52 x y.
Proof. exact (@lem1523654 x y (@lem1523630 x y h1)). Qed.
Lemma lem1523656 (x : real) (y : real) (h1 : term33 x y) : term53 x y.
Proof. exact (@lem1523655 x y h1 term54). Qed.
Lemma lem1523657 (x : real) (y : real) : (term53 x y) = ((term55 x y) = term22).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1523658 (x : real) (y : real) (h1 : term33 x y) : (term55 x y) = term22.
Proof. exact (EQ_MP (@lem1523657 x y) (@lem1523656 x y h1)). Qed.
Lemma lem1523659 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem1483508 x term54 (term57 y)). Qed.
Lemma lem1523660 (y : real) : (term58 y) = (term59 y).
Proof. exact (@lem1483476 term54 term54 y). Qed.
Lemma lem1523662 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1523663 : term62 = term63.
Proof. exact (@lem1523662 term41 term41). Qed.
Lemma lem1523664 : (term64 = (BIT1 0)) = (term65 = term41).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1523665 : term65 = term41.
Proof. exact (EQ_MP (@lem1523664) (@lem940073)). Qed.
Lemma lem1523666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1523667 : term63 = term46.
Proof. exact (MK_COMB (@lem1523666) (@lem1523665)). Qed.
Lemma lem1523668 : term62 = term46.
Proof. exact (TRANS (@lem1523663) (@lem1523667)). Qed.
Lemma lem1523669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523670 : term66 = term67.
Proof. exact (MK_COMB (@lem1523669) (@lem1523668)). Qed.
Lemma lem1523671 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523672 (y : real) : (term59 y) = (term68 y).
Proof. exact (MK_COMB (@lem1523670) (@lem1523671 y)). Qed.
Lemma lem1523673 (y : real) : (term58 y) = (term68 y).
Proof. exact (TRANS (@lem1523660 y) (@lem1523672 y)). Qed.
Lemma lem1523674 (y : real) : (term68 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1523675 (y : real) : (term58 y) = y.
Proof. exact (TRANS (@lem1523673 y) (@lem1523674 y)). Qed.
Lemma lem1523678 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1523679 (x : real) (y : real) : (term56 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1523678 x) (@lem1523675 y)). Qed.
Lemma lem1523680 (x : real) (y : real) : (term55 x y) = (term70 x y).
Proof. exact (TRANS (@lem1523659 x y) (@lem1523679 x y)). Qed.
Lemma lem1523681 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1523682 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1523681) (@lem1523680 x y)). Qed.
Lemma lem1523683 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1523684 (x : real) (y : real) : ((term55 x y) = term22) = ((term70 x y) = term22).
Proof. exact (MK_COMB (@lem1523682 x y) (@lem1523683)). Qed.
Lemma lem1523685 (x : real) (y : real) (h1 : term33 x y) : (term70 x y) = term22.
Proof. exact (EQ_MP (@lem1523684 x y) (@lem1523658 x y h1)). Qed.
Lemma lem1523686 (x : real) (y : real) (h1 : term33 x y) : term73 x y.
Proof. exact (conj (@lem1523685 x y h1) (@lem1523651 x y h1)). Qed.
Lemma lem1523688 (x : real) (y : real) : term74 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1523689 (x : real) (y : real) : term75 x y.
Proof. exact (@lem1523688 (term70 x y) (term23 x y)). Qed.
Lemma lem1523690 (x : real) (y : real) (h1 : term33 x y) : term76 x y.
Proof. exact (@lem1523689 x y (@lem1523686 x y h1)). Qed.
Lemma lem1523691 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483480 (term57 x) x y (term57 y)). Qed.
Lemma lem1523692 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483440 term54 x). Qed.
Lemma lem1523694 (m : nat) : (term81 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523695 : term82 = term22.
Proof. exact (@lem1523694 term41). Qed.
Lemma lem1523696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523697 : term83 = term84.
Proof. exact (MK_COMB (@lem1523696) (@lem1523695)). Qed.
Lemma lem1523698 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1523699 (x : real) : (term80 x) = (term85 x).
Proof. exact (MK_COMB (@lem1523697) (@lem1523698 x)). Qed.
Lemma lem1523700 (x : real) : (term79 x) = (term85 x).
Proof. exact (TRANS (@lem1523692 x) (@lem1523699 x)). Qed.
Lemma lem1523701 (x : real) : (term85 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1523702 (x : real) : (term79 x) = term22.
Proof. exact (TRANS (@lem1523700 x) (@lem1523701 x)). Qed.
Lemma lem1523703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1523704 (x : real) : (term86 x) = term87.
Proof. exact (MK_COMB (@lem1523703) (@lem1523702 x)). Qed.
Lemma lem1523705 (y : real) : (term88 y) = (term80 y).
Proof. exact (@lem1483442 term54 y). Qed.
Lemma lem1523707 (m : nat) : (term81 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523708 : term82 = term22.
Proof. exact (@lem1523707 term41). Qed.
Lemma lem1523709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523710 : term83 = term84.
Proof. exact (MK_COMB (@lem1523709) (@lem1523708)). Qed.
Lemma lem1523711 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523712 (y : real) : (term80 y) = (term85 y).
Proof. exact (MK_COMB (@lem1523710) (@lem1523711 y)). Qed.
Lemma lem1523713 (y : real) : (term88 y) = (term85 y).
Proof. exact (TRANS (@lem1523705 y) (@lem1523712 y)). Qed.
Lemma lem1523714 (y : real) : (term85 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1523715 (y : real) : (term88 y) = term22.
Proof. exact (TRANS (@lem1523713 y) (@lem1523714 y)). Qed.
Lemma lem1523716 (x : real) (y : real) : (term78 x y) = term89.
Proof. exact (MK_COMB (@lem1523704 x) (@lem1523715 y)). Qed.
Lemma lem1523717 (x : real) (y : real) : (term77 x y) = term89.
Proof. exact (TRANS (@lem1523691 x y) (@lem1523716 x y)). Qed.
Lemma lem1523718 : term89 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1523719 (x : real) (y : real) : (term77 x y) = term22.
Proof. exact (TRANS (@lem1523717 x y) (@lem1523718)). Qed.
Lemma lem1523720 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523721 (x : real) (y : real) : (term90 x y) = term91.
Proof. exact (MK_COMB (@lem1523720) (@lem1523719 x y)). Qed.
Lemma lem1523722 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1523723 (x : real) (y : real) : (term76 x y) = term92.
Proof. exact (MK_COMB (@lem1523721 x y) (@lem1523722)). Qed.
Lemma lem1523724 (x : real) (y : real) (h1 : term33 x y) : term92.
Proof. exact (EQ_MP (@lem1523723 x y) (@lem1523690 x y h1)). Qed.
Lemma lem1523726 (n : nat) (m : nat) : (term38 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523727 : term92 = term93.
Proof. exact (@lem1523726 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523728 : term93 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523729 : term92 = False.
Proof. exact (TRANS (@lem1523727) (@lem1523728)). Qed.
Lemma lem1523730 (x : real) (y : real) (h1 : term33 x y) : False.
Proof. exact (EQ_MP (@lem1523729) (@lem1523724 x y h1)). Qed.
Lemma lem1523732 (x : real) (y : real) (h1 : term33 x y) : term33 x y.
Proof. exact (h1). Qed.
Lemma lem1523733 (x : real) (y : real) (h1 : term33 x y) : (term33 x y) = False.
Proof. exact (prop_ext (fun h2 : term33 x y => @lem1523730 x y h1) (fun h2 : False => @lem1523732 x y h1)). Qed.
Lemma lem1523734 (x : real) (y : real) (h1 : term33 x y) : False.
Proof. exact (EQ_MP (@lem1523733 x y h1) (@lem1523732 x y h1)). Qed.
Lemma lem1523735 (x : real) (h1 : term35 x) : term35 x.
Proof. exact (h1). Qed.
Lemma lem1523736 (x : real) (h1 : term35 x) : False.
Proof. exact (ex_elim (@lem1523735 x h1) (fun y : real => fun h0 : term34 x y => @lem1523734 x y h0)). Qed.
Lemma lem1523737 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1523738 (h1 : term37) : False.
Proof. exact (ex_elim (@lem1523737 h1) (fun x : real => fun h0 : term36 x => @lem1523736 x h0)). Qed.
Lemma lem1523739 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1523740 (h1 : term13) : term37.
Proof. exact (EQ_MP (@lem1523624) (@lem1523739 h1)). Qed.
Lemma lem1523741 (h1 : term13) : term37 = False.
Proof. exact (prop_ext (fun h2 : term37 => @lem1523738 h2) (fun h2 : False => @lem1523740 h1)). Qed.
Lemma lem1523742 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1523741 h1) (@lem1523740 h1)). Qed.
Lemma lem1523743 : term94.
Proof. exact (fun h0 : term13 => @lem1523742 h0). Qed.
Lemma lem1523744 : term95.
Proof. exact (@lem1386578 term96). Qed.
Lemma lem1523745 : term96.
Proof. exact (@lem1523744 (@lem1523743)). Qed.

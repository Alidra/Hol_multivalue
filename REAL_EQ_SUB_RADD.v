Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_SUB_RADD_term_abbrevs.
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
Require Import thm1483482_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1521549 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 ((real_sub x y) = z) (x = (real_add z y))). Qed.
Lemma lem1521550 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1521551 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (@lem1521550 (term6 x y)). Qed.
Lemma lem1521552 (x : real) (z : real) (y : real) : (term7 x y z) = (((real_sub x y) = z) = (x = (real_add z y))).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1521553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1521554 (x : real) (z : real) (y : real) : (term8 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1521553) (@lem1521552 x z y)). Qed.
Lemma lem1521555 (x : real) (z : real) (y : real) : (term8 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1521554 x z y) (@lem1521549 x z y)). Qed.
Lemma lem1521556 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (fun_ext (fun z : real => @lem1521555 x z y)). Qed.
Lemma lem1521557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521558 (x : real) (y : real) : (term5 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1521557) (@lem1521556 x y)). Qed.
Lemma lem1521559 (x : real) (y : real) : (term4 x y) = (term11 x y).
Proof. exact (TRANS (@lem1521551 x y) (@lem1521558 x y)). Qed.
Lemma lem1521560 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1521561 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1521560 (term14 x)). Qed.
Lemma lem1521562 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1521563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1521564 (x : real) (y : real) : (term17 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1521563) (@lem1521562 x y)). Qed.
Lemma lem1521565 (x : real) (y : real) : (term17 x y) = (term11 x y).
Proof. exact (TRANS (@lem1521564 x y) (@lem1521559 x y)). Qed.
Lemma lem1521566 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1521565 x y)). Qed.
Lemma lem1521567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521568 (x : real) : (term13 x) = (term20 x).
Proof. exact (MK_COMB (@lem1521567) (@lem1521566 x)). Qed.
Lemma lem1521569 (x : real) : (term12 x) = (term20 x).
Proof. exact (TRANS (@lem1521561 x) (@lem1521568 x)). Qed.
Lemma lem1521570 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1521571 : term21 = term22.
Proof. exact (@lem1521570 term23). Qed.
Lemma lem1521572 (x : real) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1521573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1521574 (x : real) : (term26 x) = (term12 x).
Proof. exact (MK_COMB (@lem1521573) (@lem1521572 x)). Qed.
Lemma lem1521575 (x : real) : (term26 x) = (term20 x).
Proof. exact (TRANS (@lem1521574 x) (@lem1521569 x)). Qed.
Lemma lem1521576 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1521575 x)). Qed.
Lemma lem1521577 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521578 : term22 = term29.
Proof. exact (MK_COMB (@lem1521577) (@lem1521576)). Qed.
Lemma lem1521580 : term21 = term29.
Proof. exact (TRANS (@lem1521571) (@lem1521578)). Qed.
Lemma lem1521597 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1521598 (x : real) (y : real) : (term10 x y) = (term10 x y).
Proof. exact (fun_ext (fun z : real => @lem1521597 x z y)). Qed.
Lemma lem1521599 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521600 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1521599) (@lem1521598 x y)). Qed.
Lemma lem1521601 (x : real) : (term19 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1521600 x y)). Qed.
Lemma lem1521602 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521603 (x : real) : (term20 x) = (term20 x).
Proof. exact (MK_COMB (@lem1521602) (@lem1521601 x)). Qed.
Lemma lem1521604 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1521603 x)). Qed.
Lemma lem1521605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521606 : term29 = term29.
Proof. exact (MK_COMB (@lem1521605) (@lem1521604)). Qed.
Lemma lem1521607 : term21 = term29.
Proof. exact (TRANS (@lem1521580) (@lem1521606)). Qed.
Lemma lem1521608 (x : real) (y : real) (z : real) : ((real_sub x y) = z) = ((term30 x y z) = term31).
Proof. exact (@lem1483529 (real_sub x y) z). Qed.
Lemma lem1521609 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521622 (x : real) (y : real) : (real_sub x y) = (term32 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1521623 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1521624 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1521623) (@lem1521622 x y)). Qed.
Lemma lem1521625 (x : real) (y : real) (z : real) : (term30 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem1521624 x y) (@lem1521609 z)). Qed.
Lemma lem1521626 (x : real) (y : real) (z : real) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem1483519 (term32 x y) z). Qed.
Lemma lem1521635 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (@lem1483482 x (term38 y) (term38 z)). Qed.
Lemma lem1521636 (x : real) (y : real) (z : real) : (term35 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521626 x y z) (@lem1521635 x y z)). Qed.
Lemma lem1521637 (x : real) (y : real) (z : real) : (term30 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521625 x y z) (@lem1521636 x y z)). Qed.
Lemma lem1521638 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521639 (x : real) (y : real) (z : real) : (term39 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1521638) (@lem1521637 x y z)). Qed.
Lemma lem1521640 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521641 (x : real) (y : real) (z : real) : ((term30 x y z) = term31) = ((term37 x y z) = term31).
Proof. exact (MK_COMB (@lem1521639 x y z) (@lem1521640)). Qed.
Lemma lem1521642 (x : real) (y : real) (z : real) : ((real_sub x y) = z) = ((term37 x y z) = term31).
Proof. exact (TRANS (@lem1521608 x y z) (@lem1521641 x y z)). Qed.
Lemma lem1521643 (x : real) (z : real) (y : real) : (term41 x z y) = (term42 x z y).
Proof. exact (@lem1483554 x (real_add z y)). Qed.
Lemma lem1521650 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1521653 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1521654 (x : real) (y : real) (z : real) : (term43 x z y) = (term43 x y z).
Proof. exact (MK_COMB (@lem1521653 x) (@lem1521650 y z)). Qed.
Lemma lem1521655 (x : real) (y : real) (z : real) : (term43 x y z) = (term44 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1521662 (y : real) (z : real) : (term45 y z) = (term46 y z).
Proof. exact (@lem1483508 y term47 z). Qed.
Lemma lem1521663 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1521666 (x : real) (y : real) (z : real) : (term44 x y z) = (term37 x y z).
Proof. exact (MK_COMB (@lem1521663 x) (@lem1521662 y z)). Qed.
Lemma lem1521667 (x : real) (y : real) (z : real) : (term43 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521655 x y z) (@lem1521666 x y z)). Qed.
Lemma lem1521668 (x : real) (y : real) (z : real) : (term43 x z y) = (term37 x y z).
Proof. exact (TRANS (@lem1521654 x y z) (@lem1521667 x y z)). Qed.
Lemma lem1521669 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1521670 (x : real) (y : real) (z : real) : (term48 x z y) = (term49 x y z).
Proof. exact (MK_COMB (@lem1521669) (@lem1521668 x y z)). Qed.
Lemma lem1521671 (x : real) (y : real) (z : real) : (term49 x y z) = (term50 x y z).
Proof. exact (@lem1483512 (term37 x y z)). Qed.
Lemma lem1521672 (x : real) (y : real) (z : real) : (term50 x y z) = (term51 x y z).
Proof. exact (@lem1483508 x term47 (term46 y z)). Qed.
Lemma lem1521673 (y : real) (z : real) : (term52 y z) = (term53 y z).
Proof. exact (@lem1483508 (term38 y) term47 (term38 z)). Qed.
Lemma lem1521674 (z : real) : (term54 z) = (term55 z).
Proof. exact (@lem1483476 term47 term47 z). Qed.
Lemma lem1521676 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521677 : term58 = term59.
Proof. exact (@lem1521676 term60 term60). Qed.
Lemma lem1521678 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521679 : term62 = term60.
Proof. exact (EQ_MP (@lem1521678) (@lem940073)). Qed.
Lemma lem1521680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521681 : term59 = term63.
Proof. exact (MK_COMB (@lem1521680) (@lem1521679)). Qed.
Lemma lem1521682 : term58 = term63.
Proof. exact (TRANS (@lem1521677) (@lem1521681)). Qed.
Lemma lem1521683 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521684 : term64 = term65.
Proof. exact (MK_COMB (@lem1521683) (@lem1521682)). Qed.
Lemma lem1521685 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521686 (z : real) : (term55 z) = (term66 z).
Proof. exact (MK_COMB (@lem1521684) (@lem1521685 z)). Qed.
Lemma lem1521687 (z : real) : (term54 z) = (term66 z).
Proof. exact (TRANS (@lem1521674 z) (@lem1521686 z)). Qed.
Lemma lem1521688 (z : real) : (term66 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1521689 (z : real) : (term54 z) = z.
Proof. exact (TRANS (@lem1521687 z) (@lem1521688 z)). Qed.
Lemma lem1521690 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483476 term47 term47 y). Qed.
Lemma lem1521692 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521693 : term58 = term59.
Proof. exact (@lem1521692 term60 term60). Qed.
Lemma lem1521694 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521695 : term62 = term60.
Proof. exact (EQ_MP (@lem1521694) (@lem940073)). Qed.
Lemma lem1521696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521697 : term59 = term63.
Proof. exact (MK_COMB (@lem1521696) (@lem1521695)). Qed.
Lemma lem1521698 : term58 = term63.
Proof. exact (TRANS (@lem1521693) (@lem1521697)). Qed.
Lemma lem1521699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521700 : term64 = term65.
Proof. exact (MK_COMB (@lem1521699) (@lem1521698)). Qed.
Lemma lem1521701 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521702 (y : real) : (term55 y) = (term66 y).
Proof. exact (MK_COMB (@lem1521700) (@lem1521701 y)). Qed.
Lemma lem1521703 (y : real) : (term54 y) = (term66 y).
Proof. exact (TRANS (@lem1521690 y) (@lem1521702 y)). Qed.
Lemma lem1521704 (y : real) : (term66 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1521705 (y : real) : (term54 y) = y.
Proof. exact (TRANS (@lem1521703 y) (@lem1521704 y)). Qed.
Lemma lem1521706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521707 (y : real) : (term67 y) = (real_add y).
Proof. exact (MK_COMB (@lem1521706) (@lem1521705 y)). Qed.
Lemma lem1521708 (y : real) (z : real) : (term53 y z) = (real_add y z).
Proof. exact (MK_COMB (@lem1521707 y) (@lem1521689 z)). Qed.
Lemma lem1521709 (y : real) (z : real) : (term52 y z) = (real_add y z).
Proof. exact (TRANS (@lem1521673 y z) (@lem1521708 y z)). Qed.
Lemma lem1521712 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1521713 (x : real) (y : real) (z : real) : (term51 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1521712 x) (@lem1521709 y z)). Qed.
Lemma lem1521714 (x : real) (y : real) (z : real) : (term50 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521672 x y z) (@lem1521713 x y z)). Qed.
Lemma lem1521715 (x : real) (y : real) (z : real) : (term49 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521671 x y z) (@lem1521714 x y z)). Qed.
Lemma lem1521716 (x : real) (z : real) (y : real) : (term70 x z y) = (term70 x z y).
Proof. exact (eq_refl (term70 x z y)). Qed.
Lemma lem1521717 (x : real) (y : real) (z : real) : ((term48 x z y) = (term49 x y z)) = ((term48 x z y) = (term69 x y z)).
Proof. exact (MK_COMB (@lem1521716 x z y) (@lem1521715 x y z)). Qed.
Lemma lem1521718 (x : real) (y : real) (z : real) : (term48 x z y) = (term69 x y z).
Proof. exact (EQ_MP (@lem1521717 x y z) (@lem1521670 x y z)). Qed.
Lemma lem1521719 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521720 (x : real) (y : real) (z : real) : (term71 x z y) = (term72 x y z).
Proof. exact (MK_COMB (@lem1521719) (@lem1521718 x y z)). Qed.
Lemma lem1521721 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521722 (x : real) (y : real) (z : real) : (term73 x z y) = (term74 x y z).
Proof. exact (MK_COMB (@lem1521720 x y z) (@lem1521721)). Qed.
Lemma lem1521723 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521724 (x : real) (y : real) (z : real) : (term75 x z y) = (term76 x y z).
Proof. exact (MK_COMB (@lem1521723) (@lem1521668 x y z)). Qed.
Lemma lem1521725 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521726 (x : real) (y : real) (z : real) : (term77 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1521724 x y z) (@lem1521725)). Qed.
Lemma lem1521727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521728 (x : real) (y : real) (z : real) : (term79 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1521727) (@lem1521726 x y z)). Qed.
Lemma lem1521729 (x : real) (y : real) (z : real) : (term42 x z y) = (term81 x y z).
Proof. exact (MK_COMB (@lem1521728 x y z) (@lem1521722 x y z)). Qed.
Lemma lem1521730 (x : real) (y : real) (z : real) : (term41 x z y) = (term81 x y z).
Proof. exact (TRANS (@lem1521643 x z y) (@lem1521729 x y z)). Qed.
Lemma lem1521731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1521732 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (MK_COMB (@lem1521731) (@lem1521642 x y z)). Qed.
Lemma lem1521733 (x : real) (y : real) (z : real) : (term84 x z y) = (term85 x y z).
Proof. exact (MK_COMB (@lem1521732 x y z) (@lem1521730 x y z)). Qed.
Lemma lem1521734 (x : real) (y : real) (z : real) : (term86 x y z) = (term87 x y z).
Proof. exact (@lem1483554 (real_sub x y) z). Qed.
Lemma lem1521735 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521748 (x : real) (y : real) : (real_sub x y) = (term32 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1521749 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1521750 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1521749) (@lem1521748 x y)). Qed.
Lemma lem1521751 (x : real) (y : real) (z : real) : (term30 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem1521750 x y) (@lem1521735 z)). Qed.
Lemma lem1521752 (x : real) (y : real) (z : real) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem1483519 (term32 x y) z). Qed.
Lemma lem1521761 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (@lem1483482 x (term38 y) (term38 z)). Qed.
Lemma lem1521762 (x : real) (y : real) (z : real) : (term35 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521752 x y z) (@lem1521761 x y z)). Qed.
Lemma lem1521763 (x : real) (y : real) (z : real) : (term30 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521751 x y z) (@lem1521762 x y z)). Qed.
Lemma lem1521764 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1521765 (x : real) (y : real) (z : real) : (term88 x y z) = (term49 x y z).
Proof. exact (MK_COMB (@lem1521764) (@lem1521763 x y z)). Qed.
Lemma lem1521766 (x : real) (y : real) (z : real) : (term49 x y z) = (term50 x y z).
Proof. exact (@lem1483512 (term37 x y z)). Qed.
Lemma lem1521767 (x : real) (y : real) (z : real) : (term50 x y z) = (term51 x y z).
Proof. exact (@lem1483508 x term47 (term46 y z)). Qed.
Lemma lem1521768 (y : real) (z : real) : (term52 y z) = (term53 y z).
Proof. exact (@lem1483508 (term38 y) term47 (term38 z)). Qed.
Lemma lem1521769 (z : real) : (term54 z) = (term55 z).
Proof. exact (@lem1483476 term47 term47 z). Qed.
Lemma lem1521771 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521772 : term58 = term59.
Proof. exact (@lem1521771 term60 term60). Qed.
Lemma lem1521773 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521774 : term62 = term60.
Proof. exact (EQ_MP (@lem1521773) (@lem940073)). Qed.
Lemma lem1521775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521776 : term59 = term63.
Proof. exact (MK_COMB (@lem1521775) (@lem1521774)). Qed.
Lemma lem1521777 : term58 = term63.
Proof. exact (TRANS (@lem1521772) (@lem1521776)). Qed.
Lemma lem1521778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521779 : term64 = term65.
Proof. exact (MK_COMB (@lem1521778) (@lem1521777)). Qed.
Lemma lem1521780 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1521781 (z : real) : (term55 z) = (term66 z).
Proof. exact (MK_COMB (@lem1521779) (@lem1521780 z)). Qed.
Lemma lem1521782 (z : real) : (term54 z) = (term66 z).
Proof. exact (TRANS (@lem1521769 z) (@lem1521781 z)). Qed.
Lemma lem1521783 (z : real) : (term66 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1521784 (z : real) : (term54 z) = z.
Proof. exact (TRANS (@lem1521782 z) (@lem1521783 z)). Qed.
Lemma lem1521785 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483476 term47 term47 y). Qed.
Lemma lem1521787 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1521788 : term58 = term59.
Proof. exact (@lem1521787 term60 term60). Qed.
Lemma lem1521789 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1521790 : term62 = term60.
Proof. exact (EQ_MP (@lem1521789) (@lem940073)). Qed.
Lemma lem1521791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1521792 : term59 = term63.
Proof. exact (MK_COMB (@lem1521791) (@lem1521790)). Qed.
Lemma lem1521793 : term58 = term63.
Proof. exact (TRANS (@lem1521788) (@lem1521792)). Qed.
Lemma lem1521794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1521795 : term64 = term65.
Proof. exact (MK_COMB (@lem1521794) (@lem1521793)). Qed.
Lemma lem1521796 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1521797 (y : real) : (term55 y) = (term66 y).
Proof. exact (MK_COMB (@lem1521795) (@lem1521796 y)). Qed.
Lemma lem1521798 (y : real) : (term54 y) = (term66 y).
Proof. exact (TRANS (@lem1521785 y) (@lem1521797 y)). Qed.
Lemma lem1521799 (y : real) : (term66 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1521800 (y : real) : (term54 y) = y.
Proof. exact (TRANS (@lem1521798 y) (@lem1521799 y)). Qed.
Lemma lem1521801 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1521802 (y : real) : (term67 y) = (real_add y).
Proof. exact (MK_COMB (@lem1521801) (@lem1521800 y)). Qed.
Lemma lem1521803 (y : real) (z : real) : (term53 y z) = (real_add y z).
Proof. exact (MK_COMB (@lem1521802 y) (@lem1521784 z)). Qed.
Lemma lem1521804 (y : real) (z : real) : (term52 y z) = (real_add y z).
Proof. exact (TRANS (@lem1521768 y z) (@lem1521803 y z)). Qed.
Lemma lem1521807 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1521808 (x : real) (y : real) (z : real) : (term51 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1521807 x) (@lem1521804 y z)). Qed.
Lemma lem1521809 (x : real) (y : real) (z : real) : (term50 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521767 x y z) (@lem1521808 x y z)). Qed.
Lemma lem1521810 (x : real) (y : real) (z : real) : (term49 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1521766 x y z) (@lem1521809 x y z)). Qed.
Lemma lem1521811 (x : real) (y : real) (z : real) : (term89 x y z) = (term89 x y z).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1521812 (x : real) (y : real) (z : real) : ((term88 x y z) = (term49 x y z)) = ((term88 x y z) = (term69 x y z)).
Proof. exact (MK_COMB (@lem1521811 x y z) (@lem1521810 x y z)). Qed.
Lemma lem1521813 (x : real) (y : real) (z : real) : (term88 x y z) = (term69 x y z).
Proof. exact (EQ_MP (@lem1521812 x y z) (@lem1521765 x y z)). Qed.
Lemma lem1521814 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521815 (x : real) (y : real) (z : real) : (term90 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1521814) (@lem1521813 x y z)). Qed.
Lemma lem1521816 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521817 (x : real) (y : real) (z : real) : (term91 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1521815 x y z) (@lem1521816)). Qed.
Lemma lem1521818 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1521819 (x : real) (y : real) (z : real) : (term92 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1521818) (@lem1521763 x y z)). Qed.
Lemma lem1521820 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521821 (x : real) (y : real) (z : real) : (term93 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1521819 x y z) (@lem1521820)). Qed.
Lemma lem1521822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521823 (x : real) (y : real) (z : real) : (term94 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1521822) (@lem1521821 x y z)). Qed.
Lemma lem1521824 (x : real) (y : real) (z : real) : (term87 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1521823 x y z) (@lem1521817 x y z)). Qed.
Lemma lem1521825 (x : real) (y : real) (z : real) : (term86 x y z) = (term81 x y z).
Proof. exact (TRANS (@lem1521734 x y z) (@lem1521824 x y z)). Qed.
Lemma lem1521826 (x : real) (z : real) (y : real) : (x = (real_add z y)) = ((term43 x z y) = term31).
Proof. exact (@lem1483529 x (real_add z y)). Qed.
Lemma lem1521833 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1521836 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1521837 (x : real) (y : real) (z : real) : (term43 x z y) = (term43 x y z).
Proof. exact (MK_COMB (@lem1521836 x) (@lem1521833 y z)). Qed.
Lemma lem1521838 (x : real) (y : real) (z : real) : (term43 x y z) = (term44 x y z).
Proof. exact (@lem1483519 x (real_add y z)). Qed.
Lemma lem1521845 (y : real) (z : real) : (term45 y z) = (term46 y z).
Proof. exact (@lem1483508 y term47 z). Qed.
Lemma lem1521846 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1521849 (x : real) (y : real) (z : real) : (term44 x y z) = (term37 x y z).
Proof. exact (MK_COMB (@lem1521846 x) (@lem1521845 y z)). Qed.
Lemma lem1521850 (x : real) (y : real) (z : real) : (term43 x y z) = (term37 x y z).
Proof. exact (TRANS (@lem1521838 x y z) (@lem1521849 x y z)). Qed.
Lemma lem1521851 (x : real) (y : real) (z : real) : (term43 x z y) = (term37 x y z).
Proof. exact (TRANS (@lem1521837 x y z) (@lem1521850 x y z)). Qed.
Lemma lem1521852 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1521853 (x : real) (y : real) (z : real) : (term95 x z y) = (term40 x y z).
Proof. exact (MK_COMB (@lem1521852) (@lem1521851 x y z)). Qed.
Lemma lem1521854 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1521855 (x : real) (y : real) (z : real) : ((term43 x z y) = term31) = ((term37 x y z) = term31).
Proof. exact (MK_COMB (@lem1521853 x y z) (@lem1521854)). Qed.
Lemma lem1521856 (x : real) (y : real) (z : real) : (x = (real_add z y)) = ((term37 x y z) = term31).
Proof. exact (TRANS (@lem1521826 x z y) (@lem1521855 x y z)). Qed.
Lemma lem1521857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1521858 (x : real) (y : real) (z : real) : (term96 x y z) = (term97 x y z).
Proof. exact (MK_COMB (@lem1521857) (@lem1521825 x y z)). Qed.
Lemma lem1521859 (x : real) (y : real) (z : real) : (term98 x z y) = (term99 x y z).
Proof. exact (MK_COMB (@lem1521858 x y z) (@lem1521856 x y z)). Qed.
Lemma lem1521860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521861 (x : real) (y : real) (z : real) : (term100 x z y) = (term101 x y z).
Proof. exact (MK_COMB (@lem1521860) (@lem1521733 x y z)). Qed.
Lemma lem1521862 (x : real) (y : real) (z : real) : (term1 x z y) = (term102 x y z).
Proof. exact (MK_COMB (@lem1521861 x y z) (@lem1521859 x y z)). Qed.
Lemma lem1521863 (x : real) (y : real) : (term10 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1521862 x y z)). Qed.
Lemma lem1521864 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521865 (x : real) (y : real) : (term11 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1521864) (@lem1521863 x y)). Qed.
Lemma lem1521866 (x : real) : (term19 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1521865 x y)). Qed.
Lemma lem1521867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521868 (x : real) : (term20 x) = (term106 x).
Proof. exact (MK_COMB (@lem1521867) (@lem1521866 x)). Qed.
Lemma lem1521869 : term28 = term107.
Proof. exact (fun_ext (fun x : real => @lem1521868 x)). Qed.
Lemma lem1521870 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521871 : term29 = term108.
Proof. exact (MK_COMB (@lem1521870) (@lem1521869)). Qed.
Lemma lem1521872 : term21 = term108.
Proof. exact (TRANS (@lem1521607) (@lem1521871)). Qed.
Lemma lem1521882 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1521883 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1521882 real P Q). Qed.
Lemma lem1521884 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (@lem1521883 (term115 x y) (term116 x y)). Qed.
Lemma lem1521885 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1521886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521887 (x : real) (y : real) (z : real) : (term118 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1521886) (@lem1521885 x y z)). Qed.
Lemma lem1521888 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1521889 (x : real) (y : real) (z : real) : (term120 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1521887 x y z) (@lem1521888 x y z)). Qed.
Lemma lem1521890 (x : real) (y : real) : (term121 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1521889 x y z)). Qed.
Lemma lem1521891 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521892 (x : real) (y : real) : (term113 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1521891) (@lem1521890 x y)). Qed.
Lemma lem1521893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1521894 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1521893) (@lem1521892 x y)). Qed.
Lemma lem1521895 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1521896 (x : real) (y : real) : (term124 x y) = (term115 x y).
Proof. exact (fun_ext (fun z : real => @lem1521895 x y z)). Qed.
Lemma lem1521897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521898 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1521897) (@lem1521896 x y)). Qed.
Lemma lem1521899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1521900 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1521899) (@lem1521898 x y)). Qed.
Lemma lem1521901 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1521902 (x : real) (y : real) : (term129 x y) = (term116 x y).
Proof. exact (fun_ext (fun z : real => @lem1521901 x y z)). Qed.
Lemma lem1521903 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1521904 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1521903) (@lem1521902 x y)). Qed.
Lemma lem1521905 (x : real) (y : real) : (term114 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1521900 x y) (@lem1521904 x y)). Qed.
Lemma lem1521906 (x : real) (y : real) : ((term113 x y) = (term114 x y)) = ((term104 x y) = (term132 x y)).
Proof. exact (MK_COMB (@lem1521894 x y) (@lem1521905 x y)). Qed.
Lemma lem1521907 (x : real) (y : real) : (term104 x y) = (term132 x y).
Proof. exact (EQ_MP (@lem1521906 x y) (@lem1521884 x y)). Qed.
Lemma lem1522004 (x : real) : (term105 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1521907 x y)). Qed.
Lemma lem1522005 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522006 (x : real) : (term106 x) = (term134 x).
Proof. exact (MK_COMB (@lem1522005) (@lem1522004 x)). Qed.
Lemma lem1522008 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1522009 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1522008 real P Q). Qed.
Lemma lem1522010 (x : real) : (term135 x) = (term136 x).
Proof. exact (@lem1522009 (term137 x) (term138 x)). Qed.
Lemma lem1522011 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1522012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522013 (x : real) (y : real) : (term140 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1522012) (@lem1522011 x y)). Qed.
Lemma lem1522014 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1522015 (x : real) (y : real) : (term142 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1522013 x y) (@lem1522014 x y)). Qed.
Lemma lem1522016 (x : real) : (term143 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1522015 x y)). Qed.
Lemma lem1522017 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522018 (x : real) : (term135 x) = (term134 x).
Proof. exact (MK_COMB (@lem1522017) (@lem1522016 x)). Qed.
Lemma lem1522019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1522020 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1522019) (@lem1522018 x)). Qed.
Lemma lem1522021 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1522022 (x : real) : (term146 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1522021 x y)). Qed.
Lemma lem1522023 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522024 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1522023) (@lem1522022 x)). Qed.
Lemma lem1522025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522026 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1522025) (@lem1522024 x)). Qed.
Lemma lem1522027 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1522028 (x : real) : (term151 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1522027 x y)). Qed.
Lemma lem1522029 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522030 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1522029) (@lem1522028 x)). Qed.
Lemma lem1522031 (x : real) : (term136 x) = (term154 x).
Proof. exact (MK_COMB (@lem1522026 x) (@lem1522030 x)). Qed.
Lemma lem1522032 (x : real) : ((term135 x) = (term136 x)) = ((term134 x) = (term154 x)).
Proof. exact (MK_COMB (@lem1522020 x) (@lem1522031 x)). Qed.
Lemma lem1522033 (x : real) : (term134 x) = (term154 x).
Proof. exact (EQ_MP (@lem1522032 x) (@lem1522010 x)). Qed.
Lemma lem1522138 (x : real) : (term106 x) = (term154 x).
Proof. exact (TRANS (@lem1522006 x) (@lem1522033 x)). Qed.
Lemma lem1522139 : term107 = term155.
Proof. exact (fun_ext (fun x : real => @lem1522138 x)). Qed.
Lemma lem1522140 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522141 : term108 = term156.
Proof. exact (MK_COMB (@lem1522140) (@lem1522139)). Qed.
Lemma lem1522143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1522144 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1522143 real P Q). Qed.
Lemma lem1522145 : term157 = term158.
Proof. exact (@lem1522144 term159 term160). Qed.
Lemma lem1522146 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1522147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522148 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1522147) (@lem1522146 x)). Qed.
Lemma lem1522149 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1522150 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1522148 x) (@lem1522149 x)). Qed.
Lemma lem1522151 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1522150 x)). Qed.
Lemma lem1522152 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522153 : term157 = term156.
Proof. exact (MK_COMB (@lem1522152) (@lem1522151)). Qed.
Lemma lem1522154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1522155 : term166 = term167.
Proof. exact (MK_COMB (@lem1522154) (@lem1522153)). Qed.
Lemma lem1522156 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1522157 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1522156 x)). Qed.
Lemma lem1522158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522159 : term169 = term170.
Proof. exact (MK_COMB (@lem1522158) (@lem1522157)). Qed.
Lemma lem1522160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522161 : term171 = term172.
Proof. exact (MK_COMB (@lem1522160) (@lem1522159)). Qed.
Lemma lem1522162 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1522163 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1522162 x)). Qed.
Lemma lem1522164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522165 : term174 = term175.
Proof. exact (MK_COMB (@lem1522164) (@lem1522163)). Qed.
Lemma lem1522166 : term158 = term176.
Proof. exact (MK_COMB (@lem1522161) (@lem1522165)). Qed.
Lemma lem1522167 : (term157 = term158) = (term156 = term176).
Proof. exact (MK_COMB (@lem1522155) (@lem1522166)). Qed.
Lemma lem1522168 : term156 = term176.
Proof. exact (EQ_MP (@lem1522167) (@lem1522145)). Qed.
Lemma lem1522281 : term108 = term176.
Proof. exact (TRANS (@lem1522141) (@lem1522168)). Qed.
Lemma lem1522283 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1522284 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1522283 real P Q). Qed.
Lemma lem1522285 : term158 = term157.
Proof. exact (@lem1522284 term159 term160). Qed.
Lemma lem1522286 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1522287 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1522286 x)). Qed.
Lemma lem1522288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522289 : term169 = term170.
Proof. exact (MK_COMB (@lem1522288) (@lem1522287)). Qed.
Lemma lem1522290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522291 : term171 = term172.
Proof. exact (MK_COMB (@lem1522290) (@lem1522289)). Qed.
Lemma lem1522292 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1522293 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1522292 x)). Qed.
Lemma lem1522294 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522295 : term174 = term175.
Proof. exact (MK_COMB (@lem1522294) (@lem1522293)). Qed.
Lemma lem1522296 : term158 = term176.
Proof. exact (MK_COMB (@lem1522291) (@lem1522295)). Qed.
Lemma lem1522297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1522298 : term177 = term178.
Proof. exact (MK_COMB (@lem1522297) (@lem1522296)). Qed.
Lemma lem1522299 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1522300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522301 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1522300) (@lem1522299 x)). Qed.
Lemma lem1522302 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1522303 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1522301 x) (@lem1522302 x)). Qed.
Lemma lem1522304 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1522303 x)). Qed.
Lemma lem1522305 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522306 : term157 = term156.
Proof. exact (MK_COMB (@lem1522305) (@lem1522304)). Qed.
Lemma lem1522307 : (term158 = term157) = (term176 = term156).
Proof. exact (MK_COMB (@lem1522298) (@lem1522306)). Qed.
Lemma lem1522308 : term176 = term156.
Proof. exact (EQ_MP (@lem1522307) (@lem1522285)). Qed.
Lemma lem1522310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1522311 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1522310 real P Q). Qed.
Lemma lem1522312 (x : real) : (term136 x) = (term135 x).
Proof. exact (@lem1522311 (term137 x) (term138 x)). Qed.
Lemma lem1522313 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1522314 (x : real) : (term146 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1522313 x y)). Qed.
Lemma lem1522315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522316 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1522315) (@lem1522314 x)). Qed.
Lemma lem1522317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522318 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1522317) (@lem1522316 x)). Qed.
Lemma lem1522319 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1522320 (x : real) : (term151 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem1522319 x y)). Qed.
Lemma lem1522321 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522322 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1522321) (@lem1522320 x)). Qed.
Lemma lem1522323 (x : real) : (term136 x) = (term154 x).
Proof. exact (MK_COMB (@lem1522318 x) (@lem1522322 x)). Qed.
Lemma lem1522324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1522325 (x : real) : (term179 x) = (term180 x).
Proof. exact (MK_COMB (@lem1522324) (@lem1522323 x)). Qed.
Lemma lem1522326 (x : real) (y : real) : (term139 x y) = (term126 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1522327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522328 (x : real) (y : real) : (term140 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1522327) (@lem1522326 x y)). Qed.
Lemma lem1522329 (x : real) (y : real) : (term141 x y) = (term131 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1522330 (x : real) (y : real) : (term142 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1522328 x y) (@lem1522329 x y)). Qed.
Lemma lem1522331 (x : real) : (term143 x) = (term133 x).
Proof. exact (fun_ext (fun y : real => @lem1522330 x y)). Qed.
Lemma lem1522332 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522333 (x : real) : (term135 x) = (term134 x).
Proof. exact (MK_COMB (@lem1522332) (@lem1522331 x)). Qed.
Lemma lem1522334 (x : real) : ((term136 x) = (term135 x)) = ((term154 x) = (term134 x)).
Proof. exact (MK_COMB (@lem1522325 x) (@lem1522333 x)). Qed.
Lemma lem1522335 (x : real) : (term154 x) = (term134 x).
Proof. exact (EQ_MP (@lem1522334 x) (@lem1522312 x)). Qed.
Lemma lem1522337 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1522338 (P : real -> Prop) (Q : real -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem1522337 real P Q). Qed.
Lemma lem1522339 (x : real) (y : real) : (term114 x y) = (term113 x y).
Proof. exact (@lem1522338 (term115 x y) (term116 x y)). Qed.
Lemma lem1522340 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1522341 (x : real) (y : real) : (term124 x y) = (term115 x y).
Proof. exact (fun_ext (fun z : real => @lem1522340 x y z)). Qed.
Lemma lem1522342 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522343 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1522342) (@lem1522341 x y)). Qed.
Lemma lem1522344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522345 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1522344) (@lem1522343 x y)). Qed.
Lemma lem1522346 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1522347 (x : real) (y : real) : (term129 x y) = (term116 x y).
Proof. exact (fun_ext (fun z : real => @lem1522346 x y z)). Qed.
Lemma lem1522348 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522349 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1522348) (@lem1522347 x y)). Qed.
Lemma lem1522350 (x : real) (y : real) : (term114 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1522345 x y) (@lem1522349 x y)). Qed.
Lemma lem1522351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1522352 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1522351) (@lem1522350 x y)). Qed.
Lemma lem1522353 (x : real) (y : real) (z : real) : (term117 x y z) = (term85 x y z).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem1522354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522355 (x : real) (y : real) (z : real) : (term118 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1522354) (@lem1522353 x y z)). Qed.
Lemma lem1522356 (x : real) (y : real) (z : real) : (term119 x y z) = (term99 x y z).
Proof. exact (eq_refl (term119 x y z)). Qed.
Lemma lem1522357 (x : real) (y : real) (z : real) : (term120 x y z) = (term102 x y z).
Proof. exact (MK_COMB (@lem1522355 x y z) (@lem1522356 x y z)). Qed.
Lemma lem1522358 (x : real) (y : real) : (term121 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1522357 x y z)). Qed.
Lemma lem1522359 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522360 (x : real) (y : real) : (term113 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1522359) (@lem1522358 x y)). Qed.
Lemma lem1522361 (x : real) (y : real) : ((term114 x y) = (term113 x y)) = ((term132 x y) = (term104 x y)).
Proof. exact (MK_COMB (@lem1522352 x y) (@lem1522360 x y)). Qed.
Lemma lem1522362 (x : real) (y : real) : (term132 x y) = (term104 x y).
Proof. exact (EQ_MP (@lem1522361 x y) (@lem1522339 x y)). Qed.
Lemma lem1522363 (x : real) : (term133 x) = (term105 x).
Proof. exact (fun_ext (fun y : real => @lem1522362 x y)). Qed.
Lemma lem1522364 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522365 (x : real) : (term134 x) = (term106 x).
Proof. exact (MK_COMB (@lem1522364) (@lem1522363 x)). Qed.
Lemma lem1522366 (x : real) : (term154 x) = (term106 x).
Proof. exact (TRANS (@lem1522335 x) (@lem1522365 x)). Qed.
Lemma lem1522367 : term155 = term107.
Proof. exact (fun_ext (fun x : real => @lem1522366 x)). Qed.
Lemma lem1522368 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522369 : term156 = term108.
Proof. exact (MK_COMB (@lem1522368) (@lem1522367)). Qed.
Lemma lem1522370 : term176 = term108.
Proof. exact (TRANS (@lem1522308) (@lem1522369)). Qed.
Lemma lem1522371 : term108 = term108.
Proof. exact (TRANS (@lem1522281) (@lem1522370)). Qed.
Lemma lem1522374 : term21 = term108.
Proof. exact (TRANS (@lem1521872) (@lem1522371)). Qed.
Lemma lem1522391 (x : real) (y : real) (z : real) : (term99 x y z) = (term183 x y z).
Proof. exact (@lem19367 (term78 x y z) (term74 x y z) ((term37 x y z) = term31)). Qed.
Lemma lem1522408 (x : real) (y : real) (z : real) : (term85 x y z) = (term184 x y z).
Proof. exact (@lem19158 (term78 x y z) ((term37 x y z) = term31) (term74 x y z)). Qed.
Lemma lem1522409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1522410 (x : real) (y : real) (z : real) : (term101 x y z) = (term185 x y z).
Proof. exact (MK_COMB (@lem1522409) (@lem1522408 x y z)). Qed.
Lemma lem1522411 (x : real) (y : real) (z : real) : (term102 x y z) = (term186 x y z).
Proof. exact (MK_COMB (@lem1522410 x y z) (@lem1522391 x y z)). Qed.
Lemma lem1522412 (x : real) (y : real) : (term103 x y) = (term187 x y).
Proof. exact (fun_ext (fun z : real => @lem1522411 x y z)). Qed.
Lemma lem1522413 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522414 (x : real) (y : real) : (term104 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1522413) (@lem1522412 x y)). Qed.
Lemma lem1522415 (x : real) : (term105 x) = (term189 x).
Proof. exact (fun_ext (fun y : real => @lem1522414 x y)). Qed.
Lemma lem1522416 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522417 (x : real) : (term106 x) = (term190 x).
Proof. exact (MK_COMB (@lem1522416) (@lem1522415 x)). Qed.
Lemma lem1522418 : term107 = term191.
Proof. exact (fun_ext (fun x : real => @lem1522417 x)). Qed.
Lemma lem1522419 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522420 : term108 = term192.
Proof. exact (MK_COMB (@lem1522419) (@lem1522418)). Qed.
Lemma lem1522421 : term21 = term192.
Proof. exact (TRANS (@lem1522374) (@lem1522420)). Qed.
Lemma lem1522443 (x : real) (y : real) (z : real) (h1 : term186 x y z) : term186 x y z.
Proof. exact (h1). Qed.
Lemma lem1522444 (x : real) (y : real) (z : real) (h1 : term184 x y z) : term184 x y z.
Proof. exact (h1). Qed.
Lemma lem1522445 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term193 x y z.
Proof. exact (h1). Qed.
Lemma lem1522446 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term78 x y z.
Proof. exact (proj2 (@lem1522445 x y z h1)). Qed.
Lemma lem1522447 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term37 x y z) = term31.
Proof. exact (proj1 (@lem1522445 x y z h1)). Qed.
Lemma lem1522449 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522450 : term195 = term196.
Proof. exact (@lem1522449 (NUMERAL 0) term60). Qed.
Lemma lem1522451 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1522452 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1522453 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1522452 h1) (fun h1 : term196 = True => @lem1522451)). Qed.
Lemma lem1522454 : term196 = True.
Proof. exact (EQ_MP (@lem1522453) (@lem1522451)). Qed.
Lemma lem1522455 : term195 = True.
Proof. exact (TRANS (@lem1522450) (@lem1522454)). Qed.
Lemma lem1522456 : True = term195.
Proof. exact (SYM (@lem1522455)). Qed.
Lemma lem1522457 : term195.
Proof. exact (EQ_MP (@lem1522456) (@lem0)). Qed.
Lemma lem1522458 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term198 x y z.
Proof. exact (conj (@lem1522457) (@lem1522446 x y z h1)). Qed.
Lemma lem1522460 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1522461 (x : real) (y : real) (z : real) : term200 x y z.
Proof. exact (@lem1522460 term63 (term37 x y z)). Qed.
Lemma lem1522462 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term201 x y z.
Proof. exact (@lem1522461 x y z (@lem1522458 x y z h1)). Qed.
Lemma lem1522463 (x : real) (y : real) (z : real) : (term202 x y z) = (term37 x y z).
Proof. exact (@lem1483460 (term37 x y z)). Qed.
Lemma lem1522464 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522465 (x : real) (y : real) (z : real) : (term203 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1522464) (@lem1522463 x y z)). Qed.
Lemma lem1522466 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522467 (x : real) (y : real) (z : real) : (term201 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1522465 x y z) (@lem1522466)). Qed.
Lemma lem1522468 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term78 x y z.
Proof. exact (EQ_MP (@lem1522467 x y z) (@lem1522462 x y z h1)). Qed.
Lemma lem1522470 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1522471 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1522470 (term37 x y z)). Qed.
Lemma lem1522472 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term206 x y z.
Proof. exact (@lem1522471 x y z (@lem1522447 x y z h1)). Qed.
Lemma lem1522473 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term207 x y z.
Proof. exact (@lem1522472 x y z h1 term47). Qed.
Lemma lem1522474 (x : real) (y : real) (z : real) : (term207 x y z) = ((term50 x y z) = term31).
Proof. exact (eq_refl (term207 x y z)). Qed.
Lemma lem1522475 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term50 x y z) = term31.
Proof. exact (EQ_MP (@lem1522474 x y z) (@lem1522473 x y z h1)). Qed.
Lemma lem1522476 (x : real) (y : real) (z : real) : (term50 x y z) = (term51 x y z).
Proof. exact (@lem1483508 x term47 (term46 y z)). Qed.
Lemma lem1522477 (y : real) (z : real) : (term52 y z) = (term53 y z).
Proof. exact (@lem1483508 (term38 y) term47 (term38 z)). Qed.
Lemma lem1522478 (z : real) : (term54 z) = (term55 z).
Proof. exact (@lem1483476 term47 term47 z). Qed.
Lemma lem1522480 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1522481 : term58 = term59.
Proof. exact (@lem1522480 term60 term60). Qed.
Lemma lem1522482 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1522483 : term62 = term60.
Proof. exact (EQ_MP (@lem1522482) (@lem940073)). Qed.
Lemma lem1522484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1522485 : term59 = term63.
Proof. exact (MK_COMB (@lem1522484) (@lem1522483)). Qed.
Lemma lem1522486 : term58 = term63.
Proof. exact (TRANS (@lem1522481) (@lem1522485)). Qed.
Lemma lem1522487 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522488 : term64 = term65.
Proof. exact (MK_COMB (@lem1522487) (@lem1522486)). Qed.
Lemma lem1522489 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522490 (z : real) : (term55 z) = (term66 z).
Proof. exact (MK_COMB (@lem1522488) (@lem1522489 z)). Qed.
Lemma lem1522491 (z : real) : (term54 z) = (term66 z).
Proof. exact (TRANS (@lem1522478 z) (@lem1522490 z)). Qed.
Lemma lem1522492 (z : real) : (term66 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1522493 (z : real) : (term54 z) = z.
Proof. exact (TRANS (@lem1522491 z) (@lem1522492 z)). Qed.
Lemma lem1522494 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483476 term47 term47 y). Qed.
Lemma lem1522496 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1522497 : term58 = term59.
Proof. exact (@lem1522496 term60 term60). Qed.
Lemma lem1522498 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1522499 : term62 = term60.
Proof. exact (EQ_MP (@lem1522498) (@lem940073)). Qed.
Lemma lem1522500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1522501 : term59 = term63.
Proof. exact (MK_COMB (@lem1522500) (@lem1522499)). Qed.
Lemma lem1522502 : term58 = term63.
Proof. exact (TRANS (@lem1522497) (@lem1522501)). Qed.
Lemma lem1522503 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522504 : term64 = term65.
Proof. exact (MK_COMB (@lem1522503) (@lem1522502)). Qed.
Lemma lem1522505 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522506 (y : real) : (term55 y) = (term66 y).
Proof. exact (MK_COMB (@lem1522504) (@lem1522505 y)). Qed.
Lemma lem1522507 (y : real) : (term54 y) = (term66 y).
Proof. exact (TRANS (@lem1522494 y) (@lem1522506 y)). Qed.
Lemma lem1522508 (y : real) : (term66 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1522509 (y : real) : (term54 y) = y.
Proof. exact (TRANS (@lem1522507 y) (@lem1522508 y)). Qed.
Lemma lem1522510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522511 (y : real) : (term67 y) = (real_add y).
Proof. exact (MK_COMB (@lem1522510) (@lem1522509 y)). Qed.
Lemma lem1522512 (y : real) (z : real) : (term53 y z) = (real_add y z).
Proof. exact (MK_COMB (@lem1522511 y) (@lem1522493 z)). Qed.
Lemma lem1522513 (y : real) (z : real) : (term52 y z) = (real_add y z).
Proof. exact (TRANS (@lem1522477 y z) (@lem1522512 y z)). Qed.
Lemma lem1522516 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1522517 (x : real) (y : real) (z : real) : (term51 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1522516 x) (@lem1522513 y z)). Qed.
Lemma lem1522518 (x : real) (y : real) (z : real) : (term50 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1522476 x y z) (@lem1522517 x y z)). Qed.
Lemma lem1522519 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1522520 (x : real) (y : real) (z : real) : (term208 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1522519) (@lem1522518 x y z)). Qed.
Lemma lem1522521 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522522 (x : real) (y : real) (z : real) : ((term50 x y z) = term31) = ((term69 x y z) = term31).
Proof. exact (MK_COMB (@lem1522520 x y z) (@lem1522521)). Qed.
Lemma lem1522523 (x : real) (y : real) (z : real) (h1 : term193 x y z) : (term69 x y z) = term31.
Proof. exact (EQ_MP (@lem1522522 x y z) (@lem1522475 x y z h1)). Qed.
Lemma lem1522524 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term210 x y z.
Proof. exact (conj (@lem1522523 x y z h1) (@lem1522468 x y z h1)). Qed.
Lemma lem1522526 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1522527 (x : real) (y : real) (z : real) : term212 x y z.
Proof. exact (@lem1522526 (term69 x y z) (term37 x y z)). Qed.
Lemma lem1522528 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term213 x y z.
Proof. exact (@lem1522527 x y z (@lem1522524 x y z h1)). Qed.
Lemma lem1522529 (x : real) (y : real) (z : real) : (term214 x y z) = (term215 x y z).
Proof. exact (@lem1483480 (term38 x) x (real_add y z) (term46 y z)). Qed.
Lemma lem1522530 (x : real) : (term216 x) = (term217 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1522532 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522533 : term219 = term31.
Proof. exact (@lem1522532 term60). Qed.
Lemma lem1522534 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522535 : term220 = term221.
Proof. exact (MK_COMB (@lem1522534) (@lem1522533)). Qed.
Lemma lem1522536 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1522537 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1522535) (@lem1522536 x)). Qed.
Lemma lem1522538 (x : real) : (term216 x) = (term222 x).
Proof. exact (TRANS (@lem1522530 x) (@lem1522537 x)). Qed.
Lemma lem1522539 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1522540 (x : real) : (term216 x) = term31.
Proof. exact (TRANS (@lem1522538 x) (@lem1522539 x)). Qed.
Lemma lem1522541 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522542 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1522541) (@lem1522540 x)). Qed.
Lemma lem1522543 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (@lem1483480 y (term38 y) z (term38 z)). Qed.
Lemma lem1522544 (y : real) : (term227 y) = (term217 y).
Proof. exact (@lem1483442 term47 y). Qed.
Lemma lem1522546 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522547 : term219 = term31.
Proof. exact (@lem1522546 term60). Qed.
Lemma lem1522548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522549 : term220 = term221.
Proof. exact (MK_COMB (@lem1522548) (@lem1522547)). Qed.
Lemma lem1522550 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522551 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1522549) (@lem1522550 y)). Qed.
Lemma lem1522552 (y : real) : (term227 y) = (term222 y).
Proof. exact (TRANS (@lem1522544 y) (@lem1522551 y)). Qed.
Lemma lem1522553 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1522554 (y : real) : (term227 y) = term31.
Proof. exact (TRANS (@lem1522552 y) (@lem1522553 y)). Qed.
Lemma lem1522555 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522556 (y : real) : (term228 y) = term224.
Proof. exact (MK_COMB (@lem1522555) (@lem1522554 y)). Qed.
Lemma lem1522557 (z : real) : (term227 z) = (term217 z).
Proof. exact (@lem1483442 term47 z). Qed.
Lemma lem1522559 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522560 : term219 = term31.
Proof. exact (@lem1522559 term60). Qed.
Lemma lem1522561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522562 : term220 = term221.
Proof. exact (MK_COMB (@lem1522561) (@lem1522560)). Qed.
Lemma lem1522563 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522564 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1522562) (@lem1522563 z)). Qed.
Lemma lem1522565 (z : real) : (term227 z) = (term222 z).
Proof. exact (TRANS (@lem1522557 z) (@lem1522564 z)). Qed.
Lemma lem1522566 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1522567 (z : real) : (term227 z) = term31.
Proof. exact (TRANS (@lem1522565 z) (@lem1522566 z)). Qed.
Lemma lem1522568 (y : real) (z : real) : (term226 y z) = term229.
Proof. exact (MK_COMB (@lem1522556 y) (@lem1522567 z)). Qed.
Lemma lem1522569 (y : real) (z : real) : (term225 y z) = term229.
Proof. exact (TRANS (@lem1522543 y z) (@lem1522568 y z)). Qed.
Lemma lem1522570 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522571 (y : real) (z : real) : (term225 y z) = term31.
Proof. exact (TRANS (@lem1522569 y z) (@lem1522570)). Qed.
Lemma lem1522572 (x : real) (y : real) (z : real) : (term215 x y z) = term229.
Proof. exact (MK_COMB (@lem1522542 x) (@lem1522571 y z)). Qed.
Lemma lem1522573 (x : real) (y : real) (z : real) : (term214 x y z) = term229.
Proof. exact (TRANS (@lem1522529 x y z) (@lem1522572 x y z)). Qed.
Lemma lem1522574 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522575 (x : real) (y : real) (z : real) : (term214 x y z) = term31.
Proof. exact (TRANS (@lem1522573 x y z) (@lem1522574)). Qed.
Lemma lem1522576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522577 (x : real) (y : real) (z : real) : (term230 x y z) = term231.
Proof. exact (MK_COMB (@lem1522576) (@lem1522575 x y z)). Qed.
Lemma lem1522578 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522579 (x : real) (y : real) (z : real) : (term213 x y z) = term232.
Proof. exact (MK_COMB (@lem1522577 x y z) (@lem1522578)). Qed.
Lemma lem1522580 (x : real) (y : real) (z : real) (h1 : term193 x y z) : term232.
Proof. exact (EQ_MP (@lem1522579 x y z) (@lem1522528 x y z h1)). Qed.
Lemma lem1522582 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522583 : term232 = term233.
Proof. exact (@lem1522582 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1522584 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1522585 : term232 = False.
Proof. exact (TRANS (@lem1522583) (@lem1522584)). Qed.
Lemma lem1522586 (x : real) (y : real) (z : real) (h1 : term193 x y z) : False.
Proof. exact (EQ_MP (@lem1522585) (@lem1522580 x y z h1)). Qed.
Lemma lem1522587 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term234 x y z.
Proof. exact (h1). Qed.
Lemma lem1522588 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term74 x y z.
Proof. exact (proj2 (@lem1522587 x y z h1)). Qed.
Lemma lem1522589 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term37 x y z) = term31.
Proof. exact (proj1 (@lem1522587 x y z h1)). Qed.
Lemma lem1522591 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522592 : term195 = term196.
Proof. exact (@lem1522591 (NUMERAL 0) term60). Qed.
Lemma lem1522593 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1522594 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1522595 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1522594 h1) (fun h1 : term196 = True => @lem1522593)). Qed.
Lemma lem1522596 : term196 = True.
Proof. exact (EQ_MP (@lem1522595) (@lem1522593)). Qed.
Lemma lem1522597 : term195 = True.
Proof. exact (TRANS (@lem1522592) (@lem1522596)). Qed.
Lemma lem1522598 : True = term195.
Proof. exact (SYM (@lem1522597)). Qed.
Lemma lem1522599 : term195.
Proof. exact (EQ_MP (@lem1522598) (@lem0)). Qed.
Lemma lem1522600 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term235 x y z.
Proof. exact (conj (@lem1522599) (@lem1522588 x y z h1)). Qed.
Lemma lem1522602 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1522603 (x : real) (y : real) (z : real) : term236 x y z.
Proof. exact (@lem1522602 term63 (term69 x y z)). Qed.
Lemma lem1522604 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term237 x y z.
Proof. exact (@lem1522603 x y z (@lem1522600 x y z h1)). Qed.
Lemma lem1522605 (x : real) (y : real) (z : real) : (term238 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1522606 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522607 (x : real) (y : real) (z : real) : (term239 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1522606) (@lem1522605 x y z)). Qed.
Lemma lem1522608 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522609 (x : real) (y : real) (z : real) : (term237 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1522607 x y z) (@lem1522608)). Qed.
Lemma lem1522610 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term74 x y z.
Proof. exact (EQ_MP (@lem1522609 x y z) (@lem1522604 x y z h1)). Qed.
Lemma lem1522612 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1522613 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1522612 (term37 x y z)). Qed.
Lemma lem1522614 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term206 x y z.
Proof. exact (@lem1522613 x y z (@lem1522589 x y z h1)). Qed.
Lemma lem1522615 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term240 x y z.
Proof. exact (@lem1522614 x y z h1 term63). Qed.
Lemma lem1522616 (x : real) (y : real) (z : real) : (term240 x y z) = ((term202 x y z) = term31).
Proof. exact (eq_refl (term240 x y z)). Qed.
Lemma lem1522617 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term202 x y z) = term31.
Proof. exact (EQ_MP (@lem1522616 x y z) (@lem1522615 x y z h1)). Qed.
Lemma lem1522618 (x : real) (y : real) (z : real) : (term202 x y z) = (term37 x y z).
Proof. exact (@lem1483460 (term37 x y z)). Qed.
Lemma lem1522619 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1522620 (x : real) (y : real) (z : real) : (term241 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1522619) (@lem1522618 x y z)). Qed.
Lemma lem1522621 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522622 (x : real) (y : real) (z : real) : ((term202 x y z) = term31) = ((term37 x y z) = term31).
Proof. exact (MK_COMB (@lem1522620 x y z) (@lem1522621)). Qed.
Lemma lem1522623 (x : real) (y : real) (z : real) (h1 : term234 x y z) : (term37 x y z) = term31.
Proof. exact (EQ_MP (@lem1522622 x y z) (@lem1522617 x y z h1)). Qed.
Lemma lem1522624 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term234 x y z.
Proof. exact (conj (@lem1522623 x y z h1) (@lem1522610 x y z h1)). Qed.
Lemma lem1522626 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1522627 (x : real) (y : real) (z : real) : term242 x y z.
Proof. exact (@lem1522626 (term37 x y z) (term69 x y z)). Qed.
Lemma lem1522628 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term243 x y z.
Proof. exact (@lem1522627 x y z (@lem1522624 x y z h1)). Qed.
Lemma lem1522629 (x : real) (y : real) (z : real) : (term244 x y z) = (term245 x y z).
Proof. exact (@lem1483480 x (term38 x) (term46 y z) (real_add y z)). Qed.
Lemma lem1522630 (x : real) : (term227 x) = (term217 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1522632 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522633 : term219 = term31.
Proof. exact (@lem1522632 term60). Qed.
Lemma lem1522634 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522635 : term220 = term221.
Proof. exact (MK_COMB (@lem1522634) (@lem1522633)). Qed.
Lemma lem1522636 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1522637 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1522635) (@lem1522636 x)). Qed.
Lemma lem1522638 (x : real) : (term227 x) = (term222 x).
Proof. exact (TRANS (@lem1522630 x) (@lem1522637 x)). Qed.
Lemma lem1522639 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1522640 (x : real) : (term227 x) = term31.
Proof. exact (TRANS (@lem1522638 x) (@lem1522639 x)). Qed.
Lemma lem1522641 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522642 (x : real) : (term228 x) = term224.
Proof. exact (MK_COMB (@lem1522641) (@lem1522640 x)). Qed.
Lemma lem1522643 (y : real) (z : real) : (term246 y z) = (term247 y z).
Proof. exact (@lem1483480 (term38 y) y (term38 z) z). Qed.
Lemma lem1522644 (y : real) : (term216 y) = (term217 y).
Proof. exact (@lem1483440 term47 y). Qed.
Lemma lem1522646 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522647 : term219 = term31.
Proof. exact (@lem1522646 term60). Qed.
Lemma lem1522648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522649 : term220 = term221.
Proof. exact (MK_COMB (@lem1522648) (@lem1522647)). Qed.
Lemma lem1522650 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522651 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1522649) (@lem1522650 y)). Qed.
Lemma lem1522652 (y : real) : (term216 y) = (term222 y).
Proof. exact (TRANS (@lem1522644 y) (@lem1522651 y)). Qed.
Lemma lem1522653 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1522654 (y : real) : (term216 y) = term31.
Proof. exact (TRANS (@lem1522652 y) (@lem1522653 y)). Qed.
Lemma lem1522655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522656 (y : real) : (term223 y) = term224.
Proof. exact (MK_COMB (@lem1522655) (@lem1522654 y)). Qed.
Lemma lem1522657 (z : real) : (term216 z) = (term217 z).
Proof. exact (@lem1483440 term47 z). Qed.
Lemma lem1522659 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522660 : term219 = term31.
Proof. exact (@lem1522659 term60). Qed.
Lemma lem1522661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522662 : term220 = term221.
Proof. exact (MK_COMB (@lem1522661) (@lem1522660)). Qed.
Lemma lem1522663 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522664 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1522662) (@lem1522663 z)). Qed.
Lemma lem1522665 (z : real) : (term216 z) = (term222 z).
Proof. exact (TRANS (@lem1522657 z) (@lem1522664 z)). Qed.
Lemma lem1522666 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1522667 (z : real) : (term216 z) = term31.
Proof. exact (TRANS (@lem1522665 z) (@lem1522666 z)). Qed.
Lemma lem1522668 (y : real) (z : real) : (term247 y z) = term229.
Proof. exact (MK_COMB (@lem1522656 y) (@lem1522667 z)). Qed.
Lemma lem1522669 (y : real) (z : real) : (term246 y z) = term229.
Proof. exact (TRANS (@lem1522643 y z) (@lem1522668 y z)). Qed.
Lemma lem1522670 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522671 (y : real) (z : real) : (term246 y z) = term31.
Proof. exact (TRANS (@lem1522669 y z) (@lem1522670)). Qed.
Lemma lem1522672 (x : real) (y : real) (z : real) : (term245 x y z) = term229.
Proof. exact (MK_COMB (@lem1522642 x) (@lem1522671 y z)). Qed.
Lemma lem1522673 (x : real) (y : real) (z : real) : (term244 x y z) = term229.
Proof. exact (TRANS (@lem1522629 x y z) (@lem1522672 x y z)). Qed.
Lemma lem1522674 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522675 (x : real) (y : real) (z : real) : (term244 x y z) = term31.
Proof. exact (TRANS (@lem1522673 x y z) (@lem1522674)). Qed.
Lemma lem1522676 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522677 (x : real) (y : real) (z : real) : (term248 x y z) = term231.
Proof. exact (MK_COMB (@lem1522676) (@lem1522675 x y z)). Qed.
Lemma lem1522678 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522679 (x : real) (y : real) (z : real) : (term243 x y z) = term232.
Proof. exact (MK_COMB (@lem1522677 x y z) (@lem1522678)). Qed.
Lemma lem1522680 (x : real) (y : real) (z : real) (h1 : term234 x y z) : term232.
Proof. exact (EQ_MP (@lem1522679 x y z) (@lem1522628 x y z h1)). Qed.
Lemma lem1522682 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522683 : term232 = term233.
Proof. exact (@lem1522682 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1522684 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1522685 : term232 = False.
Proof. exact (TRANS (@lem1522683) (@lem1522684)). Qed.
Lemma lem1522686 (x : real) (y : real) (z : real) (h1 : term234 x y z) : False.
Proof. exact (EQ_MP (@lem1522685) (@lem1522680 x y z h1)). Qed.
Lemma lem1522687 (x : real) (y : real) (z : real) (h1 : term184 x y z) : False.
Proof. exact (or_elim (@lem1522444 x y z h1) (fun h0 : term193 x y z => @lem1522586 x y z h0) (fun h0 : term234 x y z => @lem1522686 x y z h0)). Qed.
Lemma lem1522688 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1522689 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term249 x y z.
Proof. exact (h1). Qed.
Lemma lem1522690 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term37 x y z) = term31.
Proof. exact (proj2 (@lem1522689 x y z h1)). Qed.
Lemma lem1522691 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term78 x y z.
Proof. exact (proj1 (@lem1522689 x y z h1)). Qed.
Lemma lem1522693 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522694 : term195 = term196.
Proof. exact (@lem1522693 (NUMERAL 0) term60). Qed.
Lemma lem1522695 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1522696 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1522697 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1522696 h1) (fun h1 : term196 = True => @lem1522695)). Qed.
Lemma lem1522698 : term196 = True.
Proof. exact (EQ_MP (@lem1522697) (@lem1522695)). Qed.
Lemma lem1522699 : term195 = True.
Proof. exact (TRANS (@lem1522694) (@lem1522698)). Qed.
Lemma lem1522700 : True = term195.
Proof. exact (SYM (@lem1522699)). Qed.
Lemma lem1522701 : term195.
Proof. exact (EQ_MP (@lem1522700) (@lem0)). Qed.
Lemma lem1522702 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term198 x y z.
Proof. exact (conj (@lem1522701) (@lem1522691 x y z h1)). Qed.
Lemma lem1522704 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1522705 (x : real) (y : real) (z : real) : term200 x y z.
Proof. exact (@lem1522704 term63 (term37 x y z)). Qed.
Lemma lem1522706 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term201 x y z.
Proof. exact (@lem1522705 x y z (@lem1522702 x y z h1)). Qed.
Lemma lem1522707 (x : real) (y : real) (z : real) : (term202 x y z) = (term37 x y z).
Proof. exact (@lem1483460 (term37 x y z)). Qed.
Lemma lem1522708 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522709 (x : real) (y : real) (z : real) : (term203 x y z) = (term76 x y z).
Proof. exact (MK_COMB (@lem1522708) (@lem1522707 x y z)). Qed.
Lemma lem1522710 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522711 (x : real) (y : real) (z : real) : (term201 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1522709 x y z) (@lem1522710)). Qed.
Lemma lem1522712 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term78 x y z.
Proof. exact (EQ_MP (@lem1522711 x y z) (@lem1522706 x y z h1)). Qed.
Lemma lem1522714 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1522715 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1522714 (term37 x y z)). Qed.
Lemma lem1522716 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term206 x y z.
Proof. exact (@lem1522715 x y z (@lem1522690 x y z h1)). Qed.
Lemma lem1522717 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term207 x y z.
Proof. exact (@lem1522716 x y z h1 term47). Qed.
Lemma lem1522718 (x : real) (y : real) (z : real) : (term207 x y z) = ((term50 x y z) = term31).
Proof. exact (eq_refl (term207 x y z)). Qed.
Lemma lem1522719 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term50 x y z) = term31.
Proof. exact (EQ_MP (@lem1522718 x y z) (@lem1522717 x y z h1)). Qed.
Lemma lem1522720 (x : real) (y : real) (z : real) : (term50 x y z) = (term51 x y z).
Proof. exact (@lem1483508 x term47 (term46 y z)). Qed.
Lemma lem1522721 (y : real) (z : real) : (term52 y z) = (term53 y z).
Proof. exact (@lem1483508 (term38 y) term47 (term38 z)). Qed.
Lemma lem1522722 (z : real) : (term54 z) = (term55 z).
Proof. exact (@lem1483476 term47 term47 z). Qed.
Lemma lem1522724 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1522725 : term58 = term59.
Proof. exact (@lem1522724 term60 term60). Qed.
Lemma lem1522726 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1522727 : term62 = term60.
Proof. exact (EQ_MP (@lem1522726) (@lem940073)). Qed.
Lemma lem1522728 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1522729 : term59 = term63.
Proof. exact (MK_COMB (@lem1522728) (@lem1522727)). Qed.
Lemma lem1522730 : term58 = term63.
Proof. exact (TRANS (@lem1522725) (@lem1522729)). Qed.
Lemma lem1522731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522732 : term64 = term65.
Proof. exact (MK_COMB (@lem1522731) (@lem1522730)). Qed.
Lemma lem1522733 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522734 (z : real) : (term55 z) = (term66 z).
Proof. exact (MK_COMB (@lem1522732) (@lem1522733 z)). Qed.
Lemma lem1522735 (z : real) : (term54 z) = (term66 z).
Proof. exact (TRANS (@lem1522722 z) (@lem1522734 z)). Qed.
Lemma lem1522736 (z : real) : (term66 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1522737 (z : real) : (term54 z) = z.
Proof. exact (TRANS (@lem1522735 z) (@lem1522736 z)). Qed.
Lemma lem1522738 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483476 term47 term47 y). Qed.
Lemma lem1522740 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1522741 : term58 = term59.
Proof. exact (@lem1522740 term60 term60). Qed.
Lemma lem1522742 : (term61 = (BIT1 0)) = (term62 = term60).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1522743 : term62 = term60.
Proof. exact (EQ_MP (@lem1522742) (@lem940073)). Qed.
Lemma lem1522744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1522745 : term59 = term63.
Proof. exact (MK_COMB (@lem1522744) (@lem1522743)). Qed.
Lemma lem1522746 : term58 = term63.
Proof. exact (TRANS (@lem1522741) (@lem1522745)). Qed.
Lemma lem1522747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522748 : term64 = term65.
Proof. exact (MK_COMB (@lem1522747) (@lem1522746)). Qed.
Lemma lem1522749 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522750 (y : real) : (term55 y) = (term66 y).
Proof. exact (MK_COMB (@lem1522748) (@lem1522749 y)). Qed.
Lemma lem1522751 (y : real) : (term54 y) = (term66 y).
Proof. exact (TRANS (@lem1522738 y) (@lem1522750 y)). Qed.
Lemma lem1522752 (y : real) : (term66 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1522753 (y : real) : (term54 y) = y.
Proof. exact (TRANS (@lem1522751 y) (@lem1522752 y)). Qed.
Lemma lem1522754 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522755 (y : real) : (term67 y) = (real_add y).
Proof. exact (MK_COMB (@lem1522754) (@lem1522753 y)). Qed.
Lemma lem1522756 (y : real) (z : real) : (term53 y z) = (real_add y z).
Proof. exact (MK_COMB (@lem1522755 y) (@lem1522737 z)). Qed.
Lemma lem1522757 (y : real) (z : real) : (term52 y z) = (real_add y z).
Proof. exact (TRANS (@lem1522721 y z) (@lem1522756 y z)). Qed.
Lemma lem1522760 (x : real) : (term68 x) = (term68 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1522761 (x : real) (y : real) (z : real) : (term51 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem1522760 x) (@lem1522757 y z)). Qed.
Lemma lem1522762 (x : real) (y : real) (z : real) : (term50 x y z) = (term69 x y z).
Proof. exact (TRANS (@lem1522720 x y z) (@lem1522761 x y z)). Qed.
Lemma lem1522763 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1522764 (x : real) (y : real) (z : real) : (term208 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1522763) (@lem1522762 x y z)). Qed.
Lemma lem1522765 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522766 (x : real) (y : real) (z : real) : ((term50 x y z) = term31) = ((term69 x y z) = term31).
Proof. exact (MK_COMB (@lem1522764 x y z) (@lem1522765)). Qed.
Lemma lem1522767 (x : real) (y : real) (z : real) (h1 : term249 x y z) : (term69 x y z) = term31.
Proof. exact (EQ_MP (@lem1522766 x y z) (@lem1522719 x y z h1)). Qed.
Lemma lem1522768 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term210 x y z.
Proof. exact (conj (@lem1522767 x y z h1) (@lem1522712 x y z h1)). Qed.
Lemma lem1522770 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1522771 (x : real) (y : real) (z : real) : term212 x y z.
Proof. exact (@lem1522770 (term69 x y z) (term37 x y z)). Qed.
Lemma lem1522772 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term213 x y z.
Proof. exact (@lem1522771 x y z (@lem1522768 x y z h1)). Qed.
Lemma lem1522773 (x : real) (y : real) (z : real) : (term214 x y z) = (term215 x y z).
Proof. exact (@lem1483480 (term38 x) x (real_add y z) (term46 y z)). Qed.
Lemma lem1522774 (x : real) : (term216 x) = (term217 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1522776 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522777 : term219 = term31.
Proof. exact (@lem1522776 term60). Qed.
Lemma lem1522778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522779 : term220 = term221.
Proof. exact (MK_COMB (@lem1522778) (@lem1522777)). Qed.
Lemma lem1522780 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1522781 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1522779) (@lem1522780 x)). Qed.
Lemma lem1522782 (x : real) : (term216 x) = (term222 x).
Proof. exact (TRANS (@lem1522774 x) (@lem1522781 x)). Qed.
Lemma lem1522783 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1522784 (x : real) : (term216 x) = term31.
Proof. exact (TRANS (@lem1522782 x) (@lem1522783 x)). Qed.
Lemma lem1522785 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522786 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1522785) (@lem1522784 x)). Qed.
Lemma lem1522787 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (@lem1483480 y (term38 y) z (term38 z)). Qed.
Lemma lem1522788 (y : real) : (term227 y) = (term217 y).
Proof. exact (@lem1483442 term47 y). Qed.
Lemma lem1522790 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522791 : term219 = term31.
Proof. exact (@lem1522790 term60). Qed.
Lemma lem1522792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522793 : term220 = term221.
Proof. exact (MK_COMB (@lem1522792) (@lem1522791)). Qed.
Lemma lem1522794 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522795 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1522793) (@lem1522794 y)). Qed.
Lemma lem1522796 (y : real) : (term227 y) = (term222 y).
Proof. exact (TRANS (@lem1522788 y) (@lem1522795 y)). Qed.
Lemma lem1522797 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1522798 (y : real) : (term227 y) = term31.
Proof. exact (TRANS (@lem1522796 y) (@lem1522797 y)). Qed.
Lemma lem1522799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522800 (y : real) : (term228 y) = term224.
Proof. exact (MK_COMB (@lem1522799) (@lem1522798 y)). Qed.
Lemma lem1522801 (z : real) : (term227 z) = (term217 z).
Proof. exact (@lem1483442 term47 z). Qed.
Lemma lem1522803 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522804 : term219 = term31.
Proof. exact (@lem1522803 term60). Qed.
Lemma lem1522805 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522806 : term220 = term221.
Proof. exact (MK_COMB (@lem1522805) (@lem1522804)). Qed.
Lemma lem1522807 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522808 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1522806) (@lem1522807 z)). Qed.
Lemma lem1522809 (z : real) : (term227 z) = (term222 z).
Proof. exact (TRANS (@lem1522801 z) (@lem1522808 z)). Qed.
Lemma lem1522810 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1522811 (z : real) : (term227 z) = term31.
Proof. exact (TRANS (@lem1522809 z) (@lem1522810 z)). Qed.
Lemma lem1522812 (y : real) (z : real) : (term226 y z) = term229.
Proof. exact (MK_COMB (@lem1522800 y) (@lem1522811 z)). Qed.
Lemma lem1522813 (y : real) (z : real) : (term225 y z) = term229.
Proof. exact (TRANS (@lem1522787 y z) (@lem1522812 y z)). Qed.
Lemma lem1522814 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522815 (y : real) (z : real) : (term225 y z) = term31.
Proof. exact (TRANS (@lem1522813 y z) (@lem1522814)). Qed.
Lemma lem1522816 (x : real) (y : real) (z : real) : (term215 x y z) = term229.
Proof. exact (MK_COMB (@lem1522786 x) (@lem1522815 y z)). Qed.
Lemma lem1522817 (x : real) (y : real) (z : real) : (term214 x y z) = term229.
Proof. exact (TRANS (@lem1522773 x y z) (@lem1522816 x y z)). Qed.
Lemma lem1522818 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522819 (x : real) (y : real) (z : real) : (term214 x y z) = term31.
Proof. exact (TRANS (@lem1522817 x y z) (@lem1522818)). Qed.
Lemma lem1522820 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522821 (x : real) (y : real) (z : real) : (term230 x y z) = term231.
Proof. exact (MK_COMB (@lem1522820) (@lem1522819 x y z)). Qed.
Lemma lem1522822 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522823 (x : real) (y : real) (z : real) : (term213 x y z) = term232.
Proof. exact (MK_COMB (@lem1522821 x y z) (@lem1522822)). Qed.
Lemma lem1522824 (x : real) (y : real) (z : real) (h1 : term249 x y z) : term232.
Proof. exact (EQ_MP (@lem1522823 x y z) (@lem1522772 x y z h1)). Qed.
Lemma lem1522826 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522827 : term232 = term233.
Proof. exact (@lem1522826 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1522828 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1522829 : term232 = False.
Proof. exact (TRANS (@lem1522827) (@lem1522828)). Qed.
Lemma lem1522830 (x : real) (y : real) (z : real) (h1 : term249 x y z) : False.
Proof. exact (EQ_MP (@lem1522829) (@lem1522824 x y z h1)). Qed.
Lemma lem1522831 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term250 x y z.
Proof. exact (h1). Qed.
Lemma lem1522832 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term37 x y z) = term31.
Proof. exact (proj2 (@lem1522831 x y z h1)). Qed.
Lemma lem1522833 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term74 x y z.
Proof. exact (proj1 (@lem1522831 x y z h1)). Qed.
Lemma lem1522835 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522836 : term195 = term196.
Proof. exact (@lem1522835 (NUMERAL 0) term60). Qed.
Lemma lem1522837 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1522838 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1522839 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1522838 h1) (fun h1 : term196 = True => @lem1522837)). Qed.
Lemma lem1522840 : term196 = True.
Proof. exact (EQ_MP (@lem1522839) (@lem1522837)). Qed.
Lemma lem1522841 : term195 = True.
Proof. exact (TRANS (@lem1522836) (@lem1522840)). Qed.
Lemma lem1522842 : True = term195.
Proof. exact (SYM (@lem1522841)). Qed.
Lemma lem1522843 : term195.
Proof. exact (EQ_MP (@lem1522842) (@lem0)). Qed.
Lemma lem1522844 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term235 x y z.
Proof. exact (conj (@lem1522843) (@lem1522833 x y z h1)). Qed.
Lemma lem1522846 (x : real) (y : real) : term199 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1522847 (x : real) (y : real) (z : real) : term236 x y z.
Proof. exact (@lem1522846 term63 (term69 x y z)). Qed.
Lemma lem1522848 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term237 x y z.
Proof. exact (@lem1522847 x y z (@lem1522844 x y z h1)). Qed.
Lemma lem1522849 (x : real) (y : real) (z : real) : (term238 x y z) = (term69 x y z).
Proof. exact (@lem1483460 (term69 x y z)). Qed.
Lemma lem1522850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522851 (x : real) (y : real) (z : real) : (term239 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1522850) (@lem1522849 x y z)). Qed.
Lemma lem1522852 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522853 (x : real) (y : real) (z : real) : (term237 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1522851 x y z) (@lem1522852)). Qed.
Lemma lem1522854 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term74 x y z.
Proof. exact (EQ_MP (@lem1522853 x y z) (@lem1522848 x y z h1)). Qed.
Lemma lem1522856 (y : real) : term204 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1522857 (x : real) (y : real) (z : real) : term205 x y z.
Proof. exact (@lem1522856 (term37 x y z)). Qed.
Lemma lem1522858 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term206 x y z.
Proof. exact (@lem1522857 x y z (@lem1522832 x y z h1)). Qed.
Lemma lem1522859 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term240 x y z.
Proof. exact (@lem1522858 x y z h1 term63). Qed.
Lemma lem1522860 (x : real) (y : real) (z : real) : (term240 x y z) = ((term202 x y z) = term31).
Proof. exact (eq_refl (term240 x y z)). Qed.
Lemma lem1522861 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term202 x y z) = term31.
Proof. exact (EQ_MP (@lem1522860 x y z) (@lem1522859 x y z h1)). Qed.
Lemma lem1522862 (x : real) (y : real) (z : real) : (term202 x y z) = (term37 x y z).
Proof. exact (@lem1483460 (term37 x y z)). Qed.
Lemma lem1522863 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1522864 (x : real) (y : real) (z : real) : (term241 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1522863) (@lem1522862 x y z)). Qed.
Lemma lem1522865 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522866 (x : real) (y : real) (z : real) : ((term202 x y z) = term31) = ((term37 x y z) = term31).
Proof. exact (MK_COMB (@lem1522864 x y z) (@lem1522865)). Qed.
Lemma lem1522867 (x : real) (y : real) (z : real) (h1 : term250 x y z) : (term37 x y z) = term31.
Proof. exact (EQ_MP (@lem1522866 x y z) (@lem1522861 x y z h1)). Qed.
Lemma lem1522868 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term234 x y z.
Proof. exact (conj (@lem1522867 x y z h1) (@lem1522854 x y z h1)). Qed.
Lemma lem1522870 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1522871 (x : real) (y : real) (z : real) : term242 x y z.
Proof. exact (@lem1522870 (term37 x y z) (term69 x y z)). Qed.
Lemma lem1522872 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term243 x y z.
Proof. exact (@lem1522871 x y z (@lem1522868 x y z h1)). Qed.
Lemma lem1522873 (x : real) (y : real) (z : real) : (term244 x y z) = (term245 x y z).
Proof. exact (@lem1483480 x (term38 x) (term46 y z) (real_add y z)). Qed.
Lemma lem1522874 (x : real) : (term227 x) = (term217 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1522876 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522877 : term219 = term31.
Proof. exact (@lem1522876 term60). Qed.
Lemma lem1522878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522879 : term220 = term221.
Proof. exact (MK_COMB (@lem1522878) (@lem1522877)). Qed.
Lemma lem1522880 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1522881 (x : real) : (term217 x) = (term222 x).
Proof. exact (MK_COMB (@lem1522879) (@lem1522880 x)). Qed.
Lemma lem1522882 (x : real) : (term227 x) = (term222 x).
Proof. exact (TRANS (@lem1522874 x) (@lem1522881 x)). Qed.
Lemma lem1522883 (x : real) : (term222 x) = term31.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1522884 (x : real) : (term227 x) = term31.
Proof. exact (TRANS (@lem1522882 x) (@lem1522883 x)). Qed.
Lemma lem1522885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522886 (x : real) : (term228 x) = term224.
Proof. exact (MK_COMB (@lem1522885) (@lem1522884 x)). Qed.
Lemma lem1522887 (y : real) (z : real) : (term246 y z) = (term247 y z).
Proof. exact (@lem1483480 (term38 y) y (term38 z) z). Qed.
Lemma lem1522888 (y : real) : (term216 y) = (term217 y).
Proof. exact (@lem1483440 term47 y). Qed.
Lemma lem1522890 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522891 : term219 = term31.
Proof. exact (@lem1522890 term60). Qed.
Lemma lem1522892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522893 : term220 = term221.
Proof. exact (MK_COMB (@lem1522892) (@lem1522891)). Qed.
Lemma lem1522894 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1522895 (y : real) : (term217 y) = (term222 y).
Proof. exact (MK_COMB (@lem1522893) (@lem1522894 y)). Qed.
Lemma lem1522896 (y : real) : (term216 y) = (term222 y).
Proof. exact (TRANS (@lem1522888 y) (@lem1522895 y)). Qed.
Lemma lem1522897 (y : real) : (term222 y) = term31.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1522898 (y : real) : (term216 y) = term31.
Proof. exact (TRANS (@lem1522896 y) (@lem1522897 y)). Qed.
Lemma lem1522899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1522900 (y : real) : (term223 y) = term224.
Proof. exact (MK_COMB (@lem1522899) (@lem1522898 y)). Qed.
Lemma lem1522901 (z : real) : (term216 z) = (term217 z).
Proof. exact (@lem1483440 term47 z). Qed.
Lemma lem1522903 (m : nat) : (term218 m) = term31.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1522904 : term219 = term31.
Proof. exact (@lem1522903 term60). Qed.
Lemma lem1522905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1522906 : term220 = term221.
Proof. exact (MK_COMB (@lem1522905) (@lem1522904)). Qed.
Lemma lem1522907 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1522908 (z : real) : (term217 z) = (term222 z).
Proof. exact (MK_COMB (@lem1522906) (@lem1522907 z)). Qed.
Lemma lem1522909 (z : real) : (term216 z) = (term222 z).
Proof. exact (TRANS (@lem1522901 z) (@lem1522908 z)). Qed.
Lemma lem1522910 (z : real) : (term222 z) = term31.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1522911 (z : real) : (term216 z) = term31.
Proof. exact (TRANS (@lem1522909 z) (@lem1522910 z)). Qed.
Lemma lem1522912 (y : real) (z : real) : (term247 y z) = term229.
Proof. exact (MK_COMB (@lem1522900 y) (@lem1522911 z)). Qed.
Lemma lem1522913 (y : real) (z : real) : (term246 y z) = term229.
Proof. exact (TRANS (@lem1522887 y z) (@lem1522912 y z)). Qed.
Lemma lem1522914 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522915 (y : real) (z : real) : (term246 y z) = term31.
Proof. exact (TRANS (@lem1522913 y z) (@lem1522914)). Qed.
Lemma lem1522916 (x : real) (y : real) (z : real) : (term245 x y z) = term229.
Proof. exact (MK_COMB (@lem1522886 x) (@lem1522915 y z)). Qed.
Lemma lem1522917 (x : real) (y : real) (z : real) : (term244 x y z) = term229.
Proof. exact (TRANS (@lem1522873 x y z) (@lem1522916 x y z)). Qed.
Lemma lem1522918 : term229 = term31.
Proof. exact (@lem1483448 term31). Qed.
Lemma lem1522919 (x : real) (y : real) (z : real) : (term244 x y z) = term31.
Proof. exact (TRANS (@lem1522917 x y z) (@lem1522918)). Qed.
Lemma lem1522920 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1522921 (x : real) (y : real) (z : real) : (term248 x y z) = term231.
Proof. exact (MK_COMB (@lem1522920) (@lem1522919 x y z)). Qed.
Lemma lem1522922 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1522923 (x : real) (y : real) (z : real) : (term243 x y z) = term232.
Proof. exact (MK_COMB (@lem1522921 x y z) (@lem1522922)). Qed.
Lemma lem1522924 (x : real) (y : real) (z : real) (h1 : term250 x y z) : term232.
Proof. exact (EQ_MP (@lem1522923 x y z) (@lem1522872 x y z h1)). Qed.
Lemma lem1522926 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1522927 : term232 = term233.
Proof. exact (@lem1522926 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1522928 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1522929 : term232 = False.
Proof. exact (TRANS (@lem1522927) (@lem1522928)). Qed.
Lemma lem1522930 (x : real) (y : real) (z : real) (h1 : term250 x y z) : False.
Proof. exact (EQ_MP (@lem1522929) (@lem1522924 x y z h1)). Qed.
Lemma lem1522931 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1522688 x y z h1) (fun h0 : term249 x y z => @lem1522830 x y z h0) (fun h0 : term250 x y z => @lem1522930 x y z h0)). Qed.
Lemma lem1522932 (x : real) (y : real) (z : real) (h1 : term186 x y z) : False.
Proof. exact (or_elim (@lem1522443 x y z h1) (fun h0 : term184 x y z => @lem1522687 x y z h0) (fun h0 : term183 x y z => @lem1522931 x y z h0)). Qed.
Lemma lem1522934 (x : real) (y : real) (z : real) (h1 : term186 x y z) : term186 x y z.
Proof. exact (h1). Qed.
Lemma lem1522935 (x : real) (y : real) (z : real) (h1 : term186 x y z) : (term186 x y z) = False.
Proof. exact (prop_ext (fun h2 : term186 x y z => @lem1522932 x y z h1) (fun h2 : False => @lem1522934 x y z h1)). Qed.
Lemma lem1522936 (x : real) (y : real) (z : real) (h1 : term186 x y z) : False.
Proof. exact (EQ_MP (@lem1522935 x y z h1) (@lem1522934 x y z h1)). Qed.
Lemma lem1522937 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1522938 (x : real) (y : real) (h1 : term188 x y) : False.
Proof. exact (ex_elim (@lem1522937 x y h1) (fun z : real => fun h0 : term187 x y z => @lem1522936 x y z h0)). Qed.
Lemma lem1522939 (x : real) (h1 : term190 x) : term190 x.
Proof. exact (h1). Qed.
Lemma lem1522940 (x : real) (h1 : term190 x) : False.
Proof. exact (ex_elim (@lem1522939 x h1) (fun y : real => fun h0 : term189 x y => @lem1522938 x y h0)). Qed.
Lemma lem1522941 (h1 : term192) : term192.
Proof. exact (h1). Qed.
Lemma lem1522942 (h1 : term192) : False.
Proof. exact (ex_elim (@lem1522941 h1) (fun x : real => fun h0 : term191 x => @lem1522940 x h0)). Qed.
Lemma lem1522943 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1522944 (h1 : term21) : term192.
Proof. exact (EQ_MP (@lem1522421) (@lem1522943 h1)). Qed.
Lemma lem1522945 (h1 : term21) : term192 = False.
Proof. exact (prop_ext (fun h2 : term192 => @lem1522942 h2) (fun h2 : False => @lem1522944 h1)). Qed.
Lemma lem1522946 (h1 : term21) : False.
Proof. exact (EQ_MP (@lem1522945 h1) (@lem1522944 h1)). Qed.
Lemma lem1522947 : term251.
Proof. exact (fun h0 : term21 => @lem1522946 h0). Qed.
Lemma lem1522948 : term252.
Proof. exact (@lem1386578 term253). Qed.
Lemma lem1522949 : term253.
Proof. exact (@lem1522948 (@lem1522947)). Qed.

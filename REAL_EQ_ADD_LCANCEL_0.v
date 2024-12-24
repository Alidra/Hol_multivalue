Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_ADD_LCANCEL_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483486_spec.
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
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Lemma lem1487591 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 ((real_add x y) = x) (y = term2)). Qed.
Lemma lem1487592 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1487593 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1487592 (term7 x)). Qed.
Lemma lem1487594 (x : real) (y : real) : (term8 x y) = (((real_add x y) = x) = (y = term2)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1487595 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487596 (x : real) (y : real) : (term9 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1487595) (@lem1487594 x y)). Qed.
Lemma lem1487597 (x : real) (y : real) : (term9 x y) = (term1 x y).
Proof. exact (TRANS (@lem1487596 x y) (@lem1487591 x y)). Qed.
Lemma lem1487598 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1487597 x y)). Qed.
Lemma lem1487599 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487600 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1487599) (@lem1487598 x)). Qed.
Lemma lem1487601 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1487593 x) (@lem1487600 x)). Qed.
Lemma lem1487602 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1487603 : term13 = term14.
Proof. exact (@lem1487602 term15). Qed.
Lemma lem1487604 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1487605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487606 (x : real) : (term18 x) = (term5 x).
Proof. exact (MK_COMB (@lem1487605) (@lem1487604 x)). Qed.
Lemma lem1487607 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1487606 x) (@lem1487601 x)). Qed.
Lemma lem1487608 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1487607 x)). Qed.
Lemma lem1487609 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487610 : term14 = term21.
Proof. exact (MK_COMB (@lem1487609) (@lem1487608)). Qed.
Lemma lem1487612 : term13 = term21.
Proof. exact (TRANS (@lem1487603) (@lem1487610)). Qed.
Lemma lem1487629 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1487630 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1487629 x y)). Qed.
Lemma lem1487631 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487632 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1487631) (@lem1487630 x)). Qed.
Lemma lem1487633 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1487632 x)). Qed.
Lemma lem1487634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487635 : term21 = term21.
Proof. exact (MK_COMB (@lem1487634) (@lem1487633)). Qed.
Lemma lem1487636 : term13 = term21.
Proof. exact (TRANS (@lem1487612) (@lem1487635)). Qed.
Lemma lem1487637 (y : real) (x : real) : ((real_add x y) = x) = ((term22 y x) = term2).
Proof. exact (@lem1483529 (real_add x y) x). Qed.
Lemma lem1487649 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1483519 (real_add x y) x). Qed.
Lemma lem1487653 (x : real) (y : real) : (term23 y x) = (term24 x y).
Proof. exact (@lem1483486 x (term25 x) y). Qed.
Lemma lem1487654 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1487656 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1487657 : term30 = term2.
Proof. exact (@lem1487656 term31). Qed.
Lemma lem1487658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1487659 : term32 = term33.
Proof. exact (MK_COMB (@lem1487658) (@lem1487657)). Qed.
Lemma lem1487660 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1487661 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1487659) (@lem1487660 x)). Qed.
Lemma lem1487662 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1487654 x) (@lem1487661 x)). Qed.
Lemma lem1487663 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1487664 (x : real) : (term26 x) = term2.
Proof. exact (TRANS (@lem1487662 x) (@lem1487663 x)). Qed.
Lemma lem1487665 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1487666 (x : real) : (term35 x) = term36.
Proof. exact (MK_COMB (@lem1487665) (@lem1487664 x)). Qed.
Lemma lem1487667 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1487668 (x : real) (y : real) : (term24 x y) = (term37 y).
Proof. exact (MK_COMB (@lem1487666 x) (@lem1487667 y)). Qed.
Lemma lem1487669 (x : real) (y : real) : (term23 y x) = (term37 y).
Proof. exact (TRANS (@lem1487653 x y) (@lem1487668 x y)). Qed.
Lemma lem1487670 (y : real) : (term37 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1487672 (x : real) (y : real) : (term23 y x) = y.
Proof. exact (TRANS (@lem1487669 x y) (@lem1487670 y)). Qed.
Lemma lem1487674 (x : real) (y : real) : (term22 y x) = y.
Proof. exact (TRANS (@lem1487649 y x) (@lem1487672 x y)). Qed.
Lemma lem1487675 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1487676 (x : real) (y : real) : (term38 y x) = (@eq real y).
Proof. exact (MK_COMB (@lem1487675) (@lem1487674 x y)). Qed.
Lemma lem1487677 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487678 (x : real) (y : real) : ((term22 y x) = term2) = (y = term2).
Proof. exact (MK_COMB (@lem1487676 x y) (@lem1487677)). Qed.
Lemma lem1487679 (x : real) (y : real) : ((real_add x y) = x) = (y = term2).
Proof. exact (TRANS (@lem1487637 y x) (@lem1487678 x y)). Qed.
Lemma lem1487680 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483554 y term2). Qed.
Lemma lem1487686 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483519 y term2). Qed.
Lemma lem1487688 (x : nat) : (term43 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1487689 : term44 = term2.
Proof. exact (@lem1487688 term31). Qed.
Lemma lem1487690 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1487691 (y : real) : (term42 y) = (term45 y).
Proof. exact (MK_COMB (@lem1487690 y) (@lem1487689)). Qed.
Lemma lem1487692 (y : real) : (term45 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1487693 (y : real) : (term42 y) = y.
Proof. exact (TRANS (@lem1487691 y) (@lem1487692 y)). Qed.
Lemma lem1487695 (y : real) : (term41 y) = y.
Proof. exact (TRANS (@lem1487686 y) (@lem1487693 y)). Qed.
Lemma lem1487696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1487697 (y : real) : (term46 y) = (real_neg y).
Proof. exact (MK_COMB (@lem1487696) (@lem1487695 y)). Qed.
Lemma lem1487700 (y : real) : (real_neg y) = (term25 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1487701 (y : real) : (term47 y) = (term47 y).
Proof. exact (eq_refl (term47 y)). Qed.
Lemma lem1487702 (y : real) : ((term46 y) = (real_neg y)) = ((term46 y) = (term25 y)).
Proof. exact (MK_COMB (@lem1487701 y) (@lem1487700 y)). Qed.
Lemma lem1487703 (y : real) : (term46 y) = (term25 y).
Proof. exact (EQ_MP (@lem1487702 y) (@lem1487697 y)). Qed.
Lemma lem1487704 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1487705 (y : real) : (term48 y) = (term49 y).
Proof. exact (MK_COMB (@lem1487704) (@lem1487703 y)). Qed.
Lemma lem1487706 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487707 (y : real) : (term50 y) = (term51 y).
Proof. exact (MK_COMB (@lem1487705 y) (@lem1487706)). Qed.
Lemma lem1487708 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1487709 (y : real) : (term52 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1487708) (@lem1487695 y)). Qed.
Lemma lem1487710 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487711 (y : real) : (term53 y) = (term54 y).
Proof. exact (MK_COMB (@lem1487709 y) (@lem1487710)). Qed.
Lemma lem1487712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487713 (y : real) : (term55 y) = (term56 y).
Proof. exact (MK_COMB (@lem1487712) (@lem1487711 y)). Qed.
Lemma lem1487714 (y : real) : (term40 y) = (term57 y).
Proof. exact (MK_COMB (@lem1487713 y) (@lem1487707 y)). Qed.
Lemma lem1487715 (y : real) : (term39 y) = (term57 y).
Proof. exact (TRANS (@lem1487680 y) (@lem1487714 y)). Qed.
Lemma lem1487716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487717 (x : real) (y : real) : (term58 y x) = (term59 y).
Proof. exact (MK_COMB (@lem1487716) (@lem1487679 x y)). Qed.
Lemma lem1487718 (x : real) (y : real) : (term60 x y) = (term61 y).
Proof. exact (MK_COMB (@lem1487717 x y) (@lem1487715 y)). Qed.
Lemma lem1487719 (y : real) (x : real) : (term62 y x) = (term63 y x).
Proof. exact (@lem1483554 (real_add x y) x). Qed.
Lemma lem1487731 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1483519 (real_add x y) x). Qed.
Lemma lem1487735 (x : real) (y : real) : (term23 y x) = (term24 x y).
Proof. exact (@lem1483486 x (term25 x) y). Qed.
Lemma lem1487736 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1487738 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1487739 : term30 = term2.
Proof. exact (@lem1487738 term31). Qed.
Lemma lem1487740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1487741 : term32 = term33.
Proof. exact (MK_COMB (@lem1487740) (@lem1487739)). Qed.
Lemma lem1487742 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1487743 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1487741) (@lem1487742 x)). Qed.
Lemma lem1487744 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1487736 x) (@lem1487743 x)). Qed.
Lemma lem1487745 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1487746 (x : real) : (term26 x) = term2.
Proof. exact (TRANS (@lem1487744 x) (@lem1487745 x)). Qed.
Lemma lem1487747 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1487748 (x : real) : (term35 x) = term36.
Proof. exact (MK_COMB (@lem1487747) (@lem1487746 x)). Qed.
Lemma lem1487749 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1487750 (x : real) (y : real) : (term24 x y) = (term37 y).
Proof. exact (MK_COMB (@lem1487748 x) (@lem1487749 y)). Qed.
Lemma lem1487751 (x : real) (y : real) : (term23 y x) = (term37 y).
Proof. exact (TRANS (@lem1487735 x y) (@lem1487750 x y)). Qed.
Lemma lem1487752 (y : real) : (term37 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1487754 (x : real) (y : real) : (term23 y x) = y.
Proof. exact (TRANS (@lem1487751 x y) (@lem1487752 y)). Qed.
Lemma lem1487756 (x : real) (y : real) : (term22 y x) = y.
Proof. exact (TRANS (@lem1487731 y x) (@lem1487754 x y)). Qed.
Lemma lem1487757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1487758 (x : real) (y : real) : (term64 y x) = (real_neg y).
Proof. exact (MK_COMB (@lem1487757) (@lem1487756 x y)). Qed.
Lemma lem1487761 (y : real) : (real_neg y) = (term25 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1487762 (y : real) (x : real) : (term65 y x) = (term65 y x).
Proof. exact (eq_refl (term65 y x)). Qed.
Lemma lem1487763 (x : real) (y : real) : ((term64 y x) = (real_neg y)) = ((term64 y x) = (term25 y)).
Proof. exact (MK_COMB (@lem1487762 y x) (@lem1487761 y)). Qed.
Lemma lem1487764 (x : real) (y : real) : (term64 y x) = (term25 y).
Proof. exact (EQ_MP (@lem1487763 x y) (@lem1487758 x y)). Qed.
Lemma lem1487765 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1487766 (x : real) (y : real) : (term66 y x) = (term49 y).
Proof. exact (MK_COMB (@lem1487765) (@lem1487764 x y)). Qed.
Lemma lem1487767 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487768 (x : real) (y : real) : (term67 y x) = (term51 y).
Proof. exact (MK_COMB (@lem1487766 x y) (@lem1487767)). Qed.
Lemma lem1487769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1487770 (x : real) (y : real) : (term68 y x) = (real_gt y).
Proof. exact (MK_COMB (@lem1487769) (@lem1487756 x y)). Qed.
Lemma lem1487771 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487772 (x : real) (y : real) : (term69 y x) = (term54 y).
Proof. exact (MK_COMB (@lem1487770 x y) (@lem1487771)). Qed.
Lemma lem1487773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487774 (x : real) (y : real) : (term70 y x) = (term56 y).
Proof. exact (MK_COMB (@lem1487773) (@lem1487772 x y)). Qed.
Lemma lem1487775 (x : real) (y : real) : (term63 y x) = (term57 y).
Proof. exact (MK_COMB (@lem1487774 x y) (@lem1487768 x y)). Qed.
Lemma lem1487776 (x : real) (y : real) : (term62 y x) = (term57 y).
Proof. exact (TRANS (@lem1487719 y x) (@lem1487775 x y)). Qed.
Lemma lem1487777 (y : real) : (y = term2) = ((term41 y) = term2).
Proof. exact (@lem1483529 y term2). Qed.
Lemma lem1487783 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483519 y term2). Qed.
Lemma lem1487785 (x : nat) : (term43 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1487786 : term44 = term2.
Proof. exact (@lem1487785 term31). Qed.
Lemma lem1487787 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1487788 (y : real) : (term42 y) = (term45 y).
Proof. exact (MK_COMB (@lem1487787 y) (@lem1487786)). Qed.
Lemma lem1487789 (y : real) : (term45 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1487790 (y : real) : (term42 y) = y.
Proof. exact (TRANS (@lem1487788 y) (@lem1487789 y)). Qed.
Lemma lem1487792 (y : real) : (term41 y) = y.
Proof. exact (TRANS (@lem1487783 y) (@lem1487790 y)). Qed.
Lemma lem1487793 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1487794 (y : real) : (term71 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1487793) (@lem1487792 y)). Qed.
Lemma lem1487795 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1487796 (y : real) : ((term41 y) = term2) = (y = term2).
Proof. exact (MK_COMB (@lem1487794 y) (@lem1487795)). Qed.
Lemma lem1487797 (y : real) : (y = term2) = (y = term2).
Proof. exact (TRANS (@lem1487777 y) (@lem1487796 y)). Qed.
Lemma lem1487798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487799 (x : real) (y : real) : (term72 y x) = (term73 y).
Proof. exact (MK_COMB (@lem1487798) (@lem1487776 x y)). Qed.
Lemma lem1487800 (x : real) (y : real) : (term74 x y) = (term75 y).
Proof. exact (MK_COMB (@lem1487799 x y) (@lem1487797 y)). Qed.
Lemma lem1487801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487802 (x : real) (y : real) : (term76 x y) = (term77 y).
Proof. exact (MK_COMB (@lem1487801) (@lem1487718 x y)). Qed.
Lemma lem1487803 (x : real) (y : real) : (term1 x y) = (term78 y).
Proof. exact (MK_COMB (@lem1487802 x y) (@lem1487800 x y)). Qed.
Lemma lem1487804 (x : real) : (term11 x) = term79.
Proof. exact (fun_ext (fun y : real => @lem1487803 x y)). Qed.
Lemma lem1487805 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487806 (x : real) : (term12 x) = term80.
Proof. exact (MK_COMB (@lem1487805) (@lem1487804 x)). Qed.
Lemma lem1487807 : term20 = term81.
Proof. exact (fun_ext (fun x : real => @lem1487806 x)). Qed.
Lemma lem1487808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487809 : term21 = term82.
Proof. exact (MK_COMB (@lem1487808) (@lem1487807)). Qed.
Lemma lem1487810 : term13 = term82.
Proof. exact (TRANS (@lem1487636) (@lem1487809)). Qed.
Lemma lem1487812 {A : Type'} (t : Prop) : (term83 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1487813 (t : Prop) : (term84 t) = t.
Proof. exact (@lem1487812 real t). Qed.
Lemma lem1487814 : term82 = term80.
Proof. exact (@lem1487813 term80). Qed.
Lemma lem1487816 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1487817 (P : real -> Prop) (Q : real -> Prop) : (term87 P Q) = (term88 P Q).
Proof. exact (@lem1487816 real P Q). Qed.
Lemma lem1487818 : term89 = term90.
Proof. exact (@lem1487817 term91 term92). Qed.
Lemma lem1487819 (y : real) : (term93 y) = (term61 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1487820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487821 (y : real) : (term94 y) = (term77 y).
Proof. exact (MK_COMB (@lem1487820) (@lem1487819 y)). Qed.
Lemma lem1487822 (y : real) : (term95 y) = (term75 y).
Proof. exact (eq_refl (term95 y)). Qed.
Lemma lem1487823 (y : real) : (term96 y) = (term78 y).
Proof. exact (MK_COMB (@lem1487821 y) (@lem1487822 y)). Qed.
Lemma lem1487824 : term97 = term79.
Proof. exact (fun_ext (fun y : real => @lem1487823 y)). Qed.
Lemma lem1487825 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487826 : term89 = term80.
Proof. exact (MK_COMB (@lem1487825) (@lem1487824)). Qed.
Lemma lem1487827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1487828 : term98 = term99.
Proof. exact (MK_COMB (@lem1487827) (@lem1487826)). Qed.
Lemma lem1487829 (y : real) : (term93 y) = (term61 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1487830 : term100 = term91.
Proof. exact (fun_ext (fun y : real => @lem1487829 y)). Qed.
Lemma lem1487831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487832 : term101 = term102.
Proof. exact (MK_COMB (@lem1487831) (@lem1487830)). Qed.
Lemma lem1487833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487834 : term103 = term104.
Proof. exact (MK_COMB (@lem1487833) (@lem1487832)). Qed.
Lemma lem1487835 (y : real) : (term95 y) = (term75 y).
Proof. exact (eq_refl (term95 y)). Qed.
Lemma lem1487836 : term105 = term92.
Proof. exact (fun_ext (fun y : real => @lem1487835 y)). Qed.
Lemma lem1487837 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487838 : term106 = term107.
Proof. exact (MK_COMB (@lem1487837) (@lem1487836)). Qed.
Lemma lem1487839 : term90 = term108.
Proof. exact (MK_COMB (@lem1487834) (@lem1487838)). Qed.
Lemma lem1487840 : (term89 = term90) = (term80 = term108).
Proof. exact (MK_COMB (@lem1487828) (@lem1487839)). Qed.
Lemma lem1487841 : term80 = term108.
Proof. exact (EQ_MP (@lem1487840) (@lem1487818)). Qed.
Lemma lem1487842 : term82 = term108.
Proof. exact (TRANS (@lem1487814) (@lem1487841)). Qed.
Lemma lem1487940 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1487941 (P : real -> Prop) (Q : real -> Prop) : (term88 P Q) = (term87 P Q).
Proof. exact (@lem1487940 real P Q). Qed.
Lemma lem1487942 : term90 = term89.
Proof. exact (@lem1487941 term91 term92). Qed.
Lemma lem1487943 (y : real) : (term93 y) = (term61 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1487944 : term100 = term91.
Proof. exact (fun_ext (fun y : real => @lem1487943 y)). Qed.
Lemma lem1487945 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487946 : term101 = term102.
Proof. exact (MK_COMB (@lem1487945) (@lem1487944)). Qed.
Lemma lem1487947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487948 : term103 = term104.
Proof. exact (MK_COMB (@lem1487947) (@lem1487946)). Qed.
Lemma lem1487949 (y : real) : (term95 y) = (term75 y).
Proof. exact (eq_refl (term95 y)). Qed.
Lemma lem1487950 : term105 = term92.
Proof. exact (fun_ext (fun y : real => @lem1487949 y)). Qed.
Lemma lem1487951 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487952 : term106 = term107.
Proof. exact (MK_COMB (@lem1487951) (@lem1487950)). Qed.
Lemma lem1487953 : term90 = term108.
Proof. exact (MK_COMB (@lem1487948) (@lem1487952)). Qed.
Lemma lem1487954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1487955 : term109 = term110.
Proof. exact (MK_COMB (@lem1487954) (@lem1487953)). Qed.
Lemma lem1487956 (y : real) : (term93 y) = (term61 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1487957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487958 (y : real) : (term94 y) = (term77 y).
Proof. exact (MK_COMB (@lem1487957) (@lem1487956 y)). Qed.
Lemma lem1487959 (y : real) : (term95 y) = (term75 y).
Proof. exact (eq_refl (term95 y)). Qed.
Lemma lem1487960 (y : real) : (term96 y) = (term78 y).
Proof. exact (MK_COMB (@lem1487958 y) (@lem1487959 y)). Qed.
Lemma lem1487961 : term97 = term79.
Proof. exact (fun_ext (fun y : real => @lem1487960 y)). Qed.
Lemma lem1487962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1487963 : term89 = term80.
Proof. exact (MK_COMB (@lem1487962) (@lem1487961)). Qed.
Lemma lem1487964 : (term90 = term89) = (term108 = term80).
Proof. exact (MK_COMB (@lem1487955) (@lem1487963)). Qed.
Lemma lem1487965 : term108 = term80.
Proof. exact (EQ_MP (@lem1487964) (@lem1487942)). Qed.
Lemma lem1487966 : term82 = term80.
Proof. exact (TRANS (@lem1487842) (@lem1487965)). Qed.
Lemma lem1487969 : term13 = term80.
Proof. exact (TRANS (@lem1487810) (@lem1487966)). Qed.
Lemma lem1487986 (y : real) : (term75 y) = (term111 y).
Proof. exact (@lem19367 (term54 y) (term51 y) (y = term2)). Qed.
Lemma lem1488003 (y : real) : (term61 y) = (term112 y).
Proof. exact (@lem19158 (term54 y) (y = term2) (term51 y)). Qed.
Lemma lem1488004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488005 (y : real) : (term77 y) = (term113 y).
Proof. exact (MK_COMB (@lem1488004) (@lem1488003 y)). Qed.
Lemma lem1488006 (y : real) : (term78 y) = (term114 y).
Proof. exact (MK_COMB (@lem1488005 y) (@lem1487986 y)). Qed.
Lemma lem1488007 : term79 = term115.
Proof. exact (fun_ext (fun y : real => @lem1488006 y)). Qed.
Lemma lem1488008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488009 : term80 = term116.
Proof. exact (MK_COMB (@lem1488008) (@lem1488007)). Qed.
Lemma lem1488010 : term13 = term116.
Proof. exact (TRANS (@lem1487969) (@lem1488009)). Qed.
Lemma lem1488032 (y : real) (h1 : term114 y) : term114 y.
Proof. exact (h1). Qed.
Lemma lem1488033 (y : real) (h1 : term112 y) : term112 y.
Proof. exact (h1). Qed.
Lemma lem1488034 (y : real) (h1 : term117 y) : term117 y.
Proof. exact (h1). Qed.
Lemma lem1488035 (y : real) (h1 : term117 y) : term54 y.
Proof. exact (proj2 (@lem1488034 y h1)). Qed.
Lemma lem1488036 (y : real) (h1 : term117 y) : y = term2.
Proof. exact (proj1 (@lem1488034 y h1)). Qed.
Lemma lem1488038 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488039 : term119 = term120.
Proof. exact (@lem1488038 (NUMERAL 0) term31). Qed.
Lemma lem1488040 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488041 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488042 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1488041 h1) (fun h1 : term120 = True => @lem1488040)). Qed.
Lemma lem1488043 : term120 = True.
Proof. exact (EQ_MP (@lem1488042) (@lem1488040)). Qed.
Lemma lem1488044 : term119 = True.
Proof. exact (TRANS (@lem1488039) (@lem1488043)). Qed.
Lemma lem1488045 : True = term119.
Proof. exact (SYM (@lem1488044)). Qed.
Lemma lem1488046 : term119.
Proof. exact (EQ_MP (@lem1488045) (@lem0)). Qed.
Lemma lem1488047 (y : real) (h1 : term117 y) : term122 y.
Proof. exact (conj (@lem1488046) (@lem1488035 y h1)). Qed.
Lemma lem1488049 (x : real) (y : real) : term123 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488050 (y : real) : term124 y.
Proof. exact (@lem1488049 term125 y). Qed.
Lemma lem1488051 (y : real) (h1 : term117 y) : term126 y.
Proof. exact (@lem1488050 y (@lem1488047 y h1)). Qed.
Lemma lem1488052 (y : real) : (term127 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1488053 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488054 (y : real) : (term128 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1488053) (@lem1488052 y)). Qed.
Lemma lem1488055 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488056 (y : real) : (term126 y) = (term54 y).
Proof. exact (MK_COMB (@lem1488054 y) (@lem1488055)). Qed.
Lemma lem1488057 (y : real) (h1 : term117 y) : term54 y.
Proof. exact (EQ_MP (@lem1488056 y) (@lem1488051 y h1)). Qed.
Lemma lem1488059 (y : real) : term129 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488060 (y : real) (h1 : term117 y) : term130 y.
Proof. exact (@lem1488059 y (@lem1488036 y h1)). Qed.
Lemma lem1488061 (y : real) (h1 : term117 y) : term131 y.
Proof. exact (@lem1488060 y h1 term28). Qed.
Lemma lem1488062 (y : real) : (term131 y) = ((term25 y) = term2).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem1488069 (y : real) (h1 : term117 y) : (term25 y) = term2.
Proof. exact (EQ_MP (@lem1488062 y) (@lem1488061 y h1)). Qed.
Lemma lem1488070 (y : real) (h1 : term117 y) : term132 y.
Proof. exact (conj (@lem1488069 y h1) (@lem1488057 y h1)). Qed.
Lemma lem1488072 (x : real) (y : real) : term133 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488073 (y : real) : term134 y.
Proof. exact (@lem1488072 (term25 y) y). Qed.
Lemma lem1488074 (y : real) (h1 : term117 y) : term135 y.
Proof. exact (@lem1488073 y (@lem1488070 y h1)). Qed.
Lemma lem1488075 (y : real) : (term136 y) = (term27 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1488077 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488078 : term30 = term2.
Proof. exact (@lem1488077 term31). Qed.
Lemma lem1488079 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488080 : term32 = term33.
Proof. exact (MK_COMB (@lem1488079) (@lem1488078)). Qed.
Lemma lem1488081 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488082 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488080) (@lem1488081 y)). Qed.
Lemma lem1488083 (y : real) : (term136 y) = (term34 y).
Proof. exact (TRANS (@lem1488075 y) (@lem1488082 y)). Qed.
Lemma lem1488084 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488085 (y : real) : (term136 y) = term2.
Proof. exact (TRANS (@lem1488083 y) (@lem1488084 y)). Qed.
Lemma lem1488086 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488087 (y : real) : (term137 y) = term138.
Proof. exact (MK_COMB (@lem1488086) (@lem1488085 y)). Qed.
Lemma lem1488088 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488089 (y : real) : (term135 y) = term139.
Proof. exact (MK_COMB (@lem1488087 y) (@lem1488088)). Qed.
Lemma lem1488090 (y : real) (h1 : term117 y) : term139.
Proof. exact (EQ_MP (@lem1488089 y) (@lem1488074 y h1)). Qed.
Lemma lem1488092 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488093 : term139 = term140.
Proof. exact (@lem1488092 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1488094 : term140 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1488095 : term139 = False.
Proof. exact (TRANS (@lem1488093) (@lem1488094)). Qed.
Lemma lem1488096 (y : real) (h1 : term117 y) : False.
Proof. exact (EQ_MP (@lem1488095) (@lem1488090 y h1)). Qed.
Lemma lem1488097 (y : real) (h1 : term141 y) : term141 y.
Proof. exact (h1). Qed.
Lemma lem1488098 (y : real) (h1 : term141 y) : term51 y.
Proof. exact (proj2 (@lem1488097 y h1)). Qed.
Lemma lem1488099 (y : real) (h1 : term141 y) : y = term2.
Proof. exact (proj1 (@lem1488097 y h1)). Qed.
Lemma lem1488101 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488102 : term119 = term120.
Proof. exact (@lem1488101 (NUMERAL 0) term31). Qed.
Lemma lem1488103 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488104 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488105 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1488104 h1) (fun h1 : term120 = True => @lem1488103)). Qed.
Lemma lem1488106 : term120 = True.
Proof. exact (EQ_MP (@lem1488105) (@lem1488103)). Qed.
Lemma lem1488107 : term119 = True.
Proof. exact (TRANS (@lem1488102) (@lem1488106)). Qed.
Lemma lem1488108 : True = term119.
Proof. exact (SYM (@lem1488107)). Qed.
Lemma lem1488109 : term119.
Proof. exact (EQ_MP (@lem1488108) (@lem0)). Qed.
Lemma lem1488110 (y : real) (h1 : term141 y) : term142 y.
Proof. exact (conj (@lem1488109) (@lem1488098 y h1)). Qed.
Lemma lem1488112 (x : real) (y : real) : term123 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488113 (y : real) : term143 y.
Proof. exact (@lem1488112 term125 (term25 y)). Qed.
Lemma lem1488114 (y : real) (h1 : term141 y) : term144 y.
Proof. exact (@lem1488113 y (@lem1488110 y h1)). Qed.
Lemma lem1488115 (y : real) : (term145 y) = (term25 y).
Proof. exact (@lem1483460 (term25 y)). Qed.
Lemma lem1488116 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488117 (y : real) : (term146 y) = (term49 y).
Proof. exact (MK_COMB (@lem1488116) (@lem1488115 y)). Qed.
Lemma lem1488118 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488119 (y : real) : (term144 y) = (term51 y).
Proof. exact (MK_COMB (@lem1488117 y) (@lem1488118)). Qed.
Lemma lem1488120 (y : real) (h1 : term141 y) : term51 y.
Proof. exact (EQ_MP (@lem1488119 y) (@lem1488114 y h1)). Qed.
Lemma lem1488122 (y : real) : term129 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488123 (y : real) (h1 : term141 y) : term130 y.
Proof. exact (@lem1488122 y (@lem1488099 y h1)). Qed.
Lemma lem1488124 (y : real) (h1 : term141 y) : term147 y.
Proof. exact (@lem1488123 y h1 term125). Qed.
Lemma lem1488125 (y : real) : (term147 y) = ((term127 y) = term2).
Proof. exact (eq_refl (term147 y)). Qed.
Lemma lem1488126 (y : real) (h1 : term141 y) : (term127 y) = term2.
Proof. exact (EQ_MP (@lem1488125 y) (@lem1488124 y h1)). Qed.
Lemma lem1488127 (y : real) : (term127 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1488128 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1488129 (y : real) : (term148 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1488128) (@lem1488127 y)). Qed.
Lemma lem1488130 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488131 (y : real) : ((term127 y) = term2) = (y = term2).
Proof. exact (MK_COMB (@lem1488129 y) (@lem1488130)). Qed.
Lemma lem1488132 (y : real) (h1 : term141 y) : y = term2.
Proof. exact (EQ_MP (@lem1488131 y) (@lem1488126 y h1)). Qed.
Lemma lem1488133 (y : real) (h1 : term141 y) : term141 y.
Proof. exact (conj (@lem1488132 y h1) (@lem1488120 y h1)). Qed.
Lemma lem1488135 (x : real) (y : real) : term133 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488136 (y : real) : term149 y.
Proof. exact (@lem1488135 y (term25 y)). Qed.
Lemma lem1488137 (y : real) (h1 : term141 y) : term150 y.
Proof. exact (@lem1488136 y (@lem1488133 y h1)). Qed.
Lemma lem1488138 (y : real) : (term26 y) = (term27 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1488140 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488141 : term30 = term2.
Proof. exact (@lem1488140 term31). Qed.
Lemma lem1488142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488143 : term32 = term33.
Proof. exact (MK_COMB (@lem1488142) (@lem1488141)). Qed.
Lemma lem1488144 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488145 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488143) (@lem1488144 y)). Qed.
Lemma lem1488146 (y : real) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem1488138 y) (@lem1488145 y)). Qed.
Lemma lem1488147 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488148 (y : real) : (term26 y) = term2.
Proof. exact (TRANS (@lem1488146 y) (@lem1488147 y)). Qed.
Lemma lem1488149 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488150 (y : real) : (term151 y) = term138.
Proof. exact (MK_COMB (@lem1488149) (@lem1488148 y)). Qed.
Lemma lem1488151 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488152 (y : real) : (term150 y) = term139.
Proof. exact (MK_COMB (@lem1488150 y) (@lem1488151)). Qed.
Lemma lem1488153 (y : real) (h1 : term141 y) : term139.
Proof. exact (EQ_MP (@lem1488152 y) (@lem1488137 y h1)). Qed.
Lemma lem1488155 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488156 : term139 = term140.
Proof. exact (@lem1488155 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1488157 : term140 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1488158 : term139 = False.
Proof. exact (TRANS (@lem1488156) (@lem1488157)). Qed.
Lemma lem1488159 (y : real) (h1 : term141 y) : False.
Proof. exact (EQ_MP (@lem1488158) (@lem1488153 y h1)). Qed.
Lemma lem1488160 (y : real) (h1 : term112 y) : False.
Proof. exact (or_elim (@lem1488033 y h1) (fun h0 : term117 y => @lem1488096 y h0) (fun h0 : term141 y => @lem1488159 y h0)). Qed.
Lemma lem1488161 (y : real) (h1 : term111 y) : term111 y.
Proof. exact (h1). Qed.
Lemma lem1488162 (y : real) (h1 : term152 y) : term152 y.
Proof. exact (h1). Qed.
Lemma lem1488163 (y : real) (h1 : term152 y) : y = term2.
Proof. exact (proj2 (@lem1488162 y h1)). Qed.
Lemma lem1488164 (y : real) (h1 : term152 y) : term54 y.
Proof. exact (proj1 (@lem1488162 y h1)). Qed.
Lemma lem1488166 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488167 : term119 = term120.
Proof. exact (@lem1488166 (NUMERAL 0) term31). Qed.
Lemma lem1488168 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488169 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488170 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1488169 h1) (fun h1 : term120 = True => @lem1488168)). Qed.
Lemma lem1488171 : term120 = True.
Proof. exact (EQ_MP (@lem1488170) (@lem1488168)). Qed.
Lemma lem1488172 : term119 = True.
Proof. exact (TRANS (@lem1488167) (@lem1488171)). Qed.
Lemma lem1488173 : True = term119.
Proof. exact (SYM (@lem1488172)). Qed.
Lemma lem1488174 : term119.
Proof. exact (EQ_MP (@lem1488173) (@lem0)). Qed.
Lemma lem1488175 (y : real) (h1 : term152 y) : term122 y.
Proof. exact (conj (@lem1488174) (@lem1488164 y h1)). Qed.
Lemma lem1488177 (x : real) (y : real) : term123 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488178 (y : real) : term124 y.
Proof. exact (@lem1488177 term125 y). Qed.
Lemma lem1488179 (y : real) (h1 : term152 y) : term126 y.
Proof. exact (@lem1488178 y (@lem1488175 y h1)). Qed.
Lemma lem1488180 (y : real) : (term127 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1488181 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488182 (y : real) : (term128 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1488181) (@lem1488180 y)). Qed.
Lemma lem1488183 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488184 (y : real) : (term126 y) = (term54 y).
Proof. exact (MK_COMB (@lem1488182 y) (@lem1488183)). Qed.
Lemma lem1488185 (y : real) (h1 : term152 y) : term54 y.
Proof. exact (EQ_MP (@lem1488184 y) (@lem1488179 y h1)). Qed.
Lemma lem1488187 (y : real) : term129 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488188 (y : real) (h1 : term152 y) : term130 y.
Proof. exact (@lem1488187 y (@lem1488163 y h1)). Qed.
Lemma lem1488189 (y : real) (h1 : term152 y) : term131 y.
Proof. exact (@lem1488188 y h1 term28). Qed.
Lemma lem1488190 (y : real) : (term131 y) = ((term25 y) = term2).
Proof. exact (eq_refl (term131 y)). Qed.
Lemma lem1488197 (y : real) (h1 : term152 y) : (term25 y) = term2.
Proof. exact (EQ_MP (@lem1488190 y) (@lem1488189 y h1)). Qed.
Lemma lem1488198 (y : real) (h1 : term152 y) : term132 y.
Proof. exact (conj (@lem1488197 y h1) (@lem1488185 y h1)). Qed.
Lemma lem1488200 (x : real) (y : real) : term133 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488201 (y : real) : term134 y.
Proof. exact (@lem1488200 (term25 y) y). Qed.
Lemma lem1488202 (y : real) (h1 : term152 y) : term135 y.
Proof. exact (@lem1488201 y (@lem1488198 y h1)). Qed.
Lemma lem1488203 (y : real) : (term136 y) = (term27 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1488205 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488206 : term30 = term2.
Proof. exact (@lem1488205 term31). Qed.
Lemma lem1488207 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488208 : term32 = term33.
Proof. exact (MK_COMB (@lem1488207) (@lem1488206)). Qed.
Lemma lem1488209 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488210 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488208) (@lem1488209 y)). Qed.
Lemma lem1488211 (y : real) : (term136 y) = (term34 y).
Proof. exact (TRANS (@lem1488203 y) (@lem1488210 y)). Qed.
Lemma lem1488212 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488213 (y : real) : (term136 y) = term2.
Proof. exact (TRANS (@lem1488211 y) (@lem1488212 y)). Qed.
Lemma lem1488214 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488215 (y : real) : (term137 y) = term138.
Proof. exact (MK_COMB (@lem1488214) (@lem1488213 y)). Qed.
Lemma lem1488216 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488217 (y : real) : (term135 y) = term139.
Proof. exact (MK_COMB (@lem1488215 y) (@lem1488216)). Qed.
Lemma lem1488218 (y : real) (h1 : term152 y) : term139.
Proof. exact (EQ_MP (@lem1488217 y) (@lem1488202 y h1)). Qed.
Lemma lem1488220 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488221 : term139 = term140.
Proof. exact (@lem1488220 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1488222 : term140 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1488223 : term139 = False.
Proof. exact (TRANS (@lem1488221) (@lem1488222)). Qed.
Lemma lem1488224 (y : real) (h1 : term152 y) : False.
Proof. exact (EQ_MP (@lem1488223) (@lem1488218 y h1)). Qed.
Lemma lem1488225 (y : real) (h1 : term153 y) : term153 y.
Proof. exact (h1). Qed.
Lemma lem1488226 (y : real) (h1 : term153 y) : y = term2.
Proof. exact (proj2 (@lem1488225 y h1)). Qed.
Lemma lem1488227 (y : real) (h1 : term153 y) : term51 y.
Proof. exact (proj1 (@lem1488225 y h1)). Qed.
Lemma lem1488229 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488230 : term119 = term120.
Proof. exact (@lem1488229 (NUMERAL 0) term31). Qed.
Lemma lem1488231 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488232 (h1 : term121 = (BIT1 0)) : term120 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488233 : (term121 = (BIT1 0)) = (term120 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem1488232 h1) (fun h1 : term120 = True => @lem1488231)). Qed.
Lemma lem1488234 : term120 = True.
Proof. exact (EQ_MP (@lem1488233) (@lem1488231)). Qed.
Lemma lem1488235 : term119 = True.
Proof. exact (TRANS (@lem1488230) (@lem1488234)). Qed.
Lemma lem1488236 : True = term119.
Proof. exact (SYM (@lem1488235)). Qed.
Lemma lem1488237 : term119.
Proof. exact (EQ_MP (@lem1488236) (@lem0)). Qed.
Lemma lem1488238 (y : real) (h1 : term153 y) : term142 y.
Proof. exact (conj (@lem1488237) (@lem1488227 y h1)). Qed.
Lemma lem1488240 (x : real) (y : real) : term123 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488241 (y : real) : term143 y.
Proof. exact (@lem1488240 term125 (term25 y)). Qed.
Lemma lem1488242 (y : real) (h1 : term153 y) : term144 y.
Proof. exact (@lem1488241 y (@lem1488238 y h1)). Qed.
Lemma lem1488243 (y : real) : (term145 y) = (term25 y).
Proof. exact (@lem1483460 (term25 y)). Qed.
Lemma lem1488244 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488245 (y : real) : (term146 y) = (term49 y).
Proof. exact (MK_COMB (@lem1488244) (@lem1488243 y)). Qed.
Lemma lem1488246 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488247 (y : real) : (term144 y) = (term51 y).
Proof. exact (MK_COMB (@lem1488245 y) (@lem1488246)). Qed.
Lemma lem1488248 (y : real) (h1 : term153 y) : term51 y.
Proof. exact (EQ_MP (@lem1488247 y) (@lem1488242 y h1)). Qed.
Lemma lem1488250 (y : real) : term129 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488251 (y : real) (h1 : term153 y) : term130 y.
Proof. exact (@lem1488250 y (@lem1488226 y h1)). Qed.
Lemma lem1488252 (y : real) (h1 : term153 y) : term147 y.
Proof. exact (@lem1488251 y h1 term125). Qed.
Lemma lem1488253 (y : real) : (term147 y) = ((term127 y) = term2).
Proof. exact (eq_refl (term147 y)). Qed.
Lemma lem1488254 (y : real) (h1 : term153 y) : (term127 y) = term2.
Proof. exact (EQ_MP (@lem1488253 y) (@lem1488252 y h1)). Qed.
Lemma lem1488255 (y : real) : (term127 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1488256 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1488257 (y : real) : (term148 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1488256) (@lem1488255 y)). Qed.
Lemma lem1488258 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488259 (y : real) : ((term127 y) = term2) = (y = term2).
Proof. exact (MK_COMB (@lem1488257 y) (@lem1488258)). Qed.
Lemma lem1488260 (y : real) (h1 : term153 y) : y = term2.
Proof. exact (EQ_MP (@lem1488259 y) (@lem1488254 y h1)). Qed.
Lemma lem1488261 (y : real) (h1 : term153 y) : term141 y.
Proof. exact (conj (@lem1488260 y h1) (@lem1488248 y h1)). Qed.
Lemma lem1488263 (x : real) (y : real) : term133 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488264 (y : real) : term149 y.
Proof. exact (@lem1488263 y (term25 y)). Qed.
Lemma lem1488265 (y : real) (h1 : term153 y) : term150 y.
Proof. exact (@lem1488264 y (@lem1488261 y h1)). Qed.
Lemma lem1488266 (y : real) : (term26 y) = (term27 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1488268 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488269 : term30 = term2.
Proof. exact (@lem1488268 term31). Qed.
Lemma lem1488270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488271 : term32 = term33.
Proof. exact (MK_COMB (@lem1488270) (@lem1488269)). Qed.
Lemma lem1488272 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488273 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488271) (@lem1488272 y)). Qed.
Lemma lem1488274 (y : real) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem1488266 y) (@lem1488273 y)). Qed.
Lemma lem1488275 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488276 (y : real) : (term26 y) = term2.
Proof. exact (TRANS (@lem1488274 y) (@lem1488275 y)). Qed.
Lemma lem1488277 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488278 (y : real) : (term151 y) = term138.
Proof. exact (MK_COMB (@lem1488277) (@lem1488276 y)). Qed.
Lemma lem1488279 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488280 (y : real) : (term150 y) = term139.
Proof. exact (MK_COMB (@lem1488278 y) (@lem1488279)). Qed.
Lemma lem1488281 (y : real) (h1 : term153 y) : term139.
Proof. exact (EQ_MP (@lem1488280 y) (@lem1488265 y h1)). Qed.
Lemma lem1488283 (n : nat) (m : nat) : (term118 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488284 : term139 = term140.
Proof. exact (@lem1488283 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1488285 : term140 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1488286 : term139 = False.
Proof. exact (TRANS (@lem1488284) (@lem1488285)). Qed.
Lemma lem1488287 (y : real) (h1 : term153 y) : False.
Proof. exact (EQ_MP (@lem1488286) (@lem1488281 y h1)). Qed.
Lemma lem1488288 (y : real) (h1 : term111 y) : False.
Proof. exact (or_elim (@lem1488161 y h1) (fun h0 : term152 y => @lem1488224 y h0) (fun h0 : term153 y => @lem1488287 y h0)). Qed.
Lemma lem1488289 (y : real) (h1 : term114 y) : False.
Proof. exact (or_elim (@lem1488032 y h1) (fun h0 : term112 y => @lem1488160 y h0) (fun h0 : term111 y => @lem1488288 y h0)). Qed.
Lemma lem1488291 (y : real) (h1 : term114 y) : term114 y.
Proof. exact (h1). Qed.
Lemma lem1488292 (y : real) (h1 : term114 y) : (term114 y) = False.
Proof. exact (prop_ext (fun h2 : term114 y => @lem1488289 y h1) (fun h2 : False => @lem1488291 y h1)). Qed.
Lemma lem1488293 (y : real) (h1 : term114 y) : False.
Proof. exact (EQ_MP (@lem1488292 y h1) (@lem1488291 y h1)). Qed.
Lemma lem1488294 (h1 : term116) : term116.
Proof. exact (h1). Qed.
Lemma lem1488295 (h1 : term116) : False.
Proof. exact (ex_elim (@lem1488294 h1) (fun y : real => fun h0 : term115 y => @lem1488293 y h0)). Qed.
Lemma lem1488296 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1488297 (h1 : term13) : term116.
Proof. exact (EQ_MP (@lem1488010) (@lem1488296 h1)). Qed.
Lemma lem1488298 (h1 : term13) : term116 = False.
Proof. exact (prop_ext (fun h2 : term116 => @lem1488295 h2) (fun h2 : False => @lem1488297 h1)). Qed.
Lemma lem1488299 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1488298 h1) (@lem1488297 h1)). Qed.
Lemma lem1488300 : term154.
Proof. exact (fun h0 : term13 => @lem1488299 h0). Qed.
Lemma lem1488301 : term155.
Proof. exact (@lem1386578 term156). Qed.
Lemma lem1488302 : term156.
Proof. exact (@lem1488301 (@lem1488300)). Qed.

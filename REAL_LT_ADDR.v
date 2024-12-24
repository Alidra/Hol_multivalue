Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADDR_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483486_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1510647 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 (term2 x y) (term3 y)). Qed.
Lemma lem1510648 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1510649 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1510648 (term8 x)). Qed.
Lemma lem1510650 (x : real) (y : real) : (term9 x y) = ((term2 x y) = (term3 y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1510651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1510652 (x : real) (y : real) : (term10 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1510651) (@lem1510650 x y)). Qed.
Lemma lem1510653 (x : real) (y : real) : (term10 x y) = (term1 x y).
Proof. exact (TRANS (@lem1510652 x y) (@lem1510647 x y)). Qed.
Lemma lem1510654 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1510653 x y)). Qed.
Lemma lem1510655 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510656 (x : real) : (term7 x) = (term13 x).
Proof. exact (MK_COMB (@lem1510655) (@lem1510654 x)). Qed.
Lemma lem1510657 (x : real) : (term6 x) = (term13 x).
Proof. exact (TRANS (@lem1510649 x) (@lem1510656 x)). Qed.
Lemma lem1510658 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1510659 : term14 = term15.
Proof. exact (@lem1510658 term16). Qed.
Lemma lem1510660 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1510661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1510662 (x : real) : (term19 x) = (term6 x).
Proof. exact (MK_COMB (@lem1510661) (@lem1510660 x)). Qed.
Lemma lem1510663 (x : real) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem1510662 x) (@lem1510657 x)). Qed.
Lemma lem1510664 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1510663 x)). Qed.
Lemma lem1510665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510666 : term15 = term22.
Proof. exact (MK_COMB (@lem1510665) (@lem1510664)). Qed.
Lemma lem1510668 : term14 = term22.
Proof. exact (TRANS (@lem1510659) (@lem1510666)). Qed.
Lemma lem1510685 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1510686 (x : real) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1510685 x y)). Qed.
Lemma lem1510687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510688 (x : real) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem1510687) (@lem1510686 x)). Qed.
Lemma lem1510689 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1510688 x)). Qed.
Lemma lem1510690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510691 : term22 = term22.
Proof. exact (MK_COMB (@lem1510690) (@lem1510689)). Qed.
Lemma lem1510692 : term14 = term22.
Proof. exact (TRANS (@lem1510668) (@lem1510691)). Qed.
Lemma lem1510693 (y : real) (x : real) : (term2 x y) = (term23 y x).
Proof. exact (@lem1483521 (real_add x y) x). Qed.
Lemma lem1510705 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (@lem1483519 (real_add x y) x). Qed.
Lemma lem1510709 (x : real) (y : real) : (term25 y x) = (term26 x y).
Proof. exact (@lem1483486 x (term27 x) y). Qed.
Lemma lem1510710 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1510712 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510713 : term33 = term32.
Proof. exact (@lem1510712 term34). Qed.
Lemma lem1510714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510715 : term35 = term36.
Proof. exact (MK_COMB (@lem1510714) (@lem1510713)). Qed.
Lemma lem1510716 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1510717 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1510715) (@lem1510716 x)). Qed.
Lemma lem1510718 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1510710 x) (@lem1510717 x)). Qed.
Lemma lem1510719 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1510720 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1510718 x) (@lem1510719 x)). Qed.
Lemma lem1510721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1510722 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1510721) (@lem1510720 x)). Qed.
Lemma lem1510723 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1510724 (x : real) (y : real) : (term26 x y) = (term40 y).
Proof. exact (MK_COMB (@lem1510722 x) (@lem1510723 y)). Qed.
Lemma lem1510725 (x : real) (y : real) : (term25 y x) = (term40 y).
Proof. exact (TRANS (@lem1510709 x y) (@lem1510724 x y)). Qed.
Lemma lem1510726 (y : real) : (term40 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1510728 (x : real) (y : real) : (term25 y x) = y.
Proof. exact (TRANS (@lem1510725 x y) (@lem1510726 y)). Qed.
Lemma lem1510730 (x : real) (y : real) : (term24 y x) = y.
Proof. exact (TRANS (@lem1510705 y x) (@lem1510728 x y)). Qed.
Lemma lem1510731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510732 (x : real) (y : real) : (term41 y x) = (real_gt y).
Proof. exact (MK_COMB (@lem1510731) (@lem1510730 x y)). Qed.
Lemma lem1510733 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510734 (x : real) (y : real) : (term23 y x) = (term42 y).
Proof. exact (MK_COMB (@lem1510732 x y) (@lem1510733)). Qed.
Lemma lem1510735 (x : real) (y : real) : (term2 x y) = (term42 y).
Proof. exact (TRANS (@lem1510693 y x) (@lem1510734 x y)). Qed.
Lemma lem1510736 (y : real) : (term43 y) = (term44 y).
Proof. exact (@lem1483531 term32 y). Qed.
Lemma lem1510742 (y : real) : (term45 y) = (term46 y).
Proof. exact (@lem1483519 term32 y). Qed.
Lemma lem1510747 (y : real) : (term46 y) = (term27 y).
Proof. exact (@lem1483448 (term27 y)). Qed.
Lemma lem1510749 (y : real) : (term45 y) = (term27 y).
Proof. exact (TRANS (@lem1510742 y) (@lem1510747 y)). Qed.
Lemma lem1510750 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510751 (y : real) : (term47 y) = (term48 y).
Proof. exact (MK_COMB (@lem1510750) (@lem1510749 y)). Qed.
Lemma lem1510752 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510753 (y : real) : (term44 y) = (term49 y).
Proof. exact (MK_COMB (@lem1510751 y) (@lem1510752)). Qed.
Lemma lem1510754 (y : real) : (term43 y) = (term49 y).
Proof. exact (TRANS (@lem1510736 y) (@lem1510753 y)). Qed.
Lemma lem1510755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1510756 (x : real) (y : real) : (term50 x y) = (term51 y).
Proof. exact (MK_COMB (@lem1510755) (@lem1510735 x y)). Qed.
Lemma lem1510757 (x : real) (y : real) : (term52 x y) = (term53 y).
Proof. exact (MK_COMB (@lem1510756 x y) (@lem1510754 y)). Qed.
Lemma lem1510758 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem1483531 x (real_add x y)). Qed.
Lemma lem1510770 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (@lem1483519 x (real_add x y)). Qed.
Lemma lem1510777 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483508 x term30 y). Qed.
Lemma lem1510778 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1510779 (x : real) (y : real) : (term57 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1510778 x) (@lem1510777 x y)). Qed.
Lemma lem1510780 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (@lem1483490 x (term27 x) (term27 y)). Qed.
Lemma lem1510781 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1510783 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1510784 : term33 = term32.
Proof. exact (@lem1510783 term34). Qed.
Lemma lem1510785 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1510786 : term35 = term36.
Proof. exact (MK_COMB (@lem1510785) (@lem1510784)). Qed.
Lemma lem1510787 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1510788 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1510786) (@lem1510787 x)). Qed.
Lemma lem1510789 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1510781 x) (@lem1510788 x)). Qed.
Lemma lem1510790 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1510791 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1510789 x) (@lem1510790 x)). Qed.
Lemma lem1510792 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1510793 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1510792) (@lem1510791 x)). Qed.
Lemma lem1510794 (y : real) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1510795 (x : real) (y : real) : (term61 x y) = (term46 y).
Proof. exact (MK_COMB (@lem1510793 x) (@lem1510794 y)). Qed.
Lemma lem1510796 (x : real) (y : real) : (term60 x y) = (term46 y).
Proof. exact (TRANS (@lem1510780 x y) (@lem1510795 x y)). Qed.
Lemma lem1510797 (y : real) : (term46 y) = (term27 y).
Proof. exact (@lem1483448 (term27 y)). Qed.
Lemma lem1510798 (x : real) (y : real) : (term60 x y) = (term27 y).
Proof. exact (TRANS (@lem1510796 x y) (@lem1510797 y)). Qed.
Lemma lem1510799 (x : real) (y : real) : (term57 x y) = (term27 y).
Proof. exact (TRANS (@lem1510779 x y) (@lem1510798 x y)). Qed.
Lemma lem1510801 (x : real) (y : real) : (term56 x y) = (term27 y).
Proof. exact (TRANS (@lem1510770 x y) (@lem1510799 x y)). Qed.
Lemma lem1510802 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1510803 (x : real) (y : real) : (term62 x y) = (term48 y).
Proof. exact (MK_COMB (@lem1510802) (@lem1510801 x y)). Qed.
Lemma lem1510804 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510805 (x : real) (y : real) : (term55 x y) = (term49 y).
Proof. exact (MK_COMB (@lem1510803 x y) (@lem1510804)). Qed.
Lemma lem1510806 (x : real) (y : real) : (term54 x y) = (term49 y).
Proof. exact (TRANS (@lem1510758 x y) (@lem1510805 x y)). Qed.
Lemma lem1510807 (y : real) : (term3 y) = (term63 y).
Proof. exact (@lem1483521 y term32). Qed.
Lemma lem1510813 (y : real) : (term64 y) = (term65 y).
Proof. exact (@lem1483519 y term32). Qed.
Lemma lem1510815 (x : nat) : (term66 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1510816 : term67 = term32.
Proof. exact (@lem1510815 term34). Qed.
Lemma lem1510817 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1510818 (y : real) : (term65 y) = (term68 y).
Proof. exact (MK_COMB (@lem1510817 y) (@lem1510816)). Qed.
Lemma lem1510819 (y : real) : (term68 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1510820 (y : real) : (term65 y) = y.
Proof. exact (TRANS (@lem1510818 y) (@lem1510819 y)). Qed.
Lemma lem1510822 (y : real) : (term64 y) = y.
Proof. exact (TRANS (@lem1510813 y) (@lem1510820 y)). Qed.
Lemma lem1510823 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1510824 (y : real) : (term69 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1510823) (@lem1510822 y)). Qed.
Lemma lem1510825 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1510826 (y : real) : (term63 y) = (term42 y).
Proof. exact (MK_COMB (@lem1510824 y) (@lem1510825)). Qed.
Lemma lem1510827 (y : real) : (term3 y) = (term42 y).
Proof. exact (TRANS (@lem1510807 y) (@lem1510826 y)). Qed.
Lemma lem1510828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1510829 (x : real) (y : real) : (term70 x y) = (term71 y).
Proof. exact (MK_COMB (@lem1510828) (@lem1510806 x y)). Qed.
Lemma lem1510830 (x : real) (y : real) : (term72 x y) = (term73 y).
Proof. exact (MK_COMB (@lem1510829 x y) (@lem1510827 y)). Qed.
Lemma lem1510831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510832 (x : real) (y : real) : (term74 x y) = (term75 y).
Proof. exact (MK_COMB (@lem1510831) (@lem1510757 x y)). Qed.
Lemma lem1510833 (x : real) (y : real) : (term1 x y) = (term76 y).
Proof. exact (MK_COMB (@lem1510832 x y) (@lem1510830 x y)). Qed.
Lemma lem1510834 (x : real) : (term12 x) = term77.
Proof. exact (fun_ext (fun y : real => @lem1510833 x y)). Qed.
Lemma lem1510835 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510836 (x : real) : (term13 x) = term78.
Proof. exact (MK_COMB (@lem1510835) (@lem1510834 x)). Qed.
Lemma lem1510837 : term21 = term79.
Proof. exact (fun_ext (fun x : real => @lem1510836 x)). Qed.
Lemma lem1510838 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510839 : term22 = term80.
Proof. exact (MK_COMB (@lem1510838) (@lem1510837)). Qed.
Lemma lem1510840 : term14 = term80.
Proof. exact (TRANS (@lem1510692) (@lem1510839)). Qed.
Lemma lem1510842 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1510843 (t : Prop) : (term82 t) = t.
Proof. exact (@lem1510842 real t). Qed.
Lemma lem1510844 : term80 = term78.
Proof. exact (@lem1510843 term78). Qed.
Lemma lem1510846 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1510847 (P : real -> Prop) (Q : real -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem1510846 real P Q). Qed.
Lemma lem1510848 : term87 = term88.
Proof. exact (@lem1510847 term89 term90). Qed.
Lemma lem1510849 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1510850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510851 (y : real) : (term92 y) = (term75 y).
Proof. exact (MK_COMB (@lem1510850) (@lem1510849 y)). Qed.
Lemma lem1510852 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1510853 (y : real) : (term94 y) = (term76 y).
Proof. exact (MK_COMB (@lem1510851 y) (@lem1510852 y)). Qed.
Lemma lem1510854 : term95 = term77.
Proof. exact (fun_ext (fun y : real => @lem1510853 y)). Qed.
Lemma lem1510855 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510856 : term87 = term78.
Proof. exact (MK_COMB (@lem1510855) (@lem1510854)). Qed.
Lemma lem1510857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510858 : term96 = term97.
Proof. exact (MK_COMB (@lem1510857) (@lem1510856)). Qed.
Lemma lem1510859 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1510860 : term98 = term89.
Proof. exact (fun_ext (fun y : real => @lem1510859 y)). Qed.
Lemma lem1510861 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510862 : term99 = term100.
Proof. exact (MK_COMB (@lem1510861) (@lem1510860)). Qed.
Lemma lem1510863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510864 : term101 = term102.
Proof. exact (MK_COMB (@lem1510863) (@lem1510862)). Qed.
Lemma lem1510865 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1510866 : term103 = term90.
Proof. exact (fun_ext (fun y : real => @lem1510865 y)). Qed.
Lemma lem1510867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510868 : term104 = term105.
Proof. exact (MK_COMB (@lem1510867) (@lem1510866)). Qed.
Lemma lem1510869 : term88 = term106.
Proof. exact (MK_COMB (@lem1510864) (@lem1510868)). Qed.
Lemma lem1510870 : (term87 = term88) = (term78 = term106).
Proof. exact (MK_COMB (@lem1510858) (@lem1510869)). Qed.
Lemma lem1510871 : term78 = term106.
Proof. exact (EQ_MP (@lem1510870) (@lem1510848)). Qed.
Lemma lem1510872 : term80 = term106.
Proof. exact (TRANS (@lem1510844) (@lem1510871)). Qed.
Lemma lem1510970 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term83 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1510971 (P : real -> Prop) (Q : real -> Prop) : (term86 P Q) = (term85 P Q).
Proof. exact (@lem1510970 real P Q). Qed.
Lemma lem1510972 : term88 = term87.
Proof. exact (@lem1510971 term89 term90). Qed.
Lemma lem1510973 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1510974 : term98 = term89.
Proof. exact (fun_ext (fun y : real => @lem1510973 y)). Qed.
Lemma lem1510975 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510976 : term99 = term100.
Proof. exact (MK_COMB (@lem1510975) (@lem1510974)). Qed.
Lemma lem1510977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510978 : term101 = term102.
Proof. exact (MK_COMB (@lem1510977) (@lem1510976)). Qed.
Lemma lem1510979 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1510980 : term103 = term90.
Proof. exact (fun_ext (fun y : real => @lem1510979 y)). Qed.
Lemma lem1510981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510982 : term104 = term105.
Proof. exact (MK_COMB (@lem1510981) (@lem1510980)). Qed.
Lemma lem1510983 : term88 = term106.
Proof. exact (MK_COMB (@lem1510978) (@lem1510982)). Qed.
Lemma lem1510984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1510985 : term107 = term108.
Proof. exact (MK_COMB (@lem1510984) (@lem1510983)). Qed.
Lemma lem1510986 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1510987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1510988 (y : real) : (term92 y) = (term75 y).
Proof. exact (MK_COMB (@lem1510987) (@lem1510986 y)). Qed.
Lemma lem1510989 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1510990 (y : real) : (term94 y) = (term76 y).
Proof. exact (MK_COMB (@lem1510988 y) (@lem1510989 y)). Qed.
Lemma lem1510991 : term95 = term77.
Proof. exact (fun_ext (fun y : real => @lem1510990 y)). Qed.
Lemma lem1510992 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1510993 : term87 = term78.
Proof. exact (MK_COMB (@lem1510992) (@lem1510991)). Qed.
Lemma lem1510994 : (term88 = term87) = (term106 = term78).
Proof. exact (MK_COMB (@lem1510985) (@lem1510993)). Qed.
Lemma lem1510995 : term106 = term78.
Proof. exact (EQ_MP (@lem1510994) (@lem1510972)). Qed.
Lemma lem1510996 : term80 = term78.
Proof. exact (TRANS (@lem1510872) (@lem1510995)). Qed.
Lemma lem1510999 : term14 = term78.
Proof. exact (TRANS (@lem1510840) (@lem1510996)). Qed.
Lemma lem1511016 (y : real) : (term76 y) = (term76 y).
Proof. exact (eq_refl (term76 y)). Qed.
Lemma lem1511017 : term77 = term77.
Proof. exact (fun_ext (fun y : real => @lem1511016 y)). Qed.
Lemma lem1511018 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511019 : term78 = term78.
Proof. exact (MK_COMB (@lem1511018) (@lem1511017)). Qed.
Lemma lem1511020 : term14 = term78.
Proof. exact (TRANS (@lem1510999) (@lem1511019)). Qed.
Lemma lem1511030 (y : real) (h1 : term76 y) : term76 y.
Proof. exact (h1). Qed.
Lemma lem1511031 (y : real) (h1 : term53 y) : term53 y.
Proof. exact (h1). Qed.
Lemma lem1511032 (y : real) (h1 : term53 y) : term49 y.
Proof. exact (proj2 (@lem1511031 y h1)). Qed.
Lemma lem1511033 (y : real) (h1 : term53 y) : term42 y.
Proof. exact (proj1 (@lem1511031 y h1)). Qed.
Lemma lem1511035 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511036 : term110 = term111.
Proof. exact (@lem1511035 (NUMERAL 0) term34). Qed.
Lemma lem1511037 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511038 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511039 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1511038 h1) (fun h1 : term111 = True => @lem1511037)). Qed.
Lemma lem1511040 : term111 = True.
Proof. exact (EQ_MP (@lem1511039) (@lem1511037)). Qed.
Lemma lem1511041 : term110 = True.
Proof. exact (TRANS (@lem1511036) (@lem1511040)). Qed.
Lemma lem1511042 : True = term110.
Proof. exact (SYM (@lem1511041)). Qed.
Lemma lem1511043 : term110.
Proof. exact (EQ_MP (@lem1511042) (@lem0)). Qed.
Lemma lem1511044 (y : real) (h1 : term53 y) : term113 y.
Proof. exact (conj (@lem1511043) (@lem1511032 y h1)). Qed.
Lemma lem1511046 (x : real) (y : real) : term114 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1511047 (y : real) : term115 y.
Proof. exact (@lem1511046 term116 (term27 y)). Qed.
Lemma lem1511048 (y : real) (h1 : term53 y) : term117 y.
Proof. exact (@lem1511047 y (@lem1511044 y h1)). Qed.
Lemma lem1511049 (y : real) : (term118 y) = (term27 y).
Proof. exact (@lem1483460 (term27 y)). Qed.
Lemma lem1511050 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511051 (y : real) : (term119 y) = (term48 y).
Proof. exact (MK_COMB (@lem1511050) (@lem1511049 y)). Qed.
Lemma lem1511052 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511053 (y : real) : (term117 y) = (term49 y).
Proof. exact (MK_COMB (@lem1511051 y) (@lem1511052)). Qed.
Lemma lem1511054 (y : real) (h1 : term53 y) : term49 y.
Proof. exact (EQ_MP (@lem1511053 y) (@lem1511048 y h1)). Qed.
Lemma lem1511056 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511057 : term110 = term111.
Proof. exact (@lem1511056 (NUMERAL 0) term34). Qed.
Lemma lem1511058 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511059 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511060 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1511059 h1) (fun h1 : term111 = True => @lem1511058)). Qed.
Lemma lem1511061 : term111 = True.
Proof. exact (EQ_MP (@lem1511060) (@lem1511058)). Qed.
Lemma lem1511062 : term110 = True.
Proof. exact (TRANS (@lem1511057) (@lem1511061)). Qed.
Lemma lem1511063 : True = term110.
Proof. exact (SYM (@lem1511062)). Qed.
Lemma lem1511064 : term110.
Proof. exact (EQ_MP (@lem1511063) (@lem0)). Qed.
Lemma lem1511065 (y : real) (h1 : term53 y) : term120 y.
Proof. exact (conj (@lem1511064) (@lem1511033 y h1)). Qed.
Lemma lem1511067 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1511068 (y : real) : term122 y.
Proof. exact (@lem1511067 term116 y). Qed.
Lemma lem1511069 (y : real) (h1 : term53 y) : term123 y.
Proof. exact (@lem1511068 y (@lem1511065 y h1)). Qed.
Lemma lem1511070 (y : real) : (term124 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1511071 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511072 (y : real) : (term125 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1511071) (@lem1511070 y)). Qed.
Lemma lem1511073 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511074 (y : real) : (term123 y) = (term42 y).
Proof. exact (MK_COMB (@lem1511072 y) (@lem1511073)). Qed.
Lemma lem1511075 (y : real) (h1 : term53 y) : term42 y.
Proof. exact (EQ_MP (@lem1511074 y) (@lem1511069 y h1)). Qed.
Lemma lem1511076 (y : real) (h1 : term53 y) : term53 y.
Proof. exact (conj (@lem1511075 y h1) (@lem1511054 y h1)). Qed.
Lemma lem1511078 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1511079 (y : real) : term127 y.
Proof. exact (@lem1511078 y (term27 y)). Qed.
Lemma lem1511080 (y : real) (h1 : term53 y) : term128 y.
Proof. exact (@lem1511079 y (@lem1511076 y h1)). Qed.
Lemma lem1511081 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1511083 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511084 : term33 = term32.
Proof. exact (@lem1511083 term34). Qed.
Lemma lem1511085 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511086 : term35 = term36.
Proof. exact (MK_COMB (@lem1511085) (@lem1511084)). Qed.
Lemma lem1511087 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511088 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1511086) (@lem1511087 y)). Qed.
Lemma lem1511089 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1511081 y) (@lem1511088 y)). Qed.
Lemma lem1511090 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1511091 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1511089 y) (@lem1511090 y)). Qed.
Lemma lem1511092 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511093 (y : real) : (term129 y) = term130.
Proof. exact (MK_COMB (@lem1511092) (@lem1511091 y)). Qed.
Lemma lem1511094 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511095 (y : real) : (term128 y) = term131.
Proof. exact (MK_COMB (@lem1511093 y) (@lem1511094)). Qed.
Lemma lem1511096 (y : real) (h1 : term53 y) : term131.
Proof. exact (EQ_MP (@lem1511095 y) (@lem1511080 y h1)). Qed.
Lemma lem1511098 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511099 : term131 = term132.
Proof. exact (@lem1511098 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1511100 : term132 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1511101 : term131 = False.
Proof. exact (TRANS (@lem1511099) (@lem1511100)). Qed.
Lemma lem1511102 (y : real) (h1 : term53 y) : False.
Proof. exact (EQ_MP (@lem1511101) (@lem1511096 y h1)). Qed.
Lemma lem1511103 (y : real) (h1 : term73 y) : term73 y.
Proof. exact (h1). Qed.
Lemma lem1511104 (y : real) (h1 : term73 y) : term42 y.
Proof. exact (proj2 (@lem1511103 y h1)). Qed.
Lemma lem1511105 (y : real) (h1 : term73 y) : term49 y.
Proof. exact (proj1 (@lem1511103 y h1)). Qed.
Lemma lem1511107 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511108 : term110 = term111.
Proof. exact (@lem1511107 (NUMERAL 0) term34). Qed.
Lemma lem1511109 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511110 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511111 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1511110 h1) (fun h1 : term111 = True => @lem1511109)). Qed.
Lemma lem1511112 : term111 = True.
Proof. exact (EQ_MP (@lem1511111) (@lem1511109)). Qed.
Lemma lem1511113 : term110 = True.
Proof. exact (TRANS (@lem1511108) (@lem1511112)). Qed.
Lemma lem1511114 : True = term110.
Proof. exact (SYM (@lem1511113)). Qed.
Lemma lem1511115 : term110.
Proof. exact (EQ_MP (@lem1511114) (@lem0)). Qed.
Lemma lem1511116 (y : real) (h1 : term73 y) : term113 y.
Proof. exact (conj (@lem1511115) (@lem1511105 y h1)). Qed.
Lemma lem1511118 (x : real) (y : real) : term114 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1511119 (y : real) : term115 y.
Proof. exact (@lem1511118 term116 (term27 y)). Qed.
Lemma lem1511120 (y : real) (h1 : term73 y) : term117 y.
Proof. exact (@lem1511119 y (@lem1511116 y h1)). Qed.
Lemma lem1511121 (y : real) : (term118 y) = (term27 y).
Proof. exact (@lem1483460 (term27 y)). Qed.
Lemma lem1511122 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511123 (y : real) : (term119 y) = (term48 y).
Proof. exact (MK_COMB (@lem1511122) (@lem1511121 y)). Qed.
Lemma lem1511124 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511125 (y : real) : (term117 y) = (term49 y).
Proof. exact (MK_COMB (@lem1511123 y) (@lem1511124)). Qed.
Lemma lem1511126 (y : real) (h1 : term73 y) : term49 y.
Proof. exact (EQ_MP (@lem1511125 y) (@lem1511120 y h1)). Qed.
Lemma lem1511128 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511129 : term110 = term111.
Proof. exact (@lem1511128 (NUMERAL 0) term34). Qed.
Lemma lem1511130 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511131 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511132 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1511131 h1) (fun h1 : term111 = True => @lem1511130)). Qed.
Lemma lem1511133 : term111 = True.
Proof. exact (EQ_MP (@lem1511132) (@lem1511130)). Qed.
Lemma lem1511134 : term110 = True.
Proof. exact (TRANS (@lem1511129) (@lem1511133)). Qed.
Lemma lem1511135 : True = term110.
Proof. exact (SYM (@lem1511134)). Qed.
Lemma lem1511136 : term110.
Proof. exact (EQ_MP (@lem1511135) (@lem0)). Qed.
Lemma lem1511137 (y : real) (h1 : term73 y) : term120 y.
Proof. exact (conj (@lem1511136) (@lem1511104 y h1)). Qed.
Lemma lem1511139 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1511140 (y : real) : term122 y.
Proof. exact (@lem1511139 term116 y). Qed.
Lemma lem1511141 (y : real) (h1 : term73 y) : term123 y.
Proof. exact (@lem1511140 y (@lem1511137 y h1)). Qed.
Lemma lem1511142 (y : real) : (term124 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1511143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511144 (y : real) : (term125 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1511143) (@lem1511142 y)). Qed.
Lemma lem1511145 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511146 (y : real) : (term123 y) = (term42 y).
Proof. exact (MK_COMB (@lem1511144 y) (@lem1511145)). Qed.
Lemma lem1511147 (y : real) (h1 : term73 y) : term42 y.
Proof. exact (EQ_MP (@lem1511146 y) (@lem1511141 y h1)). Qed.
Lemma lem1511148 (y : real) (h1 : term73 y) : term53 y.
Proof. exact (conj (@lem1511147 y h1) (@lem1511126 y h1)). Qed.
Lemma lem1511150 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1511151 (y : real) : term127 y.
Proof. exact (@lem1511150 y (term27 y)). Qed.
Lemma lem1511152 (y : real) (h1 : term73 y) : term128 y.
Proof. exact (@lem1511151 y (@lem1511148 y h1)). Qed.
Lemma lem1511153 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1511155 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511156 : term33 = term32.
Proof. exact (@lem1511155 term34). Qed.
Lemma lem1511157 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511158 : term35 = term36.
Proof. exact (MK_COMB (@lem1511157) (@lem1511156)). Qed.
Lemma lem1511159 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511160 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1511158) (@lem1511159 y)). Qed.
Lemma lem1511161 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1511153 y) (@lem1511160 y)). Qed.
Lemma lem1511162 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1511163 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1511161 y) (@lem1511162 y)). Qed.
Lemma lem1511164 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511165 (y : real) : (term129 y) = term130.
Proof. exact (MK_COMB (@lem1511164) (@lem1511163 y)). Qed.
Lemma lem1511166 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511167 (y : real) : (term128 y) = term131.
Proof. exact (MK_COMB (@lem1511165 y) (@lem1511166)). Qed.
Lemma lem1511168 (y : real) (h1 : term73 y) : term131.
Proof. exact (EQ_MP (@lem1511167 y) (@lem1511152 y h1)). Qed.
Lemma lem1511170 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511171 : term131 = term132.
Proof. exact (@lem1511170 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1511172 : term132 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1511173 : term131 = False.
Proof. exact (TRANS (@lem1511171) (@lem1511172)). Qed.
Lemma lem1511174 (y : real) (h1 : term73 y) : False.
Proof. exact (EQ_MP (@lem1511173) (@lem1511168 y h1)). Qed.
Lemma lem1511175 (y : real) (h1 : term76 y) : False.
Proof. exact (or_elim (@lem1511030 y h1) (fun h0 : term53 y => @lem1511102 y h0) (fun h0 : term73 y => @lem1511174 y h0)). Qed.
Lemma lem1511177 (y : real) (h1 : term76 y) : term76 y.
Proof. exact (h1). Qed.
Lemma lem1511178 (y : real) (h1 : term76 y) : (term76 y) = False.
Proof. exact (prop_ext (fun h2 : term76 y => @lem1511175 y h1) (fun h2 : False => @lem1511177 y h1)). Qed.
Lemma lem1511179 (y : real) (h1 : term76 y) : False.
Proof. exact (EQ_MP (@lem1511178 y h1) (@lem1511177 y h1)). Qed.
Lemma lem1511180 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem1511181 (h1 : term78) : False.
Proof. exact (ex_elim (@lem1511180 h1) (fun y : real => fun h0 : term77 y => @lem1511179 y h0)). Qed.
Lemma lem1511182 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1511183 (h1 : term14) : term78.
Proof. exact (EQ_MP (@lem1511020) (@lem1511182 h1)). Qed.
Lemma lem1511184 (h1 : term14) : term78 = False.
Proof. exact (prop_ext (fun h2 : term78 => @lem1511181 h2) (fun h2 : False => @lem1511183 h1)). Qed.
Lemma lem1511185 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1511184 h1) (@lem1511183 h1)). Qed.
Lemma lem1511186 : term133.
Proof. exact (fun h0 : term14 => @lem1511185 h0). Qed.
Lemma lem1511187 : term134.
Proof. exact (@lem1386578 term135). Qed.
Lemma lem1511188 : term135.
Proof. exact (@lem1511187 (@lem1511186)). Qed.

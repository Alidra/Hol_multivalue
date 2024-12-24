Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_NZ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482678_spec.
Require Import thm1482981_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Lemma lem1533628 (x : real) : (term0 x) = (x = term1).
Proof. exact (@lem16933 (x = term1)). Qed.
Lemma lem1533630 (x : real) : (term2 x) = (term2 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1533631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533632 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1533631) (@lem1533628 x)). Qed.
Lemma lem1533633 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1533632 x) (@lem1533630 x)). Qed.
Lemma lem1533638 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1533639 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1533638 x) (@lem1533633 x)). Qed.
Lemma lem1533640 (x : real) : (term10 x) = (term8 x).
Proof. exact (@lem17646 (term11 x) (term2 x)). Qed.
Lemma lem1533641 (x : real) : (term10 x) = (term9 x).
Proof. exact (TRANS (@lem1533640 x) (@lem1533639 x)). Qed.
Lemma lem1533642 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1533643 : term14 = term15.
Proof. exact (@lem1533642 term16). Qed.
Lemma lem1533644 (x : real) : (term17 x) = ((term11 x) = (term2 x)).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1533645 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1533646 (x : real) : (term18 x) = (term10 x).
Proof. exact (MK_COMB (@lem1533645) (@lem1533644 x)). Qed.
Lemma lem1533647 (x : real) : (term18 x) = (term9 x).
Proof. exact (TRANS (@lem1533646 x) (@lem1533641 x)). Qed.
Lemma lem1533648 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1533647 x)). Qed.
Lemma lem1533649 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533650 : term15 = term21.
Proof. exact (MK_COMB (@lem1533649) (@lem1533648)). Qed.
Lemma lem1533652 : term14 = term21.
Proof. exact (TRANS (@lem1533643) (@lem1533650)). Qed.
Lemma lem1533669 (x : real) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1533670 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1533669 x)). Qed.
Lemma lem1533671 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533672 : term21 = term21.
Proof. exact (MK_COMB (@lem1533671) (@lem1533670)). Qed.
Lemma lem1533673 : term14 = term21.
Proof. exact (TRANS (@lem1533652) (@lem1533672)). Qed.
Lemma lem1533674 (x : real) : (term11 x) = (term22 x).
Proof. exact (@lem1483554 x term1). Qed.
Lemma lem1533680 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1533682 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533683 : term26 = term1.
Proof. exact (@lem1533682 term27). Qed.
Lemma lem1533684 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533685 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1533684 x) (@lem1533683)). Qed.
Lemma lem1533686 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1533687 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1533685 x) (@lem1533686 x)). Qed.
Lemma lem1533689 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1533680 x) (@lem1533687 x)). Qed.
Lemma lem1533690 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1533691 (x : real) : (term29 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1533690) (@lem1533689 x)). Qed.
Lemma lem1533694 (x : real) : (real_neg x) = (term30 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1533695 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1533696 (x : real) : ((term29 x) = (real_neg x)) = ((term29 x) = (term30 x)).
Proof. exact (MK_COMB (@lem1533695 x) (@lem1533694 x)). Qed.
Lemma lem1533697 (x : real) : (term29 x) = (term30 x).
Proof. exact (EQ_MP (@lem1533696 x) (@lem1533691 x)). Qed.
Lemma lem1533698 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533699 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1533698) (@lem1533697 x)). Qed.
Lemma lem1533700 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533701 (x : real) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1533699 x) (@lem1533700)). Qed.
Lemma lem1533702 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533703 (x : real) : (term36 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1533702) (@lem1533689 x)). Qed.
Lemma lem1533704 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533705 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1533703 x) (@lem1533704)). Qed.
Lemma lem1533706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533707 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1533706) (@lem1533705 x)). Qed.
Lemma lem1533708 (x : real) : (term22 x) = (term41 x).
Proof. exact (MK_COMB (@lem1533707 x) (@lem1533701 x)). Qed.
Lemma lem1533709 (x : real) : (term11 x) = (term41 x).
Proof. exact (TRANS (@lem1533674 x) (@lem1533708 x)). Qed.
Lemma lem1533710 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483531 term1 (real_abs x)). Qed.
Lemma lem1533716 (x : real) : (term44 x) = (term45 x).
Proof. exact (@lem1483519 term1 (real_abs x)). Qed.
Lemma lem1533721 (x : real) : (term45 x) = (term46 x).
Proof. exact (@lem1483448 (term46 x)). Qed.
Lemma lem1533723 (x : real) : (term44 x) = (term46 x).
Proof. exact (TRANS (@lem1533716 x) (@lem1533721 x)). Qed.
Lemma lem1533724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1533725 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem1533724) (@lem1533723 x)). Qed.
Lemma lem1533726 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533727 (x : real) : (term43 x) = (term49 x).
Proof. exact (MK_COMB (@lem1533725 x) (@lem1533726)). Qed.
Lemma lem1533728 (x : real) : (term42 x) = (term49 x).
Proof. exact (TRANS (@lem1533710 x) (@lem1533727 x)). Qed.
Lemma lem1533729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533730 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1533729) (@lem1533709 x)). Qed.
Lemma lem1533731 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1533730 x) (@lem1533728 x)). Qed.
Lemma lem1533732 (x : real) : (x = term1) = ((term23 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1533738 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1533740 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533741 : term26 = term1.
Proof. exact (@lem1533740 term27). Qed.
Lemma lem1533742 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1533743 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1533742 x) (@lem1533741)). Qed.
Lemma lem1533744 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1533745 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1533743 x) (@lem1533744 x)). Qed.
Lemma lem1533747 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1533738 x) (@lem1533745 x)). Qed.
Lemma lem1533748 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1533749 (x : real) : (term54 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1533748) (@lem1533747 x)). Qed.
Lemma lem1533750 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533751 (x : real) : ((term23 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1533749 x) (@lem1533750)). Qed.
Lemma lem1533752 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1533732 x) (@lem1533751 x)). Qed.
Lemma lem1533753 (x : real) : (term2 x) = (term55 x).
Proof. exact (@lem1483521 (real_abs x) term1). Qed.
Lemma lem1533759 (x : real) : (term56 x) = (term57 x).
Proof. exact (@lem1483519 (real_abs x) term1). Qed.
Lemma lem1533761 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1533762 : term26 = term1.
Proof. exact (@lem1533761 term27). Qed.
Lemma lem1533763 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1533764 (x : real) : (term57 x) = (term59 x).
Proof. exact (MK_COMB (@lem1533763 x) (@lem1533762)). Qed.
Lemma lem1533765 (x : real) : (term59 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1533766 (x : real) : (term57 x) = (real_abs x).
Proof. exact (TRANS (@lem1533764 x) (@lem1533765 x)). Qed.
Lemma lem1533768 (x : real) : (term56 x) = (real_abs x).
Proof. exact (TRANS (@lem1533759 x) (@lem1533766 x)). Qed.
Lemma lem1533769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1533770 (x : real) : (term60 x) = (term61 x).
Proof. exact (MK_COMB (@lem1533769) (@lem1533768 x)). Qed.
Lemma lem1533771 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533772 (x : real) : (term55 x) = (term62 x).
Proof. exact (MK_COMB (@lem1533770 x) (@lem1533771)). Qed.
Lemma lem1533773 (x : real) : (term2 x) = (term62 x).
Proof. exact (TRANS (@lem1533753 x) (@lem1533772 x)). Qed.
Lemma lem1533774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1533775 (x : real) : (term4 x) = (term4 x).
Proof. exact (MK_COMB (@lem1533774) (@lem1533752 x)). Qed.
Lemma lem1533776 (x : real) : (term6 x) = (term63 x).
Proof. exact (MK_COMB (@lem1533775 x) (@lem1533773 x)). Qed.
Lemma lem1533777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533778 (x : real) : (term7 x) = (term64 x).
Proof. exact (MK_COMB (@lem1533777) (@lem1533731 x)). Qed.
Lemma lem1533779 (x : real) : (term9 x) = (term65 x).
Proof. exact (MK_COMB (@lem1533778 x) (@lem1533776 x)). Qed.
Lemma lem1533780 : term20 = term66.
Proof. exact (fun_ext (fun x : real => @lem1533779 x)). Qed.
Lemma lem1533781 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533782 : term21 = term67.
Proof. exact (MK_COMB (@lem1533781) (@lem1533780)). Qed.
Lemma lem1533783 : term14 = term67.
Proof. exact (TRANS (@lem1533673) (@lem1533782)). Qed.
Lemma lem1533785 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1533786 (P : real -> Prop) (Q : real -> Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem1533785 real P Q). Qed.
Lemma lem1533787 : term72 = term73.
Proof. exact (@lem1533786 term74 term75). Qed.
Lemma lem1533788 (x : real) : (term76 x) = (term53 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1533789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533790 (x : real) : (term77 x) = (term64 x).
Proof. exact (MK_COMB (@lem1533789) (@lem1533788 x)). Qed.
Lemma lem1533791 (x : real) : (term78 x) = (term63 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1533792 (x : real) : (term79 x) = (term65 x).
Proof. exact (MK_COMB (@lem1533790 x) (@lem1533791 x)). Qed.
Lemma lem1533793 : term80 = term66.
Proof. exact (fun_ext (fun x : real => @lem1533792 x)). Qed.
Lemma lem1533794 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533795 : term72 = term67.
Proof. exact (MK_COMB (@lem1533794) (@lem1533793)). Qed.
Lemma lem1533796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1533797 : term81 = term82.
Proof. exact (MK_COMB (@lem1533796) (@lem1533795)). Qed.
Lemma lem1533798 (x : real) : (term76 x) = (term53 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1533799 : term83 = term74.
Proof. exact (fun_ext (fun x : real => @lem1533798 x)). Qed.
Lemma lem1533800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533801 : term84 = term85.
Proof. exact (MK_COMB (@lem1533800) (@lem1533799)). Qed.
Lemma lem1533802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533803 : term86 = term87.
Proof. exact (MK_COMB (@lem1533802) (@lem1533801)). Qed.
Lemma lem1533804 (x : real) : (term78 x) = (term63 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1533805 : term88 = term75.
Proof. exact (fun_ext (fun x : real => @lem1533804 x)). Qed.
Lemma lem1533806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533807 : term89 = term90.
Proof. exact (MK_COMB (@lem1533806) (@lem1533805)). Qed.
Lemma lem1533808 : term73 = term91.
Proof. exact (MK_COMB (@lem1533803) (@lem1533807)). Qed.
Lemma lem1533809 : (term72 = term73) = (term67 = term91).
Proof. exact (MK_COMB (@lem1533797) (@lem1533808)). Qed.
Lemma lem1533810 : term67 = term91.
Proof. exact (EQ_MP (@lem1533809) (@lem1533787)). Qed.
Lemma lem1533908 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term69 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1533909 (P : real -> Prop) (Q : real -> Prop) : (term71 P Q) = (term70 P Q).
Proof. exact (@lem1533908 real P Q). Qed.
Lemma lem1533910 : term73 = term72.
Proof. exact (@lem1533909 term74 term75). Qed.
Lemma lem1533911 (x : real) : (term76 x) = (term53 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1533912 : term83 = term74.
Proof. exact (fun_ext (fun x : real => @lem1533911 x)). Qed.
Lemma lem1533913 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533914 : term84 = term85.
Proof. exact (MK_COMB (@lem1533913) (@lem1533912)). Qed.
Lemma lem1533915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533916 : term86 = term87.
Proof. exact (MK_COMB (@lem1533915) (@lem1533914)). Qed.
Lemma lem1533917 (x : real) : (term78 x) = (term63 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1533918 : term88 = term75.
Proof. exact (fun_ext (fun x : real => @lem1533917 x)). Qed.
Lemma lem1533919 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533920 : term89 = term90.
Proof. exact (MK_COMB (@lem1533919) (@lem1533918)). Qed.
Lemma lem1533921 : term73 = term91.
Proof. exact (MK_COMB (@lem1533916) (@lem1533920)). Qed.
Lemma lem1533922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1533923 : term92 = term93.
Proof. exact (MK_COMB (@lem1533922) (@lem1533921)). Qed.
Lemma lem1533924 (x : real) : (term76 x) = (term53 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1533925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533926 (x : real) : (term77 x) = (term64 x).
Proof. exact (MK_COMB (@lem1533925) (@lem1533924 x)). Qed.
Lemma lem1533927 (x : real) : (term78 x) = (term63 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1533928 (x : real) : (term79 x) = (term65 x).
Proof. exact (MK_COMB (@lem1533926 x) (@lem1533927 x)). Qed.
Lemma lem1533929 : term80 = term66.
Proof. exact (fun_ext (fun x : real => @lem1533928 x)). Qed.
Lemma lem1533930 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533931 : term72 = term67.
Proof. exact (MK_COMB (@lem1533930) (@lem1533929)). Qed.
Lemma lem1533932 : (term73 = term72) = (term91 = term67).
Proof. exact (MK_COMB (@lem1533923) (@lem1533931)). Qed.
Lemma lem1533933 : term91 = term67.
Proof. exact (EQ_MP (@lem1533932) (@lem1533910)). Qed.
Lemma lem1533934 : term67 = term67.
Proof. exact (TRANS (@lem1533810) (@lem1533933)). Qed.
Lemma lem1533937 : term14 = term67.
Proof. exact (TRANS (@lem1533783) (@lem1533934)). Qed.
Lemma lem1533944 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1533961 (x : real) : (term53 x) = (term94 x).
Proof. exact (@lem19367 (term38 x) (term35 x) (term49 x)). Qed.
Lemma lem1533962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1533963 (x : real) : (term64 x) = (term95 x).
Proof. exact (MK_COMB (@lem1533962) (@lem1533961 x)). Qed.
Lemma lem1533964 (x : real) : (term65 x) = (term96 x).
Proof. exact (MK_COMB (@lem1533963 x) (@lem1533944 x)). Qed.
Lemma lem1533965 : term66 = term97.
Proof. exact (fun_ext (fun x : real => @lem1533964 x)). Qed.
Lemma lem1533966 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1533967 : term67 = term98.
Proof. exact (MK_COMB (@lem1533966) (@lem1533965)). Qed.
Lemma lem1533968 : term14 = term98.
Proof. exact (TRANS (@lem1533937) (@lem1533967)). Qed.
Lemma lem1533970 (x : real) (r : real) : (term99 x r) = (term100 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1533971 (x : real) : (term49 x) = (term101 x).
Proof. exact (@lem1533970 x term1). Qed.
Lemma lem1533978 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1533979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1533980 (x : real) : (term103 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1533979) (@lem1533978 x)). Qed.
Lemma lem1533981 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1533982 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1533980 x) (@lem1533981)). Qed.
Lemma lem1533995 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1533996 (x : real) : (term101 x) = (term107 x).
Proof. exact (MK_COMB (@lem1533995 x) (@lem1533982 x)). Qed.
Lemma lem1533997 (x : real) : (term49 x) = (term107 x).
Proof. exact (TRANS (@lem1533971 x) (@lem1533996 x)). Qed.
Lemma lem1533998 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1534001 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1533998 x) (@lem1533997 x)). Qed.
Lemma lem1534003 (x : real) (r : real) : (term99 x r) = (term100 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1534004 (x : real) : (term49 x) = (term101 x).
Proof. exact (@lem1534003 x term1). Qed.
Lemma lem1534011 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1534013 (x : real) : (term103 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1534012) (@lem1534011 x)). Qed.
Lemma lem1534014 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534015 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1534013 x) (@lem1534014)). Qed.
Lemma lem1534028 (x : real) : (term106 x) = (term106 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1534029 (x : real) : (term101 x) = (term107 x).
Proof. exact (MK_COMB (@lem1534028 x) (@lem1534015 x)). Qed.
Lemma lem1534030 (x : real) : (term49 x) = (term107 x).
Proof. exact (TRANS (@lem1534004 x) (@lem1534029 x)). Qed.
Lemma lem1534031 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1534034 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1534031 x) (@lem1534030 x)). Qed.
Lemma lem1534035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534036 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1534035) (@lem1534001 x)). Qed.
Lemma lem1534037 (x : real) : (term94 x) = (term116 x).
Proof. exact (MK_COMB (@lem1534036 x) (@lem1534034 x)). Qed.
Lemma lem1534039 (x : real) : (term117 x) = (term63 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem1534040 (x : real) : (term63 x) = (term117 x).
Proof. exact (SYM (@lem1534039 x)). Qed.
Lemma lem1534041 (x : real) : (term117 x) = (term118 x).
Proof. exact (@lem1482981 (term119 x) x). Qed.
Lemma lem1534042 (x : real) : (term63 x) = (term118 x).
Proof. exact (TRANS (@lem1534040 x) (@lem1534041 x)). Qed.
Lemma lem1534043 (x : real) : (term120 x) = (term121 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1534044 (x : real) : (term122 x) = (term122 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1534045 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1534044 x) (@lem1534043 x)). Qed.
Lemma lem1534046 (x : real) : (term125 x) = (term126 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1534047 (x : real) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1534048 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1534047 x) (@lem1534046 x)). Qed.
Lemma lem1534049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534050 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1534049) (@lem1534048 x)). Qed.
Lemma lem1534051 (x : real) : (term118 x) = (term132 x).
Proof. exact (MK_COMB (@lem1534050 x) (@lem1534045 x)). Qed.
Lemma lem1534052 (x : real) : (term133 x) = (term133 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1534053 (x : real) : ((term63 x) = (term118 x)) = ((term63 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1534052 x) (@lem1534051 x)). Qed.
Lemma lem1534054 (x : real) : (term63 x) = (term132 x).
Proof. exact (EQ_MP (@lem1534053 x) (@lem1534042 x)). Qed.
Lemma lem1534055 (x : real) : (term105 x) = (term134 x).
Proof. exact (@lem1483527 x term1). Qed.
Lemma lem1534061 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1534063 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534064 : term26 = term1.
Proof. exact (@lem1534063 term27). Qed.
Lemma lem1534065 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1534066 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1534065 x) (@lem1534064)). Qed.
Lemma lem1534067 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1534068 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1534066 x) (@lem1534067 x)). Qed.
Lemma lem1534070 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1534061 x) (@lem1534068 x)). Qed.
Lemma lem1534071 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1534072 (x : real) : (term135 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1534071) (@lem1534070 x)). Qed.
Lemma lem1534073 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534074 (x : real) : (term134 x) = (term105 x).
Proof. exact (MK_COMB (@lem1534072 x) (@lem1534073)). Qed.
Lemma lem1534075 (x : real) : (term105 x) = (term105 x).
Proof. exact (TRANS (@lem1534055 x) (@lem1534074 x)). Qed.
Lemma lem1534076 (x : real) : (x = term1) = ((term23 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1534082 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1534084 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534085 : term26 = term1.
Proof. exact (@lem1534084 term27). Qed.
Lemma lem1534086 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1534087 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1534086 x) (@lem1534085)). Qed.
Lemma lem1534088 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1534089 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1534087 x) (@lem1534088 x)). Qed.
Lemma lem1534091 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1534082 x) (@lem1534089 x)). Qed.
Lemma lem1534092 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1534093 (x : real) : (term54 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1534092) (@lem1534091 x)). Qed.
Lemma lem1534094 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534095 (x : real) : ((term23 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1534093 x) (@lem1534094)). Qed.
Lemma lem1534096 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1534076 x) (@lem1534095 x)). Qed.
Lemma lem1534097 (x : real) : (term38 x) = (term37 x).
Proof. exact (@lem1483525 x term1). Qed.
Lemma lem1534103 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1534105 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534106 : term26 = term1.
Proof. exact (@lem1534105 term27). Qed.
Lemma lem1534107 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1534108 (x : real) : (term24 x) = (term28 x).
Proof. exact (MK_COMB (@lem1534107 x) (@lem1534106)). Qed.
Lemma lem1534109 (x : real) : (term28 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1534110 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1534108 x) (@lem1534109 x)). Qed.
Lemma lem1534112 (x : real) : (term23 x) = x.
Proof. exact (TRANS (@lem1534103 x) (@lem1534110 x)). Qed.
Lemma lem1534113 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534114 (x : real) : (term36 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1534113) (@lem1534112 x)). Qed.
Lemma lem1534115 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534116 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1534114 x) (@lem1534115)). Qed.
Lemma lem1534117 (x : real) : (term38 x) = (term38 x).
Proof. exact (TRANS (@lem1534097 x) (@lem1534116 x)). Qed.
Lemma lem1534118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534119 (x : real) : (term4 x) = (term4 x).
Proof. exact (MK_COMB (@lem1534118) (@lem1534096 x)). Qed.
Lemma lem1534120 (x : real) : (term126 x) = (term126 x).
Proof. exact (MK_COMB (@lem1534119 x) (@lem1534117 x)). Qed.
Lemma lem1534121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534122 (x : real) : (term127 x) = (term127 x).
Proof. exact (MK_COMB (@lem1534121) (@lem1534075 x)). Qed.
Lemma lem1534123 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1534122 x) (@lem1534120 x)). Qed.
Lemma lem1534124 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483525 term1 x). Qed.
Lemma lem1534130 (x : real) : (term138 x) = (term139 x).
Proof. exact (@lem1483519 term1 x). Qed.
Lemma lem1534135 (x : real) : (term139 x) = (term30 x).
Proof. exact (@lem1483448 (term30 x)). Qed.
Lemma lem1534137 (x : real) : (term138 x) = (term30 x).
Proof. exact (TRANS (@lem1534130 x) (@lem1534135 x)). Qed.
Lemma lem1534138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534139 (x : real) : (term140 x) = (term33 x).
Proof. exact (MK_COMB (@lem1534138) (@lem1534137 x)). Qed.
Lemma lem1534140 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534141 (x : real) : (term137 x) = (term35 x).
Proof. exact (MK_COMB (@lem1534139 x) (@lem1534140)). Qed.
Lemma lem1534142 (x : real) : (term136 x) = (term35 x).
Proof. exact (TRANS (@lem1534124 x) (@lem1534141 x)). Qed.
Lemma lem1534143 (x : real) : (term141 x) = (term142 x).
Proof. exact (@lem1483525 (real_neg x) term1). Qed.
Lemma lem1534144 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534151 (x : real) : (real_neg x) = (term30 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1534152 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1534153 (x : real) : (term143 x) = (term144 x).
Proof. exact (MK_COMB (@lem1534152) (@lem1534151 x)). Qed.
Lemma lem1534154 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1534153 x) (@lem1534144)). Qed.
Lemma lem1534155 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem1483519 (term30 x) term1). Qed.
Lemma lem1534157 (x : nat) : (term25 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534158 : term26 = term1.
Proof. exact (@lem1534157 term27). Qed.
Lemma lem1534159 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1534160 (x : real) : (term147 x) = (term149 x).
Proof. exact (MK_COMB (@lem1534159 x) (@lem1534158)). Qed.
Lemma lem1534161 (x : real) : (term149 x) = (term30 x).
Proof. exact (@lem1483450 (term30 x)). Qed.
Lemma lem1534162 (x : real) : (term147 x) = (term30 x).
Proof. exact (TRANS (@lem1534160 x) (@lem1534161 x)). Qed.
Lemma lem1534163 (x : real) : (term146 x) = (term30 x).
Proof. exact (TRANS (@lem1534155 x) (@lem1534162 x)). Qed.
Lemma lem1534164 (x : real) : (term145 x) = (term30 x).
Proof. exact (TRANS (@lem1534154 x) (@lem1534163 x)). Qed.
Lemma lem1534165 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534166 (x : real) : (term150 x) = (term33 x).
Proof. exact (MK_COMB (@lem1534165) (@lem1534164 x)). Qed.
Lemma lem1534167 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534168 (x : real) : (term142 x) = (term35 x).
Proof. exact (MK_COMB (@lem1534166 x) (@lem1534167)). Qed.
Lemma lem1534169 (x : real) : (term141 x) = (term35 x).
Proof. exact (TRANS (@lem1534143 x) (@lem1534168 x)). Qed.
Lemma lem1534170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534171 (x : real) : (term4 x) = (term4 x).
Proof. exact (MK_COMB (@lem1534170) (@lem1534096 x)). Qed.
Lemma lem1534172 (x : real) : (term121 x) = (term151 x).
Proof. exact (MK_COMB (@lem1534171 x) (@lem1534169 x)). Qed.
Lemma lem1534173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534174 (x : real) : (term122 x) = (term111 x).
Proof. exact (MK_COMB (@lem1534173) (@lem1534142 x)). Qed.
Lemma lem1534175 (x : real) : (term124 x) = (term152 x).
Proof. exact (MK_COMB (@lem1534174 x) (@lem1534172 x)). Qed.
Lemma lem1534176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534177 (x : real) : (term131 x) = (term131 x).
Proof. exact (MK_COMB (@lem1534176) (@lem1534123 x)). Qed.
Lemma lem1534178 (x : real) : (term132 x) = (term153 x).
Proof. exact (MK_COMB (@lem1534177 x) (@lem1534175 x)). Qed.
Lemma lem1534190 (x : real) : (term63 x) = (term153 x).
Proof. exact (TRANS (@lem1534054 x) (@lem1534178 x)). Qed.
Lemma lem1534191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534192 (x : real) : (term95 x) = (term154 x).
Proof. exact (MK_COMB (@lem1534191) (@lem1534037 x)). Qed.
Lemma lem1534193 (x : real) : (term96 x) = (term155 x).
Proof. exact (MK_COMB (@lem1534192 x) (@lem1534190 x)). Qed.
Lemma lem1534194 (x : real) (h1 : term155 x) : term155 x.
Proof. exact (h1). Qed.
Lemma lem1534195 (x : real) (h1 : term116 x) : term116 x.
Proof. exact (h1). Qed.
Lemma lem1534196 (x : real) (h1 : term110 x) : term110 x.
Proof. exact (h1). Qed.
Lemma lem1534197 (x : real) (h1 : term110 x) : term107 x.
Proof. exact (proj2 (@lem1534196 x h1)). Qed.
Lemma lem1534198 (x : real) (h1 : term110 x) : term38 x.
Proof. exact (proj1 (@lem1534196 x h1)). Qed.
Lemma lem1534200 (x : real) (h1 : term110 x) : term156 x.
Proof. exact (proj1 (@lem1534197 x h1)). Qed.
Lemma lem1534202 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534203 : term158 = term159.
Proof. exact (@lem1534202 (NUMERAL 0) term27). Qed.
Lemma lem1534204 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534205 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534206 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534205 h1) (fun h1 : term159 = True => @lem1534204)). Qed.
Lemma lem1534207 : term159 = True.
Proof. exact (EQ_MP (@lem1534206) (@lem1534204)). Qed.
Lemma lem1534208 : term158 = True.
Proof. exact (TRANS (@lem1534203) (@lem1534207)). Qed.
Lemma lem1534209 : True = term158.
Proof. exact (SYM (@lem1534208)). Qed.
Lemma lem1534210 : term158.
Proof. exact (EQ_MP (@lem1534209) (@lem0)). Qed.
Lemma lem1534211 (x : real) (h1 : term110 x) : term161 x.
Proof. exact (conj (@lem1534210) (@lem1534200 x h1)). Qed.
Lemma lem1534213 (x : real) (y : real) : term162 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1534214 (x : real) : term163 x.
Proof. exact (@lem1534213 term164 (term30 x)). Qed.
Lemma lem1534215 (x : real) (h1 : term110 x) : term165 x.
Proof. exact (@lem1534214 x (@lem1534211 x h1)). Qed.
Lemma lem1534216 (x : real) : (term166 x) = (term30 x).
Proof. exact (@lem1483460 (term30 x)). Qed.
Lemma lem1534217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1534218 (x : real) : (term167 x) = (term168 x).
Proof. exact (MK_COMB (@lem1534217) (@lem1534216 x)). Qed.
Lemma lem1534219 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534220 (x : real) : (term165 x) = (term156 x).
Proof. exact (MK_COMB (@lem1534218 x) (@lem1534219)). Qed.
Lemma lem1534221 (x : real) (h1 : term110 x) : term156 x.
Proof. exact (EQ_MP (@lem1534220 x) (@lem1534215 x h1)). Qed.
Lemma lem1534223 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534224 : term158 = term159.
Proof. exact (@lem1534223 (NUMERAL 0) term27). Qed.
Lemma lem1534225 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534226 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534227 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534226 h1) (fun h1 : term159 = True => @lem1534225)). Qed.
Lemma lem1534228 : term159 = True.
Proof. exact (EQ_MP (@lem1534227) (@lem1534225)). Qed.
Lemma lem1534229 : term158 = True.
Proof. exact (TRANS (@lem1534224) (@lem1534228)). Qed.
Lemma lem1534230 : True = term158.
Proof. exact (SYM (@lem1534229)). Qed.
Lemma lem1534231 : term158.
Proof. exact (EQ_MP (@lem1534230) (@lem0)). Qed.
Lemma lem1534232 (x : real) (h1 : term110 x) : term169 x.
Proof. exact (conj (@lem1534231) (@lem1534198 x h1)). Qed.
Lemma lem1534234 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1534235 (x : real) : term171 x.
Proof. exact (@lem1534234 term164 x). Qed.
Lemma lem1534236 (x : real) (h1 : term110 x) : term172 x.
Proof. exact (@lem1534235 x (@lem1534232 x h1)). Qed.
Lemma lem1534237 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534238 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534239 (x : real) : (term173 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1534238) (@lem1534237 x)). Qed.
Lemma lem1534240 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534241 (x : real) : (term172 x) = (term38 x).
Proof. exact (MK_COMB (@lem1534239 x) (@lem1534240)). Qed.
Lemma lem1534242 (x : real) (h1 : term110 x) : term38 x.
Proof. exact (EQ_MP (@lem1534241 x) (@lem1534236 x h1)). Qed.
Lemma lem1534243 (x : real) (h1 : term110 x) : term174 x.
Proof. exact (conj (@lem1534242 x h1) (@lem1534221 x h1)). Qed.
Lemma lem1534245 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1534246 (x : real) : term176 x.
Proof. exact (@lem1534245 x (term30 x)). Qed.
Lemma lem1534247 (x : real) (h1 : term110 x) : term177 x.
Proof. exact (@lem1534246 x (@lem1534243 x h1)). Qed.
Lemma lem1534248 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem1483442 term180 x). Qed.
Lemma lem1534250 (m : nat) : (term181 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1534251 : term182 = term1.
Proof. exact (@lem1534250 term27). Qed.
Lemma lem1534252 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534253 : term183 = term184.
Proof. exact (MK_COMB (@lem1534252) (@lem1534251)). Qed.
Lemma lem1534254 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534255 (x : real) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem1534253) (@lem1534254 x)). Qed.
Lemma lem1534256 (x : real) : (term178 x) = (term185 x).
Proof. exact (TRANS (@lem1534248 x) (@lem1534255 x)). Qed.
Lemma lem1534257 (x : real) : (term185 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1534258 (x : real) : (term178 x) = term1.
Proof. exact (TRANS (@lem1534256 x) (@lem1534257 x)). Qed.
Lemma lem1534259 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534260 (x : real) : (term186 x) = term187.
Proof. exact (MK_COMB (@lem1534259) (@lem1534258 x)). Qed.
Lemma lem1534261 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534262 (x : real) : (term177 x) = term188.
Proof. exact (MK_COMB (@lem1534260 x) (@lem1534261)). Qed.
Lemma lem1534263 (x : real) (h1 : term110 x) : term188.
Proof. exact (EQ_MP (@lem1534262 x) (@lem1534247 x h1)). Qed.
Lemma lem1534265 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534266 : term188 = term189.
Proof. exact (@lem1534265 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1534267 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1534268 : term188 = False.
Proof. exact (TRANS (@lem1534266) (@lem1534267)). Qed.
Lemma lem1534269 (x : real) (h1 : term110 x) : False.
Proof. exact (EQ_MP (@lem1534268) (@lem1534263 x h1)). Qed.
Lemma lem1534270 (x : real) (h1 : term113 x) : term113 x.
Proof. exact (h1). Qed.
Lemma lem1534271 (x : real) (h1 : term113 x) : term107 x.
Proof. exact (proj2 (@lem1534270 x h1)). Qed.
Lemma lem1534272 (x : real) (h1 : term113 x) : term35 x.
Proof. exact (proj1 (@lem1534270 x h1)). Qed.
Lemma lem1534273 (x : real) (h1 : term113 x) : term105 x.
Proof. exact (proj2 (@lem1534271 x h1)). Qed.
Lemma lem1534276 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534277 : term158 = term159.
Proof. exact (@lem1534276 (NUMERAL 0) term27). Qed.
Lemma lem1534278 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534279 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534280 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534279 h1) (fun h1 : term159 = True => @lem1534278)). Qed.
Lemma lem1534281 : term159 = True.
Proof. exact (EQ_MP (@lem1534280) (@lem1534278)). Qed.
Lemma lem1534282 : term158 = True.
Proof. exact (TRANS (@lem1534277) (@lem1534281)). Qed.
Lemma lem1534283 : True = term158.
Proof. exact (SYM (@lem1534282)). Qed.
Lemma lem1534284 : term158.
Proof. exact (EQ_MP (@lem1534283) (@lem0)). Qed.
Lemma lem1534285 (x : real) (h1 : term113 x) : term190 x.
Proof. exact (conj (@lem1534284) (@lem1534273 x h1)). Qed.
Lemma lem1534287 (x : real) (y : real) : term162 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1534288 (x : real) : term191 x.
Proof. exact (@lem1534287 term164 x). Qed.
Lemma lem1534289 (x : real) (h1 : term113 x) : term104 x.
Proof. exact (@lem1534288 x (@lem1534285 x h1)). Qed.
Lemma lem1534290 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1534292 (x : real) : (term103 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1534291) (@lem1534290 x)). Qed.
Lemma lem1534293 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534294 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1534292 x) (@lem1534293)). Qed.
Lemma lem1534295 (x : real) (h1 : term113 x) : term105 x.
Proof. exact (EQ_MP (@lem1534294 x) (@lem1534289 x h1)). Qed.
Lemma lem1534297 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534298 : term158 = term159.
Proof. exact (@lem1534297 (NUMERAL 0) term27). Qed.
Lemma lem1534299 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534300 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534301 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534300 h1) (fun h1 : term159 = True => @lem1534299)). Qed.
Lemma lem1534302 : term159 = True.
Proof. exact (EQ_MP (@lem1534301) (@lem1534299)). Qed.
Lemma lem1534303 : term158 = True.
Proof. exact (TRANS (@lem1534298) (@lem1534302)). Qed.
Lemma lem1534304 : True = term158.
Proof. exact (SYM (@lem1534303)). Qed.
Lemma lem1534305 : term158.
Proof. exact (EQ_MP (@lem1534304) (@lem0)). Qed.
Lemma lem1534306 (x : real) (h1 : term113 x) : term192 x.
Proof. exact (conj (@lem1534305) (@lem1534272 x h1)). Qed.
Lemma lem1534308 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1534309 (x : real) : term193 x.
Proof. exact (@lem1534308 term164 (term30 x)). Qed.
Lemma lem1534310 (x : real) (h1 : term113 x) : term194 x.
Proof. exact (@lem1534309 x (@lem1534306 x h1)). Qed.
Lemma lem1534311 (x : real) : (term166 x) = (term30 x).
Proof. exact (@lem1483460 (term30 x)). Qed.
Lemma lem1534312 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534313 (x : real) : (term195 x) = (term33 x).
Proof. exact (MK_COMB (@lem1534312) (@lem1534311 x)). Qed.
Lemma lem1534314 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534315 (x : real) : (term194 x) = (term35 x).
Proof. exact (MK_COMB (@lem1534313 x) (@lem1534314)). Qed.
Lemma lem1534316 (x : real) (h1 : term113 x) : term35 x.
Proof. exact (EQ_MP (@lem1534315 x) (@lem1534310 x h1)). Qed.
Lemma lem1534317 (x : real) (h1 : term113 x) : term196 x.
Proof. exact (conj (@lem1534316 x h1) (@lem1534295 x h1)). Qed.
Lemma lem1534319 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1534320 (x : real) : term197 x.
Proof. exact (@lem1534319 (term30 x) x). Qed.
Lemma lem1534321 (x : real) (h1 : term113 x) : term198 x.
Proof. exact (@lem1534320 x (@lem1534317 x h1)). Qed.
Lemma lem1534322 (x : real) : (term199 x) = (term179 x).
Proof. exact (@lem1483440 term180 x). Qed.
Lemma lem1534324 (m : nat) : (term181 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1534325 : term182 = term1.
Proof. exact (@lem1534324 term27). Qed.
Lemma lem1534326 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534327 : term183 = term184.
Proof. exact (MK_COMB (@lem1534326) (@lem1534325)). Qed.
Lemma lem1534328 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534329 (x : real) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem1534327) (@lem1534328 x)). Qed.
Lemma lem1534330 (x : real) : (term199 x) = (term185 x).
Proof. exact (TRANS (@lem1534322 x) (@lem1534329 x)). Qed.
Lemma lem1534331 (x : real) : (term185 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1534332 (x : real) : (term199 x) = term1.
Proof. exact (TRANS (@lem1534330 x) (@lem1534331 x)). Qed.
Lemma lem1534333 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534334 (x : real) : (term200 x) = term187.
Proof. exact (MK_COMB (@lem1534333) (@lem1534332 x)). Qed.
Lemma lem1534335 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534336 (x : real) : (term198 x) = term188.
Proof. exact (MK_COMB (@lem1534334 x) (@lem1534335)). Qed.
Lemma lem1534337 (x : real) (h1 : term113 x) : term188.
Proof. exact (EQ_MP (@lem1534336 x) (@lem1534321 x h1)). Qed.
Lemma lem1534339 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534340 : term188 = term189.
Proof. exact (@lem1534339 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1534341 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1534342 : term188 = False.
Proof. exact (TRANS (@lem1534340) (@lem1534341)). Qed.
Lemma lem1534343 (x : real) (h1 : term113 x) : False.
Proof. exact (EQ_MP (@lem1534342) (@lem1534337 x h1)). Qed.
Lemma lem1534344 (x : real) (h1 : term116 x) : False.
Proof. exact (or_elim (@lem1534195 x h1) (fun h0 : term110 x => @lem1534269 x h0) (fun h0 : term113 x => @lem1534343 x h0)). Qed.
Lemma lem1534345 (x : real) (h1 : term153 x) : term153 x.
Proof. exact (h1). Qed.
Lemma lem1534346 (x : real) (h1 : term129 x) : term129 x.
Proof. exact (h1). Qed.
Lemma lem1534347 (x : real) (h1 : term129 x) : term126 x.
Proof. exact (proj2 (@lem1534346 x h1)). Qed.
Lemma lem1534349 (x : real) (h1 : term129 x) : term38 x.
Proof. exact (proj2 (@lem1534347 x h1)). Qed.
Lemma lem1534350 (x : real) (h1 : term129 x) : x = term1.
Proof. exact (proj1 (@lem1534347 x h1)). Qed.
Lemma lem1534352 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534353 : term158 = term159.
Proof. exact (@lem1534352 (NUMERAL 0) term27). Qed.
Lemma lem1534354 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534355 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534356 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534355 h1) (fun h1 : term159 = True => @lem1534354)). Qed.
Lemma lem1534357 : term159 = True.
Proof. exact (EQ_MP (@lem1534356) (@lem1534354)). Qed.
Lemma lem1534358 : term158 = True.
Proof. exact (TRANS (@lem1534353) (@lem1534357)). Qed.
Lemma lem1534359 : True = term158.
Proof. exact (SYM (@lem1534358)). Qed.
Lemma lem1534360 : term158.
Proof. exact (EQ_MP (@lem1534359) (@lem0)). Qed.
Lemma lem1534361 (x : real) (h1 : term129 x) : term169 x.
Proof. exact (conj (@lem1534360) (@lem1534349 x h1)). Qed.
Lemma lem1534363 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1534364 (x : real) : term171 x.
Proof. exact (@lem1534363 term164 x). Qed.
Lemma lem1534365 (x : real) (h1 : term129 x) : term172 x.
Proof. exact (@lem1534364 x (@lem1534361 x h1)). Qed.
Lemma lem1534366 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534367 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534368 (x : real) : (term173 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1534367) (@lem1534366 x)). Qed.
Lemma lem1534369 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534370 (x : real) : (term172 x) = (term38 x).
Proof. exact (MK_COMB (@lem1534368 x) (@lem1534369)). Qed.
Lemma lem1534371 (x : real) (h1 : term129 x) : term38 x.
Proof. exact (EQ_MP (@lem1534370 x) (@lem1534365 x h1)). Qed.
Lemma lem1534373 (y : real) : term201 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1534374 (x : real) : term201 x.
Proof. exact (@lem1534373 x). Qed.
Lemma lem1534375 (x : real) (h1 : term129 x) : term202 x.
Proof. exact (@lem1534374 x (@lem1534350 x h1)). Qed.
Lemma lem1534376 (x : real) (h1 : term129 x) : term203 x.
Proof. exact (@lem1534375 x h1 term180). Qed.
Lemma lem1534377 (x : real) : (term203 x) = ((term30 x) = term1).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem1534384 (x : real) (h1 : term129 x) : (term30 x) = term1.
Proof. exact (EQ_MP (@lem1534377 x) (@lem1534376 x h1)). Qed.
Lemma lem1534385 (x : real) (h1 : term129 x) : term204 x.
Proof. exact (conj (@lem1534384 x h1) (@lem1534371 x h1)). Qed.
Lemma lem1534387 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1534388 (x : real) : term206 x.
Proof. exact (@lem1534387 (term30 x) x). Qed.
Lemma lem1534389 (x : real) (h1 : term129 x) : term198 x.
Proof. exact (@lem1534388 x (@lem1534385 x h1)). Qed.
Lemma lem1534390 (x : real) : (term199 x) = (term179 x).
Proof. exact (@lem1483440 term180 x). Qed.
Lemma lem1534392 (m : nat) : (term181 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1534393 : term182 = term1.
Proof. exact (@lem1534392 term27). Qed.
Lemma lem1534394 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534395 : term183 = term184.
Proof. exact (MK_COMB (@lem1534394) (@lem1534393)). Qed.
Lemma lem1534396 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534397 (x : real) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem1534395) (@lem1534396 x)). Qed.
Lemma lem1534398 (x : real) : (term199 x) = (term185 x).
Proof. exact (TRANS (@lem1534390 x) (@lem1534397 x)). Qed.
Lemma lem1534399 (x : real) : (term185 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1534400 (x : real) : (term199 x) = term1.
Proof. exact (TRANS (@lem1534398 x) (@lem1534399 x)). Qed.
Lemma lem1534401 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534402 (x : real) : (term200 x) = term187.
Proof. exact (MK_COMB (@lem1534401) (@lem1534400 x)). Qed.
Lemma lem1534403 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534404 (x : real) : (term198 x) = term188.
Proof. exact (MK_COMB (@lem1534402 x) (@lem1534403)). Qed.
Lemma lem1534405 (x : real) (h1 : term129 x) : term188.
Proof. exact (EQ_MP (@lem1534404 x) (@lem1534389 x h1)). Qed.
Lemma lem1534407 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534408 : term188 = term189.
Proof. exact (@lem1534407 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1534409 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1534410 : term188 = False.
Proof. exact (TRANS (@lem1534408) (@lem1534409)). Qed.
Lemma lem1534411 (x : real) (h1 : term129 x) : False.
Proof. exact (EQ_MP (@lem1534410) (@lem1534405 x h1)). Qed.
Lemma lem1534412 (x : real) (h1 : term152 x) : term152 x.
Proof. exact (h1). Qed.
Lemma lem1534413 (x : real) (h1 : term152 x) : term151 x.
Proof. exact (proj2 (@lem1534412 x h1)). Qed.
Lemma lem1534415 (x : real) (h1 : term152 x) : term35 x.
Proof. exact (proj2 (@lem1534413 x h1)). Qed.
Lemma lem1534416 (x : real) (h1 : term152 x) : x = term1.
Proof. exact (proj1 (@lem1534413 x h1)). Qed.
Lemma lem1534418 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534419 : term158 = term159.
Proof. exact (@lem1534418 (NUMERAL 0) term27). Qed.
Lemma lem1534420 : term160 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1534421 (h1 : term160 = (BIT1 0)) : term159 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1534422 : (term160 = (BIT1 0)) = (term159 = True).
Proof. exact (prop_ext (fun h1 : term160 = (BIT1 0) => @lem1534421 h1) (fun h1 : term159 = True => @lem1534420)). Qed.
Lemma lem1534423 : term159 = True.
Proof. exact (EQ_MP (@lem1534422) (@lem1534420)). Qed.
Lemma lem1534424 : term158 = True.
Proof. exact (TRANS (@lem1534419) (@lem1534423)). Qed.
Lemma lem1534425 : True = term158.
Proof. exact (SYM (@lem1534424)). Qed.
Lemma lem1534426 : term158.
Proof. exact (EQ_MP (@lem1534425) (@lem0)). Qed.
Lemma lem1534427 (x : real) (h1 : term152 x) : term192 x.
Proof. exact (conj (@lem1534426) (@lem1534415 x h1)). Qed.
Lemma lem1534429 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1534430 (x : real) : term193 x.
Proof. exact (@lem1534429 term164 (term30 x)). Qed.
Lemma lem1534431 (x : real) (h1 : term152 x) : term194 x.
Proof. exact (@lem1534430 x (@lem1534427 x h1)). Qed.
Lemma lem1534432 (x : real) : (term166 x) = (term30 x).
Proof. exact (@lem1483460 (term30 x)). Qed.
Lemma lem1534433 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534434 (x : real) : (term195 x) = (term33 x).
Proof. exact (MK_COMB (@lem1534433) (@lem1534432 x)). Qed.
Lemma lem1534435 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534436 (x : real) : (term194 x) = (term35 x).
Proof. exact (MK_COMB (@lem1534434 x) (@lem1534435)). Qed.
Lemma lem1534437 (x : real) (h1 : term152 x) : term35 x.
Proof. exact (EQ_MP (@lem1534436 x) (@lem1534431 x h1)). Qed.
Lemma lem1534439 (y : real) : term201 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1534440 (x : real) : term201 x.
Proof. exact (@lem1534439 x). Qed.
Lemma lem1534441 (x : real) (h1 : term152 x) : term202 x.
Proof. exact (@lem1534440 x (@lem1534416 x h1)). Qed.
Lemma lem1534442 (x : real) (h1 : term152 x) : term207 x.
Proof. exact (@lem1534441 x h1 term164). Qed.
Lemma lem1534443 (x : real) : (term207 x) = ((term102 x) = term1).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem1534444 (x : real) (h1 : term152 x) : (term102 x) = term1.
Proof. exact (EQ_MP (@lem1534443 x) (@lem1534442 x h1)). Qed.
Lemma lem1534445 (x : real) : (term102 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534446 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1534447 (x : real) : (term208 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1534446) (@lem1534445 x)). Qed.
Lemma lem1534448 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534449 (x : real) : ((term102 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1534447 x) (@lem1534448)). Qed.
Lemma lem1534450 (x : real) (h1 : term152 x) : x = term1.
Proof. exact (EQ_MP (@lem1534449 x) (@lem1534444 x h1)). Qed.
Lemma lem1534451 (x : real) (h1 : term152 x) : term151 x.
Proof. exact (conj (@lem1534450 x h1) (@lem1534437 x h1)). Qed.
Lemma lem1534453 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1534454 (x : real) : term209 x.
Proof. exact (@lem1534453 x (term30 x)). Qed.
Lemma lem1534455 (x : real) (h1 : term152 x) : term177 x.
Proof. exact (@lem1534454 x (@lem1534451 x h1)). Qed.
Lemma lem1534456 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem1483442 term180 x). Qed.
Lemma lem1534458 (m : nat) : (term181 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1534459 : term182 = term1.
Proof. exact (@lem1534458 term27). Qed.
Lemma lem1534460 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534461 : term183 = term184.
Proof. exact (MK_COMB (@lem1534460) (@lem1534459)). Qed.
Lemma lem1534462 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534463 (x : real) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem1534461) (@lem1534462 x)). Qed.
Lemma lem1534464 (x : real) : (term178 x) = (term185 x).
Proof. exact (TRANS (@lem1534456 x) (@lem1534463 x)). Qed.
Lemma lem1534465 (x : real) : (term185 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1534466 (x : real) : (term178 x) = term1.
Proof. exact (TRANS (@lem1534464 x) (@lem1534465 x)). Qed.
Lemma lem1534467 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534468 (x : real) : (term186 x) = term187.
Proof. exact (MK_COMB (@lem1534467) (@lem1534466 x)). Qed.
Lemma lem1534469 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1534470 (x : real) : (term177 x) = term188.
Proof. exact (MK_COMB (@lem1534468 x) (@lem1534469)). Qed.
Lemma lem1534471 (x : real) (h1 : term152 x) : term188.
Proof. exact (EQ_MP (@lem1534470 x) (@lem1534455 x h1)). Qed.
Lemma lem1534473 (n : nat) (m : nat) : (term157 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1534474 : term188 = term189.
Proof. exact (@lem1534473 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1534475 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1534476 : term188 = False.
Proof. exact (TRANS (@lem1534474) (@lem1534475)). Qed.
Lemma lem1534477 (x : real) (h1 : term152 x) : False.
Proof. exact (EQ_MP (@lem1534476) (@lem1534471 x h1)). Qed.
Lemma lem1534478 (x : real) (h1 : term153 x) : False.
Proof. exact (or_elim (@lem1534345 x h1) (fun h0 : term129 x => @lem1534411 x h0) (fun h0 : term152 x => @lem1534477 x h0)). Qed.
Lemma lem1534479 (x : real) (h1 : term155 x) : False.
Proof. exact (or_elim (@lem1534194 x h1) (fun h0 : term116 x => @lem1534344 x h0) (fun h0 : term153 x => @lem1534478 x h0)). Qed.
Lemma lem1534480 (x : real) (h1 : term96 x) : term96 x.
Proof. exact (h1). Qed.
Lemma lem1534481 (x : real) (h1 : term96 x) : term155 x.
Proof. exact (EQ_MP (@lem1534193 x) (@lem1534480 x h1)). Qed.
Lemma lem1534482 (x : real) (h1 : term96 x) : (term155 x) = False.
Proof. exact (prop_ext (fun h2 : term155 x => @lem1534479 x h2) (fun h2 : False => @lem1534481 x h1)). Qed.
Lemma lem1534483 (x : real) (h1 : term96 x) : False.
Proof. exact (EQ_MP (@lem1534482 x h1) (@lem1534481 x h1)). Qed.
Lemma lem1534484 (h1 : term98) : term98.
Proof. exact (h1). Qed.
Lemma lem1534485 (h1 : term98) : False.
Proof. exact (ex_elim (@lem1534484 h1) (fun x : real => fun h0 : term97 x => @lem1534483 x h0)). Qed.
Lemma lem1534486 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1534487 (h1 : term14) : term98.
Proof. exact (EQ_MP (@lem1533968) (@lem1534486 h1)). Qed.
Lemma lem1534488 (h1 : term14) : term98 = False.
Proof. exact (prop_ext (fun h2 : term98 => @lem1534485 h2) (fun h2 : False => @lem1534487 h1)). Qed.
Lemma lem1534489 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1534488 h1) (@lem1534487 h1)). Qed.
Lemma lem1534490 : term210.
Proof. exact (fun h0 : term14 => @lem1534489 h0). Qed.
Lemma lem1534491 : term211.
Proof. exact (@lem1386578 term212). Qed.
Lemma lem1534492 : term212.
Proof. exact (@lem1534491 (@lem1534490)). Qed.

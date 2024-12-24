Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_SYM_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482715_spec.
Require Import thm1482716_spec.
Require Import thm1483429_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1558675 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1558676 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1558675 (term4 x)). Qed.
Lemma lem1558677 (y : real) (x : real) : (term5 x y) = ((real_min x y) = (real_min y x)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1558678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1558680 (y : real) (x : real) : (term6 x y) = (term7 y x).
Proof. exact (MK_COMB (@lem1558678) (@lem1558677 y x)). Qed.
Lemma lem1558681 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1558680 y x)). Qed.
Lemma lem1558682 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558683 (x : real) : (term3 x) = (term10 x).
Proof. exact (MK_COMB (@lem1558682) (@lem1558681 x)). Qed.
Lemma lem1558684 (x : real) : (term2 x) = (term10 x).
Proof. exact (TRANS (@lem1558676 x) (@lem1558683 x)). Qed.
Lemma lem1558685 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1558686 : term11 = term12.
Proof. exact (@lem1558685 term13). Qed.
Lemma lem1558687 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1558688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1558689 (x : real) : (term16 x) = (term2 x).
Proof. exact (MK_COMB (@lem1558688) (@lem1558687 x)). Qed.
Lemma lem1558690 (x : real) : (term16 x) = (term10 x).
Proof. exact (TRANS (@lem1558689 x) (@lem1558684 x)). Qed.
Lemma lem1558691 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1558690 x)). Qed.
Lemma lem1558692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558693 : term12 = term19.
Proof. exact (MK_COMB (@lem1558692) (@lem1558691)). Qed.
Lemma lem1558695 : term11 = term19.
Proof. exact (TRANS (@lem1558686) (@lem1558693)). Qed.
Lemma lem1558698 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1558699 (x : real) : (term9 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1558698 y x)). Qed.
Lemma lem1558700 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558701 (x : real) : (term10 x) = (term10 x).
Proof. exact (MK_COMB (@lem1558700) (@lem1558699 x)). Qed.
Lemma lem1558702 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1558701 x)). Qed.
Lemma lem1558703 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558704 : term19 = term19.
Proof. exact (MK_COMB (@lem1558703) (@lem1558702)). Qed.
Lemma lem1558705 : term11 = term19.
Proof. exact (TRANS (@lem1558695) (@lem1558704)). Qed.
Lemma lem1558706 (y : real) (x : real) : (term7 y x) = (term20 y x).
Proof. exact (@lem1483554 (real_min x y) (real_min y x)). Qed.
Lemma lem1558719 (y : real) (x : real) : (term21 y x) = (term22 y x).
Proof. exact (@lem1483519 (real_min x y) (real_min y x)). Qed.
Lemma lem1558720 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1558721 (y : real) (x : real) : (term23 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1558720) (@lem1558719 y x)). Qed.
Lemma lem1558722 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (@lem1483512 (term22 y x)). Qed.
Lemma lem1558723 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1483508 (real_min x y) term27 (term28 y x)). Qed.
Lemma lem1558724 (y : real) (x : real) : (term29 y x) = (term30 y x).
Proof. exact (@lem1483476 term27 term27 (real_min y x)). Qed.
Lemma lem1558726 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1558727 : term33 = term34.
Proof. exact (@lem1558726 term35 term35). Qed.
Lemma lem1558728 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1558729 : term37 = term35.
Proof. exact (EQ_MP (@lem1558728) (@lem940073)). Qed.
Lemma lem1558730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1558731 : term34 = term38.
Proof. exact (MK_COMB (@lem1558730) (@lem1558729)). Qed.
Lemma lem1558732 : term33 = term38.
Proof. exact (TRANS (@lem1558727) (@lem1558731)). Qed.
Lemma lem1558733 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1558734 : term39 = term40.
Proof. exact (MK_COMB (@lem1558733) (@lem1558732)). Qed.
Lemma lem1558735 (y : real) (x : real) : (real_min y x) = (real_min y x).
Proof. exact (eq_refl (real_min y x)). Qed.
Lemma lem1558736 (y : real) (x : real) : (term30 y x) = (term41 y x).
Proof. exact (MK_COMB (@lem1558734) (@lem1558735 y x)). Qed.
Lemma lem1558737 (y : real) (x : real) : (term29 y x) = (term41 y x).
Proof. exact (TRANS (@lem1558724 y x) (@lem1558736 y x)). Qed.
Lemma lem1558738 (y : real) (x : real) : (term41 y x) = (real_min y x).
Proof. exact (@lem1483436 (real_min y x)). Qed.
Lemma lem1558739 (y : real) (x : real) : (term29 y x) = (real_min y x).
Proof. exact (TRANS (@lem1558737 y x) (@lem1558738 y x)). Qed.
Lemma lem1558742 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1558743 (y : real) (x : real) : (term26 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem1558742 x y) (@lem1558739 y x)). Qed.
Lemma lem1558744 (y : real) (x : real) : (term25 y x) = (term43 y x).
Proof. exact (TRANS (@lem1558723 y x) (@lem1558743 y x)). Qed.
Lemma lem1558745 (y : real) (x : real) : (term24 y x) = (term43 y x).
Proof. exact (TRANS (@lem1558722 y x) (@lem1558744 y x)). Qed.
Lemma lem1558746 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (eq_refl (term44 y x)). Qed.
Lemma lem1558747 (y : real) (x : real) : ((term23 y x) = (term24 y x)) = ((term23 y x) = (term43 y x)).
Proof. exact (MK_COMB (@lem1558746 y x) (@lem1558745 y x)). Qed.
Lemma lem1558748 (y : real) (x : real) : (term23 y x) = (term43 y x).
Proof. exact (EQ_MP (@lem1558747 y x) (@lem1558721 y x)). Qed.
Lemma lem1558749 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558750 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1558749) (@lem1558748 y x)). Qed.
Lemma lem1558751 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558752 (y : real) (x : real) : (term48 y x) = (term49 y x).
Proof. exact (MK_COMB (@lem1558750 y x) (@lem1558751)). Qed.
Lemma lem1558753 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558754 (y : real) (x : real) : (term50 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1558753) (@lem1558719 y x)). Qed.
Lemma lem1558755 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558756 (y : real) (x : real) : (term52 y x) = (term53 y x).
Proof. exact (MK_COMB (@lem1558754 y x) (@lem1558755)). Qed.
Lemma lem1558757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558758 (y : real) (x : real) : (term54 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1558757) (@lem1558756 y x)). Qed.
Lemma lem1558759 (y : real) (x : real) : (term20 y x) = (term56 y x).
Proof. exact (MK_COMB (@lem1558758 y x) (@lem1558752 y x)). Qed.
Lemma lem1558760 (y : real) (x : real) : (term7 y x) = (term56 y x).
Proof. exact (TRANS (@lem1558706 y x) (@lem1558759 y x)). Qed.
Lemma lem1558761 (x : real) : (term9 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558760 y x)). Qed.
Lemma lem1558762 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558763 (x : real) : (term10 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558762) (@lem1558761 x)). Qed.
Lemma lem1558764 : term18 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558763 x)). Qed.
Lemma lem1558765 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558766 : term19 = term60.
Proof. exact (MK_COMB (@lem1558765) (@lem1558764)). Qed.
Lemma lem1558767 : term11 = term60.
Proof. exact (TRANS (@lem1558705) (@lem1558766)). Qed.
Lemma lem1558773 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1558774 (P : real -> Prop) (Q : real -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem1558773 real P Q). Qed.
Lemma lem1558775 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1558774 (term67 x) (term68 x)). Qed.
Lemma lem1558776 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558778 (y : real) (x : real) : (term70 x y) = (term55 y x).
Proof. exact (MK_COMB (@lem1558777) (@lem1558776 y x)). Qed.
Lemma lem1558779 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558780 (y : real) (x : real) : (term72 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1558778 y x) (@lem1558779 y x)). Qed.
Lemma lem1558781 (x : real) : (term73 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558780 y x)). Qed.
Lemma lem1558782 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558783 (x : real) : (term65 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558782) (@lem1558781 x)). Qed.
Lemma lem1558784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558785 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1558784) (@lem1558783 x)). Qed.
Lemma lem1558786 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558787 (x : real) : (term76 x) = (term67 x).
Proof. exact (fun_ext (fun y : real => @lem1558786 y x)). Qed.
Lemma lem1558788 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558789 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1558788) (@lem1558787 x)). Qed.
Lemma lem1558790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558791 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558790) (@lem1558789 x)). Qed.
Lemma lem1558792 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558793 (x : real) : (term81 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1558792 y x)). Qed.
Lemma lem1558794 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558795 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1558794) (@lem1558793 x)). Qed.
Lemma lem1558796 (x : real) : (term66 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558791 x) (@lem1558795 x)). Qed.
Lemma lem1558797 (x : real) : ((term65 x) = (term66 x)) = ((term58 x) = (term84 x)).
Proof. exact (MK_COMB (@lem1558785 x) (@lem1558796 x)). Qed.
Lemma lem1558798 (x : real) : (term58 x) = (term84 x).
Proof. exact (EQ_MP (@lem1558797 x) (@lem1558775 x)). Qed.
Lemma lem1558807 : term59 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558798 x)). Qed.
Lemma lem1558808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558809 : term60 = term86.
Proof. exact (MK_COMB (@lem1558808) (@lem1558807)). Qed.
Lemma lem1558811 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1558812 (P : real -> Prop) (Q : real -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem1558811 real P Q). Qed.
Lemma lem1558813 : term87 = term88.
Proof. exact (@lem1558812 term89 term90). Qed.
Lemma lem1558814 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558816 (x : real) : (term92 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558815) (@lem1558814 x)). Qed.
Lemma lem1558817 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558818 (x : real) : (term94 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558816 x) (@lem1558817 x)). Qed.
Lemma lem1558819 : term95 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558818 x)). Qed.
Lemma lem1558820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558821 : term87 = term86.
Proof. exact (MK_COMB (@lem1558820) (@lem1558819)). Qed.
Lemma lem1558822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558823 : term96 = term97.
Proof. exact (MK_COMB (@lem1558822) (@lem1558821)). Qed.
Lemma lem1558824 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558825 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1558824 x)). Qed.
Lemma lem1558826 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558827 : term99 = term100.
Proof. exact (MK_COMB (@lem1558826) (@lem1558825)). Qed.
Lemma lem1558828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558829 : term101 = term102.
Proof. exact (MK_COMB (@lem1558828) (@lem1558827)). Qed.
Lemma lem1558830 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558831 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1558830 x)). Qed.
Lemma lem1558832 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558833 : term104 = term105.
Proof. exact (MK_COMB (@lem1558832) (@lem1558831)). Qed.
Lemma lem1558834 : term88 = term106.
Proof. exact (MK_COMB (@lem1558829) (@lem1558833)). Qed.
Lemma lem1558835 : (term87 = term88) = (term86 = term106).
Proof. exact (MK_COMB (@lem1558823) (@lem1558834)). Qed.
Lemma lem1558836 : term86 = term106.
Proof. exact (EQ_MP (@lem1558835) (@lem1558813)). Qed.
Lemma lem1558853 : term60 = term106.
Proof. exact (TRANS (@lem1558809) (@lem1558836)). Qed.
Lemma lem1558855 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1558856 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term63 P Q).
Proof. exact (@lem1558855 real P Q). Qed.
Lemma lem1558857 : term88 = term87.
Proof. exact (@lem1558856 term89 term90). Qed.
Lemma lem1558858 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558859 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1558858 x)). Qed.
Lemma lem1558860 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558861 : term99 = term100.
Proof. exact (MK_COMB (@lem1558860) (@lem1558859)). Qed.
Lemma lem1558862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558863 : term101 = term102.
Proof. exact (MK_COMB (@lem1558862) (@lem1558861)). Qed.
Lemma lem1558864 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558865 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1558864 x)). Qed.
Lemma lem1558866 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558867 : term104 = term105.
Proof. exact (MK_COMB (@lem1558866) (@lem1558865)). Qed.
Lemma lem1558868 : term88 = term106.
Proof. exact (MK_COMB (@lem1558863) (@lem1558867)). Qed.
Lemma lem1558869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558870 : term107 = term108.
Proof. exact (MK_COMB (@lem1558869) (@lem1558868)). Qed.
Lemma lem1558871 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558873 (x : real) : (term92 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558872) (@lem1558871 x)). Qed.
Lemma lem1558874 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558875 (x : real) : (term94 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558873 x) (@lem1558874 x)). Qed.
Lemma lem1558876 : term95 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558875 x)). Qed.
Lemma lem1558877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558878 : term87 = term86.
Proof. exact (MK_COMB (@lem1558877) (@lem1558876)). Qed.
Lemma lem1558879 : (term88 = term87) = (term106 = term86).
Proof. exact (MK_COMB (@lem1558870) (@lem1558878)). Qed.
Lemma lem1558880 : term106 = term86.
Proof. exact (EQ_MP (@lem1558879) (@lem1558857)). Qed.
Lemma lem1558882 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1558883 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term63 P Q).
Proof. exact (@lem1558882 real P Q). Qed.
Lemma lem1558884 (x : real) : (term66 x) = (term65 x).
Proof. exact (@lem1558883 (term67 x) (term68 x)). Qed.
Lemma lem1558885 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558886 (x : real) : (term76 x) = (term67 x).
Proof. exact (fun_ext (fun y : real => @lem1558885 y x)). Qed.
Lemma lem1558887 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558888 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1558887) (@lem1558886 x)). Qed.
Lemma lem1558889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558890 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558889) (@lem1558888 x)). Qed.
Lemma lem1558891 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558892 (x : real) : (term81 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1558891 y x)). Qed.
Lemma lem1558893 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558894 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1558893) (@lem1558892 x)). Qed.
Lemma lem1558895 (x : real) : (term66 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558890 x) (@lem1558894 x)). Qed.
Lemma lem1558896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558897 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1558896) (@lem1558895 x)). Qed.
Lemma lem1558898 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558900 (y : real) (x : real) : (term70 x y) = (term55 y x).
Proof. exact (MK_COMB (@lem1558899) (@lem1558898 y x)). Qed.
Lemma lem1558901 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558902 (y : real) (x : real) : (term72 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1558900 y x) (@lem1558901 y x)). Qed.
Lemma lem1558903 (x : real) : (term73 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558902 y x)). Qed.
Lemma lem1558904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558905 (x : real) : (term65 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558904) (@lem1558903 x)). Qed.
Lemma lem1558906 (x : real) : ((term66 x) = (term65 x)) = ((term84 x) = (term58 x)).
Proof. exact (MK_COMB (@lem1558897 x) (@lem1558905 x)). Qed.
Lemma lem1558907 (x : real) : (term84 x) = (term58 x).
Proof. exact (EQ_MP (@lem1558906 x) (@lem1558884 x)). Qed.
Lemma lem1558908 : term85 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558907 x)). Qed.
Lemma lem1558909 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558910 : term86 = term60.
Proof. exact (MK_COMB (@lem1558909) (@lem1558908)). Qed.
Lemma lem1558911 : term106 = term60.
Proof. exact (TRANS (@lem1558880) (@lem1558910)). Qed.
Lemma lem1558912 : term60 = term60.
Proof. exact (TRANS (@lem1558853) (@lem1558911)). Qed.
Lemma lem1558915 : term11 = term60.
Proof. exact (TRANS (@lem1558767) (@lem1558912)). Qed.
Lemma lem1558920 (y : real) (x : real) : (term56 y x) = (term56 y x).
Proof. exact (eq_refl (term56 y x)). Qed.
Lemma lem1558921 (x : real) : (term57 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558920 y x)). Qed.
Lemma lem1558922 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558923 (x : real) : (term58 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558922) (@lem1558921 x)). Qed.
Lemma lem1558924 : term59 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558923 x)). Qed.
Lemma lem1558925 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558926 : term60 = term60.
Proof. exact (MK_COMB (@lem1558925) (@lem1558924)). Qed.
Lemma lem1558927 : term11 = term60.
Proof. exact (TRANS (@lem1558915) (@lem1558926)). Qed.
Lemma lem1558929 (x : real) (a : real) (y : real) (r : real) : (term111 x y a r) = (term112 x a y r).
Proof. exact (proj1 (@lem1482715 x a (@el real) y (@el real) r)). Qed.
Lemma lem1558930 (x : real) (y : real) : (term53 y x) = (term113 x y).
Proof. exact (@lem1558929 x (term28 y x) y term47). Qed.
Lemma lem1558943 (y : real) (x : real) : (term114 x y) = (term115 y x).
Proof. exact (@lem1483488 y (term28 y x)). Qed.
Lemma lem1558944 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558945 (y : real) (x : real) : (term116 x y) = (term117 y x).
Proof. exact (MK_COMB (@lem1558944) (@lem1558943 y x)). Qed.
Lemma lem1558946 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558947 (y : real) (x : real) : (term118 x y) = (term119 y x).
Proof. exact (MK_COMB (@lem1558945 y x) (@lem1558946)). Qed.
Lemma lem1558960 (y : real) (x : real) : (term120 y x) = (term121 y x).
Proof. exact (@lem1483488 x (term28 y x)). Qed.
Lemma lem1558961 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558962 (y : real) (x : real) : (term122 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1558961) (@lem1558960 y x)). Qed.
Lemma lem1558963 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558964 (y : real) (x : real) : (term124 y x) = (term125 y x).
Proof. exact (MK_COMB (@lem1558962 y x) (@lem1558963)). Qed.
Lemma lem1558965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558966 (y : real) (x : real) : (term126 y x) = (term127 y x).
Proof. exact (MK_COMB (@lem1558965) (@lem1558964 y x)). Qed.
Lemma lem1558967 (y : real) (x : real) : (term113 x y) = (term128 y x).
Proof. exact (MK_COMB (@lem1558966 y x) (@lem1558947 y x)). Qed.
Lemma lem1558968 (y : real) (x : real) : (term53 y x) = (term128 y x).
Proof. exact (TRANS (@lem1558930 x y) (@lem1558967 y x)). Qed.
Lemma lem1558969 (y : real) (x : real) : (term129 y x) = (term128 y x).
Proof. exact (eq_refl (term129 y x)). Qed.
Lemma lem1558970 (y : real) (x : real) : (term128 y x) = (term129 y x).
Proof. exact (SYM (@lem1558969 y x)). Qed.
Lemma lem1558971 (y : real) (x : real) : (term129 y x) = (term130 y x).
Proof. exact (@lem1483429 y (term131 x y) x). Qed.
Lemma lem1558972 (y : real) (x : real) : (term128 y x) = (term130 y x).
Proof. exact (TRANS (@lem1558970 y x) (@lem1558971 y x)). Qed.
Lemma lem1558973 (y : real) (x : real) : (term132 y x) = (term133 y x).
Proof. exact (eq_refl (term132 y x)). Qed.
Lemma lem1558974 (y : real) (x : real) : (term134 y x) = (term134 y x).
Proof. exact (eq_refl (term134 y x)). Qed.
Lemma lem1558975 (y : real) (x : real) : (term135 y x) = (term136 y x).
Proof. exact (MK_COMB (@lem1558974 y x) (@lem1558973 y x)). Qed.
Lemma lem1558976 (x : real) (y : real) : (term137 x y) = (term138 x y).
Proof. exact (eq_refl (term137 x y)). Qed.
Lemma lem1558977 (x : real) (y : real) : (term139 x y) = (term139 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1558978 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1558977 x y) (@lem1558976 x y)). Qed.
Lemma lem1558979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558980 (x : real) (y : real) : (term142 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1558979) (@lem1558978 x y)). Qed.
Lemma lem1558981 (y : real) (x : real) : (term130 y x) = (term144 y x).
Proof. exact (MK_COMB (@lem1558980 x y) (@lem1558975 y x)). Qed.
Lemma lem1558982 (y : real) (x : real) : (term145 y x) = (term145 y x).
Proof. exact (eq_refl (term145 y x)). Qed.
Lemma lem1558983 (y : real) (x : real) : ((term128 y x) = (term130 y x)) = ((term128 y x) = (term144 y x)).
Proof. exact (MK_COMB (@lem1558982 y x) (@lem1558981 y x)). Qed.
Lemma lem1558984 (y : real) (x : real) : (term128 y x) = (term144 y x).
Proof. exact (EQ_MP (@lem1558983 y x) (@lem1558972 y x)). Qed.
Lemma lem1558985 (x : real) (y : real) : (real_ge x y) = (term146 x y).
Proof. exact (@lem1483527 x y). Qed.
Lemma lem1558998 (x : real) (y : real) : (real_sub x y) = (term147 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1558999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1559000 (x : real) (y : real) : (term148 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1558999) (@lem1558998 x y)). Qed.
Lemma lem1559001 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559002 (x : real) (y : real) : (term146 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1559000 x y) (@lem1559001)). Qed.
Lemma lem1559003 (x : real) (y : real) : (real_ge x y) = (term150 x y).
Proof. exact (TRANS (@lem1558985 x y) (@lem1559002 x y)). Qed.
Lemma lem1559004 (x : real) (y : real) : (term151 x y) = (term152 x y).
Proof. exact (@lem1483525 (term147 x y) term47). Qed.
Lemma lem1559022 (x : real) (y : real) : (term153 x y) = (term154 x y).
Proof. exact (@lem1483519 (term147 x y) term47). Qed.
Lemma lem1559024 (x : nat) : (term155 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1559025 : term156 = term47.
Proof. exact (@lem1559024 term35). Qed.
Lemma lem1559026 (x : real) (y : real) : (term157 x y) = (term157 x y).
Proof. exact (eq_refl (term157 x y)). Qed.
Lemma lem1559027 (x : real) (y : real) : (term154 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1559026 x y) (@lem1559025)). Qed.
Lemma lem1559028 (x : real) (y : real) : (term158 x y) = (term147 x y).
Proof. exact (@lem1483450 (term147 x y)). Qed.
Lemma lem1559029 (x : real) (y : real) : (term154 x y) = (term147 x y).
Proof. exact (TRANS (@lem1559027 x y) (@lem1559028 x y)). Qed.
Lemma lem1559031 (x : real) (y : real) : (term153 x y) = (term147 x y).
Proof. exact (TRANS (@lem1559022 x y) (@lem1559029 x y)). Qed.
Lemma lem1559032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559033 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1559032) (@lem1559031 x y)). Qed.
Lemma lem1559034 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559035 (x : real) (y : real) : (term152 x y) = (term151 x y).
Proof. exact (MK_COMB (@lem1559033 x y) (@lem1559034)). Qed.
Lemma lem1559036 (x : real) (y : real) : (term151 x y) = (term151 x y).
Proof. exact (TRANS (@lem1559004 x y) (@lem1559035 x y)). Qed.
Lemma lem1559037 (y : real) : (term161 y) = (term162 y).
Proof. exact (@lem1483525 (term163 y) term47). Qed.
Lemma lem1559038 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559050 (y : real) : (term163 y) = (term164 y).
Proof. exact (@lem1483442 term27 y). Qed.
Lemma lem1559052 (m : nat) : (term165 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1559053 : term166 = term47.
Proof. exact (@lem1559052 term35). Qed.
Lemma lem1559054 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1559055 : term167 = term168.
Proof. exact (MK_COMB (@lem1559054) (@lem1559053)). Qed.
Lemma lem1559056 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1559057 (y : real) : (term164 y) = (term169 y).
Proof. exact (MK_COMB (@lem1559055) (@lem1559056 y)). Qed.
Lemma lem1559058 (y : real) : (term163 y) = (term169 y).
Proof. exact (TRANS (@lem1559050 y) (@lem1559057 y)). Qed.
Lemma lem1559059 (y : real) : (term169 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1559061 (y : real) : (term163 y) = term47.
Proof. exact (TRANS (@lem1559058 y) (@lem1559059 y)). Qed.
Lemma lem1559062 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1559063 (y : real) : (term170 y) = term171.
Proof. exact (MK_COMB (@lem1559062) (@lem1559061 y)). Qed.
Lemma lem1559064 (y : real) : (term172 y) = term173.
Proof. exact (MK_COMB (@lem1559063 y) (@lem1559038)). Qed.
Lemma lem1559065 : term173 = term174.
Proof. exact (@lem1483519 term47 term47). Qed.
Lemma lem1559067 (x : nat) : (term155 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1559068 : term156 = term47.
Proof. exact (@lem1559067 term35). Qed.
Lemma lem1559069 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem1559070 : term174 = term176.
Proof. exact (MK_COMB (@lem1559069) (@lem1559068)). Qed.
Lemma lem1559071 : term176 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1559072 : term174 = term47.
Proof. exact (TRANS (@lem1559070) (@lem1559071)). Qed.
Lemma lem1559073 : term173 = term47.
Proof. exact (TRANS (@lem1559065) (@lem1559072)). Qed.
Lemma lem1559074 (y : real) : (term172 y) = term47.
Proof. exact (TRANS (@lem1559064 y) (@lem1559073)). Qed.
Lemma lem1559075 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559076 (y : real) : (term177 y) = term178.
Proof. exact (MK_COMB (@lem1559075) (@lem1559074 y)). Qed.
Lemma lem1559077 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559078 (y : real) : (term162 y) = term179.
Proof. exact (MK_COMB (@lem1559076 y) (@lem1559077)). Qed.
Lemma lem1559079 (y : real) : (term161 y) = term179.
Proof. exact (TRANS (@lem1559037 y) (@lem1559078 y)). Qed.
Lemma lem1559080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559081 (x : real) (y : real) : (term180 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1559080) (@lem1559036 x y)). Qed.
Lemma lem1559082 (x : real) (y : real) : (term138 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1559081 x y) (@lem1559079 y)). Qed.
Lemma lem1559083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559084 (x : real) (y : real) : (term139 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1559083) (@lem1559003 x y)). Qed.
Lemma lem1559085 (x : real) (y : real) : (term141 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1559084 x y) (@lem1559082 x y)). Qed.
Lemma lem1559086 (y : real) (x : real) : (real_gt y x) = (term184 y x).
Proof. exact (@lem1483525 y x). Qed.
Lemma lem1559092 (y : real) (x : real) : (real_sub y x) = (term147 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1559097 (x : real) (y : real) : (term147 y x) = (term185 x y).
Proof. exact (@lem1483488 (term186 x) y). Qed.
Lemma lem1559099 (x : real) (y : real) : (real_sub y x) = (term185 x y).
Proof. exact (TRANS (@lem1559092 y x) (@lem1559097 x y)). Qed.
Lemma lem1559100 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559101 (x : real) (y : real) : (term187 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1559100) (@lem1559099 x y)). Qed.
Lemma lem1559102 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559103 (x : real) (y : real) : (term184 y x) = (term189 x y).
Proof. exact (MK_COMB (@lem1559101 x y) (@lem1559102)). Qed.
Lemma lem1559104 (x : real) (y : real) : (real_gt y x) = (term189 x y).
Proof. exact (TRANS (@lem1559086 y x) (@lem1559103 x y)). Qed.
Lemma lem1559105 (x : real) : (term161 x) = (term162 x).
Proof. exact (@lem1483525 (term163 x) term47). Qed.
Lemma lem1559106 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559118 (x : real) : (term163 x) = (term164 x).
Proof. exact (@lem1483442 term27 x). Qed.
Lemma lem1559120 (m : nat) : (term165 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1559121 : term166 = term47.
Proof. exact (@lem1559120 term35). Qed.
Lemma lem1559122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1559123 : term167 = term168.
Proof. exact (MK_COMB (@lem1559122) (@lem1559121)). Qed.
Lemma lem1559124 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1559125 (x : real) : (term164 x) = (term169 x).
Proof. exact (MK_COMB (@lem1559123) (@lem1559124 x)). Qed.
Lemma lem1559126 (x : real) : (term163 x) = (term169 x).
Proof. exact (TRANS (@lem1559118 x) (@lem1559125 x)). Qed.
Lemma lem1559127 (x : real) : (term169 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1559129 (x : real) : (term163 x) = term47.
Proof. exact (TRANS (@lem1559126 x) (@lem1559127 x)). Qed.
Lemma lem1559130 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1559131 (x : real) : (term170 x) = term171.
Proof. exact (MK_COMB (@lem1559130) (@lem1559129 x)). Qed.
Lemma lem1559132 (x : real) : (term172 x) = term173.
Proof. exact (MK_COMB (@lem1559131 x) (@lem1559106)). Qed.
Lemma lem1559133 : term173 = term174.
Proof. exact (@lem1483519 term47 term47). Qed.
Lemma lem1559135 (x : nat) : (term155 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1559136 : term156 = term47.
Proof. exact (@lem1559135 term35). Qed.
Lemma lem1559137 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem1559138 : term174 = term176.
Proof. exact (MK_COMB (@lem1559137) (@lem1559136)). Qed.
Lemma lem1559139 : term176 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1559140 : term174 = term47.
Proof. exact (TRANS (@lem1559138) (@lem1559139)). Qed.
Lemma lem1559141 : term173 = term47.
Proof. exact (TRANS (@lem1559133) (@lem1559140)). Qed.
Lemma lem1559142 (x : real) : (term172 x) = term47.
Proof. exact (TRANS (@lem1559132 x) (@lem1559141)). Qed.
Lemma lem1559143 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559144 (x : real) : (term177 x) = term178.
Proof. exact (MK_COMB (@lem1559143) (@lem1559142 x)). Qed.
Lemma lem1559145 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559146 (x : real) : (term162 x) = term179.
Proof. exact (MK_COMB (@lem1559144 x) (@lem1559145)). Qed.
Lemma lem1559147 (x : real) : (term161 x) = term179.
Proof. exact (TRANS (@lem1559105 x) (@lem1559146 x)). Qed.
Lemma lem1559148 (y : real) (x : real) : (term151 y x) = (term152 y x).
Proof. exact (@lem1483525 (term147 y x) term47). Qed.
Lemma lem1559149 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559162 (x : real) (y : real) : (term147 y x) = (term185 x y).
Proof. exact (@lem1483488 (term186 x) y). Qed.
Lemma lem1559163 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1559164 (x : real) (y : real) : (term190 y x) = (term191 x y).
Proof. exact (MK_COMB (@lem1559163) (@lem1559162 x y)). Qed.
Lemma lem1559165 (x : real) (y : real) : (term153 y x) = (term192 x y).
Proof. exact (MK_COMB (@lem1559164 x y) (@lem1559149)). Qed.
Lemma lem1559166 (x : real) (y : real) : (term192 x y) = (term193 x y).
Proof. exact (@lem1483519 (term185 x y) term47). Qed.
Lemma lem1559168 (x : nat) : (term155 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1559169 : term156 = term47.
Proof. exact (@lem1559168 term35). Qed.
Lemma lem1559170 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1559171 (x : real) (y : real) : (term193 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1559170 x y) (@lem1559169)). Qed.
Lemma lem1559172 (x : real) (y : real) : (term195 x y) = (term185 x y).
Proof. exact (@lem1483450 (term185 x y)). Qed.
Lemma lem1559173 (x : real) (y : real) : (term193 x y) = (term185 x y).
Proof. exact (TRANS (@lem1559171 x y) (@lem1559172 x y)). Qed.
Lemma lem1559174 (x : real) (y : real) : (term192 x y) = (term185 x y).
Proof. exact (TRANS (@lem1559166 x y) (@lem1559173 x y)). Qed.
Lemma lem1559175 (x : real) (y : real) : (term153 y x) = (term185 x y).
Proof. exact (TRANS (@lem1559165 x y) (@lem1559174 x y)). Qed.
Lemma lem1559176 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559177 (x : real) (y : real) : (term159 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1559176) (@lem1559175 x y)). Qed.
Lemma lem1559178 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559179 (x : real) (y : real) : (term152 y x) = (term189 x y).
Proof. exact (MK_COMB (@lem1559177 x y) (@lem1559178)). Qed.
Lemma lem1559180 (x : real) (y : real) : (term151 y x) = (term189 x y).
Proof. exact (TRANS (@lem1559148 y x) (@lem1559179 x y)). Qed.
Lemma lem1559181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559182 (x : real) : (term196 x) = term197.
Proof. exact (MK_COMB (@lem1559181) (@lem1559147 x)). Qed.
Lemma lem1559183 (x : real) (y : real) : (term133 y x) = (term198 x y).
Proof. exact (MK_COMB (@lem1559182 x) (@lem1559180 x y)). Qed.
Lemma lem1559184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559185 (x : real) (y : real) : (term134 y x) = (term199 x y).
Proof. exact (MK_COMB (@lem1559184) (@lem1559104 x y)). Qed.
Lemma lem1559186 (x : real) (y : real) : (term136 y x) = (term200 x y).
Proof. exact (MK_COMB (@lem1559185 x y) (@lem1559183 x y)). Qed.
Lemma lem1559187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559188 (x : real) (y : real) : (term143 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1559187) (@lem1559085 x y)). Qed.
Lemma lem1559189 (x : real) (y : real) : (term144 y x) = (term202 x y).
Proof. exact (MK_COMB (@lem1559188 x y) (@lem1559186 x y)). Qed.
Lemma lem1559200 (x : real) (y : real) : (term128 y x) = (term202 x y).
Proof. exact (TRANS (@lem1558984 y x) (@lem1559189 x y)). Qed.
Lemma lem1559201 (x : real) (y : real) : (term53 y x) = (term202 x y).
Proof. exact (TRANS (@lem1558968 y x) (@lem1559200 x y)). Qed.
Lemma lem1559203 (x : real) (a : real) (y : real) (r : real) : (term203 a x y r) = (term112 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1559204 (y : real) (x : real) : (term49 y x) = (term113 y x).
Proof. exact (@lem1559203 y (term28 x y) x term47). Qed.
Lemma lem1559217 (x : real) (y : real) : (term114 y x) = (term115 x y).
Proof. exact (@lem1483488 x (term28 x y)). Qed.
Lemma lem1559218 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559219 (x : real) (y : real) : (term116 y x) = (term117 x y).
Proof. exact (MK_COMB (@lem1559218) (@lem1559217 x y)). Qed.
Lemma lem1559220 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559221 (x : real) (y : real) : (term118 y x) = (term119 x y).
Proof. exact (MK_COMB (@lem1559219 x y) (@lem1559220)). Qed.
Lemma lem1559234 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (@lem1483488 y (term28 x y)). Qed.
Lemma lem1559235 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559236 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1559235) (@lem1559234 x y)). Qed.
Lemma lem1559237 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559238 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1559236 x y) (@lem1559237)). Qed.
Lemma lem1559239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559240 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1559239) (@lem1559238 x y)). Qed.
Lemma lem1559241 (x : real) (y : real) : (term113 y x) = (term128 x y).
Proof. exact (MK_COMB (@lem1559240 x y) (@lem1559221 x y)). Qed.
Lemma lem1559242 (x : real) (y : real) : (term49 y x) = (term128 x y).
Proof. exact (TRANS (@lem1559204 y x) (@lem1559241 x y)). Qed.
Lemma lem1559243 (x : real) (y : real) : (term129 x y) = (term128 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1559244 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (SYM (@lem1559243 x y)). Qed.
Lemma lem1559245 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (@lem1483429 x (term131 y x) y). Qed.
Lemma lem1559246 (x : real) (y : real) : (term128 x y) = (term130 x y).
Proof. exact (TRANS (@lem1559244 x y) (@lem1559245 x y)). Qed.
Lemma lem1559247 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1559248 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1559249 (x : real) (y : real) : (term135 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1559248 x y) (@lem1559247 x y)). Qed.
Lemma lem1559250 (y : real) (x : real) : (term137 y x) = (term138 y x).
Proof. exact (eq_refl (term137 y x)). Qed.
Lemma lem1559251 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1559252 (y : real) (x : real) : (term140 y x) = (term141 y x).
Proof. exact (MK_COMB (@lem1559251 y x) (@lem1559250 y x)). Qed.
Lemma lem1559253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559254 (y : real) (x : real) : (term142 y x) = (term143 y x).
Proof. exact (MK_COMB (@lem1559253) (@lem1559252 y x)). Qed.
Lemma lem1559255 (x : real) (y : real) : (term130 x y) = (term144 x y).
Proof. exact (MK_COMB (@lem1559254 y x) (@lem1559249 x y)). Qed.
Lemma lem1559256 (x : real) (y : real) : (term145 x y) = (term145 x y).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1559257 (x : real) (y : real) : ((term128 x y) = (term130 x y)) = ((term128 x y) = (term144 x y)).
Proof. exact (MK_COMB (@lem1559256 x y) (@lem1559255 x y)). Qed.
Lemma lem1559258 (x : real) (y : real) : (term128 x y) = (term144 x y).
Proof. exact (EQ_MP (@lem1559257 x y) (@lem1559246 x y)). Qed.
Lemma lem1559259 (y : real) (x : real) : (real_ge y x) = (term146 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1559265 (y : real) (x : real) : (real_sub y x) = (term147 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1559270 (x : real) (y : real) : (term147 y x) = (term185 x y).
Proof. exact (@lem1483488 (term186 x) y). Qed.
Lemma lem1559272 (x : real) (y : real) : (real_sub y x) = (term185 x y).
Proof. exact (TRANS (@lem1559265 y x) (@lem1559270 x y)). Qed.
Lemma lem1559273 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1559274 (x : real) (y : real) : (term148 y x) = (term204 x y).
Proof. exact (MK_COMB (@lem1559273) (@lem1559272 x y)). Qed.
Lemma lem1559275 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559276 (x : real) (y : real) : (term146 y x) = (term205 x y).
Proof. exact (MK_COMB (@lem1559274 x y) (@lem1559275)). Qed.
Lemma lem1559277 (x : real) (y : real) : (real_ge y x) = (term205 x y).
Proof. exact (TRANS (@lem1559259 y x) (@lem1559276 x y)). Qed.
Lemma lem1559278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559279 (x : real) (y : real) : (term180 y x) = (term199 x y).
Proof. exact (MK_COMB (@lem1559278) (@lem1559180 x y)). Qed.
Lemma lem1559280 (x : real) (y : real) : (term138 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem1559279 x y) (@lem1559147 x)). Qed.
Lemma lem1559281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559282 (x : real) (y : real) : (term139 y x) = (term207 x y).
Proof. exact (MK_COMB (@lem1559281) (@lem1559277 x y)). Qed.
Lemma lem1559283 (x : real) (y : real) : (term141 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1559282 x y) (@lem1559280 x y)). Qed.
Lemma lem1559284 (x : real) (y : real) : (real_gt x y) = (term184 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1559297 (x : real) (y : real) : (real_sub x y) = (term147 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1559298 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559299 (x : real) (y : real) : (term187 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1559298) (@lem1559297 x y)). Qed.
Lemma lem1559300 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1559301 (x : real) (y : real) : (term184 x y) = (term151 x y).
Proof. exact (MK_COMB (@lem1559299 x y) (@lem1559300)). Qed.
Lemma lem1559302 (x : real) (y : real) : (real_gt x y) = (term151 x y).
Proof. exact (TRANS (@lem1559284 x y) (@lem1559301 x y)). Qed.
Lemma lem1559303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559304 (y : real) : (term196 y) = term197.
Proof. exact (MK_COMB (@lem1559303) (@lem1559079 y)). Qed.
Lemma lem1559305 (x : real) (y : real) : (term133 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1559304 y) (@lem1559036 x y)). Qed.
Lemma lem1559306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559307 (x : real) (y : real) : (term134 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1559306) (@lem1559302 x y)). Qed.
Lemma lem1559308 (x : real) (y : real) : (term136 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1559307 x y) (@lem1559305 x y)). Qed.
Lemma lem1559309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559310 (x : real) (y : real) : (term143 y x) = (term211 x y).
Proof. exact (MK_COMB (@lem1559309) (@lem1559283 x y)). Qed.
Lemma lem1559311 (x : real) (y : real) : (term144 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem1559310 x y) (@lem1559308 x y)). Qed.
Lemma lem1559322 (x : real) (y : real) : (term128 x y) = (term212 x y).
Proof. exact (TRANS (@lem1559258 x y) (@lem1559311 x y)). Qed.
Lemma lem1559323 (x : real) (y : real) : (term49 y x) = (term212 x y).
Proof. exact (TRANS (@lem1559242 x y) (@lem1559322 x y)). Qed.
Lemma lem1559324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559325 (x : real) (y : real) : (term55 y x) = (term213 x y).
Proof. exact (MK_COMB (@lem1559324) (@lem1559201 x y)). Qed.
Lemma lem1559326 (x : real) (y : real) : (term56 y x) = (term214 x y).
Proof. exact (MK_COMB (@lem1559325 x y) (@lem1559323 x y)). Qed.
Lemma lem1559327 (x : real) (y : real) (h1 : term214 x y) : term214 x y.
Proof. exact (h1). Qed.
Lemma lem1559328 (x : real) (y : real) (h1 : term202 x y) : term202 x y.
Proof. exact (h1). Qed.
Lemma lem1559329 (x : real) (y : real) (h1 : term183 x y) : term183 x y.
Proof. exact (h1). Qed.
Lemma lem1559330 (x : real) (y : real) (h1 : term183 x y) : term181 x y.
Proof. exact (proj2 (@lem1559329 x y h1)). Qed.
Lemma lem1559332 (x : real) (y : real) (h1 : term183 x y) : term179.
Proof. exact (proj2 (@lem1559330 x y h1)). Qed.
Lemma lem1559335 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1559336 : term179 = term216.
Proof. exact (@lem1559335 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1559337 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1559338 : term179 = False.
Proof. exact (TRANS (@lem1559336) (@lem1559337)). Qed.
Lemma lem1559339 (x : real) (y : real) (h1 : term183 x y) : False.
Proof. exact (EQ_MP (@lem1559338) (@lem1559332 x y h1)). Qed.
Lemma lem1559340 (x : real) (y : real) (h1 : term200 x y) : term200 x y.
Proof. exact (h1). Qed.
Lemma lem1559341 (x : real) (y : real) (h1 : term200 x y) : term198 x y.
Proof. exact (proj2 (@lem1559340 x y h1)). Qed.
Lemma lem1559344 (x : real) (y : real) (h1 : term200 x y) : term179.
Proof. exact (proj1 (@lem1559341 x y h1)). Qed.
Lemma lem1559346 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1559347 : term179 = term216.
Proof. exact (@lem1559346 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1559348 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1559349 : term179 = False.
Proof. exact (TRANS (@lem1559347) (@lem1559348)). Qed.
Lemma lem1559350 (x : real) (y : real) (h1 : term200 x y) : False.
Proof. exact (EQ_MP (@lem1559349) (@lem1559344 x y h1)). Qed.
Lemma lem1559351 (x : real) (y : real) (h1 : term202 x y) : False.
Proof. exact (or_elim (@lem1559328 x y h1) (fun h0 : term183 x y => @lem1559339 x y h0) (fun h0 : term200 x y => @lem1559350 x y h0)). Qed.
Lemma lem1559352 (x : real) (y : real) (h1 : term212 x y) : term212 x y.
Proof. exact (h1). Qed.
Lemma lem1559353 (x : real) (y : real) (h1 : term208 x y) : term208 x y.
Proof. exact (h1). Qed.
Lemma lem1559354 (x : real) (y : real) (h1 : term208 x y) : term206 x y.
Proof. exact (proj2 (@lem1559353 x y h1)). Qed.
Lemma lem1559356 (x : real) (y : real) (h1 : term208 x y) : term179.
Proof. exact (proj2 (@lem1559354 x y h1)). Qed.
Lemma lem1559359 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1559360 : term179 = term216.
Proof. exact (@lem1559359 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1559361 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1559362 : term179 = False.
Proof. exact (TRANS (@lem1559360) (@lem1559361)). Qed.
Lemma lem1559363 (x : real) (y : real) (h1 : term208 x y) : False.
Proof. exact (EQ_MP (@lem1559362) (@lem1559356 x y h1)). Qed.
Lemma lem1559364 (x : real) (y : real) (h1 : term210 x y) : term210 x y.
Proof. exact (h1). Qed.
Lemma lem1559365 (x : real) (y : real) (h1 : term210 x y) : term209 x y.
Proof. exact (proj2 (@lem1559364 x y h1)). Qed.
Lemma lem1559368 (x : real) (y : real) (h1 : term210 x y) : term179.
Proof. exact (proj1 (@lem1559365 x y h1)). Qed.
Lemma lem1559370 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1559371 : term179 = term216.
Proof. exact (@lem1559370 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1559372 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1559373 : term179 = False.
Proof. exact (TRANS (@lem1559371) (@lem1559372)). Qed.
Lemma lem1559374 (x : real) (y : real) (h1 : term210 x y) : False.
Proof. exact (EQ_MP (@lem1559373) (@lem1559368 x y h1)). Qed.
Lemma lem1559375 (x : real) (y : real) (h1 : term212 x y) : False.
Proof. exact (or_elim (@lem1559352 x y h1) (fun h0 : term208 x y => @lem1559363 x y h0) (fun h0 : term210 x y => @lem1559374 x y h0)). Qed.
Lemma lem1559376 (x : real) (y : real) (h1 : term214 x y) : False.
Proof. exact (or_elim (@lem1559327 x y h1) (fun h0 : term202 x y => @lem1559351 x y h0) (fun h0 : term212 x y => @lem1559375 x y h0)). Qed.
Lemma lem1559377 (y : real) (x : real) (h1 : term56 y x) : term56 y x.
Proof. exact (h1). Qed.
Lemma lem1559378 (y : real) (x : real) (h1 : term56 y x) : term214 x y.
Proof. exact (EQ_MP (@lem1559326 x y) (@lem1559377 y x h1)). Qed.
Lemma lem1559379 (y : real) (x : real) (h1 : term56 y x) : (term214 x y) = False.
Proof. exact (prop_ext (fun h2 : term214 x y => @lem1559376 x y h2) (fun h2 : False => @lem1559378 y x h1)). Qed.
Lemma lem1559380 (y : real) (x : real) (h1 : term56 y x) : False.
Proof. exact (EQ_MP (@lem1559379 y x h1) (@lem1559378 y x h1)). Qed.
Lemma lem1559381 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1559382 (x : real) (h1 : term58 x) : False.
Proof. exact (ex_elim (@lem1559381 x h1) (fun y : real => fun h0 : term57 x y => @lem1559380 y x h0)). Qed.
Lemma lem1559383 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem1559384 (h1 : term60) : False.
Proof. exact (ex_elim (@lem1559383 h1) (fun x : real => fun h0 : term59 x => @lem1559382 x h0)). Qed.
Lemma lem1559385 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1559386 (h1 : term11) : term60.
Proof. exact (EQ_MP (@lem1558927) (@lem1559385 h1)). Qed.
Lemma lem1559387 (h1 : term11) : term60 = False.
Proof. exact (prop_ext (fun h2 : term60 => @lem1559384 h2) (fun h2 : False => @lem1559386 h1)). Qed.
Lemma lem1559388 (h1 : term11) : False.
Proof. exact (EQ_MP (@lem1559387 h1) (@lem1559386 h1)). Qed.
Lemma lem1559389 : term217.
Proof. exact (fun h0 : term11 => @lem1559388 h0). Qed.
Lemma lem1559390 : term218.
Proof. exact (@lem1386578 term219). Qed.
Lemma lem1559391 : term219.
Proof. exact (@lem1559390 (@lem1559389)). Qed.

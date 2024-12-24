Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DELETE_term_abbrevs.
Require Import ITERATE_DELETE_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988293_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988338_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7119703 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17646 (y = (real_sub z x)) ((real_add x y) = z)). Qed.
Lemma lem7119704 (y : real) (z : real) (x : real) : (y = (real_sub z x)) = ((term2 y z x) = term3).
Proof. exact (@lem1988293 y (real_sub z x)). Qed.
Lemma lem7119710 (z : real) (x : real) : (real_sub z x) = (term4 z x).
Proof. exact (@lem1982792 z x). Qed.
Lemma lem7119715 (x : real) (z : real) : (term4 z x) = (term5 x z).
Proof. exact (@lem1982761 (term6 x) z). Qed.
Lemma lem7119717 (x : real) (z : real) : (real_sub z x) = (term5 x z).
Proof. exact (TRANS (@lem7119710 z x) (@lem7119715 x z)). Qed.
Lemma lem7119720 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem7119721 (y : real) (x : real) (z : real) : (term2 y z x) = (term7 y x z).
Proof. exact (MK_COMB (@lem7119720 y) (@lem7119717 x z)). Qed.
Lemma lem7119722 (y : real) (x : real) (z : real) : (term7 y x z) = (term8 y x z).
Proof. exact (@lem1982792 y (term5 x z)). Qed.
Lemma lem7119723 (x : real) (z : real) : (term9 x z) = (term10 x z).
Proof. exact (@lem1982781 (term6 x) term11 z). Qed.
Lemma lem7119724 (z : real) : (term6 z) = (term6 z).
Proof. exact (eq_refl (term6 z)). Qed.
Lemma lem7119725 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1982749 term11 term11 x). Qed.
Lemma lem7119727 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119728 : term11 = term16.
Proof. exact (@lem7119727 term17). Qed.
Lemma lem7119730 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119731 : term11 = term16.
Proof. exact (@lem7119730 term17). Qed.
Lemma lem7119732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119733 : term18 = term19.
Proof. exact (MK_COMB (@lem7119732) (@lem7119731)). Qed.
Lemma lem7119734 : term20 = term21.
Proof. exact (MK_COMB (@lem7119733) (@lem7119728)). Qed.
Lemma lem7119735 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7119737 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7119738 : term26 = term27.
Proof. exact (@lem7119737 term17 term17). Qed.
Lemma lem7119739 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119740 : term29 = term17.
Proof. exact (EQ_MP (@lem7119739) (@lem940073)). Qed.
Lemma lem7119741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119742 : term27 = term23.
Proof. exact (MK_COMB (@lem7119741) (@lem7119740)). Qed.
Lemma lem7119743 : term26 = term23.
Proof. exact (TRANS (@lem7119738) (@lem7119742)). Qed.
Lemma lem7119745 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7119746 : term20 = term27.
Proof. exact (@lem7119745 term17 term17). Qed.
Lemma lem7119747 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119748 : term29 = term17.
Proof. exact (EQ_MP (@lem7119747) (@lem940073)). Qed.
Lemma lem7119749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119750 : term27 = term23.
Proof. exact (MK_COMB (@lem7119749) (@lem7119748)). Qed.
Lemma lem7119751 : term20 = term23.
Proof. exact (TRANS (@lem7119746) (@lem7119750)). Qed.
Lemma lem7119752 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7119753 : term31 = term32.
Proof. exact (MK_COMB (@lem7119752) (@lem7119751)). Qed.
Lemma lem7119754 : term22 = term33.
Proof. exact (MK_COMB (@lem7119753) (@lem7119743)). Qed.
Lemma lem7119755 : term21 = term33.
Proof. exact (TRANS (@lem7119735) (@lem7119754)). Qed.
Lemma lem7119756 : term20 = term33.
Proof. exact (TRANS (@lem7119734) (@lem7119755)). Qed.
Lemma lem7119758 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7119759 : term33 = term23.
Proof. exact (@lem7119758 term23). Qed.
Lemma lem7119760 : term20 = term23.
Proof. exact (TRANS (@lem7119756) (@lem7119759)). Qed.
Lemma lem7119761 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119762 : term35 = term36.
Proof. exact (MK_COMB (@lem7119761) (@lem7119760)). Qed.
Lemma lem7119763 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7119764 (x : real) : (term13 x) = (term37 x).
Proof. exact (MK_COMB (@lem7119762) (@lem7119763 x)). Qed.
Lemma lem7119765 (x : real) : (term12 x) = (term37 x).
Proof. exact (TRANS (@lem7119725 x) (@lem7119764 x)). Qed.
Lemma lem7119766 (x : real) : (term37 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem7119767 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem7119765 x) (@lem7119766 x)). Qed.
Lemma lem7119768 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7119769 (x : real) : (term38 x) = (real_add x).
Proof. exact (MK_COMB (@lem7119768) (@lem7119767 x)). Qed.
Lemma lem7119770 (x : real) (z : real) : (term10 x z) = (term4 x z).
Proof. exact (MK_COMB (@lem7119769 x) (@lem7119724 z)). Qed.
Lemma lem7119771 (x : real) (z : real) : (term9 x z) = (term4 x z).
Proof. exact (TRANS (@lem7119723 x z) (@lem7119770 x z)). Qed.
Lemma lem7119772 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7119773 (y : real) (x : real) (z : real) : (term8 y x z) = (term39 y x z).
Proof. exact (MK_COMB (@lem7119772 y) (@lem7119771 x z)). Qed.
Lemma lem7119778 (x : real) (y : real) (z : real) : (term39 y x z) = (term39 x y z).
Proof. exact (@lem1982757 x y (term6 z)). Qed.
Lemma lem7119779 (x : real) (y : real) (z : real) : (term8 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem7119773 y x z) (@lem7119778 x y z)). Qed.
Lemma lem7119780 (x : real) (y : real) (z : real) : (term7 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem7119722 y x z) (@lem7119779 x y z)). Qed.
Lemma lem7119781 (x : real) (y : real) (z : real) : (term2 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem7119721 y x z) (@lem7119780 x y z)). Qed.
Lemma lem7119782 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7119783 (x : real) (y : real) (z : real) : (term40 y z x) = (term41 x y z).
Proof. exact (MK_COMB (@lem7119782) (@lem7119781 x y z)). Qed.
Lemma lem7119784 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7119785 (x : real) (y : real) (z : real) : ((term2 y z x) = term3) = ((term39 x y z) = term3).
Proof. exact (MK_COMB (@lem7119783 x y z) (@lem7119784)). Qed.
Lemma lem7119786 (x : real) (y : real) (z : real) : (y = (real_sub z x)) = ((term39 x y z) = term3).
Proof. exact (TRANS (@lem7119704 y z x) (@lem7119785 x y z)). Qed.
Lemma lem7119787 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 x y z).
Proof. exact (@lem1988318 (real_add x y) z). Qed.
Lemma lem7119799 (x : real) (y : real) (z : real) : (term44 x y z) = (term45 x y z).
Proof. exact (@lem1982792 (real_add x y) z). Qed.
Lemma lem7119808 (x : real) (y : real) (z : real) : (term45 x y z) = (term39 x y z).
Proof. exact (@lem1982755 x y (term6 z)). Qed.
Lemma lem7119810 (x : real) (y : real) (z : real) : (term44 x y z) = (term39 x y z).
Proof. exact (TRANS (@lem7119799 x y z) (@lem7119808 x y z)). Qed.
Lemma lem7119811 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7119812 (x : real) (y : real) (z : real) : (term46 x y z) = (term47 x y z).
Proof. exact (MK_COMB (@lem7119811) (@lem7119810 x y z)). Qed.
Lemma lem7119813 (x : real) (y : real) (z : real) : (term47 x y z) = (term48 x y z).
Proof. exact (@lem1982785 (term39 x y z)). Qed.
Lemma lem7119814 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (@lem1982781 x term11 (term4 y z)). Qed.
Lemma lem7119815 (y : real) (z : real) : (term50 y z) = (term51 y z).
Proof. exact (@lem1982781 y term11 (term6 z)). Qed.
Lemma lem7119816 (z : real) : (term12 z) = (term13 z).
Proof. exact (@lem1982749 term11 term11 z). Qed.
Lemma lem7119818 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119819 : term11 = term16.
Proof. exact (@lem7119818 term17). Qed.
Lemma lem7119821 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119822 : term11 = term16.
Proof. exact (@lem7119821 term17). Qed.
Lemma lem7119823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119824 : term18 = term19.
Proof. exact (MK_COMB (@lem7119823) (@lem7119822)). Qed.
Lemma lem7119825 : term20 = term21.
Proof. exact (MK_COMB (@lem7119824) (@lem7119819)). Qed.
Lemma lem7119826 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7119828 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7119829 : term26 = term27.
Proof. exact (@lem7119828 term17 term17). Qed.
Lemma lem7119830 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119831 : term29 = term17.
Proof. exact (EQ_MP (@lem7119830) (@lem940073)). Qed.
Lemma lem7119832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119833 : term27 = term23.
Proof. exact (MK_COMB (@lem7119832) (@lem7119831)). Qed.
Lemma lem7119834 : term26 = term23.
Proof. exact (TRANS (@lem7119829) (@lem7119833)). Qed.
Lemma lem7119836 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7119837 : term20 = term27.
Proof. exact (@lem7119836 term17 term17). Qed.
Lemma lem7119838 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119839 : term29 = term17.
Proof. exact (EQ_MP (@lem7119838) (@lem940073)). Qed.
Lemma lem7119840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119841 : term27 = term23.
Proof. exact (MK_COMB (@lem7119840) (@lem7119839)). Qed.
Lemma lem7119842 : term20 = term23.
Proof. exact (TRANS (@lem7119837) (@lem7119841)). Qed.
Lemma lem7119843 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7119844 : term31 = term32.
Proof. exact (MK_COMB (@lem7119843) (@lem7119842)). Qed.
Lemma lem7119845 : term22 = term33.
Proof. exact (MK_COMB (@lem7119844) (@lem7119834)). Qed.
Lemma lem7119846 : term21 = term33.
Proof. exact (TRANS (@lem7119826) (@lem7119845)). Qed.
Lemma lem7119847 : term20 = term33.
Proof. exact (TRANS (@lem7119825) (@lem7119846)). Qed.
Lemma lem7119849 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7119850 : term33 = term23.
Proof. exact (@lem7119849 term23). Qed.
Lemma lem7119851 : term20 = term23.
Proof. exact (TRANS (@lem7119847) (@lem7119850)). Qed.
Lemma lem7119852 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119853 : term35 = term36.
Proof. exact (MK_COMB (@lem7119852) (@lem7119851)). Qed.
Lemma lem7119854 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7119855 (z : real) : (term13 z) = (term37 z).
Proof. exact (MK_COMB (@lem7119853) (@lem7119854 z)). Qed.
Lemma lem7119856 (z : real) : (term12 z) = (term37 z).
Proof. exact (TRANS (@lem7119816 z) (@lem7119855 z)). Qed.
Lemma lem7119857 (z : real) : (term37 z) = z.
Proof. exact (@lem1982709 z). Qed.
Lemma lem7119858 (z : real) : (term12 z) = z.
Proof. exact (TRANS (@lem7119856 z) (@lem7119857 z)). Qed.
Lemma lem7119861 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem7119862 (y : real) (z : real) : (term51 y z) = (term5 y z).
Proof. exact (MK_COMB (@lem7119861 y) (@lem7119858 z)). Qed.
Lemma lem7119863 (y : real) (z : real) : (term50 y z) = (term5 y z).
Proof. exact (TRANS (@lem7119815 y z) (@lem7119862 y z)). Qed.
Lemma lem7119866 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem7119867 (x : real) (y : real) (z : real) : (term49 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem7119866 x) (@lem7119863 y z)). Qed.
Lemma lem7119868 (x : real) (y : real) (z : real) : (term48 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7119814 x y z) (@lem7119867 x y z)). Qed.
Lemma lem7119869 (x : real) (y : real) (z : real) : (term47 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7119813 x y z) (@lem7119868 x y z)). Qed.
Lemma lem7119870 (x : real) (y : real) (z : real) : (term54 x y z) = (term54 x y z).
Proof. exact (eq_refl (term54 x y z)). Qed.
Lemma lem7119871 (x : real) (y : real) (z : real) : ((term46 x y z) = (term47 x y z)) = ((term46 x y z) = (term53 x y z)).
Proof. exact (MK_COMB (@lem7119870 x y z) (@lem7119869 x y z)). Qed.
Lemma lem7119872 (x : real) (y : real) (z : real) : (term46 x y z) = (term53 x y z).
Proof. exact (EQ_MP (@lem7119871 x y z) (@lem7119812 x y z)). Qed.
Lemma lem7119873 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7119874 (x : real) (y : real) (z : real) : (term55 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem7119873) (@lem7119872 x y z)). Qed.
Lemma lem7119875 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7119876 (x : real) (y : real) (z : real) : (term57 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem7119874 x y z) (@lem7119875)). Qed.
Lemma lem7119877 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7119878 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem7119877) (@lem7119810 x y z)). Qed.
Lemma lem7119879 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7119880 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem7119878 x y z) (@lem7119879)). Qed.
Lemma lem7119881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7119882 (x : real) (y : real) (z : real) : (term63 x y z) = (term64 x y z).
Proof. exact (MK_COMB (@lem7119881) (@lem7119880 x y z)). Qed.
Lemma lem7119883 (x : real) (y : real) (z : real) : (term43 x y z) = (term65 x y z).
Proof. exact (MK_COMB (@lem7119882 x y z) (@lem7119876 x y z)). Qed.
Lemma lem7119884 (x : real) (y : real) (z : real) : (term42 x y z) = (term65 x y z).
Proof. exact (TRANS (@lem7119787 x y z) (@lem7119883 x y z)). Qed.
Lemma lem7119885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119886 (x : real) (y : real) (z : real) : (term66 y z x) = (term67 x y z).
Proof. exact (MK_COMB (@lem7119885) (@lem7119786 x y z)). Qed.
Lemma lem7119887 (x : real) (y : real) (z : real) : (term68 x y z) = (term69 x y z).
Proof. exact (MK_COMB (@lem7119886 x y z) (@lem7119884 x y z)). Qed.
Lemma lem7119888 (y : real) (z : real) (x : real) : (term70 y z x) = (term71 y z x).
Proof. exact (@lem1988318 y (real_sub z x)). Qed.
Lemma lem7119894 (z : real) (x : real) : (real_sub z x) = (term4 z x).
Proof. exact (@lem1982792 z x). Qed.
Lemma lem7119899 (x : real) (z : real) : (term4 z x) = (term5 x z).
Proof. exact (@lem1982761 (term6 x) z). Qed.
Lemma lem7119901 (x : real) (z : real) : (real_sub z x) = (term5 x z).
Proof. exact (TRANS (@lem7119894 z x) (@lem7119899 x z)). Qed.
Lemma lem7119904 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem7119905 (y : real) (x : real) (z : real) : (term2 y z x) = (term7 y x z).
Proof. exact (MK_COMB (@lem7119904 y) (@lem7119901 x z)). Qed.
Lemma lem7119906 (y : real) (x : real) (z : real) : (term7 y x z) = (term8 y x z).
Proof. exact (@lem1982792 y (term5 x z)). Qed.
Lemma lem7119907 (x : real) (z : real) : (term9 x z) = (term10 x z).
Proof. exact (@lem1982781 (term6 x) term11 z). Qed.
Lemma lem7119908 (z : real) : (term6 z) = (term6 z).
Proof. exact (eq_refl (term6 z)). Qed.
Lemma lem7119909 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1982749 term11 term11 x). Qed.
Lemma lem7119911 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119912 : term11 = term16.
Proof. exact (@lem7119911 term17). Qed.
Lemma lem7119914 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119915 : term11 = term16.
Proof. exact (@lem7119914 term17). Qed.
Lemma lem7119916 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119917 : term18 = term19.
Proof. exact (MK_COMB (@lem7119916) (@lem7119915)). Qed.
Lemma lem7119918 : term20 = term21.
Proof. exact (MK_COMB (@lem7119917) (@lem7119912)). Qed.
Lemma lem7119919 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7119921 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7119922 : term26 = term27.
Proof. exact (@lem7119921 term17 term17). Qed.
Lemma lem7119923 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119924 : term29 = term17.
Proof. exact (EQ_MP (@lem7119923) (@lem940073)). Qed.
Lemma lem7119925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119926 : term27 = term23.
Proof. exact (MK_COMB (@lem7119925) (@lem7119924)). Qed.
Lemma lem7119927 : term26 = term23.
Proof. exact (TRANS (@lem7119922) (@lem7119926)). Qed.
Lemma lem7119929 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7119930 : term20 = term27.
Proof. exact (@lem7119929 term17 term17). Qed.
Lemma lem7119931 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119932 : term29 = term17.
Proof. exact (EQ_MP (@lem7119931) (@lem940073)). Qed.
Lemma lem7119933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119934 : term27 = term23.
Proof. exact (MK_COMB (@lem7119933) (@lem7119932)). Qed.
Lemma lem7119935 : term20 = term23.
Proof. exact (TRANS (@lem7119930) (@lem7119934)). Qed.
Lemma lem7119936 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7119937 : term31 = term32.
Proof. exact (MK_COMB (@lem7119936) (@lem7119935)). Qed.
Lemma lem7119938 : term22 = term33.
Proof. exact (MK_COMB (@lem7119937) (@lem7119927)). Qed.
Lemma lem7119939 : term21 = term33.
Proof. exact (TRANS (@lem7119919) (@lem7119938)). Qed.
Lemma lem7119940 : term20 = term33.
Proof. exact (TRANS (@lem7119918) (@lem7119939)). Qed.
Lemma lem7119942 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7119943 : term33 = term23.
Proof. exact (@lem7119942 term23). Qed.
Lemma lem7119944 : term20 = term23.
Proof. exact (TRANS (@lem7119940) (@lem7119943)). Qed.
Lemma lem7119945 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119946 : term35 = term36.
Proof. exact (MK_COMB (@lem7119945) (@lem7119944)). Qed.
Lemma lem7119947 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7119948 (x : real) : (term13 x) = (term37 x).
Proof. exact (MK_COMB (@lem7119946) (@lem7119947 x)). Qed.
Lemma lem7119949 (x : real) : (term12 x) = (term37 x).
Proof. exact (TRANS (@lem7119909 x) (@lem7119948 x)). Qed.
Lemma lem7119950 (x : real) : (term37 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem7119951 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem7119949 x) (@lem7119950 x)). Qed.
Lemma lem7119952 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7119953 (x : real) : (term38 x) = (real_add x).
Proof. exact (MK_COMB (@lem7119952) (@lem7119951 x)). Qed.
Lemma lem7119954 (x : real) (z : real) : (term10 x z) = (term4 x z).
Proof. exact (MK_COMB (@lem7119953 x) (@lem7119908 z)). Qed.
Lemma lem7119955 (x : real) (z : real) : (term9 x z) = (term4 x z).
Proof. exact (TRANS (@lem7119907 x z) (@lem7119954 x z)). Qed.
Lemma lem7119956 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7119957 (y : real) (x : real) (z : real) : (term8 y x z) = (term39 y x z).
Proof. exact (MK_COMB (@lem7119956 y) (@lem7119955 x z)). Qed.
Lemma lem7119962 (x : real) (y : real) (z : real) : (term39 y x z) = (term39 x y z).
Proof. exact (@lem1982757 x y (term6 z)). Qed.
Lemma lem7119963 (x : real) (y : real) (z : real) : (term8 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem7119957 y x z) (@lem7119962 x y z)). Qed.
Lemma lem7119964 (x : real) (y : real) (z : real) : (term7 y x z) = (term39 x y z).
Proof. exact (TRANS (@lem7119906 y x z) (@lem7119963 x y z)). Qed.
Lemma lem7119965 (x : real) (y : real) (z : real) : (term2 y z x) = (term39 x y z).
Proof. exact (TRANS (@lem7119905 y x z) (@lem7119964 x y z)). Qed.
Lemma lem7119966 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7119967 (x : real) (y : real) (z : real) : (term72 y z x) = (term47 x y z).
Proof. exact (MK_COMB (@lem7119966) (@lem7119965 x y z)). Qed.
Lemma lem7119968 (x : real) (y : real) (z : real) : (term47 x y z) = (term48 x y z).
Proof. exact (@lem1982785 (term39 x y z)). Qed.
Lemma lem7119969 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (@lem1982781 x term11 (term4 y z)). Qed.
Lemma lem7119970 (y : real) (z : real) : (term50 y z) = (term51 y z).
Proof. exact (@lem1982781 y term11 (term6 z)). Qed.
Lemma lem7119971 (z : real) : (term12 z) = (term13 z).
Proof. exact (@lem1982749 term11 term11 z). Qed.
Lemma lem7119973 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119974 : term11 = term16.
Proof. exact (@lem7119973 term17). Qed.
Lemma lem7119976 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7119977 : term11 = term16.
Proof. exact (@lem7119976 term17). Qed.
Lemma lem7119978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7119979 : term18 = term19.
Proof. exact (MK_COMB (@lem7119978) (@lem7119977)). Qed.
Lemma lem7119980 : term20 = term21.
Proof. exact (MK_COMB (@lem7119979) (@lem7119974)). Qed.
Lemma lem7119981 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7119983 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7119984 : term26 = term27.
Proof. exact (@lem7119983 term17 term17). Qed.
Lemma lem7119985 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119986 : term29 = term17.
Proof. exact (EQ_MP (@lem7119985) (@lem940073)). Qed.
Lemma lem7119987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119988 : term27 = term23.
Proof. exact (MK_COMB (@lem7119987) (@lem7119986)). Qed.
Lemma lem7119989 : term26 = term23.
Proof. exact (TRANS (@lem7119984) (@lem7119988)). Qed.
Lemma lem7119991 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7119992 : term20 = term27.
Proof. exact (@lem7119991 term17 term17). Qed.
Lemma lem7119993 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7119994 : term29 = term17.
Proof. exact (EQ_MP (@lem7119993) (@lem940073)). Qed.
Lemma lem7119995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7119996 : term27 = term23.
Proof. exact (MK_COMB (@lem7119995) (@lem7119994)). Qed.
Lemma lem7119997 : term20 = term23.
Proof. exact (TRANS (@lem7119992) (@lem7119996)). Qed.
Lemma lem7119998 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7119999 : term31 = term32.
Proof. exact (MK_COMB (@lem7119998) (@lem7119997)). Qed.
Lemma lem7120000 : term22 = term33.
Proof. exact (MK_COMB (@lem7119999) (@lem7119989)). Qed.
Lemma lem7120001 : term21 = term33.
Proof. exact (TRANS (@lem7119981) (@lem7120000)). Qed.
Lemma lem7120002 : term20 = term33.
Proof. exact (TRANS (@lem7119980) (@lem7120001)). Qed.
Lemma lem7120004 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7120005 : term33 = term23.
Proof. exact (@lem7120004 term23). Qed.
Lemma lem7120006 : term20 = term23.
Proof. exact (TRANS (@lem7120002) (@lem7120005)). Qed.
Lemma lem7120007 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120008 : term35 = term36.
Proof. exact (MK_COMB (@lem7120007) (@lem7120006)). Qed.
Lemma lem7120009 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7120010 (z : real) : (term13 z) = (term37 z).
Proof. exact (MK_COMB (@lem7120008) (@lem7120009 z)). Qed.
Lemma lem7120011 (z : real) : (term12 z) = (term37 z).
Proof. exact (TRANS (@lem7119971 z) (@lem7120010 z)). Qed.
Lemma lem7120012 (z : real) : (term37 z) = z.
Proof. exact (@lem1982709 z). Qed.
Lemma lem7120013 (z : real) : (term12 z) = z.
Proof. exact (TRANS (@lem7120011 z) (@lem7120012 z)). Qed.
Lemma lem7120016 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem7120017 (y : real) (z : real) : (term51 y z) = (term5 y z).
Proof. exact (MK_COMB (@lem7120016 y) (@lem7120013 z)). Qed.
Lemma lem7120018 (y : real) (z : real) : (term50 y z) = (term5 y z).
Proof. exact (TRANS (@lem7119970 y z) (@lem7120017 y z)). Qed.
Lemma lem7120021 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem7120022 (x : real) (y : real) (z : real) : (term49 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem7120021 x) (@lem7120018 y z)). Qed.
Lemma lem7120023 (x : real) (y : real) (z : real) : (term48 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7119969 x y z) (@lem7120022 x y z)). Qed.
Lemma lem7120024 (x : real) (y : real) (z : real) : (term47 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7119968 x y z) (@lem7120023 x y z)). Qed.
Lemma lem7120025 (y : real) (z : real) (x : real) : (term73 y z x) = (term73 y z x).
Proof. exact (eq_refl (term73 y z x)). Qed.
Lemma lem7120026 (x : real) (y : real) (z : real) : ((term72 y z x) = (term47 x y z)) = ((term72 y z x) = (term53 x y z)).
Proof. exact (MK_COMB (@lem7120025 y z x) (@lem7120024 x y z)). Qed.
Lemma lem7120027 (x : real) (y : real) (z : real) : (term72 y z x) = (term53 x y z).
Proof. exact (EQ_MP (@lem7120026 x y z) (@lem7119967 x y z)). Qed.
Lemma lem7120028 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7120029 (x : real) (y : real) (z : real) : (term74 y z x) = (term56 x y z).
Proof. exact (MK_COMB (@lem7120028) (@lem7120027 x y z)). Qed.
Lemma lem7120030 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120031 (x : real) (y : real) (z : real) : (term75 y z x) = (term58 x y z).
Proof. exact (MK_COMB (@lem7120029 x y z) (@lem7120030)). Qed.
Lemma lem7120032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7120033 (x : real) (y : real) (z : real) : (term76 y z x) = (term60 x y z).
Proof. exact (MK_COMB (@lem7120032) (@lem7119965 x y z)). Qed.
Lemma lem7120034 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120035 (x : real) (y : real) (z : real) : (term77 y z x) = (term62 x y z).
Proof. exact (MK_COMB (@lem7120033 x y z) (@lem7120034)). Qed.
Lemma lem7120036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7120037 (x : real) (y : real) (z : real) : (term78 y z x) = (term64 x y z).
Proof. exact (MK_COMB (@lem7120036) (@lem7120035 x y z)). Qed.
Lemma lem7120038 (x : real) (y : real) (z : real) : (term71 y z x) = (term65 x y z).
Proof. exact (MK_COMB (@lem7120037 x y z) (@lem7120031 x y z)). Qed.
Lemma lem7120039 (x : real) (y : real) (z : real) : (term70 y z x) = (term65 x y z).
Proof. exact (TRANS (@lem7119888 y z x) (@lem7120038 x y z)). Qed.
Lemma lem7120040 (x : real) (y : real) (z : real) : ((real_add x y) = z) = ((term44 x y z) = term3).
Proof. exact (@lem1988293 (real_add x y) z). Qed.
Lemma lem7120052 (x : real) (y : real) (z : real) : (term44 x y z) = (term45 x y z).
Proof. exact (@lem1982792 (real_add x y) z). Qed.
Lemma lem7120061 (x : real) (y : real) (z : real) : (term45 x y z) = (term39 x y z).
Proof. exact (@lem1982755 x y (term6 z)). Qed.
Lemma lem7120063 (x : real) (y : real) (z : real) : (term44 x y z) = (term39 x y z).
Proof. exact (TRANS (@lem7120052 x y z) (@lem7120061 x y z)). Qed.
Lemma lem7120064 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7120065 (x : real) (y : real) (z : real) : (term79 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem7120064) (@lem7120063 x y z)). Qed.
Lemma lem7120066 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120067 (x : real) (y : real) (z : real) : ((term44 x y z) = term3) = ((term39 x y z) = term3).
Proof. exact (MK_COMB (@lem7120065 x y z) (@lem7120066)). Qed.
Lemma lem7120068 (x : real) (y : real) (z : real) : ((real_add x y) = z) = ((term39 x y z) = term3).
Proof. exact (TRANS (@lem7120040 x y z) (@lem7120067 x y z)). Qed.
Lemma lem7120069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7120070 (x : real) (y : real) (z : real) : (term80 y z x) = (term81 x y z).
Proof. exact (MK_COMB (@lem7120069) (@lem7120039 x y z)). Qed.
Lemma lem7120071 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (MK_COMB (@lem7120070 x y z) (@lem7120068 x y z)). Qed.
Lemma lem7120072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7120073 (x : real) (y : real) (z : real) : (term84 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem7120072) (@lem7119887 x y z)). Qed.
Lemma lem7120074 (x : real) (y : real) (z : real) : (term1 x y z) = (term86 x y z).
Proof. exact (MK_COMB (@lem7120073 x y z) (@lem7120071 x y z)). Qed.
Lemma lem7120081 (x : real) (y : real) (z : real) : (term0 x y z) = (term86 x y z).
Proof. exact (TRANS (@lem7119703 x y z) (@lem7120074 x y z)). Qed.
Lemma lem7120098 (x : real) (y : real) (z : real) : (term83 x y z) = (term87 x y z).
Proof. exact (@lem19367 (term62 x y z) (term58 x y z) ((term39 x y z) = term3)). Qed.
Lemma lem7120115 (x : real) (y : real) (z : real) : (term69 x y z) = (term88 x y z).
Proof. exact (@lem19158 (term62 x y z) ((term39 x y z) = term3) (term58 x y z)). Qed.
Lemma lem7120116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7120117 (x : real) (y : real) (z : real) : (term85 x y z) = (term89 x y z).
Proof. exact (MK_COMB (@lem7120116) (@lem7120115 x y z)). Qed.
Lemma lem7120118 (x : real) (y : real) (z : real) : (term86 x y z) = (term90 x y z).
Proof. exact (MK_COMB (@lem7120117 x y z) (@lem7120098 x y z)). Qed.
Lemma lem7120119 (x : real) (y : real) (z : real) : (term0 x y z) = (term90 x y z).
Proof. exact (TRANS (@lem7120081 x y z) (@lem7120118 x y z)). Qed.
Lemma lem7120141 (x : real) (y : real) (z : real) (h1 : term90 x y z) : term90 x y z.
Proof. exact (h1). Qed.
Lemma lem7120142 (x : real) (y : real) (z : real) (h1 : term88 x y z) : term88 x y z.
Proof. exact (h1). Qed.
Lemma lem7120143 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term91 x y z.
Proof. exact (h1). Qed.
Lemma lem7120144 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term62 x y z.
Proof. exact (proj2 (@lem7120143 x y z h1)). Qed.
Lemma lem7120145 (x : real) (y : real) (z : real) (h1 : term91 x y z) : (term39 x y z) = term3.
Proof. exact (proj1 (@lem7120143 x y z h1)). Qed.
Lemma lem7120147 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7120148 : term92 = term93.
Proof. exact (@lem7120147 term3 term23). Qed.
Lemma lem7120150 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120151 : term23 = term33.
Proof. exact (@lem7120150 term17). Qed.
Lemma lem7120153 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120154 : term3 = term95.
Proof. exact (@lem7120153 (NUMERAL 0)). Qed.
Lemma lem7120155 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120156 : term96 = term97.
Proof. exact (MK_COMB (@lem7120155) (@lem7120154)). Qed.
Lemma lem7120157 : term93 = term98.
Proof. exact (MK_COMB (@lem7120156) (@lem7120151)). Qed.
Lemma lem7120158 : term99.
Proof. exact (@lem1980255 term3 term23 term23 term23). Qed.
Lemma lem7120160 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120161 : term93 = term101.
Proof. exact (@lem7120160 (NUMERAL 0) term17). Qed.
Lemma lem7120162 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120163 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120164 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120163 h1) (fun h1 : term101 = True => @lem7120162)). Qed.
Lemma lem7120165 : term101 = True.
Proof. exact (EQ_MP (@lem7120164) (@lem7120162)). Qed.
Lemma lem7120166 : term93 = True.
Proof. exact (TRANS (@lem7120161) (@lem7120165)). Qed.
Lemma lem7120167 : True = term93.
Proof. exact (SYM (@lem7120166)). Qed.
Lemma lem7120168 : term93.
Proof. exact (EQ_MP (@lem7120167) (@lem0)). Qed.
Lemma lem7120169 : term103.
Proof. exact (@lem7120158 (@lem7120168)). Qed.
Lemma lem7120171 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120172 : term93 = term101.
Proof. exact (@lem7120171 (NUMERAL 0) term17). Qed.
Lemma lem7120173 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120174 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120175 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120174 h1) (fun h1 : term101 = True => @lem7120173)). Qed.
Lemma lem7120176 : term101 = True.
Proof. exact (EQ_MP (@lem7120175) (@lem7120173)). Qed.
Lemma lem7120177 : term93 = True.
Proof. exact (TRANS (@lem7120172) (@lem7120176)). Qed.
Lemma lem7120178 : True = term93.
Proof. exact (SYM (@lem7120177)). Qed.
Lemma lem7120179 : term93.
Proof. exact (EQ_MP (@lem7120178) (@lem0)). Qed.
Lemma lem7120180 : term98 = term104.
Proof. exact (@lem7120169 (@lem7120179)). Qed.
Lemma lem7120182 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120183 : term26 = term27.
Proof. exact (@lem7120182 term17 term17). Qed.
Lemma lem7120184 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120185 : term29 = term17.
Proof. exact (EQ_MP (@lem7120184) (@lem940073)). Qed.
Lemma lem7120186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120187 : term27 = term23.
Proof. exact (MK_COMB (@lem7120186) (@lem7120185)). Qed.
Lemma lem7120188 : term26 = term23.
Proof. exact (TRANS (@lem7120183) (@lem7120187)). Qed.
Lemma lem7120190 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120191 : term106 = term3.
Proof. exact (@lem7120190 term17). Qed.
Lemma lem7120192 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120193 : term107 = term96.
Proof. exact (MK_COMB (@lem7120192) (@lem7120191)). Qed.
Lemma lem7120194 : term104 = term93.
Proof. exact (MK_COMB (@lem7120193) (@lem7120188)). Qed.
Lemma lem7120196 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120197 : term93 = term101.
Proof. exact (@lem7120196 (NUMERAL 0) term17). Qed.
Lemma lem7120198 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120199 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120200 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120199 h1) (fun h1 : term101 = True => @lem7120198)). Qed.
Lemma lem7120201 : term101 = True.
Proof. exact (EQ_MP (@lem7120200) (@lem7120198)). Qed.
Lemma lem7120202 : term93 = True.
Proof. exact (TRANS (@lem7120197) (@lem7120201)). Qed.
Lemma lem7120203 : term104 = True.
Proof. exact (TRANS (@lem7120194) (@lem7120202)). Qed.
Lemma lem7120204 : term98 = True.
Proof. exact (TRANS (@lem7120180) (@lem7120203)). Qed.
Lemma lem7120205 : term93 = True.
Proof. exact (TRANS (@lem7120157) (@lem7120204)). Qed.
Lemma lem7120206 : term92 = True.
Proof. exact (TRANS (@lem7120148) (@lem7120205)). Qed.
Lemma lem7120207 : True = term92.
Proof. exact (SYM (@lem7120206)). Qed.
Lemma lem7120208 : term92.
Proof. exact (EQ_MP (@lem7120207) (@lem0)). Qed.
Lemma lem7120209 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term108 x y z.
Proof. exact (conj (@lem7120208) (@lem7120144 x y z h1)). Qed.
Lemma lem7120211 (x : real) (y : real) : term109 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7120212 (x : real) (y : real) (z : real) : term110 x y z.
Proof. exact (@lem7120211 term23 (term39 x y z)). Qed.
Lemma lem7120213 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term111 x y z.
Proof. exact (@lem7120212 x y z (@lem7120209 x y z h1)). Qed.
Lemma lem7120214 (x : real) (y : real) (z : real) : (term112 x y z) = (term39 x y z).
Proof. exact (@lem1982733 (term39 x y z)). Qed.
Lemma lem7120215 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7120216 (x : real) (y : real) (z : real) : (term113 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem7120215) (@lem7120214 x y z)). Qed.
Lemma lem7120217 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120218 (x : real) (y : real) (z : real) : (term111 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem7120216 x y z) (@lem7120217)). Qed.
Lemma lem7120219 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term62 x y z.
Proof. exact (EQ_MP (@lem7120218 x y z) (@lem7120213 x y z h1)). Qed.
Lemma lem7120221 (y : real) : term114 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7120222 (x : real) (y : real) (z : real) : term115 x y z.
Proof. exact (@lem7120221 (term39 x y z)). Qed.
Lemma lem7120223 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term116 x y z.
Proof. exact (@lem7120222 x y z (@lem7120145 x y z h1)). Qed.
Lemma lem7120224 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term117 x y z.
Proof. exact (@lem7120223 x y z h1 term11). Qed.
Lemma lem7120225 (x : real) (y : real) (z : real) : (term117 x y z) = ((term48 x y z) = term3).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem7120226 (x : real) (y : real) (z : real) (h1 : term91 x y z) : (term48 x y z) = term3.
Proof. exact (EQ_MP (@lem7120225 x y z) (@lem7120224 x y z h1)). Qed.
Lemma lem7120227 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (@lem1982781 x term11 (term4 y z)). Qed.
Lemma lem7120228 (y : real) (z : real) : (term50 y z) = (term51 y z).
Proof. exact (@lem1982781 y term11 (term6 z)). Qed.
Lemma lem7120229 (z : real) : (term12 z) = (term13 z).
Proof. exact (@lem1982749 term11 term11 z). Qed.
Lemma lem7120231 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120232 : term11 = term16.
Proof. exact (@lem7120231 term17). Qed.
Lemma lem7120234 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120235 : term11 = term16.
Proof. exact (@lem7120234 term17). Qed.
Lemma lem7120236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120237 : term18 = term19.
Proof. exact (MK_COMB (@lem7120236) (@lem7120235)). Qed.
Lemma lem7120238 : term20 = term21.
Proof. exact (MK_COMB (@lem7120237) (@lem7120232)). Qed.
Lemma lem7120239 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7120241 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120242 : term26 = term27.
Proof. exact (@lem7120241 term17 term17). Qed.
Lemma lem7120243 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120244 : term29 = term17.
Proof. exact (EQ_MP (@lem7120243) (@lem940073)). Qed.
Lemma lem7120245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120246 : term27 = term23.
Proof. exact (MK_COMB (@lem7120245) (@lem7120244)). Qed.
Lemma lem7120247 : term26 = term23.
Proof. exact (TRANS (@lem7120242) (@lem7120246)). Qed.
Lemma lem7120249 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7120250 : term20 = term27.
Proof. exact (@lem7120249 term17 term17). Qed.
Lemma lem7120251 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120252 : term29 = term17.
Proof. exact (EQ_MP (@lem7120251) (@lem940073)). Qed.
Lemma lem7120253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120254 : term27 = term23.
Proof. exact (MK_COMB (@lem7120253) (@lem7120252)). Qed.
Lemma lem7120255 : term20 = term23.
Proof. exact (TRANS (@lem7120250) (@lem7120254)). Qed.
Lemma lem7120256 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7120257 : term31 = term32.
Proof. exact (MK_COMB (@lem7120256) (@lem7120255)). Qed.
Lemma lem7120258 : term22 = term33.
Proof. exact (MK_COMB (@lem7120257) (@lem7120247)). Qed.
Lemma lem7120259 : term21 = term33.
Proof. exact (TRANS (@lem7120239) (@lem7120258)). Qed.
Lemma lem7120260 : term20 = term33.
Proof. exact (TRANS (@lem7120238) (@lem7120259)). Qed.
Lemma lem7120262 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7120263 : term33 = term23.
Proof. exact (@lem7120262 term23). Qed.
Lemma lem7120264 : term20 = term23.
Proof. exact (TRANS (@lem7120260) (@lem7120263)). Qed.
Lemma lem7120265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120266 : term35 = term36.
Proof. exact (MK_COMB (@lem7120265) (@lem7120264)). Qed.
Lemma lem7120267 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7120268 (z : real) : (term13 z) = (term37 z).
Proof. exact (MK_COMB (@lem7120266) (@lem7120267 z)). Qed.
Lemma lem7120269 (z : real) : (term12 z) = (term37 z).
Proof. exact (TRANS (@lem7120229 z) (@lem7120268 z)). Qed.
Lemma lem7120270 (z : real) : (term37 z) = z.
Proof. exact (@lem1982709 z). Qed.
Lemma lem7120271 (z : real) : (term12 z) = z.
Proof. exact (TRANS (@lem7120269 z) (@lem7120270 z)). Qed.
Lemma lem7120274 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem7120275 (y : real) (z : real) : (term51 y z) = (term5 y z).
Proof. exact (MK_COMB (@lem7120274 y) (@lem7120271 z)). Qed.
Lemma lem7120276 (y : real) (z : real) : (term50 y z) = (term5 y z).
Proof. exact (TRANS (@lem7120228 y z) (@lem7120275 y z)). Qed.
Lemma lem7120279 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem7120280 (x : real) (y : real) (z : real) : (term49 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem7120279 x) (@lem7120276 y z)). Qed.
Lemma lem7120281 (x : real) (y : real) (z : real) : (term48 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7120227 x y z) (@lem7120280 x y z)). Qed.
Lemma lem7120282 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7120283 (x : real) (y : real) (z : real) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem7120282) (@lem7120281 x y z)). Qed.
Lemma lem7120284 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120285 (x : real) (y : real) (z : real) : ((term48 x y z) = term3) = ((term53 x y z) = term3).
Proof. exact (MK_COMB (@lem7120283 x y z) (@lem7120284)). Qed.
Lemma lem7120286 (x : real) (y : real) (z : real) (h1 : term91 x y z) : (term53 x y z) = term3.
Proof. exact (EQ_MP (@lem7120285 x y z) (@lem7120226 x y z h1)). Qed.
Lemma lem7120287 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term120 x y z.
Proof. exact (conj (@lem7120286 x y z h1) (@lem7120219 x y z h1)). Qed.
Lemma lem7120289 (x : real) (y : real) : term121 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7120290 (x : real) (y : real) (z : real) : term122 x y z.
Proof. exact (@lem7120289 (term53 x y z) (term39 x y z)). Qed.
Lemma lem7120291 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term123 x y z.
Proof. exact (@lem7120290 x y z (@lem7120287 x y z h1)). Qed.
Lemma lem7120292 (x : real) (y : real) (z : real) : (term124 x y z) = (term125 x y z).
Proof. exact (@lem1982753 (term6 x) x (term5 y z) (term4 y z)). Qed.
Lemma lem7120293 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1982713 term11 x). Qed.
Lemma lem7120295 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120296 : term23 = term33.
Proof. exact (@lem7120295 term17). Qed.
Lemma lem7120298 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120299 : term11 = term16.
Proof. exact (@lem7120298 term17). Qed.
Lemma lem7120300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120301 : term128 = term129.
Proof. exact (MK_COMB (@lem7120300) (@lem7120299)). Qed.
Lemma lem7120302 : term130 = term131.
Proof. exact (MK_COMB (@lem7120301) (@lem7120296)). Qed.
Lemma lem7120303 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7120305 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120306 : term93 = term101.
Proof. exact (@lem7120305 (NUMERAL 0) term17). Qed.
Lemma lem7120307 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120308 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120309 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120308 h1) (fun h1 : term101 = True => @lem7120307)). Qed.
Lemma lem7120310 : term101 = True.
Proof. exact (EQ_MP (@lem7120309) (@lem7120307)). Qed.
Lemma lem7120311 : term93 = True.
Proof. exact (TRANS (@lem7120306) (@lem7120310)). Qed.
Lemma lem7120312 : True = term93.
Proof. exact (SYM (@lem7120311)). Qed.
Lemma lem7120313 : term93.
Proof. exact (EQ_MP (@lem7120312) (@lem0)). Qed.
Lemma lem7120314 : term133.
Proof. exact (@lem7120303 (@lem7120313)). Qed.
Lemma lem7120316 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120317 : term93 = term101.
Proof. exact (@lem7120316 (NUMERAL 0) term17). Qed.
Lemma lem7120318 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120319 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120320 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120319 h1) (fun h1 : term101 = True => @lem7120318)). Qed.
Lemma lem7120321 : term101 = True.
Proof. exact (EQ_MP (@lem7120320) (@lem7120318)). Qed.
Lemma lem7120322 : term93 = True.
Proof. exact (TRANS (@lem7120317) (@lem7120321)). Qed.
Lemma lem7120323 : True = term93.
Proof. exact (SYM (@lem7120322)). Qed.
Lemma lem7120324 : term93.
Proof. exact (EQ_MP (@lem7120323) (@lem0)). Qed.
Lemma lem7120325 : term134.
Proof. exact (@lem7120314 (@lem7120324)). Qed.
Lemma lem7120327 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120328 : term93 = term101.
Proof. exact (@lem7120327 (NUMERAL 0) term17). Qed.
Lemma lem7120329 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120330 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120331 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120330 h1) (fun h1 : term101 = True => @lem7120329)). Qed.
Lemma lem7120332 : term101 = True.
Proof. exact (EQ_MP (@lem7120331) (@lem7120329)). Qed.
Lemma lem7120333 : term93 = True.
Proof. exact (TRANS (@lem7120328) (@lem7120332)). Qed.
Lemma lem7120334 : True = term93.
Proof. exact (SYM (@lem7120333)). Qed.
Lemma lem7120335 : term93.
Proof. exact (EQ_MP (@lem7120334) (@lem0)). Qed.
Lemma lem7120336 : term135.
Proof. exact (@lem7120325 (@lem7120335)). Qed.
Lemma lem7120338 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120339 : term26 = term27.
Proof. exact (@lem7120338 term17 term17). Qed.
Lemma lem7120340 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120341 : term29 = term17.
Proof. exact (EQ_MP (@lem7120340) (@lem940073)). Qed.
Lemma lem7120342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120343 : term27 = term23.
Proof. exact (MK_COMB (@lem7120342) (@lem7120341)). Qed.
Lemma lem7120344 : term26 = term23.
Proof. exact (TRANS (@lem7120339) (@lem7120343)). Qed.
Lemma lem7120346 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7120347 : term138 = term139.
Proof. exact (@lem7120346 term17 term17). Qed.
Lemma lem7120348 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120349 : term29 = term17.
Proof. exact (EQ_MP (@lem7120348) (@lem940073)). Qed.
Lemma lem7120350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120351 : term27 = term23.
Proof. exact (MK_COMB (@lem7120350) (@lem7120349)). Qed.
Lemma lem7120352 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7120353 : term139 = term11.
Proof. exact (MK_COMB (@lem7120352) (@lem7120351)). Qed.
Lemma lem7120354 : term138 = term11.
Proof. exact (TRANS (@lem7120347) (@lem7120353)). Qed.
Lemma lem7120355 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120356 : term140 = term128.
Proof. exact (MK_COMB (@lem7120355) (@lem7120354)). Qed.
Lemma lem7120357 : term141 = term130.
Proof. exact (MK_COMB (@lem7120356) (@lem7120344)). Qed.
Lemma lem7120359 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7120360 : term130 = term3.
Proof. exact (@lem7120359 term17). Qed.
Lemma lem7120361 : term141 = term3.
Proof. exact (TRANS (@lem7120357) (@lem7120360)). Qed.
Lemma lem7120362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120363 : term143 = term144.
Proof. exact (MK_COMB (@lem7120362) (@lem7120361)). Qed.
Lemma lem7120364 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7120365 : term145 = term106.
Proof. exact (MK_COMB (@lem7120363) (@lem7120364)). Qed.
Lemma lem7120367 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120368 : term106 = term3.
Proof. exact (@lem7120367 term17). Qed.
Lemma lem7120369 : term145 = term3.
Proof. exact (TRANS (@lem7120365) (@lem7120368)). Qed.
Lemma lem7120371 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120372 : term26 = term27.
Proof. exact (@lem7120371 term17 term17). Qed.
Lemma lem7120373 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120374 : term29 = term17.
Proof. exact (EQ_MP (@lem7120373) (@lem940073)). Qed.
Lemma lem7120375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120376 : term27 = term23.
Proof. exact (MK_COMB (@lem7120375) (@lem7120374)). Qed.
Lemma lem7120377 : term26 = term23.
Proof. exact (TRANS (@lem7120372) (@lem7120376)). Qed.
Lemma lem7120378 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7120379 : term146 = term106.
Proof. exact (MK_COMB (@lem7120378) (@lem7120377)). Qed.
Lemma lem7120381 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120382 : term106 = term3.
Proof. exact (@lem7120381 term17). Qed.
Lemma lem7120383 : term146 = term3.
Proof. exact (TRANS (@lem7120379) (@lem7120382)). Qed.
Lemma lem7120384 : term3 = term146.
Proof. exact (SYM (@lem7120383)). Qed.
Lemma lem7120385 : term145 = term146.
Proof. exact (TRANS (@lem7120369) (@lem7120384)). Qed.
Lemma lem7120386 : term131 = term95.
Proof. exact (@lem7120336 (@lem7120385)). Qed.
Lemma lem7120387 : term130 = term95.
Proof. exact (TRANS (@lem7120302) (@lem7120386)). Qed.
Lemma lem7120389 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7120390 : term95 = term3.
Proof. exact (@lem7120389 term3). Qed.
Lemma lem7120391 : term130 = term3.
Proof. exact (TRANS (@lem7120387) (@lem7120390)). Qed.
Lemma lem7120392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120393 : term147 = term144.
Proof. exact (MK_COMB (@lem7120392) (@lem7120391)). Qed.
Lemma lem7120394 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7120395 (x : real) : (term127 x) = (term148 x).
Proof. exact (MK_COMB (@lem7120393) (@lem7120394 x)). Qed.
Lemma lem7120396 (x : real) : (term126 x) = (term148 x).
Proof. exact (TRANS (@lem7120293 x) (@lem7120395 x)). Qed.
Lemma lem7120397 (x : real) : (term148 x) = term3.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7120398 (x : real) : (term126 x) = term3.
Proof. exact (TRANS (@lem7120396 x) (@lem7120397 x)). Qed.
Lemma lem7120399 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120400 (x : real) : (term149 x) = term150.
Proof. exact (MK_COMB (@lem7120399) (@lem7120398 x)). Qed.
Lemma lem7120401 (y : real) (z : real) : (term151 y z) = (term152 y z).
Proof. exact (@lem1982753 (term6 y) y z (term6 z)). Qed.
Lemma lem7120402 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1982713 term11 y). Qed.
Lemma lem7120404 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120405 : term23 = term33.
Proof. exact (@lem7120404 term17). Qed.
Lemma lem7120407 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120408 : term11 = term16.
Proof. exact (@lem7120407 term17). Qed.
Lemma lem7120409 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120410 : term128 = term129.
Proof. exact (MK_COMB (@lem7120409) (@lem7120408)). Qed.
Lemma lem7120411 : term130 = term131.
Proof. exact (MK_COMB (@lem7120410) (@lem7120405)). Qed.
Lemma lem7120412 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7120414 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120415 : term93 = term101.
Proof. exact (@lem7120414 (NUMERAL 0) term17). Qed.
Lemma lem7120416 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120417 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120418 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120417 h1) (fun h1 : term101 = True => @lem7120416)). Qed.
Lemma lem7120419 : term101 = True.
Proof. exact (EQ_MP (@lem7120418) (@lem7120416)). Qed.
Lemma lem7120420 : term93 = True.
Proof. exact (TRANS (@lem7120415) (@lem7120419)). Qed.
Lemma lem7120421 : True = term93.
Proof. exact (SYM (@lem7120420)). Qed.
Lemma lem7120422 : term93.
Proof. exact (EQ_MP (@lem7120421) (@lem0)). Qed.
Lemma lem7120423 : term133.
Proof. exact (@lem7120412 (@lem7120422)). Qed.
Lemma lem7120425 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120426 : term93 = term101.
Proof. exact (@lem7120425 (NUMERAL 0) term17). Qed.
Lemma lem7120427 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120428 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120429 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120428 h1) (fun h1 : term101 = True => @lem7120427)). Qed.
Lemma lem7120430 : term101 = True.
Proof. exact (EQ_MP (@lem7120429) (@lem7120427)). Qed.
Lemma lem7120431 : term93 = True.
Proof. exact (TRANS (@lem7120426) (@lem7120430)). Qed.
Lemma lem7120432 : True = term93.
Proof. exact (SYM (@lem7120431)). Qed.
Lemma lem7120433 : term93.
Proof. exact (EQ_MP (@lem7120432) (@lem0)). Qed.
Lemma lem7120434 : term134.
Proof. exact (@lem7120423 (@lem7120433)). Qed.
Lemma lem7120436 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120437 : term93 = term101.
Proof. exact (@lem7120436 (NUMERAL 0) term17). Qed.
Lemma lem7120438 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120439 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120440 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120439 h1) (fun h1 : term101 = True => @lem7120438)). Qed.
Lemma lem7120441 : term101 = True.
Proof. exact (EQ_MP (@lem7120440) (@lem7120438)). Qed.
Lemma lem7120442 : term93 = True.
Proof. exact (TRANS (@lem7120437) (@lem7120441)). Qed.
Lemma lem7120443 : True = term93.
Proof. exact (SYM (@lem7120442)). Qed.
Lemma lem7120444 : term93.
Proof. exact (EQ_MP (@lem7120443) (@lem0)). Qed.
Lemma lem7120445 : term135.
Proof. exact (@lem7120434 (@lem7120444)). Qed.
Lemma lem7120447 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120448 : term26 = term27.
Proof. exact (@lem7120447 term17 term17). Qed.
Lemma lem7120449 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120450 : term29 = term17.
Proof. exact (EQ_MP (@lem7120449) (@lem940073)). Qed.
Lemma lem7120451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120452 : term27 = term23.
Proof. exact (MK_COMB (@lem7120451) (@lem7120450)). Qed.
Lemma lem7120453 : term26 = term23.
Proof. exact (TRANS (@lem7120448) (@lem7120452)). Qed.
Lemma lem7120455 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7120456 : term138 = term139.
Proof. exact (@lem7120455 term17 term17). Qed.
Lemma lem7120457 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120458 : term29 = term17.
Proof. exact (EQ_MP (@lem7120457) (@lem940073)). Qed.
Lemma lem7120459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120460 : term27 = term23.
Proof. exact (MK_COMB (@lem7120459) (@lem7120458)). Qed.
Lemma lem7120461 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7120462 : term139 = term11.
Proof. exact (MK_COMB (@lem7120461) (@lem7120460)). Qed.
Lemma lem7120463 : term138 = term11.
Proof. exact (TRANS (@lem7120456) (@lem7120462)). Qed.
Lemma lem7120464 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120465 : term140 = term128.
Proof. exact (MK_COMB (@lem7120464) (@lem7120463)). Qed.
Lemma lem7120466 : term141 = term130.
Proof. exact (MK_COMB (@lem7120465) (@lem7120453)). Qed.
Lemma lem7120468 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7120469 : term130 = term3.
Proof. exact (@lem7120468 term17). Qed.
Lemma lem7120470 : term141 = term3.
Proof. exact (TRANS (@lem7120466) (@lem7120469)). Qed.
Lemma lem7120471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120472 : term143 = term144.
Proof. exact (MK_COMB (@lem7120471) (@lem7120470)). Qed.
Lemma lem7120473 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7120474 : term145 = term106.
Proof. exact (MK_COMB (@lem7120472) (@lem7120473)). Qed.
Lemma lem7120476 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120477 : term106 = term3.
Proof. exact (@lem7120476 term17). Qed.
Lemma lem7120478 : term145 = term3.
Proof. exact (TRANS (@lem7120474) (@lem7120477)). Qed.
Lemma lem7120480 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120481 : term26 = term27.
Proof. exact (@lem7120480 term17 term17). Qed.
Lemma lem7120482 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120483 : term29 = term17.
Proof. exact (EQ_MP (@lem7120482) (@lem940073)). Qed.
Lemma lem7120484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120485 : term27 = term23.
Proof. exact (MK_COMB (@lem7120484) (@lem7120483)). Qed.
Lemma lem7120486 : term26 = term23.
Proof. exact (TRANS (@lem7120481) (@lem7120485)). Qed.
Lemma lem7120487 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7120488 : term146 = term106.
Proof. exact (MK_COMB (@lem7120487) (@lem7120486)). Qed.
Lemma lem7120490 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120491 : term106 = term3.
Proof. exact (@lem7120490 term17). Qed.
Lemma lem7120492 : term146 = term3.
Proof. exact (TRANS (@lem7120488) (@lem7120491)). Qed.
Lemma lem7120493 : term3 = term146.
Proof. exact (SYM (@lem7120492)). Qed.
Lemma lem7120494 : term145 = term146.
Proof. exact (TRANS (@lem7120478) (@lem7120493)). Qed.
Lemma lem7120495 : term131 = term95.
Proof. exact (@lem7120445 (@lem7120494)). Qed.
Lemma lem7120496 : term130 = term95.
Proof. exact (TRANS (@lem7120411) (@lem7120495)). Qed.
Lemma lem7120498 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7120499 : term95 = term3.
Proof. exact (@lem7120498 term3). Qed.
Lemma lem7120500 : term130 = term3.
Proof. exact (TRANS (@lem7120496) (@lem7120499)). Qed.
Lemma lem7120501 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120502 : term147 = term144.
Proof. exact (MK_COMB (@lem7120501) (@lem7120500)). Qed.
Lemma lem7120503 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7120504 (y : real) : (term127 y) = (term148 y).
Proof. exact (MK_COMB (@lem7120502) (@lem7120503 y)). Qed.
Lemma lem7120505 (y : real) : (term126 y) = (term148 y).
Proof. exact (TRANS (@lem7120402 y) (@lem7120504 y)). Qed.
Lemma lem7120506 (y : real) : (term148 y) = term3.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7120507 (y : real) : (term126 y) = term3.
Proof. exact (TRANS (@lem7120505 y) (@lem7120506 y)). Qed.
Lemma lem7120508 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120509 (y : real) : (term149 y) = term150.
Proof. exact (MK_COMB (@lem7120508) (@lem7120507 y)). Qed.
Lemma lem7120510 (z : real) : (term153 z) = (term127 z).
Proof. exact (@lem1982715 term11 z). Qed.
Lemma lem7120512 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120513 : term23 = term33.
Proof. exact (@lem7120512 term17). Qed.
Lemma lem7120515 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120516 : term11 = term16.
Proof. exact (@lem7120515 term17). Qed.
Lemma lem7120517 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120518 : term128 = term129.
Proof. exact (MK_COMB (@lem7120517) (@lem7120516)). Qed.
Lemma lem7120519 : term130 = term131.
Proof. exact (MK_COMB (@lem7120518) (@lem7120513)). Qed.
Lemma lem7120520 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7120522 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120523 : term93 = term101.
Proof. exact (@lem7120522 (NUMERAL 0) term17). Qed.
Lemma lem7120524 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120525 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120526 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120525 h1) (fun h1 : term101 = True => @lem7120524)). Qed.
Lemma lem7120527 : term101 = True.
Proof. exact (EQ_MP (@lem7120526) (@lem7120524)). Qed.
Lemma lem7120528 : term93 = True.
Proof. exact (TRANS (@lem7120523) (@lem7120527)). Qed.
Lemma lem7120529 : True = term93.
Proof. exact (SYM (@lem7120528)). Qed.
Lemma lem7120530 : term93.
Proof. exact (EQ_MP (@lem7120529) (@lem0)). Qed.
Lemma lem7120531 : term133.
Proof. exact (@lem7120520 (@lem7120530)). Qed.
Lemma lem7120533 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120534 : term93 = term101.
Proof. exact (@lem7120533 (NUMERAL 0) term17). Qed.
Lemma lem7120535 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120536 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120537 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120536 h1) (fun h1 : term101 = True => @lem7120535)). Qed.
Lemma lem7120538 : term101 = True.
Proof. exact (EQ_MP (@lem7120537) (@lem7120535)). Qed.
Lemma lem7120539 : term93 = True.
Proof. exact (TRANS (@lem7120534) (@lem7120538)). Qed.
Lemma lem7120540 : True = term93.
Proof. exact (SYM (@lem7120539)). Qed.
Lemma lem7120541 : term93.
Proof. exact (EQ_MP (@lem7120540) (@lem0)). Qed.
Lemma lem7120542 : term134.
Proof. exact (@lem7120531 (@lem7120541)). Qed.
Lemma lem7120544 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120545 : term93 = term101.
Proof. exact (@lem7120544 (NUMERAL 0) term17). Qed.
Lemma lem7120546 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120547 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120548 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120547 h1) (fun h1 : term101 = True => @lem7120546)). Qed.
Lemma lem7120549 : term101 = True.
Proof. exact (EQ_MP (@lem7120548) (@lem7120546)). Qed.
Lemma lem7120550 : term93 = True.
Proof. exact (TRANS (@lem7120545) (@lem7120549)). Qed.
Lemma lem7120551 : True = term93.
Proof. exact (SYM (@lem7120550)). Qed.
Lemma lem7120552 : term93.
Proof. exact (EQ_MP (@lem7120551) (@lem0)). Qed.
Lemma lem7120553 : term135.
Proof. exact (@lem7120542 (@lem7120552)). Qed.
Lemma lem7120555 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120556 : term26 = term27.
Proof. exact (@lem7120555 term17 term17). Qed.
Lemma lem7120557 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120558 : term29 = term17.
Proof. exact (EQ_MP (@lem7120557) (@lem940073)). Qed.
Lemma lem7120559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120560 : term27 = term23.
Proof. exact (MK_COMB (@lem7120559) (@lem7120558)). Qed.
Lemma lem7120561 : term26 = term23.
Proof. exact (TRANS (@lem7120556) (@lem7120560)). Qed.
Lemma lem7120563 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7120564 : term138 = term139.
Proof. exact (@lem7120563 term17 term17). Qed.
Lemma lem7120565 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120566 : term29 = term17.
Proof. exact (EQ_MP (@lem7120565) (@lem940073)). Qed.
Lemma lem7120567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120568 : term27 = term23.
Proof. exact (MK_COMB (@lem7120567) (@lem7120566)). Qed.
Lemma lem7120569 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7120570 : term139 = term11.
Proof. exact (MK_COMB (@lem7120569) (@lem7120568)). Qed.
Lemma lem7120571 : term138 = term11.
Proof. exact (TRANS (@lem7120564) (@lem7120570)). Qed.
Lemma lem7120572 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120573 : term140 = term128.
Proof. exact (MK_COMB (@lem7120572) (@lem7120571)). Qed.
Lemma lem7120574 : term141 = term130.
Proof. exact (MK_COMB (@lem7120573) (@lem7120561)). Qed.
Lemma lem7120576 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7120577 : term130 = term3.
Proof. exact (@lem7120576 term17). Qed.
Lemma lem7120578 : term141 = term3.
Proof. exact (TRANS (@lem7120574) (@lem7120577)). Qed.
Lemma lem7120579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120580 : term143 = term144.
Proof. exact (MK_COMB (@lem7120579) (@lem7120578)). Qed.
Lemma lem7120581 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7120582 : term145 = term106.
Proof. exact (MK_COMB (@lem7120580) (@lem7120581)). Qed.
Lemma lem7120584 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120585 : term106 = term3.
Proof. exact (@lem7120584 term17). Qed.
Lemma lem7120586 : term145 = term3.
Proof. exact (TRANS (@lem7120582) (@lem7120585)). Qed.
Lemma lem7120588 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120589 : term26 = term27.
Proof. exact (@lem7120588 term17 term17). Qed.
Lemma lem7120590 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120591 : term29 = term17.
Proof. exact (EQ_MP (@lem7120590) (@lem940073)). Qed.
Lemma lem7120592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120593 : term27 = term23.
Proof. exact (MK_COMB (@lem7120592) (@lem7120591)). Qed.
Lemma lem7120594 : term26 = term23.
Proof. exact (TRANS (@lem7120589) (@lem7120593)). Qed.
Lemma lem7120595 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7120596 : term146 = term106.
Proof. exact (MK_COMB (@lem7120595) (@lem7120594)). Qed.
Lemma lem7120598 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120599 : term106 = term3.
Proof. exact (@lem7120598 term17). Qed.
Lemma lem7120600 : term146 = term3.
Proof. exact (TRANS (@lem7120596) (@lem7120599)). Qed.
Lemma lem7120601 : term3 = term146.
Proof. exact (SYM (@lem7120600)). Qed.
Lemma lem7120602 : term145 = term146.
Proof. exact (TRANS (@lem7120586) (@lem7120601)). Qed.
Lemma lem7120603 : term131 = term95.
Proof. exact (@lem7120553 (@lem7120602)). Qed.
Lemma lem7120604 : term130 = term95.
Proof. exact (TRANS (@lem7120519) (@lem7120603)). Qed.
Lemma lem7120606 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7120607 : term95 = term3.
Proof. exact (@lem7120606 term3). Qed.
Lemma lem7120608 : term130 = term3.
Proof. exact (TRANS (@lem7120604) (@lem7120607)). Qed.
Lemma lem7120609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120610 : term147 = term144.
Proof. exact (MK_COMB (@lem7120609) (@lem7120608)). Qed.
Lemma lem7120611 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7120612 (z : real) : (term127 z) = (term148 z).
Proof. exact (MK_COMB (@lem7120610) (@lem7120611 z)). Qed.
Lemma lem7120613 (z : real) : (term153 z) = (term148 z).
Proof. exact (TRANS (@lem7120510 z) (@lem7120612 z)). Qed.
Lemma lem7120614 (z : real) : (term148 z) = term3.
Proof. exact (@lem1982719 z). Qed.
Lemma lem7120615 (z : real) : (term153 z) = term3.
Proof. exact (TRANS (@lem7120613 z) (@lem7120614 z)). Qed.
Lemma lem7120616 (y : real) (z : real) : (term152 y z) = term154.
Proof. exact (MK_COMB (@lem7120509 y) (@lem7120615 z)). Qed.
Lemma lem7120617 (y : real) (z : real) : (term151 y z) = term154.
Proof. exact (TRANS (@lem7120401 y z) (@lem7120616 y z)). Qed.
Lemma lem7120618 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7120619 (y : real) (z : real) : (term151 y z) = term3.
Proof. exact (TRANS (@lem7120617 y z) (@lem7120618)). Qed.
Lemma lem7120620 (x : real) (y : real) (z : real) : (term125 x y z) = term154.
Proof. exact (MK_COMB (@lem7120400 x) (@lem7120619 y z)). Qed.
Lemma lem7120621 (x : real) (y : real) (z : real) : (term124 x y z) = term154.
Proof. exact (TRANS (@lem7120292 x y z) (@lem7120620 x y z)). Qed.
Lemma lem7120622 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7120623 (x : real) (y : real) (z : real) : (term124 x y z) = term3.
Proof. exact (TRANS (@lem7120621 x y z) (@lem7120622)). Qed.
Lemma lem7120624 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7120625 (x : real) (y : real) (z : real) : (term155 x y z) = term156.
Proof. exact (MK_COMB (@lem7120624) (@lem7120623 x y z)). Qed.
Lemma lem7120626 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120627 (x : real) (y : real) (z : real) : (term123 x y z) = term157.
Proof. exact (MK_COMB (@lem7120625 x y z) (@lem7120626)). Qed.
Lemma lem7120628 (x : real) (y : real) (z : real) (h1 : term91 x y z) : term157.
Proof. exact (EQ_MP (@lem7120627 x y z) (@lem7120291 x y z h1)). Qed.
Lemma lem7120630 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7120631 : term157 = term158.
Proof. exact (@lem7120630 term3 term3). Qed.
Lemma lem7120633 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120634 : term3 = term95.
Proof. exact (@lem7120633 (NUMERAL 0)). Qed.
Lemma lem7120636 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120637 : term3 = term95.
Proof. exact (@lem7120636 (NUMERAL 0)). Qed.
Lemma lem7120638 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120639 : term96 = term97.
Proof. exact (MK_COMB (@lem7120638) (@lem7120637)). Qed.
Lemma lem7120640 : term158 = term159.
Proof. exact (MK_COMB (@lem7120639) (@lem7120634)). Qed.
Lemma lem7120641 : term160.
Proof. exact (@lem1980255 term3 term23 term3 term23). Qed.
Lemma lem7120643 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120644 : term93 = term101.
Proof. exact (@lem7120643 (NUMERAL 0) term17). Qed.
Lemma lem7120645 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120646 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120647 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120646 h1) (fun h1 : term101 = True => @lem7120645)). Qed.
Lemma lem7120648 : term101 = True.
Proof. exact (EQ_MP (@lem7120647) (@lem7120645)). Qed.
Lemma lem7120649 : term93 = True.
Proof. exact (TRANS (@lem7120644) (@lem7120648)). Qed.
Lemma lem7120650 : True = term93.
Proof. exact (SYM (@lem7120649)). Qed.
Lemma lem7120651 : term93.
Proof. exact (EQ_MP (@lem7120650) (@lem0)). Qed.
Lemma lem7120652 : term161.
Proof. exact (@lem7120641 (@lem7120651)). Qed.
Lemma lem7120654 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120655 : term93 = term101.
Proof. exact (@lem7120654 (NUMERAL 0) term17). Qed.
Lemma lem7120656 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120657 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120658 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120657 h1) (fun h1 : term101 = True => @lem7120656)). Qed.
Lemma lem7120659 : term101 = True.
Proof. exact (EQ_MP (@lem7120658) (@lem7120656)). Qed.
Lemma lem7120660 : term93 = True.
Proof. exact (TRANS (@lem7120655) (@lem7120659)). Qed.
Lemma lem7120661 : True = term93.
Proof. exact (SYM (@lem7120660)). Qed.
Lemma lem7120662 : term93.
Proof. exact (EQ_MP (@lem7120661) (@lem0)). Qed.
Lemma lem7120663 : term159 = term162.
Proof. exact (@lem7120652 (@lem7120662)). Qed.
Lemma lem7120665 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120666 : term106 = term3.
Proof. exact (@lem7120665 term17). Qed.
Lemma lem7120668 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120669 : term106 = term3.
Proof. exact (@lem7120668 term17). Qed.
Lemma lem7120670 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120671 : term107 = term96.
Proof. exact (MK_COMB (@lem7120670) (@lem7120669)). Qed.
Lemma lem7120672 : term162 = term158.
Proof. exact (MK_COMB (@lem7120671) (@lem7120666)). Qed.
Lemma lem7120674 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120675 : term158 = term163.
Proof. exact (@lem7120674 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7120676 : term163 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7120677 : term158 = False.
Proof. exact (TRANS (@lem7120675) (@lem7120676)). Qed.
Lemma lem7120678 : term162 = False.
Proof. exact (TRANS (@lem7120672) (@lem7120677)). Qed.
Lemma lem7120679 : term159 = False.
Proof. exact (TRANS (@lem7120663) (@lem7120678)). Qed.
Lemma lem7120680 : term158 = False.
Proof. exact (TRANS (@lem7120640) (@lem7120679)). Qed.
Lemma lem7120681 : term157 = False.
Proof. exact (TRANS (@lem7120631) (@lem7120680)). Qed.
Lemma lem7120682 (x : real) (y : real) (z : real) (h1 : term91 x y z) : False.
Proof. exact (EQ_MP (@lem7120681) (@lem7120628 x y z h1)). Qed.
Lemma lem7120683 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term164 x y z.
Proof. exact (h1). Qed.
Lemma lem7120684 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term58 x y z.
Proof. exact (proj2 (@lem7120683 x y z h1)). Qed.
Lemma lem7120685 (x : real) (y : real) (z : real) (h1 : term164 x y z) : (term39 x y z) = term3.
Proof. exact (proj1 (@lem7120683 x y z h1)). Qed.
Lemma lem7120687 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7120688 : term92 = term93.
Proof. exact (@lem7120687 term3 term23). Qed.
Lemma lem7120690 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120691 : term23 = term33.
Proof. exact (@lem7120690 term17). Qed.
Lemma lem7120693 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120694 : term3 = term95.
Proof. exact (@lem7120693 (NUMERAL 0)). Qed.
Lemma lem7120695 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120696 : term96 = term97.
Proof. exact (MK_COMB (@lem7120695) (@lem7120694)). Qed.
Lemma lem7120697 : term93 = term98.
Proof. exact (MK_COMB (@lem7120696) (@lem7120691)). Qed.
Lemma lem7120698 : term99.
Proof. exact (@lem1980255 term3 term23 term23 term23). Qed.
Lemma lem7120700 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120701 : term93 = term101.
Proof. exact (@lem7120700 (NUMERAL 0) term17). Qed.
Lemma lem7120702 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120703 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120704 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120703 h1) (fun h1 : term101 = True => @lem7120702)). Qed.
Lemma lem7120705 : term101 = True.
Proof. exact (EQ_MP (@lem7120704) (@lem7120702)). Qed.
Lemma lem7120706 : term93 = True.
Proof. exact (TRANS (@lem7120701) (@lem7120705)). Qed.
Lemma lem7120707 : True = term93.
Proof. exact (SYM (@lem7120706)). Qed.
Lemma lem7120708 : term93.
Proof. exact (EQ_MP (@lem7120707) (@lem0)). Qed.
Lemma lem7120709 : term103.
Proof. exact (@lem7120698 (@lem7120708)). Qed.
Lemma lem7120711 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120712 : term93 = term101.
Proof. exact (@lem7120711 (NUMERAL 0) term17). Qed.
Lemma lem7120713 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120714 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120715 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120714 h1) (fun h1 : term101 = True => @lem7120713)). Qed.
Lemma lem7120716 : term101 = True.
Proof. exact (EQ_MP (@lem7120715) (@lem7120713)). Qed.
Lemma lem7120717 : term93 = True.
Proof. exact (TRANS (@lem7120712) (@lem7120716)). Qed.
Lemma lem7120718 : True = term93.
Proof. exact (SYM (@lem7120717)). Qed.
Lemma lem7120719 : term93.
Proof. exact (EQ_MP (@lem7120718) (@lem0)). Qed.
Lemma lem7120720 : term98 = term104.
Proof. exact (@lem7120709 (@lem7120719)). Qed.
Lemma lem7120722 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120723 : term26 = term27.
Proof. exact (@lem7120722 term17 term17). Qed.
Lemma lem7120724 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120725 : term29 = term17.
Proof. exact (EQ_MP (@lem7120724) (@lem940073)). Qed.
Lemma lem7120726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120727 : term27 = term23.
Proof. exact (MK_COMB (@lem7120726) (@lem7120725)). Qed.
Lemma lem7120728 : term26 = term23.
Proof. exact (TRANS (@lem7120723) (@lem7120727)). Qed.
Lemma lem7120730 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120731 : term106 = term3.
Proof. exact (@lem7120730 term17). Qed.
Lemma lem7120732 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7120733 : term107 = term96.
Proof. exact (MK_COMB (@lem7120732) (@lem7120731)). Qed.
Lemma lem7120734 : term104 = term93.
Proof. exact (MK_COMB (@lem7120733) (@lem7120728)). Qed.
Lemma lem7120736 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120737 : term93 = term101.
Proof. exact (@lem7120736 (NUMERAL 0) term17). Qed.
Lemma lem7120738 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120739 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120740 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120739 h1) (fun h1 : term101 = True => @lem7120738)). Qed.
Lemma lem7120741 : term101 = True.
Proof. exact (EQ_MP (@lem7120740) (@lem7120738)). Qed.
Lemma lem7120742 : term93 = True.
Proof. exact (TRANS (@lem7120737) (@lem7120741)). Qed.
Lemma lem7120743 : term104 = True.
Proof. exact (TRANS (@lem7120734) (@lem7120742)). Qed.
Lemma lem7120744 : term98 = True.
Proof. exact (TRANS (@lem7120720) (@lem7120743)). Qed.
Lemma lem7120745 : term93 = True.
Proof. exact (TRANS (@lem7120697) (@lem7120744)). Qed.
Lemma lem7120746 : term92 = True.
Proof. exact (TRANS (@lem7120688) (@lem7120745)). Qed.
Lemma lem7120747 : True = term92.
Proof. exact (SYM (@lem7120746)). Qed.
Lemma lem7120748 : term92.
Proof. exact (EQ_MP (@lem7120747) (@lem0)). Qed.
Lemma lem7120749 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term165 x y z.
Proof. exact (conj (@lem7120748) (@lem7120684 x y z h1)). Qed.
Lemma lem7120751 (x : real) (y : real) : term109 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7120752 (x : real) (y : real) (z : real) : term166 x y z.
Proof. exact (@lem7120751 term23 (term53 x y z)). Qed.
Lemma lem7120753 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term167 x y z.
Proof. exact (@lem7120752 x y z (@lem7120749 x y z h1)). Qed.
Lemma lem7120754 (x : real) (y : real) (z : real) : (term168 x y z) = (term53 x y z).
Proof. exact (@lem1982733 (term53 x y z)). Qed.
Lemma lem7120755 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7120756 (x : real) (y : real) (z : real) : (term169 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem7120755) (@lem7120754 x y z)). Qed.
Lemma lem7120757 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120758 (x : real) (y : real) (z : real) : (term167 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem7120756 x y z) (@lem7120757)). Qed.
Lemma lem7120759 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term58 x y z.
Proof. exact (EQ_MP (@lem7120758 x y z) (@lem7120753 x y z h1)). Qed.
Lemma lem7120761 (y : real) : term114 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7120762 (x : real) (y : real) (z : real) : term115 x y z.
Proof. exact (@lem7120761 (term39 x y z)). Qed.
Lemma lem7120763 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term116 x y z.
Proof. exact (@lem7120762 x y z (@lem7120685 x y z h1)). Qed.
Lemma lem7120764 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term170 x y z.
Proof. exact (@lem7120763 x y z h1 term23). Qed.
Lemma lem7120765 (x : real) (y : real) (z : real) : (term170 x y z) = ((term112 x y z) = term3).
Proof. exact (eq_refl (term170 x y z)). Qed.
Lemma lem7120766 (x : real) (y : real) (z : real) (h1 : term164 x y z) : (term112 x y z) = term3.
Proof. exact (EQ_MP (@lem7120765 x y z) (@lem7120764 x y z h1)). Qed.
Lemma lem7120767 (x : real) (y : real) (z : real) : (term112 x y z) = (term39 x y z).
Proof. exact (@lem1982733 (term39 x y z)). Qed.
Lemma lem7120768 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7120769 (x : real) (y : real) (z : real) : (term171 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem7120768) (@lem7120767 x y z)). Qed.
Lemma lem7120770 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7120771 (x : real) (y : real) (z : real) : ((term112 x y z) = term3) = ((term39 x y z) = term3).
Proof. exact (MK_COMB (@lem7120769 x y z) (@lem7120770)). Qed.
Lemma lem7120772 (x : real) (y : real) (z : real) (h1 : term164 x y z) : (term39 x y z) = term3.
Proof. exact (EQ_MP (@lem7120771 x y z) (@lem7120766 x y z h1)). Qed.
Lemma lem7120773 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term164 x y z.
Proof. exact (conj (@lem7120772 x y z h1) (@lem7120759 x y z h1)). Qed.
Lemma lem7120775 (x : real) (y : real) : term121 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7120776 (x : real) (y : real) (z : real) : term172 x y z.
Proof. exact (@lem7120775 (term39 x y z) (term53 x y z)). Qed.
Lemma lem7120777 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term173 x y z.
Proof. exact (@lem7120776 x y z (@lem7120773 x y z h1)). Qed.
Lemma lem7120778 (x : real) (y : real) (z : real) : (term174 x y z) = (term175 x y z).
Proof. exact (@lem1982753 x (term6 x) (term4 y z) (term5 y z)). Qed.
Lemma lem7120779 (x : real) : (term153 x) = (term127 x).
Proof. exact (@lem1982715 term11 x). Qed.
Lemma lem7120781 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120782 : term23 = term33.
Proof. exact (@lem7120781 term17). Qed.
Lemma lem7120784 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120785 : term11 = term16.
Proof. exact (@lem7120784 term17). Qed.
Lemma lem7120786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120787 : term128 = term129.
Proof. exact (MK_COMB (@lem7120786) (@lem7120785)). Qed.
Lemma lem7120788 : term130 = term131.
Proof. exact (MK_COMB (@lem7120787) (@lem7120782)). Qed.
Lemma lem7120789 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7120791 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120792 : term93 = term101.
Proof. exact (@lem7120791 (NUMERAL 0) term17). Qed.
Lemma lem7120793 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120794 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120795 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120794 h1) (fun h1 : term101 = True => @lem7120793)). Qed.
Lemma lem7120796 : term101 = True.
Proof. exact (EQ_MP (@lem7120795) (@lem7120793)). Qed.
Lemma lem7120797 : term93 = True.
Proof. exact (TRANS (@lem7120792) (@lem7120796)). Qed.
Lemma lem7120798 : True = term93.
Proof. exact (SYM (@lem7120797)). Qed.
Lemma lem7120799 : term93.
Proof. exact (EQ_MP (@lem7120798) (@lem0)). Qed.
Lemma lem7120800 : term133.
Proof. exact (@lem7120789 (@lem7120799)). Qed.
Lemma lem7120802 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120803 : term93 = term101.
Proof. exact (@lem7120802 (NUMERAL 0) term17). Qed.
Lemma lem7120804 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120805 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120806 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120805 h1) (fun h1 : term101 = True => @lem7120804)). Qed.
Lemma lem7120807 : term101 = True.
Proof. exact (EQ_MP (@lem7120806) (@lem7120804)). Qed.
Lemma lem7120808 : term93 = True.
Proof. exact (TRANS (@lem7120803) (@lem7120807)). Qed.
Lemma lem7120809 : True = term93.
Proof. exact (SYM (@lem7120808)). Qed.
Lemma lem7120810 : term93.
Proof. exact (EQ_MP (@lem7120809) (@lem0)). Qed.
Lemma lem7120811 : term134.
Proof. exact (@lem7120800 (@lem7120810)). Qed.
Lemma lem7120813 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120814 : term93 = term101.
Proof. exact (@lem7120813 (NUMERAL 0) term17). Qed.
Lemma lem7120815 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120816 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120817 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120816 h1) (fun h1 : term101 = True => @lem7120815)). Qed.
Lemma lem7120818 : term101 = True.
Proof. exact (EQ_MP (@lem7120817) (@lem7120815)). Qed.
Lemma lem7120819 : term93 = True.
Proof. exact (TRANS (@lem7120814) (@lem7120818)). Qed.
Lemma lem7120820 : True = term93.
Proof. exact (SYM (@lem7120819)). Qed.
Lemma lem7120821 : term93.
Proof. exact (EQ_MP (@lem7120820) (@lem0)). Qed.
Lemma lem7120822 : term135.
Proof. exact (@lem7120811 (@lem7120821)). Qed.
Lemma lem7120824 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120825 : term26 = term27.
Proof. exact (@lem7120824 term17 term17). Qed.
Lemma lem7120826 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120827 : term29 = term17.
Proof. exact (EQ_MP (@lem7120826) (@lem940073)). Qed.
Lemma lem7120828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120829 : term27 = term23.
Proof. exact (MK_COMB (@lem7120828) (@lem7120827)). Qed.
Lemma lem7120830 : term26 = term23.
Proof. exact (TRANS (@lem7120825) (@lem7120829)). Qed.
Lemma lem7120832 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7120833 : term138 = term139.
Proof. exact (@lem7120832 term17 term17). Qed.
Lemma lem7120834 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120835 : term29 = term17.
Proof. exact (EQ_MP (@lem7120834) (@lem940073)). Qed.
Lemma lem7120836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120837 : term27 = term23.
Proof. exact (MK_COMB (@lem7120836) (@lem7120835)). Qed.
Lemma lem7120838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7120839 : term139 = term11.
Proof. exact (MK_COMB (@lem7120838) (@lem7120837)). Qed.
Lemma lem7120840 : term138 = term11.
Proof. exact (TRANS (@lem7120833) (@lem7120839)). Qed.
Lemma lem7120841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120842 : term140 = term128.
Proof. exact (MK_COMB (@lem7120841) (@lem7120840)). Qed.
Lemma lem7120843 : term141 = term130.
Proof. exact (MK_COMB (@lem7120842) (@lem7120830)). Qed.
Lemma lem7120845 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7120846 : term130 = term3.
Proof. exact (@lem7120845 term17). Qed.
Lemma lem7120847 : term141 = term3.
Proof. exact (TRANS (@lem7120843) (@lem7120846)). Qed.
Lemma lem7120848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120849 : term143 = term144.
Proof. exact (MK_COMB (@lem7120848) (@lem7120847)). Qed.
Lemma lem7120850 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7120851 : term145 = term106.
Proof. exact (MK_COMB (@lem7120849) (@lem7120850)). Qed.
Lemma lem7120853 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120854 : term106 = term3.
Proof. exact (@lem7120853 term17). Qed.
Lemma lem7120855 : term145 = term3.
Proof. exact (TRANS (@lem7120851) (@lem7120854)). Qed.
Lemma lem7120857 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120858 : term26 = term27.
Proof. exact (@lem7120857 term17 term17). Qed.
Lemma lem7120859 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120860 : term29 = term17.
Proof. exact (EQ_MP (@lem7120859) (@lem940073)). Qed.
Lemma lem7120861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120862 : term27 = term23.
Proof. exact (MK_COMB (@lem7120861) (@lem7120860)). Qed.
Lemma lem7120863 : term26 = term23.
Proof. exact (TRANS (@lem7120858) (@lem7120862)). Qed.
Lemma lem7120864 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7120865 : term146 = term106.
Proof. exact (MK_COMB (@lem7120864) (@lem7120863)). Qed.
Lemma lem7120867 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120868 : term106 = term3.
Proof. exact (@lem7120867 term17). Qed.
Lemma lem7120869 : term146 = term3.
Proof. exact (TRANS (@lem7120865) (@lem7120868)). Qed.
Lemma lem7120870 : term3 = term146.
Proof. exact (SYM (@lem7120869)). Qed.
Lemma lem7120871 : term145 = term146.
Proof. exact (TRANS (@lem7120855) (@lem7120870)). Qed.
Lemma lem7120872 : term131 = term95.
Proof. exact (@lem7120822 (@lem7120871)). Qed.
Lemma lem7120873 : term130 = term95.
Proof. exact (TRANS (@lem7120788) (@lem7120872)). Qed.
Lemma lem7120875 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7120876 : term95 = term3.
Proof. exact (@lem7120875 term3). Qed.
Lemma lem7120877 : term130 = term3.
Proof. exact (TRANS (@lem7120873) (@lem7120876)). Qed.
Lemma lem7120878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120879 : term147 = term144.
Proof. exact (MK_COMB (@lem7120878) (@lem7120877)). Qed.
Lemma lem7120880 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7120881 (x : real) : (term127 x) = (term148 x).
Proof. exact (MK_COMB (@lem7120879) (@lem7120880 x)). Qed.
Lemma lem7120882 (x : real) : (term153 x) = (term148 x).
Proof. exact (TRANS (@lem7120779 x) (@lem7120881 x)). Qed.
Lemma lem7120883 (x : real) : (term148 x) = term3.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7120884 (x : real) : (term153 x) = term3.
Proof. exact (TRANS (@lem7120882 x) (@lem7120883 x)). Qed.
Lemma lem7120885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120886 (x : real) : (term176 x) = term150.
Proof. exact (MK_COMB (@lem7120885) (@lem7120884 x)). Qed.
Lemma lem7120887 (y : real) (z : real) : (term177 y z) = (term178 y z).
Proof. exact (@lem1982753 y (term6 y) (term6 z) z). Qed.
Lemma lem7120888 (y : real) : (term153 y) = (term127 y).
Proof. exact (@lem1982715 term11 y). Qed.
Lemma lem7120890 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120891 : term23 = term33.
Proof. exact (@lem7120890 term17). Qed.
Lemma lem7120893 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7120894 : term11 = term16.
Proof. exact (@lem7120893 term17). Qed.
Lemma lem7120895 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120896 : term128 = term129.
Proof. exact (MK_COMB (@lem7120895) (@lem7120894)). Qed.
Lemma lem7120897 : term130 = term131.
Proof. exact (MK_COMB (@lem7120896) (@lem7120891)). Qed.
Lemma lem7120898 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7120900 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120901 : term93 = term101.
Proof. exact (@lem7120900 (NUMERAL 0) term17). Qed.
Lemma lem7120902 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120903 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120904 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120903 h1) (fun h1 : term101 = True => @lem7120902)). Qed.
Lemma lem7120905 : term101 = True.
Proof. exact (EQ_MP (@lem7120904) (@lem7120902)). Qed.
Lemma lem7120906 : term93 = True.
Proof. exact (TRANS (@lem7120901) (@lem7120905)). Qed.
Lemma lem7120907 : True = term93.
Proof. exact (SYM (@lem7120906)). Qed.
Lemma lem7120908 : term93.
Proof. exact (EQ_MP (@lem7120907) (@lem0)). Qed.
Lemma lem7120909 : term133.
Proof. exact (@lem7120898 (@lem7120908)). Qed.
Lemma lem7120911 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120912 : term93 = term101.
Proof. exact (@lem7120911 (NUMERAL 0) term17). Qed.
Lemma lem7120913 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120914 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120915 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120914 h1) (fun h1 : term101 = True => @lem7120913)). Qed.
Lemma lem7120916 : term101 = True.
Proof. exact (EQ_MP (@lem7120915) (@lem7120913)). Qed.
Lemma lem7120917 : term93 = True.
Proof. exact (TRANS (@lem7120912) (@lem7120916)). Qed.
Lemma lem7120918 : True = term93.
Proof. exact (SYM (@lem7120917)). Qed.
Lemma lem7120919 : term93.
Proof. exact (EQ_MP (@lem7120918) (@lem0)). Qed.
Lemma lem7120920 : term134.
Proof. exact (@lem7120909 (@lem7120919)). Qed.
Lemma lem7120922 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7120923 : term93 = term101.
Proof. exact (@lem7120922 (NUMERAL 0) term17). Qed.
Lemma lem7120924 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7120925 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7120926 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7120925 h1) (fun h1 : term101 = True => @lem7120924)). Qed.
Lemma lem7120927 : term101 = True.
Proof. exact (EQ_MP (@lem7120926) (@lem7120924)). Qed.
Lemma lem7120928 : term93 = True.
Proof. exact (TRANS (@lem7120923) (@lem7120927)). Qed.
Lemma lem7120929 : True = term93.
Proof. exact (SYM (@lem7120928)). Qed.
Lemma lem7120930 : term93.
Proof. exact (EQ_MP (@lem7120929) (@lem0)). Qed.
Lemma lem7120931 : term135.
Proof. exact (@lem7120920 (@lem7120930)). Qed.
Lemma lem7120933 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120934 : term26 = term27.
Proof. exact (@lem7120933 term17 term17). Qed.
Lemma lem7120935 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120936 : term29 = term17.
Proof. exact (EQ_MP (@lem7120935) (@lem940073)). Qed.
Lemma lem7120937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120938 : term27 = term23.
Proof. exact (MK_COMB (@lem7120937) (@lem7120936)). Qed.
Lemma lem7120939 : term26 = term23.
Proof. exact (TRANS (@lem7120934) (@lem7120938)). Qed.
Lemma lem7120941 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7120942 : term138 = term139.
Proof. exact (@lem7120941 term17 term17). Qed.
Lemma lem7120943 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120944 : term29 = term17.
Proof. exact (EQ_MP (@lem7120943) (@lem940073)). Qed.
Lemma lem7120945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120946 : term27 = term23.
Proof. exact (MK_COMB (@lem7120945) (@lem7120944)). Qed.
Lemma lem7120947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7120948 : term139 = term11.
Proof. exact (MK_COMB (@lem7120947) (@lem7120946)). Qed.
Lemma lem7120949 : term138 = term11.
Proof. exact (TRANS (@lem7120942) (@lem7120948)). Qed.
Lemma lem7120950 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120951 : term140 = term128.
Proof. exact (MK_COMB (@lem7120950) (@lem7120949)). Qed.
Lemma lem7120952 : term141 = term130.
Proof. exact (MK_COMB (@lem7120951) (@lem7120939)). Qed.
Lemma lem7120954 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7120955 : term130 = term3.
Proof. exact (@lem7120954 term17). Qed.
Lemma lem7120956 : term141 = term3.
Proof. exact (TRANS (@lem7120952) (@lem7120955)). Qed.
Lemma lem7120957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120958 : term143 = term144.
Proof. exact (MK_COMB (@lem7120957) (@lem7120956)). Qed.
Lemma lem7120959 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7120960 : term145 = term106.
Proof. exact (MK_COMB (@lem7120958) (@lem7120959)). Qed.
Lemma lem7120962 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120963 : term106 = term3.
Proof. exact (@lem7120962 term17). Qed.
Lemma lem7120964 : term145 = term3.
Proof. exact (TRANS (@lem7120960) (@lem7120963)). Qed.
Lemma lem7120966 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7120967 : term26 = term27.
Proof. exact (@lem7120966 term17 term17). Qed.
Lemma lem7120968 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7120969 : term29 = term17.
Proof. exact (EQ_MP (@lem7120968) (@lem940073)). Qed.
Lemma lem7120970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7120971 : term27 = term23.
Proof. exact (MK_COMB (@lem7120970) (@lem7120969)). Qed.
Lemma lem7120972 : term26 = term23.
Proof. exact (TRANS (@lem7120967) (@lem7120971)). Qed.
Lemma lem7120973 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7120974 : term146 = term106.
Proof. exact (MK_COMB (@lem7120973) (@lem7120972)). Qed.
Lemma lem7120976 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7120977 : term106 = term3.
Proof. exact (@lem7120976 term17). Qed.
Lemma lem7120978 : term146 = term3.
Proof. exact (TRANS (@lem7120974) (@lem7120977)). Qed.
Lemma lem7120979 : term3 = term146.
Proof. exact (SYM (@lem7120978)). Qed.
Lemma lem7120980 : term145 = term146.
Proof. exact (TRANS (@lem7120964) (@lem7120979)). Qed.
Lemma lem7120981 : term131 = term95.
Proof. exact (@lem7120931 (@lem7120980)). Qed.
Lemma lem7120982 : term130 = term95.
Proof. exact (TRANS (@lem7120897) (@lem7120981)). Qed.
Lemma lem7120984 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7120985 : term95 = term3.
Proof. exact (@lem7120984 term3). Qed.
Lemma lem7120986 : term130 = term3.
Proof. exact (TRANS (@lem7120982) (@lem7120985)). Qed.
Lemma lem7120987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7120988 : term147 = term144.
Proof. exact (MK_COMB (@lem7120987) (@lem7120986)). Qed.
Lemma lem7120989 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7120990 (y : real) : (term127 y) = (term148 y).
Proof. exact (MK_COMB (@lem7120988) (@lem7120989 y)). Qed.
Lemma lem7120991 (y : real) : (term153 y) = (term148 y).
Proof. exact (TRANS (@lem7120888 y) (@lem7120990 y)). Qed.
Lemma lem7120992 (y : real) : (term148 y) = term3.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7120993 (y : real) : (term153 y) = term3.
Proof. exact (TRANS (@lem7120991 y) (@lem7120992 y)). Qed.
Lemma lem7120994 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7120995 (y : real) : (term176 y) = term150.
Proof. exact (MK_COMB (@lem7120994) (@lem7120993 y)). Qed.
Lemma lem7120996 (z : real) : (term126 z) = (term127 z).
Proof. exact (@lem1982713 term11 z). Qed.
Lemma lem7120998 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7120999 : term23 = term33.
Proof. exact (@lem7120998 term17). Qed.
Lemma lem7121001 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121002 : term11 = term16.
Proof. exact (@lem7121001 term17). Qed.
Lemma lem7121003 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121004 : term128 = term129.
Proof. exact (MK_COMB (@lem7121003) (@lem7121002)). Qed.
Lemma lem7121005 : term130 = term131.
Proof. exact (MK_COMB (@lem7121004) (@lem7120999)). Qed.
Lemma lem7121006 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121008 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121009 : term93 = term101.
Proof. exact (@lem7121008 (NUMERAL 0) term17). Qed.
Lemma lem7121010 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121011 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121012 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121011 h1) (fun h1 : term101 = True => @lem7121010)). Qed.
Lemma lem7121013 : term101 = True.
Proof. exact (EQ_MP (@lem7121012) (@lem7121010)). Qed.
Lemma lem7121014 : term93 = True.
Proof. exact (TRANS (@lem7121009) (@lem7121013)). Qed.
Lemma lem7121015 : True = term93.
Proof. exact (SYM (@lem7121014)). Qed.
Lemma lem7121016 : term93.
Proof. exact (EQ_MP (@lem7121015) (@lem0)). Qed.
Lemma lem7121017 : term133.
Proof. exact (@lem7121006 (@lem7121016)). Qed.
Lemma lem7121019 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121020 : term93 = term101.
Proof. exact (@lem7121019 (NUMERAL 0) term17). Qed.
Lemma lem7121021 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121022 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121023 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121022 h1) (fun h1 : term101 = True => @lem7121021)). Qed.
Lemma lem7121024 : term101 = True.
Proof. exact (EQ_MP (@lem7121023) (@lem7121021)). Qed.
Lemma lem7121025 : term93 = True.
Proof. exact (TRANS (@lem7121020) (@lem7121024)). Qed.
Lemma lem7121026 : True = term93.
Proof. exact (SYM (@lem7121025)). Qed.
Lemma lem7121027 : term93.
Proof. exact (EQ_MP (@lem7121026) (@lem0)). Qed.
Lemma lem7121028 : term134.
Proof. exact (@lem7121017 (@lem7121027)). Qed.
Lemma lem7121030 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121031 : term93 = term101.
Proof. exact (@lem7121030 (NUMERAL 0) term17). Qed.
Lemma lem7121032 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121033 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121034 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121033 h1) (fun h1 : term101 = True => @lem7121032)). Qed.
Lemma lem7121035 : term101 = True.
Proof. exact (EQ_MP (@lem7121034) (@lem7121032)). Qed.
Lemma lem7121036 : term93 = True.
Proof. exact (TRANS (@lem7121031) (@lem7121035)). Qed.
Lemma lem7121037 : True = term93.
Proof. exact (SYM (@lem7121036)). Qed.
Lemma lem7121038 : term93.
Proof. exact (EQ_MP (@lem7121037) (@lem0)). Qed.
Lemma lem7121039 : term135.
Proof. exact (@lem7121028 (@lem7121038)). Qed.
Lemma lem7121041 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121042 : term26 = term27.
Proof. exact (@lem7121041 term17 term17). Qed.
Lemma lem7121043 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121044 : term29 = term17.
Proof. exact (EQ_MP (@lem7121043) (@lem940073)). Qed.
Lemma lem7121045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121046 : term27 = term23.
Proof. exact (MK_COMB (@lem7121045) (@lem7121044)). Qed.
Lemma lem7121047 : term26 = term23.
Proof. exact (TRANS (@lem7121042) (@lem7121046)). Qed.
Lemma lem7121049 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121050 : term138 = term139.
Proof. exact (@lem7121049 term17 term17). Qed.
Lemma lem7121051 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121052 : term29 = term17.
Proof. exact (EQ_MP (@lem7121051) (@lem940073)). Qed.
Lemma lem7121053 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121054 : term27 = term23.
Proof. exact (MK_COMB (@lem7121053) (@lem7121052)). Qed.
Lemma lem7121055 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121056 : term139 = term11.
Proof. exact (MK_COMB (@lem7121055) (@lem7121054)). Qed.
Lemma lem7121057 : term138 = term11.
Proof. exact (TRANS (@lem7121050) (@lem7121056)). Qed.
Lemma lem7121058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121059 : term140 = term128.
Proof. exact (MK_COMB (@lem7121058) (@lem7121057)). Qed.
Lemma lem7121060 : term141 = term130.
Proof. exact (MK_COMB (@lem7121059) (@lem7121047)). Qed.
Lemma lem7121062 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121063 : term130 = term3.
Proof. exact (@lem7121062 term17). Qed.
Lemma lem7121064 : term141 = term3.
Proof. exact (TRANS (@lem7121060) (@lem7121063)). Qed.
Lemma lem7121065 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121066 : term143 = term144.
Proof. exact (MK_COMB (@lem7121065) (@lem7121064)). Qed.
Lemma lem7121067 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121068 : term145 = term106.
Proof. exact (MK_COMB (@lem7121066) (@lem7121067)). Qed.
Lemma lem7121070 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121071 : term106 = term3.
Proof. exact (@lem7121070 term17). Qed.
Lemma lem7121072 : term145 = term3.
Proof. exact (TRANS (@lem7121068) (@lem7121071)). Qed.
Lemma lem7121074 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121075 : term26 = term27.
Proof. exact (@lem7121074 term17 term17). Qed.
Lemma lem7121076 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121077 : term29 = term17.
Proof. exact (EQ_MP (@lem7121076) (@lem940073)). Qed.
Lemma lem7121078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121079 : term27 = term23.
Proof. exact (MK_COMB (@lem7121078) (@lem7121077)). Qed.
Lemma lem7121080 : term26 = term23.
Proof. exact (TRANS (@lem7121075) (@lem7121079)). Qed.
Lemma lem7121081 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7121082 : term146 = term106.
Proof. exact (MK_COMB (@lem7121081) (@lem7121080)). Qed.
Lemma lem7121084 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121085 : term106 = term3.
Proof. exact (@lem7121084 term17). Qed.
Lemma lem7121086 : term146 = term3.
Proof. exact (TRANS (@lem7121082) (@lem7121085)). Qed.
Lemma lem7121087 : term3 = term146.
Proof. exact (SYM (@lem7121086)). Qed.
Lemma lem7121088 : term145 = term146.
Proof. exact (TRANS (@lem7121072) (@lem7121087)). Qed.
Lemma lem7121089 : term131 = term95.
Proof. exact (@lem7121039 (@lem7121088)). Qed.
Lemma lem7121090 : term130 = term95.
Proof. exact (TRANS (@lem7121005) (@lem7121089)). Qed.
Lemma lem7121092 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7121093 : term95 = term3.
Proof. exact (@lem7121092 term3). Qed.
Lemma lem7121094 : term130 = term3.
Proof. exact (TRANS (@lem7121090) (@lem7121093)). Qed.
Lemma lem7121095 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121096 : term147 = term144.
Proof. exact (MK_COMB (@lem7121095) (@lem7121094)). Qed.
Lemma lem7121097 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7121098 (z : real) : (term127 z) = (term148 z).
Proof. exact (MK_COMB (@lem7121096) (@lem7121097 z)). Qed.
Lemma lem7121099 (z : real) : (term126 z) = (term148 z).
Proof. exact (TRANS (@lem7120996 z) (@lem7121098 z)). Qed.
Lemma lem7121100 (z : real) : (term148 z) = term3.
Proof. exact (@lem1982719 z). Qed.
Lemma lem7121101 (z : real) : (term126 z) = term3.
Proof. exact (TRANS (@lem7121099 z) (@lem7121100 z)). Qed.
Lemma lem7121102 (y : real) (z : real) : (term178 y z) = term154.
Proof. exact (MK_COMB (@lem7120995 y) (@lem7121101 z)). Qed.
Lemma lem7121103 (y : real) (z : real) : (term177 y z) = term154.
Proof. exact (TRANS (@lem7120887 y z) (@lem7121102 y z)). Qed.
Lemma lem7121104 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7121105 (y : real) (z : real) : (term177 y z) = term3.
Proof. exact (TRANS (@lem7121103 y z) (@lem7121104)). Qed.
Lemma lem7121106 (x : real) (y : real) (z : real) : (term175 x y z) = term154.
Proof. exact (MK_COMB (@lem7120886 x) (@lem7121105 y z)). Qed.
Lemma lem7121107 (x : real) (y : real) (z : real) : (term174 x y z) = term154.
Proof. exact (TRANS (@lem7120778 x y z) (@lem7121106 x y z)). Qed.
Lemma lem7121108 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7121109 (x : real) (y : real) (z : real) : (term174 x y z) = term3.
Proof. exact (TRANS (@lem7121107 x y z) (@lem7121108)). Qed.
Lemma lem7121110 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7121111 (x : real) (y : real) (z : real) : (term179 x y z) = term156.
Proof. exact (MK_COMB (@lem7121110) (@lem7121109 x y z)). Qed.
Lemma lem7121112 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121113 (x : real) (y : real) (z : real) : (term173 x y z) = term157.
Proof. exact (MK_COMB (@lem7121111 x y z) (@lem7121112)). Qed.
Lemma lem7121114 (x : real) (y : real) (z : real) (h1 : term164 x y z) : term157.
Proof. exact (EQ_MP (@lem7121113 x y z) (@lem7120777 x y z h1)). Qed.
Lemma lem7121116 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7121117 : term157 = term158.
Proof. exact (@lem7121116 term3 term3). Qed.
Lemma lem7121119 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121120 : term3 = term95.
Proof. exact (@lem7121119 (NUMERAL 0)). Qed.
Lemma lem7121122 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121123 : term3 = term95.
Proof. exact (@lem7121122 (NUMERAL 0)). Qed.
Lemma lem7121124 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121125 : term96 = term97.
Proof. exact (MK_COMB (@lem7121124) (@lem7121123)). Qed.
Lemma lem7121126 : term158 = term159.
Proof. exact (MK_COMB (@lem7121125) (@lem7121120)). Qed.
Lemma lem7121127 : term160.
Proof. exact (@lem1980255 term3 term23 term3 term23). Qed.
Lemma lem7121129 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121130 : term93 = term101.
Proof. exact (@lem7121129 (NUMERAL 0) term17). Qed.
Lemma lem7121131 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121132 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121133 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121132 h1) (fun h1 : term101 = True => @lem7121131)). Qed.
Lemma lem7121134 : term101 = True.
Proof. exact (EQ_MP (@lem7121133) (@lem7121131)). Qed.
Lemma lem7121135 : term93 = True.
Proof. exact (TRANS (@lem7121130) (@lem7121134)). Qed.
Lemma lem7121136 : True = term93.
Proof. exact (SYM (@lem7121135)). Qed.
Lemma lem7121137 : term93.
Proof. exact (EQ_MP (@lem7121136) (@lem0)). Qed.
Lemma lem7121138 : term161.
Proof. exact (@lem7121127 (@lem7121137)). Qed.
Lemma lem7121140 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121141 : term93 = term101.
Proof. exact (@lem7121140 (NUMERAL 0) term17). Qed.
Lemma lem7121142 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121143 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121144 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121143 h1) (fun h1 : term101 = True => @lem7121142)). Qed.
Lemma lem7121145 : term101 = True.
Proof. exact (EQ_MP (@lem7121144) (@lem7121142)). Qed.
Lemma lem7121146 : term93 = True.
Proof. exact (TRANS (@lem7121141) (@lem7121145)). Qed.
Lemma lem7121147 : True = term93.
Proof. exact (SYM (@lem7121146)). Qed.
Lemma lem7121148 : term93.
Proof. exact (EQ_MP (@lem7121147) (@lem0)). Qed.
Lemma lem7121149 : term159 = term162.
Proof. exact (@lem7121138 (@lem7121148)). Qed.
Lemma lem7121151 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121152 : term106 = term3.
Proof. exact (@lem7121151 term17). Qed.
Lemma lem7121154 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121155 : term106 = term3.
Proof. exact (@lem7121154 term17). Qed.
Lemma lem7121156 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121157 : term107 = term96.
Proof. exact (MK_COMB (@lem7121156) (@lem7121155)). Qed.
Lemma lem7121158 : term162 = term158.
Proof. exact (MK_COMB (@lem7121157) (@lem7121152)). Qed.
Lemma lem7121160 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121161 : term158 = term163.
Proof. exact (@lem7121160 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7121162 : term163 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7121163 : term158 = False.
Proof. exact (TRANS (@lem7121161) (@lem7121162)). Qed.
Lemma lem7121164 : term162 = False.
Proof. exact (TRANS (@lem7121158) (@lem7121163)). Qed.
Lemma lem7121165 : term159 = False.
Proof. exact (TRANS (@lem7121149) (@lem7121164)). Qed.
Lemma lem7121166 : term158 = False.
Proof. exact (TRANS (@lem7121126) (@lem7121165)). Qed.
Lemma lem7121167 : term157 = False.
Proof. exact (TRANS (@lem7121117) (@lem7121166)). Qed.
Lemma lem7121168 (x : real) (y : real) (z : real) (h1 : term164 x y z) : False.
Proof. exact (EQ_MP (@lem7121167) (@lem7121114 x y z h1)). Qed.
Lemma lem7121169 (x : real) (y : real) (z : real) (h1 : term88 x y z) : False.
Proof. exact (or_elim (@lem7120142 x y z h1) (fun h0 : term91 x y z => @lem7120682 x y z h0) (fun h0 : term164 x y z => @lem7121168 x y z h0)). Qed.
Lemma lem7121170 (x : real) (y : real) (z : real) (h1 : term87 x y z) : term87 x y z.
Proof. exact (h1). Qed.
Lemma lem7121171 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term180 x y z.
Proof. exact (h1). Qed.
Lemma lem7121172 (x : real) (y : real) (z : real) (h1 : term180 x y z) : (term39 x y z) = term3.
Proof. exact (proj2 (@lem7121171 x y z h1)). Qed.
Lemma lem7121173 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term62 x y z.
Proof. exact (proj1 (@lem7121171 x y z h1)). Qed.
Lemma lem7121175 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7121176 : term92 = term93.
Proof. exact (@lem7121175 term3 term23). Qed.
Lemma lem7121178 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121179 : term23 = term33.
Proof. exact (@lem7121178 term17). Qed.
Lemma lem7121181 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121182 : term3 = term95.
Proof. exact (@lem7121181 (NUMERAL 0)). Qed.
Lemma lem7121183 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121184 : term96 = term97.
Proof. exact (MK_COMB (@lem7121183) (@lem7121182)). Qed.
Lemma lem7121185 : term93 = term98.
Proof. exact (MK_COMB (@lem7121184) (@lem7121179)). Qed.
Lemma lem7121186 : term99.
Proof. exact (@lem1980255 term3 term23 term23 term23). Qed.
Lemma lem7121188 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121189 : term93 = term101.
Proof. exact (@lem7121188 (NUMERAL 0) term17). Qed.
Lemma lem7121190 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121191 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121192 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121191 h1) (fun h1 : term101 = True => @lem7121190)). Qed.
Lemma lem7121193 : term101 = True.
Proof. exact (EQ_MP (@lem7121192) (@lem7121190)). Qed.
Lemma lem7121194 : term93 = True.
Proof. exact (TRANS (@lem7121189) (@lem7121193)). Qed.
Lemma lem7121195 : True = term93.
Proof. exact (SYM (@lem7121194)). Qed.
Lemma lem7121196 : term93.
Proof. exact (EQ_MP (@lem7121195) (@lem0)). Qed.
Lemma lem7121197 : term103.
Proof. exact (@lem7121186 (@lem7121196)). Qed.
Lemma lem7121199 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121200 : term93 = term101.
Proof. exact (@lem7121199 (NUMERAL 0) term17). Qed.
Lemma lem7121201 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121202 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121203 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121202 h1) (fun h1 : term101 = True => @lem7121201)). Qed.
Lemma lem7121204 : term101 = True.
Proof. exact (EQ_MP (@lem7121203) (@lem7121201)). Qed.
Lemma lem7121205 : term93 = True.
Proof. exact (TRANS (@lem7121200) (@lem7121204)). Qed.
Lemma lem7121206 : True = term93.
Proof. exact (SYM (@lem7121205)). Qed.
Lemma lem7121207 : term93.
Proof. exact (EQ_MP (@lem7121206) (@lem0)). Qed.
Lemma lem7121208 : term98 = term104.
Proof. exact (@lem7121197 (@lem7121207)). Qed.
Lemma lem7121210 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121211 : term26 = term27.
Proof. exact (@lem7121210 term17 term17). Qed.
Lemma lem7121212 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121213 : term29 = term17.
Proof. exact (EQ_MP (@lem7121212) (@lem940073)). Qed.
Lemma lem7121214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121215 : term27 = term23.
Proof. exact (MK_COMB (@lem7121214) (@lem7121213)). Qed.
Lemma lem7121216 : term26 = term23.
Proof. exact (TRANS (@lem7121211) (@lem7121215)). Qed.
Lemma lem7121218 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121219 : term106 = term3.
Proof. exact (@lem7121218 term17). Qed.
Lemma lem7121220 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121221 : term107 = term96.
Proof. exact (MK_COMB (@lem7121220) (@lem7121219)). Qed.
Lemma lem7121222 : term104 = term93.
Proof. exact (MK_COMB (@lem7121221) (@lem7121216)). Qed.
Lemma lem7121224 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121225 : term93 = term101.
Proof. exact (@lem7121224 (NUMERAL 0) term17). Qed.
Lemma lem7121226 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121227 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121228 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121227 h1) (fun h1 : term101 = True => @lem7121226)). Qed.
Lemma lem7121229 : term101 = True.
Proof. exact (EQ_MP (@lem7121228) (@lem7121226)). Qed.
Lemma lem7121230 : term93 = True.
Proof. exact (TRANS (@lem7121225) (@lem7121229)). Qed.
Lemma lem7121231 : term104 = True.
Proof. exact (TRANS (@lem7121222) (@lem7121230)). Qed.
Lemma lem7121232 : term98 = True.
Proof. exact (TRANS (@lem7121208) (@lem7121231)). Qed.
Lemma lem7121233 : term93 = True.
Proof. exact (TRANS (@lem7121185) (@lem7121232)). Qed.
Lemma lem7121234 : term92 = True.
Proof. exact (TRANS (@lem7121176) (@lem7121233)). Qed.
Lemma lem7121235 : True = term92.
Proof. exact (SYM (@lem7121234)). Qed.
Lemma lem7121236 : term92.
Proof. exact (EQ_MP (@lem7121235) (@lem0)). Qed.
Lemma lem7121237 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term108 x y z.
Proof. exact (conj (@lem7121236) (@lem7121173 x y z h1)). Qed.
Lemma lem7121239 (x : real) (y : real) : term109 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7121240 (x : real) (y : real) (z : real) : term110 x y z.
Proof. exact (@lem7121239 term23 (term39 x y z)). Qed.
Lemma lem7121241 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term111 x y z.
Proof. exact (@lem7121240 x y z (@lem7121237 x y z h1)). Qed.
Lemma lem7121242 (x : real) (y : real) (z : real) : (term112 x y z) = (term39 x y z).
Proof. exact (@lem1982733 (term39 x y z)). Qed.
Lemma lem7121243 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7121244 (x : real) (y : real) (z : real) : (term113 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem7121243) (@lem7121242 x y z)). Qed.
Lemma lem7121245 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121246 (x : real) (y : real) (z : real) : (term111 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem7121244 x y z) (@lem7121245)). Qed.
Lemma lem7121247 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term62 x y z.
Proof. exact (EQ_MP (@lem7121246 x y z) (@lem7121241 x y z h1)). Qed.
Lemma lem7121249 (y : real) : term114 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7121250 (x : real) (y : real) (z : real) : term115 x y z.
Proof. exact (@lem7121249 (term39 x y z)). Qed.
Lemma lem7121251 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term116 x y z.
Proof. exact (@lem7121250 x y z (@lem7121172 x y z h1)). Qed.
Lemma lem7121252 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term117 x y z.
Proof. exact (@lem7121251 x y z h1 term11). Qed.
Lemma lem7121253 (x : real) (y : real) (z : real) : (term117 x y z) = ((term48 x y z) = term3).
Proof. exact (eq_refl (term117 x y z)). Qed.
Lemma lem7121254 (x : real) (y : real) (z : real) (h1 : term180 x y z) : (term48 x y z) = term3.
Proof. exact (EQ_MP (@lem7121253 x y z) (@lem7121252 x y z h1)). Qed.
Lemma lem7121255 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (@lem1982781 x term11 (term4 y z)). Qed.
Lemma lem7121256 (y : real) (z : real) : (term50 y z) = (term51 y z).
Proof. exact (@lem1982781 y term11 (term6 z)). Qed.
Lemma lem7121257 (z : real) : (term12 z) = (term13 z).
Proof. exact (@lem1982749 term11 term11 z). Qed.
Lemma lem7121259 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121260 : term11 = term16.
Proof. exact (@lem7121259 term17). Qed.
Lemma lem7121262 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121263 : term11 = term16.
Proof. exact (@lem7121262 term17). Qed.
Lemma lem7121264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121265 : term18 = term19.
Proof. exact (MK_COMB (@lem7121264) (@lem7121263)). Qed.
Lemma lem7121266 : term20 = term21.
Proof. exact (MK_COMB (@lem7121265) (@lem7121260)). Qed.
Lemma lem7121267 : term21 = term22.
Proof. exact (@lem1981613 term11 term11 term23 term23). Qed.
Lemma lem7121269 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121270 : term26 = term27.
Proof. exact (@lem7121269 term17 term17). Qed.
Lemma lem7121271 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121272 : term29 = term17.
Proof. exact (EQ_MP (@lem7121271) (@lem940073)). Qed.
Lemma lem7121273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121274 : term27 = term23.
Proof. exact (MK_COMB (@lem7121273) (@lem7121272)). Qed.
Lemma lem7121275 : term26 = term23.
Proof. exact (TRANS (@lem7121270) (@lem7121274)). Qed.
Lemma lem7121277 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7121278 : term20 = term27.
Proof. exact (@lem7121277 term17 term17). Qed.
Lemma lem7121279 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121280 : term29 = term17.
Proof. exact (EQ_MP (@lem7121279) (@lem940073)). Qed.
Lemma lem7121281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121282 : term27 = term23.
Proof. exact (MK_COMB (@lem7121281) (@lem7121280)). Qed.
Lemma lem7121283 : term20 = term23.
Proof. exact (TRANS (@lem7121278) (@lem7121282)). Qed.
Lemma lem7121284 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7121285 : term31 = term32.
Proof. exact (MK_COMB (@lem7121284) (@lem7121283)). Qed.
Lemma lem7121286 : term22 = term33.
Proof. exact (MK_COMB (@lem7121285) (@lem7121275)). Qed.
Lemma lem7121287 : term21 = term33.
Proof. exact (TRANS (@lem7121267) (@lem7121286)). Qed.
Lemma lem7121288 : term20 = term33.
Proof. exact (TRANS (@lem7121266) (@lem7121287)). Qed.
Lemma lem7121290 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7121291 : term33 = term23.
Proof. exact (@lem7121290 term23). Qed.
Lemma lem7121292 : term20 = term23.
Proof. exact (TRANS (@lem7121288) (@lem7121291)). Qed.
Lemma lem7121293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121294 : term35 = term36.
Proof. exact (MK_COMB (@lem7121293) (@lem7121292)). Qed.
Lemma lem7121295 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7121296 (z : real) : (term13 z) = (term37 z).
Proof. exact (MK_COMB (@lem7121294) (@lem7121295 z)). Qed.
Lemma lem7121297 (z : real) : (term12 z) = (term37 z).
Proof. exact (TRANS (@lem7121257 z) (@lem7121296 z)). Qed.
Lemma lem7121298 (z : real) : (term37 z) = z.
Proof. exact (@lem1982709 z). Qed.
Lemma lem7121299 (z : real) : (term12 z) = z.
Proof. exact (TRANS (@lem7121297 z) (@lem7121298 z)). Qed.
Lemma lem7121302 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem7121303 (y : real) (z : real) : (term51 y z) = (term5 y z).
Proof. exact (MK_COMB (@lem7121302 y) (@lem7121299 z)). Qed.
Lemma lem7121304 (y : real) (z : real) : (term50 y z) = (term5 y z).
Proof. exact (TRANS (@lem7121256 y z) (@lem7121303 y z)). Qed.
Lemma lem7121307 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem7121308 (x : real) (y : real) (z : real) : (term49 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem7121307 x) (@lem7121304 y z)). Qed.
Lemma lem7121309 (x : real) (y : real) (z : real) : (term48 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem7121255 x y z) (@lem7121308 x y z)). Qed.
Lemma lem7121310 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7121311 (x : real) (y : real) (z : real) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem7121310) (@lem7121309 x y z)). Qed.
Lemma lem7121312 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121313 (x : real) (y : real) (z : real) : ((term48 x y z) = term3) = ((term53 x y z) = term3).
Proof. exact (MK_COMB (@lem7121311 x y z) (@lem7121312)). Qed.
Lemma lem7121314 (x : real) (y : real) (z : real) (h1 : term180 x y z) : (term53 x y z) = term3.
Proof. exact (EQ_MP (@lem7121313 x y z) (@lem7121254 x y z h1)). Qed.
Lemma lem7121315 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term120 x y z.
Proof. exact (conj (@lem7121314 x y z h1) (@lem7121247 x y z h1)). Qed.
Lemma lem7121317 (x : real) (y : real) : term121 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7121318 (x : real) (y : real) (z : real) : term122 x y z.
Proof. exact (@lem7121317 (term53 x y z) (term39 x y z)). Qed.
Lemma lem7121319 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term123 x y z.
Proof. exact (@lem7121318 x y z (@lem7121315 x y z h1)). Qed.
Lemma lem7121320 (x : real) (y : real) (z : real) : (term124 x y z) = (term125 x y z).
Proof. exact (@lem1982753 (term6 x) x (term5 y z) (term4 y z)). Qed.
Lemma lem7121321 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1982713 term11 x). Qed.
Lemma lem7121323 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121324 : term23 = term33.
Proof. exact (@lem7121323 term17). Qed.
Lemma lem7121326 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121327 : term11 = term16.
Proof. exact (@lem7121326 term17). Qed.
Lemma lem7121328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121329 : term128 = term129.
Proof. exact (MK_COMB (@lem7121328) (@lem7121327)). Qed.
Lemma lem7121330 : term130 = term131.
Proof. exact (MK_COMB (@lem7121329) (@lem7121324)). Qed.
Lemma lem7121331 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121333 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121334 : term93 = term101.
Proof. exact (@lem7121333 (NUMERAL 0) term17). Qed.
Lemma lem7121335 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121336 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121337 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121336 h1) (fun h1 : term101 = True => @lem7121335)). Qed.
Lemma lem7121338 : term101 = True.
Proof. exact (EQ_MP (@lem7121337) (@lem7121335)). Qed.
Lemma lem7121339 : term93 = True.
Proof. exact (TRANS (@lem7121334) (@lem7121338)). Qed.
Lemma lem7121340 : True = term93.
Proof. exact (SYM (@lem7121339)). Qed.
Lemma lem7121341 : term93.
Proof. exact (EQ_MP (@lem7121340) (@lem0)). Qed.
Lemma lem7121342 : term133.
Proof. exact (@lem7121331 (@lem7121341)). Qed.
Lemma lem7121344 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121345 : term93 = term101.
Proof. exact (@lem7121344 (NUMERAL 0) term17). Qed.
Lemma lem7121346 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121347 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121348 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121347 h1) (fun h1 : term101 = True => @lem7121346)). Qed.
Lemma lem7121349 : term101 = True.
Proof. exact (EQ_MP (@lem7121348) (@lem7121346)). Qed.
Lemma lem7121350 : term93 = True.
Proof. exact (TRANS (@lem7121345) (@lem7121349)). Qed.
Lemma lem7121351 : True = term93.
Proof. exact (SYM (@lem7121350)). Qed.
Lemma lem7121352 : term93.
Proof. exact (EQ_MP (@lem7121351) (@lem0)). Qed.
Lemma lem7121353 : term134.
Proof. exact (@lem7121342 (@lem7121352)). Qed.
Lemma lem7121355 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121356 : term93 = term101.
Proof. exact (@lem7121355 (NUMERAL 0) term17). Qed.
Lemma lem7121357 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121358 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121359 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121358 h1) (fun h1 : term101 = True => @lem7121357)). Qed.
Lemma lem7121360 : term101 = True.
Proof. exact (EQ_MP (@lem7121359) (@lem7121357)). Qed.
Lemma lem7121361 : term93 = True.
Proof. exact (TRANS (@lem7121356) (@lem7121360)). Qed.
Lemma lem7121362 : True = term93.
Proof. exact (SYM (@lem7121361)). Qed.
Lemma lem7121363 : term93.
Proof. exact (EQ_MP (@lem7121362) (@lem0)). Qed.
Lemma lem7121364 : term135.
Proof. exact (@lem7121353 (@lem7121363)). Qed.
Lemma lem7121366 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121367 : term26 = term27.
Proof. exact (@lem7121366 term17 term17). Qed.
Lemma lem7121368 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121369 : term29 = term17.
Proof. exact (EQ_MP (@lem7121368) (@lem940073)). Qed.
Lemma lem7121370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121371 : term27 = term23.
Proof. exact (MK_COMB (@lem7121370) (@lem7121369)). Qed.
Lemma lem7121372 : term26 = term23.
Proof. exact (TRANS (@lem7121367) (@lem7121371)). Qed.
Lemma lem7121374 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121375 : term138 = term139.
Proof. exact (@lem7121374 term17 term17). Qed.
Lemma lem7121376 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121377 : term29 = term17.
Proof. exact (EQ_MP (@lem7121376) (@lem940073)). Qed.
Lemma lem7121378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121379 : term27 = term23.
Proof. exact (MK_COMB (@lem7121378) (@lem7121377)). Qed.
Lemma lem7121380 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121381 : term139 = term11.
Proof. exact (MK_COMB (@lem7121380) (@lem7121379)). Qed.
Lemma lem7121382 : term138 = term11.
Proof. exact (TRANS (@lem7121375) (@lem7121381)). Qed.
Lemma lem7121383 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121384 : term140 = term128.
Proof. exact (MK_COMB (@lem7121383) (@lem7121382)). Qed.
Lemma lem7121385 : term141 = term130.
Proof. exact (MK_COMB (@lem7121384) (@lem7121372)). Qed.
Lemma lem7121387 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121388 : term130 = term3.
Proof. exact (@lem7121387 term17). Qed.
Lemma lem7121389 : term141 = term3.
Proof. exact (TRANS (@lem7121385) (@lem7121388)). Qed.
Lemma lem7121390 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121391 : term143 = term144.
Proof. exact (MK_COMB (@lem7121390) (@lem7121389)). Qed.
Lemma lem7121392 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121393 : term145 = term106.
Proof. exact (MK_COMB (@lem7121391) (@lem7121392)). Qed.
Lemma lem7121395 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121396 : term106 = term3.
Proof. exact (@lem7121395 term17). Qed.
Lemma lem7121397 : term145 = term3.
Proof. exact (TRANS (@lem7121393) (@lem7121396)). Qed.
Lemma lem7121399 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121400 : term26 = term27.
Proof. exact (@lem7121399 term17 term17). Qed.
Lemma lem7121401 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121402 : term29 = term17.
Proof. exact (EQ_MP (@lem7121401) (@lem940073)). Qed.
Lemma lem7121403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121404 : term27 = term23.
Proof. exact (MK_COMB (@lem7121403) (@lem7121402)). Qed.
Lemma lem7121405 : term26 = term23.
Proof. exact (TRANS (@lem7121400) (@lem7121404)). Qed.
Lemma lem7121406 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7121407 : term146 = term106.
Proof. exact (MK_COMB (@lem7121406) (@lem7121405)). Qed.
Lemma lem7121409 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121410 : term106 = term3.
Proof. exact (@lem7121409 term17). Qed.
Lemma lem7121411 : term146 = term3.
Proof. exact (TRANS (@lem7121407) (@lem7121410)). Qed.
Lemma lem7121412 : term3 = term146.
Proof. exact (SYM (@lem7121411)). Qed.
Lemma lem7121413 : term145 = term146.
Proof. exact (TRANS (@lem7121397) (@lem7121412)). Qed.
Lemma lem7121414 : term131 = term95.
Proof. exact (@lem7121364 (@lem7121413)). Qed.
Lemma lem7121415 : term130 = term95.
Proof. exact (TRANS (@lem7121330) (@lem7121414)). Qed.
Lemma lem7121417 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7121418 : term95 = term3.
Proof. exact (@lem7121417 term3). Qed.
Lemma lem7121419 : term130 = term3.
Proof. exact (TRANS (@lem7121415) (@lem7121418)). Qed.
Lemma lem7121420 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121421 : term147 = term144.
Proof. exact (MK_COMB (@lem7121420) (@lem7121419)). Qed.
Lemma lem7121422 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7121423 (x : real) : (term127 x) = (term148 x).
Proof. exact (MK_COMB (@lem7121421) (@lem7121422 x)). Qed.
Lemma lem7121424 (x : real) : (term126 x) = (term148 x).
Proof. exact (TRANS (@lem7121321 x) (@lem7121423 x)). Qed.
Lemma lem7121425 (x : real) : (term148 x) = term3.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7121426 (x : real) : (term126 x) = term3.
Proof. exact (TRANS (@lem7121424 x) (@lem7121425 x)). Qed.
Lemma lem7121427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121428 (x : real) : (term149 x) = term150.
Proof. exact (MK_COMB (@lem7121427) (@lem7121426 x)). Qed.
Lemma lem7121429 (y : real) (z : real) : (term151 y z) = (term152 y z).
Proof. exact (@lem1982753 (term6 y) y z (term6 z)). Qed.
Lemma lem7121430 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1982713 term11 y). Qed.
Lemma lem7121432 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121433 : term23 = term33.
Proof. exact (@lem7121432 term17). Qed.
Lemma lem7121435 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121436 : term11 = term16.
Proof. exact (@lem7121435 term17). Qed.
Lemma lem7121437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121438 : term128 = term129.
Proof. exact (MK_COMB (@lem7121437) (@lem7121436)). Qed.
Lemma lem7121439 : term130 = term131.
Proof. exact (MK_COMB (@lem7121438) (@lem7121433)). Qed.
Lemma lem7121440 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121442 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121443 : term93 = term101.
Proof. exact (@lem7121442 (NUMERAL 0) term17). Qed.
Lemma lem7121444 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121445 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121446 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121445 h1) (fun h1 : term101 = True => @lem7121444)). Qed.
Lemma lem7121447 : term101 = True.
Proof. exact (EQ_MP (@lem7121446) (@lem7121444)). Qed.
Lemma lem7121448 : term93 = True.
Proof. exact (TRANS (@lem7121443) (@lem7121447)). Qed.
Lemma lem7121449 : True = term93.
Proof. exact (SYM (@lem7121448)). Qed.
Lemma lem7121450 : term93.
Proof. exact (EQ_MP (@lem7121449) (@lem0)). Qed.
Lemma lem7121451 : term133.
Proof. exact (@lem7121440 (@lem7121450)). Qed.
Lemma lem7121453 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121454 : term93 = term101.
Proof. exact (@lem7121453 (NUMERAL 0) term17). Qed.
Lemma lem7121455 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121456 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121457 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121456 h1) (fun h1 : term101 = True => @lem7121455)). Qed.
Lemma lem7121458 : term101 = True.
Proof. exact (EQ_MP (@lem7121457) (@lem7121455)). Qed.
Lemma lem7121459 : term93 = True.
Proof. exact (TRANS (@lem7121454) (@lem7121458)). Qed.
Lemma lem7121460 : True = term93.
Proof. exact (SYM (@lem7121459)). Qed.
Lemma lem7121461 : term93.
Proof. exact (EQ_MP (@lem7121460) (@lem0)). Qed.
Lemma lem7121462 : term134.
Proof. exact (@lem7121451 (@lem7121461)). Qed.
Lemma lem7121464 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121465 : term93 = term101.
Proof. exact (@lem7121464 (NUMERAL 0) term17). Qed.
Lemma lem7121466 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121467 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121468 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121467 h1) (fun h1 : term101 = True => @lem7121466)). Qed.
Lemma lem7121469 : term101 = True.
Proof. exact (EQ_MP (@lem7121468) (@lem7121466)). Qed.
Lemma lem7121470 : term93 = True.
Proof. exact (TRANS (@lem7121465) (@lem7121469)). Qed.
Lemma lem7121471 : True = term93.
Proof. exact (SYM (@lem7121470)). Qed.
Lemma lem7121472 : term93.
Proof. exact (EQ_MP (@lem7121471) (@lem0)). Qed.
Lemma lem7121473 : term135.
Proof. exact (@lem7121462 (@lem7121472)). Qed.
Lemma lem7121475 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121476 : term26 = term27.
Proof. exact (@lem7121475 term17 term17). Qed.
Lemma lem7121477 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121478 : term29 = term17.
Proof. exact (EQ_MP (@lem7121477) (@lem940073)). Qed.
Lemma lem7121479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121480 : term27 = term23.
Proof. exact (MK_COMB (@lem7121479) (@lem7121478)). Qed.
Lemma lem7121481 : term26 = term23.
Proof. exact (TRANS (@lem7121476) (@lem7121480)). Qed.
Lemma lem7121483 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121484 : term138 = term139.
Proof. exact (@lem7121483 term17 term17). Qed.
Lemma lem7121485 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121486 : term29 = term17.
Proof. exact (EQ_MP (@lem7121485) (@lem940073)). Qed.
Lemma lem7121487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121488 : term27 = term23.
Proof. exact (MK_COMB (@lem7121487) (@lem7121486)). Qed.
Lemma lem7121489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121490 : term139 = term11.
Proof. exact (MK_COMB (@lem7121489) (@lem7121488)). Qed.
Lemma lem7121491 : term138 = term11.
Proof. exact (TRANS (@lem7121484) (@lem7121490)). Qed.
Lemma lem7121492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121493 : term140 = term128.
Proof. exact (MK_COMB (@lem7121492) (@lem7121491)). Qed.
Lemma lem7121494 : term141 = term130.
Proof. exact (MK_COMB (@lem7121493) (@lem7121481)). Qed.
Lemma lem7121496 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121497 : term130 = term3.
Proof. exact (@lem7121496 term17). Qed.
Lemma lem7121498 : term141 = term3.
Proof. exact (TRANS (@lem7121494) (@lem7121497)). Qed.
Lemma lem7121499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121500 : term143 = term144.
Proof. exact (MK_COMB (@lem7121499) (@lem7121498)). Qed.
Lemma lem7121501 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121502 : term145 = term106.
Proof. exact (MK_COMB (@lem7121500) (@lem7121501)). Qed.
Lemma lem7121504 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121505 : term106 = term3.
Proof. exact (@lem7121504 term17). Qed.
Lemma lem7121506 : term145 = term3.
Proof. exact (TRANS (@lem7121502) (@lem7121505)). Qed.
Lemma lem7121508 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121509 : term26 = term27.
Proof. exact (@lem7121508 term17 term17). Qed.
Lemma lem7121510 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121511 : term29 = term17.
Proof. exact (EQ_MP (@lem7121510) (@lem940073)). Qed.
Lemma lem7121512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121513 : term27 = term23.
Proof. exact (MK_COMB (@lem7121512) (@lem7121511)). Qed.
Lemma lem7121514 : term26 = term23.
Proof. exact (TRANS (@lem7121509) (@lem7121513)). Qed.
Lemma lem7121515 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7121516 : term146 = term106.
Proof. exact (MK_COMB (@lem7121515) (@lem7121514)). Qed.
Lemma lem7121518 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121519 : term106 = term3.
Proof. exact (@lem7121518 term17). Qed.
Lemma lem7121520 : term146 = term3.
Proof. exact (TRANS (@lem7121516) (@lem7121519)). Qed.
Lemma lem7121521 : term3 = term146.
Proof. exact (SYM (@lem7121520)). Qed.
Lemma lem7121522 : term145 = term146.
Proof. exact (TRANS (@lem7121506) (@lem7121521)). Qed.
Lemma lem7121523 : term131 = term95.
Proof. exact (@lem7121473 (@lem7121522)). Qed.
Lemma lem7121524 : term130 = term95.
Proof. exact (TRANS (@lem7121439) (@lem7121523)). Qed.
Lemma lem7121526 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7121527 : term95 = term3.
Proof. exact (@lem7121526 term3). Qed.
Lemma lem7121528 : term130 = term3.
Proof. exact (TRANS (@lem7121524) (@lem7121527)). Qed.
Lemma lem7121529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121530 : term147 = term144.
Proof. exact (MK_COMB (@lem7121529) (@lem7121528)). Qed.
Lemma lem7121531 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7121532 (y : real) : (term127 y) = (term148 y).
Proof. exact (MK_COMB (@lem7121530) (@lem7121531 y)). Qed.
Lemma lem7121533 (y : real) : (term126 y) = (term148 y).
Proof. exact (TRANS (@lem7121430 y) (@lem7121532 y)). Qed.
Lemma lem7121534 (y : real) : (term148 y) = term3.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7121535 (y : real) : (term126 y) = term3.
Proof. exact (TRANS (@lem7121533 y) (@lem7121534 y)). Qed.
Lemma lem7121536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121537 (y : real) : (term149 y) = term150.
Proof. exact (MK_COMB (@lem7121536) (@lem7121535 y)). Qed.
Lemma lem7121538 (z : real) : (term153 z) = (term127 z).
Proof. exact (@lem1982715 term11 z). Qed.
Lemma lem7121540 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121541 : term23 = term33.
Proof. exact (@lem7121540 term17). Qed.
Lemma lem7121543 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121544 : term11 = term16.
Proof. exact (@lem7121543 term17). Qed.
Lemma lem7121545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121546 : term128 = term129.
Proof. exact (MK_COMB (@lem7121545) (@lem7121544)). Qed.
Lemma lem7121547 : term130 = term131.
Proof. exact (MK_COMB (@lem7121546) (@lem7121541)). Qed.
Lemma lem7121548 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121550 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121551 : term93 = term101.
Proof. exact (@lem7121550 (NUMERAL 0) term17). Qed.
Lemma lem7121552 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121553 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121554 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121553 h1) (fun h1 : term101 = True => @lem7121552)). Qed.
Lemma lem7121555 : term101 = True.
Proof. exact (EQ_MP (@lem7121554) (@lem7121552)). Qed.
Lemma lem7121556 : term93 = True.
Proof. exact (TRANS (@lem7121551) (@lem7121555)). Qed.
Lemma lem7121557 : True = term93.
Proof. exact (SYM (@lem7121556)). Qed.
Lemma lem7121558 : term93.
Proof. exact (EQ_MP (@lem7121557) (@lem0)). Qed.
Lemma lem7121559 : term133.
Proof. exact (@lem7121548 (@lem7121558)). Qed.
Lemma lem7121561 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121562 : term93 = term101.
Proof. exact (@lem7121561 (NUMERAL 0) term17). Qed.
Lemma lem7121563 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121564 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121565 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121564 h1) (fun h1 : term101 = True => @lem7121563)). Qed.
Lemma lem7121566 : term101 = True.
Proof. exact (EQ_MP (@lem7121565) (@lem7121563)). Qed.
Lemma lem7121567 : term93 = True.
Proof. exact (TRANS (@lem7121562) (@lem7121566)). Qed.
Lemma lem7121568 : True = term93.
Proof. exact (SYM (@lem7121567)). Qed.
Lemma lem7121569 : term93.
Proof. exact (EQ_MP (@lem7121568) (@lem0)). Qed.
Lemma lem7121570 : term134.
Proof. exact (@lem7121559 (@lem7121569)). Qed.
Lemma lem7121572 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121573 : term93 = term101.
Proof. exact (@lem7121572 (NUMERAL 0) term17). Qed.
Lemma lem7121574 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121575 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121576 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121575 h1) (fun h1 : term101 = True => @lem7121574)). Qed.
Lemma lem7121577 : term101 = True.
Proof. exact (EQ_MP (@lem7121576) (@lem7121574)). Qed.
Lemma lem7121578 : term93 = True.
Proof. exact (TRANS (@lem7121573) (@lem7121577)). Qed.
Lemma lem7121579 : True = term93.
Proof. exact (SYM (@lem7121578)). Qed.
Lemma lem7121580 : term93.
Proof. exact (EQ_MP (@lem7121579) (@lem0)). Qed.
Lemma lem7121581 : term135.
Proof. exact (@lem7121570 (@lem7121580)). Qed.
Lemma lem7121583 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121584 : term26 = term27.
Proof. exact (@lem7121583 term17 term17). Qed.
Lemma lem7121585 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121586 : term29 = term17.
Proof. exact (EQ_MP (@lem7121585) (@lem940073)). Qed.
Lemma lem7121587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121588 : term27 = term23.
Proof. exact (MK_COMB (@lem7121587) (@lem7121586)). Qed.
Lemma lem7121589 : term26 = term23.
Proof. exact (TRANS (@lem7121584) (@lem7121588)). Qed.
Lemma lem7121591 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121592 : term138 = term139.
Proof. exact (@lem7121591 term17 term17). Qed.
Lemma lem7121593 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121594 : term29 = term17.
Proof. exact (EQ_MP (@lem7121593) (@lem940073)). Qed.
Lemma lem7121595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121596 : term27 = term23.
Proof. exact (MK_COMB (@lem7121595) (@lem7121594)). Qed.
Lemma lem7121597 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121598 : term139 = term11.
Proof. exact (MK_COMB (@lem7121597) (@lem7121596)). Qed.
Lemma lem7121599 : term138 = term11.
Proof. exact (TRANS (@lem7121592) (@lem7121598)). Qed.
Lemma lem7121600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121601 : term140 = term128.
Proof. exact (MK_COMB (@lem7121600) (@lem7121599)). Qed.
Lemma lem7121602 : term141 = term130.
Proof. exact (MK_COMB (@lem7121601) (@lem7121589)). Qed.
Lemma lem7121604 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121605 : term130 = term3.
Proof. exact (@lem7121604 term17). Qed.
Lemma lem7121606 : term141 = term3.
Proof. exact (TRANS (@lem7121602) (@lem7121605)). Qed.
Lemma lem7121607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121608 : term143 = term144.
Proof. exact (MK_COMB (@lem7121607) (@lem7121606)). Qed.
Lemma lem7121609 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121610 : term145 = term106.
Proof. exact (MK_COMB (@lem7121608) (@lem7121609)). Qed.
Lemma lem7121612 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121613 : term106 = term3.
Proof. exact (@lem7121612 term17). Qed.
Lemma lem7121614 : term145 = term3.
Proof. exact (TRANS (@lem7121610) (@lem7121613)). Qed.
Lemma lem7121616 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121617 : term26 = term27.
Proof. exact (@lem7121616 term17 term17). Qed.
Lemma lem7121618 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121619 : term29 = term17.
Proof. exact (EQ_MP (@lem7121618) (@lem940073)). Qed.
Lemma lem7121620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121621 : term27 = term23.
Proof. exact (MK_COMB (@lem7121620) (@lem7121619)). Qed.
Lemma lem7121622 : term26 = term23.
Proof. exact (TRANS (@lem7121617) (@lem7121621)). Qed.
Lemma lem7121623 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7121624 : term146 = term106.
Proof. exact (MK_COMB (@lem7121623) (@lem7121622)). Qed.
Lemma lem7121626 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121627 : term106 = term3.
Proof. exact (@lem7121626 term17). Qed.
Lemma lem7121628 : term146 = term3.
Proof. exact (TRANS (@lem7121624) (@lem7121627)). Qed.
Lemma lem7121629 : term3 = term146.
Proof. exact (SYM (@lem7121628)). Qed.
Lemma lem7121630 : term145 = term146.
Proof. exact (TRANS (@lem7121614) (@lem7121629)). Qed.
Lemma lem7121631 : term131 = term95.
Proof. exact (@lem7121581 (@lem7121630)). Qed.
Lemma lem7121632 : term130 = term95.
Proof. exact (TRANS (@lem7121547) (@lem7121631)). Qed.
Lemma lem7121634 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7121635 : term95 = term3.
Proof. exact (@lem7121634 term3). Qed.
Lemma lem7121636 : term130 = term3.
Proof. exact (TRANS (@lem7121632) (@lem7121635)). Qed.
Lemma lem7121637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121638 : term147 = term144.
Proof. exact (MK_COMB (@lem7121637) (@lem7121636)). Qed.
Lemma lem7121639 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7121640 (z : real) : (term127 z) = (term148 z).
Proof. exact (MK_COMB (@lem7121638) (@lem7121639 z)). Qed.
Lemma lem7121641 (z : real) : (term153 z) = (term148 z).
Proof. exact (TRANS (@lem7121538 z) (@lem7121640 z)). Qed.
Lemma lem7121642 (z : real) : (term148 z) = term3.
Proof. exact (@lem1982719 z). Qed.
Lemma lem7121643 (z : real) : (term153 z) = term3.
Proof. exact (TRANS (@lem7121641 z) (@lem7121642 z)). Qed.
Lemma lem7121644 (y : real) (z : real) : (term152 y z) = term154.
Proof. exact (MK_COMB (@lem7121537 y) (@lem7121643 z)). Qed.
Lemma lem7121645 (y : real) (z : real) : (term151 y z) = term154.
Proof. exact (TRANS (@lem7121429 y z) (@lem7121644 y z)). Qed.
Lemma lem7121646 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7121647 (y : real) (z : real) : (term151 y z) = term3.
Proof. exact (TRANS (@lem7121645 y z) (@lem7121646)). Qed.
Lemma lem7121648 (x : real) (y : real) (z : real) : (term125 x y z) = term154.
Proof. exact (MK_COMB (@lem7121428 x) (@lem7121647 y z)). Qed.
Lemma lem7121649 (x : real) (y : real) (z : real) : (term124 x y z) = term154.
Proof. exact (TRANS (@lem7121320 x y z) (@lem7121648 x y z)). Qed.
Lemma lem7121650 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7121651 (x : real) (y : real) (z : real) : (term124 x y z) = term3.
Proof. exact (TRANS (@lem7121649 x y z) (@lem7121650)). Qed.
Lemma lem7121652 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7121653 (x : real) (y : real) (z : real) : (term155 x y z) = term156.
Proof. exact (MK_COMB (@lem7121652) (@lem7121651 x y z)). Qed.
Lemma lem7121654 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121655 (x : real) (y : real) (z : real) : (term123 x y z) = term157.
Proof. exact (MK_COMB (@lem7121653 x y z) (@lem7121654)). Qed.
Lemma lem7121656 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term157.
Proof. exact (EQ_MP (@lem7121655 x y z) (@lem7121319 x y z h1)). Qed.
Lemma lem7121658 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7121659 : term157 = term158.
Proof. exact (@lem7121658 term3 term3). Qed.
Lemma lem7121661 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121662 : term3 = term95.
Proof. exact (@lem7121661 (NUMERAL 0)). Qed.
Lemma lem7121664 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121665 : term3 = term95.
Proof. exact (@lem7121664 (NUMERAL 0)). Qed.
Lemma lem7121666 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121667 : term96 = term97.
Proof. exact (MK_COMB (@lem7121666) (@lem7121665)). Qed.
Lemma lem7121668 : term158 = term159.
Proof. exact (MK_COMB (@lem7121667) (@lem7121662)). Qed.
Lemma lem7121669 : term160.
Proof. exact (@lem1980255 term3 term23 term3 term23). Qed.
Lemma lem7121671 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121672 : term93 = term101.
Proof. exact (@lem7121671 (NUMERAL 0) term17). Qed.
Lemma lem7121673 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121674 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121675 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121674 h1) (fun h1 : term101 = True => @lem7121673)). Qed.
Lemma lem7121676 : term101 = True.
Proof. exact (EQ_MP (@lem7121675) (@lem7121673)). Qed.
Lemma lem7121677 : term93 = True.
Proof. exact (TRANS (@lem7121672) (@lem7121676)). Qed.
Lemma lem7121678 : True = term93.
Proof. exact (SYM (@lem7121677)). Qed.
Lemma lem7121679 : term93.
Proof. exact (EQ_MP (@lem7121678) (@lem0)). Qed.
Lemma lem7121680 : term161.
Proof. exact (@lem7121669 (@lem7121679)). Qed.
Lemma lem7121682 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121683 : term93 = term101.
Proof. exact (@lem7121682 (NUMERAL 0) term17). Qed.
Lemma lem7121684 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121685 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121686 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121685 h1) (fun h1 : term101 = True => @lem7121684)). Qed.
Lemma lem7121687 : term101 = True.
Proof. exact (EQ_MP (@lem7121686) (@lem7121684)). Qed.
Lemma lem7121688 : term93 = True.
Proof. exact (TRANS (@lem7121683) (@lem7121687)). Qed.
Lemma lem7121689 : True = term93.
Proof. exact (SYM (@lem7121688)). Qed.
Lemma lem7121690 : term93.
Proof. exact (EQ_MP (@lem7121689) (@lem0)). Qed.
Lemma lem7121691 : term159 = term162.
Proof. exact (@lem7121680 (@lem7121690)). Qed.
Lemma lem7121693 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121694 : term106 = term3.
Proof. exact (@lem7121693 term17). Qed.
Lemma lem7121696 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121697 : term106 = term3.
Proof. exact (@lem7121696 term17). Qed.
Lemma lem7121698 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121699 : term107 = term96.
Proof. exact (MK_COMB (@lem7121698) (@lem7121697)). Qed.
Lemma lem7121700 : term162 = term158.
Proof. exact (MK_COMB (@lem7121699) (@lem7121694)). Qed.
Lemma lem7121702 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121703 : term158 = term163.
Proof. exact (@lem7121702 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7121704 : term163 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7121705 : term158 = False.
Proof. exact (TRANS (@lem7121703) (@lem7121704)). Qed.
Lemma lem7121706 : term162 = False.
Proof. exact (TRANS (@lem7121700) (@lem7121705)). Qed.
Lemma lem7121707 : term159 = False.
Proof. exact (TRANS (@lem7121691) (@lem7121706)). Qed.
Lemma lem7121708 : term158 = False.
Proof. exact (TRANS (@lem7121668) (@lem7121707)). Qed.
Lemma lem7121709 : term157 = False.
Proof. exact (TRANS (@lem7121659) (@lem7121708)). Qed.
Lemma lem7121710 (x : real) (y : real) (z : real) (h1 : term180 x y z) : False.
Proof. exact (EQ_MP (@lem7121709) (@lem7121656 x y z h1)). Qed.
Lemma lem7121711 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term181 x y z.
Proof. exact (h1). Qed.
Lemma lem7121712 (x : real) (y : real) (z : real) (h1 : term181 x y z) : (term39 x y z) = term3.
Proof. exact (proj2 (@lem7121711 x y z h1)). Qed.
Lemma lem7121713 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term58 x y z.
Proof. exact (proj1 (@lem7121711 x y z h1)). Qed.
Lemma lem7121715 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7121716 : term92 = term93.
Proof. exact (@lem7121715 term3 term23). Qed.
Lemma lem7121718 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121719 : term23 = term33.
Proof. exact (@lem7121718 term17). Qed.
Lemma lem7121721 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121722 : term3 = term95.
Proof. exact (@lem7121721 (NUMERAL 0)). Qed.
Lemma lem7121723 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121724 : term96 = term97.
Proof. exact (MK_COMB (@lem7121723) (@lem7121722)). Qed.
Lemma lem7121725 : term93 = term98.
Proof. exact (MK_COMB (@lem7121724) (@lem7121719)). Qed.
Lemma lem7121726 : term99.
Proof. exact (@lem1980255 term3 term23 term23 term23). Qed.
Lemma lem7121728 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121729 : term93 = term101.
Proof. exact (@lem7121728 (NUMERAL 0) term17). Qed.
Lemma lem7121730 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121731 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121732 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121731 h1) (fun h1 : term101 = True => @lem7121730)). Qed.
Lemma lem7121733 : term101 = True.
Proof. exact (EQ_MP (@lem7121732) (@lem7121730)). Qed.
Lemma lem7121734 : term93 = True.
Proof. exact (TRANS (@lem7121729) (@lem7121733)). Qed.
Lemma lem7121735 : True = term93.
Proof. exact (SYM (@lem7121734)). Qed.
Lemma lem7121736 : term93.
Proof. exact (EQ_MP (@lem7121735) (@lem0)). Qed.
Lemma lem7121737 : term103.
Proof. exact (@lem7121726 (@lem7121736)). Qed.
Lemma lem7121739 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121740 : term93 = term101.
Proof. exact (@lem7121739 (NUMERAL 0) term17). Qed.
Lemma lem7121741 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121742 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121743 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121742 h1) (fun h1 : term101 = True => @lem7121741)). Qed.
Lemma lem7121744 : term101 = True.
Proof. exact (EQ_MP (@lem7121743) (@lem7121741)). Qed.
Lemma lem7121745 : term93 = True.
Proof. exact (TRANS (@lem7121740) (@lem7121744)). Qed.
Lemma lem7121746 : True = term93.
Proof. exact (SYM (@lem7121745)). Qed.
Lemma lem7121747 : term93.
Proof. exact (EQ_MP (@lem7121746) (@lem0)). Qed.
Lemma lem7121748 : term98 = term104.
Proof. exact (@lem7121737 (@lem7121747)). Qed.
Lemma lem7121750 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121751 : term26 = term27.
Proof. exact (@lem7121750 term17 term17). Qed.
Lemma lem7121752 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121753 : term29 = term17.
Proof. exact (EQ_MP (@lem7121752) (@lem940073)). Qed.
Lemma lem7121754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121755 : term27 = term23.
Proof. exact (MK_COMB (@lem7121754) (@lem7121753)). Qed.
Lemma lem7121756 : term26 = term23.
Proof. exact (TRANS (@lem7121751) (@lem7121755)). Qed.
Lemma lem7121758 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121759 : term106 = term3.
Proof. exact (@lem7121758 term17). Qed.
Lemma lem7121760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7121761 : term107 = term96.
Proof. exact (MK_COMB (@lem7121760) (@lem7121759)). Qed.
Lemma lem7121762 : term104 = term93.
Proof. exact (MK_COMB (@lem7121761) (@lem7121756)). Qed.
Lemma lem7121764 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121765 : term93 = term101.
Proof. exact (@lem7121764 (NUMERAL 0) term17). Qed.
Lemma lem7121766 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121767 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121768 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121767 h1) (fun h1 : term101 = True => @lem7121766)). Qed.
Lemma lem7121769 : term101 = True.
Proof. exact (EQ_MP (@lem7121768) (@lem7121766)). Qed.
Lemma lem7121770 : term93 = True.
Proof. exact (TRANS (@lem7121765) (@lem7121769)). Qed.
Lemma lem7121771 : term104 = True.
Proof. exact (TRANS (@lem7121762) (@lem7121770)). Qed.
Lemma lem7121772 : term98 = True.
Proof. exact (TRANS (@lem7121748) (@lem7121771)). Qed.
Lemma lem7121773 : term93 = True.
Proof. exact (TRANS (@lem7121725) (@lem7121772)). Qed.
Lemma lem7121774 : term92 = True.
Proof. exact (TRANS (@lem7121716) (@lem7121773)). Qed.
Lemma lem7121775 : True = term92.
Proof. exact (SYM (@lem7121774)). Qed.
Lemma lem7121776 : term92.
Proof. exact (EQ_MP (@lem7121775) (@lem0)). Qed.
Lemma lem7121777 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term165 x y z.
Proof. exact (conj (@lem7121776) (@lem7121713 x y z h1)). Qed.
Lemma lem7121779 (x : real) (y : real) : term109 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7121780 (x : real) (y : real) (z : real) : term166 x y z.
Proof. exact (@lem7121779 term23 (term53 x y z)). Qed.
Lemma lem7121781 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term167 x y z.
Proof. exact (@lem7121780 x y z (@lem7121777 x y z h1)). Qed.
Lemma lem7121782 (x : real) (y : real) (z : real) : (term168 x y z) = (term53 x y z).
Proof. exact (@lem1982733 (term53 x y z)). Qed.
Lemma lem7121783 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7121784 (x : real) (y : real) (z : real) : (term169 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem7121783) (@lem7121782 x y z)). Qed.
Lemma lem7121785 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121786 (x : real) (y : real) (z : real) : (term167 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem7121784 x y z) (@lem7121785)). Qed.
Lemma lem7121787 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term58 x y z.
Proof. exact (EQ_MP (@lem7121786 x y z) (@lem7121781 x y z h1)). Qed.
Lemma lem7121789 (y : real) : term114 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7121790 (x : real) (y : real) (z : real) : term115 x y z.
Proof. exact (@lem7121789 (term39 x y z)). Qed.
Lemma lem7121791 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term116 x y z.
Proof. exact (@lem7121790 x y z (@lem7121712 x y z h1)). Qed.
Lemma lem7121792 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term170 x y z.
Proof. exact (@lem7121791 x y z h1 term23). Qed.
Lemma lem7121793 (x : real) (y : real) (z : real) : (term170 x y z) = ((term112 x y z) = term3).
Proof. exact (eq_refl (term170 x y z)). Qed.
Lemma lem7121794 (x : real) (y : real) (z : real) (h1 : term181 x y z) : (term112 x y z) = term3.
Proof. exact (EQ_MP (@lem7121793 x y z) (@lem7121792 x y z h1)). Qed.
Lemma lem7121795 (x : real) (y : real) (z : real) : (term112 x y z) = (term39 x y z).
Proof. exact (@lem1982733 (term39 x y z)). Qed.
Lemma lem7121796 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7121797 (x : real) (y : real) (z : real) : (term171 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem7121796) (@lem7121795 x y z)). Qed.
Lemma lem7121798 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7121799 (x : real) (y : real) (z : real) : ((term112 x y z) = term3) = ((term39 x y z) = term3).
Proof. exact (MK_COMB (@lem7121797 x y z) (@lem7121798)). Qed.
Lemma lem7121800 (x : real) (y : real) (z : real) (h1 : term181 x y z) : (term39 x y z) = term3.
Proof. exact (EQ_MP (@lem7121799 x y z) (@lem7121794 x y z h1)). Qed.
Lemma lem7121801 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term164 x y z.
Proof. exact (conj (@lem7121800 x y z h1) (@lem7121787 x y z h1)). Qed.
Lemma lem7121803 (x : real) (y : real) : term121 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7121804 (x : real) (y : real) (z : real) : term172 x y z.
Proof. exact (@lem7121803 (term39 x y z) (term53 x y z)). Qed.
Lemma lem7121805 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term173 x y z.
Proof. exact (@lem7121804 x y z (@lem7121801 x y z h1)). Qed.
Lemma lem7121806 (x : real) (y : real) (z : real) : (term174 x y z) = (term175 x y z).
Proof. exact (@lem1982753 x (term6 x) (term4 y z) (term5 y z)). Qed.
Lemma lem7121807 (x : real) : (term153 x) = (term127 x).
Proof. exact (@lem1982715 term11 x). Qed.
Lemma lem7121809 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121810 : term23 = term33.
Proof. exact (@lem7121809 term17). Qed.
Lemma lem7121812 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121813 : term11 = term16.
Proof. exact (@lem7121812 term17). Qed.
Lemma lem7121814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121815 : term128 = term129.
Proof. exact (MK_COMB (@lem7121814) (@lem7121813)). Qed.
Lemma lem7121816 : term130 = term131.
Proof. exact (MK_COMB (@lem7121815) (@lem7121810)). Qed.
Lemma lem7121817 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121819 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121820 : term93 = term101.
Proof. exact (@lem7121819 (NUMERAL 0) term17). Qed.
Lemma lem7121821 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121822 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121823 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121822 h1) (fun h1 : term101 = True => @lem7121821)). Qed.
Lemma lem7121824 : term101 = True.
Proof. exact (EQ_MP (@lem7121823) (@lem7121821)). Qed.
Lemma lem7121825 : term93 = True.
Proof. exact (TRANS (@lem7121820) (@lem7121824)). Qed.
Lemma lem7121826 : True = term93.
Proof. exact (SYM (@lem7121825)). Qed.
Lemma lem7121827 : term93.
Proof. exact (EQ_MP (@lem7121826) (@lem0)). Qed.
Lemma lem7121828 : term133.
Proof. exact (@lem7121817 (@lem7121827)). Qed.
Lemma lem7121830 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121831 : term93 = term101.
Proof. exact (@lem7121830 (NUMERAL 0) term17). Qed.
Lemma lem7121832 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121833 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121834 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121833 h1) (fun h1 : term101 = True => @lem7121832)). Qed.
Lemma lem7121835 : term101 = True.
Proof. exact (EQ_MP (@lem7121834) (@lem7121832)). Qed.
Lemma lem7121836 : term93 = True.
Proof. exact (TRANS (@lem7121831) (@lem7121835)). Qed.
Lemma lem7121837 : True = term93.
Proof. exact (SYM (@lem7121836)). Qed.
Lemma lem7121838 : term93.
Proof. exact (EQ_MP (@lem7121837) (@lem0)). Qed.
Lemma lem7121839 : term134.
Proof. exact (@lem7121828 (@lem7121838)). Qed.
Lemma lem7121841 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121842 : term93 = term101.
Proof. exact (@lem7121841 (NUMERAL 0) term17). Qed.
Lemma lem7121843 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121844 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121845 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121844 h1) (fun h1 : term101 = True => @lem7121843)). Qed.
Lemma lem7121846 : term101 = True.
Proof. exact (EQ_MP (@lem7121845) (@lem7121843)). Qed.
Lemma lem7121847 : term93 = True.
Proof. exact (TRANS (@lem7121842) (@lem7121846)). Qed.
Lemma lem7121848 : True = term93.
Proof. exact (SYM (@lem7121847)). Qed.
Lemma lem7121849 : term93.
Proof. exact (EQ_MP (@lem7121848) (@lem0)). Qed.
Lemma lem7121850 : term135.
Proof. exact (@lem7121839 (@lem7121849)). Qed.
Lemma lem7121852 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121853 : term26 = term27.
Proof. exact (@lem7121852 term17 term17). Qed.
Lemma lem7121854 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121855 : term29 = term17.
Proof. exact (EQ_MP (@lem7121854) (@lem940073)). Qed.
Lemma lem7121856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121857 : term27 = term23.
Proof. exact (MK_COMB (@lem7121856) (@lem7121855)). Qed.
Lemma lem7121858 : term26 = term23.
Proof. exact (TRANS (@lem7121853) (@lem7121857)). Qed.
Lemma lem7121860 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121861 : term138 = term139.
Proof. exact (@lem7121860 term17 term17). Qed.
Lemma lem7121862 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121863 : term29 = term17.
Proof. exact (EQ_MP (@lem7121862) (@lem940073)). Qed.
Lemma lem7121864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121865 : term27 = term23.
Proof. exact (MK_COMB (@lem7121864) (@lem7121863)). Qed.
Lemma lem7121866 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121867 : term139 = term11.
Proof. exact (MK_COMB (@lem7121866) (@lem7121865)). Qed.
Lemma lem7121868 : term138 = term11.
Proof. exact (TRANS (@lem7121861) (@lem7121867)). Qed.
Lemma lem7121869 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121870 : term140 = term128.
Proof. exact (MK_COMB (@lem7121869) (@lem7121868)). Qed.
Lemma lem7121871 : term141 = term130.
Proof. exact (MK_COMB (@lem7121870) (@lem7121858)). Qed.
Lemma lem7121873 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121874 : term130 = term3.
Proof. exact (@lem7121873 term17). Qed.
Lemma lem7121875 : term141 = term3.
Proof. exact (TRANS (@lem7121871) (@lem7121874)). Qed.
Lemma lem7121876 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121877 : term143 = term144.
Proof. exact (MK_COMB (@lem7121876) (@lem7121875)). Qed.
Lemma lem7121878 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121879 : term145 = term106.
Proof. exact (MK_COMB (@lem7121877) (@lem7121878)). Qed.
Lemma lem7121881 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121882 : term106 = term3.
Proof. exact (@lem7121881 term17). Qed.
Lemma lem7121883 : term145 = term3.
Proof. exact (TRANS (@lem7121879) (@lem7121882)). Qed.
Lemma lem7121885 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121886 : term26 = term27.
Proof. exact (@lem7121885 term17 term17). Qed.
Lemma lem7121887 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121888 : term29 = term17.
Proof. exact (EQ_MP (@lem7121887) (@lem940073)). Qed.
Lemma lem7121889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121890 : term27 = term23.
Proof. exact (MK_COMB (@lem7121889) (@lem7121888)). Qed.
Lemma lem7121891 : term26 = term23.
Proof. exact (TRANS (@lem7121886) (@lem7121890)). Qed.
Lemma lem7121892 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7121893 : term146 = term106.
Proof. exact (MK_COMB (@lem7121892) (@lem7121891)). Qed.
Lemma lem7121895 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121896 : term106 = term3.
Proof. exact (@lem7121895 term17). Qed.
Lemma lem7121897 : term146 = term3.
Proof. exact (TRANS (@lem7121893) (@lem7121896)). Qed.
Lemma lem7121898 : term3 = term146.
Proof. exact (SYM (@lem7121897)). Qed.
Lemma lem7121899 : term145 = term146.
Proof. exact (TRANS (@lem7121883) (@lem7121898)). Qed.
Lemma lem7121900 : term131 = term95.
Proof. exact (@lem7121850 (@lem7121899)). Qed.
Lemma lem7121901 : term130 = term95.
Proof. exact (TRANS (@lem7121816) (@lem7121900)). Qed.
Lemma lem7121903 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7121904 : term95 = term3.
Proof. exact (@lem7121903 term3). Qed.
Lemma lem7121905 : term130 = term3.
Proof. exact (TRANS (@lem7121901) (@lem7121904)). Qed.
Lemma lem7121906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121907 : term147 = term144.
Proof. exact (MK_COMB (@lem7121906) (@lem7121905)). Qed.
Lemma lem7121908 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7121909 (x : real) : (term127 x) = (term148 x).
Proof. exact (MK_COMB (@lem7121907) (@lem7121908 x)). Qed.
Lemma lem7121910 (x : real) : (term153 x) = (term148 x).
Proof. exact (TRANS (@lem7121807 x) (@lem7121909 x)). Qed.
Lemma lem7121911 (x : real) : (term148 x) = term3.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7121912 (x : real) : (term153 x) = term3.
Proof. exact (TRANS (@lem7121910 x) (@lem7121911 x)). Qed.
Lemma lem7121913 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121914 (x : real) : (term176 x) = term150.
Proof. exact (MK_COMB (@lem7121913) (@lem7121912 x)). Qed.
Lemma lem7121915 (y : real) (z : real) : (term177 y z) = (term178 y z).
Proof. exact (@lem1982753 y (term6 y) (term6 z) z). Qed.
Lemma lem7121916 (y : real) : (term153 y) = (term127 y).
Proof. exact (@lem1982715 term11 y). Qed.
Lemma lem7121918 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7121919 : term23 = term33.
Proof. exact (@lem7121918 term17). Qed.
Lemma lem7121921 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7121922 : term11 = term16.
Proof. exact (@lem7121921 term17). Qed.
Lemma lem7121923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121924 : term128 = term129.
Proof. exact (MK_COMB (@lem7121923) (@lem7121922)). Qed.
Lemma lem7121925 : term130 = term131.
Proof. exact (MK_COMB (@lem7121924) (@lem7121919)). Qed.
Lemma lem7121926 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7121928 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121929 : term93 = term101.
Proof. exact (@lem7121928 (NUMERAL 0) term17). Qed.
Lemma lem7121930 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121931 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121932 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121931 h1) (fun h1 : term101 = True => @lem7121930)). Qed.
Lemma lem7121933 : term101 = True.
Proof. exact (EQ_MP (@lem7121932) (@lem7121930)). Qed.
Lemma lem7121934 : term93 = True.
Proof. exact (TRANS (@lem7121929) (@lem7121933)). Qed.
Lemma lem7121935 : True = term93.
Proof. exact (SYM (@lem7121934)). Qed.
Lemma lem7121936 : term93.
Proof. exact (EQ_MP (@lem7121935) (@lem0)). Qed.
Lemma lem7121937 : term133.
Proof. exact (@lem7121926 (@lem7121936)). Qed.
Lemma lem7121939 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121940 : term93 = term101.
Proof. exact (@lem7121939 (NUMERAL 0) term17). Qed.
Lemma lem7121941 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121942 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121943 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121942 h1) (fun h1 : term101 = True => @lem7121941)). Qed.
Lemma lem7121944 : term101 = True.
Proof. exact (EQ_MP (@lem7121943) (@lem7121941)). Qed.
Lemma lem7121945 : term93 = True.
Proof. exact (TRANS (@lem7121940) (@lem7121944)). Qed.
Lemma lem7121946 : True = term93.
Proof. exact (SYM (@lem7121945)). Qed.
Lemma lem7121947 : term93.
Proof. exact (EQ_MP (@lem7121946) (@lem0)). Qed.
Lemma lem7121948 : term134.
Proof. exact (@lem7121937 (@lem7121947)). Qed.
Lemma lem7121950 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7121951 : term93 = term101.
Proof. exact (@lem7121950 (NUMERAL 0) term17). Qed.
Lemma lem7121952 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7121953 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7121954 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7121953 h1) (fun h1 : term101 = True => @lem7121952)). Qed.
Lemma lem7121955 : term101 = True.
Proof. exact (EQ_MP (@lem7121954) (@lem7121952)). Qed.
Lemma lem7121956 : term93 = True.
Proof. exact (TRANS (@lem7121951) (@lem7121955)). Qed.
Lemma lem7121957 : True = term93.
Proof. exact (SYM (@lem7121956)). Qed.
Lemma lem7121958 : term93.
Proof. exact (EQ_MP (@lem7121957) (@lem0)). Qed.
Lemma lem7121959 : term135.
Proof. exact (@lem7121948 (@lem7121958)). Qed.
Lemma lem7121961 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121962 : term26 = term27.
Proof. exact (@lem7121961 term17 term17). Qed.
Lemma lem7121963 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121964 : term29 = term17.
Proof. exact (EQ_MP (@lem7121963) (@lem940073)). Qed.
Lemma lem7121965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121966 : term27 = term23.
Proof. exact (MK_COMB (@lem7121965) (@lem7121964)). Qed.
Lemma lem7121967 : term26 = term23.
Proof. exact (TRANS (@lem7121962) (@lem7121966)). Qed.
Lemma lem7121969 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7121970 : term138 = term139.
Proof. exact (@lem7121969 term17 term17). Qed.
Lemma lem7121971 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121972 : term29 = term17.
Proof. exact (EQ_MP (@lem7121971) (@lem940073)). Qed.
Lemma lem7121973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121974 : term27 = term23.
Proof. exact (MK_COMB (@lem7121973) (@lem7121972)). Qed.
Lemma lem7121975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7121976 : term139 = term11.
Proof. exact (MK_COMB (@lem7121975) (@lem7121974)). Qed.
Lemma lem7121977 : term138 = term11.
Proof. exact (TRANS (@lem7121970) (@lem7121976)). Qed.
Lemma lem7121978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7121979 : term140 = term128.
Proof. exact (MK_COMB (@lem7121978) (@lem7121977)). Qed.
Lemma lem7121980 : term141 = term130.
Proof. exact (MK_COMB (@lem7121979) (@lem7121967)). Qed.
Lemma lem7121982 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7121983 : term130 = term3.
Proof. exact (@lem7121982 term17). Qed.
Lemma lem7121984 : term141 = term3.
Proof. exact (TRANS (@lem7121980) (@lem7121983)). Qed.
Lemma lem7121985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7121986 : term143 = term144.
Proof. exact (MK_COMB (@lem7121985) (@lem7121984)). Qed.
Lemma lem7121987 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7121988 : term145 = term106.
Proof. exact (MK_COMB (@lem7121986) (@lem7121987)). Qed.
Lemma lem7121990 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7121991 : term106 = term3.
Proof. exact (@lem7121990 term17). Qed.
Lemma lem7121992 : term145 = term3.
Proof. exact (TRANS (@lem7121988) (@lem7121991)). Qed.
Lemma lem7121994 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7121995 : term26 = term27.
Proof. exact (@lem7121994 term17 term17). Qed.
Lemma lem7121996 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7121997 : term29 = term17.
Proof. exact (EQ_MP (@lem7121996) (@lem940073)). Qed.
Lemma lem7121998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7121999 : term27 = term23.
Proof. exact (MK_COMB (@lem7121998) (@lem7121997)). Qed.
Lemma lem7122000 : term26 = term23.
Proof. exact (TRANS (@lem7121995) (@lem7121999)). Qed.
Lemma lem7122001 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7122002 : term146 = term106.
Proof. exact (MK_COMB (@lem7122001) (@lem7122000)). Qed.
Lemma lem7122004 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7122005 : term106 = term3.
Proof. exact (@lem7122004 term17). Qed.
Lemma lem7122006 : term146 = term3.
Proof. exact (TRANS (@lem7122002) (@lem7122005)). Qed.
Lemma lem7122007 : term3 = term146.
Proof. exact (SYM (@lem7122006)). Qed.
Lemma lem7122008 : term145 = term146.
Proof. exact (TRANS (@lem7121992) (@lem7122007)). Qed.
Lemma lem7122009 : term131 = term95.
Proof. exact (@lem7121959 (@lem7122008)). Qed.
Lemma lem7122010 : term130 = term95.
Proof. exact (TRANS (@lem7121925) (@lem7122009)). Qed.
Lemma lem7122012 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7122013 : term95 = term3.
Proof. exact (@lem7122012 term3). Qed.
Lemma lem7122014 : term130 = term3.
Proof. exact (TRANS (@lem7122010) (@lem7122013)). Qed.
Lemma lem7122015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7122016 : term147 = term144.
Proof. exact (MK_COMB (@lem7122015) (@lem7122014)). Qed.
Lemma lem7122017 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7122018 (y : real) : (term127 y) = (term148 y).
Proof. exact (MK_COMB (@lem7122016) (@lem7122017 y)). Qed.
Lemma lem7122019 (y : real) : (term153 y) = (term148 y).
Proof. exact (TRANS (@lem7121916 y) (@lem7122018 y)). Qed.
Lemma lem7122020 (y : real) : (term148 y) = term3.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7122021 (y : real) : (term153 y) = term3.
Proof. exact (TRANS (@lem7122019 y) (@lem7122020 y)). Qed.
Lemma lem7122022 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7122023 (y : real) : (term176 y) = term150.
Proof. exact (MK_COMB (@lem7122022) (@lem7122021 y)). Qed.
Lemma lem7122024 (z : real) : (term126 z) = (term127 z).
Proof. exact (@lem1982713 term11 z). Qed.
Lemma lem7122026 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7122027 : term23 = term33.
Proof. exact (@lem7122026 term17). Qed.
Lemma lem7122029 (x : nat) : (term14 x) = (term15 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7122030 : term11 = term16.
Proof. exact (@lem7122029 term17). Qed.
Lemma lem7122031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7122032 : term128 = term129.
Proof. exact (MK_COMB (@lem7122031) (@lem7122030)). Qed.
Lemma lem7122033 : term130 = term131.
Proof. exact (MK_COMB (@lem7122032) (@lem7122027)). Qed.
Lemma lem7122034 : term132.
Proof. exact (@lem1981473 term11 term23 term23 term23 term3 term23). Qed.
Lemma lem7122036 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122037 : term93 = term101.
Proof. exact (@lem7122036 (NUMERAL 0) term17). Qed.
Lemma lem7122038 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7122039 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7122040 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7122039 h1) (fun h1 : term101 = True => @lem7122038)). Qed.
Lemma lem7122041 : term101 = True.
Proof. exact (EQ_MP (@lem7122040) (@lem7122038)). Qed.
Lemma lem7122042 : term93 = True.
Proof. exact (TRANS (@lem7122037) (@lem7122041)). Qed.
Lemma lem7122043 : True = term93.
Proof. exact (SYM (@lem7122042)). Qed.
Lemma lem7122044 : term93.
Proof. exact (EQ_MP (@lem7122043) (@lem0)). Qed.
Lemma lem7122045 : term133.
Proof. exact (@lem7122034 (@lem7122044)). Qed.
Lemma lem7122047 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122048 : term93 = term101.
Proof. exact (@lem7122047 (NUMERAL 0) term17). Qed.
Lemma lem7122049 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7122050 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7122051 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7122050 h1) (fun h1 : term101 = True => @lem7122049)). Qed.
Lemma lem7122052 : term101 = True.
Proof. exact (EQ_MP (@lem7122051) (@lem7122049)). Qed.
Lemma lem7122053 : term93 = True.
Proof. exact (TRANS (@lem7122048) (@lem7122052)). Qed.
Lemma lem7122054 : True = term93.
Proof. exact (SYM (@lem7122053)). Qed.
Lemma lem7122055 : term93.
Proof. exact (EQ_MP (@lem7122054) (@lem0)). Qed.
Lemma lem7122056 : term134.
Proof. exact (@lem7122045 (@lem7122055)). Qed.
Lemma lem7122058 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122059 : term93 = term101.
Proof. exact (@lem7122058 (NUMERAL 0) term17). Qed.
Lemma lem7122060 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7122061 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7122062 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7122061 h1) (fun h1 : term101 = True => @lem7122060)). Qed.
Lemma lem7122063 : term101 = True.
Proof. exact (EQ_MP (@lem7122062) (@lem7122060)). Qed.
Lemma lem7122064 : term93 = True.
Proof. exact (TRANS (@lem7122059) (@lem7122063)). Qed.
Lemma lem7122065 : True = term93.
Proof. exact (SYM (@lem7122064)). Qed.
Lemma lem7122066 : term93.
Proof. exact (EQ_MP (@lem7122065) (@lem0)). Qed.
Lemma lem7122067 : term135.
Proof. exact (@lem7122056 (@lem7122066)). Qed.
Lemma lem7122069 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7122070 : term26 = term27.
Proof. exact (@lem7122069 term17 term17). Qed.
Lemma lem7122071 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7122072 : term29 = term17.
Proof. exact (EQ_MP (@lem7122071) (@lem940073)). Qed.
Lemma lem7122073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7122074 : term27 = term23.
Proof. exact (MK_COMB (@lem7122073) (@lem7122072)). Qed.
Lemma lem7122075 : term26 = term23.
Proof. exact (TRANS (@lem7122070) (@lem7122074)). Qed.
Lemma lem7122077 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7122078 : term138 = term139.
Proof. exact (@lem7122077 term17 term17). Qed.
Lemma lem7122079 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7122080 : term29 = term17.
Proof. exact (EQ_MP (@lem7122079) (@lem940073)). Qed.
Lemma lem7122081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7122082 : term27 = term23.
Proof. exact (MK_COMB (@lem7122081) (@lem7122080)). Qed.
Lemma lem7122083 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7122084 : term139 = term11.
Proof. exact (MK_COMB (@lem7122083) (@lem7122082)). Qed.
Lemma lem7122085 : term138 = term11.
Proof. exact (TRANS (@lem7122078) (@lem7122084)). Qed.
Lemma lem7122086 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7122087 : term140 = term128.
Proof. exact (MK_COMB (@lem7122086) (@lem7122085)). Qed.
Lemma lem7122088 : term141 = term130.
Proof. exact (MK_COMB (@lem7122087) (@lem7122075)). Qed.
Lemma lem7122090 (m : nat) : (term142 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7122091 : term130 = term3.
Proof. exact (@lem7122090 term17). Qed.
Lemma lem7122092 : term141 = term3.
Proof. exact (TRANS (@lem7122088) (@lem7122091)). Qed.
Lemma lem7122093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7122094 : term143 = term144.
Proof. exact (MK_COMB (@lem7122093) (@lem7122092)). Qed.
Lemma lem7122095 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7122096 : term145 = term106.
Proof. exact (MK_COMB (@lem7122094) (@lem7122095)). Qed.
Lemma lem7122098 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7122099 : term106 = term3.
Proof. exact (@lem7122098 term17). Qed.
Lemma lem7122100 : term145 = term3.
Proof. exact (TRANS (@lem7122096) (@lem7122099)). Qed.
Lemma lem7122102 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7122103 : term26 = term27.
Proof. exact (@lem7122102 term17 term17). Qed.
Lemma lem7122104 : (term28 = (BIT1 0)) = (term29 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7122105 : term29 = term17.
Proof. exact (EQ_MP (@lem7122104) (@lem940073)). Qed.
Lemma lem7122106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7122107 : term27 = term23.
Proof. exact (MK_COMB (@lem7122106) (@lem7122105)). Qed.
Lemma lem7122108 : term26 = term23.
Proof. exact (TRANS (@lem7122103) (@lem7122107)). Qed.
Lemma lem7122109 : term144 = term144.
Proof. exact (eq_refl term144). Qed.
Lemma lem7122110 : term146 = term106.
Proof. exact (MK_COMB (@lem7122109) (@lem7122108)). Qed.
Lemma lem7122112 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7122113 : term106 = term3.
Proof. exact (@lem7122112 term17). Qed.
Lemma lem7122114 : term146 = term3.
Proof. exact (TRANS (@lem7122110) (@lem7122113)). Qed.
Lemma lem7122115 : term3 = term146.
Proof. exact (SYM (@lem7122114)). Qed.
Lemma lem7122116 : term145 = term146.
Proof. exact (TRANS (@lem7122100) (@lem7122115)). Qed.
Lemma lem7122117 : term131 = term95.
Proof. exact (@lem7122067 (@lem7122116)). Qed.
Lemma lem7122118 : term130 = term95.
Proof. exact (TRANS (@lem7122033) (@lem7122117)). Qed.
Lemma lem7122120 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7122121 : term95 = term3.
Proof. exact (@lem7122120 term3). Qed.
Lemma lem7122122 : term130 = term3.
Proof. exact (TRANS (@lem7122118) (@lem7122121)). Qed.
Lemma lem7122123 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7122124 : term147 = term144.
Proof. exact (MK_COMB (@lem7122123) (@lem7122122)). Qed.
Lemma lem7122125 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7122126 (z : real) : (term127 z) = (term148 z).
Proof. exact (MK_COMB (@lem7122124) (@lem7122125 z)). Qed.
Lemma lem7122127 (z : real) : (term126 z) = (term148 z).
Proof. exact (TRANS (@lem7122024 z) (@lem7122126 z)). Qed.
Lemma lem7122128 (z : real) : (term148 z) = term3.
Proof. exact (@lem1982719 z). Qed.
Lemma lem7122129 (z : real) : (term126 z) = term3.
Proof. exact (TRANS (@lem7122127 z) (@lem7122128 z)). Qed.
Lemma lem7122130 (y : real) (z : real) : (term178 y z) = term154.
Proof. exact (MK_COMB (@lem7122023 y) (@lem7122129 z)). Qed.
Lemma lem7122131 (y : real) (z : real) : (term177 y z) = term154.
Proof. exact (TRANS (@lem7121915 y z) (@lem7122130 y z)). Qed.
Lemma lem7122132 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7122133 (y : real) (z : real) : (term177 y z) = term3.
Proof. exact (TRANS (@lem7122131 y z) (@lem7122132)). Qed.
Lemma lem7122134 (x : real) (y : real) (z : real) : (term175 x y z) = term154.
Proof. exact (MK_COMB (@lem7121914 x) (@lem7122133 y z)). Qed.
Lemma lem7122135 (x : real) (y : real) (z : real) : (term174 x y z) = term154.
Proof. exact (TRANS (@lem7121806 x y z) (@lem7122134 x y z)). Qed.
Lemma lem7122136 : term154 = term3.
Proof. exact (@lem1982721 term3). Qed.
Lemma lem7122137 (x : real) (y : real) (z : real) : (term174 x y z) = term3.
Proof. exact (TRANS (@lem7122135 x y z) (@lem7122136)). Qed.
Lemma lem7122138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7122139 (x : real) (y : real) (z : real) : (term179 x y z) = term156.
Proof. exact (MK_COMB (@lem7122138) (@lem7122137 x y z)). Qed.
Lemma lem7122140 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem7122141 (x : real) (y : real) (z : real) : (term173 x y z) = term157.
Proof. exact (MK_COMB (@lem7122139 x y z) (@lem7122140)). Qed.
Lemma lem7122142 (x : real) (y : real) (z : real) (h1 : term181 x y z) : term157.
Proof. exact (EQ_MP (@lem7122141 x y z) (@lem7121805 x y z h1)). Qed.
Lemma lem7122144 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7122145 : term157 = term158.
Proof. exact (@lem7122144 term3 term3). Qed.
Lemma lem7122147 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7122148 : term3 = term95.
Proof. exact (@lem7122147 (NUMERAL 0)). Qed.
Lemma lem7122150 (x : nat) : (real_of_num x) = (term94 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7122151 : term3 = term95.
Proof. exact (@lem7122150 (NUMERAL 0)). Qed.
Lemma lem7122152 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7122153 : term96 = term97.
Proof. exact (MK_COMB (@lem7122152) (@lem7122151)). Qed.
Lemma lem7122154 : term158 = term159.
Proof. exact (MK_COMB (@lem7122153) (@lem7122148)). Qed.
Lemma lem7122155 : term160.
Proof. exact (@lem1980255 term3 term23 term3 term23). Qed.
Lemma lem7122157 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122158 : term93 = term101.
Proof. exact (@lem7122157 (NUMERAL 0) term17). Qed.
Lemma lem7122159 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7122160 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7122161 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7122160 h1) (fun h1 : term101 = True => @lem7122159)). Qed.
Lemma lem7122162 : term101 = True.
Proof. exact (EQ_MP (@lem7122161) (@lem7122159)). Qed.
Lemma lem7122163 : term93 = True.
Proof. exact (TRANS (@lem7122158) (@lem7122162)). Qed.
Lemma lem7122164 : True = term93.
Proof. exact (SYM (@lem7122163)). Qed.
Lemma lem7122165 : term93.
Proof. exact (EQ_MP (@lem7122164) (@lem0)). Qed.
Lemma lem7122166 : term161.
Proof. exact (@lem7122155 (@lem7122165)). Qed.
Lemma lem7122168 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122169 : term93 = term101.
Proof. exact (@lem7122168 (NUMERAL 0) term17). Qed.
Lemma lem7122170 : term102 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7122171 (h1 : term102 = (BIT1 0)) : term101 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7122172 : (term102 = (BIT1 0)) = (term101 = True).
Proof. exact (prop_ext (fun h1 : term102 = (BIT1 0) => @lem7122171 h1) (fun h1 : term101 = True => @lem7122170)). Qed.
Lemma lem7122173 : term101 = True.
Proof. exact (EQ_MP (@lem7122172) (@lem7122170)). Qed.
Lemma lem7122174 : term93 = True.
Proof. exact (TRANS (@lem7122169) (@lem7122173)). Qed.
Lemma lem7122175 : True = term93.
Proof. exact (SYM (@lem7122174)). Qed.
Lemma lem7122176 : term93.
Proof. exact (EQ_MP (@lem7122175) (@lem0)). Qed.
Lemma lem7122177 : term159 = term162.
Proof. exact (@lem7122166 (@lem7122176)). Qed.
Lemma lem7122179 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7122180 : term106 = term3.
Proof. exact (@lem7122179 term17). Qed.
Lemma lem7122182 (x : nat) : (term105 x) = term3.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7122183 : term106 = term3.
Proof. exact (@lem7122182 term17). Qed.
Lemma lem7122184 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7122185 : term107 = term96.
Proof. exact (MK_COMB (@lem7122184) (@lem7122183)). Qed.
Lemma lem7122186 : term162 = term158.
Proof. exact (MK_COMB (@lem7122185) (@lem7122180)). Qed.
Lemma lem7122188 (m : nat) (n : nat) : (term100 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7122189 : term158 = term163.
Proof. exact (@lem7122188 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7122190 : term163 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7122191 : term158 = False.
Proof. exact (TRANS (@lem7122189) (@lem7122190)). Qed.
Lemma lem7122192 : term162 = False.
Proof. exact (TRANS (@lem7122186) (@lem7122191)). Qed.
Lemma lem7122193 : term159 = False.
Proof. exact (TRANS (@lem7122177) (@lem7122192)). Qed.
Lemma lem7122194 : term158 = False.
Proof. exact (TRANS (@lem7122154) (@lem7122193)). Qed.
Lemma lem7122195 : term157 = False.
Proof. exact (TRANS (@lem7122145) (@lem7122194)). Qed.
Lemma lem7122196 (x : real) (y : real) (z : real) (h1 : term181 x y z) : False.
Proof. exact (EQ_MP (@lem7122195) (@lem7122142 x y z h1)). Qed.
Lemma lem7122197 (x : real) (y : real) (z : real) (h1 : term87 x y z) : False.
Proof. exact (or_elim (@lem7121170 x y z h1) (fun h0 : term180 x y z => @lem7121710 x y z h0) (fun h0 : term181 x y z => @lem7122196 x y z h0)). Qed.
Lemma lem7122198 (x : real) (y : real) (z : real) (h1 : term90 x y z) : False.
Proof. exact (or_elim (@lem7120141 x y z h1) (fun h0 : term88 x y z => @lem7121169 x y z h0) (fun h0 : term87 x y z => @lem7122197 x y z h0)). Qed.
Lemma lem7122200 (x : real) (y : real) (z : real) (h1 : term90 x y z) : term90 x y z.
Proof. exact (h1). Qed.
Lemma lem7122201 (x : real) (y : real) (z : real) (h1 : term90 x y z) : (term90 x y z) = False.
Proof. exact (prop_ext (fun h2 : term90 x y z => @lem7122198 x y z h1) (fun h2 : False => @lem7122200 x y z h1)). Qed.
Lemma lem7122202 (x : real) (y : real) (z : real) (h1 : term90 x y z) : False.
Proof. exact (EQ_MP (@lem7122201 x y z h1) (@lem7122200 x y z h1)). Qed.
Lemma lem7122203 (x : real) (y : real) (z : real) (h1 : term0 x y z) : term0 x y z.
Proof. exact (h1). Qed.
Lemma lem7122204 (x : real) (y : real) (z : real) (h1 : term0 x y z) : term90 x y z.
Proof. exact (EQ_MP (@lem7120119 x y z) (@lem7122203 x y z h1)). Qed.
Lemma lem7122205 (x : real) (y : real) (z : real) (h1 : term0 x y z) : (term90 x y z) = False.
Proof. exact (prop_ext (fun h2 : term90 x y z => @lem7122202 x y z h2) (fun h2 : False => @lem7122204 x y z h1)). Qed.
Lemma lem7122206 (x : real) (y : real) (z : real) (h1 : term0 x y z) : False.
Proof. exact (EQ_MP (@lem7122205 x y z h1) (@lem7122204 x y z h1)). Qed.
Lemma lem7122207 (x : real) (y : real) (z : real) : term182 x y z.
Proof. exact (fun h0 : term0 x y z => @lem7122206 x y z h0). Qed.
Lemma lem7122208 (x : real) (y : real) (z : real) : term183 x y z.
Proof. exact (@lem1386578 ((y = (real_sub z x)) = ((real_add x y) = z))). Qed.
Lemma lem7122212 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7122214 {A B : Type'} (op : type1400 B) : term184 A B op.
Proof. exact (@lem5824997 A B op). Qed.
Lemma lem7122215 {A B : Type'} (op : type1400 B) : (term184 A B op) = (term185 A B op).
Proof. exact (eq_refl (term184 A B op)). Qed.
Lemma lem7122216 {A B : Type'} (op : type1400 B) : term185 A B op.
Proof. exact (EQ_MP (@lem7122215 A B op) (@lem7122214 A B op)). Qed.
Lemma lem7122217 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7122218 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term186 A B op.
Proof. exact (@lem7122216 A B op (@lem7122217 B op h1)). Qed.
Lemma lem7122219 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term187 A B op f.
Proof. exact (@lem7122218 A B op h1 f). Qed.
Lemma lem7122220 {A B : Type'} (op : type1400 B) (f : A -> B) : (term187 A B op f) = (term188 A B op f).
Proof. exact (eq_refl (term187 A B op f)). Qed.
Lemma lem7122221 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term188 A B op f.
Proof. exact (EQ_MP (@lem7122220 A B op f) (@lem7122219 A B f op h1)). Qed.
Lemma lem7122222 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term189 A B op f s.
Proof. exact (@lem7122221 A B f op h1 s). Qed.
Lemma lem7122223 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term189 A B op f s) = (term190 A B op s f).
Proof. exact (eq_refl (term189 A B op f s)). Qed.
Lemma lem7122224 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term190 A B op s f.
Proof. exact (EQ_MP (@lem7122223 A B op s f) (@lem7122222 A B f s op h1)). Qed.
Lemma lem7122225 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) (op : type1400 B) (h1 : @monoidal B op) : term191 A B op s f a.
Proof. exact (@lem7122224 A B s f op h1 a). Qed.
Lemma lem7122226 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term191 A B op s f a) = (term192 A B a op s f).
Proof. exact (eq_refl (term191 A B op s f a)). Qed.
Lemma lem7122227 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term192 A B a op s f.
Proof. exact (EQ_MP (@lem7122226 A B a op s f) (@lem7122225 A B s f a op h1)). Qed.
Lemma lem7122228 {A : Type'} (a : A) (s : A -> Prop) (h1 : term193 A a s) : term193 A a s.
Proof. exact (h1). Qed.
Lemma lem7122229 {A B : Type'} (f : A -> B) (op : type1400 B) (a : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term193 A a s) : (term194 A B op s a f) = (@iterate B A op s f).
Proof. exact (@lem7122227 A B a s f op h1 (@lem7122228 A a s h2)). Qed.
Lemma lem7122230 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term192 A B a op s f.
Proof. exact (fun h0 : term193 A a s => @lem7122229 A B f op a s h1 h0). Qed.
Lemma lem7122231 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term195 A B a op s f.
Proof. exact (fun h0 : @monoidal B op => @lem7122230 A B a s f op h0). Qed.
Lemma lem7122233 (p : Prop) (q : Prop) (r : Prop) : (term196 p q r) = (term197 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem7122238 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term195 A B a op s f) = (term198 A B a op s f).
Proof. exact (@lem7122233 (@monoidal B op) (term193 A a s) ((term194 A B op s a f) = (@iterate B A op s f))). Qed.
Lemma lem7122275 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term199 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7122276 (p : Prop) (q : Prop) (p' : Prop) : term200 p q p'.
Proof. exact (fun q' : Prop => @lem7122275 p q p' q'). Qed.
Lemma lem7122277 (p : Prop) (q : Prop) : term201 p q.
Proof. exact (fun p' : Prop => @lem7122276 p q p'). Qed.
Lemma lem7122278 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term202 _132960 s f a.
Proof. exact (@lem7122277 (term193 _132960 a s) ((term203 _132960 s a f) = (term204 _132960 s f a))). Qed.
Lemma lem7122279 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) : term205 _132960 s f a p'.
Proof. exact (@lem7122278 _132960 s f a p'). Qed.
Lemma lem7122280 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) : (term205 _132960 s f a p') = (term206 _132960 s f a p').
Proof. exact (eq_refl (term205 _132960 s f a p')). Qed.
Lemma lem7122281 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) : term206 _132960 s f a p'.
Proof. exact (EQ_MP (@lem7122280 _132960 s f a p') (@lem7122279 _132960 s f a p')). Qed.
Lemma lem7122282 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) (q' : Prop) : term207 _132960 s f a p' q'.
Proof. exact (@lem7122281 _132960 s f a p' q'). Qed.
Lemma lem7122283 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) (q' : Prop) : (term207 _132960 s f a p' q') = (term208 _132960 s f a p' q').
Proof. exact (eq_refl (term207 _132960 s f a p' q')). Qed.
Lemma lem7122284 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) (p' : Prop) (q' : Prop) : term208 _132960 s f a p' q'.
Proof. exact (EQ_MP (@lem7122283 _132960 s f a p' q') (@lem7122282 _132960 s f a p' q')). Qed.
Lemma lem7122309 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) : (term193 _132960 a s) = (term193 _132960 a s).
Proof. exact (eq_refl (term193 _132960 a s)). Qed.
Lemma lem7122310 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (q' : Prop) : term209 _132960 f a s q'.
Proof. exact (@lem7122284 _132960 s f a (term193 _132960 a s) q'). Qed.
Lemma lem7122311 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (q' : Prop) : term210 _132960 f a s q'.
Proof. exact (@lem7122310 _132960 f a s q' (@lem7122309 _132960 a s)). Qed.
Lemma lem7122312 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : term193 _132960 a s.
Proof. exact (h1). Qed.
Lemma lem7122313 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : @IN _132960 a s.
Proof. exact (proj2 (@lem7122312 _132960 a s h1)). Qed.
Lemma lem7122314 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) : (@IN _132960 a s) = ((@IN _132960 a s) = True).
Proof. exact (@lem7 (@IN _132960 a s)). Qed.
Lemma lem7122316 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : @FINITE _132960 s.
Proof. exact (proj1 (@lem7122312 _132960 a s h1)). Qed.
Lemma lem7122317 {_132960 : Type'} (s : _132960 -> Prop) : (@FINITE _132960 s) = ((@FINITE _132960 s) = True).
Proof. exact (@lem7 (@FINITE _132960 s)). Qed.
Lemma lem7122320 (x : real) (y : real) (z : real) : (y = (real_sub z x)) = ((real_add x y) = z).
Proof. exact (@lem7122208 x y z (@lem7122207 x y z)). Qed.
Lemma lem7122321 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (f : _132960 -> real) : ((term203 _132960 s a f) = (term204 _132960 s f a)) = ((term211 _132960 s a f) = (@sum _132960 s f)).
Proof. exact (@lem7122320 (f a) (term203 _132960 s a f) (@sum _132960 s f)). Qed.
Lemma lem7122347 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7122348 {_132960 : Type'} : (@sum _132960) = (@iterate real _132960 real_add).
Proof. exact (@lem7122347 _132960). Qed.
Lemma lem7122365 {_132960 : Type'} (s : _132960 -> Prop) (a : _132960) : (@DELETE _132960 s a) = (@DELETE _132960 s a).
Proof. exact (eq_refl (@DELETE _132960 s a)). Qed.
Lemma lem7122366 {_132960 : Type'} (s : _132960 -> Prop) (a : _132960) : (term212 _132960 s a) = (term213 _132960 s a).
Proof. exact (MK_COMB (@lem7122348 _132960) (@lem7122365 _132960 s a)). Qed.
Lemma lem7122387 {_132960 : Type'} (f : _132960 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7122388 {_132960 : Type'} (s : _132960 -> Prop) (a : _132960) (f : _132960 -> real) : (term203 _132960 s a f) = (term214 _132960 s a f).
Proof. exact (MK_COMB (@lem7122366 _132960 s a) (@lem7122387 _132960 f)). Qed.
Lemma lem7122411 {_132960 : Type'} (f : _132960 -> real) (a : _132960) : (term215 _132960 f a) = (term215 _132960 f a).
Proof. exact (eq_refl (term215 _132960 f a)). Qed.
Lemma lem7122412 {_132960 : Type'} (s : _132960 -> Prop) (a : _132960) (f : _132960 -> real) : (term211 _132960 s a f) = (term216 _132960 s a f).
Proof. exact (MK_COMB (@lem7122411 _132960 f a) (@lem7122388 _132960 s a f)). Qed.
Lemma lem7122414 {A B : Type'} (a : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term198 A B a op s f.
Proof. exact (EQ_MP (@lem7122238 A B a op s f) (@lem7122231 A B a op s f)). Qed.
Lemma lem7122415 {_132960 : Type'} (a : _132960) (op : type1627) (s : _132960 -> Prop) (f : _132960 -> real) : term217 _132960 a op s f.
Proof. exact (@lem7122414 _132960 real a op s f). Qed.
Lemma lem7122416 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (f : _132960 -> real) : term218 _132960 a s f.
Proof. exact (@lem7122415 _132960 a real_add s f). Qed.
Lemma lem7122426 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7122212) (@lem7067132)). Qed.
Lemma lem7122429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7122430 : term219 = (and True).
Proof. exact (MK_COMB (@lem7122429) (@lem7122426)). Qed.
Lemma lem7122446 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (@FINITE _132960 s) = True.
Proof. exact (EQ_MP (@lem7122317 _132960 s) (@lem7122316 _132960 a s h1)). Qed.
Lemma lem7122449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7122450 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term220 _132960 s) = (and True).
Proof. exact (MK_COMB (@lem7122449) (@lem7122446 _132960 a s h1)). Qed.
Lemma lem7122458 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (@IN _132960 a s) = True.
Proof. exact (EQ_MP (@lem7122314 _132960 a s) (@lem7122313 _132960 a s h1)). Qed.
Lemma lem7122461 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term193 _132960 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem7122450 _132960 a s h1) (@lem7122458 _132960 a s h1)). Qed.
Lemma lem7122463 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7122464 : (True /\ True) = True.
Proof. exact (@lem7122463 True). Qed.
Lemma lem7122467 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term193 _132960 a s) = True.
Proof. exact (TRANS (@lem7122461 _132960 a s h1) (@lem7122464)). Qed.
Lemma lem7122468 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term221 _132960 a s) = (True /\ True).
Proof. exact (MK_COMB (@lem7122430) (@lem7122467 _132960 a s h1)). Qed.
Lemma lem7122470 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7122471 : (True /\ True) = True.
Proof. exact (@lem7122470 True). Qed.
Lemma lem7122474 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term221 _132960 a s) = True.
Proof. exact (TRANS (@lem7122468 _132960 a s h1) (@lem7122471)). Qed.
Lemma lem7122475 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : True = (term221 _132960 a s).
Proof. exact (SYM (@lem7122474 _132960 a s h1)). Qed.
Lemma lem7122476 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : term221 _132960 a s.
Proof. exact (EQ_MP (@lem7122475 _132960 a s h1) (@lem0)). Qed.
Lemma lem7122477 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term216 _132960 s a f) = (@iterate real _132960 real_add s f).
Proof. exact (@lem7122416 _132960 a s f (@lem7122476 _132960 a s h1)). Qed.
Lemma lem7122492 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term211 _132960 s a f) = (@iterate real _132960 real_add s f).
Proof. exact (TRANS (@lem7122412 _132960 s a f) (@lem7122477 _132960 f a s h1)). Qed.
Lemma lem7122493 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7122494 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : (term222 _132960 s a f) = (term223 _132960 s f).
Proof. exact (MK_COMB (@lem7122493) (@lem7122492 _132960 f a s h1)). Qed.
Lemma lem7122518 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7122519 {_132960 : Type'} : (@sum _132960) = (@iterate real _132960 real_add).
Proof. exact (@lem7122518 _132960). Qed.
Lemma lem7122528 {_132960 : Type'} (s : _132960 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7122529 {_132960 : Type'} (s : _132960 -> Prop) : (@sum _132960 s) = (@iterate real _132960 real_add s).
Proof. exact (MK_COMB (@lem7122519 _132960) (@lem7122528 _132960 s)). Qed.
Lemma lem7122542 {_132960 : Type'} (f : _132960 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7122543 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (@sum _132960 s f) = (@iterate real _132960 real_add s f).
Proof. exact (MK_COMB (@lem7122529 _132960 s) (@lem7122542 _132960 f)). Qed.
Lemma lem7122558 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : ((term211 _132960 s a f) = (@sum _132960 s f)) = ((@iterate real _132960 real_add s f) = (@iterate real _132960 real_add s f)).
Proof. exact (MK_COMB (@lem7122494 _132960 f a s h1) (@lem7122543 _132960 s f)). Qed.
Lemma lem7122560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7122561 (x : real) : (x = x) = True.
Proof. exact (@lem7122560 real x). Qed.
Lemma lem7122562 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : ((@iterate real _132960 real_add s f) = (@iterate real _132960 real_add s f)) = True.
Proof. exact (@lem7122561 (@iterate real _132960 real_add s f)). Qed.
Lemma lem7122565 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : ((term211 _132960 s a f) = (@sum _132960 s f)) = True.
Proof. exact (TRANS (@lem7122558 _132960 f a s h1) (@lem7122562 _132960 s f)). Qed.
Lemma lem7122566 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) (h1 : term193 _132960 a s) : ((term203 _132960 s a f) = (term204 _132960 s f a)) = True.
Proof. exact (TRANS (@lem7122321 _132960 a s f) (@lem7122565 _132960 f a s h1)). Qed.
Lemma lem7122567 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : term224 _132960 s f a.
Proof. exact (fun h0 : term193 _132960 a s => @lem7122566 _132960 f a s h0). Qed.
Lemma lem7122568 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) : term225 _132960 f a s.
Proof. exact (@lem7122311 _132960 f a s True). Qed.
Lemma lem7122569 {_132960 : Type'} (f : _132960 -> real) (a : _132960) (s : _132960 -> Prop) : (term226 _132960 s f a) = (term227 _132960 a s).
Proof. exact (@lem7122568 _132960 f a s (@lem7122567 _132960 s f a)). Qed.
Lemma lem7122571 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7122572 {_132960 : Type'} (a : _132960) (s : _132960 -> Prop) : (term227 _132960 a s) = True.
Proof. exact (@lem7122571 (term193 _132960 a s)). Qed.
Lemma lem7122575 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) (a : _132960) : (term226 _132960 s f a) = True.
Proof. exact (TRANS (@lem7122569 _132960 f a s) (@lem7122572 _132960 a s)). Qed.
Lemma lem7122576 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (term228 _132960 s f) = (term229 _132960).
Proof. exact (fun_ext (fun a : _132960 => @lem7122575 _132960 s f a)). Qed.
Lemma lem7122581 {_132960 : Type'} : (@all _132960) = (@all _132960).
Proof. exact (eq_refl (@all _132960)). Qed.
Lemma lem7122582 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (term230 _132960 s f) = (term231 _132960).
Proof. exact (MK_COMB (@lem7122581 _132960) (@lem7122576 _132960 s f)). Qed.
Lemma lem7122584 {A : Type'} (t : Prop) : (term232 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7122585 {_132960 : Type'} (t : Prop) : (term232 _132960 t) = t.
Proof. exact (@lem7122584 _132960 t). Qed.
Lemma lem7122586 {_132960 : Type'} : (term231 _132960) = True.
Proof. exact (@lem7122585 _132960 True). Qed.
Lemma lem7122589 {_132960 : Type'} (s : _132960 -> Prop) (f : _132960 -> real) : (term230 _132960 s f) = True.
Proof. exact (TRANS (@lem7122582 _132960 s f) (@lem7122586 _132960)). Qed.
Lemma lem7122590 {_132960 : Type'} (f : _132960 -> real) : (term233 _132960 f) = (term234 _132960).
Proof. exact (fun_ext (fun s : _132960 -> Prop => @lem7122589 _132960 s f)). Qed.
Lemma lem7122595 {_132960 : Type'} : (@all (_132960 -> Prop)) = (@all (_132960 -> Prop)).
Proof. exact (eq_refl (@all (_132960 -> Prop))). Qed.
Lemma lem7122596 {_132960 : Type'} (f : _132960 -> real) : (term235 _132960 f) = (term236 _132960).
Proof. exact (MK_COMB (@lem7122595 _132960) (@lem7122590 _132960 f)). Qed.
Lemma lem7122598 {A : Type'} (t : Prop) : (term232 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7122599 {_132960 : Type'} (t : Prop) : (term237 _132960 t) = t.
Proof. exact (@lem7122598 (_132960 -> Prop) t). Qed.
Lemma lem7122600 {_132960 : Type'} : (term236 _132960) = True.
Proof. exact (@lem7122599 _132960 True). Qed.
Lemma lem7122603 {_132960 : Type'} (f : _132960 -> real) : (term235 _132960 f) = True.
Proof. exact (TRANS (@lem7122596 _132960 f) (@lem7122600 _132960)). Qed.
Lemma lem7122604 {_132960 : Type'} : (term238 _132960) = (term239 _132960).
Proof. exact (fun_ext (fun f : _132960 -> real => @lem7122603 _132960 f)). Qed.
Lemma lem7122609 {_132960 : Type'} : (@all (_132960 -> real)) = (@all (_132960 -> real)).
Proof. exact (eq_refl (@all (_132960 -> real))). Qed.
Lemma lem7122610 {_132960 : Type'} : (term240 _132960) = (term241 _132960).
Proof. exact (MK_COMB (@lem7122609 _132960) (@lem7122604 _132960)). Qed.
Lemma lem7122612 {A : Type'} (t : Prop) : (term232 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7122613 {_132960 : Type'} (t : Prop) : (term242 _132960 t) = t.
Proof. exact (@lem7122612 (_132960 -> real) t). Qed.
Lemma lem7122614 {_132960 : Type'} : (term241 _132960) = True.
Proof. exact (@lem7122613 _132960 True). Qed.
Lemma lem7122617 {_132960 : Type'} : (term240 _132960) = True.
Proof. exact (TRANS (@lem7122610 _132960) (@lem7122614 _132960)). Qed.
Lemma lem7122618 {_132960 : Type'} : True = (term240 _132960).
Proof. exact (SYM (@lem7122617 _132960)). Qed.
Lemma lem7122619 {_132960 : Type'} : term240 _132960.
Proof. exact (EQ_MP (@lem7122618 _132960) (@lem0)). Qed.

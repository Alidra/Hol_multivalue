Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_POW_2_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_POW_2_spec.
Require Import REAL_POW_EQ_0_spec.
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
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1646394 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1646395 : term1.
Proof. exact (proj2 (@lem1646394)). Qed.
Lemma lem1646396 : term2.
Proof. exact (proj2 (@lem1646395)). Qed.
Lemma lem1646397 : term3.
Proof. exact (proj2 (@lem1646396)). Qed.
Lemma lem1646439 : term4.
Proof. exact (proj1 (@lem1646397)). Qed.
Lemma lem1646440 (n : nat) : term5 n.
Proof. exact (@lem1646439 n). Qed.
Lemma lem1646441 (n : nat) : (term5 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1646443 : term6.
Proof. exact (proj1 (@lem1646396)). Qed.
Lemma lem1646444 (n : nat) : term7 n.
Proof. exact (@lem1646443 n). Qed.
Lemma lem1646445 (n : nat) : (term7 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1646448 : term8.
Proof. exact (proj1 (@lem1646394)). Qed.
Lemma lem1646449 (m : nat) : term9 m.
Proof. exact (@lem1646448 m). Qed.
Lemma lem1646450 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1646451 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1646450 m) (@lem1646449 m)). Qed.
Lemma lem1646452 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1646451 m n). Qed.
Lemma lem1646453 (m : nat) (n : nat) : (term11 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1646705 (x : real) : term12 x.
Proof. exact (@lem1630283 x). Qed.
Lemma lem1646706 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1646707 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1646706 x) (@lem1646705 x)). Qed.
Lemma lem1646708 (x : real) (n : nat) : term14 x n.
Proof. exact (@lem1646707 x n). Qed.
Lemma lem1646709 (x : real) (n : nat) : (term14 x n) = (((real_pow x n) = term15) = (term16 x n)).
Proof. exact (eq_refl (term14 x n)). Qed.
Lemma lem1646723 (x : real) : (term17 x) = (x = term15).
Proof. exact (@lem16933 (x = term15)). Qed.
Lemma lem1646725 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1646726 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1646725 x) (@lem1646723 x)). Qed.
Lemma lem1646727 (x : real) : (term21 x) = (term19 x).
Proof. exact (@lem17045 (term22 x) (term23 x)). Qed.
Lemma lem1646728 (x : real) : (term21 x) = (term20 x).
Proof. exact (TRANS (@lem1646727 x) (@lem1646726 x)). Qed.
Lemma lem1646734 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1646736 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1646737 (x : real) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1646736 x) (@lem1646728 x)). Qed.
Lemma lem1646738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1646739 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1646738) (@lem1646737 x)). Qed.
Lemma lem1646740 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1646739 x) (@lem1646734 x)). Qed.
Lemma lem1646741 (x : real) : (term32 x) = (term30 x).
Proof. exact (@lem17646 (term33 x) (term34 x)). Qed.
Lemma lem1646771 (x : real) : (term32 x) = (term31 x).
Proof. exact (TRANS (@lem1646741 x) (@lem1646740 x)). Qed.
Lemma lem1646772 (x : real) : (term33 x) = (term35 x).
Proof. exact (@lem1483521 x term15). Qed.
Lemma lem1646778 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1646780 (x : nat) : (term38 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1646781 : term39 = term15.
Proof. exact (@lem1646780 term40). Qed.
Lemma lem1646782 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1646783 (x : real) : (term37 x) = (term41 x).
Proof. exact (MK_COMB (@lem1646782 x) (@lem1646781)). Qed.
Lemma lem1646784 (x : real) : (term41 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1646785 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1646783 x) (@lem1646784 x)). Qed.
Lemma lem1646787 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1646778 x) (@lem1646785 x)). Qed.
Lemma lem1646788 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1646789 (x : real) : (term42 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1646788) (@lem1646787 x)). Qed.
Lemma lem1646790 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646791 (x : real) : (term35 x) = (term43 x).
Proof. exact (MK_COMB (@lem1646789 x) (@lem1646790)). Qed.
Lemma lem1646792 (x : real) : (term33 x) = (term43 x).
Proof. exact (TRANS (@lem1646772 x) (@lem1646791 x)). Qed.
Lemma lem1646793 (x : real) : (term44 x) = (term45 x).
Proof. exact (@lem1483533 term15 x). Qed.
Lemma lem1646799 (x : real) : (term46 x) = (term47 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1646804 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1483448 (term48 x)). Qed.
Lemma lem1646806 (x : real) : (term46 x) = (term48 x).
Proof. exact (TRANS (@lem1646799 x) (@lem1646804 x)). Qed.
Lemma lem1646807 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1646808 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1646807) (@lem1646806 x)). Qed.
Lemma lem1646809 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646810 (x : real) : (term45 x) = (term51 x).
Proof. exact (MK_COMB (@lem1646808 x) (@lem1646809)). Qed.
Lemma lem1646811 (x : real) : (term44 x) = (term51 x).
Proof. exact (TRANS (@lem1646793 x) (@lem1646810 x)). Qed.
Lemma lem1646812 (x : real) : (x = term15) = ((term36 x) = term15).
Proof. exact (@lem1483529 x term15). Qed.
Lemma lem1646818 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1646820 (x : nat) : (term38 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1646821 : term39 = term15.
Proof. exact (@lem1646820 term40). Qed.
Lemma lem1646822 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1646823 (x : real) : (term37 x) = (term41 x).
Proof. exact (MK_COMB (@lem1646822 x) (@lem1646821)). Qed.
Lemma lem1646824 (x : real) : (term41 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1646825 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1646823 x) (@lem1646824 x)). Qed.
Lemma lem1646827 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1646818 x) (@lem1646825 x)). Qed.
Lemma lem1646828 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1646829 (x : real) : (term52 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1646828) (@lem1646827 x)). Qed.
Lemma lem1646830 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646831 (x : real) : ((term36 x) = term15) = (x = term15).
Proof. exact (MK_COMB (@lem1646829 x) (@lem1646830)). Qed.
Lemma lem1646832 (x : real) : (x = term15) = (x = term15).
Proof. exact (TRANS (@lem1646812 x) (@lem1646831 x)). Qed.
Lemma lem1646833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1646834 (x : real) : (term18 x) = (term53 x).
Proof. exact (MK_COMB (@lem1646833) (@lem1646811 x)). Qed.
Lemma lem1646835 (x : real) : (term20 x) = (term54 x).
Proof. exact (MK_COMB (@lem1646834 x) (@lem1646832 x)). Qed.
Lemma lem1646836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1646837 (x : real) : (term25 x) = (term55 x).
Proof. exact (MK_COMB (@lem1646836) (@lem1646792 x)). Qed.
Lemma lem1646838 (x : real) : (term27 x) = (term56 x).
Proof. exact (MK_COMB (@lem1646837 x) (@lem1646835 x)). Qed.
Lemma lem1646839 (x : real) : (term57 x) = (term58 x).
Proof. exact (@lem1483531 term15 x). Qed.
Lemma lem1646845 (x : real) : (term46 x) = (term47 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1646850 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1483448 (term48 x)). Qed.
Lemma lem1646852 (x : real) : (term46 x) = (term48 x).
Proof. exact (TRANS (@lem1646845 x) (@lem1646850 x)). Qed.
Lemma lem1646853 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1646854 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1646853) (@lem1646852 x)). Qed.
Lemma lem1646855 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646856 (x : real) : (term58 x) = (term61 x).
Proof. exact (MK_COMB (@lem1646854 x) (@lem1646855)). Qed.
Lemma lem1646857 (x : real) : (term57 x) = (term61 x).
Proof. exact (TRANS (@lem1646839 x) (@lem1646856 x)). Qed.
Lemma lem1646858 (x : real) : (term22 x) = (term62 x).
Proof. exact (@lem1483523 x term15). Qed.
Lemma lem1646864 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1646866 (x : nat) : (term38 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1646867 : term39 = term15.
Proof. exact (@lem1646866 term40). Qed.
Lemma lem1646868 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1646869 (x : real) : (term37 x) = (term41 x).
Proof. exact (MK_COMB (@lem1646868 x) (@lem1646867)). Qed.
Lemma lem1646870 (x : real) : (term41 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1646871 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1646869 x) (@lem1646870 x)). Qed.
Lemma lem1646873 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1646864 x) (@lem1646871 x)). Qed.
Lemma lem1646874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1646875 (x : real) : (term63 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1646874) (@lem1646873 x)). Qed.
Lemma lem1646876 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646877 (x : real) : (term62 x) = (term64 x).
Proof. exact (MK_COMB (@lem1646875 x) (@lem1646876)). Qed.
Lemma lem1646878 (x : real) : (term22 x) = (term64 x).
Proof. exact (TRANS (@lem1646858 x) (@lem1646877 x)). Qed.
Lemma lem1646879 (x : real) : (term23 x) = (term65 x).
Proof. exact (@lem1483554 x term15). Qed.
Lemma lem1646885 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1646887 (x : nat) : (term38 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1646888 : term39 = term15.
Proof. exact (@lem1646887 term40). Qed.
Lemma lem1646889 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1646890 (x : real) : (term37 x) = (term41 x).
Proof. exact (MK_COMB (@lem1646889 x) (@lem1646888)). Qed.
Lemma lem1646891 (x : real) : (term41 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1646892 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1646890 x) (@lem1646891 x)). Qed.
Lemma lem1646894 (x : real) : (term36 x) = x.
Proof. exact (TRANS (@lem1646885 x) (@lem1646892 x)). Qed.
Lemma lem1646895 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1646896 (x : real) : (term66 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1646895) (@lem1646894 x)). Qed.
Lemma lem1646899 (x : real) : (real_neg x) = (term48 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1646900 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1646901 (x : real) : ((term66 x) = (real_neg x)) = ((term66 x) = (term48 x)).
Proof. exact (MK_COMB (@lem1646900 x) (@lem1646899 x)). Qed.
Lemma lem1646902 (x : real) : (term66 x) = (term48 x).
Proof. exact (EQ_MP (@lem1646901 x) (@lem1646896 x)). Qed.
Lemma lem1646903 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1646904 (x : real) : (term68 x) = (term50 x).
Proof. exact (MK_COMB (@lem1646903) (@lem1646902 x)). Qed.
Lemma lem1646905 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646906 (x : real) : (term69 x) = (term51 x).
Proof. exact (MK_COMB (@lem1646904 x) (@lem1646905)). Qed.
Lemma lem1646907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1646908 (x : real) : (term42 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1646907) (@lem1646894 x)). Qed.
Lemma lem1646909 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1646910 (x : real) : (term35 x) = (term43 x).
Proof. exact (MK_COMB (@lem1646908 x) (@lem1646909)). Qed.
Lemma lem1646911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1646912 (x : real) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1646911) (@lem1646910 x)). Qed.
Lemma lem1646913 (x : real) : (term65 x) = (term72 x).
Proof. exact (MK_COMB (@lem1646912 x) (@lem1646906 x)). Qed.
Lemma lem1646914 (x : real) : (term23 x) = (term72 x).
Proof. exact (TRANS (@lem1646879 x) (@lem1646913 x)). Qed.
Lemma lem1646915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1646916 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1646915) (@lem1646878 x)). Qed.
Lemma lem1646917 (x : real) : (term34 x) = (term75 x).
Proof. exact (MK_COMB (@lem1646916 x) (@lem1646914 x)). Qed.
Lemma lem1646918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1646919 (x : real) : (term76 x) = (term77 x).
Proof. exact (MK_COMB (@lem1646918) (@lem1646857 x)). Qed.
Lemma lem1646920 (x : real) : (term24 x) = (term78 x).
Proof. exact (MK_COMB (@lem1646919 x) (@lem1646917 x)). Qed.
Lemma lem1646921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1646922 (x : real) : (term29 x) = (term79 x).
Proof. exact (MK_COMB (@lem1646921) (@lem1646838 x)). Qed.
Lemma lem1646923 (x : real) : (term31 x) = (term80 x).
Proof. exact (MK_COMB (@lem1646922 x) (@lem1646920 x)). Qed.
Lemma lem1646930 (x : real) : (term32 x) = (term80 x).
Proof. exact (TRANS (@lem1646771 x) (@lem1646923 x)). Qed.
Lemma lem1646947 (x : real) : (term75 x) = (term81 x).
Proof. exact (@lem19158 (term43 x) (term64 x) (term51 x)). Qed.
Lemma lem1646950 (x : real) : (term77 x) = (term77 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1646951 (x : real) : (term78 x) = (term82 x).
Proof. exact (MK_COMB (@lem1646950 x) (@lem1646947 x)). Qed.
Lemma lem1646958 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem19158 (term84 x) (term61 x) (term85 x)). Qed.
Lemma lem1646959 (x : real) : (term78 x) = (term83 x).
Proof. exact (TRANS (@lem1646951 x) (@lem1646958 x)). Qed.
Lemma lem1646976 (x : real) : (term56 x) = (term86 x).
Proof. exact (@lem19158 (term51 x) (term43 x) (x = term15)). Qed.
Lemma lem1646977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1646978 (x : real) : (term79 x) = (term87 x).
Proof. exact (MK_COMB (@lem1646977) (@lem1646976 x)). Qed.
Lemma lem1646979 (x : real) : (term80 x) = (term88 x).
Proof. exact (MK_COMB (@lem1646978 x) (@lem1646959 x)). Qed.
Lemma lem1646980 (x : real) : (term32 x) = (term88 x).
Proof. exact (TRANS (@lem1646930 x) (@lem1646979 x)). Qed.
Lemma lem1647002 (x : real) (h1 : term88 x) : term88 x.
Proof. exact (h1). Qed.
Lemma lem1647003 (x : real) (h1 : term86 x) : term86 x.
Proof. exact (h1). Qed.
Lemma lem1647004 (x : real) (h1 : term89 x) : term89 x.
Proof. exact (h1). Qed.
Lemma lem1647005 (x : real) (h1 : term89 x) : term51 x.
Proof. exact (proj2 (@lem1647004 x h1)). Qed.
Lemma lem1647006 (x : real) (h1 : term89 x) : term43 x.
Proof. exact (proj1 (@lem1647004 x h1)). Qed.
Lemma lem1647008 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647009 : term91 = term92.
Proof. exact (@lem1647008 (NUMERAL 0) term40). Qed.
Lemma lem1647010 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647011 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647012 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647011 h1) (fun h1 : term92 = True => @lem1647010)). Qed.
Lemma lem1647013 : term92 = True.
Proof. exact (EQ_MP (@lem1647012) (@lem1647010)). Qed.
Lemma lem1647014 : term91 = True.
Proof. exact (TRANS (@lem1647009) (@lem1647013)). Qed.
Lemma lem1647015 : True = term91.
Proof. exact (SYM (@lem1647014)). Qed.
Lemma lem1647016 : term91.
Proof. exact (EQ_MP (@lem1647015) (@lem0)). Qed.
Lemma lem1647017 (x : real) (h1 : term89 x) : term94 x.
Proof. exact (conj (@lem1647016) (@lem1647006 x h1)). Qed.
Lemma lem1647019 (x : real) (y : real) : term95 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647020 (x : real) : term96 x.
Proof. exact (@lem1647019 term97 x). Qed.
Lemma lem1647021 (x : real) (h1 : term89 x) : term98 x.
Proof. exact (@lem1647020 x (@lem1647017 x h1)). Qed.
Lemma lem1647022 (x : real) : (term99 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647023 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647024 (x : real) : (term100 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1647023) (@lem1647022 x)). Qed.
Lemma lem1647025 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647026 (x : real) : (term98 x) = (term43 x).
Proof. exact (MK_COMB (@lem1647024 x) (@lem1647025)). Qed.
Lemma lem1647027 (x : real) (h1 : term89 x) : term43 x.
Proof. exact (EQ_MP (@lem1647026 x) (@lem1647021 x h1)). Qed.
Lemma lem1647029 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647030 : term91 = term92.
Proof. exact (@lem1647029 (NUMERAL 0) term40). Qed.
Lemma lem1647031 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647032 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647033 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647032 h1) (fun h1 : term92 = True => @lem1647031)). Qed.
Lemma lem1647034 : term92 = True.
Proof. exact (EQ_MP (@lem1647033) (@lem1647031)). Qed.
Lemma lem1647035 : term91 = True.
Proof. exact (TRANS (@lem1647030) (@lem1647034)). Qed.
Lemma lem1647036 : True = term91.
Proof. exact (SYM (@lem1647035)). Qed.
Lemma lem1647037 : term91.
Proof. exact (EQ_MP (@lem1647036) (@lem0)). Qed.
Lemma lem1647038 (x : real) (h1 : term89 x) : term101 x.
Proof. exact (conj (@lem1647037) (@lem1647005 x h1)). Qed.
Lemma lem1647040 (x : real) (y : real) : term95 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647041 (x : real) : term102 x.
Proof. exact (@lem1647040 term97 (term48 x)). Qed.
Lemma lem1647042 (x : real) (h1 : term89 x) : term103 x.
Proof. exact (@lem1647041 x (@lem1647038 x h1)). Qed.
Lemma lem1647043 (x : real) : (term104 x) = (term48 x).
Proof. exact (@lem1483460 (term48 x)). Qed.
Lemma lem1647044 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647045 (x : real) : (term105 x) = (term50 x).
Proof. exact (MK_COMB (@lem1647044) (@lem1647043 x)). Qed.
Lemma lem1647046 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647047 (x : real) : (term103 x) = (term51 x).
Proof. exact (MK_COMB (@lem1647045 x) (@lem1647046)). Qed.
Lemma lem1647048 (x : real) (h1 : term89 x) : term51 x.
Proof. exact (EQ_MP (@lem1647047 x) (@lem1647042 x h1)). Qed.
Lemma lem1647049 (x : real) (h1 : term89 x) : term106 x.
Proof. exact (conj (@lem1647048 x h1) (@lem1647027 x h1)). Qed.
Lemma lem1647051 (x : real) (y : real) : term107 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1647052 (x : real) : term108 x.
Proof. exact (@lem1647051 (term48 x) x). Qed.
Lemma lem1647053 (x : real) (h1 : term89 x) : term109 x.
Proof. exact (@lem1647052 x (@lem1647049 x h1)). Qed.
Lemma lem1647054 (x : real) : (term110 x) = (term111 x).
Proof. exact (@lem1483440 term112 x). Qed.
Lemma lem1647056 (m : nat) : (term113 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647057 : term114 = term15.
Proof. exact (@lem1647056 term40). Qed.
Lemma lem1647058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647059 : term115 = term116.
Proof. exact (MK_COMB (@lem1647058) (@lem1647057)). Qed.
Lemma lem1647060 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647061 (x : real) : (term111 x) = (term117 x).
Proof. exact (MK_COMB (@lem1647059) (@lem1647060 x)). Qed.
Lemma lem1647062 (x : real) : (term110 x) = (term117 x).
Proof. exact (TRANS (@lem1647054 x) (@lem1647061 x)). Qed.
Lemma lem1647063 (x : real) : (term117 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647064 (x : real) : (term110 x) = term15.
Proof. exact (TRANS (@lem1647062 x) (@lem1647063 x)). Qed.
Lemma lem1647065 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647066 (x : real) : (term118 x) = term119.
Proof. exact (MK_COMB (@lem1647065) (@lem1647064 x)). Qed.
Lemma lem1647067 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647068 (x : real) : (term109 x) = term120.
Proof. exact (MK_COMB (@lem1647066 x) (@lem1647067)). Qed.
Lemma lem1647069 (x : real) (h1 : term89 x) : term120.
Proof. exact (EQ_MP (@lem1647068 x) (@lem1647053 x h1)). Qed.
Lemma lem1647071 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647072 : term120 = term121.
Proof. exact (@lem1647071 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1647073 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1647074 : term120 = False.
Proof. exact (TRANS (@lem1647072) (@lem1647073)). Qed.
Lemma lem1647075 (x : real) (h1 : term89 x) : False.
Proof. exact (EQ_MP (@lem1647074) (@lem1647069 x h1)). Qed.
Lemma lem1647076 (x : real) (h1 : term122 x) : term122 x.
Proof. exact (h1). Qed.
Lemma lem1647077 (x : real) (h1 : term122 x) : x = term15.
Proof. exact (proj2 (@lem1647076 x h1)). Qed.
Lemma lem1647078 (x : real) (h1 : term122 x) : term43 x.
Proof. exact (proj1 (@lem1647076 x h1)). Qed.
Lemma lem1647080 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647081 : term91 = term92.
Proof. exact (@lem1647080 (NUMERAL 0) term40). Qed.
Lemma lem1647082 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647083 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647084 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647083 h1) (fun h1 : term92 = True => @lem1647082)). Qed.
Lemma lem1647085 : term92 = True.
Proof. exact (EQ_MP (@lem1647084) (@lem1647082)). Qed.
Lemma lem1647086 : term91 = True.
Proof. exact (TRANS (@lem1647081) (@lem1647085)). Qed.
Lemma lem1647087 : True = term91.
Proof. exact (SYM (@lem1647086)). Qed.
Lemma lem1647088 : term91.
Proof. exact (EQ_MP (@lem1647087) (@lem0)). Qed.
Lemma lem1647089 (x : real) (h1 : term122 x) : term94 x.
Proof. exact (conj (@lem1647088) (@lem1647078 x h1)). Qed.
Lemma lem1647091 (x : real) (y : real) : term95 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647092 (x : real) : term96 x.
Proof. exact (@lem1647091 term97 x). Qed.
Lemma lem1647093 (x : real) (h1 : term122 x) : term98 x.
Proof. exact (@lem1647092 x (@lem1647089 x h1)). Qed.
Lemma lem1647094 (x : real) : (term99 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647095 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647096 (x : real) : (term100 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1647095) (@lem1647094 x)). Qed.
Lemma lem1647097 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647098 (x : real) : (term98 x) = (term43 x).
Proof. exact (MK_COMB (@lem1647096 x) (@lem1647097)). Qed.
Lemma lem1647099 (x : real) (h1 : term122 x) : term43 x.
Proof. exact (EQ_MP (@lem1647098 x) (@lem1647093 x h1)). Qed.
Lemma lem1647101 (y : real) : term123 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1647102 (x : real) : term123 x.
Proof. exact (@lem1647101 x). Qed.
Lemma lem1647103 (x : real) (h1 : term122 x) : term124 x.
Proof. exact (@lem1647102 x (@lem1647077 x h1)). Qed.
Lemma lem1647104 (x : real) (h1 : term122 x) : term125 x.
Proof. exact (@lem1647103 x h1 term112). Qed.
Lemma lem1647105 (x : real) : (term125 x) = ((term48 x) = term15).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1647112 (x : real) (h1 : term122 x) : (term48 x) = term15.
Proof. exact (EQ_MP (@lem1647105 x) (@lem1647104 x h1)). Qed.
Lemma lem1647113 (x : real) (h1 : term122 x) : term126 x.
Proof. exact (conj (@lem1647112 x h1) (@lem1647099 x h1)). Qed.
Lemma lem1647115 (x : real) (y : real) : term127 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1647116 (x : real) : term128 x.
Proof. exact (@lem1647115 (term48 x) x). Qed.
Lemma lem1647117 (x : real) (h1 : term122 x) : term109 x.
Proof. exact (@lem1647116 x (@lem1647113 x h1)). Qed.
Lemma lem1647118 (x : real) : (term110 x) = (term111 x).
Proof. exact (@lem1483440 term112 x). Qed.
Lemma lem1647120 (m : nat) : (term113 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647121 : term114 = term15.
Proof. exact (@lem1647120 term40). Qed.
Lemma lem1647122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647123 : term115 = term116.
Proof. exact (MK_COMB (@lem1647122) (@lem1647121)). Qed.
Lemma lem1647124 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647125 (x : real) : (term111 x) = (term117 x).
Proof. exact (MK_COMB (@lem1647123) (@lem1647124 x)). Qed.
Lemma lem1647126 (x : real) : (term110 x) = (term117 x).
Proof. exact (TRANS (@lem1647118 x) (@lem1647125 x)). Qed.
Lemma lem1647127 (x : real) : (term117 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647128 (x : real) : (term110 x) = term15.
Proof. exact (TRANS (@lem1647126 x) (@lem1647127 x)). Qed.
Lemma lem1647129 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647130 (x : real) : (term118 x) = term119.
Proof. exact (MK_COMB (@lem1647129) (@lem1647128 x)). Qed.
Lemma lem1647131 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647132 (x : real) : (term109 x) = term120.
Proof. exact (MK_COMB (@lem1647130 x) (@lem1647131)). Qed.
Lemma lem1647133 (x : real) (h1 : term122 x) : term120.
Proof. exact (EQ_MP (@lem1647132 x) (@lem1647117 x h1)). Qed.
Lemma lem1647135 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647136 : term120 = term121.
Proof. exact (@lem1647135 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1647137 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1647138 : term120 = False.
Proof. exact (TRANS (@lem1647136) (@lem1647137)). Qed.
Lemma lem1647139 (x : real) (h1 : term122 x) : False.
Proof. exact (EQ_MP (@lem1647138) (@lem1647133 x h1)). Qed.
Lemma lem1647140 (x : real) (h1 : term86 x) : False.
Proof. exact (or_elim (@lem1647003 x h1) (fun h0 : term89 x => @lem1647075 x h0) (fun h0 : term122 x => @lem1647139 x h0)). Qed.
Lemma lem1647141 (x : real) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1647142 (x : real) (h1 : term129 x) : term129 x.
Proof. exact (h1). Qed.
Lemma lem1647143 (x : real) (h1 : term129 x) : term84 x.
Proof. exact (proj2 (@lem1647142 x h1)). Qed.
Lemma lem1647144 (x : real) (h1 : term129 x) : term61 x.
Proof. exact (proj1 (@lem1647142 x h1)). Qed.
Lemma lem1647145 (x : real) (h1 : term129 x) : term43 x.
Proof. exact (proj2 (@lem1647143 x h1)). Qed.
Lemma lem1647148 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647149 : term91 = term92.
Proof. exact (@lem1647148 (NUMERAL 0) term40). Qed.
Lemma lem1647150 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647151 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647152 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647151 h1) (fun h1 : term92 = True => @lem1647150)). Qed.
Lemma lem1647153 : term92 = True.
Proof. exact (EQ_MP (@lem1647152) (@lem1647150)). Qed.
Lemma lem1647154 : term91 = True.
Proof. exact (TRANS (@lem1647149) (@lem1647153)). Qed.
Lemma lem1647155 : True = term91.
Proof. exact (SYM (@lem1647154)). Qed.
Lemma lem1647156 : term91.
Proof. exact (EQ_MP (@lem1647155) (@lem0)). Qed.
Lemma lem1647157 (x : real) (h1 : term129 x) : term130 x.
Proof. exact (conj (@lem1647156) (@lem1647144 x h1)). Qed.
Lemma lem1647159 (x : real) (y : real) : term131 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1647160 (x : real) : term132 x.
Proof. exact (@lem1647159 term97 (term48 x)). Qed.
Lemma lem1647161 (x : real) (h1 : term129 x) : term133 x.
Proof. exact (@lem1647160 x (@lem1647157 x h1)). Qed.
Lemma lem1647162 (x : real) : (term104 x) = (term48 x).
Proof. exact (@lem1483460 (term48 x)). Qed.
Lemma lem1647163 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647164 (x : real) : (term134 x) = (term60 x).
Proof. exact (MK_COMB (@lem1647163) (@lem1647162 x)). Qed.
Lemma lem1647165 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647166 (x : real) : (term133 x) = (term61 x).
Proof. exact (MK_COMB (@lem1647164 x) (@lem1647165)). Qed.
Lemma lem1647167 (x : real) (h1 : term129 x) : term61 x.
Proof. exact (EQ_MP (@lem1647166 x) (@lem1647161 x h1)). Qed.
Lemma lem1647169 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647170 : term91 = term92.
Proof. exact (@lem1647169 (NUMERAL 0) term40). Qed.
Lemma lem1647171 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647172 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647173 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647172 h1) (fun h1 : term92 = True => @lem1647171)). Qed.
Lemma lem1647174 : term92 = True.
Proof. exact (EQ_MP (@lem1647173) (@lem1647171)). Qed.
Lemma lem1647175 : term91 = True.
Proof. exact (TRANS (@lem1647170) (@lem1647174)). Qed.
Lemma lem1647176 : True = term91.
Proof. exact (SYM (@lem1647175)). Qed.
Lemma lem1647177 : term91.
Proof. exact (EQ_MP (@lem1647176) (@lem0)). Qed.
Lemma lem1647178 (x : real) (h1 : term129 x) : term94 x.
Proof. exact (conj (@lem1647177) (@lem1647145 x h1)). Qed.
Lemma lem1647180 (x : real) (y : real) : term95 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647181 (x : real) : term96 x.
Proof. exact (@lem1647180 term97 x). Qed.
Lemma lem1647182 (x : real) (h1 : term129 x) : term98 x.
Proof. exact (@lem1647181 x (@lem1647178 x h1)). Qed.
Lemma lem1647183 (x : real) : (term99 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647185 (x : real) : (term100 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1647184) (@lem1647183 x)). Qed.
Lemma lem1647186 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647187 (x : real) : (term98 x) = (term43 x).
Proof. exact (MK_COMB (@lem1647185 x) (@lem1647186)). Qed.
Lemma lem1647188 (x : real) (h1 : term129 x) : term43 x.
Proof. exact (EQ_MP (@lem1647187 x) (@lem1647182 x h1)). Qed.
Lemma lem1647189 (x : real) (h1 : term129 x) : term135 x.
Proof. exact (conj (@lem1647188 x h1) (@lem1647167 x h1)). Qed.
Lemma lem1647191 (x : real) (y : real) : term136 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1647192 (x : real) : term137 x.
Proof. exact (@lem1647191 x (term48 x)). Qed.
Lemma lem1647193 (x : real) (h1 : term129 x) : term138 x.
Proof. exact (@lem1647192 x (@lem1647189 x h1)). Qed.
Lemma lem1647194 (x : real) : (term139 x) = (term111 x).
Proof. exact (@lem1483442 term112 x). Qed.
Lemma lem1647196 (m : nat) : (term113 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647197 : term114 = term15.
Proof. exact (@lem1647196 term40). Qed.
Lemma lem1647198 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647199 : term115 = term116.
Proof. exact (MK_COMB (@lem1647198) (@lem1647197)). Qed.
Lemma lem1647200 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647201 (x : real) : (term111 x) = (term117 x).
Proof. exact (MK_COMB (@lem1647199) (@lem1647200 x)). Qed.
Lemma lem1647202 (x : real) : (term139 x) = (term117 x).
Proof. exact (TRANS (@lem1647194 x) (@lem1647201 x)). Qed.
Lemma lem1647203 (x : real) : (term117 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647204 (x : real) : (term139 x) = term15.
Proof. exact (TRANS (@lem1647202 x) (@lem1647203 x)). Qed.
Lemma lem1647205 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647206 (x : real) : (term140 x) = term119.
Proof. exact (MK_COMB (@lem1647205) (@lem1647204 x)). Qed.
Lemma lem1647207 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647208 (x : real) : (term138 x) = term120.
Proof. exact (MK_COMB (@lem1647206 x) (@lem1647207)). Qed.
Lemma lem1647209 (x : real) (h1 : term129 x) : term120.
Proof. exact (EQ_MP (@lem1647208 x) (@lem1647193 x h1)). Qed.
Lemma lem1647211 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647212 : term120 = term121.
Proof. exact (@lem1647211 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1647213 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1647214 : term120 = False.
Proof. exact (TRANS (@lem1647212) (@lem1647213)). Qed.
Lemma lem1647215 (x : real) (h1 : term129 x) : False.
Proof. exact (EQ_MP (@lem1647214) (@lem1647209 x h1)). Qed.
Lemma lem1647216 (x : real) (h1 : term141 x) : term141 x.
Proof. exact (h1). Qed.
Lemma lem1647217 (x : real) (h1 : term141 x) : term85 x.
Proof. exact (proj2 (@lem1647216 x h1)). Qed.
Lemma lem1647219 (x : real) (h1 : term141 x) : term51 x.
Proof. exact (proj2 (@lem1647217 x h1)). Qed.
Lemma lem1647220 (x : real) (h1 : term141 x) : term64 x.
Proof. exact (proj1 (@lem1647217 x h1)). Qed.
Lemma lem1647222 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647223 : term91 = term92.
Proof. exact (@lem1647222 (NUMERAL 0) term40). Qed.
Lemma lem1647224 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647225 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647226 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647225 h1) (fun h1 : term92 = True => @lem1647224)). Qed.
Lemma lem1647227 : term92 = True.
Proof. exact (EQ_MP (@lem1647226) (@lem1647224)). Qed.
Lemma lem1647228 : term91 = True.
Proof. exact (TRANS (@lem1647223) (@lem1647227)). Qed.
Lemma lem1647229 : True = term91.
Proof. exact (SYM (@lem1647228)). Qed.
Lemma lem1647230 : term91.
Proof. exact (EQ_MP (@lem1647229) (@lem0)). Qed.
Lemma lem1647231 (x : real) (h1 : term141 x) : term142 x.
Proof. exact (conj (@lem1647230) (@lem1647220 x h1)). Qed.
Lemma lem1647233 (x : real) (y : real) : term131 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1647234 (x : real) : term143 x.
Proof. exact (@lem1647233 term97 x). Qed.
Lemma lem1647235 (x : real) (h1 : term141 x) : term144 x.
Proof. exact (@lem1647234 x (@lem1647231 x h1)). Qed.
Lemma lem1647236 (x : real) : (term99 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647237 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647238 (x : real) : (term145 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1647237) (@lem1647236 x)). Qed.
Lemma lem1647239 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647240 (x : real) : (term144 x) = (term64 x).
Proof. exact (MK_COMB (@lem1647238 x) (@lem1647239)). Qed.
Lemma lem1647241 (x : real) (h1 : term141 x) : term64 x.
Proof. exact (EQ_MP (@lem1647240 x) (@lem1647235 x h1)). Qed.
Lemma lem1647243 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647244 : term91 = term92.
Proof. exact (@lem1647243 (NUMERAL 0) term40). Qed.
Lemma lem1647245 : term93 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647246 (h1 : term93 = (BIT1 0)) : term92 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647247 : (term93 = (BIT1 0)) = (term92 = True).
Proof. exact (prop_ext (fun h1 : term93 = (BIT1 0) => @lem1647246 h1) (fun h1 : term92 = True => @lem1647245)). Qed.
Lemma lem1647248 : term92 = True.
Proof. exact (EQ_MP (@lem1647247) (@lem1647245)). Qed.
Lemma lem1647249 : term91 = True.
Proof. exact (TRANS (@lem1647244) (@lem1647248)). Qed.
Lemma lem1647250 : True = term91.
Proof. exact (SYM (@lem1647249)). Qed.
Lemma lem1647251 : term91.
Proof. exact (EQ_MP (@lem1647250) (@lem0)). Qed.
Lemma lem1647252 (x : real) (h1 : term141 x) : term101 x.
Proof. exact (conj (@lem1647251) (@lem1647219 x h1)). Qed.
Lemma lem1647254 (x : real) (y : real) : term95 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647255 (x : real) : term102 x.
Proof. exact (@lem1647254 term97 (term48 x)). Qed.
Lemma lem1647256 (x : real) (h1 : term141 x) : term103 x.
Proof. exact (@lem1647255 x (@lem1647252 x h1)). Qed.
Lemma lem1647257 (x : real) : (term104 x) = (term48 x).
Proof. exact (@lem1483460 (term48 x)). Qed.
Lemma lem1647258 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647259 (x : real) : (term105 x) = (term50 x).
Proof. exact (MK_COMB (@lem1647258) (@lem1647257 x)). Qed.
Lemma lem1647260 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647261 (x : real) : (term103 x) = (term51 x).
Proof. exact (MK_COMB (@lem1647259 x) (@lem1647260)). Qed.
Lemma lem1647262 (x : real) (h1 : term141 x) : term51 x.
Proof. exact (EQ_MP (@lem1647261 x) (@lem1647256 x h1)). Qed.
Lemma lem1647263 (x : real) (h1 : term141 x) : term146 x.
Proof. exact (conj (@lem1647262 x h1) (@lem1647241 x h1)). Qed.
Lemma lem1647265 (x : real) (y : real) : term136 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1647266 (x : real) : term147 x.
Proof. exact (@lem1647265 (term48 x) x). Qed.
Lemma lem1647267 (x : real) (h1 : term141 x) : term109 x.
Proof. exact (@lem1647266 x (@lem1647263 x h1)). Qed.
Lemma lem1647268 (x : real) : (term110 x) = (term111 x).
Proof. exact (@lem1483440 term112 x). Qed.
Lemma lem1647270 (m : nat) : (term113 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647271 : term114 = term15.
Proof. exact (@lem1647270 term40). Qed.
Lemma lem1647272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647273 : term115 = term116.
Proof. exact (MK_COMB (@lem1647272) (@lem1647271)). Qed.
Lemma lem1647274 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647275 (x : real) : (term111 x) = (term117 x).
Proof. exact (MK_COMB (@lem1647273) (@lem1647274 x)). Qed.
Lemma lem1647276 (x : real) : (term110 x) = (term117 x).
Proof. exact (TRANS (@lem1647268 x) (@lem1647275 x)). Qed.
Lemma lem1647277 (x : real) : (term117 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647278 (x : real) : (term110 x) = term15.
Proof. exact (TRANS (@lem1647276 x) (@lem1647277 x)). Qed.
Lemma lem1647279 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647280 (x : real) : (term118 x) = term119.
Proof. exact (MK_COMB (@lem1647279) (@lem1647278 x)). Qed.
Lemma lem1647281 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1647282 (x : real) : (term109 x) = term120.
Proof. exact (MK_COMB (@lem1647280 x) (@lem1647281)). Qed.
Lemma lem1647283 (x : real) (h1 : term141 x) : term120.
Proof. exact (EQ_MP (@lem1647282 x) (@lem1647267 x h1)). Qed.
Lemma lem1647285 (n : nat) (m : nat) : (term90 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647286 : term120 = term121.
Proof. exact (@lem1647285 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1647287 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1647288 : term120 = False.
Proof. exact (TRANS (@lem1647286) (@lem1647287)). Qed.
Lemma lem1647289 (x : real) (h1 : term141 x) : False.
Proof. exact (EQ_MP (@lem1647288) (@lem1647283 x h1)). Qed.
Lemma lem1647290 (x : real) (h1 : term83 x) : False.
Proof. exact (or_elim (@lem1647141 x h1) (fun h0 : term129 x => @lem1647215 x h0) (fun h0 : term141 x => @lem1647289 x h0)). Qed.
Lemma lem1647291 (x : real) (h1 : term88 x) : False.
Proof. exact (or_elim (@lem1647002 x h1) (fun h0 : term86 x => @lem1647140 x h0) (fun h0 : term83 x => @lem1647290 x h0)). Qed.
Lemma lem1647293 (x : real) (h1 : term88 x) : term88 x.
Proof. exact (h1). Qed.
Lemma lem1647294 (x : real) (h1 : term88 x) : (term88 x) = False.
Proof. exact (prop_ext (fun h2 : term88 x => @lem1647291 x h1) (fun h2 : False => @lem1647293 x h1)). Qed.
Lemma lem1647295 (x : real) (h1 : term88 x) : False.
Proof. exact (EQ_MP (@lem1647294 x h1) (@lem1647293 x h1)). Qed.
Lemma lem1647296 (x : real) (h1 : term32 x) : term32 x.
Proof. exact (h1). Qed.
Lemma lem1647297 (x : real) (h1 : term32 x) : term88 x.
Proof. exact (EQ_MP (@lem1646980 x) (@lem1647296 x h1)). Qed.
Lemma lem1647298 (x : real) (h1 : term32 x) : (term88 x) = False.
Proof. exact (prop_ext (fun h2 : term88 x => @lem1647295 x h2) (fun h2 : False => @lem1647297 x h1)). Qed.
Lemma lem1647299 (x : real) (h1 : term32 x) : False.
Proof. exact (EQ_MP (@lem1647298 x h1) (@lem1647297 x h1)). Qed.
Lemma lem1647300 (x : real) : term148 x.
Proof. exact (fun h0 : term32 x => @lem1647299 x h0). Qed.
Lemma lem1647301 (x : real) : term149 x.
Proof. exact (@lem1386578 ((term33 x) = (term34 x))). Qed.
Lemma lem1647303 (x : real) : term150 x.
Proof. exact (@lem1646060 x). Qed.
Lemma lem1647304 (x : real) : (term150 x) = (term151 x).
Proof. exact (eq_refl (term150 x)). Qed.
Lemma lem1647305 (x : real) : term151 x.
Proof. exact (EQ_MP (@lem1647304 x) (@lem1647303 x)). Qed.
Lemma lem1647306 (x : real) : (term151 x) = ((term151 x) = True).
Proof. exact (@lem7 (term151 x)). Qed.
Lemma lem1647315 (x : real) : (term33 x) = (term34 x).
Proof. exact (@lem1647301 x (@lem1647300 x)). Qed.
Lemma lem1647316 (x : real) : (term152 x) = (term153 x).
Proof. exact (@lem1647315 (term154 x)). Qed.
Lemma lem1647320 (x : real) : (term151 x) = True.
Proof. exact (EQ_MP (@lem1647306 x) (@lem1647305 x)). Qed.
Lemma lem1647321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1647322 (x : real) : (term155 x) = (and True).
Proof. exact (MK_COMB (@lem1647321) (@lem1647320 x)). Qed.
Lemma lem1647325 (x : real) : (term156 x) = (term156 x).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1647326 (x : real) : (term153 x) = (term157 x).
Proof. exact (MK_COMB (@lem1647322 x) (@lem1647325 x)). Qed.
Lemma lem1647328 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1647329 (x : real) : (term157 x) = (term156 x).
Proof. exact (@lem1647328 (term156 x)). Qed.
Lemma lem1647332 (x : real) : (term153 x) = (term156 x).
Proof. exact (TRANS (@lem1647326 x) (@lem1647329 x)). Qed.
Lemma lem1647333 (x : real) : (term152 x) = (term156 x).
Proof. exact (TRANS (@lem1647316 x) (@lem1647332 x)). Qed.
Lemma lem1647334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1647335 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1647334) (@lem1647333 x)). Qed.
Lemma lem1647338 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1647339 (x : real) : ((term152 x) = (term23 x)) = ((term156 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1647335 x) (@lem1647338 x)). Qed.
Lemma lem1647342 : term160 = term161.
Proof. exact (fun_ext (fun x : real => @lem1647339 x)). Qed.
Lemma lem1647343 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1647344 : term162 = term163.
Proof. exact (MK_COMB (@lem1647343) (@lem1647342)). Qed.
Lemma lem1647349 : term163 = term162.
Proof. exact (SYM (@lem1647344)). Qed.
Lemma lem1647357 (x : real) (n : nat) : ((real_pow x n) = term15) = (term16 x n).
Proof. exact (EQ_MP (@lem1646709 x n) (@lem1646708 x n)). Qed.
Lemma lem1647358 (x : real) : ((term154 x) = term15) = (term164 x).
Proof. exact (@lem1647357 x term165). Qed.
Lemma lem1647364 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1646453 m n) (@lem1646452 m n)). Qed.
Lemma lem1647365 : (term165 = (NUMERAL 0)) = (term166 = 0).
Proof. exact (@lem1647364 term166 0). Qed.
Lemma lem1647367 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1646445 n) (@lem1646444 n)). Qed.
Lemma lem1647368 : (term166 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1647367 (BIT1 0)). Qed.
Lemma lem1647370 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1646441 n) (@lem1646440 n)). Qed.
Lemma lem1647371 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1647370 0). Qed.
Lemma lem1647372 : (term166 = 0) = False.
Proof. exact (TRANS (@lem1647368) (@lem1647371)). Qed.
Lemma lem1647373 : (term165 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1647365) (@lem1647372)). Qed.
Lemma lem1647374 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1647375 : term167 = (~ False).
Proof. exact (MK_COMB (@lem1647374) (@lem1647373)). Qed.
Lemma lem1647377 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1647378 : term167 = True.
Proof. exact (TRANS (@lem1647375) (@lem1647377)). Qed.
Lemma lem1647379 (x : real) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1647380 (x : real) : (term164 x) = (term169 x).
Proof. exact (MK_COMB (@lem1647379 x) (@lem1647378)). Qed.
Lemma lem1647382 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1647383 (x : real) : (term169 x) = (x = term15).
Proof. exact (@lem1647382 (x = term15)). Qed.
Lemma lem1647386 (x : real) : (term164 x) = (x = term15).
Proof. exact (TRANS (@lem1647380 x) (@lem1647383 x)). Qed.
Lemma lem1647387 (x : real) : ((term154 x) = term15) = (x = term15).
Proof. exact (TRANS (@lem1647358 x) (@lem1647386 x)). Qed.
Lemma lem1647388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1647389 (x : real) : (term156 x) = (term23 x).
Proof. exact (MK_COMB (@lem1647388) (@lem1647387 x)). Qed.
Lemma lem1647390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1647391 (x : real) : (term159 x) = (term170 x).
Proof. exact (MK_COMB (@lem1647390) (@lem1647389 x)). Qed.
Lemma lem1647394 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1647395 (x : real) : ((term156 x) = (term23 x)) = ((term23 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1647391 x) (@lem1647394 x)). Qed.
Lemma lem1647397 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1647398 (x : Prop) : (x = x) = True.
Proof. exact (@lem1647397 Prop x). Qed.
Lemma lem1647399 (x : real) : ((term23 x) = (term23 x)) = True.
Proof. exact (@lem1647398 (term23 x)). Qed.
Lemma lem1647400 (x : real) : ((term156 x) = (term23 x)) = True.
Proof. exact (TRANS (@lem1647395 x) (@lem1647399 x)). Qed.
Lemma lem1647401 : term161 = term171.
Proof. exact (fun_ext (fun x : real => @lem1647400 x)). Qed.
Lemma lem1647402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1647403 : term163 = term172.
Proof. exact (MK_COMB (@lem1647402) (@lem1647401)). Qed.
Lemma lem1647405 {A : Type'} (t : Prop) : (term173 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1647406 (t : Prop) : (term174 t) = t.
Proof. exact (@lem1647405 real t). Qed.
Lemma lem1647407 : term172 = True.
Proof. exact (@lem1647406 True). Qed.
Lemma lem1647408 : term163 = True.
Proof. exact (TRANS (@lem1647403) (@lem1647407)). Qed.
Lemma lem1647409 : True = term163.
Proof. exact (SYM (@lem1647408)). Qed.
Lemma lem1647410 : term163.
Proof. exact (EQ_MP (@lem1647409) (@lem0)). Qed.
Lemma lem1647411 : term162.
Proof. exact (EQ_MP (@lem1647349) (@lem1647410)). Qed.

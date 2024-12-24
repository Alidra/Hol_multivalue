Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_POW_2_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_POS_spec.
Require Import REAL_ABS_ZERO_spec.
Require Import REAL_LE_POW_2_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW_EQ_0_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm14781_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm15222_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1758433 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1758434 : term1.
Proof. exact (proj2 (@lem1758433)). Qed.
Lemma lem1758435 : term2.
Proof. exact (proj2 (@lem1758434)). Qed.
Lemma lem1758436 : term3.
Proof. exact (proj2 (@lem1758435)). Qed.
Lemma lem1758478 : term4.
Proof. exact (proj1 (@lem1758436)). Qed.
Lemma lem1758479 (n : nat) : term5 n.
Proof. exact (@lem1758478 n). Qed.
Lemma lem1758480 (n : nat) : (term5 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1758482 : term6.
Proof. exact (proj1 (@lem1758435)). Qed.
Lemma lem1758483 (n : nat) : term7 n.
Proof. exact (@lem1758482 n). Qed.
Lemma lem1758484 (n : nat) : (term7 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1758487 : term8.
Proof. exact (proj1 (@lem1758433)). Qed.
Lemma lem1758488 (m : nat) : term9 m.
Proof. exact (@lem1758487 m). Qed.
Lemma lem1758489 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1758490 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1758489 m) (@lem1758488 m)). Qed.
Lemma lem1758491 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1758490 m n). Qed.
Lemma lem1758492 (m : nat) (n : nat) : (term11 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1758744 (x : real) : term12 x.
Proof. exact (@lem1527966 x). Qed.
Lemma lem1758745 (x : real) : (term12 x) = (((real_abs x) = term13) = (x = term13)).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1758747 (x : real) : term14 x.
Proof. exact (@lem1630283 x). Qed.
Lemma lem1758748 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1758749 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1758748 x) (@lem1758747 x)). Qed.
Lemma lem1758750 (x : real) (n : nat) : term16 x n.
Proof. exact (@lem1758749 x n). Qed.
Lemma lem1758751 (x : real) (n : nat) : (term16 x n) = (((real_pow x n) = term13) = (term17 x n)).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1758773 (x : real) : (term18 x) = (term19 x).
Proof. exact (@lem17646 (term20 x) (x = term13)). Qed.
Lemma lem1758775 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1758776 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1758775 x) (@lem1758773 x)). Qed.
Lemma lem1758777 (x : real) : (term24 x) = (term22 x).
Proof. exact (@lem17362 (term25 x) ((term20 x) = (x = term13))). Qed.
Lemma lem1758801 (x : real) : (term24 x) = (term23 x).
Proof. exact (TRANS (@lem1758777 x) (@lem1758776 x)). Qed.
Lemma lem1758802 (x : real) : (term25 x) = (term26 x).
Proof. exact (@lem1483523 x term13). Qed.
Lemma lem1758808 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1483519 x term13). Qed.
Lemma lem1758810 (x : nat) : (term29 x) = term13.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1758811 : term30 = term13.
Proof. exact (@lem1758810 term31). Qed.
Lemma lem1758812 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1758813 (x : real) : (term28 x) = (term32 x).
Proof. exact (MK_COMB (@lem1758812 x) (@lem1758811)). Qed.
Lemma lem1758814 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1758815 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1758813 x) (@lem1758814 x)). Qed.
Lemma lem1758817 (x : real) : (term27 x) = x.
Proof. exact (TRANS (@lem1758808 x) (@lem1758815 x)). Qed.
Lemma lem1758818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1758819 (x : real) : (term33 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1758818) (@lem1758817 x)). Qed.
Lemma lem1758820 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758821 (x : real) : (term26 x) = (term34 x).
Proof. exact (MK_COMB (@lem1758819 x) (@lem1758820)). Qed.
Lemma lem1758822 (x : real) : (term25 x) = (term34 x).
Proof. exact (TRANS (@lem1758802 x) (@lem1758821 x)). Qed.
Lemma lem1758823 (x : real) : (term20 x) = (term35 x).
Proof. exact (@lem1483523 term13 x). Qed.
Lemma lem1758829 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483519 term13 x). Qed.
Lemma lem1758834 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1483448 (term38 x)). Qed.
Lemma lem1758836 (x : real) : (term36 x) = (term38 x).
Proof. exact (TRANS (@lem1758829 x) (@lem1758834 x)). Qed.
Lemma lem1758837 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1758838 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1758837) (@lem1758836 x)). Qed.
Lemma lem1758839 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758840 (x : real) : (term35 x) = (term41 x).
Proof. exact (MK_COMB (@lem1758838 x) (@lem1758839)). Qed.
Lemma lem1758841 (x : real) : (term20 x) = (term41 x).
Proof. exact (TRANS (@lem1758823 x) (@lem1758840 x)). Qed.
Lemma lem1758842 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483554 x term13). Qed.
Lemma lem1758848 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1483519 x term13). Qed.
Lemma lem1758850 (x : nat) : (term29 x) = term13.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1758851 : term30 = term13.
Proof. exact (@lem1758850 term31). Qed.
Lemma lem1758852 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1758853 (x : real) : (term28 x) = (term32 x).
Proof. exact (MK_COMB (@lem1758852 x) (@lem1758851)). Qed.
Lemma lem1758854 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1758855 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1758853 x) (@lem1758854 x)). Qed.
Lemma lem1758857 (x : real) : (term27 x) = x.
Proof. exact (TRANS (@lem1758848 x) (@lem1758855 x)). Qed.
Lemma lem1758858 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1758859 (x : real) : (term44 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1758858) (@lem1758857 x)). Qed.
Lemma lem1758862 (x : real) : (real_neg x) = (term38 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1758863 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1758864 (x : real) : ((term44 x) = (real_neg x)) = ((term44 x) = (term38 x)).
Proof. exact (MK_COMB (@lem1758863 x) (@lem1758862 x)). Qed.
Lemma lem1758865 (x : real) : (term44 x) = (term38 x).
Proof. exact (EQ_MP (@lem1758864 x) (@lem1758859 x)). Qed.
Lemma lem1758866 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1758867 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1758866) (@lem1758865 x)). Qed.
Lemma lem1758868 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758869 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1758867 x) (@lem1758868)). Qed.
Lemma lem1758870 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1758871 (x : real) : (term50 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1758870) (@lem1758857 x)). Qed.
Lemma lem1758872 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758873 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1758871 x) (@lem1758872)). Qed.
Lemma lem1758874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1758875 (x : real) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem1758874) (@lem1758873 x)). Qed.
Lemma lem1758876 (x : real) : (term43 x) = (term55 x).
Proof. exact (MK_COMB (@lem1758875 x) (@lem1758869 x)). Qed.
Lemma lem1758877 (x : real) : (term42 x) = (term55 x).
Proof. exact (TRANS (@lem1758842 x) (@lem1758876 x)). Qed.
Lemma lem1758878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1758879 (x : real) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem1758878) (@lem1758841 x)). Qed.
Lemma lem1758880 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem1758879 x) (@lem1758877 x)). Qed.
Lemma lem1758881 (x : real) : (term60 x) = (term51 x).
Proof. exact (@lem1483533 x term13). Qed.
Lemma lem1758887 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1483519 x term13). Qed.
Lemma lem1758889 (x : nat) : (term29 x) = term13.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1758890 : term30 = term13.
Proof. exact (@lem1758889 term31). Qed.
Lemma lem1758891 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1758892 (x : real) : (term28 x) = (term32 x).
Proof. exact (MK_COMB (@lem1758891 x) (@lem1758890)). Qed.
Lemma lem1758893 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1758894 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1758892 x) (@lem1758893 x)). Qed.
Lemma lem1758896 (x : real) : (term27 x) = x.
Proof. exact (TRANS (@lem1758887 x) (@lem1758894 x)). Qed.
Lemma lem1758897 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1758898 (x : real) : (term50 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1758897) (@lem1758896 x)). Qed.
Lemma lem1758899 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758900 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1758898 x) (@lem1758899)). Qed.
Lemma lem1758901 (x : real) : (term60 x) = (term52 x).
Proof. exact (TRANS (@lem1758881 x) (@lem1758900 x)). Qed.
Lemma lem1758902 (x : real) : (x = term13) = ((term27 x) = term13).
Proof. exact (@lem1483529 x term13). Qed.
Lemma lem1758908 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1483519 x term13). Qed.
Lemma lem1758910 (x : nat) : (term29 x) = term13.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1758911 : term30 = term13.
Proof. exact (@lem1758910 term31). Qed.
Lemma lem1758912 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1758913 (x : real) : (term28 x) = (term32 x).
Proof. exact (MK_COMB (@lem1758912 x) (@lem1758911)). Qed.
Lemma lem1758914 (x : real) : (term32 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1758915 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1758913 x) (@lem1758914 x)). Qed.
Lemma lem1758917 (x : real) : (term27 x) = x.
Proof. exact (TRANS (@lem1758908 x) (@lem1758915 x)). Qed.
Lemma lem1758918 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1758919 (x : real) : (term61 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1758918) (@lem1758917 x)). Qed.
Lemma lem1758920 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1758921 (x : real) : ((term27 x) = term13) = (x = term13).
Proof. exact (MK_COMB (@lem1758919 x) (@lem1758920)). Qed.
Lemma lem1758922 (x : real) : (x = term13) = (x = term13).
Proof. exact (TRANS (@lem1758902 x) (@lem1758921 x)). Qed.
Lemma lem1758923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1758924 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1758923) (@lem1758901 x)). Qed.
Lemma lem1758925 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1758924 x) (@lem1758922 x)). Qed.
Lemma lem1758926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1758927 (x : real) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem1758926) (@lem1758880 x)). Qed.
Lemma lem1758928 (x : real) : (term19 x) = (term68 x).
Proof. exact (MK_COMB (@lem1758927 x) (@lem1758925 x)). Qed.
Lemma lem1758929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1758930 (x : real) : (term21 x) = (term69 x).
Proof. exact (MK_COMB (@lem1758929) (@lem1758822 x)). Qed.
Lemma lem1758931 (x : real) : (term23 x) = (term70 x).
Proof. exact (MK_COMB (@lem1758930 x) (@lem1758928 x)). Qed.
Lemma lem1758938 (x : real) : (term24 x) = (term70 x).
Proof. exact (TRANS (@lem1758801 x) (@lem1758931 x)). Qed.
Lemma lem1758945 (x : real) : (term65 x) = (term65 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1758962 (x : real) : (term59 x) = (term71 x).
Proof. exact (@lem19158 (term52 x) (term41 x) (term49 x)). Qed.
Lemma lem1758963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1758964 (x : real) : (term67 x) = (term72 x).
Proof. exact (MK_COMB (@lem1758963) (@lem1758962 x)). Qed.
Lemma lem1758965 (x : real) : (term68 x) = (term73 x).
Proof. exact (MK_COMB (@lem1758964 x) (@lem1758945 x)). Qed.
Lemma lem1758968 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1758969 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1758968 x) (@lem1758965 x)). Qed.
Lemma lem1758970 (x : real) : (term74 x) = (term75 x).
Proof. exact (@lem19158 (term71 x) (term34 x) (term65 x)). Qed.
Lemma lem1758971 (x : real) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1758978 (x : real) : (term77 x) = (term78 x).
Proof. exact (@lem19158 (term79 x) (term34 x) (term80 x)). Qed.
Lemma lem1758979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1758980 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1758979) (@lem1758978 x)). Qed.
Lemma lem1758981 (x : real) : (term75 x) = (term83 x).
Proof. exact (MK_COMB (@lem1758980 x) (@lem1758971 x)). Qed.
Lemma lem1758982 (x : real) : (term74 x) = (term83 x).
Proof. exact (TRANS (@lem1758970 x) (@lem1758981 x)). Qed.
Lemma lem1758983 (x : real) : (term70 x) = (term83 x).
Proof. exact (TRANS (@lem1758969 x) (@lem1758982 x)). Qed.
Lemma lem1758984 (x : real) : (term24 x) = (term83 x).
Proof. exact (TRANS (@lem1758938 x) (@lem1758983 x)). Qed.
Lemma lem1759000 (x : real) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1759001 (x : real) (h1 : term78 x) : term78 x.
Proof. exact (h1). Qed.
Lemma lem1759002 (x : real) (h1 : term84 x) : term84 x.
Proof. exact (h1). Qed.
Lemma lem1759003 (x : real) (h1 : term84 x) : term79 x.
Proof. exact (proj2 (@lem1759002 x h1)). Qed.
Lemma lem1759005 (x : real) (h1 : term84 x) : term52 x.
Proof. exact (proj2 (@lem1759003 x h1)). Qed.
Lemma lem1759006 (x : real) (h1 : term84 x) : term41 x.
Proof. exact (proj1 (@lem1759003 x h1)). Qed.
Lemma lem1759008 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759009 : term86 = term87.
Proof. exact (@lem1759008 (NUMERAL 0) term31). Qed.
Lemma lem1759010 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1759011 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1759012 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1759011 h1) (fun h1 : term87 = True => @lem1759010)). Qed.
Lemma lem1759013 : term87 = True.
Proof. exact (EQ_MP (@lem1759012) (@lem1759010)). Qed.
Lemma lem1759014 : term86 = True.
Proof. exact (TRANS (@lem1759009) (@lem1759013)). Qed.
Lemma lem1759015 : True = term86.
Proof. exact (SYM (@lem1759014)). Qed.
Lemma lem1759016 : term86.
Proof. exact (EQ_MP (@lem1759015) (@lem0)). Qed.
Lemma lem1759017 (x : real) (h1 : term84 x) : term89 x.
Proof. exact (conj (@lem1759016) (@lem1759006 x h1)). Qed.
Lemma lem1759019 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1759020 (x : real) : term91 x.
Proof. exact (@lem1759019 term92 (term38 x)). Qed.
Lemma lem1759021 (x : real) (h1 : term84 x) : term93 x.
Proof. exact (@lem1759020 x (@lem1759017 x h1)). Qed.
Lemma lem1759022 (x : real) : (term94 x) = (term38 x).
Proof. exact (@lem1483460 (term38 x)). Qed.
Lemma lem1759023 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1759024 (x : real) : (term95 x) = (term40 x).
Proof. exact (MK_COMB (@lem1759023) (@lem1759022 x)). Qed.
Lemma lem1759025 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759026 (x : real) : (term93 x) = (term41 x).
Proof. exact (MK_COMB (@lem1759024 x) (@lem1759025)). Qed.
Lemma lem1759027 (x : real) (h1 : term84 x) : term41 x.
Proof. exact (EQ_MP (@lem1759026 x) (@lem1759021 x h1)). Qed.
Lemma lem1759029 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759030 : term86 = term87.
Proof. exact (@lem1759029 (NUMERAL 0) term31). Qed.
Lemma lem1759031 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1759032 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1759033 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1759032 h1) (fun h1 : term87 = True => @lem1759031)). Qed.
Lemma lem1759034 : term87 = True.
Proof. exact (EQ_MP (@lem1759033) (@lem1759031)). Qed.
Lemma lem1759035 : term86 = True.
Proof. exact (TRANS (@lem1759030) (@lem1759034)). Qed.
Lemma lem1759036 : True = term86.
Proof. exact (SYM (@lem1759035)). Qed.
Lemma lem1759037 : term86.
Proof. exact (EQ_MP (@lem1759036) (@lem0)). Qed.
Lemma lem1759038 (x : real) (h1 : term84 x) : term96 x.
Proof. exact (conj (@lem1759037) (@lem1759005 x h1)). Qed.
Lemma lem1759040 (x : real) (y : real) : term97 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1759041 (x : real) : term98 x.
Proof. exact (@lem1759040 term92 x). Qed.
Lemma lem1759042 (x : real) (h1 : term84 x) : term99 x.
Proof. exact (@lem1759041 x (@lem1759038 x h1)). Qed.
Lemma lem1759043 (x : real) : (term100 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1759044 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759045 (x : real) : (term101 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1759044) (@lem1759043 x)). Qed.
Lemma lem1759046 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759047 (x : real) : (term99 x) = (term52 x).
Proof. exact (MK_COMB (@lem1759045 x) (@lem1759046)). Qed.
Lemma lem1759048 (x : real) (h1 : term84 x) : term52 x.
Proof. exact (EQ_MP (@lem1759047 x) (@lem1759042 x h1)). Qed.
Lemma lem1759049 (x : real) (h1 : term84 x) : term102 x.
Proof. exact (conj (@lem1759048 x h1) (@lem1759027 x h1)). Qed.
Lemma lem1759051 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1759052 (x : real) : term104 x.
Proof. exact (@lem1759051 x (term38 x)). Qed.
Lemma lem1759053 (x : real) (h1 : term84 x) : term105 x.
Proof. exact (@lem1759052 x (@lem1759049 x h1)). Qed.
Lemma lem1759054 (x : real) : (term106 x) = (term107 x).
Proof. exact (@lem1483442 term108 x). Qed.
Lemma lem1759056 (m : nat) : (term109 m) = term13.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1759057 : term110 = term13.
Proof. exact (@lem1759056 term31). Qed.
Lemma lem1759058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1759059 : term111 = term112.
Proof. exact (MK_COMB (@lem1759058) (@lem1759057)). Qed.
Lemma lem1759060 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1759061 (x : real) : (term107 x) = (term113 x).
Proof. exact (MK_COMB (@lem1759059) (@lem1759060 x)). Qed.
Lemma lem1759062 (x : real) : (term106 x) = (term113 x).
Proof. exact (TRANS (@lem1759054 x) (@lem1759061 x)). Qed.
Lemma lem1759063 (x : real) : (term113 x) = term13.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1759064 (x : real) : (term106 x) = term13.
Proof. exact (TRANS (@lem1759062 x) (@lem1759063 x)). Qed.
Lemma lem1759065 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759066 (x : real) : (term114 x) = term115.
Proof. exact (MK_COMB (@lem1759065) (@lem1759064 x)). Qed.
Lemma lem1759067 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759068 (x : real) : (term105 x) = term116.
Proof. exact (MK_COMB (@lem1759066 x) (@lem1759067)). Qed.
Lemma lem1759069 (x : real) (h1 : term84 x) : term116.
Proof. exact (EQ_MP (@lem1759068 x) (@lem1759053 x h1)). Qed.
Lemma lem1759071 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759072 : term116 = term117.
Proof. exact (@lem1759071 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1759073 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1759074 : term116 = False.
Proof. exact (TRANS (@lem1759072) (@lem1759073)). Qed.
Lemma lem1759075 (x : real) (h1 : term84 x) : False.
Proof. exact (EQ_MP (@lem1759074) (@lem1759069 x h1)). Qed.
Lemma lem1759076 (x : real) (h1 : term118 x) : term118 x.
Proof. exact (h1). Qed.
Lemma lem1759077 (x : real) (h1 : term118 x) : term80 x.
Proof. exact (proj2 (@lem1759076 x h1)). Qed.
Lemma lem1759078 (x : real) (h1 : term118 x) : term34 x.
Proof. exact (proj1 (@lem1759076 x h1)). Qed.
Lemma lem1759079 (x : real) (h1 : term118 x) : term49 x.
Proof. exact (proj2 (@lem1759077 x h1)). Qed.
Lemma lem1759082 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759083 : term86 = term87.
Proof. exact (@lem1759082 (NUMERAL 0) term31). Qed.
Lemma lem1759084 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1759085 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1759086 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1759085 h1) (fun h1 : term87 = True => @lem1759084)). Qed.
Lemma lem1759087 : term87 = True.
Proof. exact (EQ_MP (@lem1759086) (@lem1759084)). Qed.
Lemma lem1759088 : term86 = True.
Proof. exact (TRANS (@lem1759083) (@lem1759087)). Qed.
Lemma lem1759089 : True = term86.
Proof. exact (SYM (@lem1759088)). Qed.
Lemma lem1759090 : term86.
Proof. exact (EQ_MP (@lem1759089) (@lem0)). Qed.
Lemma lem1759091 (x : real) (h1 : term118 x) : term119 x.
Proof. exact (conj (@lem1759090) (@lem1759078 x h1)). Qed.
Lemma lem1759093 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1759094 (x : real) : term120 x.
Proof. exact (@lem1759093 term92 x). Qed.
Lemma lem1759095 (x : real) (h1 : term118 x) : term121 x.
Proof. exact (@lem1759094 x (@lem1759091 x h1)). Qed.
Lemma lem1759096 (x : real) : (term100 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1759097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1759098 (x : real) : (term122 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1759097) (@lem1759096 x)). Qed.
Lemma lem1759099 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759100 (x : real) : (term121 x) = (term34 x).
Proof. exact (MK_COMB (@lem1759098 x) (@lem1759099)). Qed.
Lemma lem1759101 (x : real) (h1 : term118 x) : term34 x.
Proof. exact (EQ_MP (@lem1759100 x) (@lem1759095 x h1)). Qed.
Lemma lem1759103 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759104 : term86 = term87.
Proof. exact (@lem1759103 (NUMERAL 0) term31). Qed.
Lemma lem1759105 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1759106 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1759107 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1759106 h1) (fun h1 : term87 = True => @lem1759105)). Qed.
Lemma lem1759108 : term87 = True.
Proof. exact (EQ_MP (@lem1759107) (@lem1759105)). Qed.
Lemma lem1759109 : term86 = True.
Proof. exact (TRANS (@lem1759104) (@lem1759108)). Qed.
Lemma lem1759110 : True = term86.
Proof. exact (SYM (@lem1759109)). Qed.
Lemma lem1759111 : term86.
Proof. exact (EQ_MP (@lem1759110) (@lem0)). Qed.
Lemma lem1759112 (x : real) (h1 : term118 x) : term123 x.
Proof. exact (conj (@lem1759111) (@lem1759079 x h1)). Qed.
Lemma lem1759114 (x : real) (y : real) : term97 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1759115 (x : real) : term124 x.
Proof. exact (@lem1759114 term92 (term38 x)). Qed.
Lemma lem1759116 (x : real) (h1 : term118 x) : term125 x.
Proof. exact (@lem1759115 x (@lem1759112 x h1)). Qed.
Lemma lem1759117 (x : real) : (term94 x) = (term38 x).
Proof. exact (@lem1483460 (term38 x)). Qed.
Lemma lem1759118 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759119 (x : real) : (term126 x) = (term47 x).
Proof. exact (MK_COMB (@lem1759118) (@lem1759117 x)). Qed.
Lemma lem1759120 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759121 (x : real) : (term125 x) = (term49 x).
Proof. exact (MK_COMB (@lem1759119 x) (@lem1759120)). Qed.
Lemma lem1759122 (x : real) (h1 : term118 x) : term49 x.
Proof. exact (EQ_MP (@lem1759121 x) (@lem1759116 x h1)). Qed.
Lemma lem1759123 (x : real) (h1 : term118 x) : term127 x.
Proof. exact (conj (@lem1759122 x h1) (@lem1759101 x h1)). Qed.
Lemma lem1759125 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1759126 (x : real) : term128 x.
Proof. exact (@lem1759125 (term38 x) x). Qed.
Lemma lem1759127 (x : real) (h1 : term118 x) : term129 x.
Proof. exact (@lem1759126 x (@lem1759123 x h1)). Qed.
Lemma lem1759128 (x : real) : (term130 x) = (term107 x).
Proof. exact (@lem1483440 term108 x). Qed.
Lemma lem1759130 (m : nat) : (term109 m) = term13.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1759131 : term110 = term13.
Proof. exact (@lem1759130 term31). Qed.
Lemma lem1759132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1759133 : term111 = term112.
Proof. exact (MK_COMB (@lem1759132) (@lem1759131)). Qed.
Lemma lem1759134 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1759135 (x : real) : (term107 x) = (term113 x).
Proof. exact (MK_COMB (@lem1759133) (@lem1759134 x)). Qed.
Lemma lem1759136 (x : real) : (term130 x) = (term113 x).
Proof. exact (TRANS (@lem1759128 x) (@lem1759135 x)). Qed.
Lemma lem1759137 (x : real) : (term113 x) = term13.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1759138 (x : real) : (term130 x) = term13.
Proof. exact (TRANS (@lem1759136 x) (@lem1759137 x)). Qed.
Lemma lem1759139 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759140 (x : real) : (term131 x) = term115.
Proof. exact (MK_COMB (@lem1759139) (@lem1759138 x)). Qed.
Lemma lem1759141 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759142 (x : real) : (term129 x) = term116.
Proof. exact (MK_COMB (@lem1759140 x) (@lem1759141)). Qed.
Lemma lem1759143 (x : real) (h1 : term118 x) : term116.
Proof. exact (EQ_MP (@lem1759142 x) (@lem1759127 x h1)). Qed.
Lemma lem1759145 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759146 : term116 = term117.
Proof. exact (@lem1759145 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1759147 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1759148 : term116 = False.
Proof. exact (TRANS (@lem1759146) (@lem1759147)). Qed.
Lemma lem1759149 (x : real) (h1 : term118 x) : False.
Proof. exact (EQ_MP (@lem1759148) (@lem1759143 x h1)). Qed.
Lemma lem1759150 (x : real) (h1 : term78 x) : False.
Proof. exact (or_elim (@lem1759001 x h1) (fun h0 : term84 x => @lem1759075 x h0) (fun h0 : term118 x => @lem1759149 x h0)). Qed.
Lemma lem1759151 (x : real) (h1 : term76 x) : term76 x.
Proof. exact (h1). Qed.
Lemma lem1759152 (x : real) (h1 : term76 x) : term65 x.
Proof. exact (proj2 (@lem1759151 x h1)). Qed.
Lemma lem1759154 (x : real) (h1 : term76 x) : x = term13.
Proof. exact (proj2 (@lem1759152 x h1)). Qed.
Lemma lem1759155 (x : real) (h1 : term76 x) : term52 x.
Proof. exact (proj1 (@lem1759152 x h1)). Qed.
Lemma lem1759157 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759158 : term86 = term87.
Proof. exact (@lem1759157 (NUMERAL 0) term31). Qed.
Lemma lem1759159 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1759160 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1759161 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1759160 h1) (fun h1 : term87 = True => @lem1759159)). Qed.
Lemma lem1759162 : term87 = True.
Proof. exact (EQ_MP (@lem1759161) (@lem1759159)). Qed.
Lemma lem1759163 : term86 = True.
Proof. exact (TRANS (@lem1759158) (@lem1759162)). Qed.
Lemma lem1759164 : True = term86.
Proof. exact (SYM (@lem1759163)). Qed.
Lemma lem1759165 : term86.
Proof. exact (EQ_MP (@lem1759164) (@lem0)). Qed.
Lemma lem1759166 (x : real) (h1 : term76 x) : term96 x.
Proof. exact (conj (@lem1759165) (@lem1759155 x h1)). Qed.
Lemma lem1759168 (x : real) (y : real) : term97 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1759169 (x : real) : term98 x.
Proof. exact (@lem1759168 term92 x). Qed.
Lemma lem1759170 (x : real) (h1 : term76 x) : term99 x.
Proof. exact (@lem1759169 x (@lem1759166 x h1)). Qed.
Lemma lem1759171 (x : real) : (term100 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1759172 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759173 (x : real) : (term101 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1759172) (@lem1759171 x)). Qed.
Lemma lem1759174 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759175 (x : real) : (term99 x) = (term52 x).
Proof. exact (MK_COMB (@lem1759173 x) (@lem1759174)). Qed.
Lemma lem1759176 (x : real) (h1 : term76 x) : term52 x.
Proof. exact (EQ_MP (@lem1759175 x) (@lem1759170 x h1)). Qed.
Lemma lem1759178 (y : real) : term132 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1759179 (x : real) : term132 x.
Proof. exact (@lem1759178 x). Qed.
Lemma lem1759180 (x : real) (h1 : term76 x) : term133 x.
Proof. exact (@lem1759179 x (@lem1759154 x h1)). Qed.
Lemma lem1759181 (x : real) (h1 : term76 x) : term134 x.
Proof. exact (@lem1759180 x h1 term108). Qed.
Lemma lem1759182 (x : real) : (term134 x) = ((term38 x) = term13).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1759189 (x : real) (h1 : term76 x) : (term38 x) = term13.
Proof. exact (EQ_MP (@lem1759182 x) (@lem1759181 x h1)). Qed.
Lemma lem1759190 (x : real) (h1 : term76 x) : term135 x.
Proof. exact (conj (@lem1759189 x h1) (@lem1759176 x h1)). Qed.
Lemma lem1759192 (x : real) (y : real) : term136 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1759193 (x : real) : term137 x.
Proof. exact (@lem1759192 (term38 x) x). Qed.
Lemma lem1759194 (x : real) (h1 : term76 x) : term129 x.
Proof. exact (@lem1759193 x (@lem1759190 x h1)). Qed.
Lemma lem1759195 (x : real) : (term130 x) = (term107 x).
Proof. exact (@lem1483440 term108 x). Qed.
Lemma lem1759197 (m : nat) : (term109 m) = term13.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1759198 : term110 = term13.
Proof. exact (@lem1759197 term31). Qed.
Lemma lem1759199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1759200 : term111 = term112.
Proof. exact (MK_COMB (@lem1759199) (@lem1759198)). Qed.
Lemma lem1759201 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1759202 (x : real) : (term107 x) = (term113 x).
Proof. exact (MK_COMB (@lem1759200) (@lem1759201 x)). Qed.
Lemma lem1759203 (x : real) : (term130 x) = (term113 x).
Proof. exact (TRANS (@lem1759195 x) (@lem1759202 x)). Qed.
Lemma lem1759204 (x : real) : (term113 x) = term13.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1759205 (x : real) : (term130 x) = term13.
Proof. exact (TRANS (@lem1759203 x) (@lem1759204 x)). Qed.
Lemma lem1759206 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1759207 (x : real) : (term131 x) = term115.
Proof. exact (MK_COMB (@lem1759206) (@lem1759205 x)). Qed.
Lemma lem1759208 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759209 (x : real) : (term129 x) = term116.
Proof. exact (MK_COMB (@lem1759207 x) (@lem1759208)). Qed.
Lemma lem1759210 (x : real) (h1 : term76 x) : term116.
Proof. exact (EQ_MP (@lem1759209 x) (@lem1759194 x h1)). Qed.
Lemma lem1759212 (n : nat) (m : nat) : (term85 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1759213 : term116 = term117.
Proof. exact (@lem1759212 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1759214 : term117 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1759215 : term116 = False.
Proof. exact (TRANS (@lem1759213) (@lem1759214)). Qed.
Lemma lem1759216 (x : real) (h1 : term76 x) : False.
Proof. exact (EQ_MP (@lem1759215) (@lem1759210 x h1)). Qed.
Lemma lem1759217 (x : real) (h1 : term83 x) : False.
Proof. exact (or_elim (@lem1759000 x h1) (fun h0 : term78 x => @lem1759150 x h0) (fun h0 : term76 x => @lem1759216 x h0)). Qed.
Lemma lem1759219 (x : real) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1759220 (x : real) (h1 : term83 x) : (term83 x) = False.
Proof. exact (prop_ext (fun h2 : term83 x => @lem1759217 x h1) (fun h2 : False => @lem1759219 x h1)). Qed.
Lemma lem1759221 (x : real) (h1 : term83 x) : False.
Proof. exact (EQ_MP (@lem1759220 x h1) (@lem1759219 x h1)). Qed.
Lemma lem1759222 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1759223 (x : real) (h1 : term24 x) : term83 x.
Proof. exact (EQ_MP (@lem1758984 x) (@lem1759222 x h1)). Qed.
Lemma lem1759224 (x : real) (h1 : term24 x) : (term83 x) = False.
Proof. exact (prop_ext (fun h2 : term83 x => @lem1759221 x h2) (fun h2 : False => @lem1759223 x h1)). Qed.
Lemma lem1759225 (x : real) (h1 : term24 x) : False.
Proof. exact (EQ_MP (@lem1759224 x h1) (@lem1759223 x h1)). Qed.
Lemma lem1759226 (x : real) : term138 x.
Proof. exact (fun h0 : term24 x => @lem1759225 x h0). Qed.
Lemma lem1759227 (x : real) : term139 x.
Proof. exact (@lem1386578 (term140 x)). Qed.
Lemma lem1759228 (x : real) : term140 x.
Proof. exact (@lem1759227 x (@lem1759226 x)). Qed.
Lemma lem1759231 (y : real) (x : real) (h1 : (term141 x y) = (real_lt y x)) : (term141 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1759232 (y : real) (x : real) (h1 : (term141 x y) = (real_lt y x)) : (real_lt y x) = (term141 x y).
Proof. exact (SYM (@lem1759231 y x h1)). Qed.
Lemma lem1759233 (x : real) (y : real) (h1 : (real_lt y x) = (term141 x y)) : (real_lt y x) = (term141 x y).
Proof. exact (h1). Qed.
Lemma lem1759234 (x : real) (y : real) (h1 : (real_lt y x) = (term141 x y)) : (term141 x y) = (real_lt y x).
Proof. exact (SYM (@lem1759233 x y h1)). Qed.
Lemma lem1759235 (x : real) (y : real) : ((term141 x y) = (real_lt y x)) = ((real_lt y x) = (term141 x y)).
Proof. exact (prop_ext (fun h1 : (term141 x y) = (real_lt y x) => @lem1759232 y x h1) (fun h1 : (real_lt y x) = (term141 x y) => @lem1759234 x y h1)). Qed.
Lemma lem1759236 (x : real) : (term142 x) = (term143 x).
Proof. exact (fun_ext (fun y : real => @lem1759235 x y)). Qed.
Lemma lem1759237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1759238 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1759237) (@lem1759236 x)). Qed.
Lemma lem1759239 : term146 = term147.
Proof. exact (fun_ext (fun x : real => @lem1759238 x)). Qed.
Lemma lem1759240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1759241 : term148 = term149.
Proof. exact (MK_COMB (@lem1759240) (@lem1759239)). Qed.
Lemma lem1759242 : term149.
Proof. exact (EQ_MP (@lem1759241) (@lem1495933)). Qed.
Lemma lem1759243 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1759244 (x : real) (h1 : term25 x) : (term20 x) = (x = term13).
Proof. exact (@lem1759228 x (@lem1759243 x h1)). Qed.
Lemma lem1759250 (x : real) : term150 x.
Proof. exact (@lem1646060 x). Qed.
Lemma lem1759251 (x : real) : (term150 x) = (term151 x).
Proof. exact (eq_refl (term150 x)). Qed.
Lemma lem1759252 (x : real) : term151 x.
Proof. exact (EQ_MP (@lem1759251 x) (@lem1759250 x)). Qed.
Lemma lem1759253 (x : real) : (term151 x) = ((term151 x) = True).
Proof. exact (@lem7 (term151 x)). Qed.
Lemma lem1759255 (x : real) : term152 x.
Proof. exact (@lem1532076 x). Qed.
Lemma lem1759256 (x : real) : (term152 x) = (term153 x).
Proof. exact (eq_refl (term152 x)). Qed.
Lemma lem1759257 (x : real) : term153 x.
Proof. exact (EQ_MP (@lem1759256 x) (@lem1759255 x)). Qed.
Lemma lem1759258 (x : real) : (term153 x) = ((term153 x) = True).
Proof. exact (@lem7 (term153 x)). Qed.
Lemma lem1759260 (x : real) : term154 x.
Proof. exact (@lem1759242 x). Qed.
Lemma lem1759261 (x : real) : (term154 x) = (term145 x).
Proof. exact (eq_refl (term154 x)). Qed.
Lemma lem1759262 (x : real) : term145 x.
Proof. exact (EQ_MP (@lem1759261 x) (@lem1759260 x)). Qed.
Lemma lem1759263 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1759262 x y). Qed.
Lemma lem1759264 (x : real) (y : real) : (term155 x y) = ((real_lt y x) = (term141 x y)).
Proof. exact (eq_refl (term155 x y)). Qed.
Lemma lem1759266 (x : real) : term156 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1759267 (x : real) : (term156 x) = ((real_sgn x) = (term157 x)).
Proof. exact (eq_refl (term156 x)). Qed.
Lemma lem1759276 (x : real) : (real_sgn x) = (term157 x).
Proof. exact (EQ_MP (@lem1759267 x) (@lem1759266 x)). Qed.
Lemma lem1759277 (x : real) : (term158 x) = (term159 x).
Proof. exact (@lem1759276 (term160 x)). Qed.
Lemma lem1759278 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1759279 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1759278) (@lem1759277 x)). Qed.
Lemma lem1759281 (x : real) : (real_sgn x) = (term157 x).
Proof. exact (EQ_MP (@lem1759267 x) (@lem1759266 x)). Qed.
Lemma lem1759282 (x : real) : (term163 x) = (term164 x).
Proof. exact (@lem1759281 (real_abs x)). Qed.
Lemma lem1759283 (x : real) : ((term158 x) = (term163 x)) = ((term159 x) = (term164 x)).
Proof. exact (MK_COMB (@lem1759279 x) (@lem1759282 x)). Qed.
Lemma lem1759286 : term165 = term166.
Proof. exact (fun_ext (fun x : real => @lem1759283 x)). Qed.
Lemma lem1759287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1759288 : term167 = term168.
Proof. exact (MK_COMB (@lem1759287) (@lem1759286)). Qed.
Lemma lem1759293 : term168 = term167.
Proof. exact (SYM (@lem1759288)). Qed.
Lemma lem1759301 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term169 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1759302 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term170 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1759301 _2963 g t e g' t' e'). Qed.
Lemma lem1759303 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term171 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1759302 _2963 g t e g' t'). Qed.
Lemma lem1759304 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term172 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1759303 _2963 g t e g'). Qed.
Lemma lem1759305 (g : Prop) (t : real) (e : real) : term173 g t e.
Proof. exact (@lem1759304 real g t e). Qed.
Lemma lem1759306 (x : real) : term174 x.
Proof. exact (@lem1759305 (term175 x) term92 (term176 x)). Qed.
Lemma lem1759307 (x : real) (g' : Prop) : term177 x g'.
Proof. exact (@lem1759306 x g'). Qed.
Lemma lem1759308 (x : real) (g' : Prop) : (term177 x g') = (term178 x g').
Proof. exact (eq_refl (term177 x g')). Qed.
Lemma lem1759309 (x : real) (g' : Prop) : term178 x g'.
Proof. exact (EQ_MP (@lem1759308 x g') (@lem1759307 x g')). Qed.
Lemma lem1759310 (x : real) (g' : Prop) (t' : real) : term179 x g' t'.
Proof. exact (@lem1759309 x g' t'). Qed.
Lemma lem1759311 (x : real) (g' : Prop) (t' : real) : (term179 x g' t') = (term180 x g' t').
Proof. exact (eq_refl (term179 x g' t')). Qed.
Lemma lem1759312 (x : real) (g' : Prop) (t' : real) : term180 x g' t'.
Proof. exact (EQ_MP (@lem1759311 x g' t') (@lem1759310 x g' t')). Qed.
Lemma lem1759313 (x : real) (g' : Prop) (t' : real) (e' : real) : term181 x g' t' e'.
Proof. exact (@lem1759312 x g' t' e'). Qed.
Lemma lem1759314 (x : real) (g' : Prop) (t' : real) (e' : real) : (term181 x g' t' e') = (term182 x g' t' e').
Proof. exact (eq_refl (term181 x g' t' e')). Qed.
Lemma lem1759315 (x : real) (g' : Prop) (t' : real) (e' : real) : term182 x g' t' e'.
Proof. exact (EQ_MP (@lem1759314 x g' t' e') (@lem1759313 x g' t' e')). Qed.
Lemma lem1759317 (x : real) (y : real) : (real_lt y x) = (term141 x y).
Proof. exact (EQ_MP (@lem1759264 x y) (@lem1759263 x y)). Qed.
Lemma lem1759318 (x : real) : (term175 x) = (term183 x).
Proof. exact (@lem1759317 (term160 x) term13). Qed.
Lemma lem1759320 (x : real) : term140 x.
Proof. exact (fun h0 : term25 x => @lem1759244 x h0). Qed.
Lemma lem1759321 (x : real) : term184 x.
Proof. exact (@lem1759320 (term160 x)). Qed.
Lemma lem1759323 (x : real) : (term151 x) = True.
Proof. exact (EQ_MP (@lem1759253 x) (@lem1759252 x)). Qed.
Lemma lem1759324 (x : real) : True = (term151 x).
Proof. exact (SYM (@lem1759323 x)). Qed.
Lemma lem1759325 (x : real) : term151 x.
Proof. exact (EQ_MP (@lem1759324 x) (@lem0)). Qed.
Lemma lem1759326 (x : real) : (term185 x) = ((term160 x) = term13).
Proof. exact (@lem1759321 x (@lem1759325 x)). Qed.
Lemma lem1759329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1759330 (x : real) : (term183 x) = (term186 x).
Proof. exact (MK_COMB (@lem1759329) (@lem1759326 x)). Qed.
Lemma lem1759333 (x : real) : (term175 x) = (term186 x).
Proof. exact (TRANS (@lem1759318 x) (@lem1759330 x)). Qed.
Lemma lem1759334 (x : real) (t' : real) (e' : real) : term187 x t' e'.
Proof. exact (@lem1759315 x (term186 x) t' e'). Qed.
Lemma lem1759335 (x : real) (t' : real) (e' : real) : term188 x t' e'.
Proof. exact (@lem1759334 x t' e' (@lem1759333 x)). Qed.
Lemma lem1759350 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem1759351 (x : real) : term189 x.
Proof. exact (fun h0 : term186 x => @lem1759350). Qed.
Lemma lem1759352 (x : real) (e' : real) : term190 x e'.
Proof. exact (@lem1759335 x term92 e'). Qed.
Lemma lem1759353 (x : real) (e' : real) : term191 x e'.
Proof. exact (@lem1759352 x e' (@lem1759351 x)). Qed.
Lemma lem1759358 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term169 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1759359 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term170 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1759358 _2963 g t e g' t' e'). Qed.
Lemma lem1759360 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term171 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1759359 _2963 g t e g' t'). Qed.
Lemma lem1759361 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term172 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1759360 _2963 g t e g'). Qed.
Lemma lem1759362 (g : Prop) (t : real) (e : real) : term173 g t e.
Proof. exact (@lem1759361 real g t e). Qed.
Lemma lem1759363 (x : real) : term192 x.
Proof. exact (@lem1759362 (term193 x) term108 term13). Qed.
Lemma lem1759364 (x : real) (g' : Prop) : term194 x g'.
Proof. exact (@lem1759363 x g'). Qed.
Lemma lem1759365 (x : real) (g' : Prop) : (term194 x g') = (term195 x g').
Proof. exact (eq_refl (term194 x g')). Qed.
Lemma lem1759366 (x : real) (g' : Prop) : term195 x g'.
Proof. exact (EQ_MP (@lem1759365 x g') (@lem1759364 x g')). Qed.
Lemma lem1759367 (x : real) (g' : Prop) (t' : real) : term196 x g' t'.
Proof. exact (@lem1759366 x g' t'). Qed.
Lemma lem1759368 (x : real) (g' : Prop) (t' : real) : (term196 x g' t') = (term197 x g' t').
Proof. exact (eq_refl (term196 x g' t')). Qed.
Lemma lem1759369 (x : real) (g' : Prop) (t' : real) : term197 x g' t'.
Proof. exact (EQ_MP (@lem1759368 x g' t') (@lem1759367 x g' t')). Qed.
Lemma lem1759370 (x : real) (g' : Prop) (t' : real) (e' : real) : term198 x g' t' e'.
Proof. exact (@lem1759369 x g' t' e'). Qed.
Lemma lem1759371 (x : real) (g' : Prop) (t' : real) (e' : real) : (term198 x g' t' e') = (term199 x g' t' e').
Proof. exact (eq_refl (term198 x g' t' e')). Qed.
Lemma lem1759372 (x : real) (g' : Prop) (t' : real) (e' : real) : term199 x g' t' e'.
Proof. exact (EQ_MP (@lem1759371 x g' t' e') (@lem1759370 x g' t' e')). Qed.
Lemma lem1759374 (x : real) (y : real) : (real_lt y x) = (term141 x y).
Proof. exact (EQ_MP (@lem1759264 x y) (@lem1759263 x y)). Qed.
Lemma lem1759375 (x : real) : (term193 x) = (term200 x).
Proof. exact (@lem1759374 term13 (term160 x)). Qed.
Lemma lem1759377 (x : real) : (term151 x) = True.
Proof. exact (EQ_MP (@lem1759253 x) (@lem1759252 x)). Qed.
Lemma lem1759378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1759379 (x : real) : (term200 x) = (~ True).
Proof. exact (MK_COMB (@lem1759378) (@lem1759377 x)). Qed.
Lemma lem1759381 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1759382 (x : real) : (term200 x) = False.
Proof. exact (TRANS (@lem1759379 x) (@lem1759381)). Qed.
Lemma lem1759383 (x : real) : (term193 x) = False.
Proof. exact (TRANS (@lem1759375 x) (@lem1759382 x)). Qed.
Lemma lem1759384 (x : real) (t' : real) (e' : real) : term201 x t' e'.
Proof. exact (@lem1759372 x False t' e'). Qed.
Lemma lem1759385 (x : real) (t' : real) (e' : real) : term202 x t' e'.
Proof. exact (@lem1759384 x t' e' (@lem1759383 x)). Qed.
Lemma lem1759389 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem1759390 : term203.
Proof. exact (fun h0 : False => @lem1759389). Qed.
Lemma lem1759391 (x : real) (e' : real) : term204 x e'.
Proof. exact (@lem1759385 x term108 e'). Qed.
Lemma lem1759392 (x : real) (e' : real) : term205 x e'.
Proof. exact (@lem1759391 x e' (@lem1759390)). Qed.
Lemma lem1759398 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759399 : term206.
Proof. exact (fun h0 : ~ False => @lem1759398). Qed.
Lemma lem1759400 (x : real) : term207 x.
Proof. exact (@lem1759392 x term13). Qed.
Lemma lem1759401 (x : real) : (term176 x) = term208.
Proof. exact (@lem1759400 x (@lem1759399)). Qed.
Lemma lem1759403 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1759404 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1759403 real t1 t2). Qed.
Lemma lem1759405 : term208 = term13.
Proof. exact (@lem1759404 term108 term13). Qed.
Lemma lem1759406 (x : real) : (term176 x) = term13.
Proof. exact (TRANS (@lem1759401 x) (@lem1759405)). Qed.
Lemma lem1759407 (x : real) : term209 x.
Proof. exact (fun h0 : term210 x => @lem1759406 x). Qed.
Lemma lem1759408 (x : real) : term211 x.
Proof. exact (@lem1759353 x term13). Qed.
Lemma lem1759409 (x : real) : (term159 x) = (term212 x).
Proof. exact (@lem1759408 x (@lem1759407 x)). Qed.
Lemma lem1759458 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1759459 (x : real) : (term162 x) = (term213 x).
Proof. exact (MK_COMB (@lem1759458) (@lem1759409 x)). Qed.
Lemma lem1759509 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term169 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1759510 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term170 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1759509 _2963 g t e g' t' e'). Qed.
Lemma lem1759511 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term171 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1759510 _2963 g t e g' t'). Qed.
Lemma lem1759512 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term172 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1759511 _2963 g t e g'). Qed.
Lemma lem1759513 (g : Prop) (t : real) (e : real) : term173 g t e.
Proof. exact (@lem1759512 real g t e). Qed.
Lemma lem1759514 (x : real) : term214 x.
Proof. exact (@lem1759513 (term215 x) term92 (term216 x)). Qed.
Lemma lem1759515 (x : real) (g' : Prop) : term217 x g'.
Proof. exact (@lem1759514 x g'). Qed.
Lemma lem1759516 (x : real) (g' : Prop) : (term217 x g') = (term218 x g').
Proof. exact (eq_refl (term217 x g')). Qed.
Lemma lem1759517 (x : real) (g' : Prop) : term218 x g'.
Proof. exact (EQ_MP (@lem1759516 x g') (@lem1759515 x g')). Qed.
Lemma lem1759518 (x : real) (g' : Prop) (t' : real) : term219 x g' t'.
Proof. exact (@lem1759517 x g' t'). Qed.
Lemma lem1759519 (x : real) (g' : Prop) (t' : real) : (term219 x g' t') = (term220 x g' t').
Proof. exact (eq_refl (term219 x g' t')). Qed.
Lemma lem1759520 (x : real) (g' : Prop) (t' : real) : term220 x g' t'.
Proof. exact (EQ_MP (@lem1759519 x g' t') (@lem1759518 x g' t')). Qed.
Lemma lem1759521 (x : real) (g' : Prop) (t' : real) (e' : real) : term221 x g' t' e'.
Proof. exact (@lem1759520 x g' t' e'). Qed.
Lemma lem1759522 (x : real) (g' : Prop) (t' : real) (e' : real) : (term221 x g' t' e') = (term222 x g' t' e').
Proof. exact (eq_refl (term221 x g' t' e')). Qed.
Lemma lem1759523 (x : real) (g' : Prop) (t' : real) (e' : real) : term222 x g' t' e'.
Proof. exact (EQ_MP (@lem1759522 x g' t' e') (@lem1759521 x g' t' e')). Qed.
Lemma lem1759525 (x : real) (y : real) : (real_lt y x) = (term141 x y).
Proof. exact (EQ_MP (@lem1759264 x y) (@lem1759263 x y)). Qed.
Lemma lem1759526 (x : real) : (term215 x) = (term223 x).
Proof. exact (@lem1759525 (real_abs x) term13). Qed.
Lemma lem1759528 (x : real) : term140 x.
Proof. exact (fun h0 : term25 x => @lem1759244 x h0). Qed.
Lemma lem1759529 (x : real) : term224 x.
Proof. exact (@lem1759528 (real_abs x)). Qed.
Lemma lem1759531 (x : real) : (term153 x) = True.
Proof. exact (EQ_MP (@lem1759258 x) (@lem1759257 x)). Qed.
Lemma lem1759532 (x : real) : True = (term153 x).
Proof. exact (SYM (@lem1759531 x)). Qed.
Lemma lem1759533 (x : real) : term153 x.
Proof. exact (EQ_MP (@lem1759532 x) (@lem0)). Qed.
Lemma lem1759534 (x : real) : (term225 x) = ((real_abs x) = term13).
Proof. exact (@lem1759529 x (@lem1759533 x)). Qed.
Lemma lem1759537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1759538 (x : real) : (term223 x) = (term226 x).
Proof. exact (MK_COMB (@lem1759537) (@lem1759534 x)). Qed.
Lemma lem1759541 (x : real) : (term215 x) = (term226 x).
Proof. exact (TRANS (@lem1759526 x) (@lem1759538 x)). Qed.
Lemma lem1759542 (x : real) (t' : real) (e' : real) : term227 x t' e'.
Proof. exact (@lem1759523 x (term226 x) t' e'). Qed.
Lemma lem1759543 (x : real) (t' : real) (e' : real) : term228 x t' e'.
Proof. exact (@lem1759542 x t' e' (@lem1759541 x)). Qed.
Lemma lem1759558 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem1759559 (x : real) : term229 x.
Proof. exact (fun h0 : term226 x => @lem1759558). Qed.
Lemma lem1759560 (x : real) (e' : real) : term230 x e'.
Proof. exact (@lem1759543 x term92 e'). Qed.
Lemma lem1759561 (x : real) (e' : real) : term231 x e'.
Proof. exact (@lem1759560 x e' (@lem1759559 x)). Qed.
Lemma lem1759566 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term169 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1759567 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term170 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1759566 _2963 g t e g' t' e'). Qed.
Lemma lem1759568 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term171 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1759567 _2963 g t e g' t'). Qed.
Lemma lem1759569 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term172 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1759568 _2963 g t e g'). Qed.
Lemma lem1759570 (g : Prop) (t : real) (e : real) : term173 g t e.
Proof. exact (@lem1759569 real g t e). Qed.
Lemma lem1759571 (x : real) : term232 x.
Proof. exact (@lem1759570 (term233 x) term108 term13). Qed.
Lemma lem1759572 (x : real) (g' : Prop) : term234 x g'.
Proof. exact (@lem1759571 x g'). Qed.
Lemma lem1759573 (x : real) (g' : Prop) : (term234 x g') = (term235 x g').
Proof. exact (eq_refl (term234 x g')). Qed.
Lemma lem1759574 (x : real) (g' : Prop) : term235 x g'.
Proof. exact (EQ_MP (@lem1759573 x g') (@lem1759572 x g')). Qed.
Lemma lem1759575 (x : real) (g' : Prop) (t' : real) : term236 x g' t'.
Proof. exact (@lem1759574 x g' t'). Qed.
Lemma lem1759576 (x : real) (g' : Prop) (t' : real) : (term236 x g' t') = (term237 x g' t').
Proof. exact (eq_refl (term236 x g' t')). Qed.
Lemma lem1759577 (x : real) (g' : Prop) (t' : real) : term237 x g' t'.
Proof. exact (EQ_MP (@lem1759576 x g' t') (@lem1759575 x g' t')). Qed.
Lemma lem1759578 (x : real) (g' : Prop) (t' : real) (e' : real) : term238 x g' t' e'.
Proof. exact (@lem1759577 x g' t' e'). Qed.
Lemma lem1759579 (x : real) (g' : Prop) (t' : real) (e' : real) : (term238 x g' t' e') = (term239 x g' t' e').
Proof. exact (eq_refl (term238 x g' t' e')). Qed.
Lemma lem1759580 (x : real) (g' : Prop) (t' : real) (e' : real) : term239 x g' t' e'.
Proof. exact (EQ_MP (@lem1759579 x g' t' e') (@lem1759578 x g' t' e')). Qed.
Lemma lem1759582 (x : real) (y : real) : (real_lt y x) = (term141 x y).
Proof. exact (EQ_MP (@lem1759264 x y) (@lem1759263 x y)). Qed.
Lemma lem1759583 (x : real) : (term233 x) = (term240 x).
Proof. exact (@lem1759582 term13 (real_abs x)). Qed.
Lemma lem1759585 (x : real) : (term153 x) = True.
Proof. exact (EQ_MP (@lem1759258 x) (@lem1759257 x)). Qed.
Lemma lem1759586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1759587 (x : real) : (term240 x) = (~ True).
Proof. exact (MK_COMB (@lem1759586) (@lem1759585 x)). Qed.
Lemma lem1759589 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1759590 (x : real) : (term240 x) = False.
Proof. exact (TRANS (@lem1759587 x) (@lem1759589)). Qed.
Lemma lem1759591 (x : real) : (term233 x) = False.
Proof. exact (TRANS (@lem1759583 x) (@lem1759590 x)). Qed.
Lemma lem1759592 (x : real) (t' : real) (e' : real) : term241 x t' e'.
Proof. exact (@lem1759580 x False t' e'). Qed.
Lemma lem1759593 (x : real) (t' : real) (e' : real) : term242 x t' e'.
Proof. exact (@lem1759592 x t' e' (@lem1759591 x)). Qed.
Lemma lem1759597 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem1759598 : term203.
Proof. exact (fun h0 : False => @lem1759597). Qed.
Lemma lem1759599 (x : real) (e' : real) : term243 x e'.
Proof. exact (@lem1759593 x term108 e'). Qed.
Lemma lem1759600 (x : real) (e' : real) : term244 x e'.
Proof. exact (@lem1759599 x e' (@lem1759598)). Qed.
Lemma lem1759606 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1759607 : term206.
Proof. exact (fun h0 : ~ False => @lem1759606). Qed.
Lemma lem1759608 (x : real) : term245 x.
Proof. exact (@lem1759600 x term13). Qed.
Lemma lem1759609 (x : real) : (term216 x) = term208.
Proof. exact (@lem1759608 x (@lem1759607)). Qed.
Lemma lem1759611 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1759612 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1759611 real t1 t2). Qed.
Lemma lem1759613 : term208 = term13.
Proof. exact (@lem1759612 term108 term13). Qed.
Lemma lem1759614 (x : real) : (term216 x) = term13.
Proof. exact (TRANS (@lem1759609 x) (@lem1759613)). Qed.
Lemma lem1759615 (x : real) : term246 x.
Proof. exact (fun h0 : term247 x => @lem1759614 x). Qed.
Lemma lem1759616 (x : real) : term248 x.
Proof. exact (@lem1759561 x term13). Qed.
Lemma lem1759617 (x : real) : (term164 x) = (term249 x).
Proof. exact (@lem1759616 x (@lem1759615 x)). Qed.
Lemma lem1759666 (x : real) : ((term159 x) = (term164 x)) = ((term212 x) = (term249 x)).
Proof. exact (MK_COMB (@lem1759459 x) (@lem1759617 x)). Qed.
Lemma lem1759765 : term166 = term250.
Proof. exact (fun_ext (fun x : real => @lem1759666 x)). Qed.
Lemma lem1759864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1759865 : term168 = term251.
Proof. exact (MK_COMB (@lem1759864) (@lem1759765)). Qed.
Lemma lem1759968 : term251 = term168.
Proof. exact (SYM (@lem1759865)). Qed.
Lemma lem1759976 (x : real) (n : nat) : ((real_pow x n) = term13) = (term17 x n).
Proof. exact (EQ_MP (@lem1758751 x n) (@lem1758750 x n)). Qed.
Lemma lem1759977 (x : real) : ((term160 x) = term13) = (term252 x).
Proof. exact (@lem1759976 x term253). Qed.
Lemma lem1759983 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1758492 m n) (@lem1758491 m n)). Qed.
Lemma lem1759984 : (term253 = (NUMERAL 0)) = (term254 = 0).
Proof. exact (@lem1759983 term254 0). Qed.
Lemma lem1759986 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1758484 n) (@lem1758483 n)). Qed.
Lemma lem1759987 : (term254 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1759986 (BIT1 0)). Qed.
Lemma lem1759989 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1758480 n) (@lem1758479 n)). Qed.
Lemma lem1759990 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1759989 0). Qed.
Lemma lem1759991 : (term254 = 0) = False.
Proof. exact (TRANS (@lem1759987) (@lem1759990)). Qed.
Lemma lem1759992 : (term253 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1759984) (@lem1759991)). Qed.
Lemma lem1759993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1759994 : term255 = (~ False).
Proof. exact (MK_COMB (@lem1759993) (@lem1759992)). Qed.
Lemma lem1759996 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1759997 : term255 = True.
Proof. exact (TRANS (@lem1759994) (@lem1759996)). Qed.
Lemma lem1759998 (x : real) : (term256 x) = (term256 x).
Proof. exact (eq_refl (term256 x)). Qed.
Lemma lem1759999 (x : real) : (term252 x) = (term257 x).
Proof. exact (MK_COMB (@lem1759998 x) (@lem1759997)). Qed.
Lemma lem1760001 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1760002 (x : real) : (term257 x) = (x = term13).
Proof. exact (@lem1760001 (x = term13)). Qed.
Lemma lem1760005 (x : real) : (term252 x) = (x = term13).
Proof. exact (TRANS (@lem1759999 x) (@lem1760002 x)). Qed.
Lemma lem1760006 (x : real) : ((term160 x) = term13) = (x = term13).
Proof. exact (TRANS (@lem1759977 x) (@lem1760005 x)). Qed.
Lemma lem1760007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760008 (x : real) : (term186 x) = (term42 x).
Proof. exact (MK_COMB (@lem1760007) (@lem1760006 x)). Qed.
Lemma lem1760009 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760010 (x : real) : (term258 x) = (term259 x).
Proof. exact (MK_COMB (@lem1760009) (@lem1760008 x)). Qed.
Lemma lem1760011 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem1760012 (x : real) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem1760010 x) (@lem1760011)). Qed.
Lemma lem1760013 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1760014 (x : real) : (term212 x) = (term262 x).
Proof. exact (MK_COMB (@lem1760012 x) (@lem1760013)). Qed.
Lemma lem1760015 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760016 (x : real) : (term213 x) = (term263 x).
Proof. exact (MK_COMB (@lem1760015) (@lem1760014 x)). Qed.
Lemma lem1760018 (x : real) : ((real_abs x) = term13) = (x = term13).
Proof. exact (EQ_MP (@lem1758745 x) (@lem1758744 x)). Qed.
Lemma lem1760021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760022 (x : real) : (term226 x) = (term42 x).
Proof. exact (MK_COMB (@lem1760021) (@lem1760018 x)). Qed.
Lemma lem1760023 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760024 (x : real) : (term264 x) = (term259 x).
Proof. exact (MK_COMB (@lem1760023) (@lem1760022 x)). Qed.
Lemma lem1760025 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem1760026 (x : real) : (term265 x) = (term261 x).
Proof. exact (MK_COMB (@lem1760024 x) (@lem1760025)). Qed.
Lemma lem1760027 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1760028 (x : real) : (term249 x) = (term262 x).
Proof. exact (MK_COMB (@lem1760026 x) (@lem1760027)). Qed.
Lemma lem1760029 (x : real) : ((term212 x) = (term249 x)) = ((term262 x) = (term262 x)).
Proof. exact (MK_COMB (@lem1760016 x) (@lem1760028 x)). Qed.
Lemma lem1760031 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1760032 (x : real) : (x = x) = True.
Proof. exact (@lem1760031 real x). Qed.
Lemma lem1760033 (x : real) : ((term262 x) = (term262 x)) = True.
Proof. exact (@lem1760032 (term262 x)). Qed.
Lemma lem1760034 (x : real) : ((term212 x) = (term249 x)) = True.
Proof. exact (TRANS (@lem1760029 x) (@lem1760033 x)). Qed.
Lemma lem1760035 : term250 = term266.
Proof. exact (fun_ext (fun x : real => @lem1760034 x)). Qed.
Lemma lem1760036 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1760037 : term251 = term267.
Proof. exact (MK_COMB (@lem1760036) (@lem1760035)). Qed.
Lemma lem1760039 {A : Type'} (t : Prop) : (term268 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1760040 (t : Prop) : (term269 t) = t.
Proof. exact (@lem1760039 real t). Qed.
Lemma lem1760041 : term267 = True.
Proof. exact (@lem1760040 True). Qed.
Lemma lem1760042 : term251 = True.
Proof. exact (TRANS (@lem1760037) (@lem1760041)). Qed.
Lemma lem1760043 : True = term251.
Proof. exact (SYM (@lem1760042)). Qed.
Lemma lem1760044 : term251.
Proof. exact (EQ_MP (@lem1760043) (@lem0)). Qed.
Lemma lem1760045 : term168.
Proof. exact (EQ_MP (@lem1759968) (@lem1760044)). Qed.
Lemma lem1760046 : term167.
Proof. exact (EQ_MP (@lem1759293) (@lem1760045)). Qed.

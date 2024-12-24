Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1999793_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1396750_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm19158_spec.
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
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988285_spec.
Require Import thm1988293_spec.
Require Import thm1988295_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988338_spec.
Require Import thm1988348_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1997781 (x : real) (y : real) : (term0 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1997783 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1997784 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (MK_COMB (@lem1997783 x y) (@lem1997781 x y)). Qed.
Lemma lem1997785 (x : real) (y : real) : (term4 x y) = (term2 x y).
Proof. exact (@lem17045 (real_lt x y) (term5 x y)). Qed.
Lemma lem1997786 (x : real) (y : real) : (term4 x y) = (term3 x y).
Proof. exact (TRANS (@lem1997785 x y) (@lem1997784 x y)). Qed.
Lemma lem1997792 (x : real) (y : real) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1997794 (x : real) (y : real) : (term7 x y) = (term7 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1997795 (x : real) (y : real) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1997794 x y) (@lem1997786 x y)). Qed.
Lemma lem1997796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1997797 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1997796) (@lem1997795 x y)). Qed.
Lemma lem1997798 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1997797 x y) (@lem1997792 x y)). Qed.
Lemma lem1997799 (x : real) (y : real) : (term14 x y) = (term12 x y).
Proof. exact (@lem17646 (real_lt x y) (term15 x y)). Qed.
Lemma lem1997829 (x : real) (y : real) : (term14 x y) = (term13 x y).
Proof. exact (TRANS (@lem1997799 x y) (@lem1997798 x y)). Qed.
Lemma lem1997830 (y : real) (x : real) : (real_lt x y) = (term16 y x).
Proof. exact (@lem1988285 y x). Qed.
Lemma lem1997836 (y : real) (x : real) : (real_sub y x) = (term17 y x).
Proof. exact (@lem1982792 y x). Qed.
Lemma lem1997841 (x : real) (y : real) : (term17 y x) = (term18 x y).
Proof. exact (@lem1982761 (term19 x) y). Qed.
Lemma lem1997843 (x : real) (y : real) : (real_sub y x) = (term18 x y).
Proof. exact (TRANS (@lem1997836 y x) (@lem1997841 x y)). Qed.
Lemma lem1997844 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1997845 (x : real) (y : real) : (term20 y x) = (term21 x y).
Proof. exact (MK_COMB (@lem1997844) (@lem1997843 x y)). Qed.
Lemma lem1997846 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1997847 (x : real) (y : real) : (term16 y x) = (term23 x y).
Proof. exact (MK_COMB (@lem1997845 x y) (@lem1997846)). Qed.
Lemma lem1997848 (x : real) (y : real) : (real_lt x y) = (term23 x y).
Proof. exact (TRANS (@lem1997830 y x) (@lem1997847 x y)). Qed.
Lemma lem1997849 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1988295 x y). Qed.
Lemma lem1997862 (x : real) (y : real) : (real_sub x y) = (term17 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1997863 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1997864 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1997863) (@lem1997862 x y)). Qed.
Lemma lem1997865 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1997866 (x : real) (y : real) : (term25 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1997864 x y) (@lem1997865)). Qed.
Lemma lem1997867 (x : real) (y : real) : (term24 x y) = (term28 x y).
Proof. exact (TRANS (@lem1997849 x y) (@lem1997866 x y)). Qed.
Lemma lem1997868 (x : real) (y : real) : (x = y) = ((real_sub x y) = term22).
Proof. exact (@lem1988293 x y). Qed.
Lemma lem1997881 (x : real) (y : real) : (real_sub x y) = (term17 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1997882 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1997883 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1997882) (@lem1997881 x y)). Qed.
Lemma lem1997884 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1997885 (x : real) (y : real) : ((real_sub x y) = term22) = ((term17 x y) = term22).
Proof. exact (MK_COMB (@lem1997883 x y) (@lem1997884)). Qed.
Lemma lem1997886 (x : real) (y : real) : (x = y) = ((term17 x y) = term22).
Proof. exact (TRANS (@lem1997868 x y) (@lem1997885 x y)). Qed.
Lemma lem1997887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1997888 (x : real) (y : real) : (term1 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1997887) (@lem1997867 x y)). Qed.
Lemma lem1997889 (x : real) (y : real) : (term3 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1997888 x y) (@lem1997886 x y)). Qed.
Lemma lem1997890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1997891 (x : real) (y : real) : (term7 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1997890) (@lem1997848 x y)). Qed.
Lemma lem1997892 (x : real) (y : real) : (term9 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1997891 x y) (@lem1997889 x y)). Qed.
Lemma lem1997893 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1988295 x y). Qed.
Lemma lem1997906 (x : real) (y : real) : (real_sub x y) = (term17 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1997907 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1997908 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1997907) (@lem1997906 x y)). Qed.
Lemma lem1997909 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1997910 (x : real) (y : real) : (term25 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1997908 x y) (@lem1997909)). Qed.
Lemma lem1997911 (x : real) (y : real) : (term24 x y) = (term28 x y).
Proof. exact (TRANS (@lem1997893 x y) (@lem1997910 x y)). Qed.
Lemma lem1997912 (y : real) (x : real) : (real_lt x y) = (term16 y x).
Proof. exact (@lem1988285 y x). Qed.
Lemma lem1997918 (y : real) (x : real) : (real_sub y x) = (term17 y x).
Proof. exact (@lem1982792 y x). Qed.
Lemma lem1997923 (x : real) (y : real) : (term17 y x) = (term18 x y).
Proof. exact (@lem1982761 (term19 x) y). Qed.
Lemma lem1997925 (x : real) (y : real) : (real_sub y x) = (term18 x y).
Proof. exact (TRANS (@lem1997918 y x) (@lem1997923 x y)). Qed.
Lemma lem1997926 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1997927 (x : real) (y : real) : (term20 y x) = (term21 x y).
Proof. exact (MK_COMB (@lem1997926) (@lem1997925 x y)). Qed.
Lemma lem1997928 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1997929 (x : real) (y : real) : (term16 y x) = (term23 x y).
Proof. exact (MK_COMB (@lem1997927 x y) (@lem1997928)). Qed.
Lemma lem1997930 (x : real) (y : real) : (real_lt x y) = (term23 x y).
Proof. exact (TRANS (@lem1997912 y x) (@lem1997929 x y)). Qed.
Lemma lem1997931 (x : real) (y : real) : (term5 x y) = (term35 x y).
Proof. exact (@lem1988318 x y). Qed.
Lemma lem1997944 (x : real) (y : real) : (real_sub x y) = (term17 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem1997945 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1997946 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1997945) (@lem1997944 x y)). Qed.
Lemma lem1997947 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem1982785 (term17 x y)). Qed.
Lemma lem1997948 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (@lem1982781 x term40 (term19 y)). Qed.
Lemma lem1997949 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1982749 term40 term40 y). Qed.
Lemma lem1997951 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1997952 : term40 = term45.
Proof. exact (@lem1997951 term46). Qed.
Lemma lem1997954 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1997955 : term40 = term45.
Proof. exact (@lem1997954 term46). Qed.
Lemma lem1997956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1997957 : term47 = term48.
Proof. exact (MK_COMB (@lem1997956) (@lem1997955)). Qed.
Lemma lem1997958 : term49 = term50.
Proof. exact (MK_COMB (@lem1997957) (@lem1997952)). Qed.
Lemma lem1997959 : term50 = term51.
Proof. exact (@lem1981613 term40 term40 term52 term52). Qed.
Lemma lem1997961 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1997962 : term55 = term56.
Proof. exact (@lem1997961 term46 term46). Qed.
Lemma lem1997963 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1997964 : term58 = term46.
Proof. exact (EQ_MP (@lem1997963) (@lem940073)). Qed.
Lemma lem1997965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1997966 : term56 = term52.
Proof. exact (MK_COMB (@lem1997965) (@lem1997964)). Qed.
Lemma lem1997967 : term55 = term52.
Proof. exact (TRANS (@lem1997962) (@lem1997966)). Qed.
Lemma lem1997969 (m : nat) (n : nat) : (term59 m n) = (term54 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1997970 : term49 = term56.
Proof. exact (@lem1997969 term46 term46). Qed.
Lemma lem1997971 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1997972 : term58 = term46.
Proof. exact (EQ_MP (@lem1997971) (@lem940073)). Qed.
Lemma lem1997973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1997974 : term56 = term52.
Proof. exact (MK_COMB (@lem1997973) (@lem1997972)). Qed.
Lemma lem1997975 : term49 = term52.
Proof. exact (TRANS (@lem1997970) (@lem1997974)). Qed.
Lemma lem1997976 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1997977 : term60 = term61.
Proof. exact (MK_COMB (@lem1997976) (@lem1997975)). Qed.
Lemma lem1997978 : term51 = term62.
Proof. exact (MK_COMB (@lem1997977) (@lem1997967)). Qed.
Lemma lem1997979 : term50 = term62.
Proof. exact (TRANS (@lem1997959) (@lem1997978)). Qed.
Lemma lem1997980 : term49 = term62.
Proof. exact (TRANS (@lem1997958) (@lem1997979)). Qed.
Lemma lem1997982 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem1997983 : term62 = term52.
Proof. exact (@lem1997982 term52). Qed.
Lemma lem1997984 : term49 = term52.
Proof. exact (TRANS (@lem1997980) (@lem1997983)). Qed.
Lemma lem1997985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1997986 : term64 = term65.
Proof. exact (MK_COMB (@lem1997985) (@lem1997984)). Qed.
Lemma lem1997987 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1997988 (y : real) : (term42 y) = (term66 y).
Proof. exact (MK_COMB (@lem1997986) (@lem1997987 y)). Qed.
Lemma lem1997989 (y : real) : (term41 y) = (term66 y).
Proof. exact (TRANS (@lem1997949 y) (@lem1997988 y)). Qed.
Lemma lem1997990 (y : real) : (term66 y) = y.
Proof. exact (@lem1982709 y). Qed.
Lemma lem1997991 (y : real) : (term41 y) = y.
Proof. exact (TRANS (@lem1997989 y) (@lem1997990 y)). Qed.
Lemma lem1997994 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1997995 (x : real) (y : real) : (term39 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1997994 x) (@lem1997991 y)). Qed.
Lemma lem1997996 (x : real) (y : real) : (term38 x y) = (term18 x y).
Proof. exact (TRANS (@lem1997948 x y) (@lem1997995 x y)). Qed.
Lemma lem1997997 (x : real) (y : real) : (term37 x y) = (term18 x y).
Proof. exact (TRANS (@lem1997947 x y) (@lem1997996 x y)). Qed.
Lemma lem1997998 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1997999 (x : real) (y : real) : ((term36 x y) = (term37 x y)) = ((term36 x y) = (term18 x y)).
Proof. exact (MK_COMB (@lem1997998 x y) (@lem1997997 x y)). Qed.
Lemma lem1998000 (x : real) (y : real) : (term36 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem1997999 x y) (@lem1997946 x y)). Qed.
Lemma lem1998001 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998002 (x : real) (y : real) : (term69 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1998001) (@lem1998000 x y)). Qed.
Lemma lem1998003 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998004 (x : real) (y : real) : (term70 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1998002 x y) (@lem1998003)). Qed.
Lemma lem1998005 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998006 (x : real) (y : real) : (term20 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1998005) (@lem1997944 x y)). Qed.
Lemma lem1998007 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998008 (x : real) (y : real) : (term16 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1998006 x y) (@lem1998007)). Qed.
Lemma lem1998009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1998010 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1998009) (@lem1998008 x y)). Qed.
Lemma lem1998011 (x : real) (y : real) : (term35 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1998010 x y) (@lem1998004 x y)). Qed.
Lemma lem1998012 (x : real) (y : real) : (term5 x y) = (term75 x y).
Proof. exact (TRANS (@lem1997931 x y) (@lem1998011 x y)). Qed.
Lemma lem1998013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1998014 (x : real) (y : real) : (term7 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1998013) (@lem1997930 x y)). Qed.
Lemma lem1998015 (x : real) (y : real) : (term15 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1998014 x y) (@lem1998012 x y)). Qed.
Lemma lem1998016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1998017 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1998016) (@lem1997911 x y)). Qed.
Lemma lem1998018 (x : real) (y : real) : (term6 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1998017 x y) (@lem1998015 x y)). Qed.
Lemma lem1998019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1998020 (x : real) (y : real) : (term11 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1998019) (@lem1997892 x y)). Qed.
Lemma lem1998021 (x : real) (y : real) : (term13 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1998020 x y) (@lem1998018 x y)). Qed.
Lemma lem1998028 (x : real) (y : real) : (term14 x y) = (term81 x y).
Proof. exact (TRANS (@lem1997829 x y) (@lem1998021 x y)). Qed.
Lemma lem1998045 (x : real) (y : real) : (term76 x y) = (term82 x y).
Proof. exact (@lem19158 (term72 x y) (term23 x y) (term23 x y)). Qed.
Lemma lem1998048 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1998049 (x : real) (y : real) : (term79 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1998048 x y) (@lem1998045 x y)). Qed.
Lemma lem1998056 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (@lem19158 (term85 x y) (term28 x y) (term86 x y)). Qed.
Lemma lem1998057 (x : real) (y : real) : (term79 x y) = (term84 x y).
Proof. exact (TRANS (@lem1998049 x y) (@lem1998056 x y)). Qed.
Lemma lem1998074 (x : real) (y : real) : (term34 x y) = (term87 x y).
Proof. exact (@lem19158 (term28 x y) (term23 x y) ((term17 x y) = term22)). Qed.
Lemma lem1998075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1998076 (x : real) (y : real) : (term80 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1998075) (@lem1998074 x y)). Qed.
Lemma lem1998077 (x : real) (y : real) : (term81 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1998076 x y) (@lem1998057 x y)). Qed.
Lemma lem1998078 (x : real) (y : real) : (term14 x y) = (term89 x y).
Proof. exact (TRANS (@lem1998028 x y) (@lem1998077 x y)). Qed.
Lemma lem1998100 (x : real) (y : real) (h1 : term89 x y) : term89 x y.
Proof. exact (h1). Qed.
Lemma lem1998101 (x : real) (y : real) (h1 : term87 x y) : term87 x y.
Proof. exact (h1). Qed.
Lemma lem1998102 (x : real) (y : real) (h1 : term90 x y) : term90 x y.
Proof. exact (h1). Qed.
Lemma lem1998103 (x : real) (y : real) (h1 : term90 x y) : term28 x y.
Proof. exact (proj2 (@lem1998102 x y h1)). Qed.
Lemma lem1998104 (x : real) (y : real) (h1 : term90 x y) : term23 x y.
Proof. exact (proj1 (@lem1998102 x y h1)). Qed.
Lemma lem1998106 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998107 : term91 = term92.
Proof. exact (@lem1998106 term22 term52). Qed.
Lemma lem1998109 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998110 : term52 = term62.
Proof. exact (@lem1998109 term46). Qed.
Lemma lem1998112 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998113 : term22 = term94.
Proof. exact (@lem1998112 (NUMERAL 0)). Qed.
Lemma lem1998114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998115 : term95 = term96.
Proof. exact (MK_COMB (@lem1998114) (@lem1998113)). Qed.
Lemma lem1998116 : term92 = term97.
Proof. exact (MK_COMB (@lem1998115) (@lem1998110)). Qed.
Lemma lem1998117 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1998119 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998120 : term92 = term100.
Proof. exact (@lem1998119 (NUMERAL 0) term46). Qed.
Lemma lem1998121 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998122 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998123 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998122 h1) (fun h1 : term100 = True => @lem1998121)). Qed.
Lemma lem1998124 : term100 = True.
Proof. exact (EQ_MP (@lem1998123) (@lem1998121)). Qed.
Lemma lem1998125 : term92 = True.
Proof. exact (TRANS (@lem1998120) (@lem1998124)). Qed.
Lemma lem1998126 : True = term92.
Proof. exact (SYM (@lem1998125)). Qed.
Lemma lem1998127 : term92.
Proof. exact (EQ_MP (@lem1998126) (@lem0)). Qed.
Lemma lem1998128 : term102.
Proof. exact (@lem1998117 (@lem1998127)). Qed.
Lemma lem1998130 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998131 : term92 = term100.
Proof. exact (@lem1998130 (NUMERAL 0) term46). Qed.
Lemma lem1998132 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998133 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998134 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998133 h1) (fun h1 : term100 = True => @lem1998132)). Qed.
Lemma lem1998135 : term100 = True.
Proof. exact (EQ_MP (@lem1998134) (@lem1998132)). Qed.
Lemma lem1998136 : term92 = True.
Proof. exact (TRANS (@lem1998131) (@lem1998135)). Qed.
Lemma lem1998137 : True = term92.
Proof. exact (SYM (@lem1998136)). Qed.
Lemma lem1998138 : term92.
Proof. exact (EQ_MP (@lem1998137) (@lem0)). Qed.
Lemma lem1998139 : term97 = term103.
Proof. exact (@lem1998128 (@lem1998138)). Qed.
Lemma lem1998141 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998142 : term55 = term56.
Proof. exact (@lem1998141 term46 term46). Qed.
Lemma lem1998143 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998144 : term58 = term46.
Proof. exact (EQ_MP (@lem1998143) (@lem940073)). Qed.
Lemma lem1998145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998146 : term56 = term52.
Proof. exact (MK_COMB (@lem1998145) (@lem1998144)). Qed.
Lemma lem1998147 : term55 = term52.
Proof. exact (TRANS (@lem1998142) (@lem1998146)). Qed.
Lemma lem1998149 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998150 : term105 = term22.
Proof. exact (@lem1998149 term46). Qed.
Lemma lem1998151 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998152 : term106 = term95.
Proof. exact (MK_COMB (@lem1998151) (@lem1998150)). Qed.
Lemma lem1998153 : term103 = term92.
Proof. exact (MK_COMB (@lem1998152) (@lem1998147)). Qed.
Lemma lem1998155 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998156 : term92 = term100.
Proof. exact (@lem1998155 (NUMERAL 0) term46). Qed.
Lemma lem1998157 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998158 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998159 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998158 h1) (fun h1 : term100 = True => @lem1998157)). Qed.
Lemma lem1998160 : term100 = True.
Proof. exact (EQ_MP (@lem1998159) (@lem1998157)). Qed.
Lemma lem1998161 : term92 = True.
Proof. exact (TRANS (@lem1998156) (@lem1998160)). Qed.
Lemma lem1998162 : term103 = True.
Proof. exact (TRANS (@lem1998153) (@lem1998161)). Qed.
Lemma lem1998163 : term97 = True.
Proof. exact (TRANS (@lem1998139) (@lem1998162)). Qed.
Lemma lem1998164 : term92 = True.
Proof. exact (TRANS (@lem1998116) (@lem1998163)). Qed.
Lemma lem1998165 : term91 = True.
Proof. exact (TRANS (@lem1998107) (@lem1998164)). Qed.
Lemma lem1998166 : True = term91.
Proof. exact (SYM (@lem1998165)). Qed.
Lemma lem1998167 : term91.
Proof. exact (EQ_MP (@lem1998166) (@lem0)). Qed.
Lemma lem1998168 (x : real) (y : real) (h1 : term90 x y) : term107 x y.
Proof. exact (conj (@lem1998167) (@lem1998103 x y h1)). Qed.
Lemma lem1998170 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1998171 (x : real) (y : real) : term109 x y.
Proof. exact (@lem1998170 term52 (term17 x y)). Qed.
Lemma lem1998172 (x : real) (y : real) (h1 : term90 x y) : term110 x y.
Proof. exact (@lem1998171 x y (@lem1998168 x y h1)). Qed.
Lemma lem1998173 (x : real) (y : real) : (term111 x y) = (term17 x y).
Proof. exact (@lem1982733 (term17 x y)). Qed.
Lemma lem1998174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1998175 (x : real) (y : real) : (term112 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1998174) (@lem1998173 x y)). Qed.
Lemma lem1998176 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998177 (x : real) (y : real) : (term110 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1998175 x y) (@lem1998176)). Qed.
Lemma lem1998178 (x : real) (y : real) (h1 : term90 x y) : term28 x y.
Proof. exact (EQ_MP (@lem1998177 x y) (@lem1998172 x y h1)). Qed.
Lemma lem1998180 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998181 : term91 = term92.
Proof. exact (@lem1998180 term22 term52). Qed.
Lemma lem1998183 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998184 : term52 = term62.
Proof. exact (@lem1998183 term46). Qed.
Lemma lem1998186 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998187 : term22 = term94.
Proof. exact (@lem1998186 (NUMERAL 0)). Qed.
Lemma lem1998188 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998189 : term95 = term96.
Proof. exact (MK_COMB (@lem1998188) (@lem1998187)). Qed.
Lemma lem1998190 : term92 = term97.
Proof. exact (MK_COMB (@lem1998189) (@lem1998184)). Qed.
Lemma lem1998191 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1998193 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998194 : term92 = term100.
Proof. exact (@lem1998193 (NUMERAL 0) term46). Qed.
Lemma lem1998195 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998196 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998197 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998196 h1) (fun h1 : term100 = True => @lem1998195)). Qed.
Lemma lem1998198 : term100 = True.
Proof. exact (EQ_MP (@lem1998197) (@lem1998195)). Qed.
Lemma lem1998199 : term92 = True.
Proof. exact (TRANS (@lem1998194) (@lem1998198)). Qed.
Lemma lem1998200 : True = term92.
Proof. exact (SYM (@lem1998199)). Qed.
Lemma lem1998201 : term92.
Proof. exact (EQ_MP (@lem1998200) (@lem0)). Qed.
Lemma lem1998202 : term102.
Proof. exact (@lem1998191 (@lem1998201)). Qed.
Lemma lem1998204 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998205 : term92 = term100.
Proof. exact (@lem1998204 (NUMERAL 0) term46). Qed.
Lemma lem1998206 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998207 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998208 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998207 h1) (fun h1 : term100 = True => @lem1998206)). Qed.
Lemma lem1998209 : term100 = True.
Proof. exact (EQ_MP (@lem1998208) (@lem1998206)). Qed.
Lemma lem1998210 : term92 = True.
Proof. exact (TRANS (@lem1998205) (@lem1998209)). Qed.
Lemma lem1998211 : True = term92.
Proof. exact (SYM (@lem1998210)). Qed.
Lemma lem1998212 : term92.
Proof. exact (EQ_MP (@lem1998211) (@lem0)). Qed.
Lemma lem1998213 : term97 = term103.
Proof. exact (@lem1998202 (@lem1998212)). Qed.
Lemma lem1998215 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998216 : term55 = term56.
Proof. exact (@lem1998215 term46 term46). Qed.
Lemma lem1998217 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998218 : term58 = term46.
Proof. exact (EQ_MP (@lem1998217) (@lem940073)). Qed.
Lemma lem1998219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998220 : term56 = term52.
Proof. exact (MK_COMB (@lem1998219) (@lem1998218)). Qed.
Lemma lem1998221 : term55 = term52.
Proof. exact (TRANS (@lem1998216) (@lem1998220)). Qed.
Lemma lem1998223 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998224 : term105 = term22.
Proof. exact (@lem1998223 term46). Qed.
Lemma lem1998225 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998226 : term106 = term95.
Proof. exact (MK_COMB (@lem1998225) (@lem1998224)). Qed.
Lemma lem1998227 : term103 = term92.
Proof. exact (MK_COMB (@lem1998226) (@lem1998221)). Qed.
Lemma lem1998229 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998230 : term92 = term100.
Proof. exact (@lem1998229 (NUMERAL 0) term46). Qed.
Lemma lem1998231 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998232 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998233 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998232 h1) (fun h1 : term100 = True => @lem1998231)). Qed.
Lemma lem1998234 : term100 = True.
Proof. exact (EQ_MP (@lem1998233) (@lem1998231)). Qed.
Lemma lem1998235 : term92 = True.
Proof. exact (TRANS (@lem1998230) (@lem1998234)). Qed.
Lemma lem1998236 : term103 = True.
Proof. exact (TRANS (@lem1998227) (@lem1998235)). Qed.
Lemma lem1998237 : term97 = True.
Proof. exact (TRANS (@lem1998213) (@lem1998236)). Qed.
Lemma lem1998238 : term92 = True.
Proof. exact (TRANS (@lem1998190) (@lem1998237)). Qed.
Lemma lem1998239 : term91 = True.
Proof. exact (TRANS (@lem1998181) (@lem1998238)). Qed.
Lemma lem1998240 : True = term91.
Proof. exact (SYM (@lem1998239)). Qed.
Lemma lem1998241 : term91.
Proof. exact (EQ_MP (@lem1998240) (@lem0)). Qed.
Lemma lem1998242 (x : real) (y : real) (h1 : term90 x y) : term113 x y.
Proof. exact (conj (@lem1998241) (@lem1998104 x y h1)). Qed.
Lemma lem1998244 (x : real) (y : real) : term114 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1998245 (x : real) (y : real) : term115 x y.
Proof. exact (@lem1998244 term52 (term18 x y)). Qed.
Lemma lem1998246 (x : real) (y : real) (h1 : term90 x y) : term116 x y.
Proof. exact (@lem1998245 x y (@lem1998242 x y h1)). Qed.
Lemma lem1998247 (x : real) (y : real) : (term117 x y) = (term18 x y).
Proof. exact (@lem1982733 (term18 x y)). Qed.
Lemma lem1998248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998249 (x : real) (y : real) : (term118 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1998248) (@lem1998247 x y)). Qed.
Lemma lem1998250 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998251 (x : real) (y : real) : (term116 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1998249 x y) (@lem1998250)). Qed.
Lemma lem1998252 (x : real) (y : real) (h1 : term90 x y) : term23 x y.
Proof. exact (EQ_MP (@lem1998251 x y) (@lem1998246 x y h1)). Qed.
Lemma lem1998253 (x : real) (y : real) (h1 : term90 x y) : term90 x y.
Proof. exact (conj (@lem1998252 x y h1) (@lem1998178 x y h1)). Qed.
Lemma lem1998255 (x : real) (y : real) : term119 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1998256 (x : real) (y : real) : term120 x y.
Proof. exact (@lem1998255 (term18 x y) (term17 x y)). Qed.
Lemma lem1998257 (x : real) (y : real) (h1 : term90 x y) : term121 x y.
Proof. exact (@lem1998256 x y (@lem1998253 x y h1)). Qed.
Lemma lem1998258 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (@lem1982753 (term19 x) x y (term19 y)). Qed.
Lemma lem1998259 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1982713 term40 x). Qed.
Lemma lem1998261 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998262 : term52 = term62.
Proof. exact (@lem1998261 term46). Qed.
Lemma lem1998264 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1998265 : term40 = term45.
Proof. exact (@lem1998264 term46). Qed.
Lemma lem1998266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998267 : term126 = term127.
Proof. exact (MK_COMB (@lem1998266) (@lem1998265)). Qed.
Lemma lem1998268 : term128 = term129.
Proof. exact (MK_COMB (@lem1998267) (@lem1998262)). Qed.
Lemma lem1998269 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1998271 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998272 : term92 = term100.
Proof. exact (@lem1998271 (NUMERAL 0) term46). Qed.
Lemma lem1998273 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998274 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998275 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998274 h1) (fun h1 : term100 = True => @lem1998273)). Qed.
Lemma lem1998276 : term100 = True.
Proof. exact (EQ_MP (@lem1998275) (@lem1998273)). Qed.
Lemma lem1998277 : term92 = True.
Proof. exact (TRANS (@lem1998272) (@lem1998276)). Qed.
Lemma lem1998278 : True = term92.
Proof. exact (SYM (@lem1998277)). Qed.
Lemma lem1998279 : term92.
Proof. exact (EQ_MP (@lem1998278) (@lem0)). Qed.
Lemma lem1998280 : term131.
Proof. exact (@lem1998269 (@lem1998279)). Qed.
Lemma lem1998282 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998283 : term92 = term100.
Proof. exact (@lem1998282 (NUMERAL 0) term46). Qed.
Lemma lem1998284 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998285 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998286 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998285 h1) (fun h1 : term100 = True => @lem1998284)). Qed.
Lemma lem1998287 : term100 = True.
Proof. exact (EQ_MP (@lem1998286) (@lem1998284)). Qed.
Lemma lem1998288 : term92 = True.
Proof. exact (TRANS (@lem1998283) (@lem1998287)). Qed.
Lemma lem1998289 : True = term92.
Proof. exact (SYM (@lem1998288)). Qed.
Lemma lem1998290 : term92.
Proof. exact (EQ_MP (@lem1998289) (@lem0)). Qed.
Lemma lem1998291 : term132.
Proof. exact (@lem1998280 (@lem1998290)). Qed.
Lemma lem1998293 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998294 : term92 = term100.
Proof. exact (@lem1998293 (NUMERAL 0) term46). Qed.
Lemma lem1998295 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998296 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998297 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998296 h1) (fun h1 : term100 = True => @lem1998295)). Qed.
Lemma lem1998298 : term100 = True.
Proof. exact (EQ_MP (@lem1998297) (@lem1998295)). Qed.
Lemma lem1998299 : term92 = True.
Proof. exact (TRANS (@lem1998294) (@lem1998298)). Qed.
Lemma lem1998300 : True = term92.
Proof. exact (SYM (@lem1998299)). Qed.
Lemma lem1998301 : term92.
Proof. exact (EQ_MP (@lem1998300) (@lem0)). Qed.
Lemma lem1998302 : term133.
Proof. exact (@lem1998291 (@lem1998301)). Qed.
Lemma lem1998304 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998305 : term55 = term56.
Proof. exact (@lem1998304 term46 term46). Qed.
Lemma lem1998306 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998307 : term58 = term46.
Proof. exact (EQ_MP (@lem1998306) (@lem940073)). Qed.
Lemma lem1998308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998309 : term56 = term52.
Proof. exact (MK_COMB (@lem1998308) (@lem1998307)). Qed.
Lemma lem1998310 : term55 = term52.
Proof. exact (TRANS (@lem1998305) (@lem1998309)). Qed.
Lemma lem1998312 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1998313 : term136 = term137.
Proof. exact (@lem1998312 term46 term46). Qed.
Lemma lem1998314 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998315 : term58 = term46.
Proof. exact (EQ_MP (@lem1998314) (@lem940073)). Qed.
Lemma lem1998316 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998317 : term56 = term52.
Proof. exact (MK_COMB (@lem1998316) (@lem1998315)). Qed.
Lemma lem1998318 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1998319 : term137 = term40.
Proof. exact (MK_COMB (@lem1998318) (@lem1998317)). Qed.
Lemma lem1998320 : term136 = term40.
Proof. exact (TRANS (@lem1998313) (@lem1998319)). Qed.
Lemma lem1998321 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998322 : term138 = term126.
Proof. exact (MK_COMB (@lem1998321) (@lem1998320)). Qed.
Lemma lem1998323 : term139 = term128.
Proof. exact (MK_COMB (@lem1998322) (@lem1998310)). Qed.
Lemma lem1998325 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1998326 : term128 = term22.
Proof. exact (@lem1998325 term46). Qed.
Lemma lem1998327 : term139 = term22.
Proof. exact (TRANS (@lem1998323) (@lem1998326)). Qed.
Lemma lem1998328 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998329 : term141 = term142.
Proof. exact (MK_COMB (@lem1998328) (@lem1998327)). Qed.
Lemma lem1998330 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1998331 : term143 = term105.
Proof. exact (MK_COMB (@lem1998329) (@lem1998330)). Qed.
Lemma lem1998333 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998334 : term105 = term22.
Proof. exact (@lem1998333 term46). Qed.
Lemma lem1998335 : term143 = term22.
Proof. exact (TRANS (@lem1998331) (@lem1998334)). Qed.
Lemma lem1998337 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998338 : term55 = term56.
Proof. exact (@lem1998337 term46 term46). Qed.
Lemma lem1998339 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998340 : term58 = term46.
Proof. exact (EQ_MP (@lem1998339) (@lem940073)). Qed.
Lemma lem1998341 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998342 : term56 = term52.
Proof. exact (MK_COMB (@lem1998341) (@lem1998340)). Qed.
Lemma lem1998343 : term55 = term52.
Proof. exact (TRANS (@lem1998338) (@lem1998342)). Qed.
Lemma lem1998344 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1998345 : term144 = term105.
Proof. exact (MK_COMB (@lem1998344) (@lem1998343)). Qed.
Lemma lem1998347 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998348 : term105 = term22.
Proof. exact (@lem1998347 term46). Qed.
Lemma lem1998349 : term144 = term22.
Proof. exact (TRANS (@lem1998345) (@lem1998348)). Qed.
Lemma lem1998350 : term22 = term144.
Proof. exact (SYM (@lem1998349)). Qed.
Lemma lem1998351 : term143 = term144.
Proof. exact (TRANS (@lem1998335) (@lem1998350)). Qed.
Lemma lem1998352 : term129 = term94.
Proof. exact (@lem1998302 (@lem1998351)). Qed.
Lemma lem1998353 : term128 = term94.
Proof. exact (TRANS (@lem1998268) (@lem1998352)). Qed.
Lemma lem1998355 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1998356 : term94 = term22.
Proof. exact (@lem1998355 term22). Qed.
Lemma lem1998357 : term128 = term22.
Proof. exact (TRANS (@lem1998353) (@lem1998356)). Qed.
Lemma lem1998358 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998359 : term145 = term142.
Proof. exact (MK_COMB (@lem1998358) (@lem1998357)). Qed.
Lemma lem1998360 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1998361 (x : real) : (term125 x) = (term146 x).
Proof. exact (MK_COMB (@lem1998359) (@lem1998360 x)). Qed.
Lemma lem1998362 (x : real) : (term124 x) = (term146 x).
Proof. exact (TRANS (@lem1998259 x) (@lem1998361 x)). Qed.
Lemma lem1998363 (x : real) : (term146 x) = term22.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1998364 (x : real) : (term124 x) = term22.
Proof. exact (TRANS (@lem1998362 x) (@lem1998363 x)). Qed.
Lemma lem1998365 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998366 (x : real) : (term147 x) = term148.
Proof. exact (MK_COMB (@lem1998365) (@lem1998364 x)). Qed.
Lemma lem1998367 (y : real) : (term149 y) = (term125 y).
Proof. exact (@lem1982715 term40 y). Qed.
Lemma lem1998369 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998370 : term52 = term62.
Proof. exact (@lem1998369 term46). Qed.
Lemma lem1998372 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1998373 : term40 = term45.
Proof. exact (@lem1998372 term46). Qed.
Lemma lem1998374 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998375 : term126 = term127.
Proof. exact (MK_COMB (@lem1998374) (@lem1998373)). Qed.
Lemma lem1998376 : term128 = term129.
Proof. exact (MK_COMB (@lem1998375) (@lem1998370)). Qed.
Lemma lem1998377 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1998379 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998380 : term92 = term100.
Proof. exact (@lem1998379 (NUMERAL 0) term46). Qed.
Lemma lem1998381 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998382 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998383 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998382 h1) (fun h1 : term100 = True => @lem1998381)). Qed.
Lemma lem1998384 : term100 = True.
Proof. exact (EQ_MP (@lem1998383) (@lem1998381)). Qed.
Lemma lem1998385 : term92 = True.
Proof. exact (TRANS (@lem1998380) (@lem1998384)). Qed.
Lemma lem1998386 : True = term92.
Proof. exact (SYM (@lem1998385)). Qed.
Lemma lem1998387 : term92.
Proof. exact (EQ_MP (@lem1998386) (@lem0)). Qed.
Lemma lem1998388 : term131.
Proof. exact (@lem1998377 (@lem1998387)). Qed.
Lemma lem1998390 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998391 : term92 = term100.
Proof. exact (@lem1998390 (NUMERAL 0) term46). Qed.
Lemma lem1998392 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998393 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998394 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998393 h1) (fun h1 : term100 = True => @lem1998392)). Qed.
Lemma lem1998395 : term100 = True.
Proof. exact (EQ_MP (@lem1998394) (@lem1998392)). Qed.
Lemma lem1998396 : term92 = True.
Proof. exact (TRANS (@lem1998391) (@lem1998395)). Qed.
Lemma lem1998397 : True = term92.
Proof. exact (SYM (@lem1998396)). Qed.
Lemma lem1998398 : term92.
Proof. exact (EQ_MP (@lem1998397) (@lem0)). Qed.
Lemma lem1998399 : term132.
Proof. exact (@lem1998388 (@lem1998398)). Qed.
Lemma lem1998401 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998402 : term92 = term100.
Proof. exact (@lem1998401 (NUMERAL 0) term46). Qed.
Lemma lem1998403 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998404 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998405 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998404 h1) (fun h1 : term100 = True => @lem1998403)). Qed.
Lemma lem1998406 : term100 = True.
Proof. exact (EQ_MP (@lem1998405) (@lem1998403)). Qed.
Lemma lem1998407 : term92 = True.
Proof. exact (TRANS (@lem1998402) (@lem1998406)). Qed.
Lemma lem1998408 : True = term92.
Proof. exact (SYM (@lem1998407)). Qed.
Lemma lem1998409 : term92.
Proof. exact (EQ_MP (@lem1998408) (@lem0)). Qed.
Lemma lem1998410 : term133.
Proof. exact (@lem1998399 (@lem1998409)). Qed.
Lemma lem1998412 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998413 : term55 = term56.
Proof. exact (@lem1998412 term46 term46). Qed.
Lemma lem1998414 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998415 : term58 = term46.
Proof. exact (EQ_MP (@lem1998414) (@lem940073)). Qed.
Lemma lem1998416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998417 : term56 = term52.
Proof. exact (MK_COMB (@lem1998416) (@lem1998415)). Qed.
Lemma lem1998418 : term55 = term52.
Proof. exact (TRANS (@lem1998413) (@lem1998417)). Qed.
Lemma lem1998420 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1998421 : term136 = term137.
Proof. exact (@lem1998420 term46 term46). Qed.
Lemma lem1998422 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998423 : term58 = term46.
Proof. exact (EQ_MP (@lem1998422) (@lem940073)). Qed.
Lemma lem1998424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998425 : term56 = term52.
Proof. exact (MK_COMB (@lem1998424) (@lem1998423)). Qed.
Lemma lem1998426 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1998427 : term137 = term40.
Proof. exact (MK_COMB (@lem1998426) (@lem1998425)). Qed.
Lemma lem1998428 : term136 = term40.
Proof. exact (TRANS (@lem1998421) (@lem1998427)). Qed.
Lemma lem1998429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998430 : term138 = term126.
Proof. exact (MK_COMB (@lem1998429) (@lem1998428)). Qed.
Lemma lem1998431 : term139 = term128.
Proof. exact (MK_COMB (@lem1998430) (@lem1998418)). Qed.
Lemma lem1998433 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1998434 : term128 = term22.
Proof. exact (@lem1998433 term46). Qed.
Lemma lem1998435 : term139 = term22.
Proof. exact (TRANS (@lem1998431) (@lem1998434)). Qed.
Lemma lem1998436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998437 : term141 = term142.
Proof. exact (MK_COMB (@lem1998436) (@lem1998435)). Qed.
Lemma lem1998438 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1998439 : term143 = term105.
Proof. exact (MK_COMB (@lem1998437) (@lem1998438)). Qed.
Lemma lem1998441 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998442 : term105 = term22.
Proof. exact (@lem1998441 term46). Qed.
Lemma lem1998443 : term143 = term22.
Proof. exact (TRANS (@lem1998439) (@lem1998442)). Qed.
Lemma lem1998445 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998446 : term55 = term56.
Proof. exact (@lem1998445 term46 term46). Qed.
Lemma lem1998447 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998448 : term58 = term46.
Proof. exact (EQ_MP (@lem1998447) (@lem940073)). Qed.
Lemma lem1998449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998450 : term56 = term52.
Proof. exact (MK_COMB (@lem1998449) (@lem1998448)). Qed.
Lemma lem1998451 : term55 = term52.
Proof. exact (TRANS (@lem1998446) (@lem1998450)). Qed.
Lemma lem1998452 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1998453 : term144 = term105.
Proof. exact (MK_COMB (@lem1998452) (@lem1998451)). Qed.
Lemma lem1998455 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998456 : term105 = term22.
Proof. exact (@lem1998455 term46). Qed.
Lemma lem1998457 : term144 = term22.
Proof. exact (TRANS (@lem1998453) (@lem1998456)). Qed.
Lemma lem1998458 : term22 = term144.
Proof. exact (SYM (@lem1998457)). Qed.
Lemma lem1998459 : term143 = term144.
Proof. exact (TRANS (@lem1998443) (@lem1998458)). Qed.
Lemma lem1998460 : term129 = term94.
Proof. exact (@lem1998410 (@lem1998459)). Qed.
Lemma lem1998461 : term128 = term94.
Proof. exact (TRANS (@lem1998376) (@lem1998460)). Qed.
Lemma lem1998463 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1998464 : term94 = term22.
Proof. exact (@lem1998463 term22). Qed.
Lemma lem1998465 : term128 = term22.
Proof. exact (TRANS (@lem1998461) (@lem1998464)). Qed.
Lemma lem1998466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998467 : term145 = term142.
Proof. exact (MK_COMB (@lem1998466) (@lem1998465)). Qed.
Lemma lem1998468 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1998469 (y : real) : (term125 y) = (term146 y).
Proof. exact (MK_COMB (@lem1998467) (@lem1998468 y)). Qed.
Lemma lem1998470 (y : real) : (term149 y) = (term146 y).
Proof. exact (TRANS (@lem1998367 y) (@lem1998469 y)). Qed.
Lemma lem1998471 (y : real) : (term146 y) = term22.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1998472 (y : real) : (term149 y) = term22.
Proof. exact (TRANS (@lem1998470 y) (@lem1998471 y)). Qed.
Lemma lem1998473 (x : real) (y : real) : (term123 x y) = term150.
Proof. exact (MK_COMB (@lem1998366 x) (@lem1998472 y)). Qed.
Lemma lem1998474 (x : real) (y : real) : (term122 x y) = term150.
Proof. exact (TRANS (@lem1998258 x y) (@lem1998473 x y)). Qed.
Lemma lem1998475 : term150 = term22.
Proof. exact (@lem1982721 term22). Qed.
Lemma lem1998476 (x : real) (y : real) : (term122 x y) = term22.
Proof. exact (TRANS (@lem1998474 x y) (@lem1998475)). Qed.
Lemma lem1998477 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998478 (x : real) (y : real) : (term151 x y) = term152.
Proof. exact (MK_COMB (@lem1998477) (@lem1998476 x y)). Qed.
Lemma lem1998479 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998480 (x : real) (y : real) : (term121 x y) = term153.
Proof. exact (MK_COMB (@lem1998478 x y) (@lem1998479)). Qed.
Lemma lem1998481 (x : real) (y : real) (h1 : term90 x y) : term153.
Proof. exact (EQ_MP (@lem1998480 x y) (@lem1998257 x y h1)). Qed.
Lemma lem1998483 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998484 : term153 = term154.
Proof. exact (@lem1998483 term22 term22). Qed.
Lemma lem1998486 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998487 : term22 = term94.
Proof. exact (@lem1998486 (NUMERAL 0)). Qed.
Lemma lem1998489 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998490 : term22 = term94.
Proof. exact (@lem1998489 (NUMERAL 0)). Qed.
Lemma lem1998491 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998492 : term95 = term96.
Proof. exact (MK_COMB (@lem1998491) (@lem1998490)). Qed.
Lemma lem1998493 : term154 = term155.
Proof. exact (MK_COMB (@lem1998492) (@lem1998487)). Qed.
Lemma lem1998494 : term156.
Proof. exact (@lem1980255 term22 term52 term22 term52). Qed.
Lemma lem1998496 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998497 : term92 = term100.
Proof. exact (@lem1998496 (NUMERAL 0) term46). Qed.
Lemma lem1998498 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998499 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998500 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998499 h1) (fun h1 : term100 = True => @lem1998498)). Qed.
Lemma lem1998501 : term100 = True.
Proof. exact (EQ_MP (@lem1998500) (@lem1998498)). Qed.
Lemma lem1998502 : term92 = True.
Proof. exact (TRANS (@lem1998497) (@lem1998501)). Qed.
Lemma lem1998503 : True = term92.
Proof. exact (SYM (@lem1998502)). Qed.
Lemma lem1998504 : term92.
Proof. exact (EQ_MP (@lem1998503) (@lem0)). Qed.
Lemma lem1998505 : term157.
Proof. exact (@lem1998494 (@lem1998504)). Qed.
Lemma lem1998507 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998508 : term92 = term100.
Proof. exact (@lem1998507 (NUMERAL 0) term46). Qed.
Lemma lem1998509 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998510 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998511 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998510 h1) (fun h1 : term100 = True => @lem1998509)). Qed.
Lemma lem1998512 : term100 = True.
Proof. exact (EQ_MP (@lem1998511) (@lem1998509)). Qed.
Lemma lem1998513 : term92 = True.
Proof. exact (TRANS (@lem1998508) (@lem1998512)). Qed.
Lemma lem1998514 : True = term92.
Proof. exact (SYM (@lem1998513)). Qed.
Lemma lem1998515 : term92.
Proof. exact (EQ_MP (@lem1998514) (@lem0)). Qed.
Lemma lem1998516 : term155 = term158.
Proof. exact (@lem1998505 (@lem1998515)). Qed.
Lemma lem1998518 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998519 : term105 = term22.
Proof. exact (@lem1998518 term46). Qed.
Lemma lem1998521 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998522 : term105 = term22.
Proof. exact (@lem1998521 term46). Qed.
Lemma lem1998523 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998524 : term106 = term95.
Proof. exact (MK_COMB (@lem1998523) (@lem1998522)). Qed.
Lemma lem1998525 : term158 = term154.
Proof. exact (MK_COMB (@lem1998524) (@lem1998519)). Qed.
Lemma lem1998527 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998528 : term154 = term159.
Proof. exact (@lem1998527 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1998529 : term159 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1998530 : term154 = False.
Proof. exact (TRANS (@lem1998528) (@lem1998529)). Qed.
Lemma lem1998531 : term158 = False.
Proof. exact (TRANS (@lem1998525) (@lem1998530)). Qed.
Lemma lem1998532 : term155 = False.
Proof. exact (TRANS (@lem1998516) (@lem1998531)). Qed.
Lemma lem1998533 : term154 = False.
Proof. exact (TRANS (@lem1998493) (@lem1998532)). Qed.
Lemma lem1998534 : term153 = False.
Proof. exact (TRANS (@lem1998484) (@lem1998533)). Qed.
Lemma lem1998535 (x : real) (y : real) (h1 : term90 x y) : False.
Proof. exact (EQ_MP (@lem1998534) (@lem1998481 x y h1)). Qed.
Lemma lem1998536 (x : real) (y : real) (h1 : term160 x y) : term160 x y.
Proof. exact (h1). Qed.
Lemma lem1998537 (x : real) (y : real) (h1 : term160 x y) : (term17 x y) = term22.
Proof. exact (proj2 (@lem1998536 x y h1)). Qed.
Lemma lem1998538 (x : real) (y : real) (h1 : term160 x y) : term23 x y.
Proof. exact (proj1 (@lem1998536 x y h1)). Qed.
Lemma lem1998540 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998541 : term91 = term92.
Proof. exact (@lem1998540 term22 term52). Qed.
Lemma lem1998543 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998544 : term52 = term62.
Proof. exact (@lem1998543 term46). Qed.
Lemma lem1998546 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998547 : term22 = term94.
Proof. exact (@lem1998546 (NUMERAL 0)). Qed.
Lemma lem1998548 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998549 : term95 = term96.
Proof. exact (MK_COMB (@lem1998548) (@lem1998547)). Qed.
Lemma lem1998550 : term92 = term97.
Proof. exact (MK_COMB (@lem1998549) (@lem1998544)). Qed.
Lemma lem1998551 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1998553 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998554 : term92 = term100.
Proof. exact (@lem1998553 (NUMERAL 0) term46). Qed.
Lemma lem1998555 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998556 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998557 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998556 h1) (fun h1 : term100 = True => @lem1998555)). Qed.
Lemma lem1998558 : term100 = True.
Proof. exact (EQ_MP (@lem1998557) (@lem1998555)). Qed.
Lemma lem1998559 : term92 = True.
Proof. exact (TRANS (@lem1998554) (@lem1998558)). Qed.
Lemma lem1998560 : True = term92.
Proof. exact (SYM (@lem1998559)). Qed.
Lemma lem1998561 : term92.
Proof. exact (EQ_MP (@lem1998560) (@lem0)). Qed.
Lemma lem1998562 : term102.
Proof. exact (@lem1998551 (@lem1998561)). Qed.
Lemma lem1998564 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998565 : term92 = term100.
Proof. exact (@lem1998564 (NUMERAL 0) term46). Qed.
Lemma lem1998566 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998567 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998568 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998567 h1) (fun h1 : term100 = True => @lem1998566)). Qed.
Lemma lem1998569 : term100 = True.
Proof. exact (EQ_MP (@lem1998568) (@lem1998566)). Qed.
Lemma lem1998570 : term92 = True.
Proof. exact (TRANS (@lem1998565) (@lem1998569)). Qed.
Lemma lem1998571 : True = term92.
Proof. exact (SYM (@lem1998570)). Qed.
Lemma lem1998572 : term92.
Proof. exact (EQ_MP (@lem1998571) (@lem0)). Qed.
Lemma lem1998573 : term97 = term103.
Proof. exact (@lem1998562 (@lem1998572)). Qed.
Lemma lem1998575 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998576 : term55 = term56.
Proof. exact (@lem1998575 term46 term46). Qed.
Lemma lem1998577 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998578 : term58 = term46.
Proof. exact (EQ_MP (@lem1998577) (@lem940073)). Qed.
Lemma lem1998579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998580 : term56 = term52.
Proof. exact (MK_COMB (@lem1998579) (@lem1998578)). Qed.
Lemma lem1998581 : term55 = term52.
Proof. exact (TRANS (@lem1998576) (@lem1998580)). Qed.
Lemma lem1998583 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998584 : term105 = term22.
Proof. exact (@lem1998583 term46). Qed.
Lemma lem1998585 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998586 : term106 = term95.
Proof. exact (MK_COMB (@lem1998585) (@lem1998584)). Qed.
Lemma lem1998587 : term103 = term92.
Proof. exact (MK_COMB (@lem1998586) (@lem1998581)). Qed.
Lemma lem1998589 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998590 : term92 = term100.
Proof. exact (@lem1998589 (NUMERAL 0) term46). Qed.
Lemma lem1998591 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998592 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998593 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998592 h1) (fun h1 : term100 = True => @lem1998591)). Qed.
Lemma lem1998594 : term100 = True.
Proof. exact (EQ_MP (@lem1998593) (@lem1998591)). Qed.
Lemma lem1998595 : term92 = True.
Proof. exact (TRANS (@lem1998590) (@lem1998594)). Qed.
Lemma lem1998596 : term103 = True.
Proof. exact (TRANS (@lem1998587) (@lem1998595)). Qed.
Lemma lem1998597 : term97 = True.
Proof. exact (TRANS (@lem1998573) (@lem1998596)). Qed.
Lemma lem1998598 : term92 = True.
Proof. exact (TRANS (@lem1998550) (@lem1998597)). Qed.
Lemma lem1998599 : term91 = True.
Proof. exact (TRANS (@lem1998541) (@lem1998598)). Qed.
Lemma lem1998600 : True = term91.
Proof. exact (SYM (@lem1998599)). Qed.
Lemma lem1998601 : term91.
Proof. exact (EQ_MP (@lem1998600) (@lem0)). Qed.
Lemma lem1998602 (x : real) (y : real) (h1 : term160 x y) : term113 x y.
Proof. exact (conj (@lem1998601) (@lem1998538 x y h1)). Qed.
Lemma lem1998604 (x : real) (y : real) : term114 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1998605 (x : real) (y : real) : term115 x y.
Proof. exact (@lem1998604 term52 (term18 x y)). Qed.
Lemma lem1998606 (x : real) (y : real) (h1 : term160 x y) : term116 x y.
Proof. exact (@lem1998605 x y (@lem1998602 x y h1)). Qed.
Lemma lem1998607 (x : real) (y : real) : (term117 x y) = (term18 x y).
Proof. exact (@lem1982733 (term18 x y)). Qed.
Lemma lem1998608 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998609 (x : real) (y : real) : (term118 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1998608) (@lem1998607 x y)). Qed.
Lemma lem1998610 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998611 (x : real) (y : real) : (term116 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1998609 x y) (@lem1998610)). Qed.
Lemma lem1998612 (x : real) (y : real) (h1 : term160 x y) : term23 x y.
Proof. exact (EQ_MP (@lem1998611 x y) (@lem1998606 x y h1)). Qed.
Lemma lem1998614 (y : real) : term161 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1998615 (x : real) (y : real) : term162 x y.
Proof. exact (@lem1998614 (term17 x y)). Qed.
Lemma lem1998616 (x : real) (y : real) (h1 : term160 x y) : term163 x y.
Proof. exact (@lem1998615 x y (@lem1998537 x y h1)). Qed.
Lemma lem1998617 (x : real) (y : real) (h1 : term160 x y) : term164 x y.
Proof. exact (@lem1998616 x y h1 term52). Qed.
Lemma lem1998618 (x : real) (y : real) : (term164 x y) = ((term111 x y) = term22).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem1998619 (x : real) (y : real) (h1 : term160 x y) : (term111 x y) = term22.
Proof. exact (EQ_MP (@lem1998618 x y) (@lem1998617 x y h1)). Qed.
Lemma lem1998620 (x : real) (y : real) : (term111 x y) = (term17 x y).
Proof. exact (@lem1982733 (term17 x y)). Qed.
Lemma lem1998621 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1998622 (x : real) (y : real) : (term165 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1998621) (@lem1998620 x y)). Qed.
Lemma lem1998623 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998624 (x : real) (y : real) : ((term111 x y) = term22) = ((term17 x y) = term22).
Proof. exact (MK_COMB (@lem1998622 x y) (@lem1998623)). Qed.
Lemma lem1998625 (x : real) (y : real) (h1 : term160 x y) : (term17 x y) = term22.
Proof. exact (EQ_MP (@lem1998624 x y) (@lem1998619 x y h1)). Qed.
Lemma lem1998626 (x : real) (y : real) (h1 : term160 x y) : term166 x y.
Proof. exact (conj (@lem1998625 x y h1) (@lem1998612 x y h1)). Qed.
Lemma lem1998628 (x : real) (y : real) : term167 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem1998629 (x : real) (y : real) : term168 x y.
Proof. exact (@lem1998628 (term17 x y) (term18 x y)). Qed.
Lemma lem1998630 (x : real) (y : real) (h1 : term160 x y) : term169 x y.
Proof. exact (@lem1998629 x y (@lem1998626 x y h1)). Qed.
Lemma lem1998631 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (@lem1982753 x (term19 x) (term19 y) y). Qed.
Lemma lem1998632 (x : real) : (term149 x) = (term125 x).
Proof. exact (@lem1982715 term40 x). Qed.
Lemma lem1998634 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998635 : term52 = term62.
Proof. exact (@lem1998634 term46). Qed.
Lemma lem1998637 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1998638 : term40 = term45.
Proof. exact (@lem1998637 term46). Qed.
Lemma lem1998639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998640 : term126 = term127.
Proof. exact (MK_COMB (@lem1998639) (@lem1998638)). Qed.
Lemma lem1998641 : term128 = term129.
Proof. exact (MK_COMB (@lem1998640) (@lem1998635)). Qed.
Lemma lem1998642 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1998644 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998645 : term92 = term100.
Proof. exact (@lem1998644 (NUMERAL 0) term46). Qed.
Lemma lem1998646 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998647 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998648 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998647 h1) (fun h1 : term100 = True => @lem1998646)). Qed.
Lemma lem1998649 : term100 = True.
Proof. exact (EQ_MP (@lem1998648) (@lem1998646)). Qed.
Lemma lem1998650 : term92 = True.
Proof. exact (TRANS (@lem1998645) (@lem1998649)). Qed.
Lemma lem1998651 : True = term92.
Proof. exact (SYM (@lem1998650)). Qed.
Lemma lem1998652 : term92.
Proof. exact (EQ_MP (@lem1998651) (@lem0)). Qed.
Lemma lem1998653 : term131.
Proof. exact (@lem1998642 (@lem1998652)). Qed.
Lemma lem1998655 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998656 : term92 = term100.
Proof. exact (@lem1998655 (NUMERAL 0) term46). Qed.
Lemma lem1998657 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998658 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998659 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998658 h1) (fun h1 : term100 = True => @lem1998657)). Qed.
Lemma lem1998660 : term100 = True.
Proof. exact (EQ_MP (@lem1998659) (@lem1998657)). Qed.
Lemma lem1998661 : term92 = True.
Proof. exact (TRANS (@lem1998656) (@lem1998660)). Qed.
Lemma lem1998662 : True = term92.
Proof. exact (SYM (@lem1998661)). Qed.
Lemma lem1998663 : term92.
Proof. exact (EQ_MP (@lem1998662) (@lem0)). Qed.
Lemma lem1998664 : term132.
Proof. exact (@lem1998653 (@lem1998663)). Qed.
Lemma lem1998666 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998667 : term92 = term100.
Proof. exact (@lem1998666 (NUMERAL 0) term46). Qed.
Lemma lem1998668 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998669 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998670 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998669 h1) (fun h1 : term100 = True => @lem1998668)). Qed.
Lemma lem1998671 : term100 = True.
Proof. exact (EQ_MP (@lem1998670) (@lem1998668)). Qed.
Lemma lem1998672 : term92 = True.
Proof. exact (TRANS (@lem1998667) (@lem1998671)). Qed.
Lemma lem1998673 : True = term92.
Proof. exact (SYM (@lem1998672)). Qed.
Lemma lem1998674 : term92.
Proof. exact (EQ_MP (@lem1998673) (@lem0)). Qed.
Lemma lem1998675 : term133.
Proof. exact (@lem1998664 (@lem1998674)). Qed.
Lemma lem1998677 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998678 : term55 = term56.
Proof. exact (@lem1998677 term46 term46). Qed.
Lemma lem1998679 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998680 : term58 = term46.
Proof. exact (EQ_MP (@lem1998679) (@lem940073)). Qed.
Lemma lem1998681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998682 : term56 = term52.
Proof. exact (MK_COMB (@lem1998681) (@lem1998680)). Qed.
Lemma lem1998683 : term55 = term52.
Proof. exact (TRANS (@lem1998678) (@lem1998682)). Qed.
Lemma lem1998685 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1998686 : term136 = term137.
Proof. exact (@lem1998685 term46 term46). Qed.
Lemma lem1998687 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998688 : term58 = term46.
Proof. exact (EQ_MP (@lem1998687) (@lem940073)). Qed.
Lemma lem1998689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998690 : term56 = term52.
Proof. exact (MK_COMB (@lem1998689) (@lem1998688)). Qed.
Lemma lem1998691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1998692 : term137 = term40.
Proof. exact (MK_COMB (@lem1998691) (@lem1998690)). Qed.
Lemma lem1998693 : term136 = term40.
Proof. exact (TRANS (@lem1998686) (@lem1998692)). Qed.
Lemma lem1998694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998695 : term138 = term126.
Proof. exact (MK_COMB (@lem1998694) (@lem1998693)). Qed.
Lemma lem1998696 : term139 = term128.
Proof. exact (MK_COMB (@lem1998695) (@lem1998683)). Qed.
Lemma lem1998698 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1998699 : term128 = term22.
Proof. exact (@lem1998698 term46). Qed.
Lemma lem1998700 : term139 = term22.
Proof. exact (TRANS (@lem1998696) (@lem1998699)). Qed.
Lemma lem1998701 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998702 : term141 = term142.
Proof. exact (MK_COMB (@lem1998701) (@lem1998700)). Qed.
Lemma lem1998703 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1998704 : term143 = term105.
Proof. exact (MK_COMB (@lem1998702) (@lem1998703)). Qed.
Lemma lem1998706 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998707 : term105 = term22.
Proof. exact (@lem1998706 term46). Qed.
Lemma lem1998708 : term143 = term22.
Proof. exact (TRANS (@lem1998704) (@lem1998707)). Qed.
Lemma lem1998710 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998711 : term55 = term56.
Proof. exact (@lem1998710 term46 term46). Qed.
Lemma lem1998712 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998713 : term58 = term46.
Proof. exact (EQ_MP (@lem1998712) (@lem940073)). Qed.
Lemma lem1998714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998715 : term56 = term52.
Proof. exact (MK_COMB (@lem1998714) (@lem1998713)). Qed.
Lemma lem1998716 : term55 = term52.
Proof. exact (TRANS (@lem1998711) (@lem1998715)). Qed.
Lemma lem1998717 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1998718 : term144 = term105.
Proof. exact (MK_COMB (@lem1998717) (@lem1998716)). Qed.
Lemma lem1998720 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998721 : term105 = term22.
Proof. exact (@lem1998720 term46). Qed.
Lemma lem1998722 : term144 = term22.
Proof. exact (TRANS (@lem1998718) (@lem1998721)). Qed.
Lemma lem1998723 : term22 = term144.
Proof. exact (SYM (@lem1998722)). Qed.
Lemma lem1998724 : term143 = term144.
Proof. exact (TRANS (@lem1998708) (@lem1998723)). Qed.
Lemma lem1998725 : term129 = term94.
Proof. exact (@lem1998675 (@lem1998724)). Qed.
Lemma lem1998726 : term128 = term94.
Proof. exact (TRANS (@lem1998641) (@lem1998725)). Qed.
Lemma lem1998728 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1998729 : term94 = term22.
Proof. exact (@lem1998728 term22). Qed.
Lemma lem1998730 : term128 = term22.
Proof. exact (TRANS (@lem1998726) (@lem1998729)). Qed.
Lemma lem1998731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998732 : term145 = term142.
Proof. exact (MK_COMB (@lem1998731) (@lem1998730)). Qed.
Lemma lem1998733 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1998734 (x : real) : (term125 x) = (term146 x).
Proof. exact (MK_COMB (@lem1998732) (@lem1998733 x)). Qed.
Lemma lem1998735 (x : real) : (term149 x) = (term146 x).
Proof. exact (TRANS (@lem1998632 x) (@lem1998734 x)). Qed.
Lemma lem1998736 (x : real) : (term146 x) = term22.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1998737 (x : real) : (term149 x) = term22.
Proof. exact (TRANS (@lem1998735 x) (@lem1998736 x)). Qed.
Lemma lem1998738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998739 (x : real) : (term172 x) = term148.
Proof. exact (MK_COMB (@lem1998738) (@lem1998737 x)). Qed.
Lemma lem1998740 (y : real) : (term124 y) = (term125 y).
Proof. exact (@lem1982713 term40 y). Qed.
Lemma lem1998742 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998743 : term52 = term62.
Proof. exact (@lem1998742 term46). Qed.
Lemma lem1998745 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1998746 : term40 = term45.
Proof. exact (@lem1998745 term46). Qed.
Lemma lem1998747 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998748 : term126 = term127.
Proof. exact (MK_COMB (@lem1998747) (@lem1998746)). Qed.
Lemma lem1998749 : term128 = term129.
Proof. exact (MK_COMB (@lem1998748) (@lem1998743)). Qed.
Lemma lem1998750 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1998752 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998753 : term92 = term100.
Proof. exact (@lem1998752 (NUMERAL 0) term46). Qed.
Lemma lem1998754 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998755 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998756 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998755 h1) (fun h1 : term100 = True => @lem1998754)). Qed.
Lemma lem1998757 : term100 = True.
Proof. exact (EQ_MP (@lem1998756) (@lem1998754)). Qed.
Lemma lem1998758 : term92 = True.
Proof. exact (TRANS (@lem1998753) (@lem1998757)). Qed.
Lemma lem1998759 : True = term92.
Proof. exact (SYM (@lem1998758)). Qed.
Lemma lem1998760 : term92.
Proof. exact (EQ_MP (@lem1998759) (@lem0)). Qed.
Lemma lem1998761 : term131.
Proof. exact (@lem1998750 (@lem1998760)). Qed.
Lemma lem1998763 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998764 : term92 = term100.
Proof. exact (@lem1998763 (NUMERAL 0) term46). Qed.
Lemma lem1998765 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998766 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998767 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998766 h1) (fun h1 : term100 = True => @lem1998765)). Qed.
Lemma lem1998768 : term100 = True.
Proof. exact (EQ_MP (@lem1998767) (@lem1998765)). Qed.
Lemma lem1998769 : term92 = True.
Proof. exact (TRANS (@lem1998764) (@lem1998768)). Qed.
Lemma lem1998770 : True = term92.
Proof. exact (SYM (@lem1998769)). Qed.
Lemma lem1998771 : term92.
Proof. exact (EQ_MP (@lem1998770) (@lem0)). Qed.
Lemma lem1998772 : term132.
Proof. exact (@lem1998761 (@lem1998771)). Qed.
Lemma lem1998774 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998775 : term92 = term100.
Proof. exact (@lem1998774 (NUMERAL 0) term46). Qed.
Lemma lem1998776 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998777 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998778 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998777 h1) (fun h1 : term100 = True => @lem1998776)). Qed.
Lemma lem1998779 : term100 = True.
Proof. exact (EQ_MP (@lem1998778) (@lem1998776)). Qed.
Lemma lem1998780 : term92 = True.
Proof. exact (TRANS (@lem1998775) (@lem1998779)). Qed.
Lemma lem1998781 : True = term92.
Proof. exact (SYM (@lem1998780)). Qed.
Lemma lem1998782 : term92.
Proof. exact (EQ_MP (@lem1998781) (@lem0)). Qed.
Lemma lem1998783 : term133.
Proof. exact (@lem1998772 (@lem1998782)). Qed.
Lemma lem1998785 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998786 : term55 = term56.
Proof. exact (@lem1998785 term46 term46). Qed.
Lemma lem1998787 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998788 : term58 = term46.
Proof. exact (EQ_MP (@lem1998787) (@lem940073)). Qed.
Lemma lem1998789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998790 : term56 = term52.
Proof. exact (MK_COMB (@lem1998789) (@lem1998788)). Qed.
Lemma lem1998791 : term55 = term52.
Proof. exact (TRANS (@lem1998786) (@lem1998790)). Qed.
Lemma lem1998793 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1998794 : term136 = term137.
Proof. exact (@lem1998793 term46 term46). Qed.
Lemma lem1998795 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998796 : term58 = term46.
Proof. exact (EQ_MP (@lem1998795) (@lem940073)). Qed.
Lemma lem1998797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998798 : term56 = term52.
Proof. exact (MK_COMB (@lem1998797) (@lem1998796)). Qed.
Lemma lem1998799 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1998800 : term137 = term40.
Proof. exact (MK_COMB (@lem1998799) (@lem1998798)). Qed.
Lemma lem1998801 : term136 = term40.
Proof. exact (TRANS (@lem1998794) (@lem1998800)). Qed.
Lemma lem1998802 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1998803 : term138 = term126.
Proof. exact (MK_COMB (@lem1998802) (@lem1998801)). Qed.
Lemma lem1998804 : term139 = term128.
Proof. exact (MK_COMB (@lem1998803) (@lem1998791)). Qed.
Lemma lem1998806 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1998807 : term128 = term22.
Proof. exact (@lem1998806 term46). Qed.
Lemma lem1998808 : term139 = term22.
Proof. exact (TRANS (@lem1998804) (@lem1998807)). Qed.
Lemma lem1998809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998810 : term141 = term142.
Proof. exact (MK_COMB (@lem1998809) (@lem1998808)). Qed.
Lemma lem1998811 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1998812 : term143 = term105.
Proof. exact (MK_COMB (@lem1998810) (@lem1998811)). Qed.
Lemma lem1998814 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998815 : term105 = term22.
Proof. exact (@lem1998814 term46). Qed.
Lemma lem1998816 : term143 = term22.
Proof. exact (TRANS (@lem1998812) (@lem1998815)). Qed.
Lemma lem1998818 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998819 : term55 = term56.
Proof. exact (@lem1998818 term46 term46). Qed.
Lemma lem1998820 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998821 : term58 = term46.
Proof. exact (EQ_MP (@lem1998820) (@lem940073)). Qed.
Lemma lem1998822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998823 : term56 = term52.
Proof. exact (MK_COMB (@lem1998822) (@lem1998821)). Qed.
Lemma lem1998824 : term55 = term52.
Proof. exact (TRANS (@lem1998819) (@lem1998823)). Qed.
Lemma lem1998825 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1998826 : term144 = term105.
Proof. exact (MK_COMB (@lem1998825) (@lem1998824)). Qed.
Lemma lem1998828 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998829 : term105 = term22.
Proof. exact (@lem1998828 term46). Qed.
Lemma lem1998830 : term144 = term22.
Proof. exact (TRANS (@lem1998826) (@lem1998829)). Qed.
Lemma lem1998831 : term22 = term144.
Proof. exact (SYM (@lem1998830)). Qed.
Lemma lem1998832 : term143 = term144.
Proof. exact (TRANS (@lem1998816) (@lem1998831)). Qed.
Lemma lem1998833 : term129 = term94.
Proof. exact (@lem1998783 (@lem1998832)). Qed.
Lemma lem1998834 : term128 = term94.
Proof. exact (TRANS (@lem1998749) (@lem1998833)). Qed.
Lemma lem1998836 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1998837 : term94 = term22.
Proof. exact (@lem1998836 term22). Qed.
Lemma lem1998838 : term128 = term22.
Proof. exact (TRANS (@lem1998834) (@lem1998837)). Qed.
Lemma lem1998839 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1998840 : term145 = term142.
Proof. exact (MK_COMB (@lem1998839) (@lem1998838)). Qed.
Lemma lem1998841 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1998842 (y : real) : (term125 y) = (term146 y).
Proof. exact (MK_COMB (@lem1998840) (@lem1998841 y)). Qed.
Lemma lem1998843 (y : real) : (term124 y) = (term146 y).
Proof. exact (TRANS (@lem1998740 y) (@lem1998842 y)). Qed.
Lemma lem1998844 (y : real) : (term146 y) = term22.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1998845 (y : real) : (term124 y) = term22.
Proof. exact (TRANS (@lem1998843 y) (@lem1998844 y)). Qed.
Lemma lem1998846 (x : real) (y : real) : (term171 x y) = term150.
Proof. exact (MK_COMB (@lem1998739 x) (@lem1998845 y)). Qed.
Lemma lem1998847 (x : real) (y : real) : (term170 x y) = term150.
Proof. exact (TRANS (@lem1998631 x y) (@lem1998846 x y)). Qed.
Lemma lem1998848 : term150 = term22.
Proof. exact (@lem1982721 term22). Qed.
Lemma lem1998849 (x : real) (y : real) : (term170 x y) = term22.
Proof. exact (TRANS (@lem1998847 x y) (@lem1998848)). Qed.
Lemma lem1998850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998851 (x : real) (y : real) : (term173 x y) = term152.
Proof. exact (MK_COMB (@lem1998850) (@lem1998849 x y)). Qed.
Lemma lem1998852 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998853 (x : real) (y : real) : (term169 x y) = term153.
Proof. exact (MK_COMB (@lem1998851 x y) (@lem1998852)). Qed.
Lemma lem1998854 (x : real) (y : real) (h1 : term160 x y) : term153.
Proof. exact (EQ_MP (@lem1998853 x y) (@lem1998630 x y h1)). Qed.
Lemma lem1998856 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998857 : term153 = term154.
Proof. exact (@lem1998856 term22 term22). Qed.
Lemma lem1998859 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998860 : term22 = term94.
Proof. exact (@lem1998859 (NUMERAL 0)). Qed.
Lemma lem1998862 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998863 : term22 = term94.
Proof. exact (@lem1998862 (NUMERAL 0)). Qed.
Lemma lem1998864 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998865 : term95 = term96.
Proof. exact (MK_COMB (@lem1998864) (@lem1998863)). Qed.
Lemma lem1998866 : term154 = term155.
Proof. exact (MK_COMB (@lem1998865) (@lem1998860)). Qed.
Lemma lem1998867 : term156.
Proof. exact (@lem1980255 term22 term52 term22 term52). Qed.
Lemma lem1998869 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998870 : term92 = term100.
Proof. exact (@lem1998869 (NUMERAL 0) term46). Qed.
Lemma lem1998871 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998872 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998873 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998872 h1) (fun h1 : term100 = True => @lem1998871)). Qed.
Lemma lem1998874 : term100 = True.
Proof. exact (EQ_MP (@lem1998873) (@lem1998871)). Qed.
Lemma lem1998875 : term92 = True.
Proof. exact (TRANS (@lem1998870) (@lem1998874)). Qed.
Lemma lem1998876 : True = term92.
Proof. exact (SYM (@lem1998875)). Qed.
Lemma lem1998877 : term92.
Proof. exact (EQ_MP (@lem1998876) (@lem0)). Qed.
Lemma lem1998878 : term157.
Proof. exact (@lem1998867 (@lem1998877)). Qed.
Lemma lem1998880 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998881 : term92 = term100.
Proof. exact (@lem1998880 (NUMERAL 0) term46). Qed.
Lemma lem1998882 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998883 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998884 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998883 h1) (fun h1 : term100 = True => @lem1998882)). Qed.
Lemma lem1998885 : term100 = True.
Proof. exact (EQ_MP (@lem1998884) (@lem1998882)). Qed.
Lemma lem1998886 : term92 = True.
Proof. exact (TRANS (@lem1998881) (@lem1998885)). Qed.
Lemma lem1998887 : True = term92.
Proof. exact (SYM (@lem1998886)). Qed.
Lemma lem1998888 : term92.
Proof. exact (EQ_MP (@lem1998887) (@lem0)). Qed.
Lemma lem1998889 : term155 = term158.
Proof. exact (@lem1998878 (@lem1998888)). Qed.
Lemma lem1998891 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998892 : term105 = term22.
Proof. exact (@lem1998891 term46). Qed.
Lemma lem1998894 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998895 : term105 = term22.
Proof. exact (@lem1998894 term46). Qed.
Lemma lem1998896 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998897 : term106 = term95.
Proof. exact (MK_COMB (@lem1998896) (@lem1998895)). Qed.
Lemma lem1998898 : term158 = term154.
Proof. exact (MK_COMB (@lem1998897) (@lem1998892)). Qed.
Lemma lem1998900 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998901 : term154 = term159.
Proof. exact (@lem1998900 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1998902 : term159 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1998903 : term154 = False.
Proof. exact (TRANS (@lem1998901) (@lem1998902)). Qed.
Lemma lem1998904 : term158 = False.
Proof. exact (TRANS (@lem1998898) (@lem1998903)). Qed.
Lemma lem1998905 : term155 = False.
Proof. exact (TRANS (@lem1998889) (@lem1998904)). Qed.
Lemma lem1998906 : term154 = False.
Proof. exact (TRANS (@lem1998866) (@lem1998905)). Qed.
Lemma lem1998907 : term153 = False.
Proof. exact (TRANS (@lem1998857) (@lem1998906)). Qed.
Lemma lem1998908 (x : real) (y : real) (h1 : term160 x y) : False.
Proof. exact (EQ_MP (@lem1998907) (@lem1998854 x y h1)). Qed.
Lemma lem1998909 (x : real) (y : real) (h1 : term87 x y) : False.
Proof. exact (or_elim (@lem1998101 x y h1) (fun h0 : term90 x y => @lem1998535 x y h0) (fun h0 : term160 x y => @lem1998908 x y h0)). Qed.
Lemma lem1998910 (x : real) (y : real) (h1 : term84 x y) : term84 x y.
Proof. exact (h1). Qed.
Lemma lem1998911 (x : real) (y : real) (h1 : term174 x y) : term174 x y.
Proof. exact (h1). Qed.
Lemma lem1998912 (x : real) (y : real) (h1 : term174 x y) : term85 x y.
Proof. exact (proj2 (@lem1998911 x y h1)). Qed.
Lemma lem1998914 (x : real) (y : real) (h1 : term174 x y) : term72 x y.
Proof. exact (proj2 (@lem1998912 x y h1)). Qed.
Lemma lem1998915 (x : real) (y : real) (h1 : term174 x y) : term23 x y.
Proof. exact (proj1 (@lem1998912 x y h1)). Qed.
Lemma lem1998917 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998918 : term91 = term92.
Proof. exact (@lem1998917 term22 term52). Qed.
Lemma lem1998920 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998921 : term52 = term62.
Proof. exact (@lem1998920 term46). Qed.
Lemma lem1998923 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998924 : term22 = term94.
Proof. exact (@lem1998923 (NUMERAL 0)). Qed.
Lemma lem1998925 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998926 : term95 = term96.
Proof. exact (MK_COMB (@lem1998925) (@lem1998924)). Qed.
Lemma lem1998927 : term92 = term97.
Proof. exact (MK_COMB (@lem1998926) (@lem1998921)). Qed.
Lemma lem1998928 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1998930 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998931 : term92 = term100.
Proof. exact (@lem1998930 (NUMERAL 0) term46). Qed.
Lemma lem1998932 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998933 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998934 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998933 h1) (fun h1 : term100 = True => @lem1998932)). Qed.
Lemma lem1998935 : term100 = True.
Proof. exact (EQ_MP (@lem1998934) (@lem1998932)). Qed.
Lemma lem1998936 : term92 = True.
Proof. exact (TRANS (@lem1998931) (@lem1998935)). Qed.
Lemma lem1998937 : True = term92.
Proof. exact (SYM (@lem1998936)). Qed.
Lemma lem1998938 : term92.
Proof. exact (EQ_MP (@lem1998937) (@lem0)). Qed.
Lemma lem1998939 : term102.
Proof. exact (@lem1998928 (@lem1998938)). Qed.
Lemma lem1998941 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998942 : term92 = term100.
Proof. exact (@lem1998941 (NUMERAL 0) term46). Qed.
Lemma lem1998943 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998944 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998945 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998944 h1) (fun h1 : term100 = True => @lem1998943)). Qed.
Lemma lem1998946 : term100 = True.
Proof. exact (EQ_MP (@lem1998945) (@lem1998943)). Qed.
Lemma lem1998947 : term92 = True.
Proof. exact (TRANS (@lem1998942) (@lem1998946)). Qed.
Lemma lem1998948 : True = term92.
Proof. exact (SYM (@lem1998947)). Qed.
Lemma lem1998949 : term92.
Proof. exact (EQ_MP (@lem1998948) (@lem0)). Qed.
Lemma lem1998950 : term97 = term103.
Proof. exact (@lem1998939 (@lem1998949)). Qed.
Lemma lem1998952 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1998953 : term55 = term56.
Proof. exact (@lem1998952 term46 term46). Qed.
Lemma lem1998954 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1998955 : term58 = term46.
Proof. exact (EQ_MP (@lem1998954) (@lem940073)). Qed.
Lemma lem1998956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1998957 : term56 = term52.
Proof. exact (MK_COMB (@lem1998956) (@lem1998955)). Qed.
Lemma lem1998958 : term55 = term52.
Proof. exact (TRANS (@lem1998953) (@lem1998957)). Qed.
Lemma lem1998960 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1998961 : term105 = term22.
Proof. exact (@lem1998960 term46). Qed.
Lemma lem1998962 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1998963 : term106 = term95.
Proof. exact (MK_COMB (@lem1998962) (@lem1998961)). Qed.
Lemma lem1998964 : term103 = term92.
Proof. exact (MK_COMB (@lem1998963) (@lem1998958)). Qed.
Lemma lem1998966 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1998967 : term92 = term100.
Proof. exact (@lem1998966 (NUMERAL 0) term46). Qed.
Lemma lem1998968 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1998969 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1998970 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1998969 h1) (fun h1 : term100 = True => @lem1998968)). Qed.
Lemma lem1998971 : term100 = True.
Proof. exact (EQ_MP (@lem1998970) (@lem1998968)). Qed.
Lemma lem1998972 : term92 = True.
Proof. exact (TRANS (@lem1998967) (@lem1998971)). Qed.
Lemma lem1998973 : term103 = True.
Proof. exact (TRANS (@lem1998964) (@lem1998972)). Qed.
Lemma lem1998974 : term97 = True.
Proof. exact (TRANS (@lem1998950) (@lem1998973)). Qed.
Lemma lem1998975 : term92 = True.
Proof. exact (TRANS (@lem1998927) (@lem1998974)). Qed.
Lemma lem1998976 : term91 = True.
Proof. exact (TRANS (@lem1998918) (@lem1998975)). Qed.
Lemma lem1998977 : True = term91.
Proof. exact (SYM (@lem1998976)). Qed.
Lemma lem1998978 : term91.
Proof. exact (EQ_MP (@lem1998977) (@lem0)). Qed.
Lemma lem1998979 (x : real) (y : real) (h1 : term174 x y) : term113 x y.
Proof. exact (conj (@lem1998978) (@lem1998915 x y h1)). Qed.
Lemma lem1998981 (x : real) (y : real) : term114 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1998982 (x : real) (y : real) : term115 x y.
Proof. exact (@lem1998981 term52 (term18 x y)). Qed.
Lemma lem1998983 (x : real) (y : real) (h1 : term174 x y) : term116 x y.
Proof. exact (@lem1998982 x y (@lem1998979 x y h1)). Qed.
Lemma lem1998984 (x : real) (y : real) : (term117 x y) = (term18 x y).
Proof. exact (@lem1982733 (term18 x y)). Qed.
Lemma lem1998985 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1998986 (x : real) (y : real) : (term118 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1998985) (@lem1998984 x y)). Qed.
Lemma lem1998987 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1998988 (x : real) (y : real) : (term116 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1998986 x y) (@lem1998987)). Qed.
Lemma lem1998989 (x : real) (y : real) (h1 : term174 x y) : term23 x y.
Proof. exact (EQ_MP (@lem1998988 x y) (@lem1998983 x y h1)). Qed.
Lemma lem1998991 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1998992 : term91 = term92.
Proof. exact (@lem1998991 term22 term52). Qed.
Lemma lem1998994 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998995 : term52 = term62.
Proof. exact (@lem1998994 term46). Qed.
Lemma lem1998997 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1998998 : term22 = term94.
Proof. exact (@lem1998997 (NUMERAL 0)). Qed.
Lemma lem1998999 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999000 : term95 = term96.
Proof. exact (MK_COMB (@lem1998999) (@lem1998998)). Qed.
Lemma lem1999001 : term92 = term97.
Proof. exact (MK_COMB (@lem1999000) (@lem1998995)). Qed.
Lemma lem1999002 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1999004 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999005 : term92 = term100.
Proof. exact (@lem1999004 (NUMERAL 0) term46). Qed.
Lemma lem1999006 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999007 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999008 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999007 h1) (fun h1 : term100 = True => @lem1999006)). Qed.
Lemma lem1999009 : term100 = True.
Proof. exact (EQ_MP (@lem1999008) (@lem1999006)). Qed.
Lemma lem1999010 : term92 = True.
Proof. exact (TRANS (@lem1999005) (@lem1999009)). Qed.
Lemma lem1999011 : True = term92.
Proof. exact (SYM (@lem1999010)). Qed.
Lemma lem1999012 : term92.
Proof. exact (EQ_MP (@lem1999011) (@lem0)). Qed.
Lemma lem1999013 : term102.
Proof. exact (@lem1999002 (@lem1999012)). Qed.
Lemma lem1999015 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999016 : term92 = term100.
Proof. exact (@lem1999015 (NUMERAL 0) term46). Qed.
Lemma lem1999017 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999018 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999019 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999018 h1) (fun h1 : term100 = True => @lem1999017)). Qed.
Lemma lem1999020 : term100 = True.
Proof. exact (EQ_MP (@lem1999019) (@lem1999017)). Qed.
Lemma lem1999021 : term92 = True.
Proof. exact (TRANS (@lem1999016) (@lem1999020)). Qed.
Lemma lem1999022 : True = term92.
Proof. exact (SYM (@lem1999021)). Qed.
Lemma lem1999023 : term92.
Proof. exact (EQ_MP (@lem1999022) (@lem0)). Qed.
Lemma lem1999024 : term97 = term103.
Proof. exact (@lem1999013 (@lem1999023)). Qed.
Lemma lem1999026 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999027 : term55 = term56.
Proof. exact (@lem1999026 term46 term46). Qed.
Lemma lem1999028 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999029 : term58 = term46.
Proof. exact (EQ_MP (@lem1999028) (@lem940073)). Qed.
Lemma lem1999030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999031 : term56 = term52.
Proof. exact (MK_COMB (@lem1999030) (@lem1999029)). Qed.
Lemma lem1999032 : term55 = term52.
Proof. exact (TRANS (@lem1999027) (@lem1999031)). Qed.
Lemma lem1999034 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999035 : term105 = term22.
Proof. exact (@lem1999034 term46). Qed.
Lemma lem1999036 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999037 : term106 = term95.
Proof. exact (MK_COMB (@lem1999036) (@lem1999035)). Qed.
Lemma lem1999038 : term103 = term92.
Proof. exact (MK_COMB (@lem1999037) (@lem1999032)). Qed.
Lemma lem1999040 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999041 : term92 = term100.
Proof. exact (@lem1999040 (NUMERAL 0) term46). Qed.
Lemma lem1999042 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999043 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999044 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999043 h1) (fun h1 : term100 = True => @lem1999042)). Qed.
Lemma lem1999045 : term100 = True.
Proof. exact (EQ_MP (@lem1999044) (@lem1999042)). Qed.
Lemma lem1999046 : term92 = True.
Proof. exact (TRANS (@lem1999041) (@lem1999045)). Qed.
Lemma lem1999047 : term103 = True.
Proof. exact (TRANS (@lem1999038) (@lem1999046)). Qed.
Lemma lem1999048 : term97 = True.
Proof. exact (TRANS (@lem1999024) (@lem1999047)). Qed.
Lemma lem1999049 : term92 = True.
Proof. exact (TRANS (@lem1999001) (@lem1999048)). Qed.
Lemma lem1999050 : term91 = True.
Proof. exact (TRANS (@lem1998992) (@lem1999049)). Qed.
Lemma lem1999051 : True = term91.
Proof. exact (SYM (@lem1999050)). Qed.
Lemma lem1999052 : term91.
Proof. exact (EQ_MP (@lem1999051) (@lem0)). Qed.
Lemma lem1999053 (x : real) (y : real) (h1 : term174 x y) : term175 x y.
Proof. exact (conj (@lem1999052) (@lem1998914 x y h1)). Qed.
Lemma lem1999055 (x : real) (y : real) : term114 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1999056 (x : real) (y : real) : term176 x y.
Proof. exact (@lem1999055 term52 (term17 x y)). Qed.
Lemma lem1999057 (x : real) (y : real) (h1 : term174 x y) : term177 x y.
Proof. exact (@lem1999056 x y (@lem1999053 x y h1)). Qed.
Lemma lem1999058 (x : real) (y : real) : (term111 x y) = (term17 x y).
Proof. exact (@lem1982733 (term17 x y)). Qed.
Lemma lem1999059 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1999060 (x : real) (y : real) : (term178 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1999059) (@lem1999058 x y)). Qed.
Lemma lem1999061 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1999062 (x : real) (y : real) : (term177 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1999060 x y) (@lem1999061)). Qed.
Lemma lem1999063 (x : real) (y : real) (h1 : term174 x y) : term72 x y.
Proof. exact (EQ_MP (@lem1999062 x y) (@lem1999057 x y h1)). Qed.
Lemma lem1999064 (x : real) (y : real) (h1 : term174 x y) : term179 x y.
Proof. exact (conj (@lem1999063 x y h1) (@lem1998989 x y h1)). Qed.
Lemma lem1999066 (x : real) (y : real) : term180 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem1999067 (x : real) (y : real) : term181 x y.
Proof. exact (@lem1999066 (term17 x y) (term18 x y)). Qed.
Lemma lem1999068 (x : real) (y : real) (h1 : term174 x y) : term169 x y.
Proof. exact (@lem1999067 x y (@lem1999064 x y h1)). Qed.
Lemma lem1999069 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (@lem1982753 x (term19 x) (term19 y) y). Qed.
Lemma lem1999070 (x : real) : (term149 x) = (term125 x).
Proof. exact (@lem1982715 term40 x). Qed.
Lemma lem1999072 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999073 : term52 = term62.
Proof. exact (@lem1999072 term46). Qed.
Lemma lem1999075 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1999076 : term40 = term45.
Proof. exact (@lem1999075 term46). Qed.
Lemma lem1999077 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999078 : term126 = term127.
Proof. exact (MK_COMB (@lem1999077) (@lem1999076)). Qed.
Lemma lem1999079 : term128 = term129.
Proof. exact (MK_COMB (@lem1999078) (@lem1999073)). Qed.
Lemma lem1999080 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1999082 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999083 : term92 = term100.
Proof. exact (@lem1999082 (NUMERAL 0) term46). Qed.
Lemma lem1999084 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999085 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999086 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999085 h1) (fun h1 : term100 = True => @lem1999084)). Qed.
Lemma lem1999087 : term100 = True.
Proof. exact (EQ_MP (@lem1999086) (@lem1999084)). Qed.
Lemma lem1999088 : term92 = True.
Proof. exact (TRANS (@lem1999083) (@lem1999087)). Qed.
Lemma lem1999089 : True = term92.
Proof. exact (SYM (@lem1999088)). Qed.
Lemma lem1999090 : term92.
Proof. exact (EQ_MP (@lem1999089) (@lem0)). Qed.
Lemma lem1999091 : term131.
Proof. exact (@lem1999080 (@lem1999090)). Qed.
Lemma lem1999093 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999094 : term92 = term100.
Proof. exact (@lem1999093 (NUMERAL 0) term46). Qed.
Lemma lem1999095 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999096 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999097 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999096 h1) (fun h1 : term100 = True => @lem1999095)). Qed.
Lemma lem1999098 : term100 = True.
Proof. exact (EQ_MP (@lem1999097) (@lem1999095)). Qed.
Lemma lem1999099 : term92 = True.
Proof. exact (TRANS (@lem1999094) (@lem1999098)). Qed.
Lemma lem1999100 : True = term92.
Proof. exact (SYM (@lem1999099)). Qed.
Lemma lem1999101 : term92.
Proof. exact (EQ_MP (@lem1999100) (@lem0)). Qed.
Lemma lem1999102 : term132.
Proof. exact (@lem1999091 (@lem1999101)). Qed.
Lemma lem1999104 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999105 : term92 = term100.
Proof. exact (@lem1999104 (NUMERAL 0) term46). Qed.
Lemma lem1999106 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999107 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999108 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999107 h1) (fun h1 : term100 = True => @lem1999106)). Qed.
Lemma lem1999109 : term100 = True.
Proof. exact (EQ_MP (@lem1999108) (@lem1999106)). Qed.
Lemma lem1999110 : term92 = True.
Proof. exact (TRANS (@lem1999105) (@lem1999109)). Qed.
Lemma lem1999111 : True = term92.
Proof. exact (SYM (@lem1999110)). Qed.
Lemma lem1999112 : term92.
Proof. exact (EQ_MP (@lem1999111) (@lem0)). Qed.
Lemma lem1999113 : term133.
Proof. exact (@lem1999102 (@lem1999112)). Qed.
Lemma lem1999115 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999116 : term55 = term56.
Proof. exact (@lem1999115 term46 term46). Qed.
Lemma lem1999117 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999118 : term58 = term46.
Proof. exact (EQ_MP (@lem1999117) (@lem940073)). Qed.
Lemma lem1999119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999120 : term56 = term52.
Proof. exact (MK_COMB (@lem1999119) (@lem1999118)). Qed.
Lemma lem1999121 : term55 = term52.
Proof. exact (TRANS (@lem1999116) (@lem1999120)). Qed.
Lemma lem1999123 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1999124 : term136 = term137.
Proof. exact (@lem1999123 term46 term46). Qed.
Lemma lem1999125 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999126 : term58 = term46.
Proof. exact (EQ_MP (@lem1999125) (@lem940073)). Qed.
Lemma lem1999127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999128 : term56 = term52.
Proof. exact (MK_COMB (@lem1999127) (@lem1999126)). Qed.
Lemma lem1999129 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1999130 : term137 = term40.
Proof. exact (MK_COMB (@lem1999129) (@lem1999128)). Qed.
Lemma lem1999131 : term136 = term40.
Proof. exact (TRANS (@lem1999124) (@lem1999130)). Qed.
Lemma lem1999132 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999133 : term138 = term126.
Proof. exact (MK_COMB (@lem1999132) (@lem1999131)). Qed.
Lemma lem1999134 : term139 = term128.
Proof. exact (MK_COMB (@lem1999133) (@lem1999121)). Qed.
Lemma lem1999136 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1999137 : term128 = term22.
Proof. exact (@lem1999136 term46). Qed.
Lemma lem1999138 : term139 = term22.
Proof. exact (TRANS (@lem1999134) (@lem1999137)). Qed.
Lemma lem1999139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999140 : term141 = term142.
Proof. exact (MK_COMB (@lem1999139) (@lem1999138)). Qed.
Lemma lem1999141 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1999142 : term143 = term105.
Proof. exact (MK_COMB (@lem1999140) (@lem1999141)). Qed.
Lemma lem1999144 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999145 : term105 = term22.
Proof. exact (@lem1999144 term46). Qed.
Lemma lem1999146 : term143 = term22.
Proof. exact (TRANS (@lem1999142) (@lem1999145)). Qed.
Lemma lem1999148 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999149 : term55 = term56.
Proof. exact (@lem1999148 term46 term46). Qed.
Lemma lem1999150 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999151 : term58 = term46.
Proof. exact (EQ_MP (@lem1999150) (@lem940073)). Qed.
Lemma lem1999152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999153 : term56 = term52.
Proof. exact (MK_COMB (@lem1999152) (@lem1999151)). Qed.
Lemma lem1999154 : term55 = term52.
Proof. exact (TRANS (@lem1999149) (@lem1999153)). Qed.
Lemma lem1999155 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1999156 : term144 = term105.
Proof. exact (MK_COMB (@lem1999155) (@lem1999154)). Qed.
Lemma lem1999158 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999159 : term105 = term22.
Proof. exact (@lem1999158 term46). Qed.
Lemma lem1999160 : term144 = term22.
Proof. exact (TRANS (@lem1999156) (@lem1999159)). Qed.
Lemma lem1999161 : term22 = term144.
Proof. exact (SYM (@lem1999160)). Qed.
Lemma lem1999162 : term143 = term144.
Proof. exact (TRANS (@lem1999146) (@lem1999161)). Qed.
Lemma lem1999163 : term129 = term94.
Proof. exact (@lem1999113 (@lem1999162)). Qed.
Lemma lem1999164 : term128 = term94.
Proof. exact (TRANS (@lem1999079) (@lem1999163)). Qed.
Lemma lem1999166 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1999167 : term94 = term22.
Proof. exact (@lem1999166 term22). Qed.
Lemma lem1999168 : term128 = term22.
Proof. exact (TRANS (@lem1999164) (@lem1999167)). Qed.
Lemma lem1999169 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999170 : term145 = term142.
Proof. exact (MK_COMB (@lem1999169) (@lem1999168)). Qed.
Lemma lem1999171 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1999172 (x : real) : (term125 x) = (term146 x).
Proof. exact (MK_COMB (@lem1999170) (@lem1999171 x)). Qed.
Lemma lem1999173 (x : real) : (term149 x) = (term146 x).
Proof. exact (TRANS (@lem1999070 x) (@lem1999172 x)). Qed.
Lemma lem1999174 (x : real) : (term146 x) = term22.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1999175 (x : real) : (term149 x) = term22.
Proof. exact (TRANS (@lem1999173 x) (@lem1999174 x)). Qed.
Lemma lem1999176 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999177 (x : real) : (term172 x) = term148.
Proof. exact (MK_COMB (@lem1999176) (@lem1999175 x)). Qed.
Lemma lem1999178 (y : real) : (term124 y) = (term125 y).
Proof. exact (@lem1982713 term40 y). Qed.
Lemma lem1999180 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999181 : term52 = term62.
Proof. exact (@lem1999180 term46). Qed.
Lemma lem1999183 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1999184 : term40 = term45.
Proof. exact (@lem1999183 term46). Qed.
Lemma lem1999185 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999186 : term126 = term127.
Proof. exact (MK_COMB (@lem1999185) (@lem1999184)). Qed.
Lemma lem1999187 : term128 = term129.
Proof. exact (MK_COMB (@lem1999186) (@lem1999181)). Qed.
Lemma lem1999188 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1999190 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999191 : term92 = term100.
Proof. exact (@lem1999190 (NUMERAL 0) term46). Qed.
Lemma lem1999192 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999193 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999194 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999193 h1) (fun h1 : term100 = True => @lem1999192)). Qed.
Lemma lem1999195 : term100 = True.
Proof. exact (EQ_MP (@lem1999194) (@lem1999192)). Qed.
Lemma lem1999196 : term92 = True.
Proof. exact (TRANS (@lem1999191) (@lem1999195)). Qed.
Lemma lem1999197 : True = term92.
Proof. exact (SYM (@lem1999196)). Qed.
Lemma lem1999198 : term92.
Proof. exact (EQ_MP (@lem1999197) (@lem0)). Qed.
Lemma lem1999199 : term131.
Proof. exact (@lem1999188 (@lem1999198)). Qed.
Lemma lem1999201 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999202 : term92 = term100.
Proof. exact (@lem1999201 (NUMERAL 0) term46). Qed.
Lemma lem1999203 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999204 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999205 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999204 h1) (fun h1 : term100 = True => @lem1999203)). Qed.
Lemma lem1999206 : term100 = True.
Proof. exact (EQ_MP (@lem1999205) (@lem1999203)). Qed.
Lemma lem1999207 : term92 = True.
Proof. exact (TRANS (@lem1999202) (@lem1999206)). Qed.
Lemma lem1999208 : True = term92.
Proof. exact (SYM (@lem1999207)). Qed.
Lemma lem1999209 : term92.
Proof. exact (EQ_MP (@lem1999208) (@lem0)). Qed.
Lemma lem1999210 : term132.
Proof. exact (@lem1999199 (@lem1999209)). Qed.
Lemma lem1999212 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999213 : term92 = term100.
Proof. exact (@lem1999212 (NUMERAL 0) term46). Qed.
Lemma lem1999214 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999215 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999216 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999215 h1) (fun h1 : term100 = True => @lem1999214)). Qed.
Lemma lem1999217 : term100 = True.
Proof. exact (EQ_MP (@lem1999216) (@lem1999214)). Qed.
Lemma lem1999218 : term92 = True.
Proof. exact (TRANS (@lem1999213) (@lem1999217)). Qed.
Lemma lem1999219 : True = term92.
Proof. exact (SYM (@lem1999218)). Qed.
Lemma lem1999220 : term92.
Proof. exact (EQ_MP (@lem1999219) (@lem0)). Qed.
Lemma lem1999221 : term133.
Proof. exact (@lem1999210 (@lem1999220)). Qed.
Lemma lem1999223 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999224 : term55 = term56.
Proof. exact (@lem1999223 term46 term46). Qed.
Lemma lem1999225 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999226 : term58 = term46.
Proof. exact (EQ_MP (@lem1999225) (@lem940073)). Qed.
Lemma lem1999227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999228 : term56 = term52.
Proof. exact (MK_COMB (@lem1999227) (@lem1999226)). Qed.
Lemma lem1999229 : term55 = term52.
Proof. exact (TRANS (@lem1999224) (@lem1999228)). Qed.
Lemma lem1999231 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1999232 : term136 = term137.
Proof. exact (@lem1999231 term46 term46). Qed.
Lemma lem1999233 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999234 : term58 = term46.
Proof. exact (EQ_MP (@lem1999233) (@lem940073)). Qed.
Lemma lem1999235 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999236 : term56 = term52.
Proof. exact (MK_COMB (@lem1999235) (@lem1999234)). Qed.
Lemma lem1999237 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1999238 : term137 = term40.
Proof. exact (MK_COMB (@lem1999237) (@lem1999236)). Qed.
Lemma lem1999239 : term136 = term40.
Proof. exact (TRANS (@lem1999232) (@lem1999238)). Qed.
Lemma lem1999240 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999241 : term138 = term126.
Proof. exact (MK_COMB (@lem1999240) (@lem1999239)). Qed.
Lemma lem1999242 : term139 = term128.
Proof. exact (MK_COMB (@lem1999241) (@lem1999229)). Qed.
Lemma lem1999244 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1999245 : term128 = term22.
Proof. exact (@lem1999244 term46). Qed.
Lemma lem1999246 : term139 = term22.
Proof. exact (TRANS (@lem1999242) (@lem1999245)). Qed.
Lemma lem1999247 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999248 : term141 = term142.
Proof. exact (MK_COMB (@lem1999247) (@lem1999246)). Qed.
Lemma lem1999249 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1999250 : term143 = term105.
Proof. exact (MK_COMB (@lem1999248) (@lem1999249)). Qed.
Lemma lem1999252 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999253 : term105 = term22.
Proof. exact (@lem1999252 term46). Qed.
Lemma lem1999254 : term143 = term22.
Proof. exact (TRANS (@lem1999250) (@lem1999253)). Qed.
Lemma lem1999256 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999257 : term55 = term56.
Proof. exact (@lem1999256 term46 term46). Qed.
Lemma lem1999258 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999259 : term58 = term46.
Proof. exact (EQ_MP (@lem1999258) (@lem940073)). Qed.
Lemma lem1999260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999261 : term56 = term52.
Proof. exact (MK_COMB (@lem1999260) (@lem1999259)). Qed.
Lemma lem1999262 : term55 = term52.
Proof. exact (TRANS (@lem1999257) (@lem1999261)). Qed.
Lemma lem1999263 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1999264 : term144 = term105.
Proof. exact (MK_COMB (@lem1999263) (@lem1999262)). Qed.
Lemma lem1999266 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999267 : term105 = term22.
Proof. exact (@lem1999266 term46). Qed.
Lemma lem1999268 : term144 = term22.
Proof. exact (TRANS (@lem1999264) (@lem1999267)). Qed.
Lemma lem1999269 : term22 = term144.
Proof. exact (SYM (@lem1999268)). Qed.
Lemma lem1999270 : term143 = term144.
Proof. exact (TRANS (@lem1999254) (@lem1999269)). Qed.
Lemma lem1999271 : term129 = term94.
Proof. exact (@lem1999221 (@lem1999270)). Qed.
Lemma lem1999272 : term128 = term94.
Proof. exact (TRANS (@lem1999187) (@lem1999271)). Qed.
Lemma lem1999274 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1999275 : term94 = term22.
Proof. exact (@lem1999274 term22). Qed.
Lemma lem1999276 : term128 = term22.
Proof. exact (TRANS (@lem1999272) (@lem1999275)). Qed.
Lemma lem1999277 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999278 : term145 = term142.
Proof. exact (MK_COMB (@lem1999277) (@lem1999276)). Qed.
Lemma lem1999279 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1999280 (y : real) : (term125 y) = (term146 y).
Proof. exact (MK_COMB (@lem1999278) (@lem1999279 y)). Qed.
Lemma lem1999281 (y : real) : (term124 y) = (term146 y).
Proof. exact (TRANS (@lem1999178 y) (@lem1999280 y)). Qed.
Lemma lem1999282 (y : real) : (term146 y) = term22.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1999283 (y : real) : (term124 y) = term22.
Proof. exact (TRANS (@lem1999281 y) (@lem1999282 y)). Qed.
Lemma lem1999284 (x : real) (y : real) : (term171 x y) = term150.
Proof. exact (MK_COMB (@lem1999177 x) (@lem1999283 y)). Qed.
Lemma lem1999285 (x : real) (y : real) : (term170 x y) = term150.
Proof. exact (TRANS (@lem1999069 x y) (@lem1999284 x y)). Qed.
Lemma lem1999286 : term150 = term22.
Proof. exact (@lem1982721 term22). Qed.
Lemma lem1999287 (x : real) (y : real) : (term170 x y) = term22.
Proof. exact (TRANS (@lem1999285 x y) (@lem1999286)). Qed.
Lemma lem1999288 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1999289 (x : real) (y : real) : (term173 x y) = term152.
Proof. exact (MK_COMB (@lem1999288) (@lem1999287 x y)). Qed.
Lemma lem1999290 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1999291 (x : real) (y : real) : (term169 x y) = term153.
Proof. exact (MK_COMB (@lem1999289 x y) (@lem1999290)). Qed.
Lemma lem1999292 (x : real) (y : real) (h1 : term174 x y) : term153.
Proof. exact (EQ_MP (@lem1999291 x y) (@lem1999068 x y h1)). Qed.
Lemma lem1999294 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1999295 : term153 = term154.
Proof. exact (@lem1999294 term22 term22). Qed.
Lemma lem1999297 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999298 : term22 = term94.
Proof. exact (@lem1999297 (NUMERAL 0)). Qed.
Lemma lem1999300 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999301 : term22 = term94.
Proof. exact (@lem1999300 (NUMERAL 0)). Qed.
Lemma lem1999302 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999303 : term95 = term96.
Proof. exact (MK_COMB (@lem1999302) (@lem1999301)). Qed.
Lemma lem1999304 : term154 = term155.
Proof. exact (MK_COMB (@lem1999303) (@lem1999298)). Qed.
Lemma lem1999305 : term156.
Proof. exact (@lem1980255 term22 term52 term22 term52). Qed.
Lemma lem1999307 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999308 : term92 = term100.
Proof. exact (@lem1999307 (NUMERAL 0) term46). Qed.
Lemma lem1999309 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999310 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999311 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999310 h1) (fun h1 : term100 = True => @lem1999309)). Qed.
Lemma lem1999312 : term100 = True.
Proof. exact (EQ_MP (@lem1999311) (@lem1999309)). Qed.
Lemma lem1999313 : term92 = True.
Proof. exact (TRANS (@lem1999308) (@lem1999312)). Qed.
Lemma lem1999314 : True = term92.
Proof. exact (SYM (@lem1999313)). Qed.
Lemma lem1999315 : term92.
Proof. exact (EQ_MP (@lem1999314) (@lem0)). Qed.
Lemma lem1999316 : term157.
Proof. exact (@lem1999305 (@lem1999315)). Qed.
Lemma lem1999318 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999319 : term92 = term100.
Proof. exact (@lem1999318 (NUMERAL 0) term46). Qed.
Lemma lem1999320 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999321 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999322 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999321 h1) (fun h1 : term100 = True => @lem1999320)). Qed.
Lemma lem1999323 : term100 = True.
Proof. exact (EQ_MP (@lem1999322) (@lem1999320)). Qed.
Lemma lem1999324 : term92 = True.
Proof. exact (TRANS (@lem1999319) (@lem1999323)). Qed.
Lemma lem1999325 : True = term92.
Proof. exact (SYM (@lem1999324)). Qed.
Lemma lem1999326 : term92.
Proof. exact (EQ_MP (@lem1999325) (@lem0)). Qed.
Lemma lem1999327 : term155 = term158.
Proof. exact (@lem1999316 (@lem1999326)). Qed.
Lemma lem1999329 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999330 : term105 = term22.
Proof. exact (@lem1999329 term46). Qed.
Lemma lem1999332 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999333 : term105 = term22.
Proof. exact (@lem1999332 term46). Qed.
Lemma lem1999334 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999335 : term106 = term95.
Proof. exact (MK_COMB (@lem1999334) (@lem1999333)). Qed.
Lemma lem1999336 : term158 = term154.
Proof. exact (MK_COMB (@lem1999335) (@lem1999330)). Qed.
Lemma lem1999338 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999339 : term154 = term159.
Proof. exact (@lem1999338 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1999340 : term159 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1999341 : term154 = False.
Proof. exact (TRANS (@lem1999339) (@lem1999340)). Qed.
Lemma lem1999342 : term158 = False.
Proof. exact (TRANS (@lem1999336) (@lem1999341)). Qed.
Lemma lem1999343 : term155 = False.
Proof. exact (TRANS (@lem1999327) (@lem1999342)). Qed.
Lemma lem1999344 : term154 = False.
Proof. exact (TRANS (@lem1999304) (@lem1999343)). Qed.
Lemma lem1999345 : term153 = False.
Proof. exact (TRANS (@lem1999295) (@lem1999344)). Qed.
Lemma lem1999346 (x : real) (y : real) (h1 : term174 x y) : False.
Proof. exact (EQ_MP (@lem1999345) (@lem1999292 x y h1)). Qed.
Lemma lem1999347 (x : real) (y : real) (h1 : term182 x y) : term182 x y.
Proof. exact (h1). Qed.
Lemma lem1999348 (x : real) (y : real) (h1 : term182 x y) : term86 x y.
Proof. exact (proj2 (@lem1999347 x y h1)). Qed.
Lemma lem1999349 (x : real) (y : real) (h1 : term182 x y) : term28 x y.
Proof. exact (proj1 (@lem1999347 x y h1)). Qed.
Lemma lem1999350 (x : real) (y : real) (h1 : term182 x y) : term23 x y.
Proof. exact (proj2 (@lem1999348 x y h1)). Qed.
Lemma lem1999353 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1999354 : term91 = term92.
Proof. exact (@lem1999353 term22 term52). Qed.
Lemma lem1999356 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999357 : term52 = term62.
Proof. exact (@lem1999356 term46). Qed.
Lemma lem1999359 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999360 : term22 = term94.
Proof. exact (@lem1999359 (NUMERAL 0)). Qed.
Lemma lem1999361 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999362 : term95 = term96.
Proof. exact (MK_COMB (@lem1999361) (@lem1999360)). Qed.
Lemma lem1999363 : term92 = term97.
Proof. exact (MK_COMB (@lem1999362) (@lem1999357)). Qed.
Lemma lem1999364 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1999366 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999367 : term92 = term100.
Proof. exact (@lem1999366 (NUMERAL 0) term46). Qed.
Lemma lem1999368 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999369 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999370 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999369 h1) (fun h1 : term100 = True => @lem1999368)). Qed.
Lemma lem1999371 : term100 = True.
Proof. exact (EQ_MP (@lem1999370) (@lem1999368)). Qed.
Lemma lem1999372 : term92 = True.
Proof. exact (TRANS (@lem1999367) (@lem1999371)). Qed.
Lemma lem1999373 : True = term92.
Proof. exact (SYM (@lem1999372)). Qed.
Lemma lem1999374 : term92.
Proof. exact (EQ_MP (@lem1999373) (@lem0)). Qed.
Lemma lem1999375 : term102.
Proof. exact (@lem1999364 (@lem1999374)). Qed.
Lemma lem1999377 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999378 : term92 = term100.
Proof. exact (@lem1999377 (NUMERAL 0) term46). Qed.
Lemma lem1999379 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999380 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999381 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999380 h1) (fun h1 : term100 = True => @lem1999379)). Qed.
Lemma lem1999382 : term100 = True.
Proof. exact (EQ_MP (@lem1999381) (@lem1999379)). Qed.
Lemma lem1999383 : term92 = True.
Proof. exact (TRANS (@lem1999378) (@lem1999382)). Qed.
Lemma lem1999384 : True = term92.
Proof. exact (SYM (@lem1999383)). Qed.
Lemma lem1999385 : term92.
Proof. exact (EQ_MP (@lem1999384) (@lem0)). Qed.
Lemma lem1999386 : term97 = term103.
Proof. exact (@lem1999375 (@lem1999385)). Qed.
Lemma lem1999388 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999389 : term55 = term56.
Proof. exact (@lem1999388 term46 term46). Qed.
Lemma lem1999390 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999391 : term58 = term46.
Proof. exact (EQ_MP (@lem1999390) (@lem940073)). Qed.
Lemma lem1999392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999393 : term56 = term52.
Proof. exact (MK_COMB (@lem1999392) (@lem1999391)). Qed.
Lemma lem1999394 : term55 = term52.
Proof. exact (TRANS (@lem1999389) (@lem1999393)). Qed.
Lemma lem1999396 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999397 : term105 = term22.
Proof. exact (@lem1999396 term46). Qed.
Lemma lem1999398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999399 : term106 = term95.
Proof. exact (MK_COMB (@lem1999398) (@lem1999397)). Qed.
Lemma lem1999400 : term103 = term92.
Proof. exact (MK_COMB (@lem1999399) (@lem1999394)). Qed.
Lemma lem1999402 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999403 : term92 = term100.
Proof. exact (@lem1999402 (NUMERAL 0) term46). Qed.
Lemma lem1999404 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999405 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999406 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999405 h1) (fun h1 : term100 = True => @lem1999404)). Qed.
Lemma lem1999407 : term100 = True.
Proof. exact (EQ_MP (@lem1999406) (@lem1999404)). Qed.
Lemma lem1999408 : term92 = True.
Proof. exact (TRANS (@lem1999403) (@lem1999407)). Qed.
Lemma lem1999409 : term103 = True.
Proof. exact (TRANS (@lem1999400) (@lem1999408)). Qed.
Lemma lem1999410 : term97 = True.
Proof. exact (TRANS (@lem1999386) (@lem1999409)). Qed.
Lemma lem1999411 : term92 = True.
Proof. exact (TRANS (@lem1999363) (@lem1999410)). Qed.
Lemma lem1999412 : term91 = True.
Proof. exact (TRANS (@lem1999354) (@lem1999411)). Qed.
Lemma lem1999413 : True = term91.
Proof. exact (SYM (@lem1999412)). Qed.
Lemma lem1999414 : term91.
Proof. exact (EQ_MP (@lem1999413) (@lem0)). Qed.
Lemma lem1999415 (x : real) (y : real) (h1 : term182 x y) : term107 x y.
Proof. exact (conj (@lem1999414) (@lem1999349 x y h1)). Qed.
Lemma lem1999417 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem1999418 (x : real) (y : real) : term109 x y.
Proof. exact (@lem1999417 term52 (term17 x y)). Qed.
Lemma lem1999419 (x : real) (y : real) (h1 : term182 x y) : term110 x y.
Proof. exact (@lem1999418 x y (@lem1999415 x y h1)). Qed.
Lemma lem1999420 (x : real) (y : real) : (term111 x y) = (term17 x y).
Proof. exact (@lem1982733 (term17 x y)). Qed.
Lemma lem1999421 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1999422 (x : real) (y : real) : (term112 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1999421) (@lem1999420 x y)). Qed.
Lemma lem1999423 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1999424 (x : real) (y : real) : (term110 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1999422 x y) (@lem1999423)). Qed.
Lemma lem1999425 (x : real) (y : real) (h1 : term182 x y) : term28 x y.
Proof. exact (EQ_MP (@lem1999424 x y) (@lem1999419 x y h1)). Qed.
Lemma lem1999427 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1999428 : term91 = term92.
Proof. exact (@lem1999427 term22 term52). Qed.
Lemma lem1999430 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999431 : term52 = term62.
Proof. exact (@lem1999430 term46). Qed.
Lemma lem1999433 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999434 : term22 = term94.
Proof. exact (@lem1999433 (NUMERAL 0)). Qed.
Lemma lem1999435 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999436 : term95 = term96.
Proof. exact (MK_COMB (@lem1999435) (@lem1999434)). Qed.
Lemma lem1999437 : term92 = term97.
Proof. exact (MK_COMB (@lem1999436) (@lem1999431)). Qed.
Lemma lem1999438 : term98.
Proof. exact (@lem1980255 term22 term52 term52 term52). Qed.
Lemma lem1999440 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999441 : term92 = term100.
Proof. exact (@lem1999440 (NUMERAL 0) term46). Qed.
Lemma lem1999442 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999443 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999444 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999443 h1) (fun h1 : term100 = True => @lem1999442)). Qed.
Lemma lem1999445 : term100 = True.
Proof. exact (EQ_MP (@lem1999444) (@lem1999442)). Qed.
Lemma lem1999446 : term92 = True.
Proof. exact (TRANS (@lem1999441) (@lem1999445)). Qed.
Lemma lem1999447 : True = term92.
Proof. exact (SYM (@lem1999446)). Qed.
Lemma lem1999448 : term92.
Proof. exact (EQ_MP (@lem1999447) (@lem0)). Qed.
Lemma lem1999449 : term102.
Proof. exact (@lem1999438 (@lem1999448)). Qed.
Lemma lem1999451 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999452 : term92 = term100.
Proof. exact (@lem1999451 (NUMERAL 0) term46). Qed.
Lemma lem1999453 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999454 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999455 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999454 h1) (fun h1 : term100 = True => @lem1999453)). Qed.
Lemma lem1999456 : term100 = True.
Proof. exact (EQ_MP (@lem1999455) (@lem1999453)). Qed.
Lemma lem1999457 : term92 = True.
Proof. exact (TRANS (@lem1999452) (@lem1999456)). Qed.
Lemma lem1999458 : True = term92.
Proof. exact (SYM (@lem1999457)). Qed.
Lemma lem1999459 : term92.
Proof. exact (EQ_MP (@lem1999458) (@lem0)). Qed.
Lemma lem1999460 : term97 = term103.
Proof. exact (@lem1999449 (@lem1999459)). Qed.
Lemma lem1999462 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999463 : term55 = term56.
Proof. exact (@lem1999462 term46 term46). Qed.
Lemma lem1999464 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999465 : term58 = term46.
Proof. exact (EQ_MP (@lem1999464) (@lem940073)). Qed.
Lemma lem1999466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999467 : term56 = term52.
Proof. exact (MK_COMB (@lem1999466) (@lem1999465)). Qed.
Lemma lem1999468 : term55 = term52.
Proof. exact (TRANS (@lem1999463) (@lem1999467)). Qed.
Lemma lem1999470 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999471 : term105 = term22.
Proof. exact (@lem1999470 term46). Qed.
Lemma lem1999472 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999473 : term106 = term95.
Proof. exact (MK_COMB (@lem1999472) (@lem1999471)). Qed.
Lemma lem1999474 : term103 = term92.
Proof. exact (MK_COMB (@lem1999473) (@lem1999468)). Qed.
Lemma lem1999476 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999477 : term92 = term100.
Proof. exact (@lem1999476 (NUMERAL 0) term46). Qed.
Lemma lem1999478 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999479 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999480 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999479 h1) (fun h1 : term100 = True => @lem1999478)). Qed.
Lemma lem1999481 : term100 = True.
Proof. exact (EQ_MP (@lem1999480) (@lem1999478)). Qed.
Lemma lem1999482 : term92 = True.
Proof. exact (TRANS (@lem1999477) (@lem1999481)). Qed.
Lemma lem1999483 : term103 = True.
Proof. exact (TRANS (@lem1999474) (@lem1999482)). Qed.
Lemma lem1999484 : term97 = True.
Proof. exact (TRANS (@lem1999460) (@lem1999483)). Qed.
Lemma lem1999485 : term92 = True.
Proof. exact (TRANS (@lem1999437) (@lem1999484)). Qed.
Lemma lem1999486 : term91 = True.
Proof. exact (TRANS (@lem1999428) (@lem1999485)). Qed.
Lemma lem1999487 : True = term91.
Proof. exact (SYM (@lem1999486)). Qed.
Lemma lem1999488 : term91.
Proof. exact (EQ_MP (@lem1999487) (@lem0)). Qed.
Lemma lem1999489 (x : real) (y : real) (h1 : term182 x y) : term113 x y.
Proof. exact (conj (@lem1999488) (@lem1999350 x y h1)). Qed.
Lemma lem1999491 (x : real) (y : real) : term114 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem1999492 (x : real) (y : real) : term115 x y.
Proof. exact (@lem1999491 term52 (term18 x y)). Qed.
Lemma lem1999493 (x : real) (y : real) (h1 : term182 x y) : term116 x y.
Proof. exact (@lem1999492 x y (@lem1999489 x y h1)). Qed.
Lemma lem1999494 (x : real) (y : real) : (term117 x y) = (term18 x y).
Proof. exact (@lem1982733 (term18 x y)). Qed.
Lemma lem1999495 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1999496 (x : real) (y : real) : (term118 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1999495) (@lem1999494 x y)). Qed.
Lemma lem1999497 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1999498 (x : real) (y : real) : (term116 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1999496 x y) (@lem1999497)). Qed.
Lemma lem1999499 (x : real) (y : real) (h1 : term182 x y) : term23 x y.
Proof. exact (EQ_MP (@lem1999498 x y) (@lem1999493 x y h1)). Qed.
Lemma lem1999500 (x : real) (y : real) (h1 : term182 x y) : term90 x y.
Proof. exact (conj (@lem1999499 x y h1) (@lem1999425 x y h1)). Qed.
Lemma lem1999502 (x : real) (y : real) : term119 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem1999503 (x : real) (y : real) : term120 x y.
Proof. exact (@lem1999502 (term18 x y) (term17 x y)). Qed.
Lemma lem1999504 (x : real) (y : real) (h1 : term182 x y) : term121 x y.
Proof. exact (@lem1999503 x y (@lem1999500 x y h1)). Qed.
Lemma lem1999505 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (@lem1982753 (term19 x) x y (term19 y)). Qed.
Lemma lem1999506 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1982713 term40 x). Qed.
Lemma lem1999508 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999509 : term52 = term62.
Proof. exact (@lem1999508 term46). Qed.
Lemma lem1999511 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1999512 : term40 = term45.
Proof. exact (@lem1999511 term46). Qed.
Lemma lem1999513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999514 : term126 = term127.
Proof. exact (MK_COMB (@lem1999513) (@lem1999512)). Qed.
Lemma lem1999515 : term128 = term129.
Proof. exact (MK_COMB (@lem1999514) (@lem1999509)). Qed.
Lemma lem1999516 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1999518 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999519 : term92 = term100.
Proof. exact (@lem1999518 (NUMERAL 0) term46). Qed.
Lemma lem1999520 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999521 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999522 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999521 h1) (fun h1 : term100 = True => @lem1999520)). Qed.
Lemma lem1999523 : term100 = True.
Proof. exact (EQ_MP (@lem1999522) (@lem1999520)). Qed.
Lemma lem1999524 : term92 = True.
Proof. exact (TRANS (@lem1999519) (@lem1999523)). Qed.
Lemma lem1999525 : True = term92.
Proof. exact (SYM (@lem1999524)). Qed.
Lemma lem1999526 : term92.
Proof. exact (EQ_MP (@lem1999525) (@lem0)). Qed.
Lemma lem1999527 : term131.
Proof. exact (@lem1999516 (@lem1999526)). Qed.
Lemma lem1999529 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999530 : term92 = term100.
Proof. exact (@lem1999529 (NUMERAL 0) term46). Qed.
Lemma lem1999531 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999532 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999533 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999532 h1) (fun h1 : term100 = True => @lem1999531)). Qed.
Lemma lem1999534 : term100 = True.
Proof. exact (EQ_MP (@lem1999533) (@lem1999531)). Qed.
Lemma lem1999535 : term92 = True.
Proof. exact (TRANS (@lem1999530) (@lem1999534)). Qed.
Lemma lem1999536 : True = term92.
Proof. exact (SYM (@lem1999535)). Qed.
Lemma lem1999537 : term92.
Proof. exact (EQ_MP (@lem1999536) (@lem0)). Qed.
Lemma lem1999538 : term132.
Proof. exact (@lem1999527 (@lem1999537)). Qed.
Lemma lem1999540 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999541 : term92 = term100.
Proof. exact (@lem1999540 (NUMERAL 0) term46). Qed.
Lemma lem1999542 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999543 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999544 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999543 h1) (fun h1 : term100 = True => @lem1999542)). Qed.
Lemma lem1999545 : term100 = True.
Proof. exact (EQ_MP (@lem1999544) (@lem1999542)). Qed.
Lemma lem1999546 : term92 = True.
Proof. exact (TRANS (@lem1999541) (@lem1999545)). Qed.
Lemma lem1999547 : True = term92.
Proof. exact (SYM (@lem1999546)). Qed.
Lemma lem1999548 : term92.
Proof. exact (EQ_MP (@lem1999547) (@lem0)). Qed.
Lemma lem1999549 : term133.
Proof. exact (@lem1999538 (@lem1999548)). Qed.
Lemma lem1999551 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999552 : term55 = term56.
Proof. exact (@lem1999551 term46 term46). Qed.
Lemma lem1999553 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999554 : term58 = term46.
Proof. exact (EQ_MP (@lem1999553) (@lem940073)). Qed.
Lemma lem1999555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999556 : term56 = term52.
Proof. exact (MK_COMB (@lem1999555) (@lem1999554)). Qed.
Lemma lem1999557 : term55 = term52.
Proof. exact (TRANS (@lem1999552) (@lem1999556)). Qed.
Lemma lem1999559 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1999560 : term136 = term137.
Proof. exact (@lem1999559 term46 term46). Qed.
Lemma lem1999561 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999562 : term58 = term46.
Proof. exact (EQ_MP (@lem1999561) (@lem940073)). Qed.
Lemma lem1999563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999564 : term56 = term52.
Proof. exact (MK_COMB (@lem1999563) (@lem1999562)). Qed.
Lemma lem1999565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1999566 : term137 = term40.
Proof. exact (MK_COMB (@lem1999565) (@lem1999564)). Qed.
Lemma lem1999567 : term136 = term40.
Proof. exact (TRANS (@lem1999560) (@lem1999566)). Qed.
Lemma lem1999568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999569 : term138 = term126.
Proof. exact (MK_COMB (@lem1999568) (@lem1999567)). Qed.
Lemma lem1999570 : term139 = term128.
Proof. exact (MK_COMB (@lem1999569) (@lem1999557)). Qed.
Lemma lem1999572 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1999573 : term128 = term22.
Proof. exact (@lem1999572 term46). Qed.
Lemma lem1999574 : term139 = term22.
Proof. exact (TRANS (@lem1999570) (@lem1999573)). Qed.
Lemma lem1999575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999576 : term141 = term142.
Proof. exact (MK_COMB (@lem1999575) (@lem1999574)). Qed.
Lemma lem1999577 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1999578 : term143 = term105.
Proof. exact (MK_COMB (@lem1999576) (@lem1999577)). Qed.
Lemma lem1999580 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999581 : term105 = term22.
Proof. exact (@lem1999580 term46). Qed.
Lemma lem1999582 : term143 = term22.
Proof. exact (TRANS (@lem1999578) (@lem1999581)). Qed.
Lemma lem1999584 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999585 : term55 = term56.
Proof. exact (@lem1999584 term46 term46). Qed.
Lemma lem1999586 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999587 : term58 = term46.
Proof. exact (EQ_MP (@lem1999586) (@lem940073)). Qed.
Lemma lem1999588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999589 : term56 = term52.
Proof. exact (MK_COMB (@lem1999588) (@lem1999587)). Qed.
Lemma lem1999590 : term55 = term52.
Proof. exact (TRANS (@lem1999585) (@lem1999589)). Qed.
Lemma lem1999591 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1999592 : term144 = term105.
Proof. exact (MK_COMB (@lem1999591) (@lem1999590)). Qed.
Lemma lem1999594 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999595 : term105 = term22.
Proof. exact (@lem1999594 term46). Qed.
Lemma lem1999596 : term144 = term22.
Proof. exact (TRANS (@lem1999592) (@lem1999595)). Qed.
Lemma lem1999597 : term22 = term144.
Proof. exact (SYM (@lem1999596)). Qed.
Lemma lem1999598 : term143 = term144.
Proof. exact (TRANS (@lem1999582) (@lem1999597)). Qed.
Lemma lem1999599 : term129 = term94.
Proof. exact (@lem1999549 (@lem1999598)). Qed.
Lemma lem1999600 : term128 = term94.
Proof. exact (TRANS (@lem1999515) (@lem1999599)). Qed.
Lemma lem1999602 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1999603 : term94 = term22.
Proof. exact (@lem1999602 term22). Qed.
Lemma lem1999604 : term128 = term22.
Proof. exact (TRANS (@lem1999600) (@lem1999603)). Qed.
Lemma lem1999605 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999606 : term145 = term142.
Proof. exact (MK_COMB (@lem1999605) (@lem1999604)). Qed.
Lemma lem1999607 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1999608 (x : real) : (term125 x) = (term146 x).
Proof. exact (MK_COMB (@lem1999606) (@lem1999607 x)). Qed.
Lemma lem1999609 (x : real) : (term124 x) = (term146 x).
Proof. exact (TRANS (@lem1999506 x) (@lem1999608 x)). Qed.
Lemma lem1999610 (x : real) : (term146 x) = term22.
Proof. exact (@lem1982719 x). Qed.
Lemma lem1999611 (x : real) : (term124 x) = term22.
Proof. exact (TRANS (@lem1999609 x) (@lem1999610 x)). Qed.
Lemma lem1999612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999613 (x : real) : (term147 x) = term148.
Proof. exact (MK_COMB (@lem1999612) (@lem1999611 x)). Qed.
Lemma lem1999614 (y : real) : (term149 y) = (term125 y).
Proof. exact (@lem1982715 term40 y). Qed.
Lemma lem1999616 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999617 : term52 = term62.
Proof. exact (@lem1999616 term46). Qed.
Lemma lem1999619 (x : nat) : (term43 x) = (term44 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem1999620 : term40 = term45.
Proof. exact (@lem1999619 term46). Qed.
Lemma lem1999621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999622 : term126 = term127.
Proof. exact (MK_COMB (@lem1999621) (@lem1999620)). Qed.
Lemma lem1999623 : term128 = term129.
Proof. exact (MK_COMB (@lem1999622) (@lem1999617)). Qed.
Lemma lem1999624 : term130.
Proof. exact (@lem1981473 term40 term52 term52 term52 term22 term52). Qed.
Lemma lem1999626 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999627 : term92 = term100.
Proof. exact (@lem1999626 (NUMERAL 0) term46). Qed.
Lemma lem1999628 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999629 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999630 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999629 h1) (fun h1 : term100 = True => @lem1999628)). Qed.
Lemma lem1999631 : term100 = True.
Proof. exact (EQ_MP (@lem1999630) (@lem1999628)). Qed.
Lemma lem1999632 : term92 = True.
Proof. exact (TRANS (@lem1999627) (@lem1999631)). Qed.
Lemma lem1999633 : True = term92.
Proof. exact (SYM (@lem1999632)). Qed.
Lemma lem1999634 : term92.
Proof. exact (EQ_MP (@lem1999633) (@lem0)). Qed.
Lemma lem1999635 : term131.
Proof. exact (@lem1999624 (@lem1999634)). Qed.
Lemma lem1999637 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999638 : term92 = term100.
Proof. exact (@lem1999637 (NUMERAL 0) term46). Qed.
Lemma lem1999639 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999640 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999641 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999640 h1) (fun h1 : term100 = True => @lem1999639)). Qed.
Lemma lem1999642 : term100 = True.
Proof. exact (EQ_MP (@lem1999641) (@lem1999639)). Qed.
Lemma lem1999643 : term92 = True.
Proof. exact (TRANS (@lem1999638) (@lem1999642)). Qed.
Lemma lem1999644 : True = term92.
Proof. exact (SYM (@lem1999643)). Qed.
Lemma lem1999645 : term92.
Proof. exact (EQ_MP (@lem1999644) (@lem0)). Qed.
Lemma lem1999646 : term132.
Proof. exact (@lem1999635 (@lem1999645)). Qed.
Lemma lem1999648 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999649 : term92 = term100.
Proof. exact (@lem1999648 (NUMERAL 0) term46). Qed.
Lemma lem1999650 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999651 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999652 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999651 h1) (fun h1 : term100 = True => @lem1999650)). Qed.
Lemma lem1999653 : term100 = True.
Proof. exact (EQ_MP (@lem1999652) (@lem1999650)). Qed.
Lemma lem1999654 : term92 = True.
Proof. exact (TRANS (@lem1999649) (@lem1999653)). Qed.
Lemma lem1999655 : True = term92.
Proof. exact (SYM (@lem1999654)). Qed.
Lemma lem1999656 : term92.
Proof. exact (EQ_MP (@lem1999655) (@lem0)). Qed.
Lemma lem1999657 : term133.
Proof. exact (@lem1999646 (@lem1999656)). Qed.
Lemma lem1999659 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999660 : term55 = term56.
Proof. exact (@lem1999659 term46 term46). Qed.
Lemma lem1999661 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999662 : term58 = term46.
Proof. exact (EQ_MP (@lem1999661) (@lem940073)). Qed.
Lemma lem1999663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999664 : term56 = term52.
Proof. exact (MK_COMB (@lem1999663) (@lem1999662)). Qed.
Lemma lem1999665 : term55 = term52.
Proof. exact (TRANS (@lem1999660) (@lem1999664)). Qed.
Lemma lem1999667 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1999668 : term136 = term137.
Proof. exact (@lem1999667 term46 term46). Qed.
Lemma lem1999669 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999670 : term58 = term46.
Proof. exact (EQ_MP (@lem1999669) (@lem940073)). Qed.
Lemma lem1999671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999672 : term56 = term52.
Proof. exact (MK_COMB (@lem1999671) (@lem1999670)). Qed.
Lemma lem1999673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1999674 : term137 = term40.
Proof. exact (MK_COMB (@lem1999673) (@lem1999672)). Qed.
Lemma lem1999675 : term136 = term40.
Proof. exact (TRANS (@lem1999668) (@lem1999674)). Qed.
Lemma lem1999676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1999677 : term138 = term126.
Proof. exact (MK_COMB (@lem1999676) (@lem1999675)). Qed.
Lemma lem1999678 : term139 = term128.
Proof. exact (MK_COMB (@lem1999677) (@lem1999665)). Qed.
Lemma lem1999680 (m : nat) : (term140 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1999681 : term128 = term22.
Proof. exact (@lem1999680 term46). Qed.
Lemma lem1999682 : term139 = term22.
Proof. exact (TRANS (@lem1999678) (@lem1999681)). Qed.
Lemma lem1999683 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999684 : term141 = term142.
Proof. exact (MK_COMB (@lem1999683) (@lem1999682)). Qed.
Lemma lem1999685 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1999686 : term143 = term105.
Proof. exact (MK_COMB (@lem1999684) (@lem1999685)). Qed.
Lemma lem1999688 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999689 : term105 = term22.
Proof. exact (@lem1999688 term46). Qed.
Lemma lem1999690 : term143 = term22.
Proof. exact (TRANS (@lem1999686) (@lem1999689)). Qed.
Lemma lem1999692 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1999693 : term55 = term56.
Proof. exact (@lem1999692 term46 term46). Qed.
Lemma lem1999694 : (term57 = (BIT1 0)) = (term58 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1999695 : term58 = term46.
Proof. exact (EQ_MP (@lem1999694) (@lem940073)). Qed.
Lemma lem1999696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1999697 : term56 = term52.
Proof. exact (MK_COMB (@lem1999696) (@lem1999695)). Qed.
Lemma lem1999698 : term55 = term52.
Proof. exact (TRANS (@lem1999693) (@lem1999697)). Qed.
Lemma lem1999699 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1999700 : term144 = term105.
Proof. exact (MK_COMB (@lem1999699) (@lem1999698)). Qed.
Lemma lem1999702 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999703 : term105 = term22.
Proof. exact (@lem1999702 term46). Qed.
Lemma lem1999704 : term144 = term22.
Proof. exact (TRANS (@lem1999700) (@lem1999703)). Qed.
Lemma lem1999705 : term22 = term144.
Proof. exact (SYM (@lem1999704)). Qed.
Lemma lem1999706 : term143 = term144.
Proof. exact (TRANS (@lem1999690) (@lem1999705)). Qed.
Lemma lem1999707 : term129 = term94.
Proof. exact (@lem1999657 (@lem1999706)). Qed.
Lemma lem1999708 : term128 = term94.
Proof. exact (TRANS (@lem1999623) (@lem1999707)). Qed.
Lemma lem1999710 (x : real) : (term63 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem1999711 : term94 = term22.
Proof. exact (@lem1999710 term22). Qed.
Lemma lem1999712 : term128 = term22.
Proof. exact (TRANS (@lem1999708) (@lem1999711)). Qed.
Lemma lem1999713 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1999714 : term145 = term142.
Proof. exact (MK_COMB (@lem1999713) (@lem1999712)). Qed.
Lemma lem1999715 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1999716 (y : real) : (term125 y) = (term146 y).
Proof. exact (MK_COMB (@lem1999714) (@lem1999715 y)). Qed.
Lemma lem1999717 (y : real) : (term149 y) = (term146 y).
Proof. exact (TRANS (@lem1999614 y) (@lem1999716 y)). Qed.
Lemma lem1999718 (y : real) : (term146 y) = term22.
Proof. exact (@lem1982719 y). Qed.
Lemma lem1999719 (y : real) : (term149 y) = term22.
Proof. exact (TRANS (@lem1999717 y) (@lem1999718 y)). Qed.
Lemma lem1999720 (x : real) (y : real) : (term123 x y) = term150.
Proof. exact (MK_COMB (@lem1999613 x) (@lem1999719 y)). Qed.
Lemma lem1999721 (x : real) (y : real) : (term122 x y) = term150.
Proof. exact (TRANS (@lem1999505 x y) (@lem1999720 x y)). Qed.
Lemma lem1999722 : term150 = term22.
Proof. exact (@lem1982721 term22). Qed.
Lemma lem1999723 (x : real) (y : real) : (term122 x y) = term22.
Proof. exact (TRANS (@lem1999721 x y) (@lem1999722)). Qed.
Lemma lem1999724 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1999725 (x : real) (y : real) : (term151 x y) = term152.
Proof. exact (MK_COMB (@lem1999724) (@lem1999723 x y)). Qed.
Lemma lem1999726 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1999727 (x : real) (y : real) : (term121 x y) = term153.
Proof. exact (MK_COMB (@lem1999725 x y) (@lem1999726)). Qed.
Lemma lem1999728 (x : real) (y : real) (h1 : term182 x y) : term153.
Proof. exact (EQ_MP (@lem1999727 x y) (@lem1999504 x y h1)). Qed.
Lemma lem1999730 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem1999731 : term153 = term154.
Proof. exact (@lem1999730 term22 term22). Qed.
Lemma lem1999733 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999734 : term22 = term94.
Proof. exact (@lem1999733 (NUMERAL 0)). Qed.
Lemma lem1999736 (x : nat) : (real_of_num x) = (term93 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem1999737 : term22 = term94.
Proof. exact (@lem1999736 (NUMERAL 0)). Qed.
Lemma lem1999738 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999739 : term95 = term96.
Proof. exact (MK_COMB (@lem1999738) (@lem1999737)). Qed.
Lemma lem1999740 : term154 = term155.
Proof. exact (MK_COMB (@lem1999739) (@lem1999734)). Qed.
Lemma lem1999741 : term156.
Proof. exact (@lem1980255 term22 term52 term22 term52). Qed.
Lemma lem1999743 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999744 : term92 = term100.
Proof. exact (@lem1999743 (NUMERAL 0) term46). Qed.
Lemma lem1999745 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999746 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999747 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999746 h1) (fun h1 : term100 = True => @lem1999745)). Qed.
Lemma lem1999748 : term100 = True.
Proof. exact (EQ_MP (@lem1999747) (@lem1999745)). Qed.
Lemma lem1999749 : term92 = True.
Proof. exact (TRANS (@lem1999744) (@lem1999748)). Qed.
Lemma lem1999750 : True = term92.
Proof. exact (SYM (@lem1999749)). Qed.
Lemma lem1999751 : term92.
Proof. exact (EQ_MP (@lem1999750) (@lem0)). Qed.
Lemma lem1999752 : term157.
Proof. exact (@lem1999741 (@lem1999751)). Qed.
Lemma lem1999754 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999755 : term92 = term100.
Proof. exact (@lem1999754 (NUMERAL 0) term46). Qed.
Lemma lem1999756 : term101 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1999757 (h1 : term101 = (BIT1 0)) : term100 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1999758 : (term101 = (BIT1 0)) = (term100 = True).
Proof. exact (prop_ext (fun h1 : term101 = (BIT1 0) => @lem1999757 h1) (fun h1 : term100 = True => @lem1999756)). Qed.
Lemma lem1999759 : term100 = True.
Proof. exact (EQ_MP (@lem1999758) (@lem1999756)). Qed.
Lemma lem1999760 : term92 = True.
Proof. exact (TRANS (@lem1999755) (@lem1999759)). Qed.
Lemma lem1999761 : True = term92.
Proof. exact (SYM (@lem1999760)). Qed.
Lemma lem1999762 : term92.
Proof. exact (EQ_MP (@lem1999761) (@lem0)). Qed.
Lemma lem1999763 : term155 = term158.
Proof. exact (@lem1999752 (@lem1999762)). Qed.
Lemma lem1999765 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999766 : term105 = term22.
Proof. exact (@lem1999765 term46). Qed.
Lemma lem1999768 (x : nat) : (term104 x) = term22.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem1999769 : term105 = term22.
Proof. exact (@lem1999768 term46). Qed.
Lemma lem1999770 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1999771 : term106 = term95.
Proof. exact (MK_COMB (@lem1999770) (@lem1999769)). Qed.
Lemma lem1999772 : term158 = term154.
Proof. exact (MK_COMB (@lem1999771) (@lem1999766)). Qed.
Lemma lem1999774 (m : nat) (n : nat) : (term99 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1999775 : term154 = term159.
Proof. exact (@lem1999774 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1999776 : term159 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1999777 : term154 = False.
Proof. exact (TRANS (@lem1999775) (@lem1999776)). Qed.
Lemma lem1999778 : term158 = False.
Proof. exact (TRANS (@lem1999772) (@lem1999777)). Qed.
Lemma lem1999779 : term155 = False.
Proof. exact (TRANS (@lem1999763) (@lem1999778)). Qed.
Lemma lem1999780 : term154 = False.
Proof. exact (TRANS (@lem1999740) (@lem1999779)). Qed.
Lemma lem1999781 : term153 = False.
Proof. exact (TRANS (@lem1999731) (@lem1999780)). Qed.
Lemma lem1999782 (x : real) (y : real) (h1 : term182 x y) : False.
Proof. exact (EQ_MP (@lem1999781) (@lem1999728 x y h1)). Qed.
Lemma lem1999783 (x : real) (y : real) (h1 : term84 x y) : False.
Proof. exact (or_elim (@lem1998910 x y h1) (fun h0 : term174 x y => @lem1999346 x y h0) (fun h0 : term182 x y => @lem1999782 x y h0)). Qed.
Lemma lem1999784 (x : real) (y : real) (h1 : term89 x y) : False.
Proof. exact (or_elim (@lem1998100 x y h1) (fun h0 : term87 x y => @lem1998909 x y h0) (fun h0 : term84 x y => @lem1999783 x y h0)). Qed.
Lemma lem1999786 (x : real) (y : real) (h1 : term89 x y) : term89 x y.
Proof. exact (h1). Qed.
Lemma lem1999787 (x : real) (y : real) (h1 : term89 x y) : (term89 x y) = False.
Proof. exact (prop_ext (fun h2 : term89 x y => @lem1999784 x y h1) (fun h2 : False => @lem1999786 x y h1)). Qed.
Lemma lem1999788 (x : real) (y : real) (h1 : term89 x y) : False.
Proof. exact (EQ_MP (@lem1999787 x y h1) (@lem1999786 x y h1)). Qed.
Lemma lem1999789 (x : real) (y : real) (h1 : term14 x y) : term14 x y.
Proof. exact (h1). Qed.
Lemma lem1999790 (x : real) (y : real) (h1 : term14 x y) : term89 x y.
Proof. exact (EQ_MP (@lem1998078 x y) (@lem1999789 x y h1)). Qed.
Lemma lem1999791 (x : real) (y : real) (h1 : term14 x y) : (term89 x y) = False.
Proof. exact (prop_ext (fun h2 : term89 x y => @lem1999788 x y h2) (fun h2 : False => @lem1999790 x y h1)). Qed.
Lemma lem1999792 (x : real) (y : real) (h1 : term14 x y) : False.
Proof. exact (EQ_MP (@lem1999791 x y h1) (@lem1999790 x y h1)). Qed.
Lemma lem1999793 (x : real) (y : real) : term183 x y.
Proof. exact (fun h0 : term14 x y => @lem1999792 x y h0). Qed.

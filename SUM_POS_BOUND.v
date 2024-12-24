Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_BOUND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SUM_CLAUSES_spec.
Require Import SUM_POS_LE_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19158_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7085825 (x : real) (y : real) (b : real) : (term0 x y b) = (term1 x y b).
Proof. exact (@lem17045 (real_le x b) (real_le y b)). Qed.
Lemma lem7085827 (x : real) (y : real) (b : real) : (term2 x y b) = (term2 x y b).
Proof. exact (eq_refl (term2 x y b)). Qed.
Lemma lem7085828 (x : real) (y : real) (b : real) : (term3 x y b) = (term4 x y b).
Proof. exact (MK_COMB (@lem7085827 x y b) (@lem7085825 x y b)). Qed.
Lemma lem7085829 (x : real) (y : real) (b : real) : (term5 x y b) = (term3 x y b).
Proof. exact (@lem17362 (term6 x y b) (term7 x y b)). Qed.
Lemma lem7085853 (x : real) (y : real) (b : real) : (term5 x y b) = (term4 x y b).
Proof. exact (TRANS (@lem7085829 x y b) (@lem7085828 x y b)). Qed.
Lemma lem7085854 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1988287 x term10). Qed.
Lemma lem7085860 (x : real) : (term11 x) = (term12 x).
Proof. exact (@lem1982792 x term10). Qed.
Lemma lem7085862 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085863 : term10 = term14.
Proof. exact (@lem7085862 (NUMERAL 0)). Qed.
Lemma lem7085865 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7085866 : term17 = term18.
Proof. exact (@lem7085865 term19). Qed.
Lemma lem7085867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7085868 : term20 = term21.
Proof. exact (MK_COMB (@lem7085867) (@lem7085866)). Qed.
Lemma lem7085869 : term22 = term23.
Proof. exact (MK_COMB (@lem7085868) (@lem7085863)). Qed.
Lemma lem7085870 : term23 = term24.
Proof. exact (@lem1981613 term17 term10 term25 term25). Qed.
Lemma lem7085872 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7085873 : term28 = term29.
Proof. exact (@lem7085872 term19 term19). Qed.
Lemma lem7085874 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085875 : term31 = term19.
Proof. exact (EQ_MP (@lem7085874) (@lem940073)). Qed.
Lemma lem7085876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085877 : term29 = term25.
Proof. exact (MK_COMB (@lem7085876) (@lem7085875)). Qed.
Lemma lem7085878 : term28 = term25.
Proof. exact (TRANS (@lem7085873) (@lem7085877)). Qed.
Lemma lem7085880 (x : nat) : (term32 x) = term10.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7085881 : term22 = term10.
Proof. exact (@lem7085880 term19). Qed.
Lemma lem7085882 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7085883 : term33 = term34.
Proof. exact (MK_COMB (@lem7085882) (@lem7085881)). Qed.
Lemma lem7085884 : term24 = term14.
Proof. exact (MK_COMB (@lem7085883) (@lem7085878)). Qed.
Lemma lem7085885 : term23 = term14.
Proof. exact (TRANS (@lem7085870) (@lem7085884)). Qed.
Lemma lem7085886 : term22 = term14.
Proof. exact (TRANS (@lem7085869) (@lem7085885)). Qed.
Lemma lem7085888 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7085889 : term14 = term10.
Proof. exact (@lem7085888 term10). Qed.
Lemma lem7085890 : term22 = term10.
Proof. exact (TRANS (@lem7085886) (@lem7085889)). Qed.
Lemma lem7085891 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem7085892 (x : real) : (term12 x) = (term36 x).
Proof. exact (MK_COMB (@lem7085891 x) (@lem7085890)). Qed.
Lemma lem7085893 (x : real) : (term36 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem7085894 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem7085892 x) (@lem7085893 x)). Qed.
Lemma lem7085896 (x : real) : (term11 x) = x.
Proof. exact (TRANS (@lem7085860 x) (@lem7085894 x)). Qed.
Lemma lem7085897 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7085898 (x : real) : (term37 x) = (real_ge x).
Proof. exact (MK_COMB (@lem7085897) (@lem7085896 x)). Qed.
Lemma lem7085899 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7085900 (x : real) : (term9 x) = (term38 x).
Proof. exact (MK_COMB (@lem7085898 x) (@lem7085899)). Qed.
Lemma lem7085901 (x : real) : (term8 x) = (term38 x).
Proof. exact (TRANS (@lem7085854 x) (@lem7085900 x)). Qed.
Lemma lem7085902 (y : real) : (term8 y) = (term9 y).
Proof. exact (@lem1988287 y term10). Qed.
Lemma lem7085908 (y : real) : (term11 y) = (term12 y).
Proof. exact (@lem1982792 y term10). Qed.
Lemma lem7085910 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7085911 : term10 = term14.
Proof. exact (@lem7085910 (NUMERAL 0)). Qed.
Lemma lem7085913 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7085914 : term17 = term18.
Proof. exact (@lem7085913 term19). Qed.
Lemma lem7085915 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7085916 : term20 = term21.
Proof. exact (MK_COMB (@lem7085915) (@lem7085914)). Qed.
Lemma lem7085917 : term22 = term23.
Proof. exact (MK_COMB (@lem7085916) (@lem7085911)). Qed.
Lemma lem7085918 : term23 = term24.
Proof. exact (@lem1981613 term17 term10 term25 term25). Qed.
Lemma lem7085920 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7085921 : term28 = term29.
Proof. exact (@lem7085920 term19 term19). Qed.
Lemma lem7085922 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7085923 : term31 = term19.
Proof. exact (EQ_MP (@lem7085922) (@lem940073)). Qed.
Lemma lem7085924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7085925 : term29 = term25.
Proof. exact (MK_COMB (@lem7085924) (@lem7085923)). Qed.
Lemma lem7085926 : term28 = term25.
Proof. exact (TRANS (@lem7085921) (@lem7085925)). Qed.
Lemma lem7085928 (x : nat) : (term32 x) = term10.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7085929 : term22 = term10.
Proof. exact (@lem7085928 term19). Qed.
Lemma lem7085930 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7085931 : term33 = term34.
Proof. exact (MK_COMB (@lem7085930) (@lem7085929)). Qed.
Lemma lem7085932 : term24 = term14.
Proof. exact (MK_COMB (@lem7085931) (@lem7085926)). Qed.
Lemma lem7085933 : term23 = term14.
Proof. exact (TRANS (@lem7085918) (@lem7085932)). Qed.
Lemma lem7085934 : term22 = term14.
Proof. exact (TRANS (@lem7085917) (@lem7085933)). Qed.
Lemma lem7085936 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7085937 : term14 = term10.
Proof. exact (@lem7085936 term10). Qed.
Lemma lem7085938 : term22 = term10.
Proof. exact (TRANS (@lem7085934) (@lem7085937)). Qed.
Lemma lem7085939 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7085940 (y : real) : (term12 y) = (term36 y).
Proof. exact (MK_COMB (@lem7085939 y) (@lem7085938)). Qed.
Lemma lem7085941 (y : real) : (term36 y) = y.
Proof. exact (@lem1982723 y). Qed.
Lemma lem7085942 (y : real) : (term12 y) = y.
Proof. exact (TRANS (@lem7085940 y) (@lem7085941 y)). Qed.
Lemma lem7085944 (y : real) : (term11 y) = y.
Proof. exact (TRANS (@lem7085908 y) (@lem7085942 y)). Qed.
Lemma lem7085945 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7085946 (y : real) : (term37 y) = (real_ge y).
Proof. exact (MK_COMB (@lem7085945) (@lem7085944 y)). Qed.
Lemma lem7085947 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7085948 (y : real) : (term9 y) = (term38 y).
Proof. exact (MK_COMB (@lem7085946 y) (@lem7085947)). Qed.
Lemma lem7085949 (y : real) : (term8 y) = (term38 y).
Proof. exact (TRANS (@lem7085902 y) (@lem7085948 y)). Qed.
Lemma lem7085950 (b : real) (x : real) (y : real) : (term39 x y b) = (term40 b x y).
Proof. exact (@lem1988287 b (real_add x y)). Qed.
Lemma lem7085962 (b : real) (x : real) (y : real) : (term41 b x y) = (term42 b x y).
Proof. exact (@lem1982792 b (real_add x y)). Qed.
Lemma lem7085969 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1982781 x term17 y). Qed.
Lemma lem7085970 (b : real) : (real_add b) = (real_add b).
Proof. exact (eq_refl (real_add b)). Qed.
Lemma lem7085973 (b : real) (x : real) (y : real) : (term42 b x y) = (term45 b x y).
Proof. exact (MK_COMB (@lem7085970 b) (@lem7085969 x y)). Qed.
Lemma lem7085975 (b : real) (x : real) (y : real) : (term41 b x y) = (term45 b x y).
Proof. exact (TRANS (@lem7085962 b x y) (@lem7085973 b x y)). Qed.
Lemma lem7085976 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7085977 (b : real) (x : real) (y : real) : (term46 b x y) = (term47 b x y).
Proof. exact (MK_COMB (@lem7085976) (@lem7085975 b x y)). Qed.
Lemma lem7085978 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7085979 (b : real) (x : real) (y : real) : (term40 b x y) = (term48 b x y).
Proof. exact (MK_COMB (@lem7085977 b x y) (@lem7085978)). Qed.
Lemma lem7085980 (b : real) (x : real) (y : real) : (term39 x y b) = (term48 b x y).
Proof. exact (TRANS (@lem7085950 b x y) (@lem7085979 b x y)). Qed.
Lemma lem7085981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7085982 (y : real) : (term49 y) = (term50 y).
Proof. exact (MK_COMB (@lem7085981) (@lem7085949 y)). Qed.
Lemma lem7085983 (b : real) (x : real) (y : real) : (term51 x y b) = (term52 b x y).
Proof. exact (MK_COMB (@lem7085982 y) (@lem7085980 b x y)). Qed.
Lemma lem7085984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7085985 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem7085984) (@lem7085901 x)). Qed.
Lemma lem7085986 (b : real) (x : real) (y : real) : (term6 x y b) = (term53 b x y).
Proof. exact (MK_COMB (@lem7085985 x) (@lem7085983 b x y)). Qed.
Lemma lem7085987 (x : real) (b : real) : (term54 x b) = (term55 x b).
Proof. exact (@lem1988297 x b). Qed.
Lemma lem7085993 (x : real) (b : real) : (real_sub x b) = (term56 x b).
Proof. exact (@lem1982792 x b). Qed.
Lemma lem7085998 (b : real) (x : real) : (term56 x b) = (term57 b x).
Proof. exact (@lem1982761 (term58 b) x). Qed.
Lemma lem7086000 (b : real) (x : real) : (real_sub x b) = (term57 b x).
Proof. exact (TRANS (@lem7085993 x b) (@lem7085998 b x)). Qed.
Lemma lem7086001 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086002 (b : real) (x : real) : (term59 x b) = (term60 b x).
Proof. exact (MK_COMB (@lem7086001) (@lem7086000 b x)). Qed.
Lemma lem7086003 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086004 (b : real) (x : real) : (term55 x b) = (term61 b x).
Proof. exact (MK_COMB (@lem7086002 b x) (@lem7086003)). Qed.
Lemma lem7086005 (b : real) (x : real) : (term54 x b) = (term61 b x).
Proof. exact (TRANS (@lem7085987 x b) (@lem7086004 b x)). Qed.
Lemma lem7086006 (y : real) (b : real) : (term54 y b) = (term55 y b).
Proof. exact (@lem1988297 y b). Qed.
Lemma lem7086012 (y : real) (b : real) : (real_sub y b) = (term56 y b).
Proof. exact (@lem1982792 y b). Qed.
Lemma lem7086017 (b : real) (y : real) : (term56 y b) = (term57 b y).
Proof. exact (@lem1982761 (term58 b) y). Qed.
Lemma lem7086019 (b : real) (y : real) : (real_sub y b) = (term57 b y).
Proof. exact (TRANS (@lem7086012 y b) (@lem7086017 b y)). Qed.
Lemma lem7086020 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086021 (b : real) (y : real) : (term59 y b) = (term60 b y).
Proof. exact (MK_COMB (@lem7086020) (@lem7086019 b y)). Qed.
Lemma lem7086022 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086023 (b : real) (y : real) : (term55 y b) = (term61 b y).
Proof. exact (MK_COMB (@lem7086021 b y) (@lem7086022)). Qed.
Lemma lem7086024 (b : real) (y : real) : (term54 y b) = (term61 b y).
Proof. exact (TRANS (@lem7086006 y b) (@lem7086023 b y)). Qed.
Lemma lem7086025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7086026 (b : real) (x : real) : (term62 x b) = (term63 b x).
Proof. exact (MK_COMB (@lem7086025) (@lem7086005 b x)). Qed.
Lemma lem7086027 (x : real) (b : real) (y : real) : (term1 x y b) = (term64 x b y).
Proof. exact (MK_COMB (@lem7086026 b x) (@lem7086024 b y)). Qed.
Lemma lem7086028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7086029 (b : real) (x : real) (y : real) : (term2 x y b) = (term65 b x y).
Proof. exact (MK_COMB (@lem7086028) (@lem7085986 b x y)). Qed.
Lemma lem7086030 (x : real) (b : real) (y : real) : (term4 x y b) = (term66 x b y).
Proof. exact (MK_COMB (@lem7086029 b x y) (@lem7086027 x b y)). Qed.
Lemma lem7086037 (x : real) (b : real) (y : real) : (term5 x y b) = (term66 x b y).
Proof. exact (TRANS (@lem7085853 x y b) (@lem7086030 x b y)). Qed.
Lemma lem7086066 (x : real) (b : real) (y : real) : (term66 x b y) = (term67 x b y).
Proof. exact (@lem19158 (term61 b x) (term53 b x y) (term61 b y)). Qed.
Lemma lem7086067 (x : real) (b : real) (y : real) : (term5 x y b) = (term67 x b y).
Proof. exact (TRANS (@lem7086037 x b y) (@lem7086066 x b y)). Qed.
Lemma lem7086077 (x : real) (b : real) (y : real) (h1 : term67 x b y) : term67 x b y.
Proof. exact (h1). Qed.
Lemma lem7086078 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term68 y b x.
Proof. exact (h1). Qed.
Lemma lem7086079 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term61 b x.
Proof. exact (proj2 (@lem7086078 y b x h1)). Qed.
Lemma lem7086080 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term53 b x y.
Proof. exact (proj1 (@lem7086078 y b x h1)). Qed.
Lemma lem7086081 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term52 b x y.
Proof. exact (proj2 (@lem7086080 y b x h1)). Qed.
Lemma lem7086083 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term48 b x y.
Proof. exact (proj2 (@lem7086081 y b x h1)). Qed.
Lemma lem7086084 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term38 y.
Proof. exact (proj1 (@lem7086081 y b x h1)). Qed.
Lemma lem7086086 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086087 : term69 = term70.
Proof. exact (@lem7086086 term10 term25). Qed.
Lemma lem7086089 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086090 : term25 = term71.
Proof. exact (@lem7086089 term19). Qed.
Lemma lem7086092 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086093 : term10 = term14.
Proof. exact (@lem7086092 (NUMERAL 0)). Qed.
Lemma lem7086094 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086095 : term72 = term73.
Proof. exact (MK_COMB (@lem7086094) (@lem7086093)). Qed.
Lemma lem7086096 : term70 = term74.
Proof. exact (MK_COMB (@lem7086095) (@lem7086090)). Qed.
Lemma lem7086097 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086099 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086100 : term70 = term77.
Proof. exact (@lem7086099 (NUMERAL 0) term19). Qed.
Lemma lem7086101 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086102 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086103 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086102 h1) (fun h1 : term77 = True => @lem7086101)). Qed.
Lemma lem7086104 : term77 = True.
Proof. exact (EQ_MP (@lem7086103) (@lem7086101)). Qed.
Lemma lem7086105 : term70 = True.
Proof. exact (TRANS (@lem7086100) (@lem7086104)). Qed.
Lemma lem7086106 : True = term70.
Proof. exact (SYM (@lem7086105)). Qed.
Lemma lem7086107 : term70.
Proof. exact (EQ_MP (@lem7086106) (@lem0)). Qed.
Lemma lem7086108 : term79.
Proof. exact (@lem7086097 (@lem7086107)). Qed.
Lemma lem7086110 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086111 : term70 = term77.
Proof. exact (@lem7086110 (NUMERAL 0) term19). Qed.
Lemma lem7086112 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086113 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086114 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086113 h1) (fun h1 : term77 = True => @lem7086112)). Qed.
Lemma lem7086115 : term77 = True.
Proof. exact (EQ_MP (@lem7086114) (@lem7086112)). Qed.
Lemma lem7086116 : term70 = True.
Proof. exact (TRANS (@lem7086111) (@lem7086115)). Qed.
Lemma lem7086117 : True = term70.
Proof. exact (SYM (@lem7086116)). Qed.
Lemma lem7086118 : term70.
Proof. exact (EQ_MP (@lem7086117) (@lem0)). Qed.
Lemma lem7086119 : term74 = term80.
Proof. exact (@lem7086108 (@lem7086118)). Qed.
Lemma lem7086121 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086122 : term28 = term29.
Proof. exact (@lem7086121 term19 term19). Qed.
Lemma lem7086123 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086124 : term31 = term19.
Proof. exact (EQ_MP (@lem7086123) (@lem940073)). Qed.
Lemma lem7086125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086126 : term29 = term25.
Proof. exact (MK_COMB (@lem7086125) (@lem7086124)). Qed.
Lemma lem7086127 : term28 = term25.
Proof. exact (TRANS (@lem7086122) (@lem7086126)). Qed.
Lemma lem7086129 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086130 : term82 = term10.
Proof. exact (@lem7086129 term19). Qed.
Lemma lem7086131 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086132 : term83 = term72.
Proof. exact (MK_COMB (@lem7086131) (@lem7086130)). Qed.
Lemma lem7086133 : term80 = term70.
Proof. exact (MK_COMB (@lem7086132) (@lem7086127)). Qed.
Lemma lem7086135 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086136 : term70 = term77.
Proof. exact (@lem7086135 (NUMERAL 0) term19). Qed.
Lemma lem7086137 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086138 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086139 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086138 h1) (fun h1 : term77 = True => @lem7086137)). Qed.
Lemma lem7086140 : term77 = True.
Proof. exact (EQ_MP (@lem7086139) (@lem7086137)). Qed.
Lemma lem7086141 : term70 = True.
Proof. exact (TRANS (@lem7086136) (@lem7086140)). Qed.
Lemma lem7086142 : term80 = True.
Proof. exact (TRANS (@lem7086133) (@lem7086141)). Qed.
Lemma lem7086143 : term74 = True.
Proof. exact (TRANS (@lem7086119) (@lem7086142)). Qed.
Lemma lem7086144 : term70 = True.
Proof. exact (TRANS (@lem7086096) (@lem7086143)). Qed.
Lemma lem7086145 : term69 = True.
Proof. exact (TRANS (@lem7086087) (@lem7086144)). Qed.
Lemma lem7086146 : True = term69.
Proof. exact (SYM (@lem7086145)). Qed.
Lemma lem7086147 : term69.
Proof. exact (EQ_MP (@lem7086146) (@lem0)). Qed.
Lemma lem7086148 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term84 y.
Proof. exact (conj (@lem7086147) (@lem7086084 y b x h1)). Qed.
Lemma lem7086150 (x : real) (y : real) : term85 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7086151 (y : real) : term86 y.
Proof. exact (@lem7086150 term25 y). Qed.
Lemma lem7086152 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term87 y.
Proof. exact (@lem7086151 y (@lem7086148 y b x h1)). Qed.
Lemma lem7086153 (y : real) : (term88 y) = y.
Proof. exact (@lem1982733 y). Qed.
Lemma lem7086154 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7086155 (y : real) : (term89 y) = (real_ge y).
Proof. exact (MK_COMB (@lem7086154) (@lem7086153 y)). Qed.
Lemma lem7086156 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086157 (y : real) : (term87 y) = (term38 y).
Proof. exact (MK_COMB (@lem7086155 y) (@lem7086156)). Qed.
Lemma lem7086158 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term38 y.
Proof. exact (EQ_MP (@lem7086157 y) (@lem7086152 y b x h1)). Qed.
Lemma lem7086160 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086161 : term69 = term70.
Proof. exact (@lem7086160 term10 term25). Qed.
Lemma lem7086163 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086164 : term25 = term71.
Proof. exact (@lem7086163 term19). Qed.
Lemma lem7086166 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086167 : term10 = term14.
Proof. exact (@lem7086166 (NUMERAL 0)). Qed.
Lemma lem7086168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086169 : term72 = term73.
Proof. exact (MK_COMB (@lem7086168) (@lem7086167)). Qed.
Lemma lem7086170 : term70 = term74.
Proof. exact (MK_COMB (@lem7086169) (@lem7086164)). Qed.
Lemma lem7086171 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086173 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086174 : term70 = term77.
Proof. exact (@lem7086173 (NUMERAL 0) term19). Qed.
Lemma lem7086175 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086176 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086177 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086176 h1) (fun h1 : term77 = True => @lem7086175)). Qed.
Lemma lem7086178 : term77 = True.
Proof. exact (EQ_MP (@lem7086177) (@lem7086175)). Qed.
Lemma lem7086179 : term70 = True.
Proof. exact (TRANS (@lem7086174) (@lem7086178)). Qed.
Lemma lem7086180 : True = term70.
Proof. exact (SYM (@lem7086179)). Qed.
Lemma lem7086181 : term70.
Proof. exact (EQ_MP (@lem7086180) (@lem0)). Qed.
Lemma lem7086182 : term79.
Proof. exact (@lem7086171 (@lem7086181)). Qed.
Lemma lem7086184 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086185 : term70 = term77.
Proof. exact (@lem7086184 (NUMERAL 0) term19). Qed.
Lemma lem7086186 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086187 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086188 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086187 h1) (fun h1 : term77 = True => @lem7086186)). Qed.
Lemma lem7086189 : term77 = True.
Proof. exact (EQ_MP (@lem7086188) (@lem7086186)). Qed.
Lemma lem7086190 : term70 = True.
Proof. exact (TRANS (@lem7086185) (@lem7086189)). Qed.
Lemma lem7086191 : True = term70.
Proof. exact (SYM (@lem7086190)). Qed.
Lemma lem7086192 : term70.
Proof. exact (EQ_MP (@lem7086191) (@lem0)). Qed.
Lemma lem7086193 : term74 = term80.
Proof. exact (@lem7086182 (@lem7086192)). Qed.
Lemma lem7086195 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086196 : term28 = term29.
Proof. exact (@lem7086195 term19 term19). Qed.
Lemma lem7086197 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086198 : term31 = term19.
Proof. exact (EQ_MP (@lem7086197) (@lem940073)). Qed.
Lemma lem7086199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086200 : term29 = term25.
Proof. exact (MK_COMB (@lem7086199) (@lem7086198)). Qed.
Lemma lem7086201 : term28 = term25.
Proof. exact (TRANS (@lem7086196) (@lem7086200)). Qed.
Lemma lem7086203 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086204 : term82 = term10.
Proof. exact (@lem7086203 term19). Qed.
Lemma lem7086205 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086206 : term83 = term72.
Proof. exact (MK_COMB (@lem7086205) (@lem7086204)). Qed.
Lemma lem7086207 : term80 = term70.
Proof. exact (MK_COMB (@lem7086206) (@lem7086201)). Qed.
Lemma lem7086209 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086210 : term70 = term77.
Proof. exact (@lem7086209 (NUMERAL 0) term19). Qed.
Lemma lem7086211 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086212 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086213 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086212 h1) (fun h1 : term77 = True => @lem7086211)). Qed.
Lemma lem7086214 : term77 = True.
Proof. exact (EQ_MP (@lem7086213) (@lem7086211)). Qed.
Lemma lem7086215 : term70 = True.
Proof. exact (TRANS (@lem7086210) (@lem7086214)). Qed.
Lemma lem7086216 : term80 = True.
Proof. exact (TRANS (@lem7086207) (@lem7086215)). Qed.
Lemma lem7086217 : term74 = True.
Proof. exact (TRANS (@lem7086193) (@lem7086216)). Qed.
Lemma lem7086218 : term70 = True.
Proof. exact (TRANS (@lem7086170) (@lem7086217)). Qed.
Lemma lem7086219 : term69 = True.
Proof. exact (TRANS (@lem7086161) (@lem7086218)). Qed.
Lemma lem7086220 : True = term69.
Proof. exact (SYM (@lem7086219)). Qed.
Lemma lem7086221 : term69.
Proof. exact (EQ_MP (@lem7086220) (@lem0)). Qed.
Lemma lem7086222 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term90 b x y.
Proof. exact (conj (@lem7086221) (@lem7086083 y b x h1)). Qed.
Lemma lem7086224 (x : real) (y : real) : term85 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7086225 (b : real) (x : real) (y : real) : term91 b x y.
Proof. exact (@lem7086224 term25 (term45 b x y)). Qed.
Lemma lem7086226 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term92 b x y.
Proof. exact (@lem7086225 b x y (@lem7086222 y b x h1)). Qed.
Lemma lem7086227 (b : real) (x : real) (y : real) : (term93 b x y) = (term45 b x y).
Proof. exact (@lem1982733 (term45 b x y)). Qed.
Lemma lem7086228 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7086229 (b : real) (x : real) (y : real) : (term94 b x y) = (term47 b x y).
Proof. exact (MK_COMB (@lem7086228) (@lem7086227 b x y)). Qed.
Lemma lem7086230 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086231 (b : real) (x : real) (y : real) : (term92 b x y) = (term48 b x y).
Proof. exact (MK_COMB (@lem7086229 b x y) (@lem7086230)). Qed.
Lemma lem7086232 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term48 b x y.
Proof. exact (EQ_MP (@lem7086231 b x y) (@lem7086226 y b x h1)). Qed.
Lemma lem7086234 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086235 : term69 = term70.
Proof. exact (@lem7086234 term10 term25). Qed.
Lemma lem7086237 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086238 : term25 = term71.
Proof. exact (@lem7086237 term19). Qed.
Lemma lem7086240 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086241 : term10 = term14.
Proof. exact (@lem7086240 (NUMERAL 0)). Qed.
Lemma lem7086242 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086243 : term72 = term73.
Proof. exact (MK_COMB (@lem7086242) (@lem7086241)). Qed.
Lemma lem7086244 : term70 = term74.
Proof. exact (MK_COMB (@lem7086243) (@lem7086238)). Qed.
Lemma lem7086245 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086247 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086248 : term70 = term77.
Proof. exact (@lem7086247 (NUMERAL 0) term19). Qed.
Lemma lem7086249 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086250 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086251 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086250 h1) (fun h1 : term77 = True => @lem7086249)). Qed.
Lemma lem7086252 : term77 = True.
Proof. exact (EQ_MP (@lem7086251) (@lem7086249)). Qed.
Lemma lem7086253 : term70 = True.
Proof. exact (TRANS (@lem7086248) (@lem7086252)). Qed.
Lemma lem7086254 : True = term70.
Proof. exact (SYM (@lem7086253)). Qed.
Lemma lem7086255 : term70.
Proof. exact (EQ_MP (@lem7086254) (@lem0)). Qed.
Lemma lem7086256 : term79.
Proof. exact (@lem7086245 (@lem7086255)). Qed.
Lemma lem7086258 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086259 : term70 = term77.
Proof. exact (@lem7086258 (NUMERAL 0) term19). Qed.
Lemma lem7086260 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086261 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086262 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086261 h1) (fun h1 : term77 = True => @lem7086260)). Qed.
Lemma lem7086263 : term77 = True.
Proof. exact (EQ_MP (@lem7086262) (@lem7086260)). Qed.
Lemma lem7086264 : term70 = True.
Proof. exact (TRANS (@lem7086259) (@lem7086263)). Qed.
Lemma lem7086265 : True = term70.
Proof. exact (SYM (@lem7086264)). Qed.
Lemma lem7086266 : term70.
Proof. exact (EQ_MP (@lem7086265) (@lem0)). Qed.
Lemma lem7086267 : term74 = term80.
Proof. exact (@lem7086256 (@lem7086266)). Qed.
Lemma lem7086269 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086270 : term28 = term29.
Proof. exact (@lem7086269 term19 term19). Qed.
Lemma lem7086271 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086272 : term31 = term19.
Proof. exact (EQ_MP (@lem7086271) (@lem940073)). Qed.
Lemma lem7086273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086274 : term29 = term25.
Proof. exact (MK_COMB (@lem7086273) (@lem7086272)). Qed.
Lemma lem7086275 : term28 = term25.
Proof. exact (TRANS (@lem7086270) (@lem7086274)). Qed.
Lemma lem7086277 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086278 : term82 = term10.
Proof. exact (@lem7086277 term19). Qed.
Lemma lem7086279 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086280 : term83 = term72.
Proof. exact (MK_COMB (@lem7086279) (@lem7086278)). Qed.
Lemma lem7086281 : term80 = term70.
Proof. exact (MK_COMB (@lem7086280) (@lem7086275)). Qed.
Lemma lem7086283 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086284 : term70 = term77.
Proof. exact (@lem7086283 (NUMERAL 0) term19). Qed.
Lemma lem7086285 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086286 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086287 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086286 h1) (fun h1 : term77 = True => @lem7086285)). Qed.
Lemma lem7086288 : term77 = True.
Proof. exact (EQ_MP (@lem7086287) (@lem7086285)). Qed.
Lemma lem7086289 : term70 = True.
Proof. exact (TRANS (@lem7086284) (@lem7086288)). Qed.
Lemma lem7086290 : term80 = True.
Proof. exact (TRANS (@lem7086281) (@lem7086289)). Qed.
Lemma lem7086291 : term74 = True.
Proof. exact (TRANS (@lem7086267) (@lem7086290)). Qed.
Lemma lem7086292 : term70 = True.
Proof. exact (TRANS (@lem7086244) (@lem7086291)). Qed.
Lemma lem7086293 : term69 = True.
Proof. exact (TRANS (@lem7086235) (@lem7086292)). Qed.
Lemma lem7086294 : True = term69.
Proof. exact (SYM (@lem7086293)). Qed.
Lemma lem7086295 : term69.
Proof. exact (EQ_MP (@lem7086294) (@lem0)). Qed.
Lemma lem7086296 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term95 b x.
Proof. exact (conj (@lem7086295) (@lem7086079 y b x h1)). Qed.
Lemma lem7086298 (x : real) (y : real) : term96 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7086299 (b : real) (x : real) : term97 b x.
Proof. exact (@lem7086298 term25 (term57 b x)). Qed.
Lemma lem7086300 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term98 b x.
Proof. exact (@lem7086299 b x (@lem7086296 y b x h1)). Qed.
Lemma lem7086301 (b : real) (x : real) : (term99 b x) = (term57 b x).
Proof. exact (@lem1982733 (term57 b x)). Qed.
Lemma lem7086302 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086303 (b : real) (x : real) : (term100 b x) = (term60 b x).
Proof. exact (MK_COMB (@lem7086302) (@lem7086301 b x)). Qed.
Lemma lem7086304 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086305 (b : real) (x : real) : (term98 b x) = (term61 b x).
Proof. exact (MK_COMB (@lem7086303 b x) (@lem7086304)). Qed.
Lemma lem7086306 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term61 b x.
Proof. exact (EQ_MP (@lem7086305 b x) (@lem7086300 y b x h1)). Qed.
Lemma lem7086307 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term101 b x y.
Proof. exact (conj (@lem7086306 y b x h1) (@lem7086232 y b x h1)). Qed.
Lemma lem7086309 (x : real) (y : real) : term102 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7086310 (b : real) (x : real) (y : real) : term103 b x y.
Proof. exact (@lem7086309 (term57 b x) (term45 b x y)). Qed.
Lemma lem7086311 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term104 b x y.
Proof. exact (@lem7086310 b x y (@lem7086307 y b x h1)). Qed.
Lemma lem7086312 (b : real) (x : real) (y : real) : (term105 b x y) = (term106 b x y).
Proof. exact (@lem1982753 (term58 b) b x (term44 x y)). Qed.
Lemma lem7086313 (b : real) : (term107 b) = (term108 b).
Proof. exact (@lem1982713 term17 b). Qed.
Lemma lem7086315 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086316 : term25 = term71.
Proof. exact (@lem7086315 term19). Qed.
Lemma lem7086318 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7086319 : term17 = term18.
Proof. exact (@lem7086318 term19). Qed.
Lemma lem7086320 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086321 : term109 = term110.
Proof. exact (MK_COMB (@lem7086320) (@lem7086319)). Qed.
Lemma lem7086322 : term111 = term112.
Proof. exact (MK_COMB (@lem7086321) (@lem7086316)). Qed.
Lemma lem7086323 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7086325 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086326 : term70 = term77.
Proof. exact (@lem7086325 (NUMERAL 0) term19). Qed.
Lemma lem7086327 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086328 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086329 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086328 h1) (fun h1 : term77 = True => @lem7086327)). Qed.
Lemma lem7086330 : term77 = True.
Proof. exact (EQ_MP (@lem7086329) (@lem7086327)). Qed.
Lemma lem7086331 : term70 = True.
Proof. exact (TRANS (@lem7086326) (@lem7086330)). Qed.
Lemma lem7086332 : True = term70.
Proof. exact (SYM (@lem7086331)). Qed.
Lemma lem7086333 : term70.
Proof. exact (EQ_MP (@lem7086332) (@lem0)). Qed.
Lemma lem7086334 : term114.
Proof. exact (@lem7086323 (@lem7086333)). Qed.
Lemma lem7086336 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086337 : term70 = term77.
Proof. exact (@lem7086336 (NUMERAL 0) term19). Qed.
Lemma lem7086338 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086339 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086340 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086339 h1) (fun h1 : term77 = True => @lem7086338)). Qed.
Lemma lem7086341 : term77 = True.
Proof. exact (EQ_MP (@lem7086340) (@lem7086338)). Qed.
Lemma lem7086342 : term70 = True.
Proof. exact (TRANS (@lem7086337) (@lem7086341)). Qed.
Lemma lem7086343 : True = term70.
Proof. exact (SYM (@lem7086342)). Qed.
Lemma lem7086344 : term70.
Proof. exact (EQ_MP (@lem7086343) (@lem0)). Qed.
Lemma lem7086345 : term115.
Proof. exact (@lem7086334 (@lem7086344)). Qed.
Lemma lem7086347 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086348 : term70 = term77.
Proof. exact (@lem7086347 (NUMERAL 0) term19). Qed.
Lemma lem7086349 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086350 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086351 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086350 h1) (fun h1 : term77 = True => @lem7086349)). Qed.
Lemma lem7086352 : term77 = True.
Proof. exact (EQ_MP (@lem7086351) (@lem7086349)). Qed.
Lemma lem7086353 : term70 = True.
Proof. exact (TRANS (@lem7086348) (@lem7086352)). Qed.
Lemma lem7086354 : True = term70.
Proof. exact (SYM (@lem7086353)). Qed.
Lemma lem7086355 : term70.
Proof. exact (EQ_MP (@lem7086354) (@lem0)). Qed.
Lemma lem7086356 : term116.
Proof. exact (@lem7086345 (@lem7086355)). Qed.
Lemma lem7086358 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086359 : term28 = term29.
Proof. exact (@lem7086358 term19 term19). Qed.
Lemma lem7086360 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086361 : term31 = term19.
Proof. exact (EQ_MP (@lem7086360) (@lem940073)). Qed.
Lemma lem7086362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086363 : term29 = term25.
Proof. exact (MK_COMB (@lem7086362) (@lem7086361)). Qed.
Lemma lem7086364 : term28 = term25.
Proof. exact (TRANS (@lem7086359) (@lem7086363)). Qed.
Lemma lem7086366 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7086367 : term119 = term120.
Proof. exact (@lem7086366 term19 term19). Qed.
Lemma lem7086368 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086369 : term31 = term19.
Proof. exact (EQ_MP (@lem7086368) (@lem940073)). Qed.
Lemma lem7086370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086371 : term29 = term25.
Proof. exact (MK_COMB (@lem7086370) (@lem7086369)). Qed.
Lemma lem7086372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7086373 : term120 = term17.
Proof. exact (MK_COMB (@lem7086372) (@lem7086371)). Qed.
Lemma lem7086374 : term119 = term17.
Proof. exact (TRANS (@lem7086367) (@lem7086373)). Qed.
Lemma lem7086375 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086376 : term121 = term109.
Proof. exact (MK_COMB (@lem7086375) (@lem7086374)). Qed.
Lemma lem7086377 : term122 = term111.
Proof. exact (MK_COMB (@lem7086376) (@lem7086364)). Qed.
Lemma lem7086379 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7086380 : term111 = term10.
Proof. exact (@lem7086379 term19). Qed.
Lemma lem7086381 : term122 = term10.
Proof. exact (TRANS (@lem7086377) (@lem7086380)). Qed.
Lemma lem7086382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086383 : term124 = term125.
Proof. exact (MK_COMB (@lem7086382) (@lem7086381)). Qed.
Lemma lem7086384 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7086385 : term126 = term82.
Proof. exact (MK_COMB (@lem7086383) (@lem7086384)). Qed.
Lemma lem7086387 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086388 : term82 = term10.
Proof. exact (@lem7086387 term19). Qed.
Lemma lem7086389 : term126 = term10.
Proof. exact (TRANS (@lem7086385) (@lem7086388)). Qed.
Lemma lem7086391 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086392 : term28 = term29.
Proof. exact (@lem7086391 term19 term19). Qed.
Lemma lem7086393 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086394 : term31 = term19.
Proof. exact (EQ_MP (@lem7086393) (@lem940073)). Qed.
Lemma lem7086395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086396 : term29 = term25.
Proof. exact (MK_COMB (@lem7086395) (@lem7086394)). Qed.
Lemma lem7086397 : term28 = term25.
Proof. exact (TRANS (@lem7086392) (@lem7086396)). Qed.
Lemma lem7086398 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7086399 : term127 = term82.
Proof. exact (MK_COMB (@lem7086398) (@lem7086397)). Qed.
Lemma lem7086401 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086402 : term82 = term10.
Proof. exact (@lem7086401 term19). Qed.
Lemma lem7086403 : term127 = term10.
Proof. exact (TRANS (@lem7086399) (@lem7086402)). Qed.
Lemma lem7086404 : term10 = term127.
Proof. exact (SYM (@lem7086403)). Qed.
Lemma lem7086405 : term126 = term127.
Proof. exact (TRANS (@lem7086389) (@lem7086404)). Qed.
Lemma lem7086406 : term112 = term14.
Proof. exact (@lem7086356 (@lem7086405)). Qed.
Lemma lem7086407 : term111 = term14.
Proof. exact (TRANS (@lem7086322) (@lem7086406)). Qed.
Lemma lem7086409 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7086410 : term14 = term10.
Proof. exact (@lem7086409 term10). Qed.
Lemma lem7086411 : term111 = term10.
Proof. exact (TRANS (@lem7086407) (@lem7086410)). Qed.
Lemma lem7086412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086413 : term128 = term125.
Proof. exact (MK_COMB (@lem7086412) (@lem7086411)). Qed.
Lemma lem7086414 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7086415 (b : real) : (term108 b) = (term129 b).
Proof. exact (MK_COMB (@lem7086413) (@lem7086414 b)). Qed.
Lemma lem7086416 (b : real) : (term107 b) = (term129 b).
Proof. exact (TRANS (@lem7086313 b) (@lem7086415 b)). Qed.
Lemma lem7086417 (b : real) : (term129 b) = term10.
Proof. exact (@lem1982719 b). Qed.
Lemma lem7086418 (b : real) : (term107 b) = term10.
Proof. exact (TRANS (@lem7086416 b) (@lem7086417 b)). Qed.
Lemma lem7086419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086420 (b : real) : (term130 b) = term131.
Proof. exact (MK_COMB (@lem7086419) (@lem7086418 b)). Qed.
Lemma lem7086421 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (@lem1982763 x (term58 x) (term58 y)). Qed.
Lemma lem7086422 (x : real) : (term134 x) = (term108 x).
Proof. exact (@lem1982715 term17 x). Qed.
Lemma lem7086424 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086425 : term25 = term71.
Proof. exact (@lem7086424 term19). Qed.
Lemma lem7086427 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7086428 : term17 = term18.
Proof. exact (@lem7086427 term19). Qed.
Lemma lem7086429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086430 : term109 = term110.
Proof. exact (MK_COMB (@lem7086429) (@lem7086428)). Qed.
Lemma lem7086431 : term111 = term112.
Proof. exact (MK_COMB (@lem7086430) (@lem7086425)). Qed.
Lemma lem7086432 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7086434 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086435 : term70 = term77.
Proof. exact (@lem7086434 (NUMERAL 0) term19). Qed.
Lemma lem7086436 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086437 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086438 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086437 h1) (fun h1 : term77 = True => @lem7086436)). Qed.
Lemma lem7086439 : term77 = True.
Proof. exact (EQ_MP (@lem7086438) (@lem7086436)). Qed.
Lemma lem7086440 : term70 = True.
Proof. exact (TRANS (@lem7086435) (@lem7086439)). Qed.
Lemma lem7086441 : True = term70.
Proof. exact (SYM (@lem7086440)). Qed.
Lemma lem7086442 : term70.
Proof. exact (EQ_MP (@lem7086441) (@lem0)). Qed.
Lemma lem7086443 : term114.
Proof. exact (@lem7086432 (@lem7086442)). Qed.
Lemma lem7086445 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086446 : term70 = term77.
Proof. exact (@lem7086445 (NUMERAL 0) term19). Qed.
Lemma lem7086447 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086448 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086449 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086448 h1) (fun h1 : term77 = True => @lem7086447)). Qed.
Lemma lem7086450 : term77 = True.
Proof. exact (EQ_MP (@lem7086449) (@lem7086447)). Qed.
Lemma lem7086451 : term70 = True.
Proof. exact (TRANS (@lem7086446) (@lem7086450)). Qed.
Lemma lem7086452 : True = term70.
Proof. exact (SYM (@lem7086451)). Qed.
Lemma lem7086453 : term70.
Proof. exact (EQ_MP (@lem7086452) (@lem0)). Qed.
Lemma lem7086454 : term115.
Proof. exact (@lem7086443 (@lem7086453)). Qed.
Lemma lem7086456 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086457 : term70 = term77.
Proof. exact (@lem7086456 (NUMERAL 0) term19). Qed.
Lemma lem7086458 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086459 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086460 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086459 h1) (fun h1 : term77 = True => @lem7086458)). Qed.
Lemma lem7086461 : term77 = True.
Proof. exact (EQ_MP (@lem7086460) (@lem7086458)). Qed.
Lemma lem7086462 : term70 = True.
Proof. exact (TRANS (@lem7086457) (@lem7086461)). Qed.
Lemma lem7086463 : True = term70.
Proof. exact (SYM (@lem7086462)). Qed.
Lemma lem7086464 : term70.
Proof. exact (EQ_MP (@lem7086463) (@lem0)). Qed.
Lemma lem7086465 : term116.
Proof. exact (@lem7086454 (@lem7086464)). Qed.
Lemma lem7086467 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086468 : term28 = term29.
Proof. exact (@lem7086467 term19 term19). Qed.
Lemma lem7086469 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086470 : term31 = term19.
Proof. exact (EQ_MP (@lem7086469) (@lem940073)). Qed.
Lemma lem7086471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086472 : term29 = term25.
Proof. exact (MK_COMB (@lem7086471) (@lem7086470)). Qed.
Lemma lem7086473 : term28 = term25.
Proof. exact (TRANS (@lem7086468) (@lem7086472)). Qed.
Lemma lem7086475 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7086476 : term119 = term120.
Proof. exact (@lem7086475 term19 term19). Qed.
Lemma lem7086477 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086478 : term31 = term19.
Proof. exact (EQ_MP (@lem7086477) (@lem940073)). Qed.
Lemma lem7086479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086480 : term29 = term25.
Proof. exact (MK_COMB (@lem7086479) (@lem7086478)). Qed.
Lemma lem7086481 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7086482 : term120 = term17.
Proof. exact (MK_COMB (@lem7086481) (@lem7086480)). Qed.
Lemma lem7086483 : term119 = term17.
Proof. exact (TRANS (@lem7086476) (@lem7086482)). Qed.
Lemma lem7086484 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086485 : term121 = term109.
Proof. exact (MK_COMB (@lem7086484) (@lem7086483)). Qed.
Lemma lem7086486 : term122 = term111.
Proof. exact (MK_COMB (@lem7086485) (@lem7086473)). Qed.
Lemma lem7086488 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7086489 : term111 = term10.
Proof. exact (@lem7086488 term19). Qed.
Lemma lem7086490 : term122 = term10.
Proof. exact (TRANS (@lem7086486) (@lem7086489)). Qed.
Lemma lem7086491 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086492 : term124 = term125.
Proof. exact (MK_COMB (@lem7086491) (@lem7086490)). Qed.
Lemma lem7086493 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7086494 : term126 = term82.
Proof. exact (MK_COMB (@lem7086492) (@lem7086493)). Qed.
Lemma lem7086496 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086497 : term82 = term10.
Proof. exact (@lem7086496 term19). Qed.
Lemma lem7086498 : term126 = term10.
Proof. exact (TRANS (@lem7086494) (@lem7086497)). Qed.
Lemma lem7086500 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086501 : term28 = term29.
Proof. exact (@lem7086500 term19 term19). Qed.
Lemma lem7086502 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086503 : term31 = term19.
Proof. exact (EQ_MP (@lem7086502) (@lem940073)). Qed.
Lemma lem7086504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086505 : term29 = term25.
Proof. exact (MK_COMB (@lem7086504) (@lem7086503)). Qed.
Lemma lem7086506 : term28 = term25.
Proof. exact (TRANS (@lem7086501) (@lem7086505)). Qed.
Lemma lem7086507 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7086508 : term127 = term82.
Proof. exact (MK_COMB (@lem7086507) (@lem7086506)). Qed.
Lemma lem7086510 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086511 : term82 = term10.
Proof. exact (@lem7086510 term19). Qed.
Lemma lem7086512 : term127 = term10.
Proof. exact (TRANS (@lem7086508) (@lem7086511)). Qed.
Lemma lem7086513 : term10 = term127.
Proof. exact (SYM (@lem7086512)). Qed.
Lemma lem7086514 : term126 = term127.
Proof. exact (TRANS (@lem7086498) (@lem7086513)). Qed.
Lemma lem7086515 : term112 = term14.
Proof. exact (@lem7086465 (@lem7086514)). Qed.
Lemma lem7086516 : term111 = term14.
Proof. exact (TRANS (@lem7086431) (@lem7086515)). Qed.
Lemma lem7086518 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7086519 : term14 = term10.
Proof. exact (@lem7086518 term10). Qed.
Lemma lem7086520 : term111 = term10.
Proof. exact (TRANS (@lem7086516) (@lem7086519)). Qed.
Lemma lem7086521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086522 : term128 = term125.
Proof. exact (MK_COMB (@lem7086521) (@lem7086520)). Qed.
Lemma lem7086523 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7086524 (x : real) : (term108 x) = (term129 x).
Proof. exact (MK_COMB (@lem7086522) (@lem7086523 x)). Qed.
Lemma lem7086525 (x : real) : (term134 x) = (term129 x).
Proof. exact (TRANS (@lem7086422 x) (@lem7086524 x)). Qed.
Lemma lem7086526 (x : real) : (term129 x) = term10.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7086527 (x : real) : (term134 x) = term10.
Proof. exact (TRANS (@lem7086525 x) (@lem7086526 x)). Qed.
Lemma lem7086528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086529 (x : real) : (term135 x) = term131.
Proof. exact (MK_COMB (@lem7086528) (@lem7086527 x)). Qed.
Lemma lem7086530 (y : real) : (term58 y) = (term58 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem7086531 (x : real) (y : real) : (term133 x y) = (term136 y).
Proof. exact (MK_COMB (@lem7086529 x) (@lem7086530 y)). Qed.
Lemma lem7086532 (x : real) (y : real) : (term132 x y) = (term136 y).
Proof. exact (TRANS (@lem7086421 x y) (@lem7086531 x y)). Qed.
Lemma lem7086533 (y : real) : (term136 y) = (term58 y).
Proof. exact (@lem1982721 (term58 y)). Qed.
Lemma lem7086534 (x : real) (y : real) : (term132 x y) = (term58 y).
Proof. exact (TRANS (@lem7086532 x y) (@lem7086533 y)). Qed.
Lemma lem7086535 (b : real) (x : real) (y : real) : (term106 b x y) = (term136 y).
Proof. exact (MK_COMB (@lem7086420 b) (@lem7086534 x y)). Qed.
Lemma lem7086536 (b : real) (x : real) (y : real) : (term105 b x y) = (term136 y).
Proof. exact (TRANS (@lem7086312 b x y) (@lem7086535 b x y)). Qed.
Lemma lem7086537 (y : real) : (term136 y) = (term58 y).
Proof. exact (@lem1982721 (term58 y)). Qed.
Lemma lem7086538 (b : real) (x : real) (y : real) : (term105 b x y) = (term58 y).
Proof. exact (TRANS (@lem7086536 b x y) (@lem7086537 y)). Qed.
Lemma lem7086539 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086540 (b : real) (x : real) (y : real) : (term137 b x y) = (term138 y).
Proof. exact (MK_COMB (@lem7086539) (@lem7086538 b x y)). Qed.
Lemma lem7086541 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086542 (b : real) (x : real) (y : real) : (term104 b x y) = (term139 y).
Proof. exact (MK_COMB (@lem7086540 b x y) (@lem7086541)). Qed.
Lemma lem7086543 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term139 y.
Proof. exact (EQ_MP (@lem7086542 b x y) (@lem7086311 y b x h1)). Qed.
Lemma lem7086545 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086546 : term69 = term70.
Proof. exact (@lem7086545 term10 term25). Qed.
Lemma lem7086548 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086549 : term25 = term71.
Proof. exact (@lem7086548 term19). Qed.
Lemma lem7086551 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086552 : term10 = term14.
Proof. exact (@lem7086551 (NUMERAL 0)). Qed.
Lemma lem7086553 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086554 : term72 = term73.
Proof. exact (MK_COMB (@lem7086553) (@lem7086552)). Qed.
Lemma lem7086555 : term70 = term74.
Proof. exact (MK_COMB (@lem7086554) (@lem7086549)). Qed.
Lemma lem7086556 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086558 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086559 : term70 = term77.
Proof. exact (@lem7086558 (NUMERAL 0) term19). Qed.
Lemma lem7086560 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086561 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086562 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086561 h1) (fun h1 : term77 = True => @lem7086560)). Qed.
Lemma lem7086563 : term77 = True.
Proof. exact (EQ_MP (@lem7086562) (@lem7086560)). Qed.
Lemma lem7086564 : term70 = True.
Proof. exact (TRANS (@lem7086559) (@lem7086563)). Qed.
Lemma lem7086565 : True = term70.
Proof. exact (SYM (@lem7086564)). Qed.
Lemma lem7086566 : term70.
Proof. exact (EQ_MP (@lem7086565) (@lem0)). Qed.
Lemma lem7086567 : term79.
Proof. exact (@lem7086556 (@lem7086566)). Qed.
Lemma lem7086569 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086570 : term70 = term77.
Proof. exact (@lem7086569 (NUMERAL 0) term19). Qed.
Lemma lem7086571 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086572 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086573 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086572 h1) (fun h1 : term77 = True => @lem7086571)). Qed.
Lemma lem7086574 : term77 = True.
Proof. exact (EQ_MP (@lem7086573) (@lem7086571)). Qed.
Lemma lem7086575 : term70 = True.
Proof. exact (TRANS (@lem7086570) (@lem7086574)). Qed.
Lemma lem7086576 : True = term70.
Proof. exact (SYM (@lem7086575)). Qed.
Lemma lem7086577 : term70.
Proof. exact (EQ_MP (@lem7086576) (@lem0)). Qed.
Lemma lem7086578 : term74 = term80.
Proof. exact (@lem7086567 (@lem7086577)). Qed.
Lemma lem7086580 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086581 : term28 = term29.
Proof. exact (@lem7086580 term19 term19). Qed.
Lemma lem7086582 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086583 : term31 = term19.
Proof. exact (EQ_MP (@lem7086582) (@lem940073)). Qed.
Lemma lem7086584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086585 : term29 = term25.
Proof. exact (MK_COMB (@lem7086584) (@lem7086583)). Qed.
Lemma lem7086586 : term28 = term25.
Proof. exact (TRANS (@lem7086581) (@lem7086585)). Qed.
Lemma lem7086588 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086589 : term82 = term10.
Proof. exact (@lem7086588 term19). Qed.
Lemma lem7086590 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086591 : term83 = term72.
Proof. exact (MK_COMB (@lem7086590) (@lem7086589)). Qed.
Lemma lem7086592 : term80 = term70.
Proof. exact (MK_COMB (@lem7086591) (@lem7086586)). Qed.
Lemma lem7086594 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086595 : term70 = term77.
Proof. exact (@lem7086594 (NUMERAL 0) term19). Qed.
Lemma lem7086596 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086597 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086598 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086597 h1) (fun h1 : term77 = True => @lem7086596)). Qed.
Lemma lem7086599 : term77 = True.
Proof. exact (EQ_MP (@lem7086598) (@lem7086596)). Qed.
Lemma lem7086600 : term70 = True.
Proof. exact (TRANS (@lem7086595) (@lem7086599)). Qed.
Lemma lem7086601 : term80 = True.
Proof. exact (TRANS (@lem7086592) (@lem7086600)). Qed.
Lemma lem7086602 : term74 = True.
Proof. exact (TRANS (@lem7086578) (@lem7086601)). Qed.
Lemma lem7086603 : term70 = True.
Proof. exact (TRANS (@lem7086555) (@lem7086602)). Qed.
Lemma lem7086604 : term69 = True.
Proof. exact (TRANS (@lem7086546) (@lem7086603)). Qed.
Lemma lem7086605 : True = term69.
Proof. exact (SYM (@lem7086604)). Qed.
Lemma lem7086606 : term69.
Proof. exact (EQ_MP (@lem7086605) (@lem0)). Qed.
Lemma lem7086607 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term140 y.
Proof. exact (conj (@lem7086606) (@lem7086543 y b x h1)). Qed.
Lemma lem7086609 (x : real) (y : real) : term96 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7086610 (y : real) : term141 y.
Proof. exact (@lem7086609 term25 (term58 y)). Qed.
Lemma lem7086611 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term142 y.
Proof. exact (@lem7086610 y (@lem7086607 y b x h1)). Qed.
Lemma lem7086612 (y : real) : (term143 y) = (term58 y).
Proof. exact (@lem1982733 (term58 y)). Qed.
Lemma lem7086613 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086614 (y : real) : (term144 y) = (term138 y).
Proof. exact (MK_COMB (@lem7086613) (@lem7086612 y)). Qed.
Lemma lem7086615 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086616 (y : real) : (term142 y) = (term139 y).
Proof. exact (MK_COMB (@lem7086614 y) (@lem7086615)). Qed.
Lemma lem7086617 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term139 y.
Proof. exact (EQ_MP (@lem7086616 y) (@lem7086611 y b x h1)). Qed.
Lemma lem7086618 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term145 y.
Proof. exact (conj (@lem7086617 y b x h1) (@lem7086158 y b x h1)). Qed.
Lemma lem7086620 (x : real) (y : real) : term102 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7086621 (y : real) : term146 y.
Proof. exact (@lem7086620 (term58 y) y). Qed.
Lemma lem7086622 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term147 y.
Proof. exact (@lem7086621 y (@lem7086618 y b x h1)). Qed.
Lemma lem7086623 (y : real) : (term107 y) = (term108 y).
Proof. exact (@lem1982713 term17 y). Qed.
Lemma lem7086625 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086626 : term25 = term71.
Proof. exact (@lem7086625 term19). Qed.
Lemma lem7086628 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7086629 : term17 = term18.
Proof. exact (@lem7086628 term19). Qed.
Lemma lem7086630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086631 : term109 = term110.
Proof. exact (MK_COMB (@lem7086630) (@lem7086629)). Qed.
Lemma lem7086632 : term111 = term112.
Proof. exact (MK_COMB (@lem7086631) (@lem7086626)). Qed.
Lemma lem7086633 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7086635 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086636 : term70 = term77.
Proof. exact (@lem7086635 (NUMERAL 0) term19). Qed.
Lemma lem7086637 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086638 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086639 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086638 h1) (fun h1 : term77 = True => @lem7086637)). Qed.
Lemma lem7086640 : term77 = True.
Proof. exact (EQ_MP (@lem7086639) (@lem7086637)). Qed.
Lemma lem7086641 : term70 = True.
Proof. exact (TRANS (@lem7086636) (@lem7086640)). Qed.
Lemma lem7086642 : True = term70.
Proof. exact (SYM (@lem7086641)). Qed.
Lemma lem7086643 : term70.
Proof. exact (EQ_MP (@lem7086642) (@lem0)). Qed.
Lemma lem7086644 : term114.
Proof. exact (@lem7086633 (@lem7086643)). Qed.
Lemma lem7086646 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086647 : term70 = term77.
Proof. exact (@lem7086646 (NUMERAL 0) term19). Qed.
Lemma lem7086648 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086649 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086650 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086649 h1) (fun h1 : term77 = True => @lem7086648)). Qed.
Lemma lem7086651 : term77 = True.
Proof. exact (EQ_MP (@lem7086650) (@lem7086648)). Qed.
Lemma lem7086652 : term70 = True.
Proof. exact (TRANS (@lem7086647) (@lem7086651)). Qed.
Lemma lem7086653 : True = term70.
Proof. exact (SYM (@lem7086652)). Qed.
Lemma lem7086654 : term70.
Proof. exact (EQ_MP (@lem7086653) (@lem0)). Qed.
Lemma lem7086655 : term115.
Proof. exact (@lem7086644 (@lem7086654)). Qed.
Lemma lem7086657 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086658 : term70 = term77.
Proof. exact (@lem7086657 (NUMERAL 0) term19). Qed.
Lemma lem7086659 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086660 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086661 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086660 h1) (fun h1 : term77 = True => @lem7086659)). Qed.
Lemma lem7086662 : term77 = True.
Proof. exact (EQ_MP (@lem7086661) (@lem7086659)). Qed.
Lemma lem7086663 : term70 = True.
Proof. exact (TRANS (@lem7086658) (@lem7086662)). Qed.
Lemma lem7086664 : True = term70.
Proof. exact (SYM (@lem7086663)). Qed.
Lemma lem7086665 : term70.
Proof. exact (EQ_MP (@lem7086664) (@lem0)). Qed.
Lemma lem7086666 : term116.
Proof. exact (@lem7086655 (@lem7086665)). Qed.
Lemma lem7086668 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086669 : term28 = term29.
Proof. exact (@lem7086668 term19 term19). Qed.
Lemma lem7086670 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086671 : term31 = term19.
Proof. exact (EQ_MP (@lem7086670) (@lem940073)). Qed.
Lemma lem7086672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086673 : term29 = term25.
Proof. exact (MK_COMB (@lem7086672) (@lem7086671)). Qed.
Lemma lem7086674 : term28 = term25.
Proof. exact (TRANS (@lem7086669) (@lem7086673)). Qed.
Lemma lem7086676 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7086677 : term119 = term120.
Proof. exact (@lem7086676 term19 term19). Qed.
Lemma lem7086678 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086679 : term31 = term19.
Proof. exact (EQ_MP (@lem7086678) (@lem940073)). Qed.
Lemma lem7086680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086681 : term29 = term25.
Proof. exact (MK_COMB (@lem7086680) (@lem7086679)). Qed.
Lemma lem7086682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7086683 : term120 = term17.
Proof. exact (MK_COMB (@lem7086682) (@lem7086681)). Qed.
Lemma lem7086684 : term119 = term17.
Proof. exact (TRANS (@lem7086677) (@lem7086683)). Qed.
Lemma lem7086685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7086686 : term121 = term109.
Proof. exact (MK_COMB (@lem7086685) (@lem7086684)). Qed.
Lemma lem7086687 : term122 = term111.
Proof. exact (MK_COMB (@lem7086686) (@lem7086674)). Qed.
Lemma lem7086689 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7086690 : term111 = term10.
Proof. exact (@lem7086689 term19). Qed.
Lemma lem7086691 : term122 = term10.
Proof. exact (TRANS (@lem7086687) (@lem7086690)). Qed.
Lemma lem7086692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086693 : term124 = term125.
Proof. exact (MK_COMB (@lem7086692) (@lem7086691)). Qed.
Lemma lem7086694 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7086695 : term126 = term82.
Proof. exact (MK_COMB (@lem7086693) (@lem7086694)). Qed.
Lemma lem7086697 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086698 : term82 = term10.
Proof. exact (@lem7086697 term19). Qed.
Lemma lem7086699 : term126 = term10.
Proof. exact (TRANS (@lem7086695) (@lem7086698)). Qed.
Lemma lem7086701 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086702 : term28 = term29.
Proof. exact (@lem7086701 term19 term19). Qed.
Lemma lem7086703 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086704 : term31 = term19.
Proof. exact (EQ_MP (@lem7086703) (@lem940073)). Qed.
Lemma lem7086705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086706 : term29 = term25.
Proof. exact (MK_COMB (@lem7086705) (@lem7086704)). Qed.
Lemma lem7086707 : term28 = term25.
Proof. exact (TRANS (@lem7086702) (@lem7086706)). Qed.
Lemma lem7086708 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7086709 : term127 = term82.
Proof. exact (MK_COMB (@lem7086708) (@lem7086707)). Qed.
Lemma lem7086711 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086712 : term82 = term10.
Proof. exact (@lem7086711 term19). Qed.
Lemma lem7086713 : term127 = term10.
Proof. exact (TRANS (@lem7086709) (@lem7086712)). Qed.
Lemma lem7086714 : term10 = term127.
Proof. exact (SYM (@lem7086713)). Qed.
Lemma lem7086715 : term126 = term127.
Proof. exact (TRANS (@lem7086699) (@lem7086714)). Qed.
Lemma lem7086716 : term112 = term14.
Proof. exact (@lem7086666 (@lem7086715)). Qed.
Lemma lem7086717 : term111 = term14.
Proof. exact (TRANS (@lem7086632) (@lem7086716)). Qed.
Lemma lem7086719 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7086720 : term14 = term10.
Proof. exact (@lem7086719 term10). Qed.
Lemma lem7086721 : term111 = term10.
Proof. exact (TRANS (@lem7086717) (@lem7086720)). Qed.
Lemma lem7086722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7086723 : term128 = term125.
Proof. exact (MK_COMB (@lem7086722) (@lem7086721)). Qed.
Lemma lem7086724 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7086725 (y : real) : (term108 y) = (term129 y).
Proof. exact (MK_COMB (@lem7086723) (@lem7086724 y)). Qed.
Lemma lem7086726 (y : real) : (term107 y) = (term129 y).
Proof. exact (TRANS (@lem7086623 y) (@lem7086725 y)). Qed.
Lemma lem7086727 (y : real) : (term129 y) = term10.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7086728 (y : real) : (term107 y) = term10.
Proof. exact (TRANS (@lem7086726 y) (@lem7086727 y)). Qed.
Lemma lem7086729 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7086730 (y : real) : (term148 y) = term149.
Proof. exact (MK_COMB (@lem7086729) (@lem7086728 y)). Qed.
Lemma lem7086731 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086732 (y : real) : (term147 y) = term150.
Proof. exact (MK_COMB (@lem7086730 y) (@lem7086731)). Qed.
Lemma lem7086733 (y : real) (b : real) (x : real) (h1 : term68 y b x) : term150.
Proof. exact (EQ_MP (@lem7086732 y) (@lem7086622 y b x h1)). Qed.
Lemma lem7086735 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086736 : term150 = term151.
Proof. exact (@lem7086735 term10 term10). Qed.
Lemma lem7086738 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086739 : term10 = term14.
Proof. exact (@lem7086738 (NUMERAL 0)). Qed.
Lemma lem7086741 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086742 : term10 = term14.
Proof. exact (@lem7086741 (NUMERAL 0)). Qed.
Lemma lem7086743 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086744 : term72 = term73.
Proof. exact (MK_COMB (@lem7086743) (@lem7086742)). Qed.
Lemma lem7086745 : term151 = term152.
Proof. exact (MK_COMB (@lem7086744) (@lem7086739)). Qed.
Lemma lem7086746 : term153.
Proof. exact (@lem1980255 term10 term25 term10 term25). Qed.
Lemma lem7086748 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086749 : term70 = term77.
Proof. exact (@lem7086748 (NUMERAL 0) term19). Qed.
Lemma lem7086750 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086751 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086752 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086751 h1) (fun h1 : term77 = True => @lem7086750)). Qed.
Lemma lem7086753 : term77 = True.
Proof. exact (EQ_MP (@lem7086752) (@lem7086750)). Qed.
Lemma lem7086754 : term70 = True.
Proof. exact (TRANS (@lem7086749) (@lem7086753)). Qed.
Lemma lem7086755 : True = term70.
Proof. exact (SYM (@lem7086754)). Qed.
Lemma lem7086756 : term70.
Proof. exact (EQ_MP (@lem7086755) (@lem0)). Qed.
Lemma lem7086757 : term154.
Proof. exact (@lem7086746 (@lem7086756)). Qed.
Lemma lem7086759 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086760 : term70 = term77.
Proof. exact (@lem7086759 (NUMERAL 0) term19). Qed.
Lemma lem7086761 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086762 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086763 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086762 h1) (fun h1 : term77 = True => @lem7086761)). Qed.
Lemma lem7086764 : term77 = True.
Proof. exact (EQ_MP (@lem7086763) (@lem7086761)). Qed.
Lemma lem7086765 : term70 = True.
Proof. exact (TRANS (@lem7086760) (@lem7086764)). Qed.
Lemma lem7086766 : True = term70.
Proof. exact (SYM (@lem7086765)). Qed.
Lemma lem7086767 : term70.
Proof. exact (EQ_MP (@lem7086766) (@lem0)). Qed.
Lemma lem7086768 : term152 = term155.
Proof. exact (@lem7086757 (@lem7086767)). Qed.
Lemma lem7086770 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086771 : term82 = term10.
Proof. exact (@lem7086770 term19). Qed.
Lemma lem7086773 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086774 : term82 = term10.
Proof. exact (@lem7086773 term19). Qed.
Lemma lem7086775 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086776 : term83 = term72.
Proof. exact (MK_COMB (@lem7086775) (@lem7086774)). Qed.
Lemma lem7086777 : term155 = term151.
Proof. exact (MK_COMB (@lem7086776) (@lem7086771)). Qed.
Lemma lem7086779 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086780 : term151 = term156.
Proof. exact (@lem7086779 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7086781 : term156 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7086782 : term151 = False.
Proof. exact (TRANS (@lem7086780) (@lem7086781)). Qed.
Lemma lem7086783 : term155 = False.
Proof. exact (TRANS (@lem7086777) (@lem7086782)). Qed.
Lemma lem7086784 : term152 = False.
Proof. exact (TRANS (@lem7086768) (@lem7086783)). Qed.
Lemma lem7086785 : term151 = False.
Proof. exact (TRANS (@lem7086745) (@lem7086784)). Qed.
Lemma lem7086786 : term150 = False.
Proof. exact (TRANS (@lem7086736) (@lem7086785)). Qed.
Lemma lem7086787 (y : real) (b : real) (x : real) (h1 : term68 y b x) : False.
Proof. exact (EQ_MP (@lem7086786) (@lem7086733 y b x h1)). Qed.
Lemma lem7086788 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term157 x b y.
Proof. exact (h1). Qed.
Lemma lem7086789 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term61 b y.
Proof. exact (proj2 (@lem7086788 x b y h1)). Qed.
Lemma lem7086790 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term53 b x y.
Proof. exact (proj1 (@lem7086788 x b y h1)). Qed.
Lemma lem7086791 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term52 b x y.
Proof. exact (proj2 (@lem7086790 x b y h1)). Qed.
Lemma lem7086792 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term38 x.
Proof. exact (proj1 (@lem7086790 x b y h1)). Qed.
Lemma lem7086793 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term48 b x y.
Proof. exact (proj2 (@lem7086791 x b y h1)). Qed.
Lemma lem7086796 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086797 : term69 = term70.
Proof. exact (@lem7086796 term10 term25). Qed.
Lemma lem7086799 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086800 : term25 = term71.
Proof. exact (@lem7086799 term19). Qed.
Lemma lem7086802 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086803 : term10 = term14.
Proof. exact (@lem7086802 (NUMERAL 0)). Qed.
Lemma lem7086804 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086805 : term72 = term73.
Proof. exact (MK_COMB (@lem7086804) (@lem7086803)). Qed.
Lemma lem7086806 : term70 = term74.
Proof. exact (MK_COMB (@lem7086805) (@lem7086800)). Qed.
Lemma lem7086807 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086809 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086810 : term70 = term77.
Proof. exact (@lem7086809 (NUMERAL 0) term19). Qed.
Lemma lem7086811 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086812 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086813 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086812 h1) (fun h1 : term77 = True => @lem7086811)). Qed.
Lemma lem7086814 : term77 = True.
Proof. exact (EQ_MP (@lem7086813) (@lem7086811)). Qed.
Lemma lem7086815 : term70 = True.
Proof. exact (TRANS (@lem7086810) (@lem7086814)). Qed.
Lemma lem7086816 : True = term70.
Proof. exact (SYM (@lem7086815)). Qed.
Lemma lem7086817 : term70.
Proof. exact (EQ_MP (@lem7086816) (@lem0)). Qed.
Lemma lem7086818 : term79.
Proof. exact (@lem7086807 (@lem7086817)). Qed.
Lemma lem7086820 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086821 : term70 = term77.
Proof. exact (@lem7086820 (NUMERAL 0) term19). Qed.
Lemma lem7086822 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086823 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086824 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086823 h1) (fun h1 : term77 = True => @lem7086822)). Qed.
Lemma lem7086825 : term77 = True.
Proof. exact (EQ_MP (@lem7086824) (@lem7086822)). Qed.
Lemma lem7086826 : term70 = True.
Proof. exact (TRANS (@lem7086821) (@lem7086825)). Qed.
Lemma lem7086827 : True = term70.
Proof. exact (SYM (@lem7086826)). Qed.
Lemma lem7086828 : term70.
Proof. exact (EQ_MP (@lem7086827) (@lem0)). Qed.
Lemma lem7086829 : term74 = term80.
Proof. exact (@lem7086818 (@lem7086828)). Qed.
Lemma lem7086831 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086832 : term28 = term29.
Proof. exact (@lem7086831 term19 term19). Qed.
Lemma lem7086833 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086834 : term31 = term19.
Proof. exact (EQ_MP (@lem7086833) (@lem940073)). Qed.
Lemma lem7086835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086836 : term29 = term25.
Proof. exact (MK_COMB (@lem7086835) (@lem7086834)). Qed.
Lemma lem7086837 : term28 = term25.
Proof. exact (TRANS (@lem7086832) (@lem7086836)). Qed.
Lemma lem7086839 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086840 : term82 = term10.
Proof. exact (@lem7086839 term19). Qed.
Lemma lem7086841 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086842 : term83 = term72.
Proof. exact (MK_COMB (@lem7086841) (@lem7086840)). Qed.
Lemma lem7086843 : term80 = term70.
Proof. exact (MK_COMB (@lem7086842) (@lem7086837)). Qed.
Lemma lem7086845 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086846 : term70 = term77.
Proof. exact (@lem7086845 (NUMERAL 0) term19). Qed.
Lemma lem7086847 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086848 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086849 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086848 h1) (fun h1 : term77 = True => @lem7086847)). Qed.
Lemma lem7086850 : term77 = True.
Proof. exact (EQ_MP (@lem7086849) (@lem7086847)). Qed.
Lemma lem7086851 : term70 = True.
Proof. exact (TRANS (@lem7086846) (@lem7086850)). Qed.
Lemma lem7086852 : term80 = True.
Proof. exact (TRANS (@lem7086843) (@lem7086851)). Qed.
Lemma lem7086853 : term74 = True.
Proof. exact (TRANS (@lem7086829) (@lem7086852)). Qed.
Lemma lem7086854 : term70 = True.
Proof. exact (TRANS (@lem7086806) (@lem7086853)). Qed.
Lemma lem7086855 : term69 = True.
Proof. exact (TRANS (@lem7086797) (@lem7086854)). Qed.
Lemma lem7086856 : True = term69.
Proof. exact (SYM (@lem7086855)). Qed.
Lemma lem7086857 : term69.
Proof. exact (EQ_MP (@lem7086856) (@lem0)). Qed.
Lemma lem7086858 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term84 x.
Proof. exact (conj (@lem7086857) (@lem7086792 x b y h1)). Qed.
Lemma lem7086860 (x : real) (y : real) : term85 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7086861 (x : real) : term86 x.
Proof. exact (@lem7086860 term25 x). Qed.
Lemma lem7086862 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term87 x.
Proof. exact (@lem7086861 x (@lem7086858 x b y h1)). Qed.
Lemma lem7086863 (x : real) : (term88 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7086864 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7086865 (x : real) : (term89 x) = (real_ge x).
Proof. exact (MK_COMB (@lem7086864) (@lem7086863 x)). Qed.
Lemma lem7086866 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086867 (x : real) : (term87 x) = (term38 x).
Proof. exact (MK_COMB (@lem7086865 x) (@lem7086866)). Qed.
Lemma lem7086868 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term38 x.
Proof. exact (EQ_MP (@lem7086867 x) (@lem7086862 x b y h1)). Qed.
Lemma lem7086870 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086871 : term69 = term70.
Proof. exact (@lem7086870 term10 term25). Qed.
Lemma lem7086873 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086874 : term25 = term71.
Proof. exact (@lem7086873 term19). Qed.
Lemma lem7086876 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086877 : term10 = term14.
Proof. exact (@lem7086876 (NUMERAL 0)). Qed.
Lemma lem7086878 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086879 : term72 = term73.
Proof. exact (MK_COMB (@lem7086878) (@lem7086877)). Qed.
Lemma lem7086880 : term70 = term74.
Proof. exact (MK_COMB (@lem7086879) (@lem7086874)). Qed.
Lemma lem7086881 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086883 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086884 : term70 = term77.
Proof. exact (@lem7086883 (NUMERAL 0) term19). Qed.
Lemma lem7086885 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086886 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086887 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086886 h1) (fun h1 : term77 = True => @lem7086885)). Qed.
Lemma lem7086888 : term77 = True.
Proof. exact (EQ_MP (@lem7086887) (@lem7086885)). Qed.
Lemma lem7086889 : term70 = True.
Proof. exact (TRANS (@lem7086884) (@lem7086888)). Qed.
Lemma lem7086890 : True = term70.
Proof. exact (SYM (@lem7086889)). Qed.
Lemma lem7086891 : term70.
Proof. exact (EQ_MP (@lem7086890) (@lem0)). Qed.
Lemma lem7086892 : term79.
Proof. exact (@lem7086881 (@lem7086891)). Qed.
Lemma lem7086894 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086895 : term70 = term77.
Proof. exact (@lem7086894 (NUMERAL 0) term19). Qed.
Lemma lem7086896 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086897 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086898 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086897 h1) (fun h1 : term77 = True => @lem7086896)). Qed.
Lemma lem7086899 : term77 = True.
Proof. exact (EQ_MP (@lem7086898) (@lem7086896)). Qed.
Lemma lem7086900 : term70 = True.
Proof. exact (TRANS (@lem7086895) (@lem7086899)). Qed.
Lemma lem7086901 : True = term70.
Proof. exact (SYM (@lem7086900)). Qed.
Lemma lem7086902 : term70.
Proof. exact (EQ_MP (@lem7086901) (@lem0)). Qed.
Lemma lem7086903 : term74 = term80.
Proof. exact (@lem7086892 (@lem7086902)). Qed.
Lemma lem7086905 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086906 : term28 = term29.
Proof. exact (@lem7086905 term19 term19). Qed.
Lemma lem7086907 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086908 : term31 = term19.
Proof. exact (EQ_MP (@lem7086907) (@lem940073)). Qed.
Lemma lem7086909 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086910 : term29 = term25.
Proof. exact (MK_COMB (@lem7086909) (@lem7086908)). Qed.
Lemma lem7086911 : term28 = term25.
Proof. exact (TRANS (@lem7086906) (@lem7086910)). Qed.
Lemma lem7086913 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086914 : term82 = term10.
Proof. exact (@lem7086913 term19). Qed.
Lemma lem7086915 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086916 : term83 = term72.
Proof. exact (MK_COMB (@lem7086915) (@lem7086914)). Qed.
Lemma lem7086917 : term80 = term70.
Proof. exact (MK_COMB (@lem7086916) (@lem7086911)). Qed.
Lemma lem7086919 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086920 : term70 = term77.
Proof. exact (@lem7086919 (NUMERAL 0) term19). Qed.
Lemma lem7086921 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086922 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086923 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086922 h1) (fun h1 : term77 = True => @lem7086921)). Qed.
Lemma lem7086924 : term77 = True.
Proof. exact (EQ_MP (@lem7086923) (@lem7086921)). Qed.
Lemma lem7086925 : term70 = True.
Proof. exact (TRANS (@lem7086920) (@lem7086924)). Qed.
Lemma lem7086926 : term80 = True.
Proof. exact (TRANS (@lem7086917) (@lem7086925)). Qed.
Lemma lem7086927 : term74 = True.
Proof. exact (TRANS (@lem7086903) (@lem7086926)). Qed.
Lemma lem7086928 : term70 = True.
Proof. exact (TRANS (@lem7086880) (@lem7086927)). Qed.
Lemma lem7086929 : term69 = True.
Proof. exact (TRANS (@lem7086871) (@lem7086928)). Qed.
Lemma lem7086930 : True = term69.
Proof. exact (SYM (@lem7086929)). Qed.
Lemma lem7086931 : term69.
Proof. exact (EQ_MP (@lem7086930) (@lem0)). Qed.
Lemma lem7086932 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term90 b x y.
Proof. exact (conj (@lem7086931) (@lem7086793 x b y h1)). Qed.
Lemma lem7086934 (x : real) (y : real) : term85 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7086935 (b : real) (x : real) (y : real) : term91 b x y.
Proof. exact (@lem7086934 term25 (term45 b x y)). Qed.
Lemma lem7086936 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term92 b x y.
Proof. exact (@lem7086935 b x y (@lem7086932 x b y h1)). Qed.
Lemma lem7086937 (b : real) (x : real) (y : real) : (term93 b x y) = (term45 b x y).
Proof. exact (@lem1982733 (term45 b x y)). Qed.
Lemma lem7086938 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7086939 (b : real) (x : real) (y : real) : (term94 b x y) = (term47 b x y).
Proof. exact (MK_COMB (@lem7086938) (@lem7086937 b x y)). Qed.
Lemma lem7086940 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7086941 (b : real) (x : real) (y : real) : (term92 b x y) = (term48 b x y).
Proof. exact (MK_COMB (@lem7086939 b x y) (@lem7086940)). Qed.
Lemma lem7086942 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term48 b x y.
Proof. exact (EQ_MP (@lem7086941 b x y) (@lem7086936 x b y h1)). Qed.
Lemma lem7086944 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7086945 : term69 = term70.
Proof. exact (@lem7086944 term10 term25). Qed.
Lemma lem7086947 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086948 : term25 = term71.
Proof. exact (@lem7086947 term19). Qed.
Lemma lem7086950 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7086951 : term10 = term14.
Proof. exact (@lem7086950 (NUMERAL 0)). Qed.
Lemma lem7086952 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086953 : term72 = term73.
Proof. exact (MK_COMB (@lem7086952) (@lem7086951)). Qed.
Lemma lem7086954 : term70 = term74.
Proof. exact (MK_COMB (@lem7086953) (@lem7086948)). Qed.
Lemma lem7086955 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7086957 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086958 : term70 = term77.
Proof. exact (@lem7086957 (NUMERAL 0) term19). Qed.
Lemma lem7086959 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086960 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086961 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086960 h1) (fun h1 : term77 = True => @lem7086959)). Qed.
Lemma lem7086962 : term77 = True.
Proof. exact (EQ_MP (@lem7086961) (@lem7086959)). Qed.
Lemma lem7086963 : term70 = True.
Proof. exact (TRANS (@lem7086958) (@lem7086962)). Qed.
Lemma lem7086964 : True = term70.
Proof. exact (SYM (@lem7086963)). Qed.
Lemma lem7086965 : term70.
Proof. exact (EQ_MP (@lem7086964) (@lem0)). Qed.
Lemma lem7086966 : term79.
Proof. exact (@lem7086955 (@lem7086965)). Qed.
Lemma lem7086968 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086969 : term70 = term77.
Proof. exact (@lem7086968 (NUMERAL 0) term19). Qed.
Lemma lem7086970 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086971 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086972 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086971 h1) (fun h1 : term77 = True => @lem7086970)). Qed.
Lemma lem7086973 : term77 = True.
Proof. exact (EQ_MP (@lem7086972) (@lem7086970)). Qed.
Lemma lem7086974 : term70 = True.
Proof. exact (TRANS (@lem7086969) (@lem7086973)). Qed.
Lemma lem7086975 : True = term70.
Proof. exact (SYM (@lem7086974)). Qed.
Lemma lem7086976 : term70.
Proof. exact (EQ_MP (@lem7086975) (@lem0)). Qed.
Lemma lem7086977 : term74 = term80.
Proof. exact (@lem7086966 (@lem7086976)). Qed.
Lemma lem7086979 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7086980 : term28 = term29.
Proof. exact (@lem7086979 term19 term19). Qed.
Lemma lem7086981 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7086982 : term31 = term19.
Proof. exact (EQ_MP (@lem7086981) (@lem940073)). Qed.
Lemma lem7086983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7086984 : term29 = term25.
Proof. exact (MK_COMB (@lem7086983) (@lem7086982)). Qed.
Lemma lem7086985 : term28 = term25.
Proof. exact (TRANS (@lem7086980) (@lem7086984)). Qed.
Lemma lem7086987 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7086988 : term82 = term10.
Proof. exact (@lem7086987 term19). Qed.
Lemma lem7086989 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7086990 : term83 = term72.
Proof. exact (MK_COMB (@lem7086989) (@lem7086988)). Qed.
Lemma lem7086991 : term80 = term70.
Proof. exact (MK_COMB (@lem7086990) (@lem7086985)). Qed.
Lemma lem7086993 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7086994 : term70 = term77.
Proof. exact (@lem7086993 (NUMERAL 0) term19). Qed.
Lemma lem7086995 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7086996 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7086997 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7086996 h1) (fun h1 : term77 = True => @lem7086995)). Qed.
Lemma lem7086998 : term77 = True.
Proof. exact (EQ_MP (@lem7086997) (@lem7086995)). Qed.
Lemma lem7086999 : term70 = True.
Proof. exact (TRANS (@lem7086994) (@lem7086998)). Qed.
Lemma lem7087000 : term80 = True.
Proof. exact (TRANS (@lem7086991) (@lem7086999)). Qed.
Lemma lem7087001 : term74 = True.
Proof. exact (TRANS (@lem7086977) (@lem7087000)). Qed.
Lemma lem7087002 : term70 = True.
Proof. exact (TRANS (@lem7086954) (@lem7087001)). Qed.
Lemma lem7087003 : term69 = True.
Proof. exact (TRANS (@lem7086945) (@lem7087002)). Qed.
Lemma lem7087004 : True = term69.
Proof. exact (SYM (@lem7087003)). Qed.
Lemma lem7087005 : term69.
Proof. exact (EQ_MP (@lem7087004) (@lem0)). Qed.
Lemma lem7087006 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term95 b y.
Proof. exact (conj (@lem7087005) (@lem7086789 x b y h1)). Qed.
Lemma lem7087008 (x : real) (y : real) : term96 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7087009 (b : real) (y : real) : term97 b y.
Proof. exact (@lem7087008 term25 (term57 b y)). Qed.
Lemma lem7087010 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term98 b y.
Proof. exact (@lem7087009 b y (@lem7087006 x b y h1)). Qed.
Lemma lem7087011 (b : real) (y : real) : (term99 b y) = (term57 b y).
Proof. exact (@lem1982733 (term57 b y)). Qed.
Lemma lem7087012 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7087013 (b : real) (y : real) : (term100 b y) = (term60 b y).
Proof. exact (MK_COMB (@lem7087012) (@lem7087011 b y)). Qed.
Lemma lem7087014 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7087015 (b : real) (y : real) : (term98 b y) = (term61 b y).
Proof. exact (MK_COMB (@lem7087013 b y) (@lem7087014)). Qed.
Lemma lem7087016 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term61 b y.
Proof. exact (EQ_MP (@lem7087015 b y) (@lem7087010 x b y h1)). Qed.
Lemma lem7087017 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term158 b x y.
Proof. exact (conj (@lem7087016 x b y h1) (@lem7086942 x b y h1)). Qed.
Lemma lem7087019 (x : real) (y : real) : term102 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7087020 (b : real) (x : real) (y : real) : term159 b x y.
Proof. exact (@lem7087019 (term57 b y) (term45 b x y)). Qed.
Lemma lem7087021 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term160 b x y.
Proof. exact (@lem7087020 b x y (@lem7087017 x b y h1)). Qed.
Lemma lem7087022 (b : real) (x : real) (y : real) : (term161 b x y) = (term162 b x y).
Proof. exact (@lem1982753 (term58 b) b y (term44 x y)). Qed.
Lemma lem7087023 (b : real) : (term107 b) = (term108 b).
Proof. exact (@lem1982713 term17 b). Qed.
Lemma lem7087025 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087026 : term25 = term71.
Proof. exact (@lem7087025 term19). Qed.
Lemma lem7087028 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7087029 : term17 = term18.
Proof. exact (@lem7087028 term19). Qed.
Lemma lem7087030 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087031 : term109 = term110.
Proof. exact (MK_COMB (@lem7087030) (@lem7087029)). Qed.
Lemma lem7087032 : term111 = term112.
Proof. exact (MK_COMB (@lem7087031) (@lem7087026)). Qed.
Lemma lem7087033 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7087035 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087036 : term70 = term77.
Proof. exact (@lem7087035 (NUMERAL 0) term19). Qed.
Lemma lem7087037 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087038 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087039 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087038 h1) (fun h1 : term77 = True => @lem7087037)). Qed.
Lemma lem7087040 : term77 = True.
Proof. exact (EQ_MP (@lem7087039) (@lem7087037)). Qed.
Lemma lem7087041 : term70 = True.
Proof. exact (TRANS (@lem7087036) (@lem7087040)). Qed.
Lemma lem7087042 : True = term70.
Proof. exact (SYM (@lem7087041)). Qed.
Lemma lem7087043 : term70.
Proof. exact (EQ_MP (@lem7087042) (@lem0)). Qed.
Lemma lem7087044 : term114.
Proof. exact (@lem7087033 (@lem7087043)). Qed.
Lemma lem7087046 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087047 : term70 = term77.
Proof. exact (@lem7087046 (NUMERAL 0) term19). Qed.
Lemma lem7087048 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087049 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087050 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087049 h1) (fun h1 : term77 = True => @lem7087048)). Qed.
Lemma lem7087051 : term77 = True.
Proof. exact (EQ_MP (@lem7087050) (@lem7087048)). Qed.
Lemma lem7087052 : term70 = True.
Proof. exact (TRANS (@lem7087047) (@lem7087051)). Qed.
Lemma lem7087053 : True = term70.
Proof. exact (SYM (@lem7087052)). Qed.
Lemma lem7087054 : term70.
Proof. exact (EQ_MP (@lem7087053) (@lem0)). Qed.
Lemma lem7087055 : term115.
Proof. exact (@lem7087044 (@lem7087054)). Qed.
Lemma lem7087057 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087058 : term70 = term77.
Proof. exact (@lem7087057 (NUMERAL 0) term19). Qed.
Lemma lem7087059 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087060 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087061 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087060 h1) (fun h1 : term77 = True => @lem7087059)). Qed.
Lemma lem7087062 : term77 = True.
Proof. exact (EQ_MP (@lem7087061) (@lem7087059)). Qed.
Lemma lem7087063 : term70 = True.
Proof. exact (TRANS (@lem7087058) (@lem7087062)). Qed.
Lemma lem7087064 : True = term70.
Proof. exact (SYM (@lem7087063)). Qed.
Lemma lem7087065 : term70.
Proof. exact (EQ_MP (@lem7087064) (@lem0)). Qed.
Lemma lem7087066 : term116.
Proof. exact (@lem7087055 (@lem7087065)). Qed.
Lemma lem7087068 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087069 : term28 = term29.
Proof. exact (@lem7087068 term19 term19). Qed.
Lemma lem7087070 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087071 : term31 = term19.
Proof. exact (EQ_MP (@lem7087070) (@lem940073)). Qed.
Lemma lem7087072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087073 : term29 = term25.
Proof. exact (MK_COMB (@lem7087072) (@lem7087071)). Qed.
Lemma lem7087074 : term28 = term25.
Proof. exact (TRANS (@lem7087069) (@lem7087073)). Qed.
Lemma lem7087076 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7087077 : term119 = term120.
Proof. exact (@lem7087076 term19 term19). Qed.
Lemma lem7087078 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087079 : term31 = term19.
Proof. exact (EQ_MP (@lem7087078) (@lem940073)). Qed.
Lemma lem7087080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087081 : term29 = term25.
Proof. exact (MK_COMB (@lem7087080) (@lem7087079)). Qed.
Lemma lem7087082 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7087083 : term120 = term17.
Proof. exact (MK_COMB (@lem7087082) (@lem7087081)). Qed.
Lemma lem7087084 : term119 = term17.
Proof. exact (TRANS (@lem7087077) (@lem7087083)). Qed.
Lemma lem7087085 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087086 : term121 = term109.
Proof. exact (MK_COMB (@lem7087085) (@lem7087084)). Qed.
Lemma lem7087087 : term122 = term111.
Proof. exact (MK_COMB (@lem7087086) (@lem7087074)). Qed.
Lemma lem7087089 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7087090 : term111 = term10.
Proof. exact (@lem7087089 term19). Qed.
Lemma lem7087091 : term122 = term10.
Proof. exact (TRANS (@lem7087087) (@lem7087090)). Qed.
Lemma lem7087092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087093 : term124 = term125.
Proof. exact (MK_COMB (@lem7087092) (@lem7087091)). Qed.
Lemma lem7087094 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7087095 : term126 = term82.
Proof. exact (MK_COMB (@lem7087093) (@lem7087094)). Qed.
Lemma lem7087097 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087098 : term82 = term10.
Proof. exact (@lem7087097 term19). Qed.
Lemma lem7087099 : term126 = term10.
Proof. exact (TRANS (@lem7087095) (@lem7087098)). Qed.
Lemma lem7087101 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087102 : term28 = term29.
Proof. exact (@lem7087101 term19 term19). Qed.
Lemma lem7087103 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087104 : term31 = term19.
Proof. exact (EQ_MP (@lem7087103) (@lem940073)). Qed.
Lemma lem7087105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087106 : term29 = term25.
Proof. exact (MK_COMB (@lem7087105) (@lem7087104)). Qed.
Lemma lem7087107 : term28 = term25.
Proof. exact (TRANS (@lem7087102) (@lem7087106)). Qed.
Lemma lem7087108 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7087109 : term127 = term82.
Proof. exact (MK_COMB (@lem7087108) (@lem7087107)). Qed.
Lemma lem7087111 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087112 : term82 = term10.
Proof. exact (@lem7087111 term19). Qed.
Lemma lem7087113 : term127 = term10.
Proof. exact (TRANS (@lem7087109) (@lem7087112)). Qed.
Lemma lem7087114 : term10 = term127.
Proof. exact (SYM (@lem7087113)). Qed.
Lemma lem7087115 : term126 = term127.
Proof. exact (TRANS (@lem7087099) (@lem7087114)). Qed.
Lemma lem7087116 : term112 = term14.
Proof. exact (@lem7087066 (@lem7087115)). Qed.
Lemma lem7087117 : term111 = term14.
Proof. exact (TRANS (@lem7087032) (@lem7087116)). Qed.
Lemma lem7087119 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7087120 : term14 = term10.
Proof. exact (@lem7087119 term10). Qed.
Lemma lem7087121 : term111 = term10.
Proof. exact (TRANS (@lem7087117) (@lem7087120)). Qed.
Lemma lem7087122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087123 : term128 = term125.
Proof. exact (MK_COMB (@lem7087122) (@lem7087121)). Qed.
Lemma lem7087124 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7087125 (b : real) : (term108 b) = (term129 b).
Proof. exact (MK_COMB (@lem7087123) (@lem7087124 b)). Qed.
Lemma lem7087126 (b : real) : (term107 b) = (term129 b).
Proof. exact (TRANS (@lem7087023 b) (@lem7087125 b)). Qed.
Lemma lem7087127 (b : real) : (term129 b) = term10.
Proof. exact (@lem1982719 b). Qed.
Lemma lem7087128 (b : real) : (term107 b) = term10.
Proof. exact (TRANS (@lem7087126 b) (@lem7087127 b)). Qed.
Lemma lem7087129 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087130 (b : real) : (term130 b) = term131.
Proof. exact (MK_COMB (@lem7087129) (@lem7087128 b)). Qed.
Lemma lem7087131 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (@lem1982757 (term58 x) y (term58 y)). Qed.
Lemma lem7087132 (y : real) : (term134 y) = (term108 y).
Proof. exact (@lem1982715 term17 y). Qed.
Lemma lem7087134 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087135 : term25 = term71.
Proof. exact (@lem7087134 term19). Qed.
Lemma lem7087137 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7087138 : term17 = term18.
Proof. exact (@lem7087137 term19). Qed.
Lemma lem7087139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087140 : term109 = term110.
Proof. exact (MK_COMB (@lem7087139) (@lem7087138)). Qed.
Lemma lem7087141 : term111 = term112.
Proof. exact (MK_COMB (@lem7087140) (@lem7087135)). Qed.
Lemma lem7087142 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7087144 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087145 : term70 = term77.
Proof. exact (@lem7087144 (NUMERAL 0) term19). Qed.
Lemma lem7087146 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087147 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087148 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087147 h1) (fun h1 : term77 = True => @lem7087146)). Qed.
Lemma lem7087149 : term77 = True.
Proof. exact (EQ_MP (@lem7087148) (@lem7087146)). Qed.
Lemma lem7087150 : term70 = True.
Proof. exact (TRANS (@lem7087145) (@lem7087149)). Qed.
Lemma lem7087151 : True = term70.
Proof. exact (SYM (@lem7087150)). Qed.
Lemma lem7087152 : term70.
Proof. exact (EQ_MP (@lem7087151) (@lem0)). Qed.
Lemma lem7087153 : term114.
Proof. exact (@lem7087142 (@lem7087152)). Qed.
Lemma lem7087155 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087156 : term70 = term77.
Proof. exact (@lem7087155 (NUMERAL 0) term19). Qed.
Lemma lem7087157 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087158 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087159 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087158 h1) (fun h1 : term77 = True => @lem7087157)). Qed.
Lemma lem7087160 : term77 = True.
Proof. exact (EQ_MP (@lem7087159) (@lem7087157)). Qed.
Lemma lem7087161 : term70 = True.
Proof. exact (TRANS (@lem7087156) (@lem7087160)). Qed.
Lemma lem7087162 : True = term70.
Proof. exact (SYM (@lem7087161)). Qed.
Lemma lem7087163 : term70.
Proof. exact (EQ_MP (@lem7087162) (@lem0)). Qed.
Lemma lem7087164 : term115.
Proof. exact (@lem7087153 (@lem7087163)). Qed.
Lemma lem7087166 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087167 : term70 = term77.
Proof. exact (@lem7087166 (NUMERAL 0) term19). Qed.
Lemma lem7087168 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087169 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087170 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087169 h1) (fun h1 : term77 = True => @lem7087168)). Qed.
Lemma lem7087171 : term77 = True.
Proof. exact (EQ_MP (@lem7087170) (@lem7087168)). Qed.
Lemma lem7087172 : term70 = True.
Proof. exact (TRANS (@lem7087167) (@lem7087171)). Qed.
Lemma lem7087173 : True = term70.
Proof. exact (SYM (@lem7087172)). Qed.
Lemma lem7087174 : term70.
Proof. exact (EQ_MP (@lem7087173) (@lem0)). Qed.
Lemma lem7087175 : term116.
Proof. exact (@lem7087164 (@lem7087174)). Qed.
Lemma lem7087177 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087178 : term28 = term29.
Proof. exact (@lem7087177 term19 term19). Qed.
Lemma lem7087179 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087180 : term31 = term19.
Proof. exact (EQ_MP (@lem7087179) (@lem940073)). Qed.
Lemma lem7087181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087182 : term29 = term25.
Proof. exact (MK_COMB (@lem7087181) (@lem7087180)). Qed.
Lemma lem7087183 : term28 = term25.
Proof. exact (TRANS (@lem7087178) (@lem7087182)). Qed.
Lemma lem7087185 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7087186 : term119 = term120.
Proof. exact (@lem7087185 term19 term19). Qed.
Lemma lem7087187 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087188 : term31 = term19.
Proof. exact (EQ_MP (@lem7087187) (@lem940073)). Qed.
Lemma lem7087189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087190 : term29 = term25.
Proof. exact (MK_COMB (@lem7087189) (@lem7087188)). Qed.
Lemma lem7087191 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7087192 : term120 = term17.
Proof. exact (MK_COMB (@lem7087191) (@lem7087190)). Qed.
Lemma lem7087193 : term119 = term17.
Proof. exact (TRANS (@lem7087186) (@lem7087192)). Qed.
Lemma lem7087194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087195 : term121 = term109.
Proof. exact (MK_COMB (@lem7087194) (@lem7087193)). Qed.
Lemma lem7087196 : term122 = term111.
Proof. exact (MK_COMB (@lem7087195) (@lem7087183)). Qed.
Lemma lem7087198 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7087199 : term111 = term10.
Proof. exact (@lem7087198 term19). Qed.
Lemma lem7087200 : term122 = term10.
Proof. exact (TRANS (@lem7087196) (@lem7087199)). Qed.
Lemma lem7087201 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087202 : term124 = term125.
Proof. exact (MK_COMB (@lem7087201) (@lem7087200)). Qed.
Lemma lem7087203 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7087204 : term126 = term82.
Proof. exact (MK_COMB (@lem7087202) (@lem7087203)). Qed.
Lemma lem7087206 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087207 : term82 = term10.
Proof. exact (@lem7087206 term19). Qed.
Lemma lem7087208 : term126 = term10.
Proof. exact (TRANS (@lem7087204) (@lem7087207)). Qed.
Lemma lem7087210 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087211 : term28 = term29.
Proof. exact (@lem7087210 term19 term19). Qed.
Lemma lem7087212 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087213 : term31 = term19.
Proof. exact (EQ_MP (@lem7087212) (@lem940073)). Qed.
Lemma lem7087214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087215 : term29 = term25.
Proof. exact (MK_COMB (@lem7087214) (@lem7087213)). Qed.
Lemma lem7087216 : term28 = term25.
Proof. exact (TRANS (@lem7087211) (@lem7087215)). Qed.
Lemma lem7087217 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7087218 : term127 = term82.
Proof. exact (MK_COMB (@lem7087217) (@lem7087216)). Qed.
Lemma lem7087220 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087221 : term82 = term10.
Proof. exact (@lem7087220 term19). Qed.
Lemma lem7087222 : term127 = term10.
Proof. exact (TRANS (@lem7087218) (@lem7087221)). Qed.
Lemma lem7087223 : term10 = term127.
Proof. exact (SYM (@lem7087222)). Qed.
Lemma lem7087224 : term126 = term127.
Proof. exact (TRANS (@lem7087208) (@lem7087223)). Qed.
Lemma lem7087225 : term112 = term14.
Proof. exact (@lem7087175 (@lem7087224)). Qed.
Lemma lem7087226 : term111 = term14.
Proof. exact (TRANS (@lem7087141) (@lem7087225)). Qed.
Lemma lem7087228 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7087229 : term14 = term10.
Proof. exact (@lem7087228 term10). Qed.
Lemma lem7087230 : term111 = term10.
Proof. exact (TRANS (@lem7087226) (@lem7087229)). Qed.
Lemma lem7087231 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087232 : term128 = term125.
Proof. exact (MK_COMB (@lem7087231) (@lem7087230)). Qed.
Lemma lem7087233 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7087234 (y : real) : (term108 y) = (term129 y).
Proof. exact (MK_COMB (@lem7087232) (@lem7087233 y)). Qed.
Lemma lem7087235 (y : real) : (term134 y) = (term129 y).
Proof. exact (TRANS (@lem7087132 y) (@lem7087234 y)). Qed.
Lemma lem7087236 (y : real) : (term129 y) = term10.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7087237 (y : real) : (term134 y) = term10.
Proof. exact (TRANS (@lem7087235 y) (@lem7087236 y)). Qed.
Lemma lem7087238 (x : real) : (term165 x) = (term165 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem7087239 (y : real) (x : real) : (term164 x y) = (term166 x).
Proof. exact (MK_COMB (@lem7087238 x) (@lem7087237 y)). Qed.
Lemma lem7087240 (y : real) (x : real) : (term163 x y) = (term166 x).
Proof. exact (TRANS (@lem7087131 x y) (@lem7087239 y x)). Qed.
Lemma lem7087241 (x : real) : (term166 x) = (term58 x).
Proof. exact (@lem1982723 (term58 x)). Qed.
Lemma lem7087242 (y : real) (x : real) : (term163 x y) = (term58 x).
Proof. exact (TRANS (@lem7087240 y x) (@lem7087241 x)). Qed.
Lemma lem7087243 (b : real) (y : real) (x : real) : (term162 b x y) = (term136 x).
Proof. exact (MK_COMB (@lem7087130 b) (@lem7087242 y x)). Qed.
Lemma lem7087244 (b : real) (y : real) (x : real) : (term161 b x y) = (term136 x).
Proof. exact (TRANS (@lem7087022 b x y) (@lem7087243 b y x)). Qed.
Lemma lem7087245 (x : real) : (term136 x) = (term58 x).
Proof. exact (@lem1982721 (term58 x)). Qed.
Lemma lem7087246 (b : real) (y : real) (x : real) : (term161 b x y) = (term58 x).
Proof. exact (TRANS (@lem7087244 b y x) (@lem7087245 x)). Qed.
Lemma lem7087247 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7087248 (b : real) (y : real) (x : real) : (term167 b x y) = (term138 x).
Proof. exact (MK_COMB (@lem7087247) (@lem7087246 b y x)). Qed.
Lemma lem7087249 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7087250 (b : real) (y : real) (x : real) : (term160 b x y) = (term139 x).
Proof. exact (MK_COMB (@lem7087248 b y x) (@lem7087249)). Qed.
Lemma lem7087251 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term139 x.
Proof. exact (EQ_MP (@lem7087250 b y x) (@lem7087021 x b y h1)). Qed.
Lemma lem7087253 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7087254 : term69 = term70.
Proof. exact (@lem7087253 term10 term25). Qed.
Lemma lem7087256 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087257 : term25 = term71.
Proof. exact (@lem7087256 term19). Qed.
Lemma lem7087259 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087260 : term10 = term14.
Proof. exact (@lem7087259 (NUMERAL 0)). Qed.
Lemma lem7087261 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7087262 : term72 = term73.
Proof. exact (MK_COMB (@lem7087261) (@lem7087260)). Qed.
Lemma lem7087263 : term70 = term74.
Proof. exact (MK_COMB (@lem7087262) (@lem7087257)). Qed.
Lemma lem7087264 : term75.
Proof. exact (@lem1980255 term10 term25 term25 term25). Qed.
Lemma lem7087266 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087267 : term70 = term77.
Proof. exact (@lem7087266 (NUMERAL 0) term19). Qed.
Lemma lem7087268 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087269 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087270 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087269 h1) (fun h1 : term77 = True => @lem7087268)). Qed.
Lemma lem7087271 : term77 = True.
Proof. exact (EQ_MP (@lem7087270) (@lem7087268)). Qed.
Lemma lem7087272 : term70 = True.
Proof. exact (TRANS (@lem7087267) (@lem7087271)). Qed.
Lemma lem7087273 : True = term70.
Proof. exact (SYM (@lem7087272)). Qed.
Lemma lem7087274 : term70.
Proof. exact (EQ_MP (@lem7087273) (@lem0)). Qed.
Lemma lem7087275 : term79.
Proof. exact (@lem7087264 (@lem7087274)). Qed.
Lemma lem7087277 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087278 : term70 = term77.
Proof. exact (@lem7087277 (NUMERAL 0) term19). Qed.
Lemma lem7087279 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087280 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087281 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087280 h1) (fun h1 : term77 = True => @lem7087279)). Qed.
Lemma lem7087282 : term77 = True.
Proof. exact (EQ_MP (@lem7087281) (@lem7087279)). Qed.
Lemma lem7087283 : term70 = True.
Proof. exact (TRANS (@lem7087278) (@lem7087282)). Qed.
Lemma lem7087284 : True = term70.
Proof. exact (SYM (@lem7087283)). Qed.
Lemma lem7087285 : term70.
Proof. exact (EQ_MP (@lem7087284) (@lem0)). Qed.
Lemma lem7087286 : term74 = term80.
Proof. exact (@lem7087275 (@lem7087285)). Qed.
Lemma lem7087288 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087289 : term28 = term29.
Proof. exact (@lem7087288 term19 term19). Qed.
Lemma lem7087290 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087291 : term31 = term19.
Proof. exact (EQ_MP (@lem7087290) (@lem940073)). Qed.
Lemma lem7087292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087293 : term29 = term25.
Proof. exact (MK_COMB (@lem7087292) (@lem7087291)). Qed.
Lemma lem7087294 : term28 = term25.
Proof. exact (TRANS (@lem7087289) (@lem7087293)). Qed.
Lemma lem7087296 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087297 : term82 = term10.
Proof. exact (@lem7087296 term19). Qed.
Lemma lem7087298 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7087299 : term83 = term72.
Proof. exact (MK_COMB (@lem7087298) (@lem7087297)). Qed.
Lemma lem7087300 : term80 = term70.
Proof. exact (MK_COMB (@lem7087299) (@lem7087294)). Qed.
Lemma lem7087302 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087303 : term70 = term77.
Proof. exact (@lem7087302 (NUMERAL 0) term19). Qed.
Lemma lem7087304 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087305 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087306 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087305 h1) (fun h1 : term77 = True => @lem7087304)). Qed.
Lemma lem7087307 : term77 = True.
Proof. exact (EQ_MP (@lem7087306) (@lem7087304)). Qed.
Lemma lem7087308 : term70 = True.
Proof. exact (TRANS (@lem7087303) (@lem7087307)). Qed.
Lemma lem7087309 : term80 = True.
Proof. exact (TRANS (@lem7087300) (@lem7087308)). Qed.
Lemma lem7087310 : term74 = True.
Proof. exact (TRANS (@lem7087286) (@lem7087309)). Qed.
Lemma lem7087311 : term70 = True.
Proof. exact (TRANS (@lem7087263) (@lem7087310)). Qed.
Lemma lem7087312 : term69 = True.
Proof. exact (TRANS (@lem7087254) (@lem7087311)). Qed.
Lemma lem7087313 : True = term69.
Proof. exact (SYM (@lem7087312)). Qed.
Lemma lem7087314 : term69.
Proof. exact (EQ_MP (@lem7087313) (@lem0)). Qed.
Lemma lem7087315 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term140 x.
Proof. exact (conj (@lem7087314) (@lem7087251 x b y h1)). Qed.
Lemma lem7087317 (x : real) (y : real) : term96 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7087318 (x : real) : term141 x.
Proof. exact (@lem7087317 term25 (term58 x)). Qed.
Lemma lem7087319 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term142 x.
Proof. exact (@lem7087318 x (@lem7087315 x b y h1)). Qed.
Lemma lem7087320 (x : real) : (term143 x) = (term58 x).
Proof. exact (@lem1982733 (term58 x)). Qed.
Lemma lem7087321 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7087322 (x : real) : (term144 x) = (term138 x).
Proof. exact (MK_COMB (@lem7087321) (@lem7087320 x)). Qed.
Lemma lem7087323 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7087324 (x : real) : (term142 x) = (term139 x).
Proof. exact (MK_COMB (@lem7087322 x) (@lem7087323)). Qed.
Lemma lem7087325 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term139 x.
Proof. exact (EQ_MP (@lem7087324 x) (@lem7087319 x b y h1)). Qed.
Lemma lem7087326 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term145 x.
Proof. exact (conj (@lem7087325 x b y h1) (@lem7086868 x b y h1)). Qed.
Lemma lem7087328 (x : real) (y : real) : term102 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7087329 (x : real) : term146 x.
Proof. exact (@lem7087328 (term58 x) x). Qed.
Lemma lem7087330 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term147 x.
Proof. exact (@lem7087329 x (@lem7087326 x b y h1)). Qed.
Lemma lem7087331 (x : real) : (term107 x) = (term108 x).
Proof. exact (@lem1982713 term17 x). Qed.
Lemma lem7087333 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087334 : term25 = term71.
Proof. exact (@lem7087333 term19). Qed.
Lemma lem7087336 (x : nat) : (term15 x) = (term16 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7087337 : term17 = term18.
Proof. exact (@lem7087336 term19). Qed.
Lemma lem7087338 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087339 : term109 = term110.
Proof. exact (MK_COMB (@lem7087338) (@lem7087337)). Qed.
Lemma lem7087340 : term111 = term112.
Proof. exact (MK_COMB (@lem7087339) (@lem7087334)). Qed.
Lemma lem7087341 : term113.
Proof. exact (@lem1981473 term17 term25 term25 term25 term10 term25). Qed.
Lemma lem7087343 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087344 : term70 = term77.
Proof. exact (@lem7087343 (NUMERAL 0) term19). Qed.
Lemma lem7087345 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087346 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087347 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087346 h1) (fun h1 : term77 = True => @lem7087345)). Qed.
Lemma lem7087348 : term77 = True.
Proof. exact (EQ_MP (@lem7087347) (@lem7087345)). Qed.
Lemma lem7087349 : term70 = True.
Proof. exact (TRANS (@lem7087344) (@lem7087348)). Qed.
Lemma lem7087350 : True = term70.
Proof. exact (SYM (@lem7087349)). Qed.
Lemma lem7087351 : term70.
Proof. exact (EQ_MP (@lem7087350) (@lem0)). Qed.
Lemma lem7087352 : term114.
Proof. exact (@lem7087341 (@lem7087351)). Qed.
Lemma lem7087354 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087355 : term70 = term77.
Proof. exact (@lem7087354 (NUMERAL 0) term19). Qed.
Lemma lem7087356 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087357 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087358 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087357 h1) (fun h1 : term77 = True => @lem7087356)). Qed.
Lemma lem7087359 : term77 = True.
Proof. exact (EQ_MP (@lem7087358) (@lem7087356)). Qed.
Lemma lem7087360 : term70 = True.
Proof. exact (TRANS (@lem7087355) (@lem7087359)). Qed.
Lemma lem7087361 : True = term70.
Proof. exact (SYM (@lem7087360)). Qed.
Lemma lem7087362 : term70.
Proof. exact (EQ_MP (@lem7087361) (@lem0)). Qed.
Lemma lem7087363 : term115.
Proof. exact (@lem7087352 (@lem7087362)). Qed.
Lemma lem7087365 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087366 : term70 = term77.
Proof. exact (@lem7087365 (NUMERAL 0) term19). Qed.
Lemma lem7087367 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087368 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087369 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087368 h1) (fun h1 : term77 = True => @lem7087367)). Qed.
Lemma lem7087370 : term77 = True.
Proof. exact (EQ_MP (@lem7087369) (@lem7087367)). Qed.
Lemma lem7087371 : term70 = True.
Proof. exact (TRANS (@lem7087366) (@lem7087370)). Qed.
Lemma lem7087372 : True = term70.
Proof. exact (SYM (@lem7087371)). Qed.
Lemma lem7087373 : term70.
Proof. exact (EQ_MP (@lem7087372) (@lem0)). Qed.
Lemma lem7087374 : term116.
Proof. exact (@lem7087363 (@lem7087373)). Qed.
Lemma lem7087376 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087377 : term28 = term29.
Proof. exact (@lem7087376 term19 term19). Qed.
Lemma lem7087378 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087379 : term31 = term19.
Proof. exact (EQ_MP (@lem7087378) (@lem940073)). Qed.
Lemma lem7087380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087381 : term29 = term25.
Proof. exact (MK_COMB (@lem7087380) (@lem7087379)). Qed.
Lemma lem7087382 : term28 = term25.
Proof. exact (TRANS (@lem7087377) (@lem7087381)). Qed.
Lemma lem7087384 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7087385 : term119 = term120.
Proof. exact (@lem7087384 term19 term19). Qed.
Lemma lem7087386 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087387 : term31 = term19.
Proof. exact (EQ_MP (@lem7087386) (@lem940073)). Qed.
Lemma lem7087388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087389 : term29 = term25.
Proof. exact (MK_COMB (@lem7087388) (@lem7087387)). Qed.
Lemma lem7087390 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7087391 : term120 = term17.
Proof. exact (MK_COMB (@lem7087390) (@lem7087389)). Qed.
Lemma lem7087392 : term119 = term17.
Proof. exact (TRANS (@lem7087385) (@lem7087391)). Qed.
Lemma lem7087393 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7087394 : term121 = term109.
Proof. exact (MK_COMB (@lem7087393) (@lem7087392)). Qed.
Lemma lem7087395 : term122 = term111.
Proof. exact (MK_COMB (@lem7087394) (@lem7087382)). Qed.
Lemma lem7087397 (m : nat) : (term123 m) = term10.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7087398 : term111 = term10.
Proof. exact (@lem7087397 term19). Qed.
Lemma lem7087399 : term122 = term10.
Proof. exact (TRANS (@lem7087395) (@lem7087398)). Qed.
Lemma lem7087400 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087401 : term124 = term125.
Proof. exact (MK_COMB (@lem7087400) (@lem7087399)). Qed.
Lemma lem7087402 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem7087403 : term126 = term82.
Proof. exact (MK_COMB (@lem7087401) (@lem7087402)). Qed.
Lemma lem7087405 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087406 : term82 = term10.
Proof. exact (@lem7087405 term19). Qed.
Lemma lem7087407 : term126 = term10.
Proof. exact (TRANS (@lem7087403) (@lem7087406)). Qed.
Lemma lem7087409 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7087410 : term28 = term29.
Proof. exact (@lem7087409 term19 term19). Qed.
Lemma lem7087411 : (term30 = (BIT1 0)) = (term31 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7087412 : term31 = term19.
Proof. exact (EQ_MP (@lem7087411) (@lem940073)). Qed.
Lemma lem7087413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7087414 : term29 = term25.
Proof. exact (MK_COMB (@lem7087413) (@lem7087412)). Qed.
Lemma lem7087415 : term28 = term25.
Proof. exact (TRANS (@lem7087410) (@lem7087414)). Qed.
Lemma lem7087416 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem7087417 : term127 = term82.
Proof. exact (MK_COMB (@lem7087416) (@lem7087415)). Qed.
Lemma lem7087419 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087420 : term82 = term10.
Proof. exact (@lem7087419 term19). Qed.
Lemma lem7087421 : term127 = term10.
Proof. exact (TRANS (@lem7087417) (@lem7087420)). Qed.
Lemma lem7087422 : term10 = term127.
Proof. exact (SYM (@lem7087421)). Qed.
Lemma lem7087423 : term126 = term127.
Proof. exact (TRANS (@lem7087407) (@lem7087422)). Qed.
Lemma lem7087424 : term112 = term14.
Proof. exact (@lem7087374 (@lem7087423)). Qed.
Lemma lem7087425 : term111 = term14.
Proof. exact (TRANS (@lem7087340) (@lem7087424)). Qed.
Lemma lem7087427 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7087428 : term14 = term10.
Proof. exact (@lem7087427 term10). Qed.
Lemma lem7087429 : term111 = term10.
Proof. exact (TRANS (@lem7087425) (@lem7087428)). Qed.
Lemma lem7087430 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7087431 : term128 = term125.
Proof. exact (MK_COMB (@lem7087430) (@lem7087429)). Qed.
Lemma lem7087432 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7087433 (x : real) : (term108 x) = (term129 x).
Proof. exact (MK_COMB (@lem7087431) (@lem7087432 x)). Qed.
Lemma lem7087434 (x : real) : (term107 x) = (term129 x).
Proof. exact (TRANS (@lem7087331 x) (@lem7087433 x)). Qed.
Lemma lem7087435 (x : real) : (term129 x) = term10.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7087436 (x : real) : (term107 x) = term10.
Proof. exact (TRANS (@lem7087434 x) (@lem7087435 x)). Qed.
Lemma lem7087437 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7087438 (x : real) : (term148 x) = term149.
Proof. exact (MK_COMB (@lem7087437) (@lem7087436 x)). Qed.
Lemma lem7087439 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem7087440 (x : real) : (term147 x) = term150.
Proof. exact (MK_COMB (@lem7087438 x) (@lem7087439)). Qed.
Lemma lem7087441 (x : real) (b : real) (y : real) (h1 : term157 x b y) : term150.
Proof. exact (EQ_MP (@lem7087440 x) (@lem7087330 x b y h1)). Qed.
Lemma lem7087443 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7087444 : term150 = term151.
Proof. exact (@lem7087443 term10 term10). Qed.
Lemma lem7087446 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087447 : term10 = term14.
Proof. exact (@lem7087446 (NUMERAL 0)). Qed.
Lemma lem7087449 (x : nat) : (real_of_num x) = (term13 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7087450 : term10 = term14.
Proof. exact (@lem7087449 (NUMERAL 0)). Qed.
Lemma lem7087451 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7087452 : term72 = term73.
Proof. exact (MK_COMB (@lem7087451) (@lem7087450)). Qed.
Lemma lem7087453 : term151 = term152.
Proof. exact (MK_COMB (@lem7087452) (@lem7087447)). Qed.
Lemma lem7087454 : term153.
Proof. exact (@lem1980255 term10 term25 term10 term25). Qed.
Lemma lem7087456 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087457 : term70 = term77.
Proof. exact (@lem7087456 (NUMERAL 0) term19). Qed.
Lemma lem7087458 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087459 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087460 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087459 h1) (fun h1 : term77 = True => @lem7087458)). Qed.
Lemma lem7087461 : term77 = True.
Proof. exact (EQ_MP (@lem7087460) (@lem7087458)). Qed.
Lemma lem7087462 : term70 = True.
Proof. exact (TRANS (@lem7087457) (@lem7087461)). Qed.
Lemma lem7087463 : True = term70.
Proof. exact (SYM (@lem7087462)). Qed.
Lemma lem7087464 : term70.
Proof. exact (EQ_MP (@lem7087463) (@lem0)). Qed.
Lemma lem7087465 : term154.
Proof. exact (@lem7087454 (@lem7087464)). Qed.
Lemma lem7087467 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087468 : term70 = term77.
Proof. exact (@lem7087467 (NUMERAL 0) term19). Qed.
Lemma lem7087469 : term78 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7087470 (h1 : term78 = (BIT1 0)) : term77 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7087471 : (term78 = (BIT1 0)) = (term77 = True).
Proof. exact (prop_ext (fun h1 : term78 = (BIT1 0) => @lem7087470 h1) (fun h1 : term77 = True => @lem7087469)). Qed.
Lemma lem7087472 : term77 = True.
Proof. exact (EQ_MP (@lem7087471) (@lem7087469)). Qed.
Lemma lem7087473 : term70 = True.
Proof. exact (TRANS (@lem7087468) (@lem7087472)). Qed.
Lemma lem7087474 : True = term70.
Proof. exact (SYM (@lem7087473)). Qed.
Lemma lem7087475 : term70.
Proof. exact (EQ_MP (@lem7087474) (@lem0)). Qed.
Lemma lem7087476 : term152 = term155.
Proof. exact (@lem7087465 (@lem7087475)). Qed.
Lemma lem7087478 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087479 : term82 = term10.
Proof. exact (@lem7087478 term19). Qed.
Lemma lem7087481 (x : nat) : (term81 x) = term10.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7087482 : term82 = term10.
Proof. exact (@lem7087481 term19). Qed.
Lemma lem7087483 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7087484 : term83 = term72.
Proof. exact (MK_COMB (@lem7087483) (@lem7087482)). Qed.
Lemma lem7087485 : term155 = term151.
Proof. exact (MK_COMB (@lem7087484) (@lem7087479)). Qed.
Lemma lem7087487 (m : nat) (n : nat) : (term76 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7087488 : term151 = term156.
Proof. exact (@lem7087487 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7087489 : term156 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7087490 : term151 = False.
Proof. exact (TRANS (@lem7087488) (@lem7087489)). Qed.
Lemma lem7087491 : term155 = False.
Proof. exact (TRANS (@lem7087485) (@lem7087490)). Qed.
Lemma lem7087492 : term152 = False.
Proof. exact (TRANS (@lem7087476) (@lem7087491)). Qed.
Lemma lem7087493 : term151 = False.
Proof. exact (TRANS (@lem7087453) (@lem7087492)). Qed.
Lemma lem7087494 : term150 = False.
Proof. exact (TRANS (@lem7087444) (@lem7087493)). Qed.
Lemma lem7087495 (x : real) (b : real) (y : real) (h1 : term157 x b y) : False.
Proof. exact (EQ_MP (@lem7087494) (@lem7087441 x b y h1)). Qed.
Lemma lem7087496 (x : real) (b : real) (y : real) (h1 : term67 x b y) : False.
Proof. exact (or_elim (@lem7086077 x b y h1) (fun h0 : term68 y b x => @lem7086787 y b x h0) (fun h0 : term157 x b y => @lem7087495 x b y h0)). Qed.
Lemma lem7087498 (x : real) (b : real) (y : real) (h1 : term67 x b y) : term67 x b y.
Proof. exact (h1). Qed.
Lemma lem7087499 (x : real) (b : real) (y : real) (h1 : term67 x b y) : (term67 x b y) = False.
Proof. exact (prop_ext (fun h2 : term67 x b y => @lem7087496 x b y h1) (fun h2 : False => @lem7087498 x b y h1)). Qed.
Lemma lem7087500 (x : real) (b : real) (y : real) (h1 : term67 x b y) : False.
Proof. exact (EQ_MP (@lem7087499 x b y h1) (@lem7087498 x b y h1)). Qed.
Lemma lem7087501 (x : real) (y : real) (b : real) (h1 : term5 x y b) : term5 x y b.
Proof. exact (h1). Qed.
Lemma lem7087502 (x : real) (y : real) (b : real) (h1 : term5 x y b) : term67 x b y.
Proof. exact (EQ_MP (@lem7086067 x b y) (@lem7087501 x y b h1)). Qed.
Lemma lem7087503 (x : real) (y : real) (b : real) (h1 : term5 x y b) : (term67 x b y) = False.
Proof. exact (prop_ext (fun h2 : term67 x b y => @lem7087500 x b y h2) (fun h2 : False => @lem7087502 x y b h1)). Qed.
Lemma lem7087504 (x : real) (y : real) (b : real) (h1 : term5 x y b) : False.
Proof. exact (EQ_MP (@lem7087503 x y b h1) (@lem7087502 x y b h1)). Qed.
Lemma lem7087505 (x : real) (y : real) (b : real) : term168 x y b.
Proof. exact (fun h0 : term5 x y b => @lem7087504 x y b h0). Qed.
Lemma lem7087506 (x : real) (y : real) (b : real) : term169 x y b.
Proof. exact (@lem1386578 (term170 x y b)). Qed.
Lemma lem7087509 (x : real) (y : real) (b : real) : term170 x y b.
Proof. exact (@lem7087506 x y b (@lem7087505 x y b)). Qed.
Lemma lem7087510 (t1 : Prop) : term171 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7087511 (t1 : Prop) : (term171 t1) = (term172 t1).
Proof. exact (eq_refl (term171 t1)). Qed.
Lemma lem7087512 (t1 : Prop) : term172 t1.
Proof. exact (EQ_MP (@lem7087511 t1) (@lem7087510 t1)). Qed.
Lemma lem7087513 (t1 : Prop) (t2 : Prop) : term173 t1 t2.
Proof. exact (@lem7087512 t1 t2). Qed.
Lemma lem7087514 (t1 : Prop) (t2 : Prop) : (term173 t1 t2) = (term174 t1 t2).
Proof. exact (eq_refl (term173 t1 t2)). Qed.
Lemma lem7087515 (t1 : Prop) (t2 : Prop) : term174 t1 t2.
Proof. exact (EQ_MP (@lem7087514 t1 t2) (@lem7087513 t1 t2)). Qed.
Lemma lem7087516 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term175 t1 t2 t3.
Proof. exact (@lem7087515 t1 t2 t3). Qed.
Lemma lem7087517 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term175 t1 t2 t3) = ((term176 t1 t2 t3) = (term177 t1 t2 t3)).
Proof. exact (eq_refl (term175 t1 t2 t3)). Qed.
Lemma lem7087518 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term176 t1 t2 t3) = (term177 t1 t2 t3).
Proof. exact (EQ_MP (@lem7087517 t1 t2 t3) (@lem7087516 t1 t2 t3)). Qed.
Lemma lem7087519 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term177 t1 t2 t3) = (term176 t1 t2 t3).
Proof. exact (SYM (@lem7087518 t1 t2 t3)). Qed.
Lemma lem7087520 {A : Type'} : term178 A.
Proof. exact (fun f : A -> real => @lem7085797 A f). Qed.
Lemma lem7087521 (x : real) (y : real) : term179 x y.
Proof. exact (fun b : real => @lem7087509 x y b). Qed.
Lemma lem7087522 (x : real) : term180 x.
Proof. exact (fun y : real => @lem7087521 x y). Qed.
Lemma lem7087523 : term181.
Proof. exact (fun x : real => @lem7087522 x). Qed.
Lemma lem7087524 {A : Type'} (x : A) : term182 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem7087525 {A : Type'} (x : A) : (term182 A x) = (term183 A x).
Proof. exact (eq_refl (term182 A x)). Qed.
Lemma lem7087526 {A : Type'} (x : A) : term183 A x.
Proof. exact (EQ_MP (@lem7087525 A x) (@lem7087524 A x)). Qed.
Lemma lem7087527 {A : Type'} (x : A) (y : A) : term184 A x y.
Proof. exact (@lem7087526 A x y). Qed.
Lemma lem7087528 {A : Type'} (y : A) (x : A) : (term184 A x y) = (term185 A y x).
Proof. exact (eq_refl (term184 A x y)). Qed.
Lemma lem7087529 {A : Type'} (y : A) (x : A) : term185 A y x.
Proof. exact (EQ_MP (@lem7087528 A y x) (@lem7087527 A x y)). Qed.
Lemma lem7087530 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term186 A y x s.
Proof. exact (@lem7087529 A y x s). Qed.
Lemma lem7087531 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term186 A y x s) = ((term187 A x y s) = (term188 A y x s)).
Proof. exact (eq_refl (term186 A y x s)). Qed.
Lemma lem7087533 {A : Type'} (x : A) : term189 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem7087534 {A : Type'} (x : A) : (term189 A x) = (term190 A x).
Proof. exact (eq_refl (term189 A x)). Qed.
Lemma lem7087535 {A : Type'} (x : A) : term190 A x.
Proof. exact (EQ_MP (@lem7087534 A x) (@lem7087533 A x)). Qed.
Lemma lem7087536 {A : Type'} (x : A) : term191 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem7087538 {_131524 : Type'} : term192 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7087539 {_131524 : Type'} (x : _131524) : term193 _131524 x.
Proof. exact (@lem7087538 _131524 x). Qed.
Lemma lem7087540 {_131524 : Type'} (x : _131524) : (term193 _131524 x) = (term194 _131524 x).
Proof. exact (eq_refl (term193 _131524 x)). Qed.
Lemma lem7087541 {_131524 : Type'} (x : _131524) : term194 _131524 x.
Proof. exact (EQ_MP (@lem7087540 _131524 x) (@lem7087539 _131524 x)). Qed.
Lemma lem7087542 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term195 _131524 x f.
Proof. exact (@lem7087541 _131524 x f). Qed.
Lemma lem7087543 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term195 _131524 x f) = (term196 _131524 x f).
Proof. exact (eq_refl (term195 _131524 x f)). Qed.
Lemma lem7087544 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term196 _131524 x f.
Proof. exact (EQ_MP (@lem7087543 _131524 x f) (@lem7087542 _131524 x f)). Qed.
Lemma lem7087545 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term197 _131524 x f s.
Proof. exact (@lem7087544 _131524 x f s). Qed.
Lemma lem7087546 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term197 _131524 x f s) = (term198 _131524 x s f).
Proof. exact (eq_refl (term197 _131524 x f s)). Qed.
Lemma lem7087547 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term198 _131524 x s f.
Proof. exact (EQ_MP (@lem7087546 _131524 x s f) (@lem7087545 _131524 x f s)). Qed.
Lemma lem7087548 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7087549 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term199 _131524 x s f) = (term200 _131524 x s f).
Proof. exact (@lem7087547 _131524 x s f (@lem7087548 _131524 s h1)). Qed.
Lemma lem7087555 {_131483 : Type'} : term201 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7087556 {_131483 : Type'} (f : _131483 -> real) : term202 _131483 f.
Proof. exact (@lem7087555 _131483 f). Qed.
Lemma lem7087557 {_131483 : Type'} (f : _131483 -> real) : (term202 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term10).
Proof. exact (eq_refl (term202 _131483 f)). Qed.
Lemma lem7087559 {A : Type'} (h1 : term203 A) : term203 A.
Proof. exact (h1). Qed.
Lemma lem7087560 {A : Type'} (P : type686 A) (h1 : term203 A) : term204 A P.
Proof. exact (@lem7087559 A h1 P). Qed.
Lemma lem7087561 {A : Type'} (P : type686 A) : (term204 A P) = (term205 A P).
Proof. exact (eq_refl (term204 A P)). Qed.
Lemma lem7087562 {A : Type'} (P : type686 A) (h1 : term203 A) : term205 A P.
Proof. exact (EQ_MP (@lem7087561 A P) (@lem7087560 A P h1)). Qed.
Lemma lem7087563 {A : Type'} (P : type686 A) (h1 : term206 A P) : term206 A P.
Proof. exact (h1). Qed.
Lemma lem7087564 {A : Type'} (P : type686 A) (h1 : term203 A) (h2 : term206 A P) : term207 A P.
Proof. exact (@lem7087562 A P h1 (@lem7087563 A P h2)). Qed.
Lemma lem7087565 {A : Type'} (P : type686 A) (h1 : term206 A P) : term208 A P.
Proof. exact (fun h0 : term203 A => @lem7087564 A P h0 h1). Qed.
Lemma lem7087566 {A : Type'} (h1 : term203 A) : term203 A.
Proof. exact (h1). Qed.
Lemma lem7087567 {A : Type'} (P : type686 A) (h1 : term203 A) (h2 : term206 A P) : term207 A P.
Proof. exact (@lem7087565 A P h2 (@lem7087566 A h1)). Qed.
Lemma lem7087568 {A : Type'} (P : type686 A) (h1 : term203 A) : term205 A P.
Proof. exact (fun h0 : term206 A P => @lem7087567 A P h1 h0). Qed.
Lemma lem7087569 {A : Type'} (h1 : term203 A) : term203 A.
Proof. exact (fun P : type686 A => @lem7087568 A P h1). Qed.
Lemma lem7087570 {A : Type'} : term209 A.
Proof. exact (fun h0 : term203 A => @lem7087569 A h0). Qed.
Lemma lem7087571 {A : Type'} : term203 A.
Proof. exact (@lem7087570 A (@lem3558722 A)). Qed.
Lemma lem7087572 {A : Type'} (P : type686 A) : term204 A P.
Proof. exact (@lem7087571 A P). Qed.
Lemma lem7087573 {A : Type'} (P : type686 A) : (term204 A P) = (term205 A P).
Proof. exact (eq_refl (term204 A P)). Qed.
Lemma lem7087580 (p : Prop) (q : Prop) (r : Prop) : (term210 p q r) = (term211 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7087581 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term212 A s f b) = (term213 A s f b).
Proof. exact (@lem7087580 (@FINITE A s) (term214 A s f b) (term215 A s f b)). Qed.
Lemma lem7087585 (p : Prop) (q : Prop) (r : Prop) : (term210 p q r) = (term211 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7087586 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term216 A s f b) = (term217 A s f b).
Proof. exact (@lem7087585 (term218 A s f) (term219 A s f b) (term215 A s f b)). Qed.
Lemma lem7087603 {A : Type'} (s : A -> Prop) : (term220 A s) = (term220 A s).
Proof. exact (eq_refl (term220 A s)). Qed.
Lemma lem7087604 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term213 A s f b) = (term221 A s f b).
Proof. exact (MK_COMB (@lem7087603 A s) (@lem7087586 A s f b)). Qed.
Lemma lem7087607 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term212 A s f b) = (term221 A s f b).
Proof. exact (TRANS (@lem7087581 A s f b) (@lem7087604 A s f b)). Qed.
Lemma lem7087608 {A : Type'} (f : A -> real) (b : real) : (term222 A f b) = (term223 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7087607 A s f b)). Qed.
Lemma lem7087609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7087610 {A : Type'} (f : A -> real) (b : real) : (term224 A f b) = (term225 A f b).
Proof. exact (MK_COMB (@lem7087609 A) (@lem7087608 A f b)). Qed.
Lemma lem7087615 {A : Type'} (f : A -> real) (b : real) : (term225 A f b) = (term224 A f b).
Proof. exact (SYM (@lem7087610 A f b)). Qed.
Lemma lem7087617 {A : Type'} (P : type686 A) : term205 A P.
Proof. exact (EQ_MP (@lem7087573 A P) (@lem7087572 A P)). Qed.
Lemma lem7087618 {A : Type'} (P : type686 A) : term205 A P.
Proof. exact (@lem7087617 A P). Qed.
Lemma lem7087619 {A : Type'} (f : A -> real) (b : real) : term226 A f b.
Proof. exact (@lem7087618 A (term227 A f b)). Qed.
Lemma lem7087620 {A : Type'} (f : A -> real) (b : real) : (term228 A f b) = (term229 A f b).
Proof. exact (eq_refl (term228 A f b)). Qed.
Lemma lem7087621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7087622 {A : Type'} (f : A -> real) (b : real) : (term230 A f b) = (term231 A f b).
Proof. exact (MK_COMB (@lem7087621) (@lem7087620 A f b)). Qed.
Lemma lem7087623 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term232 A f b s) = (term217 A s f b).
Proof. exact (eq_refl (term232 A f b s)). Qed.
Lemma lem7087624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7087625 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term233 A f b s) = (term234 A s f b).
Proof. exact (MK_COMB (@lem7087624) (@lem7087623 A s f b)). Qed.
Lemma lem7087626 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7087627 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term236 A f b x s) = (term237 A f b x s).
Proof. exact (MK_COMB (@lem7087625 A s f b) (@lem7087626 A x s)). Qed.
Lemma lem7087628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7087629 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term238 A f b x s) = (term239 A f b x s).
Proof. exact (MK_COMB (@lem7087628) (@lem7087627 A f b x s)). Qed.
Lemma lem7087630 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term240 A f b x s) = (term241 A x s f b).
Proof. exact (eq_refl (term240 A f b x s)). Qed.
Lemma lem7087631 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term242 A f b x s) = (term243 A x s f b).
Proof. exact (MK_COMB (@lem7087629 A f b x s) (@lem7087630 A x s f b)). Qed.
Lemma lem7087632 {A : Type'} (x : A) (f : A -> real) (b : real) : (term244 A f b x) = (term245 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7087631 A x s f b)). Qed.
Lemma lem7087633 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7087634 {A : Type'} (x : A) (f : A -> real) (b : real) : (term246 A f b x) = (term247 A x f b).
Proof. exact (MK_COMB (@lem7087633 A) (@lem7087632 A x f b)). Qed.
Lemma lem7087635 {A : Type'} (f : A -> real) (b : real) : (term248 A f b) = (term249 A f b).
Proof. exact (fun_ext (fun x : A => @lem7087634 A x f b)). Qed.
Lemma lem7087636 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7087637 {A : Type'} (f : A -> real) (b : real) : (term250 A f b) = (term251 A f b).
Proof. exact (MK_COMB (@lem7087636 A) (@lem7087635 A f b)). Qed.
Lemma lem7087638 {A : Type'} (f : A -> real) (b : real) : (term252 A f b) = (term253 A f b).
Proof. exact (MK_COMB (@lem7087622 A f b) (@lem7087637 A f b)). Qed.
Lemma lem7087639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7087640 {A : Type'} (f : A -> real) (b : real) : (term254 A f b) = (term255 A f b).
Proof. exact (MK_COMB (@lem7087639) (@lem7087638 A f b)). Qed.
Lemma lem7087641 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term232 A f b s) = (term217 A s f b).
Proof. exact (eq_refl (term232 A f b s)). Qed.
Lemma lem7087642 {A : Type'} (s : A -> Prop) : (term220 A s) = (term220 A s).
Proof. exact (eq_refl (term220 A s)). Qed.
Lemma lem7087643 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term256 A f b s) = (term221 A s f b).
Proof. exact (MK_COMB (@lem7087642 A s) (@lem7087641 A s f b)). Qed.
Lemma lem7087644 {A : Type'} (f : A -> real) (b : real) : (term257 A f b) = (term223 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7087643 A s f b)). Qed.
Lemma lem7087645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7087646 {A : Type'} (f : A -> real) (b : real) : (term258 A f b) = (term225 A f b).
Proof. exact (MK_COMB (@lem7087645 A) (@lem7087644 A f b)). Qed.
Lemma lem7087647 {A : Type'} (f : A -> real) (b : real) : (term226 A f b) = (term259 A f b).
Proof. exact (MK_COMB (@lem7087640 A f b) (@lem7087646 A f b)). Qed.
Lemma lem7087648 {A : Type'} (f : A -> real) (b : real) : term259 A f b.
Proof. exact (EQ_MP (@lem7087647 A f b) (@lem7087619 A f b)). Qed.
Lemma lem7087654 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7087655 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7087654 p q p' q'). Qed.
Lemma lem7087656 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7087655 p q p'). Qed.
Lemma lem7087657 {A : Type'} (f : A -> real) (b : real) : term263 A f b.
Proof. exact (@lem7087656 (term264 A f) (term265 A f b)). Qed.
Lemma lem7087658 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : term266 A f b p'.
Proof. exact (@lem7087657 A f b p'). Qed.
Lemma lem7087659 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : (term266 A f b p') = (term267 A f b p').
Proof. exact (eq_refl (term266 A f b p')). Qed.
Lemma lem7087660 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : term267 A f b p'.
Proof. exact (EQ_MP (@lem7087659 A f b p') (@lem7087658 A f b p')). Qed.
Lemma lem7087661 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term268 A f b p' q'.
Proof. exact (@lem7087660 A f b p' q'). Qed.
Lemma lem7087662 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : (term268 A f b p' q') = (term269 A f b p' q').
Proof. exact (eq_refl (term268 A f b p' q')). Qed.
Lemma lem7087663 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term269 A f b p' q'.
Proof. exact (EQ_MP (@lem7087662 A f b p' q') (@lem7087661 A f b p' q')). Qed.
Lemma lem7087671 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7087672 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7087671 p q p' q'). Qed.
Lemma lem7087673 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7087672 p q p'). Qed.
Lemma lem7087674 {A : Type'} (f : A -> real) (x : A) : term270 A f x.
Proof. exact (@lem7087673 (@IN A x (@EMPTY A)) (term271 A f x)). Qed.
Lemma lem7087675 {A : Type'} (f : A -> real) (x : A) (p' : Prop) : term272 A f x p'.
Proof. exact (@lem7087674 A f x p'). Qed.
Lemma lem7087676 {A : Type'} (f : A -> real) (x : A) (p' : Prop) : (term272 A f x p') = (term273 A f x p').
Proof. exact (eq_refl (term272 A f x p')). Qed.
Lemma lem7087677 {A : Type'} (f : A -> real) (x : A) (p' : Prop) : term273 A f x p'.
Proof. exact (EQ_MP (@lem7087676 A f x p') (@lem7087675 A f x p')). Qed.
Lemma lem7087678 {A : Type'} (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term274 A f x p' q'.
Proof. exact (@lem7087677 A f x p' q'). Qed.
Lemma lem7087679 {A : Type'} (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term274 A f x p' q') = (term275 A f x p' q').
Proof. exact (eq_refl (term274 A f x p' q')). Qed.
Lemma lem7087680 {A : Type'} (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term275 A f x p' q'.
Proof. exact (EQ_MP (@lem7087679 A f x p' q') (@lem7087678 A f x p' q')). Qed.
Lemma lem7087682 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7087536 A x (@lem7087535 A x)). Qed.
Lemma lem7087683 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7087682 A x). Qed.
Lemma lem7087684 {A : Type'} (f : A -> real) (x : A) (q' : Prop) : term276 A f x q'.
Proof. exact (@lem7087680 A f x False q'). Qed.
Lemma lem7087685 {A : Type'} (f : A -> real) (x : A) (q' : Prop) : term277 A f x q'.
Proof. exact (@lem7087684 A f x q' (@lem7087683 A x)). Qed.
Lemma lem7087689 {A : Type'} (f : A -> real) (x : A) : (term271 A f x) = (term271 A f x).
Proof. exact (eq_refl (term271 A f x)). Qed.
Lemma lem7087690 {A : Type'} (f : A -> real) (x : A) : term278 A f x.
Proof. exact (fun h0 : False => @lem7087689 A f x). Qed.
Lemma lem7087691 {A : Type'} (f : A -> real) (x : A) : term279 A f x.
Proof. exact (@lem7087685 A f x (term271 A f x)). Qed.
Lemma lem7087692 {A : Type'} (f : A -> real) (x : A) : (term280 A f x) = (term281 A f x).
Proof. exact (@lem7087691 A f x (@lem7087690 A f x)). Qed.
Lemma lem7087694 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7087695 {A : Type'} (f : A -> real) (x : A) : (term281 A f x) = True.
Proof. exact (@lem7087694 (term271 A f x)). Qed.
Lemma lem7087696 {A : Type'} (f : A -> real) (x : A) : (term280 A f x) = True.
Proof. exact (TRANS (@lem7087692 A f x) (@lem7087695 A f x)). Qed.
Lemma lem7087697 {A : Type'} (f : A -> real) : (term282 A f) = (term283 A).
Proof. exact (fun_ext (fun x : A => @lem7087696 A f x)). Qed.
Lemma lem7087698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7087699 {A : Type'} (f : A -> real) : (term264 A f) = (term284 A).
Proof. exact (MK_COMB (@lem7087698 A) (@lem7087697 A f)). Qed.
Lemma lem7087701 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7087702 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (@lem7087701 A t). Qed.
Lemma lem7087703 {A : Type'} : (term284 A) = True.
Proof. exact (@lem7087702 A True). Qed.
Lemma lem7087704 {A : Type'} (f : A -> real) : (term264 A f) = True.
Proof. exact (TRANS (@lem7087699 A f) (@lem7087703 A)). Qed.
Lemma lem7087705 {A : Type'} (f : A -> real) (b : real) (q' : Prop) : term286 A f b q'.
Proof. exact (@lem7087663 A f b True q'). Qed.
Lemma lem7087706 {A : Type'} (f : A -> real) (b : real) (q' : Prop) : term287 A f b q'.
Proof. exact (@lem7087705 A f b q' (@lem7087704 A f)). Qed.
Lemma lem7087715 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7087716 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7087715 p q p' q'). Qed.
Lemma lem7087717 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7087716 p q p'). Qed.
Lemma lem7087718 {A : Type'} (f : A -> real) (b : real) : term288 A f b.
Proof. exact (@lem7087717 (term289 A f b) (term290 A f b)). Qed.
Lemma lem7087719 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : term291 A f b p'.
Proof. exact (@lem7087718 A f b p'). Qed.
Lemma lem7087720 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : (term291 A f b p') = (term292 A f b p').
Proof. exact (eq_refl (term291 A f b p')). Qed.
Lemma lem7087721 {A : Type'} (f : A -> real) (b : real) (p' : Prop) : term292 A f b p'.
Proof. exact (EQ_MP (@lem7087720 A f b p') (@lem7087719 A f b p')). Qed.
Lemma lem7087722 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term293 A f b p' q'.
Proof. exact (@lem7087721 A f b p' q'). Qed.
Lemma lem7087723 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : (term293 A f b p' q') = (term294 A f b p' q').
Proof. exact (eq_refl (term293 A f b p' q')). Qed.
Lemma lem7087724 {A : Type'} (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term294 A f b p' q'.
Proof. exact (EQ_MP (@lem7087723 A f b p' q') (@lem7087722 A f b p' q')). Qed.
Lemma lem7087726 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term10.
Proof. exact (EQ_MP (@lem7087557 _131483 f) (@lem7087556 _131483 f)). Qed.
Lemma lem7087727 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term10.
Proof. exact (@lem7087726 A f). Qed.
Lemma lem7087728 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7087729 {A : Type'} (f : A -> real) : (term295 A f) = term296.
Proof. exact (MK_COMB (@lem7087728) (@lem7087727 A f)). Qed.
Lemma lem7087730 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7087731 {A : Type'} (f : A -> real) (b : real) : (term289 A f b) = (term8 b).
Proof. exact (MK_COMB (@lem7087729 A f) (@lem7087730 b)). Qed.
Lemma lem7087732 {A : Type'} (f : A -> real) (b : real) (q' : Prop) : term297 A f b q'.
Proof. exact (@lem7087724 A f b (term8 b) q'). Qed.
Lemma lem7087733 {A : Type'} (f : A -> real) (b : real) (q' : Prop) : term298 A f b q'.
Proof. exact (@lem7087732 A f b q' (@lem7087731 A f b)). Qed.
Lemma lem7087744 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7087745 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7087744 p q p' q'). Qed.
Lemma lem7087746 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7087745 p q p'). Qed.
Lemma lem7087747 {A : Type'} (f : A -> real) (x : A) (b : real) : term299 A f x b.
Proof. exact (@lem7087746 (@IN A x (@EMPTY A)) (term300 A f x b)). Qed.
Lemma lem7087748 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) : term301 A f x b p'.
Proof. exact (@lem7087747 A f x b p'). Qed.
Lemma lem7087749 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) : (term301 A f x b p') = (term302 A f x b p').
Proof. exact (eq_refl (term301 A f x b p')). Qed.
Lemma lem7087750 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) : term302 A f x b p'.
Proof. exact (EQ_MP (@lem7087749 A f x b p') (@lem7087748 A f x b p')). Qed.
Lemma lem7087751 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : term303 A f x b p' q'.
Proof. exact (@lem7087750 A f x b p' q'). Qed.
Lemma lem7087752 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : (term303 A f x b p' q') = (term304 A f x b p' q').
Proof. exact (eq_refl (term303 A f x b p' q')). Qed.
Lemma lem7087753 {A : Type'} (f : A -> real) (x : A) (b : real) (p' : Prop) (q' : Prop) : term304 A f x b p' q'.
Proof. exact (EQ_MP (@lem7087752 A f x b p' q') (@lem7087751 A f x b p' q')). Qed.
Lemma lem7087755 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7087536 A x (@lem7087535 A x)). Qed.
Lemma lem7087756 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7087755 A x). Qed.
Lemma lem7087757 {A : Type'} (f : A -> real) (x : A) (b : real) (q' : Prop) : term305 A f x b q'.
Proof. exact (@lem7087753 A f x b False q'). Qed.
Lemma lem7087758 {A : Type'} (f : A -> real) (x : A) (b : real) (q' : Prop) : term306 A f x b q'.
Proof. exact (@lem7087757 A f x b q' (@lem7087756 A x)). Qed.
Lemma lem7087762 {A : Type'} (f : A -> real) (x : A) (b : real) : (term300 A f x b) = (term300 A f x b).
Proof. exact (eq_refl (term300 A f x b)). Qed.
Lemma lem7087763 {A : Type'} (f : A -> real) (x : A) (b : real) : term307 A f x b.
Proof. exact (fun h0 : False => @lem7087762 A f x b). Qed.
Lemma lem7087764 {A : Type'} (f : A -> real) (x : A) (b : real) : term308 A f x b.
Proof. exact (@lem7087758 A f x b (term300 A f x b)). Qed.
Lemma lem7087765 {A : Type'} (f : A -> real) (x : A) (b : real) : (term309 A f x b) = (term310 A f x b).
Proof. exact (@lem7087764 A f x b (@lem7087763 A f x b)). Qed.
Lemma lem7087767 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7087768 {A : Type'} (f : A -> real) (x : A) (b : real) : (term310 A f x b) = True.
Proof. exact (@lem7087767 (term300 A f x b)). Qed.
Lemma lem7087771 {A : Type'} (f : A -> real) (x : A) (b : real) : (term309 A f x b) = True.
Proof. exact (TRANS (@lem7087765 A f x b) (@lem7087768 A f x b)). Qed.
Lemma lem7087772 {A : Type'} (f : A -> real) (b : real) : (term311 A f b) = (term283 A).
Proof. exact (fun_ext (fun x : A => @lem7087771 A f x b)). Qed.
Lemma lem7087775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7087776 {A : Type'} (f : A -> real) (b : real) : (term290 A f b) = (term284 A).
Proof. exact (MK_COMB (@lem7087775 A) (@lem7087772 A f b)). Qed.
Lemma lem7087778 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7087779 {A : Type'} (t : Prop) : (term285 A t) = t.
Proof. exact (@lem7087778 A t). Qed.
Lemma lem7087780 {A : Type'} : (term284 A) = True.
Proof. exact (@lem7087779 A True). Qed.
Lemma lem7087783 {A : Type'} (f : A -> real) (b : real) : (term290 A f b) = True.
Proof. exact (TRANS (@lem7087776 A f b) (@lem7087780 A)). Qed.
Lemma lem7087784 {A : Type'} (f : A -> real) (b : real) : term312 A f b.
Proof. exact (fun h0 : term8 b => @lem7087783 A f b). Qed.
Lemma lem7087785 {A : Type'} (f : A -> real) (b : real) : term313 A f b.
Proof. exact (@lem7087733 A f b True). Qed.
Lemma lem7087786 {A : Type'} (f : A -> real) (b : real) : (term265 A f b) = (term314 b).
Proof. exact (@lem7087785 A f b (@lem7087784 A f b)). Qed.
Lemma lem7087788 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7087789 (b : real) : (term314 b) = True.
Proof. exact (@lem7087788 (term8 b)). Qed.
Lemma lem7087792 {A : Type'} (f : A -> real) (b : real) : (term265 A f b) = True.
Proof. exact (TRANS (@lem7087786 A f b) (@lem7087789 b)). Qed.
Lemma lem7087793 {A : Type'} (f : A -> real) (b : real) : term315 A f b.
Proof. exact (fun h0 : True => @lem7087792 A f b). Qed.
Lemma lem7087794 {A : Type'} (f : A -> real) (b : real) : term316 A f b.
Proof. exact (@lem7087706 A f b True). Qed.
Lemma lem7087795 {A : Type'} (f : A -> real) (b : real) : (term229 A f b) = (True -> True).
Proof. exact (@lem7087794 A f b (@lem7087793 A f b)). Qed.
Lemma lem7087797 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7087798 : (True -> True) = True.
Proof. exact (@lem7087797 True). Qed.
Lemma lem7087799 {A : Type'} (f : A -> real) (b : real) : (term229 A f b) = True.
Proof. exact (TRANS (@lem7087795 A f b) (@lem7087798)). Qed.
Lemma lem7087800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7087801 {A : Type'} (f : A -> real) (b : real) : (term231 A f b) = (and True).
Proof. exact (MK_COMB (@lem7087800) (@lem7087799 A f b)). Qed.
Lemma lem7087813 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7087814 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7087813 p q p' q'). Qed.
Lemma lem7087815 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7087814 p q p'). Qed.
Lemma lem7087816 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term317 A x s f b.
Proof. exact (@lem7087815 (term237 A f b x s) (term241 A x s f b)). Qed.
Lemma lem7087817 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term318 A x s f b p'.
Proof. exact (@lem7087816 A x s f b p'). Qed.
Lemma lem7087818 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : (term318 A x s f b p') = (term319 A x s f b p').
Proof. exact (eq_refl (term318 A x s f b p')). Qed.
Lemma lem7087819 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term319 A x s f b p'.
Proof. exact (EQ_MP (@lem7087818 A x s f b p') (@lem7087817 A x s f b p')). Qed.
Lemma lem7087820 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term320 A x s f b p' q'.
Proof. exact (@lem7087819 A x s f b p' q'). Qed.
Lemma lem7087821 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : (term320 A x s f b p' q') = (term321 A x s f b p' q').
Proof. exact (eq_refl (term320 A x s f b p' q')). Qed.
Lemma lem7087822 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term321 A x s f b p' q'.
Proof. exact (EQ_MP (@lem7087821 A x s f b p' q') (@lem7087820 A x s f b p' q')). Qed.
Lemma lem7088068 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term237 A f b x s) = (term237 A f b x s).
Proof. exact (eq_refl (term237 A f b x s)). Qed.
Lemma lem7088069 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term322 A f b x s q'.
Proof. exact (@lem7087822 A x s f b (term237 A f b x s) q'). Qed.
Lemma lem7088070 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (q' : Prop) : term323 A f b x s q'.
Proof. exact (@lem7088069 A f b x s q' (@lem7088068 A f b x s)). Qed.
Lemma lem7088071 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term237 A f b x s.
Proof. exact (h1). Qed.
Lemma lem7088072 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term235 A x s.
Proof. exact (proj2 (@lem7088071 A f b x s h1)). Qed.
Lemma lem7088073 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : @FINITE A s.
Proof. exact (proj2 (@lem7088072 A f b x s h1)). Qed.
Lemma lem7088074 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7088076 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term324 A x s.
Proof. exact (proj1 (@lem7088072 A f b x s h1)). Qed.
Lemma lem7088077 {A : Type'} (x : A) (s : A -> Prop) : term325 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem7088109 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7088110 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7088109 p q p' q'). Qed.
Lemma lem7088111 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7088110 p q p'). Qed.
Lemma lem7088112 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term326 A x s f b.
Proof. exact (@lem7088111 (term327 A x s f) (term328 A x s f b)). Qed.
Lemma lem7088113 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term329 A x s f b p'.
Proof. exact (@lem7088112 A x s f b p'). Qed.
Lemma lem7088114 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : (term329 A x s f b p') = (term330 A x s f b p').
Proof. exact (eq_refl (term329 A x s f b p')). Qed.
Lemma lem7088115 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term330 A x s f b p'.
Proof. exact (EQ_MP (@lem7088114 A x s f b p') (@lem7088113 A x s f b p')). Qed.
Lemma lem7088116 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term331 A x s f b p' q'.
Proof. exact (@lem7088115 A x s f b p' q'). Qed.
Lemma lem7088117 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : (term331 A x s f b p' q') = (term332 A x s f b p' q').
Proof. exact (eq_refl (term331 A x s f b p' q')). Qed.
Lemma lem7088118 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term332 A x s f b p' q'.
Proof. exact (EQ_MP (@lem7088117 A x s f b p' q') (@lem7088116 A x s f b p' q')). Qed.
Lemma lem7088126 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7088127 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7088126 p q p' q'). Qed.
Lemma lem7088128 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7088127 p q p'). Qed.
Lemma lem7088129 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : term333 A x s f x'.
Proof. exact (@lem7088128 (term187 A x' x s) (term271 A f x')). Qed.
Lemma lem7088130 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) : term334 A x s f x' p'.
Proof. exact (@lem7088129 A x s f x' p'). Qed.
Lemma lem7088131 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) : (term334 A x s f x' p') = (term335 A x s f x' p').
Proof. exact (eq_refl (term334 A x s f x' p')). Qed.
Lemma lem7088132 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) : term335 A x s f x' p'.
Proof. exact (EQ_MP (@lem7088131 A x s f x' p') (@lem7088130 A x s f x' p')). Qed.
Lemma lem7088133 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) (q' : Prop) : term336 A x s f x' p' q'.
Proof. exact (@lem7088132 A x s f x' p' q'). Qed.
Lemma lem7088134 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) (q' : Prop) : (term336 A x s f x' p' q') = (term337 A x s f x' p' q').
Proof. exact (eq_refl (term336 A x s f x' p' q')). Qed.
Lemma lem7088135 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (p' : Prop) (q' : Prop) : term337 A x s f x' p' q'.
Proof. exact (EQ_MP (@lem7088134 A x s f x' p' q') (@lem7088133 A x s f x' p' q')). Qed.
Lemma lem7088137 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A x y s) = (term188 A y x s).
Proof. exact (EQ_MP (@lem7087531 A y x s) (@lem7087530 A y x s)). Qed.
Lemma lem7088138 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A x y s) = (term188 A y x s).
Proof. exact (@lem7088137 A y x s). Qed.
Lemma lem7088139 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term187 A x' x s) = (term188 A x x' s).
Proof. exact (@lem7088138 A x x' s). Qed.
Lemma lem7088144 {A : Type'} (f : A -> real) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term338 A f x x' s q'.
Proof. exact (@lem7088135 A x s f x' (term188 A x x' s) q'). Qed.
Lemma lem7088145 {A : Type'} (f : A -> real) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term339 A f x x' s q'.
Proof. exact (@lem7088144 A f x x' s q' (@lem7088139 A x x' s)). Qed.
Lemma lem7088149 {A : Type'} (f : A -> real) (x' : A) : (term271 A f x') = (term271 A f x').
Proof. exact (eq_refl (term271 A f x')). Qed.
Lemma lem7088150 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : term340 A x s f x'.
Proof. exact (fun h0 : term188 A x x' s => @lem7088149 A f x'). Qed.
Lemma lem7088151 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : term341 A x s f x'.
Proof. exact (@lem7088145 A f x x' s (term271 A f x')). Qed.
Lemma lem7088152 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : (term342 A x s f x') = (term343 A x s f x').
Proof. exact (@lem7088151 A x s f x' (@lem7088150 A x s f x')). Qed.
Lemma lem7088184 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term344 A x s f) = (term345 A x s f).
Proof. exact (fun_ext (fun x' : A => @lem7088152 A x s f x')). Qed.
Lemma lem7088216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7088217 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term327 A x s f) = (term346 A x s f).
Proof. exact (MK_COMB (@lem7088216 A) (@lem7088184 A x s f)). Qed.
Lemma lem7088253 {A : Type'} (b : real) (x : A) (s : A -> Prop) (f : A -> real) (q' : Prop) : term347 A b x s f q'.
Proof. exact (@lem7088118 A x s f b (term346 A x s f) q'). Qed.
Lemma lem7088254 {A : Type'} (b : real) (x : A) (s : A -> Prop) (f : A -> real) (q' : Prop) : term348 A b x s f q'.
Proof. exact (@lem7088253 A b x s f q' (@lem7088217 A x s f)). Qed.
Lemma lem7088271 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7088272 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7088271 p q p' q'). Qed.
Lemma lem7088273 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7088272 p q p'). Qed.
Lemma lem7088274 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term349 A x s f b.
Proof. exact (@lem7088273 (term350 A x s f b) (term351 A x s f b)). Qed.
Lemma lem7088275 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term352 A x s f b p'.
Proof. exact (@lem7088274 A x s f b p'). Qed.
Lemma lem7088276 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : (term352 A x s f b p') = (term353 A x s f b p').
Proof. exact (eq_refl (term352 A x s f b p')). Qed.
Lemma lem7088277 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) : term353 A x s f b p'.
Proof. exact (EQ_MP (@lem7088276 A x s f b p') (@lem7088275 A x s f b p')). Qed.
Lemma lem7088278 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term354 A x s f b p' q'.
Proof. exact (@lem7088277 A x s f b p' q'). Qed.
Lemma lem7088279 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : (term354 A x s f b p' q') = (term355 A x s f b p' q').
Proof. exact (eq_refl (term354 A x s f b p' q')). Qed.
Lemma lem7088280 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (p' : Prop) (q' : Prop) : term355 A x s f b p' q'.
Proof. exact (EQ_MP (@lem7088279 A x s f b p' q') (@lem7088278 A x s f b p' q')). Qed.
Lemma lem7088282 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term198 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7087549 _131524 x f s h0). Qed.
Lemma lem7088283 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term198 A x s f.
Proof. exact (@lem7088282 A x s f). Qed.
Lemma lem7088285 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7088074 A s) (@lem7088073 A f b x s h1)). Qed.
Lemma lem7088286 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7088285 A f b x s h1)). Qed.
Lemma lem7088287 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7088286 A f b x s h1) (@lem0)). Qed.
Lemma lem7088288 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term199 A x s f) = (term200 A x s f).
Proof. exact (@lem7088283 A x s f (@lem7088287 A f b x s h1)). Qed.
Lemma lem7088290 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term356 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7088291 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term357 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7088290 _2963 g t e g' t' e'). Qed.
Lemma lem7088292 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term358 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7088291 _2963 g t e g' t'). Qed.
Lemma lem7088293 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term359 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7088292 _2963 g t e g'). Qed.
Lemma lem7088294 (g : Prop) (t : real) (e : real) : term360 g t e.
Proof. exact (@lem7088293 real g t e). Qed.
Lemma lem7088295 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term361 A x s f.
Proof. exact (@lem7088294 (@IN A x s) (@sum A s f) (term362 A x s f)). Qed.
Lemma lem7088296 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) : term363 A x s f g'.
Proof. exact (@lem7088295 A x s f g'). Qed.
Lemma lem7088297 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) : (term363 A x s f g') = (term364 A x s f g').
Proof. exact (eq_refl (term363 A x s f g')). Qed.
Lemma lem7088298 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) : term364 A x s f g'.
Proof. exact (EQ_MP (@lem7088297 A x s f g') (@lem7088296 A x s f g')). Qed.
Lemma lem7088299 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : term365 A x s f g' t'.
Proof. exact (@lem7088298 A x s f g' t'). Qed.
Lemma lem7088300 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : (term365 A x s f g' t') = (term366 A x s f g' t').
Proof. exact (eq_refl (term365 A x s f g' t')). Qed.
Lemma lem7088301 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : term366 A x s f g' t'.
Proof. exact (EQ_MP (@lem7088300 A x s f g' t') (@lem7088299 A x s f g' t')). Qed.
Lemma lem7088302 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term367 A x s f g' t' e'.
Proof. exact (@lem7088301 A x s f g' t' e'). Qed.
Lemma lem7088303 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : (term367 A x s f g' t' e') = (term368 A x s f g' t' e').
Proof. exact (eq_refl (term367 A x s f g' t' e')). Qed.
Lemma lem7088304 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term368 A x s f g' t' e'.
Proof. exact (EQ_MP (@lem7088303 A x s f g' t' e') (@lem7088302 A x s f g' t' e')). Qed.
Lemma lem7088306 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (@IN A x s) = False.
Proof. exact (@lem7088077 A x s (@lem7088076 A f b x s h1)). Qed.
Lemma lem7088307 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (t' : real) (e' : real) : term369 A x s f t' e'.
Proof. exact (@lem7088304 A x s f False t' e'). Qed.
Lemma lem7088308 {A : Type'} (t' : real) (e' : real) (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term370 A x s f t' e'.
Proof. exact (@lem7088307 A x s f t' e' (@lem7088306 A f b x s h1)). Qed.
Lemma lem7088312 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@sum A s f).
Proof. exact (eq_refl (@sum A s f)). Qed.
Lemma lem7088313 {A : Type'} (s : A -> Prop) (f : A -> real) : term371 A s f.
Proof. exact (fun h0 : False => @lem7088312 A s f). Qed.
Lemma lem7088314 {A : Type'} (e' : real) (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term372 A x s f e'.
Proof. exact (@lem7088308 A (@sum A s f) e' f b x s h1). Qed.
Lemma lem7088315 {A : Type'} (e' : real) (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term373 A x s f e'.
Proof. exact (@lem7088314 A e' f b x s h1 (@lem7088313 A s f)). Qed.
Lemma lem7088321 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term362 A x s f) = (term362 A x s f).
Proof. exact (eq_refl (term362 A x s f)). Qed.
Lemma lem7088322 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term374 A x s f.
Proof. exact (fun h0 : ~ False => @lem7088321 A x s f). Qed.
Lemma lem7088323 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term375 A x s f.
Proof. exact (@lem7088315 A (term362 A x s f) f b x s h1). Qed.
Lemma lem7088324 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term200 A x s f) = (term376 A x s f).
Proof. exact (@lem7088323 A f b x s h1 (@lem7088322 A x s f)). Qed.
Lemma lem7088326 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7088327 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7088326 real t1 t2). Qed.
Lemma lem7088328 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term376 A x s f) = (term362 A x s f).
Proof. exact (@lem7088327 (@sum A s f) (term362 A x s f)). Qed.
Lemma lem7088329 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term200 A x s f) = (term362 A x s f).
Proof. exact (TRANS (@lem7088324 A f b x s h1) (@lem7088328 A x s f)). Qed.
Lemma lem7088330 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term199 A x s f) = (term362 A x s f).
Proof. exact (TRANS (@lem7088288 A f b x s h1) (@lem7088329 A f b x s h1)). Qed.
Lemma lem7088331 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7088332 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term377 A x s f) = (term378 A x s f).
Proof. exact (MK_COMB (@lem7088331) (@lem7088330 A f b x s h1)). Qed.
Lemma lem7088333 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7088334 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term350 A x s f b) = (term379 A x s f b).
Proof. exact (MK_COMB (@lem7088332 A f b x s h1) (@lem7088333 b)). Qed.
Lemma lem7088335 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (q' : Prop) : term380 A x s f b q'.
Proof. exact (@lem7088280 A x s f b (term379 A x s f b) q'). Qed.
Lemma lem7088336 {A : Type'} (q' : Prop) (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term381 A x s f b q'.
Proof. exact (@lem7088335 A x s f b q' (@lem7088334 A f b x s h1)). Qed.
Lemma lem7088347 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term260 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7088348 (p : Prop) (q : Prop) (p' : Prop) : term261 p q p'.
Proof. exact (fun q' : Prop => @lem7088347 p q p' q'). Qed.
Lemma lem7088349 (p : Prop) (q : Prop) : term262 p q.
Proof. exact (fun p' : Prop => @lem7088348 p q p'). Qed.
Lemma lem7088350 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : term382 A x s f x' b.
Proof. exact (@lem7088349 (term187 A x' x s) (term300 A f x' b)). Qed.
Lemma lem7088351 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) : term383 A x s f x' b p'.
Proof. exact (@lem7088350 A x s f x' b p'). Qed.
Lemma lem7088352 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) : (term383 A x s f x' b p') = (term384 A x s f x' b p').
Proof. exact (eq_refl (term383 A x s f x' b p')). Qed.
Lemma lem7088353 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) : term384 A x s f x' b p'.
Proof. exact (EQ_MP (@lem7088352 A x s f x' b p') (@lem7088351 A x s f x' b p')). Qed.
Lemma lem7088354 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) (q' : Prop) : term385 A x s f x' b p' q'.
Proof. exact (@lem7088353 A x s f x' b p' q'). Qed.
Lemma lem7088355 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) (q' : Prop) : (term385 A x s f x' b p' q') = (term386 A x s f x' b p' q').
Proof. exact (eq_refl (term385 A x s f x' b p' q')). Qed.
Lemma lem7088356 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (p' : Prop) (q' : Prop) : term386 A x s f x' b p' q'.
Proof. exact (EQ_MP (@lem7088355 A x s f x' b p' q') (@lem7088354 A x s f x' b p' q')). Qed.
Lemma lem7088358 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A x y s) = (term188 A y x s).
Proof. exact (EQ_MP (@lem7087531 A y x s) (@lem7087530 A y x s)). Qed.
Lemma lem7088359 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term187 A x y s) = (term188 A y x s).
Proof. exact (@lem7088358 A y x s). Qed.
Lemma lem7088360 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term187 A x' x s) = (term188 A x x' s).
Proof. exact (@lem7088359 A x x' s). Qed.
Lemma lem7088365 {A : Type'} (f : A -> real) (b : real) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term387 A f b x x' s q'.
Proof. exact (@lem7088356 A x s f x' b (term188 A x x' s) q'). Qed.
Lemma lem7088366 {A : Type'} (f : A -> real) (b : real) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term388 A f b x x' s q'.
Proof. exact (@lem7088365 A f b x x' s q' (@lem7088360 A x x' s)). Qed.
Lemma lem7088502 {A : Type'} (f : A -> real) (x' : A) (b : real) : (term300 A f x' b) = (term300 A f x' b).
Proof. exact (eq_refl (term300 A f x' b)). Qed.
Lemma lem7088503 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : term389 A x s f x' b.
Proof. exact (fun h0 : term188 A x x' s => @lem7088502 A f x' b). Qed.
Lemma lem7088504 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : term390 A x s f x' b.
Proof. exact (@lem7088366 A f b x x' s (term300 A f x' b)). Qed.
Lemma lem7088505 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term391 A x s f x' b) = (term392 A x s f x' b).
Proof. exact (@lem7088504 A x s f x' b (@lem7088503 A x s f x' b)). Qed.
Lemma lem7088801 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term393 A x s f b) = (term394 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7088505 A x s f x' b)). Qed.
Lemma lem7089097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7089098 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term351 A x s f b) = (term395 A x s f b).
Proof. exact (MK_COMB (@lem7089097 A) (@lem7088801 A x s f b)). Qed.
Lemma lem7089398 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term396 A x s f b.
Proof. exact (fun h0 : term379 A x s f b => @lem7089098 A x s f b). Qed.
Lemma lem7089399 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term397 A x s f b.
Proof. exact (@lem7088336 A (term395 A x s f b) f b x s h1). Qed.
Lemma lem7089400 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term328 A x s f b) = (term398 A x s f b).
Proof. exact (@lem7089399 A f b x s h1 (@lem7089398 A x s f b)). Qed.
Lemma lem7090022 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : term399 A x s f b.
Proof. exact (fun h0 : term346 A x s f => @lem7089400 A f b x s h1). Qed.
Lemma lem7090023 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term400 A x s f b.
Proof. exact (@lem7088254 A b x s f (term398 A x s f b)). Qed.
Lemma lem7090024 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term237 A f b x s) : (term241 A x s f b) = (term401 A x s f b).
Proof. exact (@lem7090023 A x s f b (@lem7090022 A f b x s h1)). Qed.
Lemma lem7091098 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term402 A x s f b.
Proof. exact (fun h0 : term237 A f b x s => @lem7090024 A f b x s h0). Qed.
Lemma lem7091099 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term403 A x s f b.
Proof. exact (@lem7088070 A f b x s (term401 A x s f b)). Qed.
Lemma lem7091100 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term243 A x s f b) = (term404 A x s f b).
Proof. exact (@lem7091099 A x s f b (@lem7091098 A x s f b)). Qed.
Lemma lem7093008 {A : Type'} (x : A) (f : A -> real) (b : real) : (term245 A x f b) = (term405 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7091100 A x s f b)). Qed.
Lemma lem7094916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7094917 {A : Type'} (x : A) (f : A -> real) (b : real) : (term247 A x f b) = (term406 A x f b).
Proof. exact (MK_COMB (@lem7094916 A) (@lem7093008 A x f b)). Qed.
Lemma lem7096829 {A : Type'} (f : A -> real) (b : real) : (term249 A f b) = (term407 A f b).
Proof. exact (fun_ext (fun x : A => @lem7094917 A x f b)). Qed.
Lemma lem7098741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7098742 {A : Type'} (f : A -> real) (b : real) : (term251 A f b) = (term408 A f b).
Proof. exact (MK_COMB (@lem7098741 A) (@lem7096829 A f b)). Qed.
Lemma lem7100658 {A : Type'} (f : A -> real) (b : real) : (term253 A f b) = (term409 A f b).
Proof. exact (MK_COMB (@lem7087801 A f b) (@lem7098742 A f b)). Qed.
Lemma lem7100660 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7100661 {A : Type'} (f : A -> real) (b : real) : (term409 A f b) = (term408 A f b).
Proof. exact (@lem7100660 (term408 A f b)). Qed.
Lemma lem7102577 {A : Type'} (f : A -> real) (b : real) : (term253 A f b) = (term408 A f b).
Proof. exact (TRANS (@lem7100658 A f b) (@lem7100661 A f b)). Qed.
Lemma lem7102578 {A : Type'} (f : A -> real) (b : real) : (term408 A f b) = (term253 A f b).
Proof. exact (SYM (@lem7102577 A f b)). Qed.
Lemma lem7102580 (p : Prop) : p = (term410 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7102581 {A : Type'} (f : A -> real) (b : real) : (term408 A f b) = (term411 A f b).
Proof. exact (@lem7102580 (term408 A f b)). Qed.
Lemma lem7102582 {A : Type'} (f : A -> real) (b : real) : (term411 A f b) = (term408 A f b).
Proof. exact (SYM (@lem7102581 A f b)). Qed.
Lemma lem7102583 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term412 A f b.
Proof. exact (h1). Qed.
Lemma lem7102584 {A : Type'} : term178 A.
Proof. exact (@lem7087520 A). Qed.
Lemma lem7102588 {A : Type'} (f : A -> real) (b : real) (h1 : term413 A f b) : term413 A f b.
Proof. exact (h1). Qed.
Lemma lem7102589 {A : Type'} (f : A -> real) (b : real) : term414 A f b.
Proof. exact (fun h0 : term413 A f b => @lem7102588 A f b h0). Qed.
Lemma lem7102590 {A : Type'} (f : A -> real) (b : real) (h1 : term414 A f b) : term414 A f b.
Proof. exact (h1). Qed.
Lemma lem7102591 {A : Type'} (f : A -> real) (b : real) (h1 : term413 A f b) : term413 A f b.
Proof. exact (h1). Qed.
Lemma lem7102592 {A : Type'} (f : A -> real) (b : real) (h1 : term413 A f b) (h2 : term414 A f b) : term413 A f b.
Proof. exact (@lem7102590 A f b h2 (@lem7102591 A f b h1)). Qed.
Lemma lem7102593 {A : Type'} (f : A -> real) (b : real) (h1 : term413 A f b) : term415 A f b.
Proof. exact (fun h0 : term414 A f b => @lem7102592 A f b h1 h0). Qed.
Lemma lem7102594 {A : Type'} (f : A -> real) (b : real) (h1 : term414 A f b) : term414 A f b.
Proof. exact (h1). Qed.
Lemma lem7102595 {A : Type'} (f : A -> real) (b : real) (h1 : term413 A f b) (h2 : term414 A f b) : term413 A f b.
Proof. exact (@lem7102593 A f b h1 (@lem7102594 A f b h2)). Qed.
Lemma lem7102596 {A : Type'} (f : A -> real) (b : real) (h1 : term414 A f b) : term414 A f b.
Proof. exact (fun h0 : term413 A f b => @lem7102595 A f b h0 h1). Qed.
Lemma lem7102597 {A : Type'} (f : A -> real) (b : real) : term416 A f b.
Proof. exact (fun h0 : term414 A f b => @lem7102596 A f b h0). Qed.
Lemma lem7102600 {A : Type'} (f : A -> real) (b : real) : term414 A f b.
Proof. exact (@lem7102597 A f b (@lem7102589 A f b)). Qed.
Lemma lem7102601 {A : Type'} (f : A -> real) (b : real) : term414 A f b.
Proof. exact (@lem7102600 A f b). Qed.
Lemma lem7102685 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7102686 {A : Type'} : (term417 A) = (term418 A).
Proof. exact (@lem7102685 (term178 A)). Qed.
Lemma lem7102703 : term419 = term419.
Proof. exact (eq_refl term419). Qed.
Lemma lem7102704 {A : Type'} : (term420 A) = (term421 A).
Proof. exact (MK_COMB (@lem7102703) (@lem7102686 A)). Qed.
Lemma lem7102707 {A : Type'} (f : A -> real) (b : real) : (term422 A f b) = (term422 A f b).
Proof. exact (eq_refl (term422 A f b)). Qed.
Lemma lem7102708 {A : Type'} (f : A -> real) (b : real) : (term413 A f b) = (term423 A f b).
Proof. exact (MK_COMB (@lem7102707 A f b) (@lem7102704 A)). Qed.
Lemma lem7102711 {A : Type'} (b : real) : (term424 A b) = (term425 A b).
Proof. exact (fun_ext (fun f : A -> real => @lem7102708 A f b)). Qed.
Lemma lem7102712 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7102713 {A : Type'} (b : real) : (term426 A b) = (term427 A b).
Proof. exact (MK_COMB (@lem7102712 A) (@lem7102711 A b)). Qed.
Lemma lem7102718 {A : Type'} : (term428 A) = (term429 A).
Proof. exact (fun_ext (fun b : real => @lem7102713 A b)). Qed.
Lemma lem7102719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7102728 {A : Type'} : (term430 A) = (term431 A).
Proof. exact (MK_COMB (@lem7102719) (@lem7102718 A)). Qed.
Lemma lem7102729 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term432 A s f).
Proof. exact (eq_refl (term432 A s f)). Qed.
Lemma lem7102734 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term433 A s f x) = (term433 A s f x).
Proof. exact (eq_refl (term433 A s f x)). Qed.
Lemma lem7102735 {A : Type'} (s : A -> Prop) (f : A -> real) : (term434 A s f) = (term434 A s f).
Proof. exact (fun_ext (fun x : A => @lem7102734 A s f x)). Qed.
Lemma lem7102736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102737 {A : Type'} (s : A -> Prop) (f : A -> real) : (term218 A s f) = (term218 A s f).
Proof. exact (MK_COMB (@lem7102736 A) (@lem7102735 A s f)). Qed.
Lemma lem7102738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102739 {A : Type'} (s : A -> Prop) (f : A -> real) : (term435 A s f) = (term435 A s f).
Proof. exact (MK_COMB (@lem7102738) (@lem7102737 A s f)). Qed.
Lemma lem7102740 {A : Type'} (s : A -> Prop) (f : A -> real) : (term436 A s f) = (term436 A s f).
Proof. exact (MK_COMB (@lem7102739 A s f) (@lem7102729 A s f)). Qed.
Lemma lem7102741 {A : Type'} (f : A -> real) : (term437 A f) = (term437 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7102740 A s f)). Qed.
Lemma lem7102742 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7102743 {A : Type'} (f : A -> real) : (term438 A f) = (term438 A f).
Proof. exact (MK_COMB (@lem7102742 A) (@lem7102741 A f)). Qed.
Lemma lem7102744 {A : Type'} : (term439 A) = (term439 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7102743 A f)). Qed.
Lemma lem7102745 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7102746 {A : Type'} : (term178 A) = (term178 A).
Proof. exact (MK_COMB (@lem7102745 A) (@lem7102744 A)). Qed.
Lemma lem7102747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7102748 {A : Type'} : (term418 A) = (term418 A).
Proof. exact (MK_COMB (@lem7102747) (@lem7102746 A)). Qed.
Lemma lem7102765 (x : real) (y : real) (b : real) : (term170 x y b) = (term170 x y b).
Proof. exact (eq_refl (term170 x y b)). Qed.
Lemma lem7102766 (x : real) (y : real) : (term440 x y) = (term440 x y).
Proof. exact (fun_ext (fun b : real => @lem7102765 x y b)). Qed.
Lemma lem7102767 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7102768 (x : real) (y : real) : (term179 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem7102767) (@lem7102766 x y)). Qed.
Lemma lem7102769 (x : real) : (term441 x) = (term441 x).
Proof. exact (fun_ext (fun y : real => @lem7102768 x y)). Qed.
Lemma lem7102770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7102771 (x : real) : (term180 x) = (term180 x).
Proof. exact (MK_COMB (@lem7102770) (@lem7102769 x)). Qed.
Lemma lem7102772 : term442 = term442.
Proof. exact (fun_ext (fun x : real => @lem7102771 x)). Qed.
Lemma lem7102773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7102774 : term181 = term181.
Proof. exact (MK_COMB (@lem7102773) (@lem7102772)). Qed.
Lemma lem7102775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102776 : term419 = term419.
Proof. exact (MK_COMB (@lem7102775) (@lem7102774)). Qed.
Lemma lem7102777 {A : Type'} : (term421 A) = (term421 A).
Proof. exact (MK_COMB (@lem7102776) (@lem7102748 A)). Qed.
Lemma lem7102786 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term392 A x s f x' b) = (term392 A x s f x' b).
Proof. exact (eq_refl (term392 A x s f x' b)). Qed.
Lemma lem7102787 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term394 A x s f b) = (term394 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7102786 A x s f x' b)). Qed.
Lemma lem7102788 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102789 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term395 A x s f b) = (term395 A x s f b).
Proof. exact (MK_COMB (@lem7102788 A) (@lem7102787 A x s f b)). Qed.
Lemma lem7102792 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term443 A x s f b) = (term443 A x s f b).
Proof. exact (eq_refl (term443 A x s f b)). Qed.
Lemma lem7102793 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term398 A x s f b) = (term398 A x s f b).
Proof. exact (MK_COMB (@lem7102792 A x s f b) (@lem7102789 A x s f b)). Qed.
Lemma lem7102802 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : (term343 A x s f x') = (term343 A x s f x').
Proof. exact (eq_refl (term343 A x s f x')). Qed.
Lemma lem7102803 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term345 A x s f) = (term345 A x s f).
Proof. exact (fun_ext (fun x' : A => @lem7102802 A x s f x')). Qed.
Lemma lem7102804 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102805 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term346 A x s f) = (term346 A x s f).
Proof. exact (MK_COMB (@lem7102804 A) (@lem7102803 A x s f)). Qed.
Lemma lem7102806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102807 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term444 A x s f) = (term444 A x s f).
Proof. exact (MK_COMB (@lem7102806) (@lem7102805 A x s f)). Qed.
Lemma lem7102808 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term401 A x s f b) = (term401 A x s f b).
Proof. exact (MK_COMB (@lem7102807 A x s f) (@lem7102793 A x s f b)). Qed.
Lemma lem7102815 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7102820 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term445 A s f x b) = (term445 A s f x b).
Proof. exact (eq_refl (term445 A s f x b)). Qed.
Lemma lem7102821 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term446 A s f b) = (term446 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7102820 A s f x b)). Qed.
Lemma lem7102822 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102823 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term215 A s f b) = (term215 A s f b).
Proof. exact (MK_COMB (@lem7102822 A) (@lem7102821 A s f b)). Qed.
Lemma lem7102826 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term447 A s f b) = (term447 A s f b).
Proof. exact (eq_refl (term447 A s f b)). Qed.
Lemma lem7102827 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term448 A s f b) = (term448 A s f b).
Proof. exact (MK_COMB (@lem7102826 A s f b) (@lem7102823 A s f b)). Qed.
Lemma lem7102832 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term433 A s f x) = (term433 A s f x).
Proof. exact (eq_refl (term433 A s f x)). Qed.
Lemma lem7102833 {A : Type'} (s : A -> Prop) (f : A -> real) : (term434 A s f) = (term434 A s f).
Proof. exact (fun_ext (fun x : A => @lem7102832 A s f x)). Qed.
Lemma lem7102834 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102835 {A : Type'} (s : A -> Prop) (f : A -> real) : (term218 A s f) = (term218 A s f).
Proof. exact (MK_COMB (@lem7102834 A) (@lem7102833 A s f)). Qed.
Lemma lem7102836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102837 {A : Type'} (s : A -> Prop) (f : A -> real) : (term435 A s f) = (term435 A s f).
Proof. exact (MK_COMB (@lem7102836) (@lem7102835 A s f)). Qed.
Lemma lem7102838 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term217 A s f b) = (term217 A s f b).
Proof. exact (MK_COMB (@lem7102837 A s f) (@lem7102827 A s f b)). Qed.
Lemma lem7102839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7102840 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term234 A s f b) = (term234 A s f b).
Proof. exact (MK_COMB (@lem7102839) (@lem7102838 A s f b)). Qed.
Lemma lem7102841 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term237 A f b x s) = (term237 A f b x s).
Proof. exact (MK_COMB (@lem7102840 A s f b) (@lem7102815 A x s)). Qed.
Lemma lem7102842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102843 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term239 A f b x s) = (term239 A f b x s).
Proof. exact (MK_COMB (@lem7102842) (@lem7102841 A f b x s)). Qed.
Lemma lem7102844 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term404 A x s f b) = (term404 A x s f b).
Proof. exact (MK_COMB (@lem7102843 A f b x s) (@lem7102808 A x s f b)). Qed.
Lemma lem7102845 {A : Type'} (x : A) (f : A -> real) (b : real) : (term405 A x f b) = (term405 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7102844 A x s f b)). Qed.
Lemma lem7102846 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7102847 {A : Type'} (x : A) (f : A -> real) (b : real) : (term406 A x f b) = (term406 A x f b).
Proof. exact (MK_COMB (@lem7102846 A) (@lem7102845 A x f b)). Qed.
Lemma lem7102848 {A : Type'} (f : A -> real) (b : real) : (term407 A f b) = (term407 A f b).
Proof. exact (fun_ext (fun x : A => @lem7102847 A x f b)). Qed.
Lemma lem7102849 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7102850 {A : Type'} (f : A -> real) (b : real) : (term408 A f b) = (term408 A f b).
Proof. exact (MK_COMB (@lem7102849 A) (@lem7102848 A f b)). Qed.
Lemma lem7102851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7102852 {A : Type'} (f : A -> real) (b : real) : (term412 A f b) = (term412 A f b).
Proof. exact (MK_COMB (@lem7102851) (@lem7102850 A f b)). Qed.
Lemma lem7102853 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7102854 {A : Type'} (f : A -> real) (b : real) : (term422 A f b) = (term422 A f b).
Proof. exact (MK_COMB (@lem7102853) (@lem7102852 A f b)). Qed.
Lemma lem7102855 {A : Type'} (f : A -> real) (b : real) : (term423 A f b) = (term423 A f b).
Proof. exact (MK_COMB (@lem7102854 A f b) (@lem7102777 A)). Qed.
Lemma lem7102856 {A : Type'} (b : real) : (term425 A b) = (term425 A b).
Proof. exact (fun_ext (fun f : A -> real => @lem7102855 A f b)). Qed.
Lemma lem7102857 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7102858 {A : Type'} (b : real) : (term427 A b) = (term427 A b).
Proof. exact (MK_COMB (@lem7102857 A) (@lem7102856 A b)). Qed.
Lemma lem7102859 {A : Type'} : (term429 A) = (term429 A).
Proof. exact (fun_ext (fun b : real => @lem7102858 A b)). Qed.
Lemma lem7102860 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7102861 {A : Type'} : (term431 A) = (term431 A).
Proof. exact (MK_COMB (@lem7102860) (@lem7102859 A)). Qed.
Lemma lem7102990 {A : Type'} : (term430 A) = (term431 A).
Proof. exact (TRANS (@lem7102728 A) (@lem7102861 A)). Qed.
Lemma lem7102991 {A : Type'} : (term431 A) = (term430 A).
Proof. exact (SYM (@lem7102990 A)). Qed.
Lemma lem7102992 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term412 A f b.
Proof. exact (h1). Qed.
Lemma lem7102993 (h1 : term181) : term181.
Proof. exact (h1). Qed.
Lemma lem7102994 {A : Type'} (h1 : term178 A) : term178 A.
Proof. exact (h1). Qed.
Lemma lem7103001 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term449 A s f x) = (term450 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term271 A f x)). Qed.
Lemma lem7103002 {A : Type'} (P : A -> Prop) : (term451 A P) = (term452 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7103003 {A : Type'} (s : A -> Prop) (f : A -> real) : (term453 A s f) = (term454 A s f).
Proof. exact (@lem7103002 A (term434 A s f)). Qed.
Lemma lem7103004 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term455 A s f x) = (term433 A s f x).
Proof. exact (eq_refl (term455 A s f x)). Qed.
Lemma lem7103005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103006 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term456 A s f x) = (term449 A s f x).
Proof. exact (MK_COMB (@lem7103005) (@lem7103004 A s f x)). Qed.
Lemma lem7103007 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term456 A s f x) = (term450 A s f x).
Proof. exact (TRANS (@lem7103006 A s f x) (@lem7103001 A s f x)). Qed.
Lemma lem7103008 {A : Type'} (s : A -> Prop) (f : A -> real) : (term457 A s f) = (term458 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103007 A s f x)). Qed.
Lemma lem7103009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103010 {A : Type'} (s : A -> Prop) (f : A -> real) : (term454 A s f) = (term459 A s f).
Proof. exact (MK_COMB (@lem7103009 A) (@lem7103008 A s f)). Qed.
Lemma lem7103011 {A : Type'} (s : A -> Prop) (f : A -> real) : (term453 A s f) = (term459 A s f).
Proof. exact (TRANS (@lem7103003 A s f) (@lem7103010 A s f)). Qed.
Lemma lem7103019 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term445 A s f x b) = (term460 A s f x b).
Proof. exact (@lem17265 (@IN A x s) (term300 A f x b)). Qed.
Lemma lem7103020 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term446 A s f b) = (term461 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7103019 A s f x b)). Qed.
Lemma lem7103021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7103022 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term215 A s f b) = (term462 A s f b).
Proof. exact (MK_COMB (@lem7103021 A) (@lem7103020 A s f b)). Qed.
Lemma lem7103024 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term463 A s f b) = (term463 A s f b).
Proof. exact (eq_refl (term463 A s f b)). Qed.
Lemma lem7103025 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term464 A s f b) = (term465 A s f b).
Proof. exact (MK_COMB (@lem7103024 A s f b) (@lem7103022 A s f b)). Qed.
Lemma lem7103026 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term448 A s f b) = (term464 A s f b).
Proof. exact (@lem17265 (term219 A s f b) (term215 A s f b)). Qed.
Lemma lem7103027 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term448 A s f b) = (term465 A s f b).
Proof. exact (TRANS (@lem7103026 A s f b) (@lem7103025 A s f b)). Qed.
Lemma lem7103028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103029 {A : Type'} (s : A -> Prop) (f : A -> real) : (term466 A s f) = (term467 A s f).
Proof. exact (MK_COMB (@lem7103028) (@lem7103011 A s f)). Qed.
Lemma lem7103030 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term468 A s f b) = (term469 A s f b).
Proof. exact (MK_COMB (@lem7103029 A s f) (@lem7103027 A s f b)). Qed.
Lemma lem7103031 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term217 A s f b) = (term468 A s f b).
Proof. exact (@lem17265 (term218 A s f) (term448 A s f b)). Qed.
Lemma lem7103032 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term217 A s f b) = (term469 A s f b).
Proof. exact (TRANS (@lem7103031 A s f b) (@lem7103030 A s f b)). Qed.
Lemma lem7103037 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7103038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103039 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term234 A s f b) = (term470 A s f b).
Proof. exact (MK_COMB (@lem7103038) (@lem7103032 A s f b)). Qed.
Lemma lem7103040 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term237 A f b x s) = (term471 A f b x s).
Proof. exact (MK_COMB (@lem7103039 A s f b) (@lem7103037 A x s)). Qed.
Lemma lem7103047 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term472 A x x' s) = (term473 A x x' s).
Proof. exact (@lem17160 (x' = x) (@IN A x' s)). Qed.
Lemma lem7103048 {A : Type'} (f : A -> real) (x' : A) : (term271 A f x') = (term271 A f x').
Proof. exact (eq_refl (term271 A f x')). Qed.
Lemma lem7103049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103050 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term474 A x x' s) = (term475 A x x' s).
Proof. exact (MK_COMB (@lem7103049) (@lem7103047 A x x' s)). Qed.
Lemma lem7103051 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : (term476 A x s f x') = (term477 A x s f x').
Proof. exact (MK_COMB (@lem7103050 A x x' s) (@lem7103048 A f x')). Qed.
Lemma lem7103052 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : (term343 A x s f x') = (term476 A x s f x').
Proof. exact (@lem17265 (term188 A x x' s) (term271 A f x')). Qed.
Lemma lem7103053 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) : (term343 A x s f x') = (term477 A x s f x').
Proof. exact (TRANS (@lem7103052 A x s f x') (@lem7103051 A x s f x')). Qed.
Lemma lem7103054 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term345 A x s f) = (term478 A x s f).
Proof. exact (fun_ext (fun x' : A => @lem7103053 A x s f x')). Qed.
Lemma lem7103055 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7103056 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term346 A x s f) = (term479 A x s f).
Proof. exact (MK_COMB (@lem7103055 A) (@lem7103054 A x s f)). Qed.
Lemma lem7103068 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term480 A x s f x' b) = (term481 A x s f x' b).
Proof. exact (@lem17362 (term188 A x x' s) (term300 A f x' b)). Qed.
Lemma lem7103069 {A : Type'} (P : A -> Prop) : (term451 A P) = (term452 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7103070 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term482 A x s f b) = (term483 A x s f b).
Proof. exact (@lem7103069 A (term394 A x s f b)). Qed.
Lemma lem7103071 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term484 A x s f b x') = (term392 A x s f x' b).
Proof. exact (eq_refl (term484 A x s f b x')). Qed.
Lemma lem7103072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103073 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term485 A x s f b x') = (term480 A x s f x' b).
Proof. exact (MK_COMB (@lem7103072) (@lem7103071 A x s f x' b)). Qed.
Lemma lem7103074 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term485 A x s f b x') = (term481 A x s f x' b).
Proof. exact (TRANS (@lem7103073 A x s f x' b) (@lem7103068 A x s f x' b)). Qed.
Lemma lem7103075 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term486 A x s f b) = (term487 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103074 A x s f x' b)). Qed.
Lemma lem7103076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103077 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term483 A x s f b) = (term488 A x s f b).
Proof. exact (MK_COMB (@lem7103076 A) (@lem7103075 A x s f b)). Qed.
Lemma lem7103078 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term482 A x s f b) = (term488 A x s f b).
Proof. exact (TRANS (@lem7103070 A x s f b) (@lem7103077 A x s f b)). Qed.
Lemma lem7103080 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term489 A x s f b) = (term489 A x s f b).
Proof. exact (eq_refl (term489 A x s f b)). Qed.
Lemma lem7103081 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term490 A x s f b) = (term491 A x s f b).
Proof. exact (MK_COMB (@lem7103080 A x s f b) (@lem7103078 A x s f b)). Qed.
Lemma lem7103082 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term492 A x s f b) = (term490 A x s f b).
Proof. exact (@lem17362 (term379 A x s f b) (term395 A x s f b)). Qed.
Lemma lem7103083 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term492 A x s f b) = (term491 A x s f b).
Proof. exact (TRANS (@lem7103082 A x s f b) (@lem7103081 A x s f b)). Qed.
Lemma lem7103084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103085 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term493 A x s f) = (term494 A x s f).
Proof. exact (MK_COMB (@lem7103084) (@lem7103056 A x s f)). Qed.
Lemma lem7103086 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term495 A x s f b) = (term496 A x s f b).
Proof. exact (MK_COMB (@lem7103085 A x s f) (@lem7103083 A x s f b)). Qed.
Lemma lem7103087 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term497 A x s f b) = (term495 A x s f b).
Proof. exact (@lem17362 (term346 A x s f) (term398 A x s f b)). Qed.
Lemma lem7103088 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term497 A x s f b) = (term496 A x s f b).
Proof. exact (TRANS (@lem7103087 A x s f b) (@lem7103086 A x s f b)). Qed.
Lemma lem7103089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103090 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term498 A f b x s) = (term499 A f b x s).
Proof. exact (MK_COMB (@lem7103089) (@lem7103040 A f b x s)). Qed.
Lemma lem7103091 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term500 A x s f b) = (term501 A x s f b).
Proof. exact (MK_COMB (@lem7103090 A f b x s) (@lem7103088 A x s f b)). Qed.
Lemma lem7103092 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term502 A x s f b) = (term500 A x s f b).
Proof. exact (@lem17362 (term237 A f b x s) (term401 A x s f b)). Qed.
Lemma lem7103093 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term502 A x s f b) = (term501 A x s f b).
Proof. exact (TRANS (@lem7103092 A x s f b) (@lem7103091 A x s f b)). Qed.
Lemma lem7103094 {A : Type'} (P : type686 A) : (term503 A P) = (term504 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7103095 {A : Type'} (x : A) (f : A -> real) (b : real) : (term505 A x f b) = (term506 A x f b).
Proof. exact (@lem7103094 A (term405 A x f b)). Qed.
Lemma lem7103096 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term507 A x f b s) = (term404 A x s f b).
Proof. exact (eq_refl (term507 A x f b s)). Qed.
Lemma lem7103097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103098 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term508 A x f b s) = (term502 A x s f b).
Proof. exact (MK_COMB (@lem7103097) (@lem7103096 A x s f b)). Qed.
Lemma lem7103099 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term508 A x f b s) = (term501 A x s f b).
Proof. exact (TRANS (@lem7103098 A x s f b) (@lem7103093 A x s f b)). Qed.
Lemma lem7103100 {A : Type'} (x : A) (f : A -> real) (b : real) : (term509 A x f b) = (term510 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103099 A x s f b)). Qed.
Lemma lem7103101 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7103102 {A : Type'} (x : A) (f : A -> real) (b : real) : (term506 A x f b) = (term511 A x f b).
Proof. exact (MK_COMB (@lem7103101 A) (@lem7103100 A x f b)). Qed.
Lemma lem7103103 {A : Type'} (x : A) (f : A -> real) (b : real) : (term505 A x f b) = (term511 A x f b).
Proof. exact (TRANS (@lem7103095 A x f b) (@lem7103102 A x f b)). Qed.
Lemma lem7103104 {A : Type'} (P : A -> Prop) : (term451 A P) = (term452 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7103105 {A : Type'} (f : A -> real) (b : real) : (term412 A f b) = (term512 A f b).
Proof. exact (@lem7103104 A (term407 A f b)). Qed.
Lemma lem7103106 {A : Type'} (x : A) (f : A -> real) (b : real) : (term513 A f b x) = (term406 A x f b).
Proof. exact (eq_refl (term513 A f b x)). Qed.
Lemma lem7103107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103108 {A : Type'} (x : A) (f : A -> real) (b : real) : (term514 A f b x) = (term505 A x f b).
Proof. exact (MK_COMB (@lem7103107) (@lem7103106 A x f b)). Qed.
Lemma lem7103109 {A : Type'} (x : A) (f : A -> real) (b : real) : (term514 A f b x) = (term511 A x f b).
Proof. exact (TRANS (@lem7103108 A x f b) (@lem7103103 A x f b)). Qed.
Lemma lem7103110 {A : Type'} (f : A -> real) (b : real) : (term515 A f b) = (term516 A f b).
Proof. exact (fun_ext (fun x : A => @lem7103109 A x f b)). Qed.
Lemma lem7103111 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103112 {A : Type'} (f : A -> real) (b : real) : (term512 A f b) = (term517 A f b).
Proof. exact (MK_COMB (@lem7103111 A) (@lem7103110 A f b)). Qed.
Lemma lem7103113 {A : Type'} (f : A -> real) (b : real) : (term412 A f b) = (term517 A f b).
Proof. exact (TRANS (@lem7103105 A f b) (@lem7103112 A f b)). Qed.
Lemma lem7103360 {A : Type'} (P : A -> Prop) (Q : Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7103361 {A : Type'} (P : A -> Prop) (Q : Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (@lem7103360 A P Q). Qed.
Lemma lem7103362 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term520 A s f b) = (term521 A s f b).
Proof. exact (@lem7103361 A (term458 A s f) (term465 A s f b)). Qed.
Lemma lem7103363 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term522 A s f x) = (term450 A s f x).
Proof. exact (eq_refl (term522 A s f x)). Qed.
Lemma lem7103364 {A : Type'} (s : A -> Prop) (f : A -> real) : (term523 A s f) = (term458 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103363 A s f x)). Qed.
Lemma lem7103365 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103366 {A : Type'} (s : A -> Prop) (f : A -> real) : (term524 A s f) = (term459 A s f).
Proof. exact (MK_COMB (@lem7103365 A) (@lem7103364 A s f)). Qed.
Lemma lem7103367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103368 {A : Type'} (s : A -> Prop) (f : A -> real) : (term525 A s f) = (term467 A s f).
Proof. exact (MK_COMB (@lem7103367) (@lem7103366 A s f)). Qed.
Lemma lem7103369 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term465 A s f b) = (term465 A s f b).
Proof. exact (eq_refl (term465 A s f b)). Qed.
Lemma lem7103370 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term520 A s f b) = (term469 A s f b).
Proof. exact (MK_COMB (@lem7103368 A s f) (@lem7103369 A s f b)). Qed.
Lemma lem7103371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103372 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term526 A s f b) = (term527 A s f b).
Proof. exact (MK_COMB (@lem7103371) (@lem7103370 A s f b)). Qed.
Lemma lem7103373 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term522 A s f x) = (term450 A s f x).
Proof. exact (eq_refl (term522 A s f x)). Qed.
Lemma lem7103374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103375 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term528 A s f x) = (term529 A s f x).
Proof. exact (MK_COMB (@lem7103374) (@lem7103373 A s f x)). Qed.
Lemma lem7103376 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term465 A s f b) = (term465 A s f b).
Proof. exact (eq_refl (term465 A s f b)). Qed.
Lemma lem7103377 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term530 A x s f b) = (term531 A x s f b).
Proof. exact (MK_COMB (@lem7103375 A s f x) (@lem7103376 A s f b)). Qed.
Lemma lem7103378 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term532 A s f b) = (term533 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7103377 A x s f b)). Qed.
Lemma lem7103379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103380 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term521 A s f b) = (term534 A s f b).
Proof. exact (MK_COMB (@lem7103379 A) (@lem7103378 A s f b)). Qed.
Lemma lem7103381 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term520 A s f b) = (term521 A s f b)) = ((term469 A s f b) = (term534 A s f b)).
Proof. exact (MK_COMB (@lem7103372 A s f b) (@lem7103380 A s f b)). Qed.
Lemma lem7103382 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term469 A s f b) = (term534 A s f b).
Proof. exact (EQ_MP (@lem7103381 A s f b) (@lem7103362 A s f b)). Qed.
Lemma lem7103383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103384 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term470 A s f b) = (term535 A s f b).
Proof. exact (MK_COMB (@lem7103383) (@lem7103382 A s f b)). Qed.
Lemma lem7103385 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7103386 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term471 A f b x s) = (term536 A f b x s).
Proof. exact (MK_COMB (@lem7103384 A s f b) (@lem7103385 A x s)). Qed.
Lemma lem7103388 {A : Type'} (P : A -> Prop) (Q : Prop) : (term537 A P Q) = (term538 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7103389 {A : Type'} (P : A -> Prop) (Q : Prop) : (term537 A P Q) = (term538 A P Q).
Proof. exact (@lem7103388 A P Q). Qed.
Lemma lem7103390 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term539 A f b x s) = (term540 A f b x s).
Proof. exact (@lem7103389 A (term533 A s f b) (term235 A x s)). Qed.
Lemma lem7103391 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term541 A s f b x) = (term531 A x s f b).
Proof. exact (eq_refl (term541 A s f b x)). Qed.
Lemma lem7103392 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term542 A s f b) = (term533 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7103391 A x s f b)). Qed.
Lemma lem7103393 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103394 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term543 A s f b) = (term534 A s f b).
Proof. exact (MK_COMB (@lem7103393 A) (@lem7103392 A s f b)). Qed.
Lemma lem7103395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103396 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term544 A s f b) = (term535 A s f b).
Proof. exact (MK_COMB (@lem7103395) (@lem7103394 A s f b)). Qed.
Lemma lem7103397 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7103398 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term539 A f b x s) = (term536 A f b x s).
Proof. exact (MK_COMB (@lem7103396 A s f b) (@lem7103397 A x s)). Qed.
Lemma lem7103399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103400 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term545 A f b x s) = (term546 A f b x s).
Proof. exact (MK_COMB (@lem7103399) (@lem7103398 A f b x s)). Qed.
Lemma lem7103401 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term541 A s f b x') = (term531 A x' s f b).
Proof. exact (eq_refl (term541 A s f b x')). Qed.
Lemma lem7103402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103403 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term547 A s f b x') = (term548 A x' s f b).
Proof. exact (MK_COMB (@lem7103402) (@lem7103401 A x' s f b)). Qed.
Lemma lem7103404 {A : Type'} (x : A) (s : A -> Prop) : (term235 A x s) = (term235 A x s).
Proof. exact (eq_refl (term235 A x s)). Qed.
Lemma lem7103405 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term549 A f b x' x s) = (term550 A x' f b x s).
Proof. exact (MK_COMB (@lem7103403 A x' s f b) (@lem7103404 A x s)). Qed.
Lemma lem7103406 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term551 A f b x s) = (term552 A f b x s).
Proof. exact (fun_ext (fun x' : A => @lem7103405 A x' f b x s)). Qed.
Lemma lem7103407 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103408 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term540 A f b x s) = (term553 A f b x s).
Proof. exact (MK_COMB (@lem7103407 A) (@lem7103406 A f b x s)). Qed.
Lemma lem7103409 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : ((term539 A f b x s) = (term540 A f b x s)) = ((term536 A f b x s) = (term553 A f b x s)).
Proof. exact (MK_COMB (@lem7103400 A f b x s) (@lem7103408 A f b x s)). Qed.
Lemma lem7103410 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term536 A f b x s) = (term553 A f b x s).
Proof. exact (EQ_MP (@lem7103409 A f b x s) (@lem7103390 A f b x s)). Qed.
Lemma lem7103411 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term471 A f b x s) = (term553 A f b x s).
Proof. exact (TRANS (@lem7103386 A f b x s) (@lem7103410 A f b x s)). Qed.
Lemma lem7103412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103413 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term499 A f b x s) = (term554 A f b x s).
Proof. exact (MK_COMB (@lem7103412) (@lem7103411 A f b x s)). Qed.
Lemma lem7103415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7103416 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (@lem7103415 A P Q). Qed.
Lemma lem7103417 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term557 A x s f b) = (term558 A x s f b).
Proof. exact (@lem7103416 A (term379 A x s f b) (term487 A x s f b)). Qed.
Lemma lem7103418 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term559 A x s f b x') = (term481 A x s f x' b).
Proof. exact (eq_refl (term559 A x s f b x')). Qed.
Lemma lem7103419 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term560 A x s f b) = (term487 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103418 A x s f x' b)). Qed.
Lemma lem7103420 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103421 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term561 A x s f b) = (term488 A x s f b).
Proof. exact (MK_COMB (@lem7103420 A) (@lem7103419 A x s f b)). Qed.
Lemma lem7103422 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term489 A x s f b) = (term489 A x s f b).
Proof. exact (eq_refl (term489 A x s f b)). Qed.
Lemma lem7103423 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term557 A x s f b) = (term491 A x s f b).
Proof. exact (MK_COMB (@lem7103422 A x s f b) (@lem7103421 A x s f b)). Qed.
Lemma lem7103424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103425 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term562 A x s f b) = (term563 A x s f b).
Proof. exact (MK_COMB (@lem7103424) (@lem7103423 A x s f b)). Qed.
Lemma lem7103426 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term559 A x s f b x') = (term481 A x s f x' b).
Proof. exact (eq_refl (term559 A x s f b x')). Qed.
Lemma lem7103427 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term489 A x s f b) = (term489 A x s f b).
Proof. exact (eq_refl (term489 A x s f b)). Qed.
Lemma lem7103428 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term564 A x s f b x') = (term565 A x s f x' b).
Proof. exact (MK_COMB (@lem7103427 A x s f b) (@lem7103426 A x s f x' b)). Qed.
Lemma lem7103429 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term566 A x s f b) = (term567 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103428 A x s f x' b)). Qed.
Lemma lem7103430 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103431 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term558 A x s f b) = (term568 A x s f b).
Proof. exact (MK_COMB (@lem7103430 A) (@lem7103429 A x s f b)). Qed.
Lemma lem7103432 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : ((term557 A x s f b) = (term558 A x s f b)) = ((term491 A x s f b) = (term568 A x s f b)).
Proof. exact (MK_COMB (@lem7103425 A x s f b) (@lem7103431 A x s f b)). Qed.
Lemma lem7103433 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term491 A x s f b) = (term568 A x s f b).
Proof. exact (EQ_MP (@lem7103432 A x s f b) (@lem7103417 A x s f b)). Qed.
Lemma lem7103434 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term494 A x s f) = (term494 A x s f).
Proof. exact (eq_refl (term494 A x s f)). Qed.
Lemma lem7103435 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term496 A x s f b) = (term569 A x s f b).
Proof. exact (MK_COMB (@lem7103434 A x s f) (@lem7103433 A x s f b)). Qed.
Lemma lem7103437 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7103438 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (@lem7103437 A P Q). Qed.
Lemma lem7103439 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term570 A x s f b) = (term571 A x s f b).
Proof. exact (@lem7103438 A (term479 A x s f) (term567 A x s f b)). Qed.
Lemma lem7103440 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term572 A x s f b x') = (term565 A x s f x' b).
Proof. exact (eq_refl (term572 A x s f b x')). Qed.
Lemma lem7103441 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term573 A x s f b) = (term567 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103440 A x s f x' b)). Qed.
Lemma lem7103442 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103443 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term574 A x s f b) = (term568 A x s f b).
Proof. exact (MK_COMB (@lem7103442 A) (@lem7103441 A x s f b)). Qed.
Lemma lem7103444 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term494 A x s f) = (term494 A x s f).
Proof. exact (eq_refl (term494 A x s f)). Qed.
Lemma lem7103445 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term570 A x s f b) = (term569 A x s f b).
Proof. exact (MK_COMB (@lem7103444 A x s f) (@lem7103443 A x s f b)). Qed.
Lemma lem7103446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103447 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term575 A x s f b) = (term576 A x s f b).
Proof. exact (MK_COMB (@lem7103446) (@lem7103445 A x s f b)). Qed.
Lemma lem7103448 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term572 A x s f b x') = (term565 A x s f x' b).
Proof. exact (eq_refl (term572 A x s f b x')). Qed.
Lemma lem7103449 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term494 A x s f) = (term494 A x s f).
Proof. exact (eq_refl (term494 A x s f)). Qed.
Lemma lem7103450 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term577 A x s f b x') = (term578 A x s f x' b).
Proof. exact (MK_COMB (@lem7103449 A x s f) (@lem7103448 A x s f x' b)). Qed.
Lemma lem7103451 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term579 A x s f b) = (term580 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103450 A x s f x' b)). Qed.
Lemma lem7103452 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103453 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term571 A x s f b) = (term581 A x s f b).
Proof. exact (MK_COMB (@lem7103452 A) (@lem7103451 A x s f b)). Qed.
Lemma lem7103454 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : ((term570 A x s f b) = (term571 A x s f b)) = ((term569 A x s f b) = (term581 A x s f b)).
Proof. exact (MK_COMB (@lem7103447 A x s f b) (@lem7103453 A x s f b)). Qed.
Lemma lem7103455 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term569 A x s f b) = (term581 A x s f b).
Proof. exact (EQ_MP (@lem7103454 A x s f b) (@lem7103439 A x s f b)). Qed.
Lemma lem7103456 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term496 A x s f b) = (term581 A x s f b).
Proof. exact (TRANS (@lem7103435 A x s f b) (@lem7103455 A x s f b)). Qed.
Lemma lem7103457 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term501 A x s f b) = (term582 A x s f b).
Proof. exact (MK_COMB (@lem7103413 A f b x s) (@lem7103456 A x s f b)). Qed.
Lemma lem7103459 {A : Type'} (P : A -> Prop) (Q : Prop) : (term537 A P Q) = (term538 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7103460 {A : Type'} (P : A -> Prop) (Q : Prop) : (term537 A P Q) = (term538 A P Q).
Proof. exact (@lem7103459 A P Q). Qed.
Lemma lem7103461 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term583 A x s f b) = (term584 A x s f b).
Proof. exact (@lem7103460 A (term552 A f b x s) (term581 A x s f b)). Qed.
Lemma lem7103462 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term585 A f b x s x') = (term550 A x' f b x s).
Proof. exact (eq_refl (term585 A f b x s x')). Qed.
Lemma lem7103463 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term586 A f b x s) = (term552 A f b x s).
Proof. exact (fun_ext (fun x' : A => @lem7103462 A x' f b x s)). Qed.
Lemma lem7103464 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103465 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term587 A f b x s) = (term553 A f b x s).
Proof. exact (MK_COMB (@lem7103464 A) (@lem7103463 A f b x s)). Qed.
Lemma lem7103466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103467 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term588 A f b x s) = (term554 A f b x s).
Proof. exact (MK_COMB (@lem7103466) (@lem7103465 A f b x s)). Qed.
Lemma lem7103468 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term581 A x s f b) = (term581 A x s f b).
Proof. exact (eq_refl (term581 A x s f b)). Qed.
Lemma lem7103469 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term583 A x s f b) = (term582 A x s f b).
Proof. exact (MK_COMB (@lem7103467 A f b x s) (@lem7103468 A x s f b)). Qed.
Lemma lem7103470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103471 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term589 A x s f b) = (term590 A x s f b).
Proof. exact (MK_COMB (@lem7103470) (@lem7103469 A x s f b)). Qed.
Lemma lem7103472 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term585 A f b x s x') = (term550 A x' f b x s).
Proof. exact (eq_refl (term585 A f b x s x')). Qed.
Lemma lem7103473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103474 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term591 A f b x s x') = (term592 A x' f b x s).
Proof. exact (MK_COMB (@lem7103473) (@lem7103472 A x' f b x s)). Qed.
Lemma lem7103475 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term581 A x s f b) = (term581 A x s f b).
Proof. exact (eq_refl (term581 A x s f b)). Qed.
Lemma lem7103476 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term593 A x' x s f b) = (term594 A x' x s f b).
Proof. exact (MK_COMB (@lem7103474 A x' f b x s) (@lem7103475 A x s f b)). Qed.
Lemma lem7103477 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term595 A x s f b) = (term596 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103476 A x' x s f b)). Qed.
Lemma lem7103478 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103479 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term584 A x s f b) = (term597 A x s f b).
Proof. exact (MK_COMB (@lem7103478 A) (@lem7103477 A x s f b)). Qed.
Lemma lem7103480 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : ((term583 A x s f b) = (term584 A x s f b)) = ((term582 A x s f b) = (term597 A x s f b)).
Proof. exact (MK_COMB (@lem7103471 A x s f b) (@lem7103479 A x s f b)). Qed.
Lemma lem7103481 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term582 A x s f b) = (term597 A x s f b).
Proof. exact (EQ_MP (@lem7103480 A x s f b) (@lem7103461 A x s f b)). Qed.
Lemma lem7103483 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7103484 {A : Type'} (P : Prop) (Q : A -> Prop) : (term555 A P Q) = (term556 A P Q).
Proof. exact (@lem7103483 A P Q). Qed.
Lemma lem7103485 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term598 A x' x s f b) = (term599 A x' x s f b).
Proof. exact (@lem7103484 A (term550 A x' f b x s) (term580 A x s f b)). Qed.
Lemma lem7103486 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x' : A) (b : real) : (term600 A x s f b x') = (term578 A x s f x' b).
Proof. exact (eq_refl (term600 A x s f b x')). Qed.
Lemma lem7103487 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term601 A x s f b) = (term580 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103486 A x s f x' b)). Qed.
Lemma lem7103488 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103489 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term602 A x s f b) = (term581 A x s f b).
Proof. exact (MK_COMB (@lem7103488 A) (@lem7103487 A x s f b)). Qed.
Lemma lem7103490 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term592 A x' f b x s) = (term592 A x' f b x s).
Proof. exact (eq_refl (term592 A x' f b x s)). Qed.
Lemma lem7103491 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term598 A x' x s f b) = (term594 A x' x s f b).
Proof. exact (MK_COMB (@lem7103490 A x' f b x s) (@lem7103489 A x s f b)). Qed.
Lemma lem7103492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103493 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term603 A x' x s f b) = (term604 A x' x s f b).
Proof. exact (MK_COMB (@lem7103492) (@lem7103491 A x' x s f b)). Qed.
Lemma lem7103494 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (x'' : A) (b : real) : (term600 A x s f b x'') = (term578 A x s f x'' b).
Proof. exact (eq_refl (term600 A x s f b x'')). Qed.
Lemma lem7103495 {A : Type'} (x' : A) (f : A -> real) (b : real) (x : A) (s : A -> Prop) : (term592 A x' f b x s) = (term592 A x' f b x s).
Proof. exact (eq_refl (term592 A x' f b x s)). Qed.
Lemma lem7103496 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (x'' : A) (b : real) : (term605 A x' x s f b x'') = (term606 A x' x s f x'' b).
Proof. exact (MK_COMB (@lem7103495 A x' f b x s) (@lem7103494 A x s f x'' b)). Qed.
Lemma lem7103497 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term607 A x' x s f b) = (term608 A x' x s f b).
Proof. exact (fun_ext (fun x'' : A => @lem7103496 A x' x s f x'' b)). Qed.
Lemma lem7103498 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103499 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term599 A x' x s f b) = (term609 A x' x s f b).
Proof. exact (MK_COMB (@lem7103498 A) (@lem7103497 A x' x s f b)). Qed.
Lemma lem7103500 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : ((term598 A x' x s f b) = (term599 A x' x s f b)) = ((term594 A x' x s f b) = (term609 A x' x s f b)).
Proof. exact (MK_COMB (@lem7103493 A x' x s f b) (@lem7103499 A x' x s f b)). Qed.
Lemma lem7103501 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term594 A x' x s f b) = (term609 A x' x s f b).
Proof. exact (EQ_MP (@lem7103500 A x' x s f b) (@lem7103485 A x' x s f b)). Qed.
Lemma lem7103502 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term596 A x s f b) = (term610 A x s f b).
Proof. exact (fun_ext (fun x' : A => @lem7103501 A x' x s f b)). Qed.
Lemma lem7103503 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103504 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term597 A x s f b) = (term611 A x s f b).
Proof. exact (MK_COMB (@lem7103503 A) (@lem7103502 A x s f b)). Qed.
Lemma lem7103505 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term582 A x s f b) = (term611 A x s f b).
Proof. exact (TRANS (@lem7103481 A x s f b) (@lem7103504 A x s f b)). Qed.
Lemma lem7103506 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term501 A x s f b) = (term611 A x s f b).
Proof. exact (TRANS (@lem7103457 A x s f b) (@lem7103505 A x s f b)). Qed.
Lemma lem7103507 {A : Type'} (x : A) (f : A -> real) (b : real) : (term510 A x f b) = (term612 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103506 A x s f b)). Qed.
Lemma lem7103508 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7103509 {A : Type'} (x : A) (f : A -> real) (b : real) : (term511 A x f b) = (term613 A x f b).
Proof. exact (MK_COMB (@lem7103508 A) (@lem7103507 A x f b)). Qed.
Lemma lem7103510 {A : Type'} (f : A -> real) (b : real) : (term516 A f b) = (term614 A f b).
Proof. exact (fun_ext (fun x : A => @lem7103509 A x f b)). Qed.
Lemma lem7103511 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103513 {A : Type'} (f : A -> real) (b : real) : (term517 A f b) = (term615 A f b).
Proof. exact (MK_COMB (@lem7103511 A) (@lem7103510 A f b)). Qed.
Lemma lem7103514 {A : Type'} (f : A -> real) (b : real) : (term412 A f b) = (term615 A f b).
Proof. exact (TRANS (@lem7103113 A f b) (@lem7103513 A f b)). Qed.
Lemma lem7103515 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term615 A f b.
Proof. exact (EQ_MP (@lem7103514 A f b) (@lem7102992 A f b h1)). Qed.
Lemma lem7103523 (x : real) (y : real) (b : real) : (term616 x y b) = (term617 x y b).
Proof. exact (@lem17045 (term8 y) (term39 x y b)). Qed.
Lemma lem7103525 (x : real) : (term618 x) = (term618 x).
Proof. exact (eq_refl (term618 x)). Qed.
Lemma lem7103526 (x : real) (y : real) (b : real) : (term619 x y b) = (term620 x y b).
Proof. exact (MK_COMB (@lem7103525 x) (@lem7103523 x y b)). Qed.
Lemma lem7103527 (x : real) (y : real) (b : real) : (term621 x y b) = (term619 x y b).
Proof. exact (@lem17045 (term8 x) (term51 x y b)). Qed.
Lemma lem7103528 (x : real) (y : real) (b : real) : (term621 x y b) = (term620 x y b).
Proof. exact (TRANS (@lem7103527 x y b) (@lem7103526 x y b)). Qed.
Lemma lem7103533 (x : real) (y : real) (b : real) : (term7 x y b) = (term7 x y b).
Proof. exact (eq_refl (term7 x y b)). Qed.
Lemma lem7103534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103535 (x : real) (y : real) (b : real) : (term622 x y b) = (term623 x y b).
Proof. exact (MK_COMB (@lem7103534) (@lem7103528 x y b)). Qed.
Lemma lem7103536 (x : real) (y : real) (b : real) : (term624 x y b) = (term625 x y b).
Proof. exact (MK_COMB (@lem7103535 x y b) (@lem7103533 x y b)). Qed.
Lemma lem7103537 (x : real) (y : real) (b : real) : (term170 x y b) = (term624 x y b).
Proof. exact (@lem17265 (term6 x y b) (term7 x y b)). Qed.
Lemma lem7103538 (x : real) (y : real) (b : real) : (term170 x y b) = (term625 x y b).
Proof. exact (TRANS (@lem7103537 x y b) (@lem7103536 x y b)). Qed.
Lemma lem7103539 (x : real) (y : real) : (term440 x y) = (term626 x y).
Proof. exact (fun_ext (fun b : real => @lem7103538 x y b)). Qed.
Lemma lem7103540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103541 (x : real) (y : real) : (term179 x y) = (term627 x y).
Proof. exact (MK_COMB (@lem7103540) (@lem7103539 x y)). Qed.
Lemma lem7103542 (x : real) : (term441 x) = (term628 x).
Proof. exact (fun_ext (fun y : real => @lem7103541 x y)). Qed.
Lemma lem7103543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103544 (x : real) : (term180 x) = (term629 x).
Proof. exact (MK_COMB (@lem7103543) (@lem7103542 x)). Qed.
Lemma lem7103545 : term442 = term630.
Proof. exact (fun_ext (fun x : real => @lem7103544 x)). Qed.
Lemma lem7103546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103607 : term181 = term631.
Proof. exact (MK_COMB (@lem7103546) (@lem7103545)). Qed.
Lemma lem7103608 (h1 : term181) : term631.
Proof. exact (EQ_MP (@lem7103607) (@lem7102993 h1)). Qed.
Lemma lem7103615 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term449 A s f x) = (term450 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term271 A f x)). Qed.
Lemma lem7103616 {A : Type'} (P : A -> Prop) : (term451 A P) = (term452 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7103617 {A : Type'} (s : A -> Prop) (f : A -> real) : (term453 A s f) = (term454 A s f).
Proof. exact (@lem7103616 A (term434 A s f)). Qed.
Lemma lem7103618 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term455 A s f x) = (term433 A s f x).
Proof. exact (eq_refl (term455 A s f x)). Qed.
Lemma lem7103619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103620 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term456 A s f x) = (term449 A s f x).
Proof. exact (MK_COMB (@lem7103619) (@lem7103618 A s f x)). Qed.
Lemma lem7103621 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term456 A s f x) = (term450 A s f x).
Proof. exact (TRANS (@lem7103620 A s f x) (@lem7103615 A s f x)). Qed.
Lemma lem7103622 {A : Type'} (s : A -> Prop) (f : A -> real) : (term457 A s f) = (term458 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103621 A s f x)). Qed.
Lemma lem7103623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103624 {A : Type'} (s : A -> Prop) (f : A -> real) : (term454 A s f) = (term459 A s f).
Proof. exact (MK_COMB (@lem7103623 A) (@lem7103622 A s f)). Qed.
Lemma lem7103625 {A : Type'} (s : A -> Prop) (f : A -> real) : (term453 A s f) = (term459 A s f).
Proof. exact (TRANS (@lem7103617 A s f) (@lem7103624 A s f)). Qed.
Lemma lem7103626 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term432 A s f).
Proof. exact (eq_refl (term432 A s f)). Qed.
Lemma lem7103627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103628 {A : Type'} (s : A -> Prop) (f : A -> real) : (term466 A s f) = (term467 A s f).
Proof. exact (MK_COMB (@lem7103627) (@lem7103625 A s f)). Qed.
Lemma lem7103629 {A : Type'} (s : A -> Prop) (f : A -> real) : (term632 A s f) = (term633 A s f).
Proof. exact (MK_COMB (@lem7103628 A s f) (@lem7103626 A s f)). Qed.
Lemma lem7103630 {A : Type'} (s : A -> Prop) (f : A -> real) : (term436 A s f) = (term632 A s f).
Proof. exact (@lem17265 (term218 A s f) (term432 A s f)). Qed.
Lemma lem7103631 {A : Type'} (s : A -> Prop) (f : A -> real) : (term436 A s f) = (term633 A s f).
Proof. exact (TRANS (@lem7103630 A s f) (@lem7103629 A s f)). Qed.
Lemma lem7103632 {A : Type'} (f : A -> real) : (term437 A f) = (term634 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103631 A s f)). Qed.
Lemma lem7103633 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7103634 {A : Type'} (f : A -> real) : (term438 A f) = (term635 A f).
Proof. exact (MK_COMB (@lem7103633 A) (@lem7103632 A f)). Qed.
Lemma lem7103635 {A : Type'} : (term439 A) = (term636 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7103634 A f)). Qed.
Lemma lem7103636 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7103637 {A : Type'} : (term178 A) = (term637 A).
Proof. exact (MK_COMB (@lem7103636 A) (@lem7103635 A)). Qed.
Lemma lem7103740 {A : Type'} (P : A -> Prop) (Q : Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7103741 {A : Type'} (P : A -> Prop) (Q : Prop) : (term518 A P Q) = (term519 A P Q).
Proof. exact (@lem7103740 A P Q). Qed.
Lemma lem7103742 {A : Type'} (s : A -> Prop) (f : A -> real) : (term638 A s f) = (term639 A s f).
Proof. exact (@lem7103741 A (term458 A s f) (term432 A s f)). Qed.
Lemma lem7103743 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term522 A s f x) = (term450 A s f x).
Proof. exact (eq_refl (term522 A s f x)). Qed.
Lemma lem7103744 {A : Type'} (s : A -> Prop) (f : A -> real) : (term523 A s f) = (term458 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103743 A s f x)). Qed.
Lemma lem7103745 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103746 {A : Type'} (s : A -> Prop) (f : A -> real) : (term524 A s f) = (term459 A s f).
Proof. exact (MK_COMB (@lem7103745 A) (@lem7103744 A s f)). Qed.
Lemma lem7103747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103748 {A : Type'} (s : A -> Prop) (f : A -> real) : (term525 A s f) = (term467 A s f).
Proof. exact (MK_COMB (@lem7103747) (@lem7103746 A s f)). Qed.
Lemma lem7103749 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term432 A s f).
Proof. exact (eq_refl (term432 A s f)). Qed.
Lemma lem7103750 {A : Type'} (s : A -> Prop) (f : A -> real) : (term638 A s f) = (term633 A s f).
Proof. exact (MK_COMB (@lem7103748 A s f) (@lem7103749 A s f)). Qed.
Lemma lem7103751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103752 {A : Type'} (s : A -> Prop) (f : A -> real) : (term640 A s f) = (term641 A s f).
Proof. exact (MK_COMB (@lem7103751) (@lem7103750 A s f)). Qed.
Lemma lem7103753 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term522 A s f x) = (term450 A s f x).
Proof. exact (eq_refl (term522 A s f x)). Qed.
Lemma lem7103754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103755 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term528 A s f x) = (term529 A s f x).
Proof. exact (MK_COMB (@lem7103754) (@lem7103753 A s f x)). Qed.
Lemma lem7103756 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term432 A s f).
Proof. exact (eq_refl (term432 A s f)). Qed.
Lemma lem7103757 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term642 A x s f) = (term643 A x s f).
Proof. exact (MK_COMB (@lem7103755 A s f x) (@lem7103756 A s f)). Qed.
Lemma lem7103758 {A : Type'} (s : A -> Prop) (f : A -> real) : (term644 A s f) = (term645 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103757 A x s f)). Qed.
Lemma lem7103759 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103760 {A : Type'} (s : A -> Prop) (f : A -> real) : (term639 A s f) = (term646 A s f).
Proof. exact (MK_COMB (@lem7103759 A) (@lem7103758 A s f)). Qed.
Lemma lem7103761 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term638 A s f) = (term639 A s f)) = ((term633 A s f) = (term646 A s f)).
Proof. exact (MK_COMB (@lem7103752 A s f) (@lem7103760 A s f)). Qed.
Lemma lem7103762 {A : Type'} (s : A -> Prop) (f : A -> real) : (term633 A s f) = (term646 A s f).
Proof. exact (EQ_MP (@lem7103761 A s f) (@lem7103742 A s f)). Qed.
Lemma lem7103763 {A : Type'} (f : A -> real) : (term634 A f) = (term647 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103762 A s f)). Qed.
Lemma lem7103764 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7103765 {A : Type'} (f : A -> real) : (term635 A f) = (term648 A f).
Proof. exact (MK_COMB (@lem7103764 A) (@lem7103763 A f)). Qed.
Lemma lem7103767 {A B : Type'} (P : type1413 A B) : (term649 A B P) = (term650 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7103768 {A : Type'} (P : type672 A) : (term651 A P) = (term652 A P).
Proof. exact (@lem7103767 (A -> Prop) A P). Qed.
Lemma lem7103769 {A : Type'} (f : A -> real) : (term653 A f) = (term654 A f).
Proof. exact (@lem7103768 A (term655 A f)). Qed.
Lemma lem7103770 {A : Type'} (s : A -> Prop) (f : A -> real) : (term656 A f s) = (term645 A s f).
Proof. exact (eq_refl (term656 A f s)). Qed.
Lemma lem7103771 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7103772 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term657 A f s x) = (term658 A s f x).
Proof. exact (MK_COMB (@lem7103770 A s f) (@lem7103771 A x)). Qed.
Lemma lem7103773 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term658 A s f x) = (term643 A x s f).
Proof. exact (eq_refl (term658 A s f x)). Qed.
Lemma lem7103774 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term657 A f s x) = (term643 A x s f).
Proof. exact (TRANS (@lem7103772 A s f x) (@lem7103773 A x s f)). Qed.
Lemma lem7103775 {A : Type'} (s : A -> Prop) (f : A -> real) : (term659 A f s) = (term645 A s f).
Proof. exact (fun_ext (fun x : A => @lem7103774 A x s f)). Qed.
Lemma lem7103776 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7103777 {A : Type'} (s : A -> Prop) (f : A -> real) : (term660 A f s) = (term646 A s f).
Proof. exact (MK_COMB (@lem7103776 A) (@lem7103775 A s f)). Qed.
Lemma lem7103778 {A : Type'} (f : A -> real) : (term661 A f) = (term647 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103777 A s f)). Qed.
Lemma lem7103779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7103780 {A : Type'} (f : A -> real) : (term653 A f) = (term648 A f).
Proof. exact (MK_COMB (@lem7103779 A) (@lem7103778 A f)). Qed.
Lemma lem7103781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103782 {A : Type'} (f : A -> real) : (term662 A f) = (term663 A f).
Proof. exact (MK_COMB (@lem7103781) (@lem7103780 A f)). Qed.
Lemma lem7103783 {A : Type'} (s : A -> Prop) (f : A -> real) : (term656 A f s) = (term645 A s f).
Proof. exact (eq_refl (term656 A f s)). Qed.
Lemma lem7103784 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7103785 {A : Type'} (f : A -> real) (x : type684 A) (s : A -> Prop) : (term664 A f x s) = (term665 A f x s).
Proof. exact (MK_COMB (@lem7103783 A s f) (@lem7103784 A x s)). Qed.
Lemma lem7103786 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) : (term665 A f x s) = (term666 A x s f).
Proof. exact (eq_refl (term665 A f x s)). Qed.
Lemma lem7103787 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) : (term664 A f x s) = (term666 A x s f).
Proof. exact (TRANS (@lem7103785 A f x s) (@lem7103786 A x s f)). Qed.
Lemma lem7103788 {A : Type'} (x : type684 A) (f : A -> real) : (term667 A f x) = (term668 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7103787 A x s f)). Qed.
Lemma lem7103789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7103790 {A : Type'} (x : type684 A) (f : A -> real) : (term669 A f x) = (term670 A x f).
Proof. exact (MK_COMB (@lem7103789 A) (@lem7103788 A x f)). Qed.
Lemma lem7103791 {A : Type'} (f : A -> real) : (term671 A f) = (term672 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem7103790 A x f)). Qed.
Lemma lem7103792 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7103793 {A : Type'} (f : A -> real) : (term654 A f) = (term673 A f).
Proof. exact (MK_COMB (@lem7103792 A) (@lem7103791 A f)). Qed.
Lemma lem7103794 {A : Type'} (f : A -> real) : ((term653 A f) = (term654 A f)) = ((term648 A f) = (term673 A f)).
Proof. exact (MK_COMB (@lem7103782 A f) (@lem7103793 A f)). Qed.
Lemma lem7103795 {A : Type'} (f : A -> real) : (term648 A f) = (term673 A f).
Proof. exact (EQ_MP (@lem7103794 A f) (@lem7103769 A f)). Qed.
Lemma lem7103796 {A : Type'} (f : A -> real) : (term635 A f) = (term673 A f).
Proof. exact (TRANS (@lem7103765 A f) (@lem7103795 A f)). Qed.
Lemma lem7103797 {A : Type'} : (term636 A) = (term674 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7103796 A f)). Qed.
Lemma lem7103798 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7103799 {A : Type'} : (term637 A) = (term675 A).
Proof. exact (MK_COMB (@lem7103798 A) (@lem7103797 A)). Qed.
Lemma lem7103801 {A B : Type'} (P : type1413 A B) : (term649 A B P) = (term650 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7103802 {A : Type'} (P : type707 A) : (term676 A P) = (term677 A P).
Proof. exact (@lem7103801 (A -> real) (type684 A) P). Qed.
Lemma lem7103803 {A : Type'} : (term678 A) = (term679 A).
Proof. exact (@lem7103802 A (term680 A)). Qed.
Lemma lem7103804 {A : Type'} (f : A -> real) : (term681 A f) = (term672 A f).
Proof. exact (eq_refl (term681 A f)). Qed.
Lemma lem7103805 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7103806 {A : Type'} (f : A -> real) (x : type684 A) : (term682 A f x) = (term683 A f x).
Proof. exact (MK_COMB (@lem7103804 A f) (@lem7103805 A x)). Qed.
Lemma lem7103807 {A : Type'} (x : type684 A) (f : A -> real) : (term683 A f x) = (term670 A x f).
Proof. exact (eq_refl (term683 A f x)). Qed.
Lemma lem7103808 {A : Type'} (x : type684 A) (f : A -> real) : (term682 A f x) = (term670 A x f).
Proof. exact (TRANS (@lem7103806 A f x) (@lem7103807 A x f)). Qed.
Lemma lem7103809 {A : Type'} (f : A -> real) : (term684 A f) = (term672 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem7103808 A x f)). Qed.
Lemma lem7103810 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7103811 {A : Type'} (f : A -> real) : (term685 A f) = (term673 A f).
Proof. exact (MK_COMB (@lem7103810 A) (@lem7103809 A f)). Qed.
Lemma lem7103812 {A : Type'} : (term686 A) = (term674 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7103811 A f)). Qed.
Lemma lem7103813 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7103814 {A : Type'} : (term678 A) = (term675 A).
Proof. exact (MK_COMB (@lem7103813 A) (@lem7103812 A)). Qed.
Lemma lem7103815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7103816 {A : Type'} : (term687 A) = (term688 A).
Proof. exact (MK_COMB (@lem7103815) (@lem7103814 A)). Qed.
Lemma lem7103817 {A : Type'} (f : A -> real) : (term681 A f) = (term672 A f).
Proof. exact (eq_refl (term681 A f)). Qed.
Lemma lem7103818 {A : Type'} (x : type710 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7103819 {A : Type'} (x : type710 A) (f : A -> real) : (term689 A x f) = (term690 A x f).
Proof. exact (MK_COMB (@lem7103817 A f) (@lem7103818 A x f)). Qed.
Lemma lem7103820 {A : Type'} (x : type710 A) (f : A -> real) : (term690 A x f) = (term691 A x f).
Proof. exact (eq_refl (term690 A x f)). Qed.
Lemma lem7103821 {A : Type'} (x : type710 A) (f : A -> real) : (term689 A x f) = (term691 A x f).
Proof. exact (TRANS (@lem7103819 A x f) (@lem7103820 A x f)). Qed.
Lemma lem7103822 {A : Type'} (x : type710 A) : (term692 A x) = (term693 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7103821 A x f)). Qed.
Lemma lem7103823 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7103824 {A : Type'} (x : type710 A) : (term694 A x) = (term695 A x).
Proof. exact (MK_COMB (@lem7103823 A) (@lem7103822 A x)). Qed.
Lemma lem7103825 {A : Type'} : (term696 A) = (term697 A).
Proof. exact (fun_ext (fun x : type710 A => @lem7103824 A x)). Qed.
Lemma lem7103826 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7103827 {A : Type'} : (term679 A) = (term698 A).
Proof. exact (MK_COMB (@lem7103826 A) (@lem7103825 A)). Qed.
Lemma lem7103828 {A : Type'} : ((term678 A) = (term679 A)) = ((term675 A) = (term698 A)).
Proof. exact (MK_COMB (@lem7103816 A) (@lem7103827 A)). Qed.
Lemma lem7103829 {A : Type'} : (term675 A) = (term698 A).
Proof. exact (EQ_MP (@lem7103828 A) (@lem7103803 A)). Qed.
Lemma lem7103831 {A : Type'} : (term637 A) = (term698 A).
Proof. exact (TRANS (@lem7103799 A) (@lem7103829 A)). Qed.
Lemma lem7103832 {A : Type'} : (term178 A) = (term698 A).
Proof. exact (TRANS (@lem7103637 A) (@lem7103831 A)). Qed.
Lemma lem7103833 {A : Type'} (h1 : term178 A) : term698 A.
Proof. exact (EQ_MP (@lem7103832 A) (@lem7102994 A h1)). Qed.
Lemma lem7103834 {A : Type'} (x : type710 A) (h1 : term695 A x) : term695 A x.
Proof. exact (h1). Qed.
Lemma lem7103835 {A : Type'} (x' : A) (f : A -> real) (b : real) (h1 : term613 A x' f b) : term613 A x' f b.
Proof. exact (h1). Qed.
Lemma lem7103836 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term611 A x' s f b) : term611 A x' s f b.
Proof. exact (h1). Qed.
Lemma lem7103837 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term609 A x'' x' s f b) : term609 A x'' x' s f b.
Proof. exact (h1). Qed.
Lemma lem7103838 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term606 A x'' x' s f x''' b.
Proof. exact (h1). Qed.
Lemma lem7103845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103846 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7103845 real (real -> Prop) f x). Qed.
Lemma lem7103847 (y : real) : (real_le y) = (@I (real -> real -> Prop) real_le y).
Proof. exact (@lem7103846 real_le y). Qed.
Lemma lem7103848 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7103849 (y : real) (b : real) : (real_le y b) = (@I (real -> real -> Prop) real_le y b).
Proof. exact (MK_COMB (@lem7103847 y) (@lem7103848 b)). Qed.
Lemma lem7103851 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103852 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7103851 real Prop f x). Qed.
Lemma lem7103853 (y : real) (b : real) : (@I (real -> real -> Prop) real_le y b) = (term699 y b).
Proof. exact (@lem7103852 (@I (real -> real -> Prop) real_le y) b). Qed.
Lemma lem7103855 (y : real) (b : real) : (real_le y b) = (term699 y b).
Proof. exact (TRANS (@lem7103849 y b) (@lem7103853 y b)). Qed.
Lemma lem7103862 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103863 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7103862 real (real -> Prop) f x). Qed.
Lemma lem7103864 (x : real) : (real_le x) = (@I (real -> real -> Prop) real_le x).
Proof. exact (@lem7103863 real_le x). Qed.
Lemma lem7103865 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7103866 (x : real) (b : real) : (real_le x b) = (@I (real -> real -> Prop) real_le x b).
Proof. exact (MK_COMB (@lem7103864 x) (@lem7103865 b)). Qed.
Lemma lem7103868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103869 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7103868 real Prop f x). Qed.
Lemma lem7103870 (x : real) (b : real) : (@I (real -> real -> Prop) real_le x b) = (term699 x b).
Proof. exact (@lem7103869 (@I (real -> real -> Prop) real_le x) b). Qed.
Lemma lem7103872 (x : real) (b : real) : (real_le x b) = (term699 x b).
Proof. exact (TRANS (@lem7103866 x b) (@lem7103870 x b)). Qed.
Lemma lem7103873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7103874 (x : real) (b : real) : (term700 x b) = (term701 x b).
Proof. exact (MK_COMB (@lem7103873) (@lem7103872 x b)). Qed.
Lemma lem7103875 (x : real) (y : real) (b : real) : (term7 x y b) = (term702 x y b).
Proof. exact (MK_COMB (@lem7103874 x b) (@lem7103855 y b)). Qed.
Lemma lem7103876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103877 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7103884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103885 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7103884 real (real -> real) f x). Qed.
Lemma lem7103886 (x : real) : (real_add x) = (@I (real -> real -> real) real_add x).
Proof. exact (@lem7103885 real_add x). Qed.
Lemma lem7103887 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7103888 (x : real) (y : real) : (real_add x y) = (@I (real -> real -> real) real_add x y).
Proof. exact (MK_COMB (@lem7103886 x) (@lem7103887 y)). Qed.
Lemma lem7103890 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103891 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7103890 real real f x). Qed.
Lemma lem7103892 (x : real) (y : real) : (@I (real -> real -> real) real_add x y) = (term703 x y).
Proof. exact (@lem7103891 (@I (real -> real -> real) real_add x) y). Qed.
Lemma lem7103894 (x : real) (y : real) : (real_add x y) = (term703 x y).
Proof. exact (TRANS (@lem7103888 x y) (@lem7103892 x y)). Qed.
Lemma lem7103895 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7103896 (x : real) (y : real) : (term704 x y) = (term705 x y).
Proof. exact (MK_COMB (@lem7103877) (@lem7103894 x y)). Qed.
Lemma lem7103897 (x : real) (y : real) (b : real) : (term39 x y b) = (term706 x y b).
Proof. exact (MK_COMB (@lem7103896 x y) (@lem7103895 b)). Qed.
Lemma lem7103899 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103900 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7103899 real (real -> Prop) f x). Qed.
Lemma lem7103901 (x : real) (y : real) : (term705 x y) = (term707 x y).
Proof. exact (@lem7103900 real_le (term703 x y)). Qed.
Lemma lem7103902 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7103903 (x : real) (y : real) (b : real) : (term706 x y b) = (term708 x y b).
Proof. exact (MK_COMB (@lem7103901 x y) (@lem7103902 b)). Qed.
Lemma lem7103905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103906 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7103905 real Prop f x). Qed.
Lemma lem7103907 (x : real) (y : real) (b : real) : (term708 x y b) = (term709 x y b).
Proof. exact (@lem7103906 (term707 x y) b). Qed.
Lemma lem7103908 (x : real) (y : real) (b : real) : (term706 x y b) = (term709 x y b).
Proof. exact (TRANS (@lem7103903 x y b) (@lem7103907 x y b)). Qed.
Lemma lem7103909 (x : real) (y : real) (b : real) : (term39 x y b) = (term709 x y b).
Proof. exact (TRANS (@lem7103897 x y b) (@lem7103908 x y b)). Qed.
Lemma lem7103910 (x : real) (y : real) (b : real) : (term710 x y b) = (term711 x y b).
Proof. exact (MK_COMB (@lem7103876) (@lem7103909 x y b)). Qed.
Lemma lem7103911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103912 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7103913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7103918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103919 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7103918 nat nat f x). Qed.
Lemma lem7103921 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7103919 NUMERAL 0). Qed.
Lemma lem7103922 : term10 = term712.
Proof. exact (MK_COMB (@lem7103913) (@lem7103921)). Qed.
Lemma lem7103924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103925 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7103924 nat real f x). Qed.
Lemma lem7103926 : term712 = term713.
Proof. exact (@lem7103925 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7103927 : term10 = term713.
Proof. exact (TRANS (@lem7103922) (@lem7103926)). Qed.
Lemma lem7103928 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7103929 : term296 = term714.
Proof. exact (MK_COMB (@lem7103912) (@lem7103927)). Qed.
Lemma lem7103930 (y : real) : (term8 y) = (term715 y).
Proof. exact (MK_COMB (@lem7103929) (@lem7103928 y)). Qed.
Lemma lem7103932 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103933 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7103932 real (real -> Prop) f x). Qed.
Lemma lem7103934 : term714 = term716.
Proof. exact (@lem7103933 real_le term713). Qed.
Lemma lem7103935 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7103936 (y : real) : (term715 y) = (term717 y).
Proof. exact (MK_COMB (@lem7103934) (@lem7103935 y)). Qed.
Lemma lem7103938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103939 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7103938 real Prop f x). Qed.
Lemma lem7103940 (y : real) : (term717 y) = (term718 y).
Proof. exact (@lem7103939 term716 y). Qed.
Lemma lem7103941 (y : real) : (term715 y) = (term718 y).
Proof. exact (TRANS (@lem7103936 y) (@lem7103940 y)). Qed.
Lemma lem7103942 (y : real) : (term8 y) = (term718 y).
Proof. exact (TRANS (@lem7103930 y) (@lem7103941 y)). Qed.
Lemma lem7103943 (y : real) : (term719 y) = (term720 y).
Proof. exact (MK_COMB (@lem7103911) (@lem7103942 y)). Qed.
Lemma lem7103944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103945 (y : real) : (term618 y) = (term721 y).
Proof. exact (MK_COMB (@lem7103944) (@lem7103943 y)). Qed.
Lemma lem7103946 (x : real) (y : real) (b : real) : (term617 x y b) = (term722 x y b).
Proof. exact (MK_COMB (@lem7103945 y) (@lem7103910 x y b)). Qed.
Lemma lem7103947 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7103948 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7103949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7103954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103955 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7103954 nat nat f x). Qed.
Lemma lem7103957 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7103955 NUMERAL 0). Qed.
Lemma lem7103958 : term10 = term712.
Proof. exact (MK_COMB (@lem7103949) (@lem7103957)). Qed.
Lemma lem7103960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103961 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7103960 nat real f x). Qed.
Lemma lem7103962 : term712 = term713.
Proof. exact (@lem7103961 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7103963 : term10 = term713.
Proof. exact (TRANS (@lem7103958) (@lem7103962)). Qed.
Lemma lem7103964 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7103965 : term296 = term714.
Proof. exact (MK_COMB (@lem7103948) (@lem7103963)). Qed.
Lemma lem7103966 (x : real) : (term8 x) = (term715 x).
Proof. exact (MK_COMB (@lem7103965) (@lem7103964 x)). Qed.
Lemma lem7103968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103969 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7103968 real (real -> Prop) f x). Qed.
Lemma lem7103970 : term714 = term716.
Proof. exact (@lem7103969 real_le term713). Qed.
Lemma lem7103971 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7103972 (x : real) : (term715 x) = (term717 x).
Proof. exact (MK_COMB (@lem7103970) (@lem7103971 x)). Qed.
Lemma lem7103974 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7103975 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7103974 real Prop f x). Qed.
Lemma lem7103976 (x : real) : (term717 x) = (term718 x).
Proof. exact (@lem7103975 term716 x). Qed.
Lemma lem7103977 (x : real) : (term715 x) = (term718 x).
Proof. exact (TRANS (@lem7103972 x) (@lem7103976 x)). Qed.
Lemma lem7103978 (x : real) : (term8 x) = (term718 x).
Proof. exact (TRANS (@lem7103966 x) (@lem7103977 x)). Qed.
Lemma lem7103979 (x : real) : (term719 x) = (term720 x).
Proof. exact (MK_COMB (@lem7103947) (@lem7103978 x)). Qed.
Lemma lem7103980 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103981 (x : real) : (term618 x) = (term721 x).
Proof. exact (MK_COMB (@lem7103980) (@lem7103979 x)). Qed.
Lemma lem7103982 (x : real) (y : real) (b : real) : (term620 x y b) = (term723 x y b).
Proof. exact (MK_COMB (@lem7103981 x) (@lem7103946 x y b)). Qed.
Lemma lem7103983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7103984 (x : real) (y : real) (b : real) : (term623 x y b) = (term724 x y b).
Proof. exact (MK_COMB (@lem7103983) (@lem7103982 x y b)). Qed.
Lemma lem7103985 (x : real) (y : real) (b : real) : (term625 x y b) = (term725 x y b).
Proof. exact (MK_COMB (@lem7103984 x y b) (@lem7103875 x y b)). Qed.
Lemma lem7103986 (x : real) (y : real) : (term626 x y) = (term726 x y).
Proof. exact (fun_ext (fun b : real => @lem7103985 x y b)). Qed.
Lemma lem7103987 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103988 (x : real) (y : real) : (term627 x y) = (term727 x y).
Proof. exact (MK_COMB (@lem7103987) (@lem7103986 x y)). Qed.
Lemma lem7103989 (x : real) : (term628 x) = (term728 x).
Proof. exact (fun_ext (fun y : real => @lem7103988 x y)). Qed.
Lemma lem7103990 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103991 (x : real) : (term629 x) = (term729 x).
Proof. exact (MK_COMB (@lem7103990) (@lem7103989 x)). Qed.
Lemma lem7103992 : term630 = term730.
Proof. exact (fun_ext (fun x : real => @lem7103991 x)). Qed.
Lemma lem7103993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7103994 : term631 = term731.
Proof. exact (MK_COMB (@lem7103993) (@lem7103992)). Qed.
Lemma lem7103995 (h1 : term181) : term731.
Proof. exact (EQ_MP (@lem7103994) (@lem7103608 h1)). Qed.
Lemma lem7103996 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7103997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7104002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104003 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7104002 nat nat f x). Qed.
Lemma lem7104005 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7104003 NUMERAL 0). Qed.
Lemma lem7104006 : term10 = term712.
Proof. exact (MK_COMB (@lem7103997) (@lem7104005)). Qed.
Lemma lem7104008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104009 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7104008 nat real f x). Qed.
Lemma lem7104010 : term712 = term713.
Proof. exact (@lem7104009 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7104011 : term10 = term713.
Proof. exact (TRANS (@lem7104006) (@lem7104010)). Qed.
Lemma lem7104018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104019 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7104018 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7104020 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7104019 A (@sum A) s). Qed.
Lemma lem7104021 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7104022 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7104020 A s) (@lem7104021 A f)). Qed.
Lemma lem7104024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104025 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7104024 (A -> real) real f x). Qed.
Lemma lem7104026 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term732 A s f).
Proof. exact (@lem7104025 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7104028 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term732 A s f).
Proof. exact (TRANS (@lem7104022 A s f) (@lem7104026 A s f)). Qed.
Lemma lem7104029 : term296 = term714.
Proof. exact (MK_COMB (@lem7103996) (@lem7104011)). Qed.
Lemma lem7104030 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term733 A s f).
Proof. exact (MK_COMB (@lem7104029) (@lem7104028 A s f)). Qed.
Lemma lem7104032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104033 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104032 real (real -> Prop) f x). Qed.
Lemma lem7104034 : term714 = term716.
Proof. exact (@lem7104033 real_le term713). Qed.
Lemma lem7104035 {A : Type'} (s : A -> Prop) (f : A -> real) : (term732 A s f) = (term732 A s f).
Proof. exact (eq_refl (term732 A s f)). Qed.
Lemma lem7104036 {A : Type'} (s : A -> Prop) (f : A -> real) : (term733 A s f) = (term734 A s f).
Proof. exact (MK_COMB (@lem7104034) (@lem7104035 A s f)). Qed.
Lemma lem7104038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104039 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104038 real Prop f x). Qed.
Lemma lem7104040 {A : Type'} (s : A -> Prop) (f : A -> real) : (term734 A s f) = (term735 A s f).
Proof. exact (@lem7104039 term716 (term732 A s f)). Qed.
Lemma lem7104041 {A : Type'} (s : A -> Prop) (f : A -> real) : (term733 A s f) = (term735 A s f).
Proof. exact (TRANS (@lem7104036 A s f) (@lem7104040 A s f)). Qed.
Lemma lem7104042 {A : Type'} (s : A -> Prop) (f : A -> real) : (term432 A s f) = (term735 A s f).
Proof. exact (TRANS (@lem7104030 A s f) (@lem7104041 A s f)). Qed.
Lemma lem7104043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104044 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7104050 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104051 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7104050 nat nat f x). Qed.
Lemma lem7104053 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7104051 NUMERAL 0). Qed.
Lemma lem7104054 : term10 = term712.
Proof. exact (MK_COMB (@lem7104045) (@lem7104053)). Qed.
Lemma lem7104056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104057 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7104056 nat real f x). Qed.
Lemma lem7104058 : term712 = term713.
Proof. exact (@lem7104057 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7104059 : term10 = term713.
Proof. exact (TRANS (@lem7104054) (@lem7104058)). Qed.
Lemma lem7104060 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7104067 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104068 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7104067 (A -> real) (type684 A) f x). Qed.
Lemma lem7104069 {A : Type'} (x : type710 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7104068 A x f). Qed.
Lemma lem7104070 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104071 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (x f s) = (@I ((A -> real) -> (A -> Prop) -> A) x f s).
Proof. exact (MK_COMB (@lem7104069 A x f) (@lem7104070 A s)). Qed.
Lemma lem7104073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104074 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7104073 (A -> Prop) A f x). Qed.
Lemma lem7104075 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> A) x f s) = (term736 A x f s).
Proof. exact (@lem7104074 A (@I ((A -> real) -> (A -> Prop) -> A) x f) s). Qed.
Lemma lem7104077 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (x f s) = (term736 A x f s).
Proof. exact (TRANS (@lem7104071 A x f s) (@lem7104075 A x f s)). Qed.
Lemma lem7104078 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term737 A x f s) = (term738 A x f s).
Proof. exact (MK_COMB (@lem7104060 A f) (@lem7104077 A x f s)). Qed.
Lemma lem7104080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104081 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104080 A real f x). Qed.
Lemma lem7104082 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term738 A x f s) = (term739 A x f s).
Proof. exact (@lem7104081 A f (term736 A x f s)). Qed.
Lemma lem7104083 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term737 A x f s) = (term739 A x f s).
Proof. exact (TRANS (@lem7104078 A x f s) (@lem7104082 A x f s)). Qed.
Lemma lem7104084 : term296 = term714.
Proof. exact (MK_COMB (@lem7104044) (@lem7104059)). Qed.
Lemma lem7104085 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term740 A x f s) = (term741 A x f s).
Proof. exact (MK_COMB (@lem7104084) (@lem7104083 A x f s)). Qed.
Lemma lem7104087 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104088 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104087 real (real -> Prop) f x). Qed.
Lemma lem7104089 : term714 = term716.
Proof. exact (@lem7104088 real_le term713). Qed.
Lemma lem7104090 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term739 A x f s) = (term739 A x f s).
Proof. exact (eq_refl (term739 A x f s)). Qed.
Lemma lem7104091 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term741 A x f s) = (term742 A x f s).
Proof. exact (MK_COMB (@lem7104089) (@lem7104090 A x f s)). Qed.
Lemma lem7104093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104094 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104093 real Prop f x). Qed.
Lemma lem7104095 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term742 A x f s) = (term743 A x f s).
Proof. exact (@lem7104094 term716 (term739 A x f s)). Qed.
Lemma lem7104096 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term741 A x f s) = (term743 A x f s).
Proof. exact (TRANS (@lem7104091 A x f s) (@lem7104095 A x f s)). Qed.
Lemma lem7104097 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term740 A x f s) = (term743 A x f s).
Proof. exact (TRANS (@lem7104085 A x f s) (@lem7104096 A x f s)). Qed.
Lemma lem7104098 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term744 A x f s) = (term745 A x f s).
Proof. exact (MK_COMB (@lem7104043) (@lem7104097 A x f s)). Qed.
Lemma lem7104099 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7104106 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104107 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7104106 (A -> real) (type684 A) f x). Qed.
Lemma lem7104108 {A : Type'} (x : type710 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7104107 A x f). Qed.
Lemma lem7104109 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104110 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (x f s) = (@I ((A -> real) -> (A -> Prop) -> A) x f s).
Proof. exact (MK_COMB (@lem7104108 A x f) (@lem7104109 A s)). Qed.
Lemma lem7104112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104113 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7104112 (A -> Prop) A f x). Qed.
Lemma lem7104114 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> A) x f s) = (term736 A x f s).
Proof. exact (@lem7104113 A (@I ((A -> real) -> (A -> Prop) -> A) x f) s). Qed.
Lemma lem7104116 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (x f s) = (term736 A x f s).
Proof. exact (TRANS (@lem7104110 A x f s) (@lem7104114 A x f s)). Qed.
Lemma lem7104117 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104118 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term746 A x f s) = (term747 A x f s).
Proof. exact (MK_COMB (@lem7104099 A) (@lem7104116 A x f s)). Qed.
Lemma lem7104119 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term748 A x f s) = (term749 A x f s).
Proof. exact (MK_COMB (@lem7104118 A x f s) (@lem7104117 A s)). Qed.
Lemma lem7104121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104122 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104121 A (type686 A) f x). Qed.
Lemma lem7104123 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term747 A x f s) = (term750 A x f s).
Proof. exact (@lem7104122 A (@IN A) (term736 A x f s)). Qed.
Lemma lem7104124 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104125 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term749 A x f s) = (term751 A x f s).
Proof. exact (MK_COMB (@lem7104123 A x f s) (@lem7104124 A s)). Qed.
Lemma lem7104127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104128 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104127 (A -> Prop) Prop f x). Qed.
Lemma lem7104129 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term751 A x f s) = (term752 A x f s).
Proof. exact (@lem7104128 A (term750 A x f s) s). Qed.
Lemma lem7104130 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term749 A x f s) = (term752 A x f s).
Proof. exact (TRANS (@lem7104125 A x f s) (@lem7104129 A x f s)). Qed.
Lemma lem7104131 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term748 A x f s) = (term752 A x f s).
Proof. exact (TRANS (@lem7104119 A x f s) (@lem7104130 A x f s)). Qed.
Lemma lem7104132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104133 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term753 A x f s) = (term754 A x f s).
Proof. exact (MK_COMB (@lem7104132) (@lem7104131 A x f s)). Qed.
Lemma lem7104134 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term755 A x f s) = (term756 A x f s).
Proof. exact (MK_COMB (@lem7104133 A x f s) (@lem7104098 A x f s)). Qed.
Lemma lem7104135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7104136 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term757 A x f s) = (term758 A x f s).
Proof. exact (MK_COMB (@lem7104135) (@lem7104134 A x f s)). Qed.
Lemma lem7104137 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) : (term759 A x s f) = (term760 A x s f).
Proof. exact (MK_COMB (@lem7104136 A x f s) (@lem7104042 A s f)). Qed.
Lemma lem7104138 {A : Type'} (x : type710 A) (f : A -> real) : (term761 A x f) = (term762 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7104137 A x s f)). Qed.
Lemma lem7104139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7104140 {A : Type'} (x : type710 A) (f : A -> real) : (term691 A x f) = (term763 A x f).
Proof. exact (MK_COMB (@lem7104139 A) (@lem7104138 A x f)). Qed.
Lemma lem7104141 {A : Type'} (x : type710 A) : (term693 A x) = (term764 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7104140 A x f)). Qed.
Lemma lem7104142 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7104143 {A : Type'} (x : type710 A) : (term695 A x) = (term765 A x).
Proof. exact (MK_COMB (@lem7104142 A) (@lem7104141 A x)). Qed.
Lemma lem7104144 {A : Type'} (x : type710 A) (h1 : term695 A x) : term765 A x.
Proof. exact (EQ_MP (@lem7104143 A x) (@lem7103834 A x h1)). Qed.
Lemma lem7104145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104146 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104151 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104152 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104151 A real f x). Qed.
Lemma lem7104154 {A : Type'} (f : A -> real) (x''' : A) : (f x''') = (@I (A -> real) f x''').
Proof. exact (@lem7104152 A f x'''). Qed.
Lemma lem7104155 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104156 {A : Type'} (f : A -> real) (x''' : A) : (term766 A f x''') = (term767 A f x''').
Proof. exact (MK_COMB (@lem7104146) (@lem7104154 A f x''')). Qed.
Lemma lem7104157 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term300 A f x''' b) = (term768 A f x''' b).
Proof. exact (MK_COMB (@lem7104156 A f x''') (@lem7104155 b)). Qed.
Lemma lem7104159 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104160 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104159 real (real -> Prop) f x). Qed.
Lemma lem7104161 {A : Type'} (f : A -> real) (x''' : A) : (term767 A f x''') = (term769 A f x''').
Proof. exact (@lem7104160 real_le (@I (A -> real) f x''')). Qed.
Lemma lem7104162 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104163 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term768 A f x''' b) = (term770 A f x''' b).
Proof. exact (MK_COMB (@lem7104161 A f x''') (@lem7104162 b)). Qed.
Lemma lem7104165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104166 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104165 real Prop f x). Qed.
Lemma lem7104167 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term770 A f x''' b) = (term771 A f x''' b).
Proof. exact (@lem7104166 (term769 A f x''') b). Qed.
Lemma lem7104168 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term768 A f x''' b) = (term771 A f x''' b).
Proof. exact (TRANS (@lem7104163 A f x''' b) (@lem7104167 A f x''' b)). Qed.
Lemma lem7104169 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term300 A f x''' b) = (term771 A f x''' b).
Proof. exact (TRANS (@lem7104157 A f x''' b) (@lem7104168 A f x''' b)). Qed.
Lemma lem7104170 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term772 A f x''' b) = (term773 A f x''' b).
Proof. exact (MK_COMB (@lem7104145) (@lem7104169 A f x''' b)). Qed.
Lemma lem7104177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104178 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104177 A (type686 A) f x). Qed.
Lemma lem7104179 {A : Type'} (x''' : A) : (@IN A x''') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''').
Proof. exact (@lem7104178 A (@IN A) x'''). Qed.
Lemma lem7104180 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104181 {A : Type'} (x''' : A) (s : A -> Prop) : (@IN A x''' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''' s).
Proof. exact (MK_COMB (@lem7104179 A x''') (@lem7104180 A s)). Qed.
Lemma lem7104183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104184 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104183 (A -> Prop) Prop f x). Qed.
Lemma lem7104185 {A : Type'} (x''' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x''' s) = (term774 A x''' s).
Proof. exact (@lem7104184 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x''') s). Qed.
Lemma lem7104187 {A : Type'} (x''' : A) (s : A -> Prop) : (@IN A x''' s) = (term774 A x''' s).
Proof. exact (TRANS (@lem7104181 A x''' s) (@lem7104185 A x''' s)). Qed.
Lemma lem7104194 {A : Type'} (x''' : A) (x' : A) : (term775 A x''' x') = (term775 A x''' x').
Proof. exact (eq_refl (term775 A x''' x')). Qed.
Lemma lem7104195 {A : Type'} (x' : A) (x''' : A) (s : A -> Prop) : (term188 A x' x''' s) = (term776 A x' x''' s).
Proof. exact (MK_COMB (@lem7104194 A x''' x') (@lem7104187 A x''' s)). Qed.
Lemma lem7104196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104197 {A : Type'} (x' : A) (x''' : A) (s : A -> Prop) : (term777 A x' x''' s) = (term778 A x' x''' s).
Proof. exact (MK_COMB (@lem7104196) (@lem7104195 A x' x''' s)). Qed.
Lemma lem7104198 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) : (term481 A x' s f x''' b) = (term779 A x' s f x''' b).
Proof. exact (MK_COMB (@lem7104197 A x' x''' s) (@lem7104170 A f x''' b)). Qed.
Lemma lem7104199 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7104205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104206 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104205 A real f x). Qed.
Lemma lem7104208 {A : Type'} (f : A -> real) (x' : A) : (f x') = (@I (A -> real) f x').
Proof. exact (@lem7104206 A f x'). Qed.
Lemma lem7104215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104216 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7104215 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7104217 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7104216 A (@sum A) s). Qed.
Lemma lem7104218 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7104219 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7104217 A s) (@lem7104218 A f)). Qed.
Lemma lem7104221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104222 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7104221 (A -> real) real f x). Qed.
Lemma lem7104223 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term732 A s f).
Proof. exact (@lem7104222 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7104225 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term732 A s f).
Proof. exact (TRANS (@lem7104219 A s f) (@lem7104223 A s f)). Qed.
Lemma lem7104226 {A : Type'} (f : A -> real) (x' : A) : (term780 A f x') = (term781 A f x').
Proof. exact (MK_COMB (@lem7104200) (@lem7104208 A f x')). Qed.
Lemma lem7104227 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term362 A x' s f) = (term782 A x' s f).
Proof. exact (MK_COMB (@lem7104226 A f x') (@lem7104225 A s f)). Qed.
Lemma lem7104229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104230 (f : type1627) (x : real) : (f x) = (@I (real -> real -> real) f x).
Proof. exact (@lem7104229 real (real -> real) f x). Qed.
Lemma lem7104231 {A : Type'} (f : A -> real) (x' : A) : (term781 A f x') = (term783 A f x').
Proof. exact (@lem7104230 real_add (@I (A -> real) f x')). Qed.
Lemma lem7104232 {A : Type'} (s : A -> Prop) (f : A -> real) : (term732 A s f) = (term732 A s f).
Proof. exact (eq_refl (term732 A s f)). Qed.
Lemma lem7104233 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term782 A x' s f) = (term784 A x' s f).
Proof. exact (MK_COMB (@lem7104231 A f x') (@lem7104232 A s f)). Qed.
Lemma lem7104235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104236 (f : real -> real) (x : real) : (f x) = (@I (real -> real) f x).
Proof. exact (@lem7104235 real real f x). Qed.
Lemma lem7104237 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term784 A x' s f) = (term785 A x' s f).
Proof. exact (@lem7104236 (term783 A f x') (term732 A s f)). Qed.
Lemma lem7104238 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term782 A x' s f) = (term785 A x' s f).
Proof. exact (TRANS (@lem7104233 A x' s f) (@lem7104237 A x' s f)). Qed.
Lemma lem7104239 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term362 A x' s f) = (term785 A x' s f).
Proof. exact (TRANS (@lem7104227 A x' s f) (@lem7104238 A x' s f)). Qed.
Lemma lem7104240 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104241 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term378 A x' s f) = (term786 A x' s f).
Proof. exact (MK_COMB (@lem7104199) (@lem7104239 A x' s f)). Qed.
Lemma lem7104242 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term379 A x' s f b) = (term787 A x' s f b).
Proof. exact (MK_COMB (@lem7104241 A x' s f) (@lem7104240 b)). Qed.
Lemma lem7104244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104245 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104244 real (real -> Prop) f x). Qed.
Lemma lem7104246 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term786 A x' s f) = (term788 A x' s f).
Proof. exact (@lem7104245 real_le (term785 A x' s f)). Qed.
Lemma lem7104247 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104248 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term787 A x' s f b) = (term789 A x' s f b).
Proof. exact (MK_COMB (@lem7104246 A x' s f) (@lem7104247 b)). Qed.
Lemma lem7104250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104251 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104250 real Prop f x). Qed.
Lemma lem7104252 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term789 A x' s f b) = (term790 A x' s f b).
Proof. exact (@lem7104251 (term788 A x' s f) b). Qed.
Lemma lem7104253 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term787 A x' s f b) = (term790 A x' s f b).
Proof. exact (TRANS (@lem7104248 A x' s f b) (@lem7104252 A x' s f b)). Qed.
Lemma lem7104254 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term379 A x' s f b) = (term790 A x' s f b).
Proof. exact (TRANS (@lem7104242 A x' s f b) (@lem7104253 A x' s f b)). Qed.
Lemma lem7104255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104256 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term489 A x' s f b) = (term791 A x' s f b).
Proof. exact (MK_COMB (@lem7104255) (@lem7104254 A x' s f b)). Qed.
Lemma lem7104257 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) : (term565 A x' s f x''' b) = (term792 A x' s f x''' b).
Proof. exact (MK_COMB (@lem7104256 A x' s f b) (@lem7104198 A x' s f x''' b)). Qed.
Lemma lem7104258 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7104264 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104265 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7104264 nat nat f x). Qed.
Lemma lem7104267 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7104265 NUMERAL 0). Qed.
Lemma lem7104268 : term10 = term712.
Proof. exact (MK_COMB (@lem7104259) (@lem7104267)). Qed.
Lemma lem7104270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104271 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7104270 nat real f x). Qed.
Lemma lem7104272 : term712 = term713.
Proof. exact (@lem7104271 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7104273 : term10 = term713.
Proof. exact (TRANS (@lem7104268) (@lem7104272)). Qed.
Lemma lem7104278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104279 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104278 A real f x). Qed.
Lemma lem7104281 {A : Type'} (f : A -> real) (x'' : A) : (f x'') = (@I (A -> real) f x'').
Proof. exact (@lem7104279 A f x''). Qed.
Lemma lem7104282 : term296 = term714.
Proof. exact (MK_COMB (@lem7104258) (@lem7104273)). Qed.
Lemma lem7104283 {A : Type'} (f : A -> real) (x'' : A) : (term271 A f x'') = (term793 A f x'').
Proof. exact (MK_COMB (@lem7104282) (@lem7104281 A f x'')). Qed.
Lemma lem7104285 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104286 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104285 real (real -> Prop) f x). Qed.
Lemma lem7104287 : term714 = term716.
Proof. exact (@lem7104286 real_le term713). Qed.
Lemma lem7104288 {A : Type'} (f : A -> real) (x'' : A) : (@I (A -> real) f x'') = (@I (A -> real) f x'').
Proof. exact (eq_refl (@I (A -> real) f x'')). Qed.
Lemma lem7104289 {A : Type'} (f : A -> real) (x'' : A) : (term793 A f x'') = (term794 A f x'').
Proof. exact (MK_COMB (@lem7104287) (@lem7104288 A f x'')). Qed.
Lemma lem7104291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104292 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104291 real Prop f x). Qed.
Lemma lem7104293 {A : Type'} (f : A -> real) (x'' : A) : (term794 A f x'') = (term795 A f x'').
Proof. exact (@lem7104292 term716 (@I (A -> real) f x'')). Qed.
Lemma lem7104294 {A : Type'} (f : A -> real) (x'' : A) : (term793 A f x'') = (term795 A f x'').
Proof. exact (TRANS (@lem7104289 A f x'') (@lem7104293 A f x'')). Qed.
Lemma lem7104295 {A : Type'} (f : A -> real) (x'' : A) : (term271 A f x'') = (term795 A f x'').
Proof. exact (TRANS (@lem7104283 A f x'') (@lem7104294 A f x'')). Qed.
Lemma lem7104296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104303 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104304 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104303 A (type686 A) f x). Qed.
Lemma lem7104305 {A : Type'} (x'' : A) : (@IN A x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'').
Proof. exact (@lem7104304 A (@IN A) x''). Qed.
Lemma lem7104306 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104307 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s).
Proof. exact (MK_COMB (@lem7104305 A x'') (@lem7104306 A s)). Qed.
Lemma lem7104309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104310 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104309 (A -> Prop) Prop f x). Qed.
Lemma lem7104311 {A : Type'} (x'' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s) = (term774 A x'' s).
Proof. exact (@lem7104310 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') s). Qed.
Lemma lem7104313 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (term774 A x'' s).
Proof. exact (TRANS (@lem7104307 A x'' s) (@lem7104311 A x'' s)). Qed.
Lemma lem7104314 {A : Type'} (x'' : A) (s : A -> Prop) : (term324 A x'' s) = (term796 A x'' s).
Proof. exact (MK_COMB (@lem7104296) (@lem7104313 A x'' s)). Qed.
Lemma lem7104323 {A : Type'} (x'' : A) (x' : A) : (term797 A x'' x') = (term797 A x'' x').
Proof. exact (eq_refl (term797 A x'' x')). Qed.
Lemma lem7104324 {A : Type'} (x' : A) (x'' : A) (s : A -> Prop) : (term473 A x' x'' s) = (term798 A x' x'' s).
Proof. exact (MK_COMB (@lem7104323 A x'' x') (@lem7104314 A x'' s)). Qed.
Lemma lem7104325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7104326 {A : Type'} (x' : A) (x'' : A) (s : A -> Prop) : (term475 A x' x'' s) = (term799 A x' x'' s).
Proof. exact (MK_COMB (@lem7104325) (@lem7104324 A x' x'' s)). Qed.
Lemma lem7104327 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term477 A x' s f x'') = (term800 A x' s f x'').
Proof. exact (MK_COMB (@lem7104326 A x' x'' s) (@lem7104295 A f x'')). Qed.
Lemma lem7104328 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term478 A x' s f) = (term801 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7104327 A x' s f x'')). Qed.
Lemma lem7104329 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104330 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term479 A x' s f) = (term802 A x' s f).
Proof. exact (MK_COMB (@lem7104329 A) (@lem7104328 A x' s f)). Qed.
Lemma lem7104331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104332 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term494 A x' s f) = (term803 A x' s f).
Proof. exact (MK_COMB (@lem7104331) (@lem7104330 A x' s f)). Qed.
Lemma lem7104333 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) : (term578 A x' s f x''' b) = (term804 A x' s f x''' b).
Proof. exact (MK_COMB (@lem7104332 A x' s f) (@lem7104257 A x' s f x''' b)). Qed.
Lemma lem7104338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104339 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104338 (A -> Prop) Prop f x). Qed.
Lemma lem7104341 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@I ((A -> Prop) -> Prop) (@FINITE A) s).
Proof. exact (@lem7104339 A (@FINITE A) s). Qed.
Lemma lem7104342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104350 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104349 A (type686 A) f x). Qed.
Lemma lem7104351 {A : Type'} (x' : A) : (@IN A x') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x').
Proof. exact (@lem7104350 A (@IN A) x'). Qed.
Lemma lem7104352 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104353 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s).
Proof. exact (MK_COMB (@lem7104351 A x') (@lem7104352 A s)). Qed.
Lemma lem7104355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104356 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104355 (A -> Prop) Prop f x). Qed.
Lemma lem7104357 {A : Type'} (x' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x' s) = (term774 A x' s).
Proof. exact (@lem7104356 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x') s). Qed.
Lemma lem7104359 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (term774 A x' s).
Proof. exact (TRANS (@lem7104353 A x' s) (@lem7104357 A x' s)). Qed.
Lemma lem7104360 {A : Type'} (x' : A) (s : A -> Prop) : (term324 A x' s) = (term796 A x' s).
Proof. exact (MK_COMB (@lem7104342) (@lem7104359 A x' s)). Qed.
Lemma lem7104361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104362 {A : Type'} (x' : A) (s : A -> Prop) : (term805 A x' s) = (term806 A x' s).
Proof. exact (MK_COMB (@lem7104361) (@lem7104360 A x' s)). Qed.
Lemma lem7104363 {A : Type'} (x' : A) (s : A -> Prop) : (term235 A x' s) = (term807 A x' s).
Proof. exact (MK_COMB (@lem7104362 A x' s) (@lem7104341 A s)). Qed.
Lemma lem7104364 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104369 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104371 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104369 A real f x). Qed.
Lemma lem7104372 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104373 {A : Type'} (f : A -> real) (x : A) : (term766 A f x) = (term767 A f x).
Proof. exact (MK_COMB (@lem7104364) (@lem7104371 A f x)). Qed.
Lemma lem7104374 {A : Type'} (f : A -> real) (x : A) (b : real) : (term300 A f x b) = (term768 A f x b).
Proof. exact (MK_COMB (@lem7104373 A f x) (@lem7104372 b)). Qed.
Lemma lem7104376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104377 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104376 real (real -> Prop) f x). Qed.
Lemma lem7104378 {A : Type'} (f : A -> real) (x : A) : (term767 A f x) = (term769 A f x).
Proof. exact (@lem7104377 real_le (@I (A -> real) f x)). Qed.
Lemma lem7104379 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104380 {A : Type'} (f : A -> real) (x : A) (b : real) : (term768 A f x b) = (term770 A f x b).
Proof. exact (MK_COMB (@lem7104378 A f x) (@lem7104379 b)). Qed.
Lemma lem7104382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104383 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104382 real Prop f x). Qed.
Lemma lem7104384 {A : Type'} (f : A -> real) (x : A) (b : real) : (term770 A f x b) = (term771 A f x b).
Proof. exact (@lem7104383 (term769 A f x) b). Qed.
Lemma lem7104385 {A : Type'} (f : A -> real) (x : A) (b : real) : (term768 A f x b) = (term771 A f x b).
Proof. exact (TRANS (@lem7104380 A f x b) (@lem7104384 A f x b)). Qed.
Lemma lem7104386 {A : Type'} (f : A -> real) (x : A) (b : real) : (term300 A f x b) = (term771 A f x b).
Proof. exact (TRANS (@lem7104374 A f x b) (@lem7104385 A f x b)). Qed.
Lemma lem7104387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104394 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104395 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104394 A (type686 A) f x). Qed.
Lemma lem7104396 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7104395 A (@IN A) x). Qed.
Lemma lem7104397 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104398 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7104396 A x) (@lem7104397 A s)). Qed.
Lemma lem7104400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104401 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104400 (A -> Prop) Prop f x). Qed.
Lemma lem7104402 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term774 A x s).
Proof. exact (@lem7104401 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7104404 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term774 A x s).
Proof. exact (TRANS (@lem7104398 A x s) (@lem7104402 A x s)). Qed.
Lemma lem7104405 {A : Type'} (x : A) (s : A -> Prop) : (term324 A x s) = (term796 A x s).
Proof. exact (MK_COMB (@lem7104387) (@lem7104404 A x s)). Qed.
Lemma lem7104406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7104407 {A : Type'} (x : A) (s : A -> Prop) : (term808 A x s) = (term809 A x s).
Proof. exact (MK_COMB (@lem7104406) (@lem7104405 A x s)). Qed.
Lemma lem7104408 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term460 A s f x b) = (term810 A s f x b).
Proof. exact (MK_COMB (@lem7104407 A x s) (@lem7104386 A f x b)). Qed.
Lemma lem7104409 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term461 A s f b) = (term811 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7104408 A s f x b)). Qed.
Lemma lem7104410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104411 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term462 A s f b) = (term812 A s f b).
Proof. exact (MK_COMB (@lem7104410 A) (@lem7104409 A s f b)). Qed.
Lemma lem7104412 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104413 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104421 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7104420 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7104422 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7104421 A (@sum A) s). Qed.
Lemma lem7104423 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7104424 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7104422 A s) (@lem7104423 A f)). Qed.
Lemma lem7104426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104427 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7104426 (A -> real) real f x). Qed.
Lemma lem7104428 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term732 A s f).
Proof. exact (@lem7104427 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7104430 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term732 A s f).
Proof. exact (TRANS (@lem7104424 A s f) (@lem7104428 A s f)). Qed.
Lemma lem7104431 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104432 {A : Type'} (s : A -> Prop) (f : A -> real) : (term813 A s f) = (term814 A s f).
Proof. exact (MK_COMB (@lem7104413) (@lem7104430 A s f)). Qed.
Lemma lem7104433 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term219 A s f b) = (term815 A s f b).
Proof. exact (MK_COMB (@lem7104432 A s f) (@lem7104431 b)). Qed.
Lemma lem7104435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104436 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104435 real (real -> Prop) f x). Qed.
Lemma lem7104437 {A : Type'} (s : A -> Prop) (f : A -> real) : (term814 A s f) = (term816 A s f).
Proof. exact (@lem7104436 real_le (term732 A s f)). Qed.
Lemma lem7104438 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7104439 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term815 A s f b) = (term817 A s f b).
Proof. exact (MK_COMB (@lem7104437 A s f) (@lem7104438 b)). Qed.
Lemma lem7104441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104442 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104441 real Prop f x). Qed.
Lemma lem7104443 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term817 A s f b) = (term818 A s f b).
Proof. exact (@lem7104442 (term816 A s f) b). Qed.
Lemma lem7104444 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term815 A s f b) = (term818 A s f b).
Proof. exact (TRANS (@lem7104439 A s f b) (@lem7104443 A s f b)). Qed.
Lemma lem7104445 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term219 A s f b) = (term818 A s f b).
Proof. exact (TRANS (@lem7104433 A s f b) (@lem7104444 A s f b)). Qed.
Lemma lem7104446 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term819 A s f b) = (term820 A s f b).
Proof. exact (MK_COMB (@lem7104412) (@lem7104445 A s f b)). Qed.
Lemma lem7104447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7104448 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term463 A s f b) = (term821 A s f b).
Proof. exact (MK_COMB (@lem7104447) (@lem7104446 A s f b)). Qed.
Lemma lem7104449 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term465 A s f b) = (term822 A s f b).
Proof. exact (MK_COMB (@lem7104448 A s f b) (@lem7104411 A s f b)). Qed.
Lemma lem7104450 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7104451 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7104452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7104457 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104458 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7104457 nat nat f x). Qed.
Lemma lem7104460 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7104458 NUMERAL 0). Qed.
Lemma lem7104461 : term10 = term712.
Proof. exact (MK_COMB (@lem7104452) (@lem7104460)). Qed.
Lemma lem7104463 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104464 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7104463 nat real f x). Qed.
Lemma lem7104465 : term712 = term713.
Proof. exact (@lem7104464 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7104466 : term10 = term713.
Proof. exact (TRANS (@lem7104461) (@lem7104465)). Qed.
Lemma lem7104471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104472 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7104471 A real f x). Qed.
Lemma lem7104474 {A : Type'} (f : A -> real) (x'' : A) : (f x'') = (@I (A -> real) f x'').
Proof. exact (@lem7104472 A f x''). Qed.
Lemma lem7104475 : term296 = term714.
Proof. exact (MK_COMB (@lem7104451) (@lem7104466)). Qed.
Lemma lem7104476 {A : Type'} (f : A -> real) (x'' : A) : (term271 A f x'') = (term793 A f x'').
Proof. exact (MK_COMB (@lem7104475) (@lem7104474 A f x'')). Qed.
Lemma lem7104478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104479 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7104478 real (real -> Prop) f x). Qed.
Lemma lem7104480 : term714 = term716.
Proof. exact (@lem7104479 real_le term713). Qed.
Lemma lem7104481 {A : Type'} (f : A -> real) (x'' : A) : (@I (A -> real) f x'') = (@I (A -> real) f x'').
Proof. exact (eq_refl (@I (A -> real) f x'')). Qed.
Lemma lem7104482 {A : Type'} (f : A -> real) (x'' : A) : (term793 A f x'') = (term794 A f x'').
Proof. exact (MK_COMB (@lem7104480) (@lem7104481 A f x'')). Qed.
Lemma lem7104484 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104485 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7104484 real Prop f x). Qed.
Lemma lem7104486 {A : Type'} (f : A -> real) (x'' : A) : (term794 A f x'') = (term795 A f x'').
Proof. exact (@lem7104485 term716 (@I (A -> real) f x'')). Qed.
Lemma lem7104487 {A : Type'} (f : A -> real) (x'' : A) : (term793 A f x'') = (term795 A f x'').
Proof. exact (TRANS (@lem7104482 A f x'') (@lem7104486 A f x'')). Qed.
Lemma lem7104488 {A : Type'} (f : A -> real) (x'' : A) : (term271 A f x'') = (term795 A f x'').
Proof. exact (TRANS (@lem7104476 A f x'') (@lem7104487 A f x'')). Qed.
Lemma lem7104489 {A : Type'} (f : A -> real) (x'' : A) : (term823 A f x'') = (term824 A f x'').
Proof. exact (MK_COMB (@lem7104450) (@lem7104488 A f x'')). Qed.
Lemma lem7104496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104497 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7104496 A (type686 A) f x). Qed.
Lemma lem7104498 {A : Type'} (x'' : A) : (@IN A x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'').
Proof. exact (@lem7104497 A (@IN A) x''). Qed.
Lemma lem7104499 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7104500 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s).
Proof. exact (MK_COMB (@lem7104498 A x'') (@lem7104499 A s)). Qed.
Lemma lem7104502 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7104503 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7104502 (A -> Prop) Prop f x). Qed.
Lemma lem7104504 {A : Type'} (x'' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s) = (term774 A x'' s).
Proof. exact (@lem7104503 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') s). Qed.
Lemma lem7104506 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (term774 A x'' s).
Proof. exact (TRANS (@lem7104500 A x'' s) (@lem7104504 A x'' s)). Qed.
Lemma lem7104507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104508 {A : Type'} (x'' : A) (s : A -> Prop) : (term825 A x'' s) = (term826 A x'' s).
Proof. exact (MK_COMB (@lem7104507) (@lem7104506 A x'' s)). Qed.
Lemma lem7104509 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) : (term450 A s f x'') = (term827 A s f x'').
Proof. exact (MK_COMB (@lem7104508 A x'' s) (@lem7104489 A f x'')). Qed.
Lemma lem7104510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7104511 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) : (term529 A s f x'') = (term828 A s f x'').
Proof. exact (MK_COMB (@lem7104510) (@lem7104509 A s f x'')). Qed.
Lemma lem7104512 {A : Type'} (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term531 A x'' s f b) = (term829 A x'' s f b).
Proof. exact (MK_COMB (@lem7104511 A s f x'') (@lem7104449 A s f b)). Qed.
Lemma lem7104513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104514 {A : Type'} (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term548 A x'' s f b) = (term830 A x'' s f b).
Proof. exact (MK_COMB (@lem7104513) (@lem7104512 A x'' s f b)). Qed.
Lemma lem7104515 {A : Type'} (x'' : A) (f : A -> real) (b : real) (x' : A) (s : A -> Prop) : (term550 A x'' f b x' s) = (term831 A x'' f b x' s).
Proof. exact (MK_COMB (@lem7104514 A x'' s f b) (@lem7104363 A x' s)). Qed.
Lemma lem7104516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7104517 {A : Type'} (x'' : A) (f : A -> real) (b : real) (x' : A) (s : A -> Prop) : (term592 A x'' f b x' s) = (term832 A x'' f b x' s).
Proof. exact (MK_COMB (@lem7104516) (@lem7104515 A x'' f b x' s)). Qed.
Lemma lem7104518 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) : (term606 A x'' x' s f x''' b) = (term833 A x'' x' s f x''' b).
Proof. exact (MK_COMB (@lem7104517 A x'' f b x' s) (@lem7104333 A x' s f x''' b)). Qed.
Lemma lem7104519 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term833 A x'' x' s f x''' b.
Proof. exact (EQ_MP (@lem7104518 A x'' x' s f x''' b) (@lem7103838 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104520 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term804 A x' s f x''' b.
Proof. exact (proj2 (@lem7104519 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104521 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term831 A x'' f b x' s.
Proof. exact (proj1 (@lem7104519 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104522 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term792 A x' s f x''' b.
Proof. exact (proj2 (@lem7104520 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104523 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term802 A x' s f.
Proof. exact (proj1 (@lem7104520 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104524 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term779 A x' s f x''' b.
Proof. exact (proj2 (@lem7104522 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104527 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term776 A x' x''' s.
Proof. exact (proj1 (@lem7104524 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104529 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term829 A x'' s f b.
Proof. exact (proj1 (@lem7104521 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104532 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term827 A s f x''.
Proof. exact (h1). Qed.
Lemma lem7104533 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term822 A s f b) : term822 A s f b.
Proof. exact (h1). Qed.
Lemma lem7104539 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term812 A s f b.
Proof. exact (h1). Qed.
Lemma lem7104628 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term800 A x' s f x'') = (term834 A x' s f x'').
Proof. exact (@lem19699 (term835 A x'' x') (term796 A x'' s) (term795 A f x'')). Qed.
Lemma lem7104629 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term801 A x' s f) = (term836 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7104628 A x' s f x'')). Qed.
Lemma lem7104630 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104632 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term802 A x' s f) = (term837 A x' s f).
Proof. exact (MK_COMB (@lem7104630 A) (@lem7104629 A x' s f)). Qed.
Lemma lem7104633 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term837 A x' s f.
Proof. exact (EQ_MP (@lem7104632 A x' s f) (@lem7104523 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104746 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term800 A x' s f x'') = (term834 A x' s f x'').
Proof. exact (@lem19699 (term835 A x'' x') (term796 A x'' s) (term795 A f x'')). Qed.
Lemma lem7104747 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term801 A x' s f) = (term836 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7104746 A x' s f x'')). Qed.
Lemma lem7104748 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104750 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term802 A x' s f) = (term837 A x' s f).
Proof. exact (MK_COMB (@lem7104748 A) (@lem7104747 A x' s f)). Qed.
Lemma lem7104751 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term837 A x' s f.
Proof. exact (EQ_MP (@lem7104750 A x' s f) (@lem7104523 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104809 (x : real) (y : real) (b : real) : (term725 x y b) = (term838 x y b).
Proof. exact (@lem19490 (term699 x b) (term723 x y b) (term699 y b)). Qed.
Lemma lem7104810 (x : real) (y : real) : (term726 x y) = (term839 x y).
Proof. exact (fun_ext (fun b : real => @lem7104809 x y b)). Qed.
Lemma lem7104811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104812 (x : real) (y : real) : (term727 x y) = (term840 x y).
Proof. exact (MK_COMB (@lem7104811) (@lem7104810 x y)). Qed.
Lemma lem7104813 (x : real) : (term728 x) = (term841 x).
Proof. exact (fun_ext (fun y : real => @lem7104812 x y)). Qed.
Lemma lem7104814 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104815 (x : real) : (term729 x) = (term842 x).
Proof. exact (MK_COMB (@lem7104814) (@lem7104813 x)). Qed.
Lemma lem7104816 : term730 = term843.
Proof. exact (fun_ext (fun x : real => @lem7104815 x)). Qed.
Lemma lem7104817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104819 : term731 = term844.
Proof. exact (MK_COMB (@lem7104817) (@lem7104816)). Qed.
Lemma lem7104820 (h1 : term181) : term844.
Proof. exact (EQ_MP (@lem7104819) (@lem7103995 h1)). Qed.
Lemma lem7104838 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) : (term760 A x s f) = (term845 A x s f).
Proof. exact (@lem19699 (term752 A x f s) (term745 A x f s) (term735 A s f)). Qed.
Lemma lem7104839 {A : Type'} (x : type710 A) (f : A -> real) : (term762 A x f) = (term846 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7104838 A x s f)). Qed.
Lemma lem7104840 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7104841 {A : Type'} (x : type710 A) (f : A -> real) : (term763 A x f) = (term847 A x f).
Proof. exact (MK_COMB (@lem7104840 A) (@lem7104839 A x f)). Qed.
Lemma lem7104842 {A : Type'} (x : type710 A) : (term764 A x) = (term848 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7104841 A x f)). Qed.
Lemma lem7104843 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7104845 {A : Type'} (x : type710 A) : (term765 A x) = (term849 A x).
Proof. exact (MK_COMB (@lem7104843 A) (@lem7104842 A x)). Qed.
Lemma lem7104846 {A : Type'} (x : type710 A) (h1 : term695 A x) : term849 A x.
Proof. exact (EQ_MP (@lem7104845 A x) (@lem7104144 A x h1)). Qed.
Lemma lem7104864 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term800 A x' s f x'') = (term834 A x' s f x'').
Proof. exact (@lem19699 (term835 A x'' x') (term796 A x'' s) (term795 A f x'')). Qed.
Lemma lem7104865 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term801 A x' s f) = (term836 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7104864 A x' s f x'')). Qed.
Lemma lem7104866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104868 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term802 A x' s f) = (term837 A x' s f).
Proof. exact (MK_COMB (@lem7104866 A) (@lem7104865 A x' s f)). Qed.
Lemma lem7104869 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term837 A x' s f.
Proof. exact (EQ_MP (@lem7104868 A x' s f) (@lem7104523 A x'' x' s f x''' b h1)). Qed.
Lemma lem7104889 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term820 A s f b.
Proof. exact (h1). Qed.
Lemma lem7104923 (x : real) (y : real) (b : real) : (term725 x y b) = (term838 x y b).
Proof. exact (@lem19490 (term699 x b) (term723 x y b) (term699 y b)). Qed.
Lemma lem7104924 (x : real) (y : real) : (term726 x y) = (term839 x y).
Proof. exact (fun_ext (fun b : real => @lem7104923 x y b)). Qed.
Lemma lem7104925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104926 (x : real) (y : real) : (term727 x y) = (term840 x y).
Proof. exact (MK_COMB (@lem7104925) (@lem7104924 x y)). Qed.
Lemma lem7104927 (x : real) : (term728 x) = (term841 x).
Proof. exact (fun_ext (fun y : real => @lem7104926 x y)). Qed.
Lemma lem7104928 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104929 (x : real) : (term729 x) = (term842 x).
Proof. exact (MK_COMB (@lem7104928) (@lem7104927 x)). Qed.
Lemma lem7104930 : term730 = term843.
Proof. exact (fun_ext (fun x : real => @lem7104929 x)). Qed.
Lemma lem7104931 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7104933 : term731 = term844.
Proof. exact (MK_COMB (@lem7104931) (@lem7104930)). Qed.
Lemma lem7104934 (h1 : term181) : term844.
Proof. exact (EQ_MP (@lem7104933) (@lem7103995 h1)). Qed.
Lemma lem7104952 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) : (term760 A x s f) = (term845 A x s f).
Proof. exact (@lem19699 (term752 A x f s) (term745 A x f s) (term735 A s f)). Qed.
Lemma lem7104953 {A : Type'} (x : type710 A) (f : A -> real) : (term762 A x f) = (term846 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7104952 A x s f)). Qed.
Lemma lem7104954 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7104955 {A : Type'} (x : type710 A) (f : A -> real) : (term763 A x f) = (term847 A x f).
Proof. exact (MK_COMB (@lem7104954 A) (@lem7104953 A x f)). Qed.
Lemma lem7104956 {A : Type'} (x : type710 A) : (term764 A x) = (term848 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7104955 A x f)). Qed.
Lemma lem7104957 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7104959 {A : Type'} (x : type710 A) : (term765 A x) = (term849 A x).
Proof. exact (MK_COMB (@lem7104957 A) (@lem7104956 A x)). Qed.
Lemma lem7104960 {A : Type'} (x : type710 A) (h1 : term695 A x) : term849 A x.
Proof. exact (EQ_MP (@lem7104959 A x) (@lem7104144 A x h1)). Qed.
Lemma lem7104978 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term800 A x' s f x'') = (term834 A x' s f x'').
Proof. exact (@lem19699 (term835 A x'' x') (term796 A x'' s) (term795 A f x'')). Qed.
Lemma lem7104979 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term801 A x' s f) = (term836 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7104978 A x' s f x'')). Qed.
Lemma lem7104980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7104982 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term802 A x' s f) = (term837 A x' s f).
Proof. exact (MK_COMB (@lem7104980 A) (@lem7104979 A x' s f)). Qed.
Lemma lem7104983 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term837 A x' s f.
Proof. exact (EQ_MP (@lem7104982 A x' s f) (@lem7104523 A x'' x' s f x''' b h1)). Qed.
Lemma lem7105003 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term820 A s f b.
Proof. exact (h1). Qed.
Lemma lem7105037 (x : real) (y : real) (b : real) : (term725 x y b) = (term838 x y b).
Proof. exact (@lem19490 (term699 x b) (term723 x y b) (term699 y b)). Qed.
Lemma lem7105038 (x : real) (y : real) : (term726 x y) = (term839 x y).
Proof. exact (fun_ext (fun b : real => @lem7105037 x y b)). Qed.
Lemma lem7105039 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7105040 (x : real) (y : real) : (term727 x y) = (term840 x y).
Proof. exact (MK_COMB (@lem7105039) (@lem7105038 x y)). Qed.
Lemma lem7105041 (x : real) : (term728 x) = (term841 x).
Proof. exact (fun_ext (fun y : real => @lem7105040 x y)). Qed.
Lemma lem7105042 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7105043 (x : real) : (term729 x) = (term842 x).
Proof. exact (MK_COMB (@lem7105042) (@lem7105041 x)). Qed.
Lemma lem7105044 : term730 = term843.
Proof. exact (fun_ext (fun x : real => @lem7105043 x)). Qed.
Lemma lem7105045 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7105047 : term731 = term844.
Proof. exact (MK_COMB (@lem7105045) (@lem7105044)). Qed.
Lemma lem7105048 (h1 : term181) : term844.
Proof. exact (EQ_MP (@lem7105047) (@lem7103995 h1)). Qed.
Lemma lem7105066 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) : (term760 A x s f) = (term845 A x s f).
Proof. exact (@lem19699 (term752 A x f s) (term745 A x f s) (term735 A s f)). Qed.
Lemma lem7105067 {A : Type'} (x : type710 A) (f : A -> real) : (term762 A x f) = (term846 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7105066 A x s f)). Qed.
Lemma lem7105068 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7105069 {A : Type'} (x : type710 A) (f : A -> real) : (term763 A x f) = (term847 A x f).
Proof. exact (MK_COMB (@lem7105068 A) (@lem7105067 A x f)). Qed.
Lemma lem7105070 {A : Type'} (x : type710 A) : (term764 A x) = (term848 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7105069 A x f)). Qed.
Lemma lem7105071 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7105073 {A : Type'} (x : type710 A) : (term765 A x) = (term849 A x).
Proof. exact (MK_COMB (@lem7105071 A) (@lem7105070 A x)). Qed.
Lemma lem7105074 {A : Type'} (x : type710 A) (h1 : term695 A x) : term849 A x.
Proof. exact (EQ_MP (@lem7105073 A x) (@lem7104144 A x h1)). Qed.
Lemma lem7105092 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (x'' : A) : (term800 A x' s f x'') = (term834 A x' s f x'').
Proof. exact (@lem19699 (term835 A x'' x') (term796 A x'' s) (term795 A f x'')). Qed.
Lemma lem7105093 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term801 A x' s f) = (term836 A x' s f).
Proof. exact (fun_ext (fun x'' : A => @lem7105092 A x' s f x'')). Qed.
Lemma lem7105094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7105096 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term802 A x' s f) = (term837 A x' s f).
Proof. exact (MK_COMB (@lem7105094 A) (@lem7105093 A x' s f)). Qed.
Lemma lem7105097 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term837 A x' s f.
Proof. exact (EQ_MP (@lem7105096 A x' s f) (@lem7104523 A x'' x' s f x''' b h1)). Qed.
Lemma lem7105130 {A : Type'} (x''' : A) (x' : A) (h1 : x''' = x') : x''' = x'.
Proof. exact (h1). Qed.
Lemma lem7105244 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term810 A s f x b) = (term810 A s f x b).
Proof. exact (eq_refl (term810 A s f x b)). Qed.
Lemma lem7105245 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term811 A s f b) = (term811 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7105244 A s f x b)). Qed.
Lemma lem7105246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7105248 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term812 A s f b) = (term812 A s f b).
Proof. exact (MK_COMB (@lem7105246 A) (@lem7105245 A s f b)). Qed.
Lemma lem7105249 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term812 A s f b.
Proof. exact (EQ_MP (@lem7105248 A s f b) (@lem7104539 A s f b h1)). Qed.
Lemma lem7105253 {A : Type'} (x''' : A) (s : A -> Prop) (h1 : term774 A x''' s) : term774 A x''' s.
Proof. exact (h1). Qed.
Lemma lem7105269 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term850 A x' s f _94619.
Proof. exact (@lem7104633 A x'' x' s f x''' b h1 _94619). Qed.
Lemma lem7105270 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (_94619 : A) : (term850 A x' s f _94619) = (term834 A x' s f _94619).
Proof. exact (eq_refl (term850 A x' s f _94619)). Qed.
Lemma lem7105271 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term834 A x' s f _94619.
Proof. exact (EQ_MP (@lem7105270 A x' s f _94619) (@lem7105269 A _94619 x'' x' s f x''' b h1)). Qed.
Lemma lem7105287 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term850 A x' s f _94625.
Proof. exact (@lem7104751 A x'' x' s f x''' b h1 _94625). Qed.
Lemma lem7105288 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (_94625 : A) : (term850 A x' s f _94625) = (term834 A x' s f _94625).
Proof. exact (eq_refl (term850 A x' s f _94625)). Qed.
Lemma lem7105289 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term834 A x' s f _94625.
Proof. exact (EQ_MP (@lem7105288 A x' s f _94625) (@lem7105287 A _94625 x'' x' s f x''' b h1)). Qed.
Lemma lem7105290 (_94626 : real) (h1 : term181) : term851 _94626.
Proof. exact (@lem7104820 h1 _94626). Qed.
Lemma lem7105291 (_94626 : real) : (term851 _94626) = (term842 _94626).
Proof. exact (eq_refl (term851 _94626)). Qed.
Lemma lem7105292 (_94626 : real) (h1 : term181) : term842 _94626.
Proof. exact (EQ_MP (@lem7105291 _94626) (@lem7105290 _94626 h1)). Qed.
Lemma lem7105293 (_94626 : real) (_94627 : real) (h1 : term181) : term852 _94626 _94627.
Proof. exact (@lem7105292 _94626 h1 _94627). Qed.
Lemma lem7105294 (_94626 : real) (_94627 : real) : (term852 _94626 _94627) = (term840 _94626 _94627).
Proof. exact (eq_refl (term852 _94626 _94627)). Qed.
Lemma lem7105295 (_94626 : real) (_94627 : real) (h1 : term181) : term840 _94626 _94627.
Proof. exact (EQ_MP (@lem7105294 _94626 _94627) (@lem7105293 _94626 _94627 h1)). Qed.
Lemma lem7105296 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term853 _94626 _94627 _94628.
Proof. exact (@lem7105295 _94626 _94627 h1 _94628). Qed.
Lemma lem7105297 (_94626 : real) (_94627 : real) (_94628 : real) : (term853 _94626 _94627 _94628) = (term838 _94626 _94627 _94628).
Proof. exact (eq_refl (term853 _94626 _94627 _94628)). Qed.
Lemma lem7105298 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term838 _94626 _94627 _94628.
Proof. exact (EQ_MP (@lem7105297 _94626 _94627 _94628) (@lem7105296 _94626 _94627 _94628 h1)). Qed.
Lemma lem7105299 {A : Type'} (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term854 A x _94629.
Proof. exact (@lem7104846 A x h1 _94629). Qed.
Lemma lem7105300 {A : Type'} (x : type710 A) (_94629 : A -> real) : (term854 A x _94629) = (term847 A x _94629).
Proof. exact (eq_refl (term854 A x _94629)). Qed.
Lemma lem7105301 {A : Type'} (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term847 A x _94629.
Proof. exact (EQ_MP (@lem7105300 A x _94629) (@lem7105299 A _94629 x h1)). Qed.
Lemma lem7105302 {A : Type'} (_94629 : A -> real) (_94630 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term855 A x _94629 _94630.
Proof. exact (@lem7105301 A _94629 x h1 _94630). Qed.
Lemma lem7105303 {A : Type'} (x : type710 A) (_94630 : A -> Prop) (_94629 : A -> real) : (term855 A x _94629 _94630) = (term845 A x _94630 _94629).
Proof. exact (eq_refl (term855 A x _94629 _94630)). Qed.
Lemma lem7105304 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term845 A x _94630 _94629.
Proof. exact (EQ_MP (@lem7105303 A x _94630 _94629) (@lem7105302 A _94629 _94630 x h1)). Qed.
Lemma lem7105305 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term850 A x' s f _94631.
Proof. exact (@lem7104869 A x'' x' s f x''' b h1 _94631). Qed.
Lemma lem7105306 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (_94631 : A) : (term850 A x' s f _94631) = (term834 A x' s f _94631).
Proof. exact (eq_refl (term850 A x' s f _94631)). Qed.
Lemma lem7105307 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term834 A x' s f _94631.
Proof. exact (EQ_MP (@lem7105306 A x' s f _94631) (@lem7105305 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7105308 (_94632 : real) (h1 : term181) : term851 _94632.
Proof. exact (@lem7104934 h1 _94632). Qed.
Lemma lem7105309 (_94632 : real) : (term851 _94632) = (term842 _94632).
Proof. exact (eq_refl (term851 _94632)). Qed.
Lemma lem7105310 (_94632 : real) (h1 : term181) : term842 _94632.
Proof. exact (EQ_MP (@lem7105309 _94632) (@lem7105308 _94632 h1)). Qed.
Lemma lem7105311 (_94632 : real) (_94633 : real) (h1 : term181) : term852 _94632 _94633.
Proof. exact (@lem7105310 _94632 h1 _94633). Qed.
Lemma lem7105312 (_94632 : real) (_94633 : real) : (term852 _94632 _94633) = (term840 _94632 _94633).
Proof. exact (eq_refl (term852 _94632 _94633)). Qed.
Lemma lem7105313 (_94632 : real) (_94633 : real) (h1 : term181) : term840 _94632 _94633.
Proof. exact (EQ_MP (@lem7105312 _94632 _94633) (@lem7105311 _94632 _94633 h1)). Qed.
Lemma lem7105314 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term853 _94632 _94633 _94634.
Proof. exact (@lem7105313 _94632 _94633 h1 _94634). Qed.
Lemma lem7105315 (_94632 : real) (_94633 : real) (_94634 : real) : (term853 _94632 _94633 _94634) = (term838 _94632 _94633 _94634).
Proof. exact (eq_refl (term853 _94632 _94633 _94634)). Qed.
Lemma lem7105316 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term838 _94632 _94633 _94634.
Proof. exact (EQ_MP (@lem7105315 _94632 _94633 _94634) (@lem7105314 _94632 _94633 _94634 h1)). Qed.
Lemma lem7105317 {A : Type'} (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term854 A x _94635.
Proof. exact (@lem7104960 A x h1 _94635). Qed.
Lemma lem7105318 {A : Type'} (x : type710 A) (_94635 : A -> real) : (term854 A x _94635) = (term847 A x _94635).
Proof. exact (eq_refl (term854 A x _94635)). Qed.
Lemma lem7105319 {A : Type'} (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term847 A x _94635.
Proof. exact (EQ_MP (@lem7105318 A x _94635) (@lem7105317 A _94635 x h1)). Qed.
Lemma lem7105320 {A : Type'} (_94635 : A -> real) (_94636 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term855 A x _94635 _94636.
Proof. exact (@lem7105319 A _94635 x h1 _94636). Qed.
Lemma lem7105321 {A : Type'} (x : type710 A) (_94636 : A -> Prop) (_94635 : A -> real) : (term855 A x _94635 _94636) = (term845 A x _94636 _94635).
Proof. exact (eq_refl (term855 A x _94635 _94636)). Qed.
Lemma lem7105322 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term845 A x _94636 _94635.
Proof. exact (EQ_MP (@lem7105321 A x _94636 _94635) (@lem7105320 A _94635 _94636 x h1)). Qed.
Lemma lem7105323 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term850 A x' s f _94637.
Proof. exact (@lem7104983 A x'' x' s f x''' b h1 _94637). Qed.
Lemma lem7105324 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (_94637 : A) : (term850 A x' s f _94637) = (term834 A x' s f _94637).
Proof. exact (eq_refl (term850 A x' s f _94637)). Qed.
Lemma lem7105325 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term834 A x' s f _94637.
Proof. exact (EQ_MP (@lem7105324 A x' s f _94637) (@lem7105323 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7105326 (_94638 : real) (h1 : term181) : term851 _94638.
Proof. exact (@lem7105048 h1 _94638). Qed.
Lemma lem7105327 (_94638 : real) : (term851 _94638) = (term842 _94638).
Proof. exact (eq_refl (term851 _94638)). Qed.
Lemma lem7105328 (_94638 : real) (h1 : term181) : term842 _94638.
Proof. exact (EQ_MP (@lem7105327 _94638) (@lem7105326 _94638 h1)). Qed.
Lemma lem7105329 (_94638 : real) (_94639 : real) (h1 : term181) : term852 _94638 _94639.
Proof. exact (@lem7105328 _94638 h1 _94639). Qed.
Lemma lem7105330 (_94638 : real) (_94639 : real) : (term852 _94638 _94639) = (term840 _94638 _94639).
Proof. exact (eq_refl (term852 _94638 _94639)). Qed.
Lemma lem7105331 (_94638 : real) (_94639 : real) (h1 : term181) : term840 _94638 _94639.
Proof. exact (EQ_MP (@lem7105330 _94638 _94639) (@lem7105329 _94638 _94639 h1)). Qed.
Lemma lem7105332 (_94638 : real) (_94639 : real) (_94640 : real) (h1 : term181) : term853 _94638 _94639 _94640.
Proof. exact (@lem7105331 _94638 _94639 h1 _94640). Qed.
Lemma lem7105333 (_94638 : real) (_94639 : real) (_94640 : real) : (term853 _94638 _94639 _94640) = (term838 _94638 _94639 _94640).
Proof. exact (eq_refl (term853 _94638 _94639 _94640)). Qed.
Lemma lem7105334 (_94638 : real) (_94639 : real) (_94640 : real) (h1 : term181) : term838 _94638 _94639 _94640.
Proof. exact (EQ_MP (@lem7105333 _94638 _94639 _94640) (@lem7105332 _94638 _94639 _94640 h1)). Qed.
Lemma lem7105335 {A : Type'} (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term854 A x _94641.
Proof. exact (@lem7105074 A x h1 _94641). Qed.
Lemma lem7105336 {A : Type'} (x : type710 A) (_94641 : A -> real) : (term854 A x _94641) = (term847 A x _94641).
Proof. exact (eq_refl (term854 A x _94641)). Qed.
Lemma lem7105337 {A : Type'} (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term847 A x _94641.
Proof. exact (EQ_MP (@lem7105336 A x _94641) (@lem7105335 A _94641 x h1)). Qed.
Lemma lem7105338 {A : Type'} (_94641 : A -> real) (_94642 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term855 A x _94641 _94642.
Proof. exact (@lem7105337 A _94641 x h1 _94642). Qed.
Lemma lem7105339 {A : Type'} (x : type710 A) (_94642 : A -> Prop) (_94641 : A -> real) : (term855 A x _94641 _94642) = (term845 A x _94642 _94641).
Proof. exact (eq_refl (term855 A x _94641 _94642)). Qed.
Lemma lem7105340 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term845 A x _94642 _94641.
Proof. exact (EQ_MP (@lem7105339 A x _94642 _94641) (@lem7105338 A _94641 _94642 x h1)). Qed.
Lemma lem7105341 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term850 A x' s f _94643.
Proof. exact (@lem7105097 A x'' x' s f x''' b h1 _94643). Qed.
Lemma lem7105342 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (_94643 : A) : (term850 A x' s f _94643) = (term834 A x' s f _94643).
Proof. exact (eq_refl (term850 A x' s f _94643)). Qed.
Lemma lem7105343 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term834 A x' s f _94643.
Proof. exact (EQ_MP (@lem7105342 A x' s f _94643) (@lem7105341 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7105365 {A : Type'} (_94651 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term856 A s f b _94651.
Proof. exact (@lem7105249 A s f b h1 _94651). Qed.
Lemma lem7105366 {A : Type'} (s : A -> Prop) (f : A -> real) (_94651 : A) (b : real) : (term856 A s f b _94651) = (term810 A s f _94651 b).
Proof. exact (eq_refl (term856 A s f b _94651)). Qed.
Lemma lem7105384 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term857 _94626 _94627 _94628.
Proof. exact (proj2 (@lem7105298 _94626 _94627 _94628 h1)). Qed.
Lemma lem7105390 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term857 _94632 _94633 _94634.
Proof. exact (proj2 (@lem7105316 _94632 _94633 _94634 h1)). Qed.
Lemma lem7105397 (_94639 : real) (_94638 : real) (_94640 : real) (h1 : term181) : term858 _94639 _94638 _94640.
Proof. exact (proj1 (@lem7105334 _94638 _94639 _94640 h1)). Qed.
Lemma lem7105489 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term824 A f x''.
Proof. exact (proj2 (@lem7104532 A s f x'' h1)). Qed.
Lemma lem7105503 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term859 A s f _94625.
Proof. exact (proj2 (@lem7105289 A _94625 x'' x' s f x''' b h1)). Qed.
Lemma lem7105561 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term820 A s f b.
Proof. exact (h1). Qed.
Lemma lem7105609 (_94626 : real) (_94627 : real) (_94628 : real) : (term857 _94626 _94627 _94628) = (term860 _94626 _94627 _94628).
Proof. exact (@lem7087519 (term720 _94626) (term722 _94626 _94627 _94628) (term699 _94627 _94628)). Qed.
Lemma lem7105616 (_94626 : real) (_94627 : real) (_94628 : real) : (term861 _94626 _94627 _94628) = (term862 _94626 _94627 _94628).
Proof. exact (@lem7087519 (term720 _94627) (term711 _94626 _94627 _94628) (term699 _94627 _94628)). Qed.
Lemma lem7105617 (_94626 : real) : (term721 _94626) = (term721 _94626).
Proof. exact (eq_refl (term721 _94626)). Qed.
Lemma lem7105620 (_94626 : real) (_94627 : real) (_94628 : real) : (term860 _94626 _94627 _94628) = (term863 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7105617 _94626) (@lem7105616 _94626 _94627 _94628)). Qed.
Lemma lem7105622 (_94626 : real) (_94627 : real) (_94628 : real) : (term857 _94626 _94627 _94628) = (term863 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7105609 _94626 _94627 _94628) (@lem7105620 _94626 _94627 _94628)). Qed.
Lemma lem7105633 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term820 A s f b.
Proof. exact (h1). Qed.
Lemma lem7105641 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term864 A x' f _94637.
Proof. exact (proj1 (@lem7105325 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7105647 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term859 A s f _94637.
Proof. exact (proj2 (@lem7105325 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7105653 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term865 A x _94636 _94635.
Proof. exact (proj1 (@lem7105322 A _94636 _94635 x h1)). Qed.
Lemma lem7105659 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term866 A x _94636 _94635.
Proof. exact (proj2 (@lem7105322 A _94636 _94635 x h1)). Qed.
Lemma lem7105681 (_94632 : real) (_94633 : real) (_94634 : real) : (term857 _94632 _94633 _94634) = (term860 _94632 _94633 _94634).
Proof. exact (@lem7087519 (term720 _94632) (term722 _94632 _94633 _94634) (term699 _94633 _94634)). Qed.
Lemma lem7105688 (_94632 : real) (_94633 : real) (_94634 : real) : (term861 _94632 _94633 _94634) = (term862 _94632 _94633 _94634).
Proof. exact (@lem7087519 (term720 _94633) (term711 _94632 _94633 _94634) (term699 _94633 _94634)). Qed.
Lemma lem7105689 (_94632 : real) : (term721 _94632) = (term721 _94632).
Proof. exact (eq_refl (term721 _94632)). Qed.
Lemma lem7105692 (_94632 : real) (_94633 : real) (_94634 : real) : (term860 _94632 _94633 _94634) = (term863 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7105689 _94632) (@lem7105688 _94632 _94633 _94634)). Qed.
Lemma lem7105694 (_94632 : real) (_94633 : real) (_94634 : real) : (term857 _94632 _94633 _94634) = (term863 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7105681 _94632 _94633 _94634) (@lem7105692 _94632 _94633 _94634)). Qed.
Lemma lem7105695 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term863 _94632 _94633 _94634.
Proof. exact (EQ_MP (@lem7105694 _94632 _94633 _94634) (@lem7105390 _94632 _94633 _94634 h1)). Qed.
Lemma lem7105699 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term773 A f x''' b.
Proof. exact (proj2 (@lem7104524 A x'' x' s f x''' b h1)). Qed.
Lemma lem7105711 {A : Type'} (x''' : A) (x' : A) (h1 : x''' = x') : x''' = x'.
Proof. exact (h1). Qed.
Lemma lem7105739 (_94639 : real) (_94638 : real) (_94640 : real) : (term858 _94639 _94638 _94640) = (term867 _94639 _94638 _94640).
Proof. exact (@lem7087519 (term720 _94638) (term722 _94638 _94639 _94640) (term699 _94638 _94640)). Qed.
Lemma lem7105746 (_94639 : real) (_94638 : real) (_94640 : real) : (term868 _94639 _94638 _94640) = (term869 _94639 _94638 _94640).
Proof. exact (@lem7087519 (term720 _94639) (term711 _94638 _94639 _94640) (term699 _94638 _94640)). Qed.
Lemma lem7105747 (_94638 : real) : (term721 _94638) = (term721 _94638).
Proof. exact (eq_refl (term721 _94638)). Qed.
Lemma lem7105750 (_94639 : real) (_94638 : real) (_94640 : real) : (term867 _94639 _94638 _94640) = (term870 _94639 _94638 _94640).
Proof. exact (MK_COMB (@lem7105747 _94638) (@lem7105746 _94639 _94638 _94640)). Qed.
Lemma lem7105752 (_94639 : real) (_94638 : real) (_94640 : real) : (term858 _94639 _94638 _94640) = (term870 _94639 _94638 _94640).
Proof. exact (TRANS (@lem7105739 _94639 _94638 _94640) (@lem7105750 _94639 _94638 _94640)). Qed.
Lemma lem7105775 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term773 A f x''' b.
Proof. exact (proj2 (@lem7104524 A x'' x' s f x''' b h1)). Qed.
Lemma lem7105785 {A : Type'} (_94651 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term810 A s f _94651 b.
Proof. exact (EQ_MP (@lem7105366 A s f _94651 b) (@lem7105365 A _94651 s f b h1)). Qed.
Lemma lem7105787 {A : Type'} (x''' : A) (s : A -> Prop) (h1 : term774 A x''' s) : term774 A x''' s.
Proof. exact (h1). Qed.
Lemma lem7105944 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term824 A f x''.
Proof. exact (proj2 (@lem7104532 A s f x'' h1)). Qed.
Lemma lem7105972 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term859 A s f _94619.
Proof. exact (proj2 (@lem7105271 A _94619 x'' x' s f x''' b h1)). Qed.
Lemma lem7106111 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term820 A s f b.
Proof. exact (h1). Qed.
Lemma lem7106125 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term864 A x' f _94631.
Proof. exact (proj1 (@lem7105307 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7106139 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term859 A s f _94631.
Proof. exact (proj2 (@lem7105307 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7106153 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term865 A x _94630 _94629.
Proof. exact (proj1 (@lem7105304 A _94630 _94629 x h1)). Qed.
Lemma lem7106167 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term866 A x _94630 _94629.
Proof. exact (proj2 (@lem7105304 A _94630 _94629 x h1)). Qed.
Lemma lem7106195 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term863 _94626 _94627 _94628.
Proof. exact (EQ_MP (@lem7105622 _94626 _94627 _94628) (@lem7105384 _94626 _94627 _94628 h1)). Qed.
Lemma lem7106224 {A : Type'} (f : A -> real) (b : real) : (term871 A f b) = (term871 A f b).
Proof. exact (eq_refl (term871 A f b)). Qed.
Lemma lem7106225 {A : Type'} (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : x''' = x') : (term872 A f b x''') = (term872 A f b x').
Proof. exact (MK_COMB (@lem7106224 A f b) (@lem7105711 A x''' x' h1)). Qed.
Lemma lem7106226 {A : Type'} (f : A -> real) (x' : A) (b : real) : (term872 A f b x') = (term773 A f x' b).
Proof. exact (eq_refl (term872 A f b x')). Qed.
Lemma lem7106227 {A : Type'} (f : A -> real) (b : real) (x''' : A) : (term873 A f b x''') = (term873 A f b x''').
Proof. exact (eq_refl (term873 A f b x''')). Qed.
Lemma lem7106228 {A : Type'} (x''' : A) (f : A -> real) (x' : A) (b : real) : ((term872 A f b x''') = (term872 A f b x')) = ((term872 A f b x''') = (term773 A f x' b)).
Proof. exact (MK_COMB (@lem7106227 A f b x''') (@lem7106226 A f x' b)). Qed.
Lemma lem7106229 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term872 A f b x''') = (term773 A f x''' b).
Proof. exact (eq_refl (term872 A f b x''')). Qed.
Lemma lem7106230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7106231 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term873 A f b x''') = (term874 A f x''' b).
Proof. exact (MK_COMB (@lem7106230) (@lem7106229 A f x''' b)). Qed.
Lemma lem7106232 {A : Type'} (f : A -> real) (x' : A) (b : real) : (term773 A f x' b) = (term773 A f x' b).
Proof. exact (eq_refl (term773 A f x' b)). Qed.
Lemma lem7106233 {A : Type'} (x''' : A) (f : A -> real) (x' : A) (b : real) : ((term872 A f b x''') = (term773 A f x' b)) = ((term773 A f x''' b) = (term773 A f x' b)).
Proof. exact (MK_COMB (@lem7106231 A f x''' b) (@lem7106232 A f x' b)). Qed.
Lemma lem7106234 {A : Type'} (x''' : A) (f : A -> real) (x' : A) (b : real) : ((term872 A f b x''') = (term872 A f b x')) = ((term773 A f x''' b) = (term773 A f x' b)).
Proof. exact (TRANS (@lem7106228 A x''' f x' b) (@lem7106233 A x''' f x' b)). Qed.
Lemma lem7106235 {A : Type'} (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : x''' = x') : (term773 A f x''' b) = (term773 A f x' b).
Proof. exact (EQ_MP (@lem7106234 A x''' f x' b) (@lem7106225 A f b x''' x' h1)). Qed.
Lemma lem7106236 {A : Type'} (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : x''' = x') : term773 A f x' b.
Proof. exact (EQ_MP (@lem7106235 A f b x''' x' h2) (@lem7105699 A x'' x' s f x''' b h1)). Qed.
Lemma lem7106292 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term864 A x' f _94643.
Proof. exact (proj1 (@lem7105343 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7106306 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term859 A s f _94643.
Proof. exact (proj2 (@lem7105343 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7106320 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term865 A x _94642 _94641.
Proof. exact (proj1 (@lem7105340 A _94642 _94641 x h1)). Qed.
Lemma lem7106334 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term866 A x _94642 _94641.
Proof. exact (proj2 (@lem7105340 A _94642 _94641 x h1)). Qed.
Lemma lem7106348 (_94639 : real) (_94638 : real) (_94640 : real) (h1 : term181) : term870 _94639 _94638 _94640.
Proof. exact (EQ_MP (@lem7105752 _94639 _94638 _94640) (@lem7105397 _94639 _94638 _94640 h1)). Qed.
Lemma lem7106601 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term774 A x'' s.
Proof. exact (proj1 (@lem7104532 A s f x'' h1)). Qed.
Lemma lem7106602 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term875 A x'' s.
Proof. exact (fun h0 : term796 A x'' s => @lem7106601 A s f x'' h1). Qed.
Lemma lem7106604 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106605 {A : Type'} (x'' : A) (s : A -> Prop) : (term875 A x'' s) = (term774 A x'' s).
Proof. exact (@lem7106604 (term774 A x'' s)). Qed.
Lemma lem7106606 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term774 A x'' s.
Proof. exact (EQ_MP (@lem7106605 A x'' s) (@lem7106602 A s f x'' h1)). Qed.
Lemma lem7106612 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7106613 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : (term859 A s f _94619) = (term877 A f _94619 s).
Proof. exact (@lem7106612 (term795 A f _94619) (term796 A _94619 s)). Qed.
Lemma lem7106619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7106620 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : (term878 A s f _94619) = (term879 A f _94619 s).
Proof. exact (MK_COMB (@lem7106619) (@lem7106613 A f _94619 s)). Qed.
Lemma lem7106626 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : (term877 A f _94619 s) = (term877 A f _94619 s).
Proof. exact (eq_refl (term877 A f _94619 s)). Qed.
Lemma lem7106627 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : ((term859 A s f _94619) = (term877 A f _94619 s)) = ((term877 A f _94619 s) = (term877 A f _94619 s)).
Proof. exact (MK_COMB (@lem7106620 A f _94619 s) (@lem7106626 A f _94619 s)). Qed.
Lemma lem7106629 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7106630 (x : Prop) : (x = x) = True.
Proof. exact (@lem7106629 Prop x). Qed.
Lemma lem7106631 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : ((term877 A f _94619 s) = (term877 A f _94619 s)) = True.
Proof. exact (@lem7106630 (term877 A f _94619 s)). Qed.
Lemma lem7106632 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : ((term859 A s f _94619) = (term877 A f _94619 s)) = True.
Proof. exact (TRANS (@lem7106627 A f _94619 s) (@lem7106631 A f _94619 s)). Qed.
Lemma lem7106633 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : True = ((term859 A s f _94619) = (term877 A f _94619 s)).
Proof. exact (SYM (@lem7106632 A f _94619 s)). Qed.
Lemma lem7106634 {A : Type'} (f : A -> real) (_94619 : A) (s : A -> Prop) : (term859 A s f _94619) = (term877 A f _94619 s).
Proof. exact (EQ_MP (@lem7106633 A f _94619 s) (@lem0)). Qed.
Lemma lem7106635 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term877 A f _94619 s.
Proof. exact (EQ_MP (@lem7106634 A f _94619 s) (@lem7105972 A _94619 x'' x' s f x''' b h1)). Qed.
Lemma lem7106637 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7106638 {A : Type'} (s : A -> Prop) (f : A -> real) (_94619 : A) : (term877 A f _94619 s) = (term881 A s f _94619).
Proof. exact (@lem7106637 (term796 A _94619 s) (term795 A f _94619)). Qed.
Lemma lem7106640 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7106641 {A : Type'} (_94619 : A) (s : A -> Prop) : (term883 A _94619 s) = (term774 A _94619 s).
Proof. exact (@lem7106640 (term774 A _94619 s)). Qed.
Lemma lem7106642 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7106643 {A : Type'} (_94619 : A) (s : A -> Prop) : (term884 A _94619 s) = (term885 A _94619 s).
Proof. exact (MK_COMB (@lem7106642) (@lem7106641 A _94619 s)). Qed.
Lemma lem7106644 {A : Type'} (f : A -> real) (_94619 : A) : (term795 A f _94619) = (term795 A f _94619).
Proof. exact (eq_refl (term795 A f _94619)). Qed.
Lemma lem7106645 {A : Type'} (s : A -> Prop) (f : A -> real) (_94619 : A) : (term881 A s f _94619) = (term886 A s f _94619).
Proof. exact (MK_COMB (@lem7106643 A _94619 s) (@lem7106644 A f _94619)). Qed.
Lemma lem7106646 {A : Type'} (s : A -> Prop) (f : A -> real) (_94619 : A) : (term877 A f _94619 s) = (term886 A s f _94619).
Proof. exact (TRANS (@lem7106638 A s f _94619) (@lem7106645 A s f _94619)). Qed.
Lemma lem7106649 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94619.
Proof. exact (EQ_MP (@lem7106646 A s f _94619) (@lem7106635 A _94619 x'' x' s f x''' b h1)). Qed.
Lemma lem7106650 {A : Type'} (_94619 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94619.
Proof. exact (@lem7106649 A _94619 x'' x' s f x''' b h1). Qed.
Lemma lem7106651 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f x''.
Proof. exact (@lem7106650 A x'' x'' x' s f x''' b h1). Qed.
Lemma lem7106654 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term795 A f x''.
Proof. exact (@lem7106651 A x'' x' s f x''' b h1 (@lem7106606 A s f x'' h2)). Qed.
Lemma lem7106655 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term887 A f x''.
Proof. exact (fun h0 : term824 A f x'' => @lem7106654 A x' x''' b s f x'' h1 h2). Qed.
Lemma lem7106657 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106658 {A : Type'} (f : A -> real) (x'' : A) : (term887 A f x'') = (term795 A f x'').
Proof. exact (@lem7106657 (term795 A f x'')). Qed.
Lemma lem7106659 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term795 A f x''.
Proof. exact (EQ_MP (@lem7106658 A f x'') (@lem7106655 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7106662 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7106664 {A : Type'} (f : A -> real) (x'' : A) : (term824 A f x'') = (term888 A f x'').
Proof. exact (@lem7106662 (term795 A f x'')). Qed.
Lemma lem7106667 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term888 A f x''.
Proof. exact (EQ_MP (@lem7106664 A f x'') (@lem7105944 A s f x'' h1)). Qed.
Lemma lem7106670 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : False.
Proof. exact (@lem7106667 A s f x'' h2 (@lem7106659 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7106671 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term889.
Proof. exact (fun h0 : ~ False => @lem7106670 A x' x''' b s f x'' h1 h2). Qed.
Lemma lem7106673 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106674 : term889 = False.
Proof. exact (@lem7106673 False). Qed.
Lemma lem7106914 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term774 A x'' s.
Proof. exact (proj1 (@lem7104532 A s f x'' h1)). Qed.
Lemma lem7106915 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term875 A x'' s.
Proof. exact (fun h0 : term796 A x'' s => @lem7106914 A s f x'' h1). Qed.
Lemma lem7106917 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106918 {A : Type'} (x'' : A) (s : A -> Prop) : (term875 A x'' s) = (term774 A x'' s).
Proof. exact (@lem7106917 (term774 A x'' s)). Qed.
Lemma lem7106919 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term774 A x'' s.
Proof. exact (EQ_MP (@lem7106918 A x'' s) (@lem7106915 A s f x'' h1)). Qed.
Lemma lem7106925 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7106926 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : (term859 A s f _94625) = (term877 A f _94625 s).
Proof. exact (@lem7106925 (term795 A f _94625) (term796 A _94625 s)). Qed.
Lemma lem7106932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7106933 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : (term878 A s f _94625) = (term879 A f _94625 s).
Proof. exact (MK_COMB (@lem7106932) (@lem7106926 A f _94625 s)). Qed.
Lemma lem7106939 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : (term877 A f _94625 s) = (term877 A f _94625 s).
Proof. exact (eq_refl (term877 A f _94625 s)). Qed.
Lemma lem7106940 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : ((term859 A s f _94625) = (term877 A f _94625 s)) = ((term877 A f _94625 s) = (term877 A f _94625 s)).
Proof. exact (MK_COMB (@lem7106933 A f _94625 s) (@lem7106939 A f _94625 s)). Qed.
Lemma lem7106942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7106943 (x : Prop) : (x = x) = True.
Proof. exact (@lem7106942 Prop x). Qed.
Lemma lem7106944 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : ((term877 A f _94625 s) = (term877 A f _94625 s)) = True.
Proof. exact (@lem7106943 (term877 A f _94625 s)). Qed.
Lemma lem7106945 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : ((term859 A s f _94625) = (term877 A f _94625 s)) = True.
Proof. exact (TRANS (@lem7106940 A f _94625 s) (@lem7106944 A f _94625 s)). Qed.
Lemma lem7106946 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : True = ((term859 A s f _94625) = (term877 A f _94625 s)).
Proof. exact (SYM (@lem7106945 A f _94625 s)). Qed.
Lemma lem7106947 {A : Type'} (f : A -> real) (_94625 : A) (s : A -> Prop) : (term859 A s f _94625) = (term877 A f _94625 s).
Proof. exact (EQ_MP (@lem7106946 A f _94625 s) (@lem0)). Qed.
Lemma lem7106948 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term877 A f _94625 s.
Proof. exact (EQ_MP (@lem7106947 A f _94625 s) (@lem7105503 A _94625 x'' x' s f x''' b h1)). Qed.
Lemma lem7106950 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7106951 {A : Type'} (s : A -> Prop) (f : A -> real) (_94625 : A) : (term877 A f _94625 s) = (term881 A s f _94625).
Proof. exact (@lem7106950 (term796 A _94625 s) (term795 A f _94625)). Qed.
Lemma lem7106953 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7106954 {A : Type'} (_94625 : A) (s : A -> Prop) : (term883 A _94625 s) = (term774 A _94625 s).
Proof. exact (@lem7106953 (term774 A _94625 s)). Qed.
Lemma lem7106955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7106956 {A : Type'} (_94625 : A) (s : A -> Prop) : (term884 A _94625 s) = (term885 A _94625 s).
Proof. exact (MK_COMB (@lem7106955) (@lem7106954 A _94625 s)). Qed.
Lemma lem7106957 {A : Type'} (f : A -> real) (_94625 : A) : (term795 A f _94625) = (term795 A f _94625).
Proof. exact (eq_refl (term795 A f _94625)). Qed.
Lemma lem7106958 {A : Type'} (s : A -> Prop) (f : A -> real) (_94625 : A) : (term881 A s f _94625) = (term886 A s f _94625).
Proof. exact (MK_COMB (@lem7106956 A _94625 s) (@lem7106957 A f _94625)). Qed.
Lemma lem7106959 {A : Type'} (s : A -> Prop) (f : A -> real) (_94625 : A) : (term877 A f _94625 s) = (term886 A s f _94625).
Proof. exact (TRANS (@lem7106951 A s f _94625) (@lem7106958 A s f _94625)). Qed.
Lemma lem7106962 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94625.
Proof. exact (EQ_MP (@lem7106959 A s f _94625) (@lem7106948 A _94625 x'' x' s f x''' b h1)). Qed.
Lemma lem7106963 {A : Type'} (_94625 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94625.
Proof. exact (@lem7106962 A _94625 x'' x' s f x''' b h1). Qed.
Lemma lem7106964 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f x''.
Proof. exact (@lem7106963 A x'' x'' x' s f x''' b h1). Qed.
Lemma lem7106967 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term795 A f x''.
Proof. exact (@lem7106964 A x'' x' s f x''' b h1 (@lem7106919 A s f x'' h2)). Qed.
Lemma lem7106968 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term887 A f x''.
Proof. exact (fun h0 : term824 A f x'' => @lem7106967 A x' x''' b s f x'' h1 h2). Qed.
Lemma lem7106970 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106971 {A : Type'} (f : A -> real) (x'' : A) : (term887 A f x'') = (term795 A f x'').
Proof. exact (@lem7106970 (term795 A f x'')). Qed.
Lemma lem7106972 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term795 A f x''.
Proof. exact (EQ_MP (@lem7106971 A f x'') (@lem7106968 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7106975 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7106977 {A : Type'} (f : A -> real) (x'' : A) : (term824 A f x'') = (term888 A f x'').
Proof. exact (@lem7106975 (term795 A f x'')). Qed.
Lemma lem7106980 {A : Type'} (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term827 A s f x'') : term888 A f x''.
Proof. exact (EQ_MP (@lem7106977 A f x'') (@lem7105489 A s f x'' h1)). Qed.
Lemma lem7106983 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : False.
Proof. exact (@lem7106980 A s f x'' h2 (@lem7106972 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7106984 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : term889.
Proof. exact (fun h0 : ~ False => @lem7106983 A x' x''' b s f x'' h1 h2). Qed.
Lemma lem7106986 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7106987 : term889 = False.
Proof. exact (@lem7106986 False). Qed.
Lemma lem7106988 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : False.
Proof. exact (EQ_MP (@lem7106987) (@lem7106984 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7107227 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7107228 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7107227 A x). Qed.
Lemma lem7107229 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem7107228 A x'). Qed.
Lemma lem7107230 {A : Type'} (x' : A) : term890 A x'.
Proof. exact (fun h0 : term891 A x' => @lem7107229 A x'). Qed.
Lemma lem7107232 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107233 {A : Type'} (x' : A) : (term890 A x') = (x' = x').
Proof. exact (@lem7107232 (x' = x')). Qed.
Lemma lem7107234 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem7107233 A x') (@lem7107230 A x')). Qed.
Lemma lem7107240 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107241 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : (term864 A x' f _94631) = (term892 A f _94631 x').
Proof. exact (@lem7107240 (term795 A f _94631) (term835 A _94631 x')). Qed.
Lemma lem7107249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107250 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : (term893 A x' f _94631) = (term894 A f _94631 x').
Proof. exact (MK_COMB (@lem7107249) (@lem7107241 A f _94631 x')). Qed.
Lemma lem7107258 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : (term892 A f _94631 x') = (term892 A f _94631 x').
Proof. exact (eq_refl (term892 A f _94631 x')). Qed.
Lemma lem7107259 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : ((term864 A x' f _94631) = (term892 A f _94631 x')) = ((term892 A f _94631 x') = (term892 A f _94631 x')).
Proof. exact (MK_COMB (@lem7107250 A f _94631 x') (@lem7107258 A f _94631 x')). Qed.
Lemma lem7107261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107262 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107261 Prop x). Qed.
Lemma lem7107263 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : ((term892 A f _94631 x') = (term892 A f _94631 x')) = True.
Proof. exact (@lem7107262 (term892 A f _94631 x')). Qed.
Lemma lem7107264 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : ((term864 A x' f _94631) = (term892 A f _94631 x')) = True.
Proof. exact (TRANS (@lem7107259 A f _94631 x') (@lem7107263 A f _94631 x')). Qed.
Lemma lem7107265 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : True = ((term864 A x' f _94631) = (term892 A f _94631 x')).
Proof. exact (SYM (@lem7107264 A f _94631 x')). Qed.
Lemma lem7107266 {A : Type'} (f : A -> real) (_94631 : A) (x' : A) : (term864 A x' f _94631) = (term892 A f _94631 x').
Proof. exact (EQ_MP (@lem7107265 A f _94631 x') (@lem0)). Qed.
Lemma lem7107267 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term892 A f _94631 x'.
Proof. exact (EQ_MP (@lem7107266 A f _94631 x') (@lem7106125 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7107269 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107270 {A : Type'} (x' : A) (f : A -> real) (_94631 : A) : (term892 A f _94631 x') = (term895 A x' f _94631).
Proof. exact (@lem7107269 (term835 A _94631 x') (term795 A f _94631)). Qed.
Lemma lem7107272 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107273 {A : Type'} (_94631 : A) (x' : A) : (term896 A _94631 x') = (_94631 = x').
Proof. exact (@lem7107272 (_94631 = x')). Qed.
Lemma lem7107274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107275 {A : Type'} (_94631 : A) (x' : A) : (term897 A _94631 x') = (term898 A _94631 x').
Proof. exact (MK_COMB (@lem7107274) (@lem7107273 A _94631 x')). Qed.
Lemma lem7107276 {A : Type'} (f : A -> real) (_94631 : A) : (term795 A f _94631) = (term795 A f _94631).
Proof. exact (eq_refl (term795 A f _94631)). Qed.
Lemma lem7107277 {A : Type'} (x' : A) (f : A -> real) (_94631 : A) : (term895 A x' f _94631) = (term899 A x' f _94631).
Proof. exact (MK_COMB (@lem7107275 A _94631 x') (@lem7107276 A f _94631)). Qed.
Lemma lem7107278 {A : Type'} (x' : A) (f : A -> real) (_94631 : A) : (term892 A f _94631 x') = (term899 A x' f _94631).
Proof. exact (TRANS (@lem7107270 A x' f _94631) (@lem7107277 A x' f _94631)). Qed.
Lemma lem7107281 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94631.
Proof. exact (EQ_MP (@lem7107278 A x' f _94631) (@lem7107267 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7107282 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94631.
Proof. exact (@lem7107281 A _94631 x'' x' s f x''' b h1). Qed.
Lemma lem7107283 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term900 A f x'.
Proof. exact (@lem7107282 A x' x'' x' s f x''' b h1). Qed.
Lemma lem7107286 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (@lem7107283 A x'' x' s f x''' b h1 (@lem7107234 A x')). Qed.
Lemma lem7107287 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term887 A f x'.
Proof. exact (fun h0 : term824 A f x' => @lem7107286 A x'' x' s f x''' b h1). Qed.
Lemma lem7107289 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107290 {A : Type'} (f : A -> real) (x' : A) : (term887 A f x') = (term795 A f x').
Proof. exact (@lem7107289 (term795 A f x')). Qed.
Lemma lem7107291 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (EQ_MP (@lem7107290 A f x') (@lem7107287 A x'' x' s f x''' b h1)). Qed.
Lemma lem7107294 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (h1). Qed.
Lemma lem7107295 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term902 A s f.
Proof. exact (fun h0 : term735 A s f => @lem7107294 A s f h1). Qed.
Lemma lem7107297 (p : Prop) : (term903 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7107298 {A : Type'} (s : A -> Prop) (f : A -> real) : (term902 A s f) = (term901 A s f).
Proof. exact (@lem7107297 (term735 A s f)). Qed.
Lemma lem7107299 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (EQ_MP (@lem7107298 A s f) (@lem7107295 A s f h1)). Qed.
Lemma lem7107301 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107304 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term865 A x _94630 _94629) = (term904 A x _94629 _94630).
Proof. exact (@lem7107301 (term735 A _94630 _94629) (term752 A x _94629 _94630)). Qed.
Lemma lem7107307 {A : Type'} (_94629 : A -> real) (_94630 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94629 _94630.
Proof. exact (EQ_MP (@lem7107304 A x _94629 _94630) (@lem7106153 A _94630 _94629 x h1)). Qed.
Lemma lem7107308 {A : Type'} (_94629 : A -> real) (_94630 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94629 _94630.
Proof. exact (@lem7107307 A _94629 _94630 x h1). Qed.
Lemma lem7107309 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x f s.
Proof. exact (@lem7107308 A f s x h1). Qed.
Lemma lem7107312 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (@lem7107309 A f s x h1 (@lem7107299 A s f h2)). Qed.
Lemma lem7107313 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term905 A x f s.
Proof. exact (fun h0 : term906 A x f s => @lem7107312 A x s f h1 h2). Qed.
Lemma lem7107315 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107316 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term905 A x f s) = (term752 A x f s).
Proof. exact (@lem7107315 (term752 A x f s)). Qed.
Lemma lem7107317 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (EQ_MP (@lem7107316 A x f s) (@lem7107313 A x s f h1 h2)). Qed.
Lemma lem7107323 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107324 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : (term859 A s f _94631) = (term877 A f _94631 s).
Proof. exact (@lem7107323 (term795 A f _94631) (term796 A _94631 s)). Qed.
Lemma lem7107330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107331 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : (term878 A s f _94631) = (term879 A f _94631 s).
Proof. exact (MK_COMB (@lem7107330) (@lem7107324 A f _94631 s)). Qed.
Lemma lem7107337 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : (term877 A f _94631 s) = (term877 A f _94631 s).
Proof. exact (eq_refl (term877 A f _94631 s)). Qed.
Lemma lem7107338 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : ((term859 A s f _94631) = (term877 A f _94631 s)) = ((term877 A f _94631 s) = (term877 A f _94631 s)).
Proof. exact (MK_COMB (@lem7107331 A f _94631 s) (@lem7107337 A f _94631 s)). Qed.
Lemma lem7107340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107341 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107340 Prop x). Qed.
Lemma lem7107342 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : ((term877 A f _94631 s) = (term877 A f _94631 s)) = True.
Proof. exact (@lem7107341 (term877 A f _94631 s)). Qed.
Lemma lem7107343 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : ((term859 A s f _94631) = (term877 A f _94631 s)) = True.
Proof. exact (TRANS (@lem7107338 A f _94631 s) (@lem7107342 A f _94631 s)). Qed.
Lemma lem7107344 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : True = ((term859 A s f _94631) = (term877 A f _94631 s)).
Proof. exact (SYM (@lem7107343 A f _94631 s)). Qed.
Lemma lem7107345 {A : Type'} (f : A -> real) (_94631 : A) (s : A -> Prop) : (term859 A s f _94631) = (term877 A f _94631 s).
Proof. exact (EQ_MP (@lem7107344 A f _94631 s) (@lem0)). Qed.
Lemma lem7107346 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term877 A f _94631 s.
Proof. exact (EQ_MP (@lem7107345 A f _94631 s) (@lem7106139 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7107348 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107349 {A : Type'} (s : A -> Prop) (f : A -> real) (_94631 : A) : (term877 A f _94631 s) = (term881 A s f _94631).
Proof. exact (@lem7107348 (term796 A _94631 s) (term795 A f _94631)). Qed.
Lemma lem7107351 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107352 {A : Type'} (_94631 : A) (s : A -> Prop) : (term883 A _94631 s) = (term774 A _94631 s).
Proof. exact (@lem7107351 (term774 A _94631 s)). Qed.
Lemma lem7107353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107354 {A : Type'} (_94631 : A) (s : A -> Prop) : (term884 A _94631 s) = (term885 A _94631 s).
Proof. exact (MK_COMB (@lem7107353) (@lem7107352 A _94631 s)). Qed.
Lemma lem7107355 {A : Type'} (f : A -> real) (_94631 : A) : (term795 A f _94631) = (term795 A f _94631).
Proof. exact (eq_refl (term795 A f _94631)). Qed.
Lemma lem7107356 {A : Type'} (s : A -> Prop) (f : A -> real) (_94631 : A) : (term881 A s f _94631) = (term886 A s f _94631).
Proof. exact (MK_COMB (@lem7107354 A _94631 s) (@lem7107355 A f _94631)). Qed.
Lemma lem7107357 {A : Type'} (s : A -> Prop) (f : A -> real) (_94631 : A) : (term877 A f _94631 s) = (term886 A s f _94631).
Proof. exact (TRANS (@lem7107349 A s f _94631) (@lem7107356 A s f _94631)). Qed.
Lemma lem7107360 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94631.
Proof. exact (EQ_MP (@lem7107357 A s f _94631) (@lem7107346 A _94631 x'' x' s f x''' b h1)). Qed.
Lemma lem7107361 {A : Type'} (_94631 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94631.
Proof. exact (@lem7107360 A _94631 x'' x' s f x''' b h1). Qed.
Lemma lem7107362 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term907 A x f s.
Proof. exact (@lem7107361 A (term736 A x f s) x'' x' s f x''' b h1). Qed.
Lemma lem7107365 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (@lem7107362 A x x'' x' s f x''' b h3 (@lem7107317 A x s f h1 h2)). Qed.
Lemma lem7107366 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term908 A x f s.
Proof. exact (fun h0 : term745 A x f s => @lem7107365 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7107368 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107369 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term908 A x f s) = (term743 A x f s).
Proof. exact (@lem7107368 (term743 A x f s)). Qed.
Lemma lem7107370 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (EQ_MP (@lem7107369 A x f s) (@lem7107366 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7107376 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107377 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term866 A x _94630 _94629) = (term909 A x _94629 _94630).
Proof. exact (@lem7107376 (term735 A _94630 _94629) (term745 A x _94629 _94630)). Qed.
Lemma lem7107383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107384 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term910 A x _94630 _94629) = (term911 A x _94629 _94630).
Proof. exact (MK_COMB (@lem7107383) (@lem7107377 A x _94629 _94630)). Qed.
Lemma lem7107390 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term909 A x _94629 _94630) = (term909 A x _94629 _94630).
Proof. exact (eq_refl (term909 A x _94629 _94630)). Qed.
Lemma lem7107391 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : ((term866 A x _94630 _94629) = (term909 A x _94629 _94630)) = ((term909 A x _94629 _94630) = (term909 A x _94629 _94630)).
Proof. exact (MK_COMB (@lem7107384 A x _94629 _94630) (@lem7107390 A x _94629 _94630)). Qed.
Lemma lem7107393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107394 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107393 Prop x). Qed.
Lemma lem7107395 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : ((term909 A x _94629 _94630) = (term909 A x _94629 _94630)) = True.
Proof. exact (@lem7107394 (term909 A x _94629 _94630)). Qed.
Lemma lem7107396 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : ((term866 A x _94630 _94629) = (term909 A x _94629 _94630)) = True.
Proof. exact (TRANS (@lem7107391 A x _94629 _94630) (@lem7107395 A x _94629 _94630)). Qed.
Lemma lem7107397 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : True = ((term866 A x _94630 _94629) = (term909 A x _94629 _94630)).
Proof. exact (SYM (@lem7107396 A x _94629 _94630)). Qed.
Lemma lem7107398 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term866 A x _94630 _94629) = (term909 A x _94629 _94630).
Proof. exact (EQ_MP (@lem7107397 A x _94629 _94630) (@lem0)). Qed.
Lemma lem7107399 {A : Type'} (_94629 : A -> real) (_94630 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term909 A x _94629 _94630.
Proof. exact (EQ_MP (@lem7107398 A x _94629 _94630) (@lem7106167 A _94630 _94629 x h1)). Qed.
Lemma lem7107401 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107402 {A : Type'} (x : type710 A) (_94630 : A -> Prop) (_94629 : A -> real) : (term909 A x _94629 _94630) = (term912 A x _94630 _94629).
Proof. exact (@lem7107401 (term745 A x _94629 _94630) (term735 A _94630 _94629)). Qed.
Lemma lem7107404 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107405 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term913 A x _94629 _94630) = (term743 A x _94629 _94630).
Proof. exact (@lem7107404 (term743 A x _94629 _94630)). Qed.
Lemma lem7107406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107407 {A : Type'} (x : type710 A) (_94629 : A -> real) (_94630 : A -> Prop) : (term914 A x _94629 _94630) = (term915 A x _94629 _94630).
Proof. exact (MK_COMB (@lem7107406) (@lem7107405 A x _94629 _94630)). Qed.
Lemma lem7107408 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) : (term735 A _94630 _94629) = (term735 A _94630 _94629).
Proof. exact (eq_refl (term735 A _94630 _94629)). Qed.
Lemma lem7107409 {A : Type'} (x : type710 A) (_94630 : A -> Prop) (_94629 : A -> real) : (term912 A x _94630 _94629) = (term916 A x _94630 _94629).
Proof. exact (MK_COMB (@lem7107407 A x _94629 _94630) (@lem7107408 A _94630 _94629)). Qed.
Lemma lem7107410 {A : Type'} (x : type710 A) (_94630 : A -> Prop) (_94629 : A -> real) : (term909 A x _94629 _94630) = (term916 A x _94630 _94629).
Proof. exact (TRANS (@lem7107402 A x _94630 _94629) (@lem7107409 A x _94630 _94629)). Qed.
Lemma lem7107413 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94630 _94629.
Proof. exact (EQ_MP (@lem7107410 A x _94630 _94629) (@lem7107399 A _94629 _94630 x h1)). Qed.
Lemma lem7107414 {A : Type'} (_94630 : A -> Prop) (_94629 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94630 _94629.
Proof. exact (@lem7107413 A _94630 _94629 x h1). Qed.
Lemma lem7107415 {A : Type'} (s : A -> Prop) (f : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x s f.
Proof. exact (@lem7107414 A s f x h1). Qed.
Lemma lem7107418 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (@lem7107415 A s f x h1 (@lem7107370 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7107419 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term917 A s f.
Proof. exact (fun h0 : term901 A s f => @lem7107418 A x x'' x' s f x''' b h1 h0 h2). Qed.
Lemma lem7107421 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107422 {A : Type'} (s : A -> Prop) (f : A -> real) : (term917 A s f) = (term735 A s f).
Proof. exact (@lem7107421 (term735 A s f)). Qed.
Lemma lem7107423 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (EQ_MP (@lem7107422 A s f) (@lem7107419 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7107425 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (proj1 (@lem7104522 A x'' x' s f x''' b h1)). Qed.
Lemma lem7107426 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term918 A x' s f b.
Proof. exact (fun h0 : term919 A x' s f b => @lem7107425 A x'' x' s f x''' b h1). Qed.
Lemma lem7107428 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107429 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term918 A x' s f b) = (term790 A x' s f b).
Proof. exact (@lem7107428 (term790 A x' s f b)). Qed.
Lemma lem7107430 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (EQ_MP (@lem7107429 A x' s f b) (@lem7107426 A x'' x' s f x''' b h1)). Qed.
Lemma lem7107456 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107457 (_94626 : real) (_94627 : real) (_94628 : real) : (term920 _94626 _94627 _94628) = (term921 _94626 _94627 _94628).
Proof. exact (@lem7107456 (term699 _94627 _94628) (term711 _94626 _94627 _94628)). Qed.
Lemma lem7107463 (_94627 : real) : (term721 _94627) = (term721 _94627).
Proof. exact (eq_refl (term721 _94627)). Qed.
Lemma lem7107464 (_94626 : real) (_94627 : real) (_94628 : real) : (term862 _94626 _94627 _94628) = (term922 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107463 _94627) (@lem7107457 _94626 _94627 _94628)). Qed.
Lemma lem7107468 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7107469 (_94626 : real) (_94627 : real) (_94628 : real) : (term922 _94626 _94627 _94628) = (term923 _94626 _94627 _94628).
Proof. exact (@lem7107468 (term699 _94627 _94628) (term720 _94627) (term711 _94626 _94627 _94628)). Qed.
Lemma lem7107485 (_94626 : real) (_94627 : real) (_94628 : real) : (term862 _94626 _94627 _94628) = (term923 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7107464 _94626 _94627 _94628) (@lem7107469 _94626 _94627 _94628)). Qed.
Lemma lem7107486 (_94626 : real) : (term721 _94626) = (term721 _94626).
Proof. exact (eq_refl (term721 _94626)). Qed.
Lemma lem7107487 (_94626 : real) (_94627 : real) (_94628 : real) : (term863 _94626 _94627 _94628) = (term924 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107486 _94626) (@lem7107485 _94626 _94627 _94628)). Qed.
Lemma lem7107491 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7107492 (_94626 : real) (_94627 : real) (_94628 : real) : (term924 _94626 _94627 _94628) = (term925 _94626 _94627 _94628).
Proof. exact (@lem7107491 (term699 _94627 _94628) (term720 _94626) (term722 _94626 _94627 _94628)). Qed.
Lemma lem7107518 (_94626 : real) (_94627 : real) (_94628 : real) : (term863 _94626 _94627 _94628) = (term925 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7107487 _94626 _94627 _94628) (@lem7107492 _94626 _94627 _94628)). Qed.
Lemma lem7107519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107520 (_94626 : real) (_94627 : real) (_94628 : real) : (term926 _94626 _94627 _94628) = (term927 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107519) (@lem7107518 _94626 _94627 _94628)). Qed.
Lemma lem7107546 (_94626 : real) (_94627 : real) (_94628 : real) : (term925 _94626 _94627 _94628) = (term925 _94626 _94627 _94628).
Proof. exact (eq_refl (term925 _94626 _94627 _94628)). Qed.
Lemma lem7107547 (_94626 : real) (_94627 : real) (_94628 : real) : ((term863 _94626 _94627 _94628) = (term925 _94626 _94627 _94628)) = ((term925 _94626 _94627 _94628) = (term925 _94626 _94627 _94628)).
Proof. exact (MK_COMB (@lem7107520 _94626 _94627 _94628) (@lem7107546 _94626 _94627 _94628)). Qed.
Lemma lem7107549 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107550 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107549 Prop x). Qed.
Lemma lem7107551 (_94626 : real) (_94627 : real) (_94628 : real) : ((term925 _94626 _94627 _94628) = (term925 _94626 _94627 _94628)) = True.
Proof. exact (@lem7107550 (term925 _94626 _94627 _94628)). Qed.
Lemma lem7107552 (_94626 : real) (_94627 : real) (_94628 : real) : ((term863 _94626 _94627 _94628) = (term925 _94626 _94627 _94628)) = True.
Proof. exact (TRANS (@lem7107547 _94626 _94627 _94628) (@lem7107551 _94626 _94627 _94628)). Qed.
Lemma lem7107553 (_94626 : real) (_94627 : real) (_94628 : real) : True = ((term863 _94626 _94627 _94628) = (term925 _94626 _94627 _94628)).
Proof. exact (SYM (@lem7107552 _94626 _94627 _94628)). Qed.
Lemma lem7107554 (_94626 : real) (_94627 : real) (_94628 : real) : (term863 _94626 _94627 _94628) = (term925 _94626 _94627 _94628).
Proof. exact (EQ_MP (@lem7107553 _94626 _94627 _94628) (@lem0)). Qed.
Lemma lem7107555 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term925 _94626 _94627 _94628.
Proof. exact (EQ_MP (@lem7107554 _94626 _94627 _94628) (@lem7106195 _94626 _94627 _94628 h1)). Qed.
Lemma lem7107557 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107558 (_94626 : real) (_94627 : real) (_94628 : real) : (term925 _94626 _94627 _94628) = (term928 _94626 _94627 _94628).
Proof. exact (@lem7107557 (term723 _94626 _94627 _94628) (term699 _94627 _94628)). Qed.
Lemma lem7107560 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7107561 (_94626 : real) (_94627 : real) (_94628 : real) : (term931 _94626 _94627 _94628) = (term932 _94626 _94627 _94628).
Proof. exact (@lem7107560 (term720 _94626) (term722 _94626 _94627 _94628)). Qed.
Lemma lem7107563 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107564 (_94626 : real) : (term933 _94626) = (term718 _94626).
Proof. exact (@lem7107563 (term718 _94626)). Qed.
Lemma lem7107565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7107566 (_94626 : real) : (term934 _94626) = (term935 _94626).
Proof. exact (MK_COMB (@lem7107565) (@lem7107564 _94626)). Qed.
Lemma lem7107568 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7107569 (_94626 : real) (_94627 : real) (_94628 : real) : (term936 _94626 _94627 _94628) = (term937 _94626 _94627 _94628).
Proof. exact (@lem7107568 (term720 _94627) (term711 _94626 _94627 _94628)). Qed.
Lemma lem7107571 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107572 (_94627 : real) : (term933 _94627) = (term718 _94627).
Proof. exact (@lem7107571 (term718 _94627)). Qed.
Lemma lem7107573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7107574 (_94627 : real) : (term934 _94627) = (term935 _94627).
Proof. exact (MK_COMB (@lem7107573) (@lem7107572 _94627)). Qed.
Lemma lem7107576 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107577 (_94626 : real) (_94627 : real) (_94628 : real) : (term938 _94626 _94627 _94628) = (term709 _94626 _94627 _94628).
Proof. exact (@lem7107576 (term709 _94626 _94627 _94628)). Qed.
Lemma lem7107578 (_94626 : real) (_94627 : real) (_94628 : real) : (term937 _94626 _94627 _94628) = (term939 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107574 _94627) (@lem7107577 _94626 _94627 _94628)). Qed.
Lemma lem7107579 (_94626 : real) (_94627 : real) (_94628 : real) : (term936 _94626 _94627 _94628) = (term939 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7107569 _94626 _94627 _94628) (@lem7107578 _94626 _94627 _94628)). Qed.
Lemma lem7107580 (_94626 : real) (_94627 : real) (_94628 : real) : (term932 _94626 _94627 _94628) = (term940 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107566 _94626) (@lem7107579 _94626 _94627 _94628)). Qed.
Lemma lem7107581 (_94626 : real) (_94627 : real) (_94628 : real) : (term931 _94626 _94627 _94628) = (term940 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7107561 _94626 _94627 _94628) (@lem7107580 _94626 _94627 _94628)). Qed.
Lemma lem7107582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107583 (_94626 : real) (_94627 : real) (_94628 : real) : (term941 _94626 _94627 _94628) = (term942 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107582) (@lem7107581 _94626 _94627 _94628)). Qed.
Lemma lem7107584 (_94627 : real) (_94628 : real) : (term699 _94627 _94628) = (term699 _94627 _94628).
Proof. exact (eq_refl (term699 _94627 _94628)). Qed.
Lemma lem7107585 (_94626 : real) (_94627 : real) (_94628 : real) : (term928 _94626 _94627 _94628) = (term943 _94626 _94627 _94628).
Proof. exact (MK_COMB (@lem7107583 _94626 _94627 _94628) (@lem7107584 _94627 _94628)). Qed.
Lemma lem7107586 (_94626 : real) (_94627 : real) (_94628 : real) : (term925 _94626 _94627 _94628) = (term943 _94626 _94627 _94628).
Proof. exact (TRANS (@lem7107558 _94626 _94627 _94628) (@lem7107585 _94626 _94627 _94628)). Qed.
Lemma lem7107588 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term944 A x' s f b.
Proof. exact (conj (@lem7107423 A x x'' x' s f x''' b h1 h2) (@lem7107430 A x'' x' s f x''' b h2)). Qed.
Lemma lem7107589 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term945 A x' s f b.
Proof. exact (conj (@lem7107291 A x'' x' s f x''' b h2) (@lem7107588 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7107591 (_94626 : real) (_94627 : real) (_94628 : real) (h1 : term181) : term943 _94626 _94627 _94628.
Proof. exact (EQ_MP (@lem7107586 _94626 _94627 _94628) (@lem7107555 _94626 _94627 _94628 h1)). Qed.
Lemma lem7107592 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term181) : term946 A x' s f b.
Proof. exact (@lem7107591 (@I (A -> real) f x') (term732 A s f) b h1). Qed.
Lemma lem7107595 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term818 A s f b.
Proof. exact (@lem7107592 A x' s f b h2 (@lem7107589 A x x'' x' s f x''' b h1 h3)). Qed.
Lemma lem7107596 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term947 A s f b.
Proof. exact (fun h0 : term820 A s f b => @lem7107595 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7107598 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107599 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term947 A s f b) = (term818 A s f b).
Proof. exact (@lem7107598 (term818 A s f b)). Qed.
Lemma lem7107600 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term818 A s f b.
Proof. exact (EQ_MP (@lem7107599 A s f b) (@lem7107596 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7107603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7107605 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term820 A s f b) = (term948 A s f b).
Proof. exact (@lem7107603 (term818 A s f b)). Qed.
Lemma lem7107608 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term948 A s f b.
Proof. exact (EQ_MP (@lem7107605 A s f b) (@lem7106111 A s f b h1)). Qed.
Lemma lem7107611 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (@lem7107608 A s f b h3 (@lem7107600 A x x'' x' s f x''' b h1 h2 h4)). Qed.
Lemma lem7107612 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : term889.
Proof. exact (fun h0 : ~ False => @lem7107611 A x x'' x' s f x''' b h1 h2 h3 h4). Qed.
Lemma lem7107614 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107615 : term889 = False.
Proof. exact (@lem7107614 False). Qed.
Lemma lem7107616 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7107615) (@lem7107612 A x x'' x' s f x''' b h1 h2 h3 h4)). Qed.
Lemma lem7107855 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7107856 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7107855 A x). Qed.
Lemma lem7107857 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem7107856 A x'). Qed.
Lemma lem7107858 {A : Type'} (x' : A) : term890 A x'.
Proof. exact (fun h0 : term891 A x' => @lem7107857 A x'). Qed.
Lemma lem7107860 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107861 {A : Type'} (x' : A) : (term890 A x') = (x' = x').
Proof. exact (@lem7107860 (x' = x')). Qed.
Lemma lem7107862 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem7107861 A x') (@lem7107858 A x')). Qed.
Lemma lem7107868 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107869 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : (term864 A x' f _94637) = (term892 A f _94637 x').
Proof. exact (@lem7107868 (term795 A f _94637) (term835 A _94637 x')). Qed.
Lemma lem7107877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107878 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : (term893 A x' f _94637) = (term894 A f _94637 x').
Proof. exact (MK_COMB (@lem7107877) (@lem7107869 A f _94637 x')). Qed.
Lemma lem7107886 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : (term892 A f _94637 x') = (term892 A f _94637 x').
Proof. exact (eq_refl (term892 A f _94637 x')). Qed.
Lemma lem7107887 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : ((term864 A x' f _94637) = (term892 A f _94637 x')) = ((term892 A f _94637 x') = (term892 A f _94637 x')).
Proof. exact (MK_COMB (@lem7107878 A f _94637 x') (@lem7107886 A f _94637 x')). Qed.
Lemma lem7107889 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107890 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107889 Prop x). Qed.
Lemma lem7107891 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : ((term892 A f _94637 x') = (term892 A f _94637 x')) = True.
Proof. exact (@lem7107890 (term892 A f _94637 x')). Qed.
Lemma lem7107892 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : ((term864 A x' f _94637) = (term892 A f _94637 x')) = True.
Proof. exact (TRANS (@lem7107887 A f _94637 x') (@lem7107891 A f _94637 x')). Qed.
Lemma lem7107893 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : True = ((term864 A x' f _94637) = (term892 A f _94637 x')).
Proof. exact (SYM (@lem7107892 A f _94637 x')). Qed.
Lemma lem7107894 {A : Type'} (f : A -> real) (_94637 : A) (x' : A) : (term864 A x' f _94637) = (term892 A f _94637 x').
Proof. exact (EQ_MP (@lem7107893 A f _94637 x') (@lem0)). Qed.
Lemma lem7107895 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term892 A f _94637 x'.
Proof. exact (EQ_MP (@lem7107894 A f _94637 x') (@lem7105641 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7107897 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107898 {A : Type'} (x' : A) (f : A -> real) (_94637 : A) : (term892 A f _94637 x') = (term895 A x' f _94637).
Proof. exact (@lem7107897 (term835 A _94637 x') (term795 A f _94637)). Qed.
Lemma lem7107900 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107901 {A : Type'} (_94637 : A) (x' : A) : (term896 A _94637 x') = (_94637 = x').
Proof. exact (@lem7107900 (_94637 = x')). Qed.
Lemma lem7107902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107903 {A : Type'} (_94637 : A) (x' : A) : (term897 A _94637 x') = (term898 A _94637 x').
Proof. exact (MK_COMB (@lem7107902) (@lem7107901 A _94637 x')). Qed.
Lemma lem7107904 {A : Type'} (f : A -> real) (_94637 : A) : (term795 A f _94637) = (term795 A f _94637).
Proof. exact (eq_refl (term795 A f _94637)). Qed.
Lemma lem7107905 {A : Type'} (x' : A) (f : A -> real) (_94637 : A) : (term895 A x' f _94637) = (term899 A x' f _94637).
Proof. exact (MK_COMB (@lem7107903 A _94637 x') (@lem7107904 A f _94637)). Qed.
Lemma lem7107906 {A : Type'} (x' : A) (f : A -> real) (_94637 : A) : (term892 A f _94637 x') = (term899 A x' f _94637).
Proof. exact (TRANS (@lem7107898 A x' f _94637) (@lem7107905 A x' f _94637)). Qed.
Lemma lem7107909 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94637.
Proof. exact (EQ_MP (@lem7107906 A x' f _94637) (@lem7107895 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7107910 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94637.
Proof. exact (@lem7107909 A _94637 x'' x' s f x''' b h1). Qed.
Lemma lem7107911 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term900 A f x'.
Proof. exact (@lem7107910 A x' x'' x' s f x''' b h1). Qed.
Lemma lem7107914 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (@lem7107911 A x'' x' s f x''' b h1 (@lem7107862 A x')). Qed.
Lemma lem7107915 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term887 A f x'.
Proof. exact (fun h0 : term824 A f x' => @lem7107914 A x'' x' s f x''' b h1). Qed.
Lemma lem7107917 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107918 {A : Type'} (f : A -> real) (x' : A) : (term887 A f x') = (term795 A f x').
Proof. exact (@lem7107917 (term795 A f x')). Qed.
Lemma lem7107919 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (EQ_MP (@lem7107918 A f x') (@lem7107915 A x'' x' s f x''' b h1)). Qed.
Lemma lem7107922 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (h1). Qed.
Lemma lem7107923 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term902 A s f.
Proof. exact (fun h0 : term735 A s f => @lem7107922 A s f h1). Qed.
Lemma lem7107925 (p : Prop) : (term903 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7107926 {A : Type'} (s : A -> Prop) (f : A -> real) : (term902 A s f) = (term901 A s f).
Proof. exact (@lem7107925 (term735 A s f)). Qed.
Lemma lem7107927 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (EQ_MP (@lem7107926 A s f) (@lem7107923 A s f h1)). Qed.
Lemma lem7107929 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107932 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term865 A x _94636 _94635) = (term904 A x _94635 _94636).
Proof. exact (@lem7107929 (term735 A _94636 _94635) (term752 A x _94635 _94636)). Qed.
Lemma lem7107935 {A : Type'} (_94635 : A -> real) (_94636 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94635 _94636.
Proof. exact (EQ_MP (@lem7107932 A x _94635 _94636) (@lem7105653 A _94636 _94635 x h1)). Qed.
Lemma lem7107936 {A : Type'} (_94635 : A -> real) (_94636 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94635 _94636.
Proof. exact (@lem7107935 A _94635 _94636 x h1). Qed.
Lemma lem7107937 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x f s.
Proof. exact (@lem7107936 A f s x h1). Qed.
Lemma lem7107940 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (@lem7107937 A f s x h1 (@lem7107927 A s f h2)). Qed.
Lemma lem7107941 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term905 A x f s.
Proof. exact (fun h0 : term906 A x f s => @lem7107940 A x s f h1 h2). Qed.
Lemma lem7107943 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107944 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term905 A x f s) = (term752 A x f s).
Proof. exact (@lem7107943 (term752 A x f s)). Qed.
Lemma lem7107945 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (EQ_MP (@lem7107944 A x f s) (@lem7107941 A x s f h1 h2)). Qed.
Lemma lem7107951 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7107952 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : (term859 A s f _94637) = (term877 A f _94637 s).
Proof. exact (@lem7107951 (term795 A f _94637) (term796 A _94637 s)). Qed.
Lemma lem7107958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7107959 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : (term878 A s f _94637) = (term879 A f _94637 s).
Proof. exact (MK_COMB (@lem7107958) (@lem7107952 A f _94637 s)). Qed.
Lemma lem7107965 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : (term877 A f _94637 s) = (term877 A f _94637 s).
Proof. exact (eq_refl (term877 A f _94637 s)). Qed.
Lemma lem7107966 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : ((term859 A s f _94637) = (term877 A f _94637 s)) = ((term877 A f _94637 s) = (term877 A f _94637 s)).
Proof. exact (MK_COMB (@lem7107959 A f _94637 s) (@lem7107965 A f _94637 s)). Qed.
Lemma lem7107968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7107969 (x : Prop) : (x = x) = True.
Proof. exact (@lem7107968 Prop x). Qed.
Lemma lem7107970 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : ((term877 A f _94637 s) = (term877 A f _94637 s)) = True.
Proof. exact (@lem7107969 (term877 A f _94637 s)). Qed.
Lemma lem7107971 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : ((term859 A s f _94637) = (term877 A f _94637 s)) = True.
Proof. exact (TRANS (@lem7107966 A f _94637 s) (@lem7107970 A f _94637 s)). Qed.
Lemma lem7107972 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : True = ((term859 A s f _94637) = (term877 A f _94637 s)).
Proof. exact (SYM (@lem7107971 A f _94637 s)). Qed.
Lemma lem7107973 {A : Type'} (f : A -> real) (_94637 : A) (s : A -> Prop) : (term859 A s f _94637) = (term877 A f _94637 s).
Proof. exact (EQ_MP (@lem7107972 A f _94637 s) (@lem0)). Qed.
Lemma lem7107974 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term877 A f _94637 s.
Proof. exact (EQ_MP (@lem7107973 A f _94637 s) (@lem7105647 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7107976 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7107977 {A : Type'} (s : A -> Prop) (f : A -> real) (_94637 : A) : (term877 A f _94637 s) = (term881 A s f _94637).
Proof. exact (@lem7107976 (term796 A _94637 s) (term795 A f _94637)). Qed.
Lemma lem7107979 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7107980 {A : Type'} (_94637 : A) (s : A -> Prop) : (term883 A _94637 s) = (term774 A _94637 s).
Proof. exact (@lem7107979 (term774 A _94637 s)). Qed.
Lemma lem7107981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7107982 {A : Type'} (_94637 : A) (s : A -> Prop) : (term884 A _94637 s) = (term885 A _94637 s).
Proof. exact (MK_COMB (@lem7107981) (@lem7107980 A _94637 s)). Qed.
Lemma lem7107983 {A : Type'} (f : A -> real) (_94637 : A) : (term795 A f _94637) = (term795 A f _94637).
Proof. exact (eq_refl (term795 A f _94637)). Qed.
Lemma lem7107984 {A : Type'} (s : A -> Prop) (f : A -> real) (_94637 : A) : (term881 A s f _94637) = (term886 A s f _94637).
Proof. exact (MK_COMB (@lem7107982 A _94637 s) (@lem7107983 A f _94637)). Qed.
Lemma lem7107985 {A : Type'} (s : A -> Prop) (f : A -> real) (_94637 : A) : (term877 A f _94637 s) = (term886 A s f _94637).
Proof. exact (TRANS (@lem7107977 A s f _94637) (@lem7107984 A s f _94637)). Qed.
Lemma lem7107988 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94637.
Proof. exact (EQ_MP (@lem7107985 A s f _94637) (@lem7107974 A _94637 x'' x' s f x''' b h1)). Qed.
Lemma lem7107989 {A : Type'} (_94637 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94637.
Proof. exact (@lem7107988 A _94637 x'' x' s f x''' b h1). Qed.
Lemma lem7107990 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term907 A x f s.
Proof. exact (@lem7107989 A (term736 A x f s) x'' x' s f x''' b h1). Qed.
Lemma lem7107993 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (@lem7107990 A x x'' x' s f x''' b h3 (@lem7107945 A x s f h1 h2)). Qed.
Lemma lem7107994 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term908 A x f s.
Proof. exact (fun h0 : term745 A x f s => @lem7107993 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7107996 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7107997 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term908 A x f s) = (term743 A x f s).
Proof. exact (@lem7107996 (term743 A x f s)). Qed.
Lemma lem7107998 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (EQ_MP (@lem7107997 A x f s) (@lem7107994 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108004 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108005 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term866 A x _94636 _94635) = (term909 A x _94635 _94636).
Proof. exact (@lem7108004 (term735 A _94636 _94635) (term745 A x _94635 _94636)). Qed.
Lemma lem7108011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108012 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term910 A x _94636 _94635) = (term911 A x _94635 _94636).
Proof. exact (MK_COMB (@lem7108011) (@lem7108005 A x _94635 _94636)). Qed.
Lemma lem7108018 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term909 A x _94635 _94636) = (term909 A x _94635 _94636).
Proof. exact (eq_refl (term909 A x _94635 _94636)). Qed.
Lemma lem7108019 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : ((term866 A x _94636 _94635) = (term909 A x _94635 _94636)) = ((term909 A x _94635 _94636) = (term909 A x _94635 _94636)).
Proof. exact (MK_COMB (@lem7108012 A x _94635 _94636) (@lem7108018 A x _94635 _94636)). Qed.
Lemma lem7108021 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108022 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108021 Prop x). Qed.
Lemma lem7108023 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : ((term909 A x _94635 _94636) = (term909 A x _94635 _94636)) = True.
Proof. exact (@lem7108022 (term909 A x _94635 _94636)). Qed.
Lemma lem7108024 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : ((term866 A x _94636 _94635) = (term909 A x _94635 _94636)) = True.
Proof. exact (TRANS (@lem7108019 A x _94635 _94636) (@lem7108023 A x _94635 _94636)). Qed.
Lemma lem7108025 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : True = ((term866 A x _94636 _94635) = (term909 A x _94635 _94636)).
Proof. exact (SYM (@lem7108024 A x _94635 _94636)). Qed.
Lemma lem7108026 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term866 A x _94636 _94635) = (term909 A x _94635 _94636).
Proof. exact (EQ_MP (@lem7108025 A x _94635 _94636) (@lem0)). Qed.
Lemma lem7108027 {A : Type'} (_94635 : A -> real) (_94636 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term909 A x _94635 _94636.
Proof. exact (EQ_MP (@lem7108026 A x _94635 _94636) (@lem7105659 A _94636 _94635 x h1)). Qed.
Lemma lem7108029 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108030 {A : Type'} (x : type710 A) (_94636 : A -> Prop) (_94635 : A -> real) : (term909 A x _94635 _94636) = (term912 A x _94636 _94635).
Proof. exact (@lem7108029 (term745 A x _94635 _94636) (term735 A _94636 _94635)). Qed.
Lemma lem7108032 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108033 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term913 A x _94635 _94636) = (term743 A x _94635 _94636).
Proof. exact (@lem7108032 (term743 A x _94635 _94636)). Qed.
Lemma lem7108034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108035 {A : Type'} (x : type710 A) (_94635 : A -> real) (_94636 : A -> Prop) : (term914 A x _94635 _94636) = (term915 A x _94635 _94636).
Proof. exact (MK_COMB (@lem7108034) (@lem7108033 A x _94635 _94636)). Qed.
Lemma lem7108036 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) : (term735 A _94636 _94635) = (term735 A _94636 _94635).
Proof. exact (eq_refl (term735 A _94636 _94635)). Qed.
Lemma lem7108037 {A : Type'} (x : type710 A) (_94636 : A -> Prop) (_94635 : A -> real) : (term912 A x _94636 _94635) = (term916 A x _94636 _94635).
Proof. exact (MK_COMB (@lem7108035 A x _94635 _94636) (@lem7108036 A _94636 _94635)). Qed.
Lemma lem7108038 {A : Type'} (x : type710 A) (_94636 : A -> Prop) (_94635 : A -> real) : (term909 A x _94635 _94636) = (term916 A x _94636 _94635).
Proof. exact (TRANS (@lem7108030 A x _94636 _94635) (@lem7108037 A x _94636 _94635)). Qed.
Lemma lem7108041 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94636 _94635.
Proof. exact (EQ_MP (@lem7108038 A x _94636 _94635) (@lem7108027 A _94635 _94636 x h1)). Qed.
Lemma lem7108042 {A : Type'} (_94636 : A -> Prop) (_94635 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94636 _94635.
Proof. exact (@lem7108041 A _94636 _94635 x h1). Qed.
Lemma lem7108043 {A : Type'} (s : A -> Prop) (f : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x s f.
Proof. exact (@lem7108042 A s f x h1). Qed.
Lemma lem7108046 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (@lem7108043 A s f x h1 (@lem7107998 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108047 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term917 A s f.
Proof. exact (fun h0 : term901 A s f => @lem7108046 A x x'' x' s f x''' b h1 h0 h2). Qed.
Lemma lem7108049 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108050 {A : Type'} (s : A -> Prop) (f : A -> real) : (term917 A s f) = (term735 A s f).
Proof. exact (@lem7108049 (term735 A s f)). Qed.
Lemma lem7108051 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (EQ_MP (@lem7108050 A s f) (@lem7108047 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7108053 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (proj1 (@lem7104522 A x'' x' s f x''' b h1)). Qed.
Lemma lem7108054 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term918 A x' s f b.
Proof. exact (fun h0 : term919 A x' s f b => @lem7108053 A x'' x' s f x''' b h1). Qed.
Lemma lem7108056 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108057 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term918 A x' s f b) = (term790 A x' s f b).
Proof. exact (@lem7108056 (term790 A x' s f b)). Qed.
Lemma lem7108058 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (EQ_MP (@lem7108057 A x' s f b) (@lem7108054 A x'' x' s f x''' b h1)). Qed.
Lemma lem7108084 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108085 (_94632 : real) (_94633 : real) (_94634 : real) : (term920 _94632 _94633 _94634) = (term921 _94632 _94633 _94634).
Proof. exact (@lem7108084 (term699 _94633 _94634) (term711 _94632 _94633 _94634)). Qed.
Lemma lem7108091 (_94633 : real) : (term721 _94633) = (term721 _94633).
Proof. exact (eq_refl (term721 _94633)). Qed.
Lemma lem7108092 (_94632 : real) (_94633 : real) (_94634 : real) : (term862 _94632 _94633 _94634) = (term922 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108091 _94633) (@lem7108085 _94632 _94633 _94634)). Qed.
Lemma lem7108096 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7108097 (_94632 : real) (_94633 : real) (_94634 : real) : (term922 _94632 _94633 _94634) = (term923 _94632 _94633 _94634).
Proof. exact (@lem7108096 (term699 _94633 _94634) (term720 _94633) (term711 _94632 _94633 _94634)). Qed.
Lemma lem7108113 (_94632 : real) (_94633 : real) (_94634 : real) : (term862 _94632 _94633 _94634) = (term923 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7108092 _94632 _94633 _94634) (@lem7108097 _94632 _94633 _94634)). Qed.
Lemma lem7108114 (_94632 : real) : (term721 _94632) = (term721 _94632).
Proof. exact (eq_refl (term721 _94632)). Qed.
Lemma lem7108115 (_94632 : real) (_94633 : real) (_94634 : real) : (term863 _94632 _94633 _94634) = (term924 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108114 _94632) (@lem7108113 _94632 _94633 _94634)). Qed.
Lemma lem7108119 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7108120 (_94632 : real) (_94633 : real) (_94634 : real) : (term924 _94632 _94633 _94634) = (term925 _94632 _94633 _94634).
Proof. exact (@lem7108119 (term699 _94633 _94634) (term720 _94632) (term722 _94632 _94633 _94634)). Qed.
Lemma lem7108146 (_94632 : real) (_94633 : real) (_94634 : real) : (term863 _94632 _94633 _94634) = (term925 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7108115 _94632 _94633 _94634) (@lem7108120 _94632 _94633 _94634)). Qed.
Lemma lem7108147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108148 (_94632 : real) (_94633 : real) (_94634 : real) : (term926 _94632 _94633 _94634) = (term927 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108147) (@lem7108146 _94632 _94633 _94634)). Qed.
Lemma lem7108174 (_94632 : real) (_94633 : real) (_94634 : real) : (term925 _94632 _94633 _94634) = (term925 _94632 _94633 _94634).
Proof. exact (eq_refl (term925 _94632 _94633 _94634)). Qed.
Lemma lem7108175 (_94632 : real) (_94633 : real) (_94634 : real) : ((term863 _94632 _94633 _94634) = (term925 _94632 _94633 _94634)) = ((term925 _94632 _94633 _94634) = (term925 _94632 _94633 _94634)).
Proof. exact (MK_COMB (@lem7108148 _94632 _94633 _94634) (@lem7108174 _94632 _94633 _94634)). Qed.
Lemma lem7108177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108178 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108177 Prop x). Qed.
Lemma lem7108179 (_94632 : real) (_94633 : real) (_94634 : real) : ((term925 _94632 _94633 _94634) = (term925 _94632 _94633 _94634)) = True.
Proof. exact (@lem7108178 (term925 _94632 _94633 _94634)). Qed.
Lemma lem7108180 (_94632 : real) (_94633 : real) (_94634 : real) : ((term863 _94632 _94633 _94634) = (term925 _94632 _94633 _94634)) = True.
Proof. exact (TRANS (@lem7108175 _94632 _94633 _94634) (@lem7108179 _94632 _94633 _94634)). Qed.
Lemma lem7108181 (_94632 : real) (_94633 : real) (_94634 : real) : True = ((term863 _94632 _94633 _94634) = (term925 _94632 _94633 _94634)).
Proof. exact (SYM (@lem7108180 _94632 _94633 _94634)). Qed.
Lemma lem7108182 (_94632 : real) (_94633 : real) (_94634 : real) : (term863 _94632 _94633 _94634) = (term925 _94632 _94633 _94634).
Proof. exact (EQ_MP (@lem7108181 _94632 _94633 _94634) (@lem0)). Qed.
Lemma lem7108183 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term925 _94632 _94633 _94634.
Proof. exact (EQ_MP (@lem7108182 _94632 _94633 _94634) (@lem7105695 _94632 _94633 _94634 h1)). Qed.
Lemma lem7108185 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108186 (_94632 : real) (_94633 : real) (_94634 : real) : (term925 _94632 _94633 _94634) = (term928 _94632 _94633 _94634).
Proof. exact (@lem7108185 (term723 _94632 _94633 _94634) (term699 _94633 _94634)). Qed.
Lemma lem7108188 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7108189 (_94632 : real) (_94633 : real) (_94634 : real) : (term931 _94632 _94633 _94634) = (term932 _94632 _94633 _94634).
Proof. exact (@lem7108188 (term720 _94632) (term722 _94632 _94633 _94634)). Qed.
Lemma lem7108191 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108192 (_94632 : real) : (term933 _94632) = (term718 _94632).
Proof. exact (@lem7108191 (term718 _94632)). Qed.
Lemma lem7108193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7108194 (_94632 : real) : (term934 _94632) = (term935 _94632).
Proof. exact (MK_COMB (@lem7108193) (@lem7108192 _94632)). Qed.
Lemma lem7108196 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7108197 (_94632 : real) (_94633 : real) (_94634 : real) : (term936 _94632 _94633 _94634) = (term937 _94632 _94633 _94634).
Proof. exact (@lem7108196 (term720 _94633) (term711 _94632 _94633 _94634)). Qed.
Lemma lem7108199 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108200 (_94633 : real) : (term933 _94633) = (term718 _94633).
Proof. exact (@lem7108199 (term718 _94633)). Qed.
Lemma lem7108201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7108202 (_94633 : real) : (term934 _94633) = (term935 _94633).
Proof. exact (MK_COMB (@lem7108201) (@lem7108200 _94633)). Qed.
Lemma lem7108204 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108205 (_94632 : real) (_94633 : real) (_94634 : real) : (term938 _94632 _94633 _94634) = (term709 _94632 _94633 _94634).
Proof. exact (@lem7108204 (term709 _94632 _94633 _94634)). Qed.
Lemma lem7108206 (_94632 : real) (_94633 : real) (_94634 : real) : (term937 _94632 _94633 _94634) = (term939 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108202 _94633) (@lem7108205 _94632 _94633 _94634)). Qed.
Lemma lem7108207 (_94632 : real) (_94633 : real) (_94634 : real) : (term936 _94632 _94633 _94634) = (term939 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7108197 _94632 _94633 _94634) (@lem7108206 _94632 _94633 _94634)). Qed.
Lemma lem7108208 (_94632 : real) (_94633 : real) (_94634 : real) : (term932 _94632 _94633 _94634) = (term940 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108194 _94632) (@lem7108207 _94632 _94633 _94634)). Qed.
Lemma lem7108209 (_94632 : real) (_94633 : real) (_94634 : real) : (term931 _94632 _94633 _94634) = (term940 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7108189 _94632 _94633 _94634) (@lem7108208 _94632 _94633 _94634)). Qed.
Lemma lem7108210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108211 (_94632 : real) (_94633 : real) (_94634 : real) : (term941 _94632 _94633 _94634) = (term942 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108210) (@lem7108209 _94632 _94633 _94634)). Qed.
Lemma lem7108212 (_94633 : real) (_94634 : real) : (term699 _94633 _94634) = (term699 _94633 _94634).
Proof. exact (eq_refl (term699 _94633 _94634)). Qed.
Lemma lem7108213 (_94632 : real) (_94633 : real) (_94634 : real) : (term928 _94632 _94633 _94634) = (term943 _94632 _94633 _94634).
Proof. exact (MK_COMB (@lem7108211 _94632 _94633 _94634) (@lem7108212 _94633 _94634)). Qed.
Lemma lem7108214 (_94632 : real) (_94633 : real) (_94634 : real) : (term925 _94632 _94633 _94634) = (term943 _94632 _94633 _94634).
Proof. exact (TRANS (@lem7108186 _94632 _94633 _94634) (@lem7108213 _94632 _94633 _94634)). Qed.
Lemma lem7108216 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term944 A x' s f b.
Proof. exact (conj (@lem7108051 A x x'' x' s f x''' b h1 h2) (@lem7108058 A x'' x' s f x''' b h2)). Qed.
Lemma lem7108217 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term945 A x' s f b.
Proof. exact (conj (@lem7107919 A x'' x' s f x''' b h2) (@lem7108216 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7108219 (_94632 : real) (_94633 : real) (_94634 : real) (h1 : term181) : term943 _94632 _94633 _94634.
Proof. exact (EQ_MP (@lem7108214 _94632 _94633 _94634) (@lem7108183 _94632 _94633 _94634 h1)). Qed.
Lemma lem7108220 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term181) : term946 A x' s f b.
Proof. exact (@lem7108219 (@I (A -> real) f x') (term732 A s f) b h1). Qed.
Lemma lem7108223 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term818 A s f b.
Proof. exact (@lem7108220 A x' s f b h2 (@lem7108217 A x x'' x' s f x''' b h1 h3)). Qed.
Lemma lem7108224 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term947 A s f b.
Proof. exact (fun h0 : term820 A s f b => @lem7108223 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7108226 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108227 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term947 A s f b) = (term818 A s f b).
Proof. exact (@lem7108226 (term818 A s f b)). Qed.
Lemma lem7108228 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term818 A s f b.
Proof. exact (EQ_MP (@lem7108227 A s f b) (@lem7108224 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108231 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7108233 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term820 A s f b) = (term948 A s f b).
Proof. exact (@lem7108231 (term818 A s f b)). Qed.
Lemma lem7108236 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term820 A s f b) : term948 A s f b.
Proof. exact (EQ_MP (@lem7108233 A s f b) (@lem7105633 A s f b h1)). Qed.
Lemma lem7108239 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (@lem7108236 A s f b h3 (@lem7108228 A x x'' x' s f x''' b h1 h2 h4)). Qed.
Lemma lem7108240 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : term889.
Proof. exact (fun h0 : ~ False => @lem7108239 A x x'' x' s f x''' b h1 h2 h3 h4). Qed.
Lemma lem7108242 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108243 : term889 = False.
Proof. exact (@lem7108242 False). Qed.
Lemma lem7108244 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7108243) (@lem7108240 A x x'' x' s f x''' b h1 h2 h3 h4)). Qed.
Lemma lem7108483 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7108484 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7108483 A x). Qed.
Lemma lem7108485 {A : Type'} (x' : A) : x' = x'.
Proof. exact (@lem7108484 A x'). Qed.
Lemma lem7108486 {A : Type'} (x' : A) : term890 A x'.
Proof. exact (fun h0 : term891 A x' => @lem7108485 A x'). Qed.
Lemma lem7108488 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108489 {A : Type'} (x' : A) : (term890 A x') = (x' = x').
Proof. exact (@lem7108488 (x' = x')). Qed.
Lemma lem7108490 {A : Type'} (x' : A) : x' = x'.
Proof. exact (EQ_MP (@lem7108489 A x') (@lem7108486 A x')). Qed.
Lemma lem7108496 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108497 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : (term864 A x' f _94643) = (term892 A f _94643 x').
Proof. exact (@lem7108496 (term795 A f _94643) (term835 A _94643 x')). Qed.
Lemma lem7108505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108506 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : (term893 A x' f _94643) = (term894 A f _94643 x').
Proof. exact (MK_COMB (@lem7108505) (@lem7108497 A f _94643 x')). Qed.
Lemma lem7108514 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : (term892 A f _94643 x') = (term892 A f _94643 x').
Proof. exact (eq_refl (term892 A f _94643 x')). Qed.
Lemma lem7108515 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : ((term864 A x' f _94643) = (term892 A f _94643 x')) = ((term892 A f _94643 x') = (term892 A f _94643 x')).
Proof. exact (MK_COMB (@lem7108506 A f _94643 x') (@lem7108514 A f _94643 x')). Qed.
Lemma lem7108517 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108518 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108517 Prop x). Qed.
Lemma lem7108519 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : ((term892 A f _94643 x') = (term892 A f _94643 x')) = True.
Proof. exact (@lem7108518 (term892 A f _94643 x')). Qed.
Lemma lem7108520 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : ((term864 A x' f _94643) = (term892 A f _94643 x')) = True.
Proof. exact (TRANS (@lem7108515 A f _94643 x') (@lem7108519 A f _94643 x')). Qed.
Lemma lem7108521 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : True = ((term864 A x' f _94643) = (term892 A f _94643 x')).
Proof. exact (SYM (@lem7108520 A f _94643 x')). Qed.
Lemma lem7108522 {A : Type'} (f : A -> real) (_94643 : A) (x' : A) : (term864 A x' f _94643) = (term892 A f _94643 x').
Proof. exact (EQ_MP (@lem7108521 A f _94643 x') (@lem0)). Qed.
Lemma lem7108523 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term892 A f _94643 x'.
Proof. exact (EQ_MP (@lem7108522 A f _94643 x') (@lem7106292 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7108525 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108526 {A : Type'} (x' : A) (f : A -> real) (_94643 : A) : (term892 A f _94643 x') = (term895 A x' f _94643).
Proof. exact (@lem7108525 (term835 A _94643 x') (term795 A f _94643)). Qed.
Lemma lem7108528 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108529 {A : Type'} (_94643 : A) (x' : A) : (term896 A _94643 x') = (_94643 = x').
Proof. exact (@lem7108528 (_94643 = x')). Qed.
Lemma lem7108530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108531 {A : Type'} (_94643 : A) (x' : A) : (term897 A _94643 x') = (term898 A _94643 x').
Proof. exact (MK_COMB (@lem7108530) (@lem7108529 A _94643 x')). Qed.
Lemma lem7108532 {A : Type'} (f : A -> real) (_94643 : A) : (term795 A f _94643) = (term795 A f _94643).
Proof. exact (eq_refl (term795 A f _94643)). Qed.
Lemma lem7108533 {A : Type'} (x' : A) (f : A -> real) (_94643 : A) : (term895 A x' f _94643) = (term899 A x' f _94643).
Proof. exact (MK_COMB (@lem7108531 A _94643 x') (@lem7108532 A f _94643)). Qed.
Lemma lem7108534 {A : Type'} (x' : A) (f : A -> real) (_94643 : A) : (term892 A f _94643 x') = (term899 A x' f _94643).
Proof. exact (TRANS (@lem7108526 A x' f _94643) (@lem7108533 A x' f _94643)). Qed.
Lemma lem7108537 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94643.
Proof. exact (EQ_MP (@lem7108534 A x' f _94643) (@lem7108523 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7108538 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term899 A x' f _94643.
Proof. exact (@lem7108537 A _94643 x'' x' s f x''' b h1). Qed.
Lemma lem7108539 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term900 A f x'.
Proof. exact (@lem7108538 A x' x'' x' s f x''' b h1). Qed.
Lemma lem7108542 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (@lem7108539 A x'' x' s f x''' b h1 (@lem7108490 A x')). Qed.
Lemma lem7108543 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term887 A f x'.
Proof. exact (fun h0 : term824 A f x' => @lem7108542 A x'' x' s f x''' b h1). Qed.
Lemma lem7108545 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108546 {A : Type'} (f : A -> real) (x' : A) : (term887 A f x') = (term795 A f x').
Proof. exact (@lem7108545 (term795 A f x')). Qed.
Lemma lem7108547 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term795 A f x'.
Proof. exact (EQ_MP (@lem7108546 A f x') (@lem7108543 A x'' x' s f x''' b h1)). Qed.
Lemma lem7108550 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (h1). Qed.
Lemma lem7108551 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term902 A s f.
Proof. exact (fun h0 : term735 A s f => @lem7108550 A s f h1). Qed.
Lemma lem7108553 (p : Prop) : (term903 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7108554 {A : Type'} (s : A -> Prop) (f : A -> real) : (term902 A s f) = (term901 A s f).
Proof. exact (@lem7108553 (term735 A s f)). Qed.
Lemma lem7108555 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term901 A s f) : term901 A s f.
Proof. exact (EQ_MP (@lem7108554 A s f) (@lem7108551 A s f h1)). Qed.
Lemma lem7108557 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108560 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term865 A x _94642 _94641) = (term904 A x _94641 _94642).
Proof. exact (@lem7108557 (term735 A _94642 _94641) (term752 A x _94641 _94642)). Qed.
Lemma lem7108563 {A : Type'} (_94641 : A -> real) (_94642 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94641 _94642.
Proof. exact (EQ_MP (@lem7108560 A x _94641 _94642) (@lem7106320 A _94642 _94641 x h1)). Qed.
Lemma lem7108564 {A : Type'} (_94641 : A -> real) (_94642 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x _94641 _94642.
Proof. exact (@lem7108563 A _94641 _94642 x h1). Qed.
Lemma lem7108565 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type710 A) (h1 : term695 A x) : term904 A x f s.
Proof. exact (@lem7108564 A f s x h1). Qed.
Lemma lem7108568 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (@lem7108565 A f s x h1 (@lem7108555 A s f h2)). Qed.
Lemma lem7108569 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term905 A x f s.
Proof. exact (fun h0 : term906 A x f s => @lem7108568 A x s f h1 h2). Qed.
Lemma lem7108571 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108572 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term905 A x f s) = (term752 A x f s).
Proof. exact (@lem7108571 (term752 A x f s)). Qed.
Lemma lem7108573 {A : Type'} (x : type710 A) (s : A -> Prop) (f : A -> real) (h1 : term695 A x) (h2 : term901 A s f) : term752 A x f s.
Proof. exact (EQ_MP (@lem7108572 A x f s) (@lem7108569 A x s f h1 h2)). Qed.
Lemma lem7108579 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108580 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : (term859 A s f _94643) = (term877 A f _94643 s).
Proof. exact (@lem7108579 (term795 A f _94643) (term796 A _94643 s)). Qed.
Lemma lem7108586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108587 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : (term878 A s f _94643) = (term879 A f _94643 s).
Proof. exact (MK_COMB (@lem7108586) (@lem7108580 A f _94643 s)). Qed.
Lemma lem7108593 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : (term877 A f _94643 s) = (term877 A f _94643 s).
Proof. exact (eq_refl (term877 A f _94643 s)). Qed.
Lemma lem7108594 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : ((term859 A s f _94643) = (term877 A f _94643 s)) = ((term877 A f _94643 s) = (term877 A f _94643 s)).
Proof. exact (MK_COMB (@lem7108587 A f _94643 s) (@lem7108593 A f _94643 s)). Qed.
Lemma lem7108596 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108597 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108596 Prop x). Qed.
Lemma lem7108598 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : ((term877 A f _94643 s) = (term877 A f _94643 s)) = True.
Proof. exact (@lem7108597 (term877 A f _94643 s)). Qed.
Lemma lem7108599 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : ((term859 A s f _94643) = (term877 A f _94643 s)) = True.
Proof. exact (TRANS (@lem7108594 A f _94643 s) (@lem7108598 A f _94643 s)). Qed.
Lemma lem7108600 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : True = ((term859 A s f _94643) = (term877 A f _94643 s)).
Proof. exact (SYM (@lem7108599 A f _94643 s)). Qed.
Lemma lem7108601 {A : Type'} (f : A -> real) (_94643 : A) (s : A -> Prop) : (term859 A s f _94643) = (term877 A f _94643 s).
Proof. exact (EQ_MP (@lem7108600 A f _94643 s) (@lem0)). Qed.
Lemma lem7108602 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term877 A f _94643 s.
Proof. exact (EQ_MP (@lem7108601 A f _94643 s) (@lem7106306 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7108604 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108605 {A : Type'} (s : A -> Prop) (f : A -> real) (_94643 : A) : (term877 A f _94643 s) = (term881 A s f _94643).
Proof. exact (@lem7108604 (term796 A _94643 s) (term795 A f _94643)). Qed.
Lemma lem7108607 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108608 {A : Type'} (_94643 : A) (s : A -> Prop) : (term883 A _94643 s) = (term774 A _94643 s).
Proof. exact (@lem7108607 (term774 A _94643 s)). Qed.
Lemma lem7108609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108610 {A : Type'} (_94643 : A) (s : A -> Prop) : (term884 A _94643 s) = (term885 A _94643 s).
Proof. exact (MK_COMB (@lem7108609) (@lem7108608 A _94643 s)). Qed.
Lemma lem7108611 {A : Type'} (f : A -> real) (_94643 : A) : (term795 A f _94643) = (term795 A f _94643).
Proof. exact (eq_refl (term795 A f _94643)). Qed.
Lemma lem7108612 {A : Type'} (s : A -> Prop) (f : A -> real) (_94643 : A) : (term881 A s f _94643) = (term886 A s f _94643).
Proof. exact (MK_COMB (@lem7108610 A _94643 s) (@lem7108611 A f _94643)). Qed.
Lemma lem7108613 {A : Type'} (s : A -> Prop) (f : A -> real) (_94643 : A) : (term877 A f _94643 s) = (term886 A s f _94643).
Proof. exact (TRANS (@lem7108605 A s f _94643) (@lem7108612 A s f _94643)). Qed.
Lemma lem7108616 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94643.
Proof. exact (EQ_MP (@lem7108613 A s f _94643) (@lem7108602 A _94643 x'' x' s f x''' b h1)). Qed.
Lemma lem7108617 {A : Type'} (_94643 : A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term886 A s f _94643.
Proof. exact (@lem7108616 A _94643 x'' x' s f x''' b h1). Qed.
Lemma lem7108618 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term907 A x f s.
Proof. exact (@lem7108617 A (term736 A x f s) x'' x' s f x''' b h1). Qed.
Lemma lem7108621 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (@lem7108618 A x x'' x' s f x''' b h3 (@lem7108573 A x s f h1 h2)). Qed.
Lemma lem7108622 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term908 A x f s.
Proof. exact (fun h0 : term745 A x f s => @lem7108621 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7108624 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108625 {A : Type'} (x : type710 A) (f : A -> real) (s : A -> Prop) : (term908 A x f s) = (term743 A x f s).
Proof. exact (@lem7108624 (term743 A x f s)). Qed.
Lemma lem7108626 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term743 A x f s.
Proof. exact (EQ_MP (@lem7108625 A x f s) (@lem7108622 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108633 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term866 A x _94642 _94641) = (term909 A x _94641 _94642).
Proof. exact (@lem7108632 (term735 A _94642 _94641) (term745 A x _94641 _94642)). Qed.
Lemma lem7108639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108640 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term910 A x _94642 _94641) = (term911 A x _94641 _94642).
Proof. exact (MK_COMB (@lem7108639) (@lem7108633 A x _94641 _94642)). Qed.
Lemma lem7108646 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term909 A x _94641 _94642) = (term909 A x _94641 _94642).
Proof. exact (eq_refl (term909 A x _94641 _94642)). Qed.
Lemma lem7108647 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : ((term866 A x _94642 _94641) = (term909 A x _94641 _94642)) = ((term909 A x _94641 _94642) = (term909 A x _94641 _94642)).
Proof. exact (MK_COMB (@lem7108640 A x _94641 _94642) (@lem7108646 A x _94641 _94642)). Qed.
Lemma lem7108649 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108650 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108649 Prop x). Qed.
Lemma lem7108651 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : ((term909 A x _94641 _94642) = (term909 A x _94641 _94642)) = True.
Proof. exact (@lem7108650 (term909 A x _94641 _94642)). Qed.
Lemma lem7108652 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : ((term866 A x _94642 _94641) = (term909 A x _94641 _94642)) = True.
Proof. exact (TRANS (@lem7108647 A x _94641 _94642) (@lem7108651 A x _94641 _94642)). Qed.
Lemma lem7108653 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : True = ((term866 A x _94642 _94641) = (term909 A x _94641 _94642)).
Proof. exact (SYM (@lem7108652 A x _94641 _94642)). Qed.
Lemma lem7108654 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term866 A x _94642 _94641) = (term909 A x _94641 _94642).
Proof. exact (EQ_MP (@lem7108653 A x _94641 _94642) (@lem0)). Qed.
Lemma lem7108655 {A : Type'} (_94641 : A -> real) (_94642 : A -> Prop) (x : type710 A) (h1 : term695 A x) : term909 A x _94641 _94642.
Proof. exact (EQ_MP (@lem7108654 A x _94641 _94642) (@lem7106334 A _94642 _94641 x h1)). Qed.
Lemma lem7108657 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108658 {A : Type'} (x : type710 A) (_94642 : A -> Prop) (_94641 : A -> real) : (term909 A x _94641 _94642) = (term912 A x _94642 _94641).
Proof. exact (@lem7108657 (term745 A x _94641 _94642) (term735 A _94642 _94641)). Qed.
Lemma lem7108660 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108661 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term913 A x _94641 _94642) = (term743 A x _94641 _94642).
Proof. exact (@lem7108660 (term743 A x _94641 _94642)). Qed.
Lemma lem7108662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108663 {A : Type'} (x : type710 A) (_94641 : A -> real) (_94642 : A -> Prop) : (term914 A x _94641 _94642) = (term915 A x _94641 _94642).
Proof. exact (MK_COMB (@lem7108662) (@lem7108661 A x _94641 _94642)). Qed.
Lemma lem7108664 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) : (term735 A _94642 _94641) = (term735 A _94642 _94641).
Proof. exact (eq_refl (term735 A _94642 _94641)). Qed.
Lemma lem7108665 {A : Type'} (x : type710 A) (_94642 : A -> Prop) (_94641 : A -> real) : (term912 A x _94642 _94641) = (term916 A x _94642 _94641).
Proof. exact (MK_COMB (@lem7108663 A x _94641 _94642) (@lem7108664 A _94642 _94641)). Qed.
Lemma lem7108666 {A : Type'} (x : type710 A) (_94642 : A -> Prop) (_94641 : A -> real) : (term909 A x _94641 _94642) = (term916 A x _94642 _94641).
Proof. exact (TRANS (@lem7108658 A x _94642 _94641) (@lem7108665 A x _94642 _94641)). Qed.
Lemma lem7108669 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94642 _94641.
Proof. exact (EQ_MP (@lem7108666 A x _94642 _94641) (@lem7108655 A _94641 _94642 x h1)). Qed.
Lemma lem7108670 {A : Type'} (_94642 : A -> Prop) (_94641 : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x _94642 _94641.
Proof. exact (@lem7108669 A _94642 _94641 x h1). Qed.
Lemma lem7108671 {A : Type'} (s : A -> Prop) (f : A -> real) (x : type710 A) (h1 : term695 A x) : term916 A x s f.
Proof. exact (@lem7108670 A s f x h1). Qed.
Lemma lem7108674 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term901 A s f) (h3 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (@lem7108671 A s f x h1 (@lem7108626 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108675 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term917 A s f.
Proof. exact (fun h0 : term901 A s f => @lem7108674 A x x'' x' s f x''' b h1 h0 h2). Qed.
Lemma lem7108677 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108678 {A : Type'} (s : A -> Prop) (f : A -> real) : (term917 A s f) = (term735 A s f).
Proof. exact (@lem7108677 (term735 A s f)). Qed.
Lemma lem7108679 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term735 A s f.
Proof. exact (EQ_MP (@lem7108678 A s f) (@lem7108675 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7108681 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (proj1 (@lem7104522 A x'' x' s f x''' b h1)). Qed.
Lemma lem7108682 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term918 A x' s f b.
Proof. exact (fun h0 : term919 A x' s f b => @lem7108681 A x'' x' s f x''' b h1). Qed.
Lemma lem7108684 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108685 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (b : real) : (term918 A x' s f b) = (term790 A x' s f b).
Proof. exact (@lem7108684 (term790 A x' s f b)). Qed.
Lemma lem7108686 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term790 A x' s f b.
Proof. exact (EQ_MP (@lem7108685 A x' s f b) (@lem7108682 A x'' x' s f x''' b h1)). Qed.
Lemma lem7108712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7108713 (_94638 : real) (_94639 : real) (_94640 : real) : (term949 _94639 _94638 _94640) = (term950 _94638 _94639 _94640).
Proof. exact (@lem7108712 (term699 _94638 _94640) (term711 _94638 _94639 _94640)). Qed.
Lemma lem7108719 (_94639 : real) : (term721 _94639) = (term721 _94639).
Proof. exact (eq_refl (term721 _94639)). Qed.
Lemma lem7108720 (_94638 : real) (_94639 : real) (_94640 : real) : (term869 _94639 _94638 _94640) = (term951 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108719 _94639) (@lem7108713 _94638 _94639 _94640)). Qed.
Lemma lem7108724 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7108725 (_94638 : real) (_94639 : real) (_94640 : real) : (term951 _94638 _94639 _94640) = (term952 _94638 _94639 _94640).
Proof. exact (@lem7108724 (term699 _94638 _94640) (term720 _94639) (term711 _94638 _94639 _94640)). Qed.
Lemma lem7108741 (_94638 : real) (_94639 : real) (_94640 : real) : (term869 _94639 _94638 _94640) = (term952 _94638 _94639 _94640).
Proof. exact (TRANS (@lem7108720 _94638 _94639 _94640) (@lem7108725 _94638 _94639 _94640)). Qed.
Lemma lem7108742 (_94638 : real) : (term721 _94638) = (term721 _94638).
Proof. exact (eq_refl (term721 _94638)). Qed.
Lemma lem7108743 (_94638 : real) (_94639 : real) (_94640 : real) : (term870 _94639 _94638 _94640) = (term953 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108742 _94638) (@lem7108741 _94638 _94639 _94640)). Qed.
Lemma lem7108747 (q : Prop) (p : Prop) (r : Prop) : (term176 p q r) = (term176 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7108748 (_94638 : real) (_94639 : real) (_94640 : real) : (term953 _94638 _94639 _94640) = (term954 _94638 _94639 _94640).
Proof. exact (@lem7108747 (term699 _94638 _94640) (term720 _94638) (term722 _94638 _94639 _94640)). Qed.
Lemma lem7108774 (_94638 : real) (_94639 : real) (_94640 : real) : (term870 _94639 _94638 _94640) = (term954 _94638 _94639 _94640).
Proof. exact (TRANS (@lem7108743 _94638 _94639 _94640) (@lem7108748 _94638 _94639 _94640)). Qed.
Lemma lem7108775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7108776 (_94638 : real) (_94639 : real) (_94640 : real) : (term955 _94639 _94638 _94640) = (term956 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108775) (@lem7108774 _94638 _94639 _94640)). Qed.
Lemma lem7108802 (_94638 : real) (_94639 : real) (_94640 : real) : (term954 _94638 _94639 _94640) = (term954 _94638 _94639 _94640).
Proof. exact (eq_refl (term954 _94638 _94639 _94640)). Qed.
Lemma lem7108803 (_94638 : real) (_94639 : real) (_94640 : real) : ((term870 _94639 _94638 _94640) = (term954 _94638 _94639 _94640)) = ((term954 _94638 _94639 _94640) = (term954 _94638 _94639 _94640)).
Proof. exact (MK_COMB (@lem7108776 _94638 _94639 _94640) (@lem7108802 _94638 _94639 _94640)). Qed.
Lemma lem7108805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7108806 (x : Prop) : (x = x) = True.
Proof. exact (@lem7108805 Prop x). Qed.
Lemma lem7108807 (_94638 : real) (_94639 : real) (_94640 : real) : ((term954 _94638 _94639 _94640) = (term954 _94638 _94639 _94640)) = True.
Proof. exact (@lem7108806 (term954 _94638 _94639 _94640)). Qed.
Lemma lem7108808 (_94638 : real) (_94639 : real) (_94640 : real) : ((term870 _94639 _94638 _94640) = (term954 _94638 _94639 _94640)) = True.
Proof. exact (TRANS (@lem7108803 _94638 _94639 _94640) (@lem7108807 _94638 _94639 _94640)). Qed.
Lemma lem7108809 (_94638 : real) (_94639 : real) (_94640 : real) : True = ((term870 _94639 _94638 _94640) = (term954 _94638 _94639 _94640)).
Proof. exact (SYM (@lem7108808 _94638 _94639 _94640)). Qed.
Lemma lem7108810 (_94638 : real) (_94639 : real) (_94640 : real) : (term870 _94639 _94638 _94640) = (term954 _94638 _94639 _94640).
Proof. exact (EQ_MP (@lem7108809 _94638 _94639 _94640) (@lem0)). Qed.
Lemma lem7108811 (_94638 : real) (_94639 : real) (_94640 : real) (h1 : term181) : term954 _94638 _94639 _94640.
Proof. exact (EQ_MP (@lem7108810 _94638 _94639 _94640) (@lem7106348 _94639 _94638 _94640 h1)). Qed.
Lemma lem7108813 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7108814 (_94639 : real) (_94638 : real) (_94640 : real) : (term954 _94638 _94639 _94640) = (term957 _94639 _94638 _94640).
Proof. exact (@lem7108813 (term723 _94638 _94639 _94640) (term699 _94638 _94640)). Qed.
Lemma lem7108816 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7108817 (_94638 : real) (_94639 : real) (_94640 : real) : (term931 _94638 _94639 _94640) = (term932 _94638 _94639 _94640).
Proof. exact (@lem7108816 (term720 _94638) (term722 _94638 _94639 _94640)). Qed.
Lemma lem7108819 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108820 (_94638 : real) : (term933 _94638) = (term718 _94638).
Proof. exact (@lem7108819 (term718 _94638)). Qed.
Lemma lem7108821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7108822 (_94638 : real) : (term934 _94638) = (term935 _94638).
Proof. exact (MK_COMB (@lem7108821) (@lem7108820 _94638)). Qed.
Lemma lem7108824 (a : Prop) (b : Prop) : (term929 a b) = (term930 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7108825 (_94638 : real) (_94639 : real) (_94640 : real) : (term936 _94638 _94639 _94640) = (term937 _94638 _94639 _94640).
Proof. exact (@lem7108824 (term720 _94639) (term711 _94638 _94639 _94640)). Qed.
Lemma lem7108827 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108828 (_94639 : real) : (term933 _94639) = (term718 _94639).
Proof. exact (@lem7108827 (term718 _94639)). Qed.
Lemma lem7108829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7108830 (_94639 : real) : (term934 _94639) = (term935 _94639).
Proof. exact (MK_COMB (@lem7108829) (@lem7108828 _94639)). Qed.
Lemma lem7108832 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7108833 (_94638 : real) (_94639 : real) (_94640 : real) : (term938 _94638 _94639 _94640) = (term709 _94638 _94639 _94640).
Proof. exact (@lem7108832 (term709 _94638 _94639 _94640)). Qed.
Lemma lem7108834 (_94638 : real) (_94639 : real) (_94640 : real) : (term937 _94638 _94639 _94640) = (term939 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108830 _94639) (@lem7108833 _94638 _94639 _94640)). Qed.
Lemma lem7108835 (_94638 : real) (_94639 : real) (_94640 : real) : (term936 _94638 _94639 _94640) = (term939 _94638 _94639 _94640).
Proof. exact (TRANS (@lem7108825 _94638 _94639 _94640) (@lem7108834 _94638 _94639 _94640)). Qed.
Lemma lem7108836 (_94638 : real) (_94639 : real) (_94640 : real) : (term932 _94638 _94639 _94640) = (term940 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108822 _94638) (@lem7108835 _94638 _94639 _94640)). Qed.
Lemma lem7108837 (_94638 : real) (_94639 : real) (_94640 : real) : (term931 _94638 _94639 _94640) = (term940 _94638 _94639 _94640).
Proof. exact (TRANS (@lem7108817 _94638 _94639 _94640) (@lem7108836 _94638 _94639 _94640)). Qed.
Lemma lem7108838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7108839 (_94638 : real) (_94639 : real) (_94640 : real) : (term941 _94638 _94639 _94640) = (term942 _94638 _94639 _94640).
Proof. exact (MK_COMB (@lem7108838) (@lem7108837 _94638 _94639 _94640)). Qed.
Lemma lem7108840 (_94638 : real) (_94640 : real) : (term699 _94638 _94640) = (term699 _94638 _94640).
Proof. exact (eq_refl (term699 _94638 _94640)). Qed.
Lemma lem7108841 (_94639 : real) (_94638 : real) (_94640 : real) : (term957 _94639 _94638 _94640) = (term958 _94639 _94638 _94640).
Proof. exact (MK_COMB (@lem7108839 _94638 _94639 _94640) (@lem7108840 _94638 _94640)). Qed.
Lemma lem7108842 (_94639 : real) (_94638 : real) (_94640 : real) : (term954 _94638 _94639 _94640) = (term958 _94639 _94638 _94640).
Proof. exact (TRANS (@lem7108814 _94639 _94638 _94640) (@lem7108841 _94639 _94638 _94640)). Qed.
Lemma lem7108844 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term944 A x' s f b.
Proof. exact (conj (@lem7108679 A x x'' x' s f x''' b h1 h2) (@lem7108686 A x'' x' s f x''' b h2)). Qed.
Lemma lem7108845 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term606 A x'' x' s f x''' b) : term945 A x' s f b.
Proof. exact (conj (@lem7108547 A x'' x' s f x''' b h2) (@lem7108844 A x x'' x' s f x''' b h1 h2)). Qed.
Lemma lem7108847 (_94639 : real) (_94638 : real) (_94640 : real) (h1 : term181) : term958 _94639 _94638 _94640.
Proof. exact (EQ_MP (@lem7108842 _94639 _94638 _94640) (@lem7108811 _94638 _94639 _94640 h1)). Qed.
Lemma lem7108848 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (b : real) (h1 : term181) : term959 A s f x' b.
Proof. exact (@lem7108847 (term732 A s f) (@I (A -> real) f x') b h1). Qed.
Lemma lem7108851 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term771 A f x' b.
Proof. exact (@lem7108848 A s f x' b h2 (@lem7108845 A x x'' x' s f x''' b h1 h3)). Qed.
Lemma lem7108852 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term960 A f x' b.
Proof. exact (fun h0 : term773 A f x' b => @lem7108851 A x x'' x' s f x''' b h1 h2 h3). Qed.
Lemma lem7108854 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108855 {A : Type'} (f : A -> real) (x' : A) (b : real) : (term960 A f x' b) = (term771 A f x' b).
Proof. exact (@lem7108854 (term771 A f x' b)). Qed.
Lemma lem7108856 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : term771 A f x' b.
Proof. exact (EQ_MP (@lem7108855 A f x' b) (@lem7108852 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7108861 {A : Type'} (f : A -> real) (x' : A) (b : real) : (term773 A f x' b) = (term961 A f x' b).
Proof. exact (@lem7108859 (term771 A f x' b)). Qed.
Lemma lem7108864 {A : Type'} (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : x''' = x') : term961 A f x' b.
Proof. exact (EQ_MP (@lem7108861 A f x' b) (@lem7106236 A x'' s f b x''' x' h1 h2)). Qed.
Lemma lem7108867 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : False.
Proof. exact (@lem7108864 A x'' s f b x''' x' h3 h4 (@lem7108856 A x x'' x' s f x''' b h1 h2 h3)). Qed.
Lemma lem7108868 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : term889.
Proof. exact (fun h0 : ~ False => @lem7108867 A x x'' s f b x''' x' h1 h2 h3 h4). Qed.
Lemma lem7108870 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7108871 : term889 = False.
Proof. exact (@lem7108870 False). Qed.
Lemma lem7109111 {A : Type'} (x''' : A) (s : A -> Prop) (h1 : term774 A x''' s) : term774 A x''' s.
Proof. exact (h1). Qed.
Lemma lem7109112 {A : Type'} (x''' : A) (s : A -> Prop) (h1 : term774 A x''' s) : term875 A x''' s.
Proof. exact (fun h0 : term796 A x''' s => @lem7109111 A x''' s h1). Qed.
Lemma lem7109114 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7109115 {A : Type'} (x''' : A) (s : A -> Prop) : (term875 A x''' s) = (term774 A x''' s).
Proof. exact (@lem7109114 (term774 A x''' s)). Qed.
Lemma lem7109116 {A : Type'} (x''' : A) (s : A -> Prop) (h1 : term774 A x''' s) : term774 A x''' s.
Proof. exact (EQ_MP (@lem7109115 A x''' s) (@lem7109112 A x''' s h1)). Qed.
Lemma lem7109122 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7109123 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : (term810 A s f _94651 b) = (term962 A f b _94651 s).
Proof. exact (@lem7109122 (term771 A f _94651 b) (term796 A _94651 s)). Qed.
Lemma lem7109129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7109130 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : (term963 A s f _94651 b) = (term964 A f b _94651 s).
Proof. exact (MK_COMB (@lem7109129) (@lem7109123 A f b _94651 s)). Qed.
Lemma lem7109136 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : (term962 A f b _94651 s) = (term962 A f b _94651 s).
Proof. exact (eq_refl (term962 A f b _94651 s)). Qed.
Lemma lem7109137 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : ((term810 A s f _94651 b) = (term962 A f b _94651 s)) = ((term962 A f b _94651 s) = (term962 A f b _94651 s)).
Proof. exact (MK_COMB (@lem7109130 A f b _94651 s) (@lem7109136 A f b _94651 s)). Qed.
Lemma lem7109139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7109140 (x : Prop) : (x = x) = True.
Proof. exact (@lem7109139 Prop x). Qed.
Lemma lem7109141 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : ((term962 A f b _94651 s) = (term962 A f b _94651 s)) = True.
Proof. exact (@lem7109140 (term962 A f b _94651 s)). Qed.
Lemma lem7109142 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : ((term810 A s f _94651 b) = (term962 A f b _94651 s)) = True.
Proof. exact (TRANS (@lem7109137 A f b _94651 s) (@lem7109141 A f b _94651 s)). Qed.
Lemma lem7109143 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : True = ((term810 A s f _94651 b) = (term962 A f b _94651 s)).
Proof. exact (SYM (@lem7109142 A f b _94651 s)). Qed.
Lemma lem7109144 {A : Type'} (f : A -> real) (b : real) (_94651 : A) (s : A -> Prop) : (term810 A s f _94651 b) = (term962 A f b _94651 s).
Proof. exact (EQ_MP (@lem7109143 A f b _94651 s) (@lem0)). Qed.
Lemma lem7109145 {A : Type'} (_94651 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term962 A f b _94651 s.
Proof. exact (EQ_MP (@lem7109144 A f b _94651 s) (@lem7105785 A _94651 s f b h1)). Qed.
Lemma lem7109147 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7109148 {A : Type'} (s : A -> Prop) (f : A -> real) (_94651 : A) (b : real) : (term962 A f b _94651 s) = (term965 A s f _94651 b).
Proof. exact (@lem7109147 (term796 A _94651 s) (term771 A f _94651 b)). Qed.
Lemma lem7109150 (a : Prop) : (term882 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7109151 {A : Type'} (_94651 : A) (s : A -> Prop) : (term883 A _94651 s) = (term774 A _94651 s).
Proof. exact (@lem7109150 (term774 A _94651 s)). Qed.
Lemma lem7109152 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109153 {A : Type'} (_94651 : A) (s : A -> Prop) : (term884 A _94651 s) = (term885 A _94651 s).
Proof. exact (MK_COMB (@lem7109152) (@lem7109151 A _94651 s)). Qed.
Lemma lem7109154 {A : Type'} (f : A -> real) (_94651 : A) (b : real) : (term771 A f _94651 b) = (term771 A f _94651 b).
Proof. exact (eq_refl (term771 A f _94651 b)). Qed.
Lemma lem7109155 {A : Type'} (s : A -> Prop) (f : A -> real) (_94651 : A) (b : real) : (term965 A s f _94651 b) = (term966 A s f _94651 b).
Proof. exact (MK_COMB (@lem7109153 A _94651 s) (@lem7109154 A f _94651 b)). Qed.
Lemma lem7109156 {A : Type'} (s : A -> Prop) (f : A -> real) (_94651 : A) (b : real) : (term962 A f b _94651 s) = (term966 A s f _94651 b).
Proof. exact (TRANS (@lem7109148 A s f _94651 b) (@lem7109155 A s f _94651 b)). Qed.
Lemma lem7109159 {A : Type'} (_94651 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term966 A s f _94651 b.
Proof. exact (EQ_MP (@lem7109156 A s f _94651 b) (@lem7109145 A _94651 s f b h1)). Qed.
Lemma lem7109160 {A : Type'} (_94651 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term966 A s f _94651 b.
Proof. exact (@lem7109159 A _94651 s f b h1). Qed.
Lemma lem7109161 {A : Type'} (x''' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term812 A s f b) : term966 A s f x''' b.
Proof. exact (@lem7109160 A x''' s f b h1). Qed.
Lemma lem7109164 {A : Type'} (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term774 A x''' s) : term771 A f x''' b.
Proof. exact (@lem7109161 A x''' s f b h1 (@lem7109116 A x''' s h2)). Qed.
Lemma lem7109165 {A : Type'} (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term774 A x''' s) : term960 A f x''' b.
Proof. exact (fun h0 : term773 A f x''' b => @lem7109164 A f b x''' s h1 h2). Qed.
Lemma lem7109167 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7109168 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term960 A f x''' b) = (term771 A f x''' b).
Proof. exact (@lem7109167 (term771 A f x''' b)). Qed.
Lemma lem7109169 {A : Type'} (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term774 A x''' s) : term771 A f x''' b.
Proof. exact (EQ_MP (@lem7109168 A f x''' b) (@lem7109165 A f b x''' s h1 h2)). Qed.
Lemma lem7109172 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7109174 {A : Type'} (f : A -> real) (x''' : A) (b : real) : (term773 A f x''' b) = (term961 A f x''' b).
Proof. exact (@lem7109172 (term771 A f x''' b)). Qed.
Lemma lem7109177 {A : Type'} (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term606 A x'' x' s f x''' b) : term961 A f x''' b.
Proof. exact (EQ_MP (@lem7109174 A f x''' b) (@lem7105775 A x'' x' s f x''' b h1)). Qed.
Lemma lem7109180 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (@lem7109177 A x'' x' s f x''' b h2 (@lem7109169 A f b x''' s h1 h3)). Qed.
Lemma lem7109181 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : term889.
Proof. exact (fun h0 : ~ False => @lem7109180 A x'' x' f b x''' s h1 h2 h3). Qed.
Lemma lem7109183 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7109184 : term889 = False.
Proof. exact (@lem7109183 False). Qed.
Lemma lem7109185 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (EQ_MP (@lem7109184) (@lem7109181 A x'' x' f b x''' s h1 h2 h3)). Qed.
Lemma lem7109186 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : False.
Proof. exact (EQ_MP (@lem7108871) (@lem7108868 A x x'' s f b x''' x' h1 h2 h3 h4)). Qed.
Lemma lem7109187 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7107616 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7106111 A s f b h3)). Qed.
Lemma lem7109189 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109187 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7106111 A s f b h3)). Qed.
Lemma lem7109190 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : False.
Proof. exact (EQ_MP (@lem7106674) (@lem7106671 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7109191 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : (term774 A x''' s) = False.
Proof. exact (prop_ext (fun h4 : term774 A x''' s => @lem7109185 A x'' x' f b x''' s h1 h2 h3) (fun h4 : False => @lem7105787 A x''' s h3)). Qed.
Lemma lem7109192 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (EQ_MP (@lem7109191 A x'' x' f b x''' s h1 h2 h3) (@lem7105787 A x''' s h3)). Qed.
Lemma lem7109193 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : (x''' = x') = False.
Proof. exact (prop_ext (fun h5 : x''' = x' => @lem7109186 A x x'' s f b x''' x' h1 h2 h3 h4) (fun h5 : False => @lem7105711 A x''' x' h4)). Qed.
Lemma lem7109194 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : False.
Proof. exact (EQ_MP (@lem7109193 A x x'' s f b x''' x' h1 h2 h3 h4) (@lem7105711 A x''' x' h4)). Qed.
Lemma lem7109195 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7108244 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7105633 A s f b h3)). Qed.
Lemma lem7109196 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109195 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7105633 A s f b h3)). Qed.
Lemma lem7109197 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7109189 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7105561 A s f b h3)). Qed.
Lemma lem7109198 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109197 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7105561 A s f b h3)). Qed.
Lemma lem7109199 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : (term774 A x''' s) = False.
Proof. exact (prop_ext (fun h4 : term774 A x''' s => @lem7109192 A x'' x' f b x''' s h1 h2 h3) (fun h4 : False => @lem7105253 A x''' s h3)). Qed.
Lemma lem7109200 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (EQ_MP (@lem7109199 A x'' x' f b x''' s h1 h2 h3) (@lem7105253 A x''' s h3)). Qed.
Lemma lem7109201 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : (x''' = x') = False.
Proof. exact (prop_ext (fun h5 : x''' = x' => @lem7109194 A x x'' s f b x''' x' h1 h2 h3 h4) (fun h5 : False => @lem7105130 A x''' x' h4)). Qed.
Lemma lem7109202 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : False.
Proof. exact (EQ_MP (@lem7109201 A x x'' s f b x''' x' h1 h2 h3 h4) (@lem7105130 A x''' x' h4)). Qed.
Lemma lem7109203 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7109196 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7105003 A s f b h3)). Qed.
Lemma lem7109204 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109203 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7105003 A s f b h3)). Qed.
Lemma lem7109205 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7109198 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7104889 A s f b h3)). Qed.
Lemma lem7109206 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109205 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7104889 A s f b h3)). Qed.
Lemma lem7109207 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : (term774 A x''' s) = False.
Proof. exact (prop_ext (fun h4 : term774 A x''' s => @lem7109200 A x'' x' f b x''' s h1 h2 h3) (fun h4 : False => @lem7105253 A x''' s h3)). Qed.
Lemma lem7109208 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (EQ_MP (@lem7109207 A x'' x' f b x''' s h1 h2 h3) (@lem7105253 A x''' s h3)). Qed.
Lemma lem7109209 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : (term812 A s f b) = False.
Proof. exact (prop_ext (fun h4 : term812 A s f b => @lem7109208 A x'' x' f b x''' s h1 h2 h3) (fun h4 : False => @lem7105249 A s f b h1)). Qed.
Lemma lem7109210 {A : Type'} (x'' : A) (x' : A) (f : A -> real) (b : real) (x''' : A) (s : A -> Prop) (h1 : term812 A s f b) (h2 : term606 A x'' x' s f x''' b) (h3 : term774 A x''' s) : False.
Proof. exact (EQ_MP (@lem7109209 A x'' x' f b x''' s h1 h2 h3) (@lem7105249 A s f b h1)). Qed.
Lemma lem7109211 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : (x''' = x') = False.
Proof. exact (prop_ext (fun h5 : x''' = x' => @lem7109202 A x x'' s f b x''' x' h1 h2 h3 h4) (fun h5 : False => @lem7105130 A x''' x' h4)). Qed.
Lemma lem7109212 {A : Type'} (x : type710 A) (x'' : A) (s : A -> Prop) (f : A -> real) (b : real) (x''' : A) (x' : A) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : x''' = x') : False.
Proof. exact (EQ_MP (@lem7109211 A x x'' s f b x''' x' h1 h2 h3 h4) (@lem7105130 A x''' x' h4)). Qed.
Lemma lem7109213 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7109204 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7105003 A s f b h3)). Qed.
Lemma lem7109214 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109213 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7105003 A s f b h3)). Qed.
Lemma lem7109215 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : (term820 A s f b) = False.
Proof. exact (prop_ext (fun h5 : term820 A s f b => @lem7109206 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h5 : False => @lem7104889 A s f b h3)). Qed.
Lemma lem7109216 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (EQ_MP (@lem7109215 A x x'' x' s f x''' b h1 h2 h3 h4) (@lem7104889 A s f b h3)). Qed.
Lemma lem7109217 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term812 A s f b) (h2 : term695 A x) (h3 : term181) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (or_elim (@lem7104527 A x'' x' s f x''' b h4) (fun h0 : x''' = x' => @lem7109212 A x x'' s f b x''' x' h2 h3 h4 h0) (fun h0 : term774 A x''' s => @lem7109210 A x'' x' f b x''' s h1 h4 h0)). Qed.
Lemma lem7109218 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term820 A s f b) (h4 : term606 A x'' x' s f x''' b) : False.
Proof. exact (or_elim (@lem7104527 A x'' x' s f x''' b h4) (fun h0 : x''' = x' => @lem7109216 A x x'' x' s f x''' b h1 h2 h3 h4) (fun h0 : term774 A x''' s => @lem7109214 A x x'' x' s f x''' b h1 h2 h3 h4)). Qed.
Lemma lem7109219 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (x''' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) (h4 : term822 A s f b) : False.
Proof. exact (or_elim (@lem7104533 A s f b h4) (fun h0 : term820 A s f b => @lem7109218 A x x'' x' s f x''' b h1 h2 h0 h3) (fun h0 : term812 A s f b => @lem7109217 A x x'' x' s f x''' b h0 h1 h2 h3)). Qed.
Lemma lem7109220 {A : Type'} (x' : A) (x''' : A) (b : real) (s : A -> Prop) (f : A -> real) (x'' : A) (h1 : term606 A x'' x' s f x''' b) (h2 : term827 A s f x'') : False.
Proof. exact (or_elim (@lem7104527 A x'' x' s f x''' b h1) (fun h0 : x''' = x' => @lem7109190 A x' x''' b s f x'' h1 h2) (fun h0 : term774 A x''' s => @lem7106988 A x' x''' b s f x'' h1 h2)). Qed.
Lemma lem7109221 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (x''' : A) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term606 A x'' x' s f x''' b) : False.
Proof. exact (or_elim (@lem7104529 A x'' x' s f x''' b h3) (fun h0 : term827 A s f x'' => @lem7109220 A x' x''' b s f x'' h3 h0) (fun h0 : term822 A s f b => @lem7109219 A x x'' x' x''' s f b h1 h2 h3 h0)). Qed.
Lemma lem7109222 {A : Type'} (x : type710 A) (x'' : A) (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term609 A x'' x' s f b) : False.
Proof. exact (ex_elim (@lem7103837 A x'' x' s f b h3) (fun x''' : A => fun h0 : term608 A x'' x' s f b x''' => @lem7109221 A x x'' x' s f x''' b h1 h2 h0)). Qed.
Lemma lem7109223 {A : Type'} (x : type710 A) (x' : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term611 A x' s f b) : False.
Proof. exact (ex_elim (@lem7103836 A x' s f b h3) (fun x'' : A => fun h0 : term610 A x' s f b x'' => @lem7109222 A x x'' x' s f b h1 h2 h0)). Qed.
Lemma lem7109224 {A : Type'} (x : type710 A) (x' : A) (f : A -> real) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term613 A x' f b) : False.
Proof. exact (ex_elim (@lem7103835 A x' f b h3) (fun s : A -> Prop => fun h0 : term612 A x' f b s => @lem7109223 A x x' s f b h1 h2 h0)). Qed.
Lemma lem7109225 {A : Type'} (x : type710 A) (f : A -> real) (b : real) (h1 : term695 A x) (h2 : term181) (h3 : term412 A f b) : False.
Proof. exact (ex_elim (@lem7103515 A f b h3) (fun x' : A => fun h0 : term614 A f b x' => @lem7109224 A x x' f b h1 h2 h0)). Qed.
Lemma lem7109226 {A : Type'} (f : A -> real) (b : real) (h1 : term178 A) (h2 : term181) (h3 : term412 A f b) : False.
Proof. exact (ex_elim (@lem7103833 A h1) (fun x : type710 A => fun h0 : term697 A x => @lem7109225 A x f b h0 h2 h3)). Qed.
Lemma lem7109227 {A : Type'} (f : A -> real) (b : real) (h1 : term181) (h2 : term412 A f b) : term417 A.
Proof. exact (fun h0 : term178 A => @lem7109226 A f b h0 h1 h2). Qed.
Lemma lem7109228 {A : Type'} : (term417 A) = (term418 A).
Proof. exact (@lem69 (term178 A)). Qed.
Lemma lem7109229 {A : Type'} (f : A -> real) (b : real) (h1 : term181) (h2 : term412 A f b) : term418 A.
Proof. exact (EQ_MP (@lem7109228 A) (@lem7109227 A f b h1 h2)). Qed.
Lemma lem7109230 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term421 A.
Proof. exact (fun h0 : term181 => @lem7109229 A f b h0 h1). Qed.
Lemma lem7109231 {A : Type'} (f : A -> real) (b : real) : term423 A f b.
Proof. exact (fun h0 : term412 A f b => @lem7109230 A f b h0). Qed.
Lemma lem7109236 {A : Type'} (b : real) : term427 A b.
Proof. exact (fun f : A -> real => @lem7109231 A f b). Qed.
Lemma lem7109241 {A : Type'} : term431 A.
Proof. exact (fun b : real => @lem7109236 A b). Qed.
Lemma lem7109242 {A : Type'} : term430 A.
Proof. exact (EQ_MP (@lem7102991 A) (@lem7109241 A)). Qed.
Lemma lem7109243 {A : Type'} (b : real) : term967 A b.
Proof. exact (@lem7109242 A b). Qed.
Lemma lem7109244 {A : Type'} (b : real) : (term967 A b) = (term426 A b).
Proof. exact (eq_refl (term967 A b)). Qed.
Lemma lem7109245 {A : Type'} (b : real) : term426 A b.
Proof. exact (EQ_MP (@lem7109244 A b) (@lem7109243 A b)). Qed.
Lemma lem7109246 {A : Type'} (b : real) (f : A -> real) : term968 A b f.
Proof. exact (@lem7109245 A b f). Qed.
Lemma lem7109247 {A : Type'} (f : A -> real) (b : real) : (term968 A b f) = (term413 A f b).
Proof. exact (eq_refl (term968 A b f)). Qed.
Lemma lem7109248 {A : Type'} (f : A -> real) (b : real) : term413 A f b.
Proof. exact (EQ_MP (@lem7109247 A f b) (@lem7109246 A b f)). Qed.
Lemma lem7109250 {A : Type'} (f : A -> real) (b : real) : term413 A f b.
Proof. exact (@lem7102601 A f b (@lem7109248 A f b)). Qed.
Lemma lem7109251 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term420 A.
Proof. exact (@lem7109250 A f b (@lem7102583 A f b h1)). Qed.
Lemma lem7109252 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : term417 A.
Proof. exact (@lem7109251 A f b h1 (@lem7087523)). Qed.
Lemma lem7109253 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : False.
Proof. exact (@lem7109252 A f b h1 (@lem7102584 A)). Qed.
Lemma lem7109254 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : (term412 A f b) = False.
Proof. exact (prop_ext (fun h2 : term412 A f b => @lem7109253 A f b h1) (fun h2 : False => @lem7102583 A f b h1)). Qed.
Lemma lem7109255 {A : Type'} (f : A -> real) (b : real) (h1 : term412 A f b) : False.
Proof. exact (EQ_MP (@lem7109254 A f b h1) (@lem7102583 A f b h1)). Qed.
Lemma lem7109256 {A : Type'} (f : A -> real) (b : real) : term411 A f b.
Proof. exact (fun h0 : term412 A f b => @lem7109255 A f b h0). Qed.
Lemma lem7109257 {A : Type'} (f : A -> real) (b : real) : term408 A f b.
Proof. exact (EQ_MP (@lem7102582 A f b) (@lem7109256 A f b)). Qed.
Lemma lem7109258 {A : Type'} (f : A -> real) (b : real) : term253 A f b.
Proof. exact (EQ_MP (@lem7102578 A f b) (@lem7109257 A f b)). Qed.
Lemma lem7109259 {A : Type'} (f : A -> real) (b : real) : term225 A f b.
Proof. exact (@lem7087648 A f b (@lem7109258 A f b)). Qed.
Lemma lem7109260 {A : Type'} (f : A -> real) (b : real) : term224 A f b.
Proof. exact (EQ_MP (@lem7087615 A f b) (@lem7109259 A f b)). Qed.
Lemma lem7109265 {A : Type'} (f : A -> real) : term969 A f.
Proof. exact (fun b : real => @lem7109260 A f b). Qed.
Lemma lem7109270 {A : Type'} : term970 A.
Proof. exact (fun f : A -> real => @lem7109265 A f). Qed.

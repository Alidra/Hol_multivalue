Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_LE_SQRT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_LE_SQRT_POS_spec.
Require Import REAL_ABS_NEG_spec.
Require Import REAL_ABS_SUB_spec.
Require Import REAL_LE_POW_2_spec.
Require Import REAL_LE_RSQRT_spec.
Require Import REAL_SQRT_POW_2_spec.
Require Import REAL_WLOG_LE_spec.
Require Import SQRT_LE_0_spec.
Require Import SQRT_MONO_LE_EQ_spec.
Require Import SQRT_NEG_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1339577_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367767_spec.
Require Import thm1367769_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482702_spec.
Require Import thm1482703_spec.
Require Import thm1482704_spec.
Require Import thm1482706_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483454_spec.
Require Import thm1483460_spec.
Require Import thm1483464_spec.
Require Import thm1483472_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483498_spec.
Require Import thm1483506_spec.
Require Import thm1483507_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm706949_spec.
Require Import thm707207_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Require Import thm912803_spec.
Require Import thm913187_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Require Import thm996664_spec.
Lemma lem1969850 (x : real) : term0 x.
Proof. exact (@lem1365032 x). Qed.
Lemma lem1969851 (x : real) : (term0 x) = ((term1 x) = (real_abs x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1969853 (x : real) : term2 x.
Proof. exact (@lem1921835 x). Qed.
Lemma lem1969854 (x : real) : (term2 x) = ((term3 x) = (term4 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1969856 (x : real) : term5 x.
Proof. exact (@lem1968391 x). Qed.
Lemma lem1969857 (x : real) : (term5 x) = ((term6 x) = (real_abs x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1969868 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (@lem1483554 (term9 x y) (term10 x y)). Qed.
Lemma lem1969904 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (@lem1483519 (term12 x y) (term13 x y)). Qed.
Lemma lem1969905 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (@lem1483476 term16 term17 (real_mul x y)). Qed.
Lemma lem1969907 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1969908 : term20 = term21.
Proof. exact (@lem1969907 term22 term23). Qed.
Lemma lem1969909 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1969910 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1969911 : term26 = term23.
Proof. exact (EQ_MP (@lem1969910) (@lem1969909)). Qed.
Lemma lem1969912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969913 : term27 = term17.
Proof. exact (MK_COMB (@lem1969912) (@lem1969911)). Qed.
Lemma lem1969914 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1969915 : term21 = term28.
Proof. exact (MK_COMB (@lem1969914) (@lem1969913)). Qed.
Lemma lem1969916 : term20 = term28.
Proof. exact (TRANS (@lem1969908) (@lem1969915)). Qed.
Lemma lem1969917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969918 : term29 = term30.
Proof. exact (MK_COMB (@lem1969917) (@lem1969916)). Qed.
Lemma lem1969919 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1969920 (x : real) (y : real) : (term15 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1969918) (@lem1969919 x y)). Qed.
Lemma lem1969921 (x : real) (y : real) : (term14 x y) = (term31 x y).
Proof. exact (TRANS (@lem1969905 x y) (@lem1969920 x y)). Qed.
Lemma lem1969922 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1969923 (x : real) (y : real) : (term11 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1969922 x y) (@lem1969921 x y)). Qed.
Lemma lem1969924 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483482 (term35 x) (term35 y) (term31 x y)). Qed.
Lemma lem1969925 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem1483488 (term31 x y) (term35 y)). Qed.
Lemma lem1969926 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1969927 (x : real) (y : real) : (term34 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1969926 x) (@lem1969925 x y)). Qed.
Lemma lem1969928 (x : real) (y : real) : (term33 x y) = (term39 x y).
Proof. exact (TRANS (@lem1969924 x y) (@lem1969927 x y)). Qed.
Lemma lem1969929 (x : real) (y : real) : (term11 x y) = (term39 x y).
Proof. exact (TRANS (@lem1969923 x y) (@lem1969928 x y)). Qed.
Lemma lem1969931 (x : real) (y : real) : (term10 x y) = (term39 x y).
Proof. exact (TRANS (@lem1969904 x y) (@lem1969929 x y)). Qed.
Lemma lem1969944 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1969945 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1969946 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1969945) (@lem1969944 x y)). Qed.
Lemma lem1969947 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1969948 (x : real) (y : real) : (term9 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1969946 x y) (@lem1969947)). Qed.
Lemma lem1969949 : term44 = term25.
Proof. exact (@lem912741). Qed.
Lemma lem1969950 : (term44 = term25) = (term45 = term23).
Proof. exact (@lem1005477 (BIT1 0) term25). Qed.
Lemma lem1969951 : term45 = term23.
Proof. exact (EQ_MP (@lem1969950) (@lem1969949)). Qed.
Lemma lem1969952 : term23 = term45.
Proof. exact (SYM (@lem1969951)). Qed.
Lemma lem1969953 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem1483507 (term40 x y) term22). Qed.
Lemma lem1969954 (x : real) (y : real) : (term48 x y) = (term40 x y).
Proof. exact (@lem1483506 (term40 x y)). Qed.
Lemma lem1969955 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1969956 (x : real) (y : real) : (term47 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1969955 x y) (@lem1969954 x y)). Qed.
Lemma lem1969957 (x : real) (y : real) : (term46 x y) = (term50 x y).
Proof. exact (TRANS (@lem1969953 x y) (@lem1969956 x y)). Qed.
Lemma lem1969958 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1969959 (x : real) (y : real) : (term43 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1969958 x y) (@lem1969952)). Qed.
Lemma lem1969960 (x : real) (y : real) : (term43 x y) = (term50 x y).
Proof. exact (TRANS (@lem1969959 x y) (@lem1969957 x y)). Qed.
Lemma lem1969961 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (@lem1483454 x (term52 y) (term40 x y)). Qed.
Lemma lem1969962 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem1483508 x x (term52 y)). Qed.
Lemma lem1969967 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem1483478 term16 x y). Qed.
Lemma lem1969968 (x : real) : (real_mul x x) = (term35 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1969969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1969970 (x : real) : (term57 x) = (term38 x).
Proof. exact (MK_COMB (@lem1969969) (@lem1969968 x)). Qed.
Lemma lem1969971 (x : real) (y : real) : (term54 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1969970 x) (@lem1969967 x y)). Qed.
Lemma lem1969972 (x : real) (y : real) : (term53 x y) = (term58 x y).
Proof. exact (TRANS (@lem1969962 x y) (@lem1969971 x y)). Qed.
Lemma lem1969973 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1969974 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1969973) (@lem1969972 x y)). Qed.
Lemma lem1969975 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (@lem1483508 x (term52 y) (term52 y)). Qed.
Lemma lem1969976 (y : real) : (term63 y) = (term64 y).
Proof. exact (@lem1483464 term16 term16 y y). Qed.
Lemma lem1969978 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1969979 : term67 = term68.
Proof. exact (@lem1969978 term22 term22). Qed.
Lemma lem1969980 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1969981 : term70 = term22.
Proof. exact (EQ_MP (@lem1969980) (@lem940073)). Qed.
Lemma lem1969982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969983 : term68 = term71.
Proof. exact (MK_COMB (@lem1969982) (@lem1969981)). Qed.
Lemma lem1969984 : term67 = term71.
Proof. exact (TRANS (@lem1969979) (@lem1969983)). Qed.
Lemma lem1969985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969986 : term72 = term73.
Proof. exact (MK_COMB (@lem1969985) (@lem1969984)). Qed.
Lemma lem1969987 (y : real) : (real_mul y y) = (real_mul y y).
Proof. exact (eq_refl (real_mul y y)). Qed.
Lemma lem1969988 (y : real) : (term64 y) = (term74 y).
Proof. exact (MK_COMB (@lem1969986) (@lem1969987 y)). Qed.
Lemma lem1969989 (y : real) : (term63 y) = (term74 y).
Proof. exact (TRANS (@lem1969976 y) (@lem1969988 y)). Qed.
Lemma lem1969990 (y : real) : (real_mul y y) = (term35 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1969991 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1969992 (y : real) : (term74 y) = (term75 y).
Proof. exact (MK_COMB (@lem1969991) (@lem1969990 y)). Qed.
Lemma lem1969993 (y : real) : (term63 y) = (term75 y).
Proof. exact (TRANS (@lem1969989 y) (@lem1969992 y)). Qed.
Lemma lem1969994 (y : real) : (term75 y) = (term35 y).
Proof. exact (@lem1483436 (term35 y)). Qed.
Lemma lem1969995 (y : real) : (term63 y) = (term35 y).
Proof. exact (TRANS (@lem1969993 y) (@lem1969994 y)). Qed.
Lemma lem1969996 (y : real) (x : real) : (term76 y x) = (term56 y x).
Proof. exact (@lem1483472 term16 y x). Qed.
Lemma lem1969997 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1969998 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1969999 (x : real) (y : real) : (term56 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1969998) (@lem1969997 x y)). Qed.
Lemma lem1970000 (x : real) (y : real) : (term76 y x) = (term56 x y).
Proof. exact (TRANS (@lem1969996 y x) (@lem1969999 x y)). Qed.
Lemma lem1970001 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970002 (x : real) (y : real) : (term78 y x) = (term79 x y).
Proof. exact (MK_COMB (@lem1970001) (@lem1970000 x y)). Qed.
Lemma lem1970003 (x : real) (y : real) : (term62 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1970002 x y) (@lem1969995 y)). Qed.
Lemma lem1970004 (x : real) (y : real) : (term61 x y) = (term80 x y).
Proof. exact (TRANS (@lem1969975 x y) (@lem1970003 x y)). Qed.
Lemma lem1970005 (x : real) (y : real) : (term51 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1969974 x y) (@lem1970004 x y)). Qed.
Lemma lem1970006 (x : real) (y : real) : (term50 x y) = (term81 x y).
Proof. exact (TRANS (@lem1969961 x y) (@lem1970005 x y)). Qed.
Lemma lem1970007 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (@lem1483482 (term35 x) (term56 x y) (term80 x y)). Qed.
Lemma lem1970008 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (@lem1483490 (term56 x y) (term56 x y) (term35 y)). Qed.
Lemma lem1970009 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem1483438 term16 term16 (real_mul x y)). Qed.
Lemma lem1970010 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1970011 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1970012 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1970013 : term90 = term23.
Proof. exact (EQ_MP (@lem1970012) (@lem1970011)). Qed.
Lemma lem1970014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970015 : term91 = term17.
Proof. exact (MK_COMB (@lem1970014) (@lem1970013)). Qed.
Lemma lem1970016 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970017 : term88 = term28.
Proof. exact (MK_COMB (@lem1970016) (@lem1970015)). Qed.
Lemma lem1970018 : term87 = term28.
Proof. exact (TRANS (@lem1970010) (@lem1970017)). Qed.
Lemma lem1970019 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970020 : term92 = term30.
Proof. exact (MK_COMB (@lem1970019) (@lem1970018)). Qed.
Lemma lem1970021 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1970022 (x : real) (y : real) : (term86 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1970020) (@lem1970021 x y)). Qed.
Lemma lem1970023 (x : real) (y : real) : (term85 x y) = (term31 x y).
Proof. exact (TRANS (@lem1970009 x y) (@lem1970022 x y)). Qed.
Lemma lem1970024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970025 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1970024) (@lem1970023 x y)). Qed.
Lemma lem1970026 (y : real) : (term35 y) = (term35 y).
Proof. exact (eq_refl (term35 y)). Qed.
Lemma lem1970027 (x : real) (y : real) : (term84 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1970025 x y) (@lem1970026 y)). Qed.
Lemma lem1970028 (x : real) (y : real) : (term83 x y) = (term37 x y).
Proof. exact (TRANS (@lem1970008 x y) (@lem1970027 x y)). Qed.
Lemma lem1970029 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1970030 (x : real) (y : real) : (term82 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1970029 x) (@lem1970028 x y)). Qed.
Lemma lem1970031 (x : real) (y : real) : (term81 x y) = (term39 x y).
Proof. exact (TRANS (@lem1970007 x y) (@lem1970030 x y)). Qed.
Lemma lem1970032 (x : real) (y : real) : (term50 x y) = (term39 x y).
Proof. exact (TRANS (@lem1970006 x y) (@lem1970031 x y)). Qed.
Lemma lem1970033 (x : real) (y : real) : (term43 x y) = (term39 x y).
Proof. exact (TRANS (@lem1969960 x y) (@lem1970032 x y)). Qed.
Lemma lem1970034 (x : real) (y : real) : (term9 x y) = (term39 x y).
Proof. exact (TRANS (@lem1969948 x y) (@lem1970033 x y)). Qed.
Lemma lem1970035 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1970036 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1970035) (@lem1970034 x y)). Qed.
Lemma lem1970037 (x : real) (y : real) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1970036 x y) (@lem1969931 x y)). Qed.
Lemma lem1970038 (x : real) (y : real) : (term98 x y) = (term99 x y).
Proof. exact (@lem1483519 (term39 x y) (term39 x y)). Qed.
Lemma lem1970039 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (@lem1483508 (term35 x) term16 (term37 x y)). Qed.
Lemma lem1970040 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (@lem1483508 (term31 x y) term16 (term35 y)). Qed.
Lemma lem1970041 (y : real) : (term104 y) = (term104 y).
Proof. exact (eq_refl (term104 y)). Qed.
Lemma lem1970042 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (@lem1483476 term16 term28 (real_mul x y)). Qed.
Lemma lem1970044 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970045 : term107 = term27.
Proof. exact (@lem1970044 term22 term23). Qed.
Lemma lem1970046 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1970047 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1970048 : term26 = term23.
Proof. exact (EQ_MP (@lem1970047) (@lem1970046)). Qed.
Lemma lem1970049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970050 : term27 = term17.
Proof. exact (MK_COMB (@lem1970049) (@lem1970048)). Qed.
Lemma lem1970051 : term107 = term17.
Proof. exact (TRANS (@lem1970045) (@lem1970050)). Qed.
Lemma lem1970052 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970053 : term108 = term109.
Proof. exact (MK_COMB (@lem1970052) (@lem1970051)). Qed.
Lemma lem1970054 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1970055 (x : real) (y : real) : (term106 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1970053) (@lem1970054 x y)). Qed.
Lemma lem1970056 (x : real) (y : real) : (term105 x y) = (term13 x y).
Proof. exact (TRANS (@lem1970042 x y) (@lem1970055 x y)). Qed.
Lemma lem1970057 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970058 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1970057) (@lem1970056 x y)). Qed.
Lemma lem1970059 (x : real) (y : real) : (term103 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1970058 x y) (@lem1970041 y)). Qed.
Lemma lem1970060 (x : real) (y : real) : (term102 x y) = (term112 x y).
Proof. exact (TRANS (@lem1970040 x y) (@lem1970059 x y)). Qed.
Lemma lem1970063 (x : real) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1970064 (x : real) (y : real) : (term101 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1970063 x) (@lem1970060 x y)). Qed.
Lemma lem1970065 (x : real) (y : real) : (term100 x y) = (term114 x y).
Proof. exact (TRANS (@lem1970039 x y) (@lem1970064 x y)). Qed.
Lemma lem1970066 (x : real) (y : real) : (term115 x y) = (term115 x y).
Proof. exact (eq_refl (term115 x y)). Qed.
Lemma lem1970067 (x : real) (y : real) : (term99 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1970066 x y) (@lem1970065 x y)). Qed.
Lemma lem1970068 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (@lem1483480 (term35 x) (term104 x) (term37 x y) (term112 x y)). Qed.
Lemma lem1970069 (x : real) : (term118 x) = (term119 x).
Proof. exact (@lem1483442 term16 (term35 x)). Qed.
Lemma lem1970071 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970072 : term122 = term121.
Proof. exact (@lem1970071 term22). Qed.
Lemma lem1970073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970074 : term123 = term124.
Proof. exact (MK_COMB (@lem1970073) (@lem1970072)). Qed.
Lemma lem1970075 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1970076 (x : real) : (term119 x) = (term125 x).
Proof. exact (MK_COMB (@lem1970074) (@lem1970075 x)). Qed.
Lemma lem1970077 (x : real) : (term118 x) = (term125 x).
Proof. exact (TRANS (@lem1970069 x) (@lem1970076 x)). Qed.
Lemma lem1970078 (x : real) : (term125 x) = term121.
Proof. exact (@lem1483446 (term35 x)). Qed.
Lemma lem1970079 (x : real) : (term118 x) = term121.
Proof. exact (TRANS (@lem1970077 x) (@lem1970078 x)). Qed.
Lemma lem1970080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970081 (x : real) : (term126 x) = term127.
Proof. exact (MK_COMB (@lem1970080) (@lem1970079 x)). Qed.
Lemma lem1970082 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (@lem1483480 (term31 x y) (term13 x y) (term35 y) (term104 y)). Qed.
Lemma lem1970083 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (@lem1483438 term28 term17 (real_mul x y)). Qed.
Lemma lem1970085 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970086 : term132 = term121.
Proof. exact (@lem1970085 term23). Qed.
Lemma lem1970087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970088 : term133 = term124.
Proof. exact (MK_COMB (@lem1970087) (@lem1970086)). Qed.
Lemma lem1970089 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1970090 (x : real) (y : real) : (term131 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1970088) (@lem1970089 x y)). Qed.
Lemma lem1970091 (x : real) (y : real) : (term130 x y) = (term134 x y).
Proof. exact (TRANS (@lem1970083 x y) (@lem1970090 x y)). Qed.
Lemma lem1970092 (x : real) (y : real) : (term134 x y) = term121.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1970093 (x : real) (y : real) : (term130 x y) = term121.
Proof. exact (TRANS (@lem1970091 x y) (@lem1970092 x y)). Qed.
Lemma lem1970094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970095 (x : real) (y : real) : (term135 x y) = term127.
Proof. exact (MK_COMB (@lem1970094) (@lem1970093 x y)). Qed.
Lemma lem1970096 (y : real) : (term118 y) = (term119 y).
Proof. exact (@lem1483442 term16 (term35 y)). Qed.
Lemma lem1970098 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970099 : term122 = term121.
Proof. exact (@lem1970098 term22). Qed.
Lemma lem1970100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970101 : term123 = term124.
Proof. exact (MK_COMB (@lem1970100) (@lem1970099)). Qed.
Lemma lem1970102 (y : real) : (term35 y) = (term35 y).
Proof. exact (eq_refl (term35 y)). Qed.
Lemma lem1970103 (y : real) : (term119 y) = (term125 y).
Proof. exact (MK_COMB (@lem1970101) (@lem1970102 y)). Qed.
Lemma lem1970104 (y : real) : (term118 y) = (term125 y).
Proof. exact (TRANS (@lem1970096 y) (@lem1970103 y)). Qed.
Lemma lem1970105 (y : real) : (term125 y) = term121.
Proof. exact (@lem1483446 (term35 y)). Qed.
Lemma lem1970106 (y : real) : (term118 y) = term121.
Proof. exact (TRANS (@lem1970104 y) (@lem1970105 y)). Qed.
Lemma lem1970107 (x : real) (y : real) : (term129 x y) = term136.
Proof. exact (MK_COMB (@lem1970095 x y) (@lem1970106 y)). Qed.
Lemma lem1970108 (x : real) (y : real) : (term128 x y) = term136.
Proof. exact (TRANS (@lem1970082 x y) (@lem1970107 x y)). Qed.
Lemma lem1970109 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1970110 (x : real) (y : real) : (term128 x y) = term121.
Proof. exact (TRANS (@lem1970108 x y) (@lem1970109)). Qed.
Lemma lem1970111 (x : real) (y : real) : (term117 x y) = term136.
Proof. exact (MK_COMB (@lem1970081 x) (@lem1970110 x y)). Qed.
Lemma lem1970112 (x : real) (y : real) : (term116 x y) = term136.
Proof. exact (TRANS (@lem1970068 x y) (@lem1970111 x y)). Qed.
Lemma lem1970113 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1970114 (x : real) (y : real) : (term116 x y) = term121.
Proof. exact (TRANS (@lem1970112 x y) (@lem1970113)). Qed.
Lemma lem1970115 (x : real) (y : real) : (term99 x y) = term121.
Proof. exact (TRANS (@lem1970067 x y) (@lem1970114 x y)). Qed.
Lemma lem1970116 (x : real) (y : real) : (term98 x y) = term121.
Proof. exact (TRANS (@lem1970038 x y) (@lem1970115 x y)). Qed.
Lemma lem1970117 (x : real) (y : real) : (term97 x y) = term121.
Proof. exact (TRANS (@lem1970037 x y) (@lem1970116 x y)). Qed.
Lemma lem1970118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970119 (x : real) (y : real) : (term137 x y) = term138.
Proof. exact (MK_COMB (@lem1970118) (@lem1970117 x y)). Qed.
Lemma lem1970120 : term138 = term139.
Proof. exact (@lem1483512 term121). Qed.
Lemma lem1970122 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970123 : term139 = term121.
Proof. exact (@lem1970122 term22). Qed.
Lemma lem1970124 : term138 = term121.
Proof. exact (TRANS (@lem1970120) (@lem1970123)). Qed.
Lemma lem1970125 (x : real) (y : real) : (term141 x y) = (term141 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1970126 (x : real) (y : real) : ((term137 x y) = term138) = ((term137 x y) = term121).
Proof. exact (MK_COMB (@lem1970125 x y) (@lem1970124)). Qed.
Lemma lem1970127 (x : real) (y : real) : (term137 x y) = term121.
Proof. exact (EQ_MP (@lem1970126 x y) (@lem1970119 x y)). Qed.
Lemma lem1970128 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970129 (x : real) (y : real) : (term142 x y) = term143.
Proof. exact (MK_COMB (@lem1970128) (@lem1970127 x y)). Qed.
Lemma lem1970130 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970131 (x : real) (y : real) : (term144 x y) = term145.
Proof. exact (MK_COMB (@lem1970129 x y) (@lem1970130)). Qed.
Lemma lem1970132 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970133 (x : real) (y : real) : (term146 x y) = term143.
Proof. exact (MK_COMB (@lem1970132) (@lem1970117 x y)). Qed.
Lemma lem1970134 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970135 (x : real) (y : real) : (term147 x y) = term145.
Proof. exact (MK_COMB (@lem1970133 x y) (@lem1970134)). Qed.
Lemma lem1970136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1970137 (x : real) (y : real) : (term148 x y) = term149.
Proof. exact (MK_COMB (@lem1970136) (@lem1970135 x y)). Qed.
Lemma lem1970138 (x : real) (y : real) : (term8 x y) = term150.
Proof. exact (MK_COMB (@lem1970137 x y) (@lem1970131 x y)). Qed.
Lemma lem1970152 (x : real) (y : real) : (term7 x y) = term150.
Proof. exact (TRANS (@lem1969868 x y) (@lem1970138 x y)). Qed.
Lemma lem1970162 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1970163 (h1 : term145) : term145.
Proof. exact (h1). Qed.
Lemma lem1970165 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1970166 : term145 = term152.
Proof. exact (@lem1970165 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1970167 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1970168 : term145 = False.
Proof. exact (TRANS (@lem1970166) (@lem1970167)). Qed.
Lemma lem1970169 (h1 : term145) : False.
Proof. exact (EQ_MP (@lem1970168) (@lem1970163 h1)). Qed.
Lemma lem1970170 (h1 : term145) : term145.
Proof. exact (h1). Qed.
Lemma lem1970172 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1970173 : term145 = term152.
Proof. exact (@lem1970172 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1970174 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1970175 : term145 = False.
Proof. exact (TRANS (@lem1970173) (@lem1970174)). Qed.
Lemma lem1970176 (h1 : term145) : False.
Proof. exact (EQ_MP (@lem1970175) (@lem1970170 h1)). Qed.
Lemma lem1970177 (h1 : term150) : False.
Proof. exact (or_elim (@lem1970162 h1) (fun h0 : term145 => @lem1970169 h0) (fun h0 : term145 => @lem1970176 h0)). Qed.
Lemma lem1970179 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1970180 (h1 : term150) : term150 = False.
Proof. exact (prop_ext (fun h2 : term150 => @lem1970177 h1) (fun h2 : False => @lem1970179 h1)). Qed.
Lemma lem1970181 (h1 : term150) : False.
Proof. exact (EQ_MP (@lem1970180 h1) (@lem1970179 h1)). Qed.
Lemma lem1970182 (x : real) (y : real) (h1 : term7 x y) : term7 x y.
Proof. exact (h1). Qed.
Lemma lem1970183 (x : real) (y : real) (h1 : term7 x y) : term150.
Proof. exact (EQ_MP (@lem1970152 x y) (@lem1970182 x y h1)). Qed.
Lemma lem1970184 (x : real) (y : real) (h1 : term7 x y) : term150 = False.
Proof. exact (prop_ext (fun h2 : term150 => @lem1970181 h2) (fun h2 : False => @lem1970183 x y h1)). Qed.
Lemma lem1970185 (x : real) (y : real) (h1 : term7 x y) : False.
Proof. exact (EQ_MP (@lem1970184 x y h1) (@lem1970183 x y h1)). Qed.
Lemma lem1970186 (x : real) (y : real) : term153 x y.
Proof. exact (fun h0 : term7 x y => @lem1970185 x y h0). Qed.
Lemma lem1970187 (x : real) (y : real) : term154 x y.
Proof. exact (@lem1386578 ((term9 x y) = (term10 x y))). Qed.
Lemma lem1970189 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1646060 (term156 x y)). Qed.
Lemma lem1970190 (x : real) (y : real) : (term155 x y) = (term157 x y).
Proof. exact (eq_refl (term155 x y)). Qed.
Lemma lem1970191 (x : real) (y : real) : term157 x y.
Proof. exact (EQ_MP (@lem1970190 x y) (@lem1970189 x y)). Qed.
Lemma lem1970192 (h1 : term158) : term158.
Proof. exact (h1). Qed.
Lemma lem1970193 (x : real) (h1 : term158) : term159 x.
Proof. exact (@lem1970192 h1 x). Qed.
Lemma lem1970194 (x : real) : (term159 x) = (term160 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1970195 (x : real) (h1 : term158) : term160 x.
Proof. exact (EQ_MP (@lem1970194 x) (@lem1970193 x h1)). Qed.
Lemma lem1970196 (x : real) (y : real) (h1 : term158) : term161 x y.
Proof. exact (@lem1970195 x h1 y). Qed.
Lemma lem1970197 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1970198 (x : real) (y : real) (h1 : term158) : term162 x y.
Proof. exact (EQ_MP (@lem1970197 x y) (@lem1970196 x y h1)). Qed.
Lemma lem1970199 (x : real) (y : real) (h1 : term163 x y) : term163 x y.
Proof. exact (h1). Qed.
Lemma lem1970200 (x : real) (y : real) (h1 : term158) (h2 : term163 x y) : term164 x y.
Proof. exact (@lem1970198 x y h1 (@lem1970199 x y h2)). Qed.
Lemma lem1970201 (x : real) (y : real) (h1 : term163 x y) : term165 x y.
Proof. exact (fun h0 : term158 => @lem1970200 x y h0 h1). Qed.
Lemma lem1970202 (h1 : term158) : term158.
Proof. exact (h1). Qed.
Lemma lem1970203 (x : real) (y : real) (h1 : term158) (h2 : term163 x y) : term164 x y.
Proof. exact (@lem1970201 x y h2 (@lem1970202 h1)). Qed.
Lemma lem1970204 (x : real) (y : real) (h1 : term158) : term162 x y.
Proof. exact (fun h0 : term163 x y => @lem1970203 x y h1 h0). Qed.
Lemma lem1970205 (x : real) (h1 : term158) : term160 x.
Proof. exact (fun y : real => @lem1970204 x y h1). Qed.
Lemma lem1970206 (h1 : term158) : term158.
Proof. exact (fun x : real => @lem1970205 x h1). Qed.
Lemma lem1970207 : term166.
Proof. exact (fun h0 : term158 => @lem1970206 h0). Qed.
Lemma lem1970208 : term158.
Proof. exact (@lem1970207 (@lem1961031)). Qed.
Lemma lem1970209 (x : real) : term159 x.
Proof. exact (@lem1970208 x). Qed.
Lemma lem1970210 (x : real) : (term159 x) = (term160 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1970211 (x : real) : term160 x.
Proof. exact (EQ_MP (@lem1970210 x) (@lem1970209 x)). Qed.
Lemma lem1970212 (x : real) (y : real) : term161 x y.
Proof. exact (@lem1970211 x y). Qed.
Lemma lem1970213 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1970247 (y : real) (x : real) : (term167 y x) = (term168 y x).
Proof. exact (@lem17362 (term169 x y) ((term170 x y) = (real_sub y x))). Qed.
Lemma lem1970248 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483533 term121 x). Qed.
Lemma lem1970254 (x : real) : (term173 x) = (term174 x).
Proof. exact (@lem1483519 term121 x). Qed.
Lemma lem1970259 (x : real) : (term174 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1970261 (x : real) : (term173 x) = (term52 x).
Proof. exact (TRANS (@lem1970254 x) (@lem1970259 x)). Qed.
Lemma lem1970262 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970263 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1970262) (@lem1970261 x)). Qed.
Lemma lem1970264 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970265 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1970263 x) (@lem1970264)). Qed.
Lemma lem1970266 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1970248 x) (@lem1970265 x)). Qed.
Lemma lem1970267 (y : real) : (term178 y) = (term179 y).
Proof. exact (@lem1483523 y term121). Qed.
Lemma lem1970273 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483519 y term121). Qed.
Lemma lem1970275 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970276 : term139 = term121.
Proof. exact (@lem1970275 term22). Qed.
Lemma lem1970277 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1970278 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem1970277 y) (@lem1970276)). Qed.
Lemma lem1970279 (y : real) : (term182 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1970280 (y : real) : (term181 y) = y.
Proof. exact (TRANS (@lem1970278 y) (@lem1970279 y)). Qed.
Lemma lem1970282 (y : real) : (term180 y) = y.
Proof. exact (TRANS (@lem1970273 y) (@lem1970280 y)). Qed.
Lemma lem1970283 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1970284 (y : real) : (term183 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1970283) (@lem1970282 y)). Qed.
Lemma lem1970285 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970286 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1970284 y) (@lem1970285)). Qed.
Lemma lem1970287 (y : real) : (term178 y) = (term184 y).
Proof. exact (TRANS (@lem1970267 y) (@lem1970286 y)). Qed.
Lemma lem1970288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970289 (x : real) : (term185 x) = (term186 x).
Proof. exact (MK_COMB (@lem1970288) (@lem1970266 x)). Qed.
Lemma lem1970290 (x : real) (y : real) : (term169 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1970289 x) (@lem1970287 y)). Qed.
Lemma lem1970291 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (@lem1483554 (term170 x y) (real_sub y x)). Qed.
Lemma lem1970297 (y : real) (x : real) : (real_sub y x) = (term40 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1970302 (x : real) (y : real) : (term40 y x) = (term190 x y).
Proof. exact (@lem1483488 (term52 x) y). Qed.
Lemma lem1970304 (x : real) (y : real) : (real_sub y x) = (term190 x y).
Proof. exact (TRANS (@lem1970297 y x) (@lem1970302 x y)). Qed.
Lemma lem1970307 (x : real) (y : real) : (term191 x y) = (term191 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1970308 (x : real) (y : real) : (term192 y x) = (term193 x y).
Proof. exact (MK_COMB (@lem1970307 x y) (@lem1970304 x y)). Qed.
Lemma lem1970309 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (@lem1483519 (term170 x y) (term190 x y)). Qed.
Lemma lem1970310 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483508 (term52 x) term16 y). Qed.
Lemma lem1970311 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1970312 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1970314 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970315 : term67 = term68.
Proof. exact (@lem1970314 term22 term22). Qed.
Lemma lem1970316 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1970317 : term70 = term22.
Proof. exact (EQ_MP (@lem1970316) (@lem940073)). Qed.
Lemma lem1970318 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970319 : term68 = term71.
Proof. exact (MK_COMB (@lem1970318) (@lem1970317)). Qed.
Lemma lem1970320 : term67 = term71.
Proof. exact (TRANS (@lem1970315) (@lem1970319)). Qed.
Lemma lem1970321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970322 : term72 = term73.
Proof. exact (MK_COMB (@lem1970321) (@lem1970320)). Qed.
Lemma lem1970323 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1970324 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1970322) (@lem1970323 x)). Qed.
Lemma lem1970325 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1970312 x) (@lem1970324 x)). Qed.
Lemma lem1970326 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1970327 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1970325 x) (@lem1970326 x)). Qed.
Lemma lem1970328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970329 (x : real) : (term200 x) = (real_add x).
Proof. exact (MK_COMB (@lem1970328) (@lem1970327 x)). Qed.
Lemma lem1970330 (x : real) (y : real) : (term196 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1970329 x) (@lem1970311 y)). Qed.
Lemma lem1970331 (x : real) (y : real) : (term195 x y) = (term40 x y).
Proof. exact (TRANS (@lem1970310 x y) (@lem1970330 x y)). Qed.
Lemma lem1970332 (x : real) (y : real) : (term201 x y) = (term201 x y).
Proof. exact (eq_refl (term201 x y)). Qed.
Lemma lem1970333 (x : real) (y : real) : (term194 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem1970332 x y) (@lem1970331 x y)). Qed.
Lemma lem1970334 (x : real) (y : real) : (term202 x y) = (term203 x y).
Proof. exact (@lem1483484 x (term170 x y) (term52 y)). Qed.
Lemma lem1970335 (x : real) (y : real) : (term204 x y) = (term205 x y).
Proof. exact (@lem1483488 (term52 y) (term170 x y)). Qed.
Lemma lem1970336 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1970337 (x : real) (y : real) : (term203 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1970336 x) (@lem1970335 x y)). Qed.
Lemma lem1970338 (x : real) (y : real) : (term202 x y) = (term206 x y).
Proof. exact (TRANS (@lem1970334 x y) (@lem1970337 x y)). Qed.
Lemma lem1970339 (x : real) (y : real) : (term194 x y) = (term206 x y).
Proof. exact (TRANS (@lem1970333 x y) (@lem1970338 x y)). Qed.
Lemma lem1970340 (x : real) (y : real) : (term193 x y) = (term206 x y).
Proof. exact (TRANS (@lem1970309 x y) (@lem1970339 x y)). Qed.
Lemma lem1970341 (x : real) (y : real) : (term192 y x) = (term206 x y).
Proof. exact (TRANS (@lem1970308 x y) (@lem1970340 x y)). Qed.
Lemma lem1970342 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970343 (x : real) (y : real) : (term207 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1970342) (@lem1970341 x y)). Qed.
Lemma lem1970344 (x : real) (y : real) : (term208 x y) = (term209 x y).
Proof. exact (@lem1483512 (term206 x y)). Qed.
Lemma lem1970345 (x : real) (y : real) : (term209 x y) = (term210 x y).
Proof. exact (@lem1483508 x term16 (term205 x y)). Qed.
Lemma lem1970346 (x : real) (y : real) : (term211 x y) = (term212 x y).
Proof. exact (@lem1483508 (term52 y) term16 (term170 x y)). Qed.
Lemma lem1970347 (x : real) (y : real) : (term213 x y) = (term213 x y).
Proof. exact (eq_refl (term213 x y)). Qed.
Lemma lem1970348 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1970350 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970351 : term67 = term68.
Proof. exact (@lem1970350 term22 term22). Qed.
Lemma lem1970352 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1970353 : term70 = term22.
Proof. exact (EQ_MP (@lem1970352) (@lem940073)). Qed.
Lemma lem1970354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970355 : term68 = term71.
Proof. exact (MK_COMB (@lem1970354) (@lem1970353)). Qed.
Lemma lem1970356 : term67 = term71.
Proof. exact (TRANS (@lem1970351) (@lem1970355)). Qed.
Lemma lem1970357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970358 : term72 = term73.
Proof. exact (MK_COMB (@lem1970357) (@lem1970356)). Qed.
Lemma lem1970359 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970360 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1970358) (@lem1970359 y)). Qed.
Lemma lem1970361 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1970348 y) (@lem1970360 y)). Qed.
Lemma lem1970362 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1970363 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1970361 y) (@lem1970362 y)). Qed.
Lemma lem1970364 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970365 (y : real) : (term200 y) = (real_add y).
Proof. exact (MK_COMB (@lem1970364) (@lem1970363 y)). Qed.
Lemma lem1970366 (x : real) (y : real) : (term212 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1970365 y) (@lem1970347 x y)). Qed.
Lemma lem1970367 (x : real) (y : real) : (term211 x y) = (term214 x y).
Proof. exact (TRANS (@lem1970346 x y) (@lem1970366 x y)). Qed.
Lemma lem1970370 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970371 (x : real) (y : real) : (term210 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem1970370 x) (@lem1970367 x y)). Qed.
Lemma lem1970372 (x : real) (y : real) : (term209 x y) = (term216 x y).
Proof. exact (TRANS (@lem1970345 x y) (@lem1970371 x y)). Qed.
Lemma lem1970373 (x : real) (y : real) : (term208 x y) = (term216 x y).
Proof. exact (TRANS (@lem1970344 x y) (@lem1970372 x y)). Qed.
Lemma lem1970374 (y : real) (x : real) : (term217 y x) = (term217 y x).
Proof. exact (eq_refl (term217 y x)). Qed.
Lemma lem1970375 (x : real) (y : real) : ((term207 y x) = (term208 x y)) = ((term207 y x) = (term216 x y)).
Proof. exact (MK_COMB (@lem1970374 y x) (@lem1970373 x y)). Qed.
Lemma lem1970376 (x : real) (y : real) : (term207 y x) = (term216 x y).
Proof. exact (EQ_MP (@lem1970375 x y) (@lem1970343 x y)). Qed.
Lemma lem1970377 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970378 (x : real) (y : real) : (term218 y x) = (term219 x y).
Proof. exact (MK_COMB (@lem1970377) (@lem1970376 x y)). Qed.
Lemma lem1970379 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970380 (x : real) (y : real) : (term220 y x) = (term221 x y).
Proof. exact (MK_COMB (@lem1970378 x y) (@lem1970379)). Qed.
Lemma lem1970381 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970382 (x : real) (y : real) : (term222 y x) = (term223 x y).
Proof. exact (MK_COMB (@lem1970381) (@lem1970341 x y)). Qed.
Lemma lem1970383 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970384 (x : real) (y : real) : (term224 y x) = (term225 x y).
Proof. exact (MK_COMB (@lem1970382 x y) (@lem1970383)). Qed.
Lemma lem1970385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1970386 (x : real) (y : real) : (term226 y x) = (term227 x y).
Proof. exact (MK_COMB (@lem1970385) (@lem1970384 x y)). Qed.
Lemma lem1970387 (x : real) (y : real) : (term189 y x) = (term228 x y).
Proof. exact (MK_COMB (@lem1970386 x y) (@lem1970380 x y)). Qed.
Lemma lem1970388 (x : real) (y : real) : (term188 y x) = (term228 x y).
Proof. exact (TRANS (@lem1970291 y x) (@lem1970387 x y)). Qed.
Lemma lem1970389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970390 (x : real) (y : real) : (term229 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem1970389) (@lem1970290 x y)). Qed.
Lemma lem1970391 (x : real) (y : real) : (term168 y x) = (term231 x y).
Proof. exact (MK_COMB (@lem1970390 x y) (@lem1970388 x y)). Qed.
Lemma lem1970398 (x : real) (y : real) : (term167 y x) = (term231 x y).
Proof. exact (TRANS (@lem1970247 y x) (@lem1970391 x y)). Qed.
Lemma lem1970421 (x : real) (y : real) : (term231 x y) = (term232 x y).
Proof. exact (@lem19158 (term225 x y) (term187 x y) (term221 x y)). Qed.
Lemma lem1970422 (x : real) (y : real) : (term167 y x) = (term232 x y).
Proof. exact (TRANS (@lem1970398 x y) (@lem1970421 x y)). Qed.
Lemma lem1970424 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (eq_refl (term233 x y)). Qed.
Lemma lem1970425 (x : real) (y : real) : (term234 x y) = (term233 x y).
Proof. exact (SYM (@lem1970424 x y)). Qed.
Lemma lem1970426 (x : real) (y : real) : (term233 x y) = (term235 x y).
Proof. exact (@lem1482981 (term236 x y) (real_sub x y)). Qed.
Lemma lem1970427 (x : real) (y : real) : (term234 x y) = (term235 x y).
Proof. exact (TRANS (@lem1970425 x y) (@lem1970426 x y)). Qed.
Lemma lem1970428 (x : real) (y : real) : (term237 x y) = (term238 x y).
Proof. exact (eq_refl (term237 x y)). Qed.
Lemma lem1970429 (x : real) (y : real) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem1970430 (x : real) (y : real) : (term240 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1970429 x y) (@lem1970428 x y)). Qed.
Lemma lem1970431 (x : real) (y : real) : (term242 x y) = (term243 x y).
Proof. exact (eq_refl (term242 x y)). Qed.
Lemma lem1970432 (x : real) (y : real) : (term244 x y) = (term244 x y).
Proof. exact (eq_refl (term244 x y)). Qed.
Lemma lem1970433 (x : real) (y : real) : (term245 x y) = (term246 x y).
Proof. exact (MK_COMB (@lem1970432 x y) (@lem1970431 x y)). Qed.
Lemma lem1970434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1970435 (x : real) (y : real) : (term247 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem1970434) (@lem1970433 x y)). Qed.
Lemma lem1970436 (x : real) (y : real) : (term235 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1970435 x y) (@lem1970430 x y)). Qed.
Lemma lem1970437 (x : real) (y : real) : (term250 x y) = (term250 x y).
Proof. exact (eq_refl (term250 x y)). Qed.
Lemma lem1970438 (x : real) (y : real) : ((term234 x y) = (term235 x y)) = ((term234 x y) = (term249 x y)).
Proof. exact (MK_COMB (@lem1970437 x y) (@lem1970436 x y)). Qed.
Lemma lem1970439 (x : real) (y : real) : (term234 x y) = (term249 x y).
Proof. exact (EQ_MP (@lem1970438 x y) (@lem1970427 x y)). Qed.
Lemma lem1970440 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (@lem1483527 (real_sub x y) term121). Qed.
Lemma lem1970441 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970454 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970455 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1970456 (x : real) (y : real) : (term253 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1970455) (@lem1970454 x y)). Qed.
Lemma lem1970457 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1970456 x y) (@lem1970441)). Qed.
Lemma lem1970458 (x : real) (y : real) : (term256 x y) = (term257 x y).
Proof. exact (@lem1483519 (term40 x y) term121). Qed.
Lemma lem1970460 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970461 : term139 = term121.
Proof. exact (@lem1970460 term22). Qed.
Lemma lem1970462 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1970463 (x : real) (y : real) : (term257 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1970462 x y) (@lem1970461)). Qed.
Lemma lem1970464 (x : real) (y : real) : (term259 x y) = (term40 x y).
Proof. exact (@lem1483450 (term40 x y)). Qed.
Lemma lem1970465 (x : real) (y : real) : (term257 x y) = (term40 x y).
Proof. exact (TRANS (@lem1970463 x y) (@lem1970464 x y)). Qed.
Lemma lem1970466 (x : real) (y : real) : (term256 x y) = (term40 x y).
Proof. exact (TRANS (@lem1970458 x y) (@lem1970465 x y)). Qed.
Lemma lem1970467 (x : real) (y : real) : (term255 x y) = (term40 x y).
Proof. exact (TRANS (@lem1970457 x y) (@lem1970466 x y)). Qed.
Lemma lem1970468 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1970469 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1970468) (@lem1970467 x y)). Qed.
Lemma lem1970470 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970471 (x : real) (y : real) : (term252 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem1970469 x y) (@lem1970470)). Qed.
Lemma lem1970472 (x : real) (y : real) : (term251 x y) = (term262 x y).
Proof. exact (TRANS (@lem1970440 x y) (@lem1970471 x y)). Qed.
Lemma lem1970473 (x : real) : (term177 x) = (term263 x).
Proof. exact (@lem1483525 (term52 x) term121). Qed.
Lemma lem1970485 (x : real) : (term264 x) = (term265 x).
Proof. exact (@lem1483519 (term52 x) term121). Qed.
Lemma lem1970487 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970488 : term139 = term121.
Proof. exact (@lem1970487 term22). Qed.
Lemma lem1970489 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970490 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1970489 x) (@lem1970488)). Qed.
Lemma lem1970491 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1970492 (x : real) : (term265 x) = (term52 x).
Proof. exact (TRANS (@lem1970490 x) (@lem1970491 x)). Qed.
Lemma lem1970494 (x : real) : (term264 x) = (term52 x).
Proof. exact (TRANS (@lem1970485 x) (@lem1970492 x)). Qed.
Lemma lem1970495 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970496 (x : real) : (term267 x) = (term176 x).
Proof. exact (MK_COMB (@lem1970495) (@lem1970494 x)). Qed.
Lemma lem1970497 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970498 (x : real) : (term263 x) = (term177 x).
Proof. exact (MK_COMB (@lem1970496 x) (@lem1970497)). Qed.
Lemma lem1970499 (x : real) : (term177 x) = (term177 x).
Proof. exact (TRANS (@lem1970473 x) (@lem1970498 x)). Qed.
Lemma lem1970500 (y : real) : (term184 y) = (term179 y).
Proof. exact (@lem1483527 y term121). Qed.
Lemma lem1970506 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483519 y term121). Qed.
Lemma lem1970508 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970509 : term139 = term121.
Proof. exact (@lem1970508 term22). Qed.
Lemma lem1970510 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1970511 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem1970510 y) (@lem1970509)). Qed.
Lemma lem1970512 (y : real) : (term182 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1970513 (y : real) : (term181 y) = y.
Proof. exact (TRANS (@lem1970511 y) (@lem1970512 y)). Qed.
Lemma lem1970515 (y : real) : (term180 y) = y.
Proof. exact (TRANS (@lem1970506 y) (@lem1970513 y)). Qed.
Lemma lem1970516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1970517 (y : real) : (term183 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1970516) (@lem1970515 y)). Qed.
Lemma lem1970518 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970519 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1970517 y) (@lem1970518)). Qed.
Lemma lem1970520 (y : real) : (term184 y) = (term184 y).
Proof. exact (TRANS (@lem1970500 y) (@lem1970519 y)). Qed.
Lemma lem1970521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970522 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1970521) (@lem1970499 x)). Qed.
Lemma lem1970523 (x : real) (y : real) : (term187 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1970522 x) (@lem1970520 y)). Qed.
Lemma lem1970524 (x : real) (y : real) : (term268 x y) = (term269 x y).
Proof. exact (@lem1483525 (term270 x y) term121). Qed.
Lemma lem1970525 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970538 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970547 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1970548 (x : real) (y : real) : (term271 x y) = (term272 x y).
Proof. exact (MK_COMB (@lem1970547 y) (@lem1970538 x y)). Qed.
Lemma lem1970549 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483484 x (term52 y) (term52 y)). Qed.
Lemma lem1970550 (y : real) : (term274 y) = (term275 y).
Proof. exact (@lem1483438 term16 term16 y). Qed.
Lemma lem1970551 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1970552 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1970553 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1970554 : term90 = term23.
Proof. exact (EQ_MP (@lem1970553) (@lem1970552)). Qed.
Lemma lem1970555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970556 : term91 = term17.
Proof. exact (MK_COMB (@lem1970555) (@lem1970554)). Qed.
Lemma lem1970557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970558 : term88 = term28.
Proof. exact (MK_COMB (@lem1970557) (@lem1970556)). Qed.
Lemma lem1970559 : term87 = term28.
Proof. exact (TRANS (@lem1970551) (@lem1970558)). Qed.
Lemma lem1970560 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970561 : term92 = term30.
Proof. exact (MK_COMB (@lem1970560) (@lem1970559)). Qed.
Lemma lem1970562 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970563 (y : real) : (term275 y) = (term276 y).
Proof. exact (MK_COMB (@lem1970561) (@lem1970562 y)). Qed.
Lemma lem1970564 (y : real) : (term274 y) = (term276 y).
Proof. exact (TRANS (@lem1970550 y) (@lem1970563 y)). Qed.
Lemma lem1970565 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1970566 (x : real) (y : real) : (term273 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1970565 x) (@lem1970564 y)). Qed.
Lemma lem1970567 (x : real) (y : real) : (term272 x y) = (term277 x y).
Proof. exact (TRANS (@lem1970549 x y) (@lem1970566 x y)). Qed.
Lemma lem1970568 (x : real) (y : real) : (term271 x y) = (term277 x y).
Proof. exact (TRANS (@lem1970548 x y) (@lem1970567 x y)). Qed.
Lemma lem1970571 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1970572 (x : real) (y : real) : (term270 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1970571 x) (@lem1970568 x y)). Qed.
Lemma lem1970573 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (@lem1483490 x x (term276 y)). Qed.
Lemma lem1970574 (x : real) : (real_add x x) = (term280 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1970575 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1970576 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1970577 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1970578 : term90 = term23.
Proof. exact (EQ_MP (@lem1970577) (@lem1970576)). Qed.
Lemma lem1970579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970580 : term91 = term17.
Proof. exact (MK_COMB (@lem1970579) (@lem1970578)). Qed.
Lemma lem1970581 : term281 = term17.
Proof. exact (TRANS (@lem1970575) (@lem1970580)). Qed.
Lemma lem1970582 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970583 : term282 = term109.
Proof. exact (MK_COMB (@lem1970582) (@lem1970581)). Qed.
Lemma lem1970584 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1970585 (x : real) : (term280 x) = (term283 x).
Proof. exact (MK_COMB (@lem1970583) (@lem1970584 x)). Qed.
Lemma lem1970586 (x : real) : (real_add x x) = (term283 x).
Proof. exact (TRANS (@lem1970574 x) (@lem1970585 x)). Qed.
Lemma lem1970587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970588 (x : real) : (term284 x) = (term285 x).
Proof. exact (MK_COMB (@lem1970587) (@lem1970586 x)). Qed.
Lemma lem1970589 (y : real) : (term276 y) = (term276 y).
Proof. exact (eq_refl (term276 y)). Qed.
Lemma lem1970590 (x : real) (y : real) : (term279 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1970588 x) (@lem1970589 y)). Qed.
Lemma lem1970591 (x : real) (y : real) : (term278 x y) = (term286 x y).
Proof. exact (TRANS (@lem1970573 x y) (@lem1970590 x y)). Qed.
Lemma lem1970592 (x : real) (y : real) : (term270 x y) = (term286 x y).
Proof. exact (TRANS (@lem1970572 x y) (@lem1970591 x y)). Qed.
Lemma lem1970593 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1970594 (x : real) (y : real) : (term287 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem1970593) (@lem1970592 x y)). Qed.
Lemma lem1970595 (x : real) (y : real) : (term289 x y) = (term290 x y).
Proof. exact (MK_COMB (@lem1970594 x y) (@lem1970525)). Qed.
Lemma lem1970596 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (@lem1483519 (term286 x y) term121). Qed.
Lemma lem1970598 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970599 : term139 = term121.
Proof. exact (@lem1970598 term22). Qed.
Lemma lem1970600 (x : real) (y : real) : (term292 x y) = (term292 x y).
Proof. exact (eq_refl (term292 x y)). Qed.
Lemma lem1970601 (x : real) (y : real) : (term291 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1970600 x y) (@lem1970599)). Qed.
Lemma lem1970602 (x : real) (y : real) : (term293 x y) = (term286 x y).
Proof. exact (@lem1483450 (term286 x y)). Qed.
Lemma lem1970603 (x : real) (y : real) : (term291 x y) = (term286 x y).
Proof. exact (TRANS (@lem1970601 x y) (@lem1970602 x y)). Qed.
Lemma lem1970604 (x : real) (y : real) : (term290 x y) = (term286 x y).
Proof. exact (TRANS (@lem1970596 x y) (@lem1970603 x y)). Qed.
Lemma lem1970605 (x : real) (y : real) : (term289 x y) = (term286 x y).
Proof. exact (TRANS (@lem1970595 x y) (@lem1970604 x y)). Qed.
Lemma lem1970606 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970607 (x : real) (y : real) : (term294 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1970606) (@lem1970605 x y)). Qed.
Lemma lem1970608 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970609 (x : real) (y : real) : (term269 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1970607 x y) (@lem1970608)). Qed.
Lemma lem1970610 (x : real) (y : real) : (term268 x y) = (term296 x y).
Proof. exact (TRANS (@lem1970524 x y) (@lem1970609 x y)). Qed.
Lemma lem1970611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970612 (x : real) (y : real) : (term230 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem1970611) (@lem1970523 x y)). Qed.
Lemma lem1970613 (x : real) (y : real) : (term243 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem1970612 x y) (@lem1970610 x y)). Qed.
Lemma lem1970614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970615 (x : real) (y : real) : (term244 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem1970614) (@lem1970472 x y)). Qed.
Lemma lem1970616 (x : real) (y : real) : (term246 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem1970615 x y) (@lem1970613 x y)). Qed.
Lemma lem1970617 (x : real) (y : real) : (term300 x y) = (term301 x y).
Proof. exact (@lem1483525 term121 (real_sub x y)). Qed.
Lemma lem1970630 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970633 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1970634 (x : real) (y : real) : (term303 x y) = (term304 x y).
Proof. exact (MK_COMB (@lem1970633) (@lem1970630 x y)). Qed.
Lemma lem1970635 (x : real) (y : real) : (term304 x y) = (term305 x y).
Proof. exact (@lem1483519 term121 (term40 x y)). Qed.
Lemma lem1970636 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1970637 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1970639 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970640 : term67 = term68.
Proof. exact (@lem1970639 term22 term22). Qed.
Lemma lem1970641 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1970642 : term70 = term22.
Proof. exact (EQ_MP (@lem1970641) (@lem940073)). Qed.
Lemma lem1970643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970644 : term68 = term71.
Proof. exact (MK_COMB (@lem1970643) (@lem1970642)). Qed.
Lemma lem1970645 : term67 = term71.
Proof. exact (TRANS (@lem1970640) (@lem1970644)). Qed.
Lemma lem1970646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970647 : term72 = term73.
Proof. exact (MK_COMB (@lem1970646) (@lem1970645)). Qed.
Lemma lem1970648 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970649 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1970647) (@lem1970648 y)). Qed.
Lemma lem1970650 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1970637 y) (@lem1970649 y)). Qed.
Lemma lem1970651 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1970652 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1970650 y) (@lem1970651 y)). Qed.
Lemma lem1970655 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970656 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1970655 x) (@lem1970652 y)). Qed.
Lemma lem1970657 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970636 x y) (@lem1970656 x y)). Qed.
Lemma lem1970658 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1970659 (x : real) (y : real) : (term305 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1970658) (@lem1970657 x y)). Qed.
Lemma lem1970660 (x : real) (y : real) : (term308 x y) = (term190 x y).
Proof. exact (@lem1483448 (term190 x y)). Qed.
Lemma lem1970661 (x : real) (y : real) : (term305 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970659 x y) (@lem1970660 x y)). Qed.
Lemma lem1970662 (x : real) (y : real) : (term304 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970635 x y) (@lem1970661 x y)). Qed.
Lemma lem1970663 (x : real) (y : real) : (term303 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970634 x y) (@lem1970662 x y)). Qed.
Lemma lem1970664 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970665 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (MK_COMB (@lem1970664) (@lem1970663 x y)). Qed.
Lemma lem1970666 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970667 (x : real) (y : real) : (term301 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1970665 x y) (@lem1970666)). Qed.
Lemma lem1970668 (x : real) (y : real) : (term300 x y) = (term311 x y).
Proof. exact (TRANS (@lem1970617 x y) (@lem1970667 x y)). Qed.
Lemma lem1970669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970670 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1970669) (@lem1970499 x)). Qed.
Lemma lem1970671 (x : real) (y : real) : (term187 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1970670 x) (@lem1970520 y)). Qed.
Lemma lem1970672 (x : real) (y : real) : (term312 x y) = (term313 x y).
Proof. exact (@lem1483525 (term314 x y) term121). Qed.
Lemma lem1970673 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970686 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970687 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970688 (x : real) (y : real) : (term315 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1970687) (@lem1970686 x y)). Qed.
Lemma lem1970689 (x : real) (y : real) : (term316 x y) = (term306 x y).
Proof. exact (@lem1483512 (term40 x y)). Qed.
Lemma lem1970690 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1970691 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1970693 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970694 : term67 = term68.
Proof. exact (@lem1970693 term22 term22). Qed.
Lemma lem1970695 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1970696 : term70 = term22.
Proof. exact (EQ_MP (@lem1970695) (@lem940073)). Qed.
Lemma lem1970697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970698 : term68 = term71.
Proof. exact (MK_COMB (@lem1970697) (@lem1970696)). Qed.
Lemma lem1970699 : term67 = term71.
Proof. exact (TRANS (@lem1970694) (@lem1970698)). Qed.
Lemma lem1970700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970701 : term72 = term73.
Proof. exact (MK_COMB (@lem1970700) (@lem1970699)). Qed.
Lemma lem1970702 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970703 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1970701) (@lem1970702 y)). Qed.
Lemma lem1970704 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1970691 y) (@lem1970703 y)). Qed.
Lemma lem1970705 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1970706 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1970704 y) (@lem1970705 y)). Qed.
Lemma lem1970709 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970710 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1970709 x) (@lem1970706 y)). Qed.
Lemma lem1970711 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970690 x y) (@lem1970710 x y)). Qed.
Lemma lem1970712 (x : real) (y : real) : (term316 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970689 x y) (@lem1970711 x y)). Qed.
Lemma lem1970713 (x : real) (y : real) : (term315 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970688 x y) (@lem1970712 x y)). Qed.
Lemma lem1970722 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1970723 (x : real) (y : real) : (term317 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem1970722 y) (@lem1970713 x y)). Qed.
Lemma lem1970724 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483484 (term52 x) (term52 y) y). Qed.
Lemma lem1970725 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1970727 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970728 : term122 = term121.
Proof. exact (@lem1970727 term22). Qed.
Lemma lem1970729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970730 : term123 = term124.
Proof. exact (MK_COMB (@lem1970729) (@lem1970728)). Qed.
Lemma lem1970731 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970732 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1970730) (@lem1970731 y)). Qed.
Lemma lem1970733 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1970725 y) (@lem1970732 y)). Qed.
Lemma lem1970734 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1970735 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1970733 y) (@lem1970734 y)). Qed.
Lemma lem1970736 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970737 (y : real) (x : real) : (term319 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1970736 x) (@lem1970735 y)). Qed.
Lemma lem1970738 (y : real) (x : real) : (term318 x y) = (term266 x).
Proof. exact (TRANS (@lem1970724 x y) (@lem1970737 y x)). Qed.
Lemma lem1970739 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1970740 (y : real) (x : real) : (term318 x y) = (term52 x).
Proof. exact (TRANS (@lem1970738 y x) (@lem1970739 x)). Qed.
Lemma lem1970741 (y : real) (x : real) : (term317 x y) = (term52 x).
Proof. exact (TRANS (@lem1970723 x y) (@lem1970740 y x)). Qed.
Lemma lem1970744 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1970745 (y : real) (x : real) : (term314 x y) = (term323 x).
Proof. exact (MK_COMB (@lem1970744 x) (@lem1970741 y x)). Qed.
Lemma lem1970746 (x : real) : (term323 x) = (term321 x).
Proof. exact (@lem1483442 term16 x). Qed.
Lemma lem1970748 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970749 : term122 = term121.
Proof. exact (@lem1970748 term22). Qed.
Lemma lem1970750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970751 : term123 = term124.
Proof. exact (MK_COMB (@lem1970750) (@lem1970749)). Qed.
Lemma lem1970752 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1970753 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1970751) (@lem1970752 x)). Qed.
Lemma lem1970754 (x : real) : (term323 x) = (term322 x).
Proof. exact (TRANS (@lem1970746 x) (@lem1970753 x)). Qed.
Lemma lem1970755 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1970756 (x : real) : (term323 x) = term121.
Proof. exact (TRANS (@lem1970754 x) (@lem1970755 x)). Qed.
Lemma lem1970757 (x : real) (y : real) : (term314 x y) = term121.
Proof. exact (TRANS (@lem1970745 y x) (@lem1970756 x)). Qed.
Lemma lem1970758 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1970759 (x : real) (y : real) : (term324 x y) = term302.
Proof. exact (MK_COMB (@lem1970758) (@lem1970757 x y)). Qed.
Lemma lem1970760 (x : real) (y : real) : (term325 x y) = term326.
Proof. exact (MK_COMB (@lem1970759 x y) (@lem1970673)). Qed.
Lemma lem1970761 : term326 = term327.
Proof. exact (@lem1483519 term121 term121). Qed.
Lemma lem1970763 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1970764 : term139 = term121.
Proof. exact (@lem1970763 term22). Qed.
Lemma lem1970765 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1970766 : term327 = term136.
Proof. exact (MK_COMB (@lem1970765) (@lem1970764)). Qed.
Lemma lem1970767 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1970768 : term327 = term121.
Proof. exact (TRANS (@lem1970766) (@lem1970767)). Qed.
Lemma lem1970769 : term326 = term121.
Proof. exact (TRANS (@lem1970761) (@lem1970768)). Qed.
Lemma lem1970770 (x : real) (y : real) : (term325 x y) = term121.
Proof. exact (TRANS (@lem1970760 x y) (@lem1970769)). Qed.
Lemma lem1970771 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970772 (x : real) (y : real) : (term328 x y) = term143.
Proof. exact (MK_COMB (@lem1970771) (@lem1970770 x y)). Qed.
Lemma lem1970773 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970774 (x : real) (y : real) : (term313 x y) = term145.
Proof. exact (MK_COMB (@lem1970772 x y) (@lem1970773)). Qed.
Lemma lem1970775 (x : real) (y : real) : (term312 x y) = term145.
Proof. exact (TRANS (@lem1970672 x y) (@lem1970774 x y)). Qed.
Lemma lem1970776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970777 (x : real) (y : real) : (term230 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem1970776) (@lem1970671 x y)). Qed.
Lemma lem1970778 (x : real) (y : real) : (term238 x y) = (term329 x y).
Proof. exact (MK_COMB (@lem1970777 x y) (@lem1970775 x y)). Qed.
Lemma lem1970779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970780 (x : real) (y : real) : (term239 x y) = (term330 x y).
Proof. exact (MK_COMB (@lem1970779) (@lem1970668 x y)). Qed.
Lemma lem1970781 (x : real) (y : real) : (term241 x y) = (term331 x y).
Proof. exact (MK_COMB (@lem1970780 x y) (@lem1970778 x y)). Qed.
Lemma lem1970782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1970783 (x : real) (y : real) : (term248 x y) = (term332 x y).
Proof. exact (MK_COMB (@lem1970782) (@lem1970616 x y)). Qed.
Lemma lem1970784 (x : real) (y : real) : (term249 x y) = (term333 x y).
Proof. exact (MK_COMB (@lem1970783 x y) (@lem1970781 x y)). Qed.
Lemma lem1970796 (x : real) (y : real) : (term234 x y) = (term333 x y).
Proof. exact (TRANS (@lem1970439 x y) (@lem1970784 x y)). Qed.
Lemma lem1970798 (a : real) (b : real) (x : real) (r : real) : (term334 a b x r) = (term335 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1970799 (x : real) (y : real) : (term221 x y) = (term336 x y).
Proof. exact (@lem1970798 (term52 x) y (real_sub x y) term121). Qed.
Lemma lem1970812 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970815 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1970816 (x : real) (y : real) : (term337 x y) = (term338 x y).
Proof. exact (MK_COMB (@lem1970815) (@lem1970812 x y)). Qed.
Lemma lem1970817 (x : real) (y : real) : (term338 x y) = (term40 x y).
Proof. exact (@lem1483460 (term40 x y)). Qed.
Lemma lem1970818 (x : real) (y : real) : (term337 x y) = (term40 x y).
Proof. exact (TRANS (@lem1970816 x y) (@lem1970817 x y)). Qed.
Lemma lem1970821 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1970822 (x : real) (y : real) : (term339 x y) = (term340 x y).
Proof. exact (MK_COMB (@lem1970821 y) (@lem1970818 x y)). Qed.
Lemma lem1970823 (x : real) (y : real) : (term340 x y) = (term341 x y).
Proof. exact (@lem1483484 x y (term52 y)). Qed.
Lemma lem1970824 (y : real) : (term323 y) = (term321 y).
Proof. exact (@lem1483442 term16 y). Qed.
Lemma lem1970826 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970827 : term122 = term121.
Proof. exact (@lem1970826 term22). Qed.
Lemma lem1970828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970829 : term123 = term124.
Proof. exact (MK_COMB (@lem1970828) (@lem1970827)). Qed.
Lemma lem1970830 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970831 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1970829) (@lem1970830 y)). Qed.
Lemma lem1970832 (y : real) : (term323 y) = (term322 y).
Proof. exact (TRANS (@lem1970824 y) (@lem1970831 y)). Qed.
Lemma lem1970833 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1970834 (y : real) : (term323 y) = term121.
Proof. exact (TRANS (@lem1970832 y) (@lem1970833 y)). Qed.
Lemma lem1970835 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1970836 (y : real) (x : real) : (term341 x y) = (term182 x).
Proof. exact (MK_COMB (@lem1970835 x) (@lem1970834 y)). Qed.
Lemma lem1970837 (y : real) (x : real) : (term340 x y) = (term182 x).
Proof. exact (TRANS (@lem1970823 x y) (@lem1970836 y x)). Qed.
Lemma lem1970838 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1970839 (y : real) (x : real) : (term340 x y) = x.
Proof. exact (TRANS (@lem1970837 y x) (@lem1970838 x)). Qed.
Lemma lem1970840 (y : real) (x : real) : (term339 x y) = x.
Proof. exact (TRANS (@lem1970822 x y) (@lem1970839 y x)). Qed.
Lemma lem1970849 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970850 (y : real) (x : real) : (term342 x y) = (term320 x).
Proof. exact (MK_COMB (@lem1970849 x) (@lem1970840 y x)). Qed.
Lemma lem1970851 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1970853 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1970854 : term122 = term121.
Proof. exact (@lem1970853 term22). Qed.
Lemma lem1970855 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970856 : term123 = term124.
Proof. exact (MK_COMB (@lem1970855) (@lem1970854)). Qed.
Lemma lem1970857 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1970858 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1970856) (@lem1970857 x)). Qed.
Lemma lem1970859 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1970851 x) (@lem1970858 x)). Qed.
Lemma lem1970860 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1970861 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1970859 x) (@lem1970860 x)). Qed.
Lemma lem1970862 (x : real) (y : real) : (term342 x y) = term121.
Proof. exact (TRANS (@lem1970850 y x) (@lem1970861 x)). Qed.
Lemma lem1970863 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970864 (x : real) (y : real) : (term343 x y) = term143.
Proof. exact (MK_COMB (@lem1970863) (@lem1970862 x y)). Qed.
Lemma lem1970865 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970866 (x : real) (y : real) : (term344 x y) = term145.
Proof. exact (MK_COMB (@lem1970864 x y) (@lem1970865)). Qed.
Lemma lem1970879 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1970882 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1970883 (x : real) (y : real) : (term345 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem1970882) (@lem1970879 x y)). Qed.
Lemma lem1970884 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1970885 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1970887 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1970888 : term67 = term68.
Proof. exact (@lem1970887 term22 term22). Qed.
Lemma lem1970889 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1970890 : term70 = term22.
Proof. exact (EQ_MP (@lem1970889) (@lem940073)). Qed.
Lemma lem1970891 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970892 : term68 = term71.
Proof. exact (MK_COMB (@lem1970891) (@lem1970890)). Qed.
Lemma lem1970893 : term67 = term71.
Proof. exact (TRANS (@lem1970888) (@lem1970892)). Qed.
Lemma lem1970894 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970895 : term72 = term73.
Proof. exact (MK_COMB (@lem1970894) (@lem1970893)). Qed.
Lemma lem1970896 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970897 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1970895) (@lem1970896 y)). Qed.
Lemma lem1970898 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1970885 y) (@lem1970897 y)). Qed.
Lemma lem1970899 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1970900 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1970898 y) (@lem1970899 y)). Qed.
Lemma lem1970903 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970904 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1970903 x) (@lem1970900 y)). Qed.
Lemma lem1970905 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970884 x y) (@lem1970904 x y)). Qed.
Lemma lem1970906 (x : real) (y : real) : (term345 x y) = (term190 x y).
Proof. exact (TRANS (@lem1970883 x y) (@lem1970905 x y)). Qed.
Lemma lem1970909 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1970910 (x : real) (y : real) : (term346 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem1970909 y) (@lem1970906 x y)). Qed.
Lemma lem1970911 (x : real) (y : real) : (term347 x y) = (term348 x y).
Proof. exact (@lem1483484 (term52 x) y y). Qed.
Lemma lem1970912 (y : real) : (real_add y y) = (term280 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1970913 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1970914 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1970915 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1970916 : term90 = term23.
Proof. exact (EQ_MP (@lem1970915) (@lem1970914)). Qed.
Lemma lem1970917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970918 : term91 = term17.
Proof. exact (MK_COMB (@lem1970917) (@lem1970916)). Qed.
Lemma lem1970919 : term281 = term17.
Proof. exact (TRANS (@lem1970913) (@lem1970918)). Qed.
Lemma lem1970920 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970921 : term282 = term109.
Proof. exact (MK_COMB (@lem1970920) (@lem1970919)). Qed.
Lemma lem1970922 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1970923 (y : real) : (term280 y) = (term283 y).
Proof. exact (MK_COMB (@lem1970921) (@lem1970922 y)). Qed.
Lemma lem1970924 (y : real) : (real_add y y) = (term283 y).
Proof. exact (TRANS (@lem1970912 y) (@lem1970923 y)). Qed.
Lemma lem1970925 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970926 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem1970925 x) (@lem1970924 y)). Qed.
Lemma lem1970927 (x : real) (y : real) : (term347 x y) = (term349 x y).
Proof. exact (TRANS (@lem1970911 x y) (@lem1970926 x y)). Qed.
Lemma lem1970928 (x : real) (y : real) : (term346 x y) = (term349 x y).
Proof. exact (TRANS (@lem1970910 x y) (@lem1970927 x y)). Qed.
Lemma lem1970937 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1970938 (x : real) (y : real) : (term350 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1970937 x) (@lem1970928 x y)). Qed.
Lemma lem1970939 (x : real) (y : real) : (term351 x y) = (term352 x y).
Proof. exact (@lem1483490 (term52 x) (term52 x) (term283 y)). Qed.
Lemma lem1970940 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1483438 term16 term16 x). Qed.
Lemma lem1970941 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1970942 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1970943 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1970944 : term90 = term23.
Proof. exact (EQ_MP (@lem1970943) (@lem1970942)). Qed.
Lemma lem1970945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1970946 : term91 = term17.
Proof. exact (MK_COMB (@lem1970945) (@lem1970944)). Qed.
Lemma lem1970947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1970948 : term88 = term28.
Proof. exact (MK_COMB (@lem1970947) (@lem1970946)). Qed.
Lemma lem1970949 : term87 = term28.
Proof. exact (TRANS (@lem1970941) (@lem1970948)). Qed.
Lemma lem1970950 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1970951 : term92 = term30.
Proof. exact (MK_COMB (@lem1970950) (@lem1970949)). Qed.
Lemma lem1970952 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1970953 (x : real) : (term275 x) = (term276 x).
Proof. exact (MK_COMB (@lem1970951) (@lem1970952 x)). Qed.
Lemma lem1970954 (x : real) : (term274 x) = (term276 x).
Proof. exact (TRANS (@lem1970940 x) (@lem1970953 x)). Qed.
Lemma lem1970955 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1970956 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem1970955) (@lem1970954 x)). Qed.
Lemma lem1970957 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1970958 (x : real) (y : real) : (term352 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1970956 x) (@lem1970957 y)). Qed.
Lemma lem1970959 (x : real) (y : real) : (term351 x y) = (term355 x y).
Proof. exact (TRANS (@lem1970939 x y) (@lem1970958 x y)). Qed.
Lemma lem1970960 (x : real) (y : real) : (term350 x y) = (term355 x y).
Proof. exact (TRANS (@lem1970938 x y) (@lem1970959 x y)). Qed.
Lemma lem1970961 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1970962 (x : real) (y : real) : (term356 x y) = (term357 x y).
Proof. exact (MK_COMB (@lem1970961) (@lem1970960 x y)). Qed.
Lemma lem1970963 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1970964 (x : real) (y : real) : (term358 x y) = (term359 x y).
Proof. exact (MK_COMB (@lem1970962 x y) (@lem1970963)). Qed.
Lemma lem1970965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1970966 (x : real) (y : real) : (term360 x y) = (term361 x y).
Proof. exact (MK_COMB (@lem1970965) (@lem1970964 x y)). Qed.
Lemma lem1970967 (x : real) (y : real) : (term336 x y) = (term362 x y).
Proof. exact (MK_COMB (@lem1970966 x y) (@lem1970866 x y)). Qed.
Lemma lem1970968 (x : real) (y : real) : (term221 x y) = (term362 x y).
Proof. exact (TRANS (@lem1970799 x y) (@lem1970967 x y)). Qed.
Lemma lem1970969 (x : real) (y : real) : (term230 x y) = (term230 x y).
Proof. exact (eq_refl (term230 x y)). Qed.
Lemma lem1970972 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem1970969 x y) (@lem1970968 x y)). Qed.
Lemma lem1970973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1970974 (x : real) (y : real) : (term365 x y) = (term366 x y).
Proof. exact (MK_COMB (@lem1970973) (@lem1970796 x y)). Qed.
Lemma lem1970975 (x : real) (y : real) : (term232 x y) = (term367 x y).
Proof. exact (MK_COMB (@lem1970974 x y) (@lem1970972 x y)). Qed.
Lemma lem1970976 (x : real) (y : real) (h1 : term367 x y) : term367 x y.
Proof. exact (h1). Qed.
Lemma lem1970977 (x : real) (y : real) (h1 : term333 x y) : term333 x y.
Proof. exact (h1). Qed.
Lemma lem1970978 (x : real) (y : real) (h1 : term299 x y) : term299 x y.
Proof. exact (h1). Qed.
Lemma lem1970979 (x : real) (y : real) (h1 : term299 x y) : term297 x y.
Proof. exact (proj2 (@lem1970978 x y h1)). Qed.
Lemma lem1970980 (x : real) (y : real) (h1 : term299 x y) : term262 x y.
Proof. exact (proj1 (@lem1970978 x y h1)). Qed.
Lemma lem1970982 (x : real) (y : real) (h1 : term299 x y) : term187 x y.
Proof. exact (proj1 (@lem1970979 x y h1)). Qed.
Lemma lem1970983 (x : real) (y : real) (h1 : term299 x y) : term184 y.
Proof. exact (proj2 (@lem1970982 x y h1)). Qed.
Lemma lem1970984 (x : real) (y : real) (h1 : term299 x y) : term177 x.
Proof. exact (proj1 (@lem1970982 x y h1)). Qed.
Lemma lem1970986 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1970987 : term368 = term369.
Proof. exact (@lem1970986 (NUMERAL 0) term22). Qed.
Lemma lem1970988 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1970989 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1970990 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1970989 h1) (fun h1 : term369 = True => @lem1970988)). Qed.
Lemma lem1970991 : term369 = True.
Proof. exact (EQ_MP (@lem1970990) (@lem1970988)). Qed.
Lemma lem1970992 : term368 = True.
Proof. exact (TRANS (@lem1970987) (@lem1970991)). Qed.
Lemma lem1970993 : True = term368.
Proof. exact (SYM (@lem1970992)). Qed.
Lemma lem1970994 : term368.
Proof. exact (EQ_MP (@lem1970993) (@lem0)). Qed.
Lemma lem1970995 (x : real) (y : real) (h1 : term299 x y) : term371 y.
Proof. exact (conj (@lem1970994) (@lem1970983 x y h1)). Qed.
Lemma lem1970997 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1970998 (y : real) : term373 y.
Proof. exact (@lem1970997 term71 y). Qed.
Lemma lem1970999 (x : real) (y : real) (h1 : term299 x y) : term374 y.
Proof. exact (@lem1970998 y (@lem1970995 x y h1)). Qed.
Lemma lem1971000 (y : real) : (term199 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1971001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1971002 (y : real) : (term375 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1971001) (@lem1971000 y)). Qed.
Lemma lem1971003 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971004 (y : real) : (term374 y) = (term184 y).
Proof. exact (MK_COMB (@lem1971002 y) (@lem1971003)). Qed.
Lemma lem1971005 (x : real) (y : real) (h1 : term299 x y) : term184 y.
Proof. exact (EQ_MP (@lem1971004 y) (@lem1970999 x y h1)). Qed.
Lemma lem1971007 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971008 : term368 = term369.
Proof. exact (@lem1971007 (NUMERAL 0) term22). Qed.
Lemma lem1971009 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1971010 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1971011 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1971010 h1) (fun h1 : term369 = True => @lem1971009)). Qed.
Lemma lem1971012 : term369 = True.
Proof. exact (EQ_MP (@lem1971011) (@lem1971009)). Qed.
Lemma lem1971013 : term368 = True.
Proof. exact (TRANS (@lem1971008) (@lem1971012)). Qed.
Lemma lem1971014 : True = term368.
Proof. exact (SYM (@lem1971013)). Qed.
Lemma lem1971015 : term368.
Proof. exact (EQ_MP (@lem1971014) (@lem0)). Qed.
Lemma lem1971016 (x : real) (y : real) (h1 : term299 x y) : term376 x y.
Proof. exact (conj (@lem1971015) (@lem1970980 x y h1)). Qed.
Lemma lem1971018 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1971019 (x : real) (y : real) : term377 x y.
Proof. exact (@lem1971018 term71 (term40 x y)). Qed.
Lemma lem1971020 (x : real) (y : real) (h1 : term299 x y) : term378 x y.
Proof. exact (@lem1971019 x y (@lem1971016 x y h1)). Qed.
Lemma lem1971021 (x : real) (y : real) : (term338 x y) = (term40 x y).
Proof. exact (@lem1483460 (term40 x y)). Qed.
Lemma lem1971022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1971023 (x : real) (y : real) : (term379 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1971022) (@lem1971021 x y)). Qed.
Lemma lem1971024 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971025 (x : real) (y : real) : (term378 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem1971023 x y) (@lem1971024)). Qed.
Lemma lem1971026 (x : real) (y : real) (h1 : term299 x y) : term262 x y.
Proof. exact (EQ_MP (@lem1971025 x y) (@lem1971020 x y h1)). Qed.
Lemma lem1971028 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971029 : term368 = term369.
Proof. exact (@lem1971028 (NUMERAL 0) term22). Qed.
Lemma lem1971030 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1971031 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1971032 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1971031 h1) (fun h1 : term369 = True => @lem1971030)). Qed.
Lemma lem1971033 : term369 = True.
Proof. exact (EQ_MP (@lem1971032) (@lem1971030)). Qed.
Lemma lem1971034 : term368 = True.
Proof. exact (TRANS (@lem1971029) (@lem1971033)). Qed.
Lemma lem1971035 : True = term368.
Proof. exact (SYM (@lem1971034)). Qed.
Lemma lem1971036 : term368.
Proof. exact (EQ_MP (@lem1971035) (@lem0)). Qed.
Lemma lem1971037 (x : real) (y : real) (h1 : term299 x y) : term380 x.
Proof. exact (conj (@lem1971036) (@lem1970984 x y h1)). Qed.
Lemma lem1971039 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1971040 (x : real) : term382 x.
Proof. exact (@lem1971039 term71 (term52 x)). Qed.
Lemma lem1971041 (x : real) (y : real) (h1 : term299 x y) : term383 x.
Proof. exact (@lem1971040 x (@lem1971037 x y h1)). Qed.
Lemma lem1971042 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1971043 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971044 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1971043) (@lem1971042 x)). Qed.
Lemma lem1971045 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971046 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1971044 x) (@lem1971045)). Qed.
Lemma lem1971047 (x : real) (y : real) (h1 : term299 x y) : term177 x.
Proof. exact (EQ_MP (@lem1971046 x) (@lem1971041 x y h1)). Qed.
Lemma lem1971048 (x : real) (y : real) (h1 : term299 x y) : term386 x y.
Proof. exact (conj (@lem1971047 x y h1) (@lem1971026 x y h1)). Qed.
Lemma lem1971050 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1971051 (x : real) (y : real) : term388 x y.
Proof. exact (@lem1971050 (term52 x) (term40 x y)). Qed.
Lemma lem1971052 (x : real) (y : real) (h1 : term299 x y) : term389 x y.
Proof. exact (@lem1971051 x y (@lem1971048 x y h1)). Qed.
Lemma lem1971053 (x : real) (y : real) : (term390 x y) = (term391 x y).
Proof. exact (@lem1483490 (term52 x) x (term52 y)). Qed.
Lemma lem1971054 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1971056 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971057 : term122 = term121.
Proof. exact (@lem1971056 term22). Qed.
Lemma lem1971058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971059 : term123 = term124.
Proof. exact (MK_COMB (@lem1971058) (@lem1971057)). Qed.
Lemma lem1971060 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971061 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1971059) (@lem1971060 x)). Qed.
Lemma lem1971062 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1971054 x) (@lem1971061 x)). Qed.
Lemma lem1971063 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1971064 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1971062 x) (@lem1971063 x)). Qed.
Lemma lem1971065 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1971066 (x : real) : (term392 x) = term127.
Proof. exact (MK_COMB (@lem1971065) (@lem1971064 x)). Qed.
Lemma lem1971067 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1971068 (x : real) (y : real) : (term391 x y) = (term174 y).
Proof. exact (MK_COMB (@lem1971066 x) (@lem1971067 y)). Qed.
Lemma lem1971069 (x : real) (y : real) : (term390 x y) = (term174 y).
Proof. exact (TRANS (@lem1971053 x y) (@lem1971068 x y)). Qed.
Lemma lem1971070 (y : real) : (term174 y) = (term52 y).
Proof. exact (@lem1483448 (term52 y)). Qed.
Lemma lem1971071 (x : real) (y : real) : (term390 x y) = (term52 y).
Proof. exact (TRANS (@lem1971069 x y) (@lem1971070 y)). Qed.
Lemma lem1971072 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971073 (x : real) (y : real) : (term393 x y) = (term176 y).
Proof. exact (MK_COMB (@lem1971072) (@lem1971071 x y)). Qed.
Lemma lem1971074 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971075 (x : real) (y : real) : (term389 x y) = (term177 y).
Proof. exact (MK_COMB (@lem1971073 x y) (@lem1971074)). Qed.
Lemma lem1971076 (x : real) (y : real) (h1 : term299 x y) : term177 y.
Proof. exact (EQ_MP (@lem1971075 x y) (@lem1971052 x y h1)). Qed.
Lemma lem1971078 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971079 : term368 = term369.
Proof. exact (@lem1971078 (NUMERAL 0) term22). Qed.
Lemma lem1971080 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1971081 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1971082 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1971081 h1) (fun h1 : term369 = True => @lem1971080)). Qed.
Lemma lem1971083 : term369 = True.
Proof. exact (EQ_MP (@lem1971082) (@lem1971080)). Qed.
Lemma lem1971084 : term368 = True.
Proof. exact (TRANS (@lem1971079) (@lem1971083)). Qed.
Lemma lem1971085 : True = term368.
Proof. exact (SYM (@lem1971084)). Qed.
Lemma lem1971086 : term368.
Proof. exact (EQ_MP (@lem1971085) (@lem0)). Qed.
Lemma lem1971087 (x : real) (y : real) (h1 : term299 x y) : term380 y.
Proof. exact (conj (@lem1971086) (@lem1971076 x y h1)). Qed.
Lemma lem1971089 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1971090 (y : real) : term382 y.
Proof. exact (@lem1971089 term71 (term52 y)). Qed.
Lemma lem1971091 (x : real) (y : real) (h1 : term299 x y) : term383 y.
Proof. exact (@lem1971090 y (@lem1971087 x y h1)). Qed.
Lemma lem1971092 (y : real) : (term384 y) = (term52 y).
Proof. exact (@lem1483460 (term52 y)). Qed.
Lemma lem1971093 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971094 (y : real) : (term385 y) = (term176 y).
Proof. exact (MK_COMB (@lem1971093) (@lem1971092 y)). Qed.
Lemma lem1971095 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971096 (y : real) : (term383 y) = (term177 y).
Proof. exact (MK_COMB (@lem1971094 y) (@lem1971095)). Qed.
Lemma lem1971097 (x : real) (y : real) (h1 : term299 x y) : term177 y.
Proof. exact (EQ_MP (@lem1971096 y) (@lem1971091 x y h1)). Qed.
Lemma lem1971098 (x : real) (y : real) (h1 : term299 x y) : term394 y.
Proof. exact (conj (@lem1971097 x y h1) (@lem1971005 x y h1)). Qed.
Lemma lem1971100 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1971101 (y : real) : term395 y.
Proof. exact (@lem1971100 (term52 y) y). Qed.
Lemma lem1971102 (x : real) (y : real) (h1 : term299 x y) : term396 y.
Proof. exact (@lem1971101 y (@lem1971098 x y h1)). Qed.
Lemma lem1971103 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1971105 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971106 : term122 = term121.
Proof. exact (@lem1971105 term22). Qed.
Lemma lem1971107 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971108 : term123 = term124.
Proof. exact (MK_COMB (@lem1971107) (@lem1971106)). Qed.
Lemma lem1971109 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971110 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1971108) (@lem1971109 y)). Qed.
Lemma lem1971111 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1971103 y) (@lem1971110 y)). Qed.
Lemma lem1971112 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1971113 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1971111 y) (@lem1971112 y)). Qed.
Lemma lem1971114 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971115 (y : real) : (term397 y) = term143.
Proof. exact (MK_COMB (@lem1971114) (@lem1971113 y)). Qed.
Lemma lem1971116 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971117 (y : real) : (term396 y) = term145.
Proof. exact (MK_COMB (@lem1971115 y) (@lem1971116)). Qed.
Lemma lem1971118 (x : real) (y : real) (h1 : term299 x y) : term145.
Proof. exact (EQ_MP (@lem1971117 y) (@lem1971102 x y h1)). Qed.
Lemma lem1971120 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971121 : term145 = term152.
Proof. exact (@lem1971120 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1971122 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1971123 : term145 = False.
Proof. exact (TRANS (@lem1971121) (@lem1971122)). Qed.
Lemma lem1971124 (x : real) (y : real) (h1 : term299 x y) : False.
Proof. exact (EQ_MP (@lem1971123) (@lem1971118 x y h1)). Qed.
Lemma lem1971125 (x : real) (y : real) (h1 : term331 x y) : term331 x y.
Proof. exact (h1). Qed.
Lemma lem1971126 (x : real) (y : real) (h1 : term331 x y) : term329 x y.
Proof. exact (proj2 (@lem1971125 x y h1)). Qed.
Lemma lem1971128 (x : real) (y : real) (h1 : term331 x y) : term145.
Proof. exact (proj2 (@lem1971126 x y h1)). Qed.
Lemma lem1971133 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971134 : term145 = term152.
Proof. exact (@lem1971133 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1971135 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1971136 : term145 = False.
Proof. exact (TRANS (@lem1971134) (@lem1971135)). Qed.
Lemma lem1971137 (x : real) (y : real) (h1 : term331 x y) : False.
Proof. exact (EQ_MP (@lem1971136) (@lem1971128 x y h1)). Qed.
Lemma lem1971138 (x : real) (y : real) (h1 : term333 x y) : False.
Proof. exact (or_elim (@lem1970977 x y h1) (fun h0 : term299 x y => @lem1971124 x y h0) (fun h0 : term331 x y => @lem1971137 x y h0)). Qed.
Lemma lem1971139 (x : real) (y : real) (h1 : term364 x y) : term364 x y.
Proof. exact (h1). Qed.
Lemma lem1971140 (x : real) (y : real) (h1 : term364 x y) : term362 x y.
Proof. exact (proj2 (@lem1971139 x y h1)). Qed.
Lemma lem1971144 (x : real) (y : real) (h1 : term364 x y) : term145.
Proof. exact (proj2 (@lem1971140 x y h1)). Qed.
Lemma lem1971147 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971148 : term145 = term152.
Proof. exact (@lem1971147 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1971149 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1971150 : term145 = False.
Proof. exact (TRANS (@lem1971148) (@lem1971149)). Qed.
Lemma lem1971151 (x : real) (y : real) (h1 : term364 x y) : False.
Proof. exact (EQ_MP (@lem1971150) (@lem1971144 x y h1)). Qed.
Lemma lem1971152 (x : real) (y : real) (h1 : term367 x y) : False.
Proof. exact (or_elim (@lem1970976 x y h1) (fun h0 : term333 x y => @lem1971138 x y h0) (fun h0 : term364 x y => @lem1971151 x y h0)). Qed.
Lemma lem1971153 (x : real) (y : real) (h1 : term232 x y) : term232 x y.
Proof. exact (h1). Qed.
Lemma lem1971154 (x : real) (y : real) (h1 : term232 x y) : term367 x y.
Proof. exact (EQ_MP (@lem1970975 x y) (@lem1971153 x y h1)). Qed.
Lemma lem1971155 (x : real) (y : real) (h1 : term232 x y) : (term367 x y) = False.
Proof. exact (prop_ext (fun h2 : term367 x y => @lem1971152 x y h2) (fun h2 : False => @lem1971154 x y h1)). Qed.
Lemma lem1971156 (x : real) (y : real) (h1 : term232 x y) : False.
Proof. exact (EQ_MP (@lem1971155 x y h1) (@lem1971154 x y h1)). Qed.
Lemma lem1971157 (y : real) (x : real) (h1 : term167 y x) : term167 y x.
Proof. exact (h1). Qed.
Lemma lem1971158 (y : real) (x : real) (h1 : term167 y x) : term232 x y.
Proof. exact (EQ_MP (@lem1970422 x y) (@lem1971157 y x h1)). Qed.
Lemma lem1971159 (y : real) (x : real) (h1 : term167 y x) : (term232 x y) = False.
Proof. exact (prop_ext (fun h2 : term232 x y => @lem1971156 x y h2) (fun h2 : False => @lem1971158 y x h1)). Qed.
Lemma lem1971160 (y : real) (x : real) (h1 : term167 y x) : False.
Proof. exact (EQ_MP (@lem1971159 y x h1) (@lem1971158 y x h1)). Qed.
Lemma lem1971161 (y : real) (x : real) : term398 y x.
Proof. exact (fun h0 : term167 y x => @lem1971160 y x h0). Qed.
Lemma lem1971162 (y : real) (x : real) : term399 y x.
Proof. exact (@lem1386578 (term400 y x)). Qed.
Lemma lem1971163 (y : real) (x : real) : term400 y x.
Proof. exact (@lem1971162 y x (@lem1971161 y x)). Qed.
Lemma lem1971164 (h1 : term401) : term401.
Proof. exact (h1). Qed.
Lemma lem1971165 (x : real) (h1 : term401) : term402 x.
Proof. exact (@lem1971164 h1 x). Qed.
Lemma lem1971166 (x : real) : (term402 x) = (term403 x).
Proof. exact (eq_refl (term402 x)). Qed.
Lemma lem1971167 (x : real) (h1 : term401) : term403 x.
Proof. exact (EQ_MP (@lem1971166 x) (@lem1971165 x h1)). Qed.
Lemma lem1971168 (x : real) (y : real) (h1 : term401) : term404 x y.
Proof. exact (@lem1971167 x h1 y). Qed.
Lemma lem1971169 (x : real) (y : real) : (term404 x y) = (term405 x y).
Proof. exact (eq_refl (term404 x y)). Qed.
Lemma lem1971170 (x : real) (y : real) (h1 : term401) : term405 x y.
Proof. exact (EQ_MP (@lem1971169 x y) (@lem1971168 x y h1)). Qed.
Lemma lem1971171 (x : real) (y : real) (h1 : term406 x y) : term406 x y.
Proof. exact (h1). Qed.
Lemma lem1971172 (x : real) (y : real) (h1 : term401) (h2 : term406 x y) : term407 x y.
Proof. exact (@lem1971170 x y h1 (@lem1971171 x y h2)). Qed.
Lemma lem1971173 (x : real) (y : real) (h1 : term406 x y) : term408 x y.
Proof. exact (fun h0 : term401 => @lem1971172 x y h0 h1). Qed.
Lemma lem1971174 (h1 : term401) : term401.
Proof. exact (h1). Qed.
Lemma lem1971175 (x : real) (y : real) (h1 : term401) (h2 : term406 x y) : term407 x y.
Proof. exact (@lem1971173 x y h2 (@lem1971174 h1)). Qed.
Lemma lem1971176 (x : real) (y : real) (h1 : term401) : term405 x y.
Proof. exact (fun h0 : term406 x y => @lem1971175 x y h1 h0). Qed.
Lemma lem1971177 (x : real) (h1 : term401) : term403 x.
Proof. exact (fun y : real => @lem1971176 x y h1). Qed.
Lemma lem1971178 (h1 : term401) : term401.
Proof. exact (fun x : real => @lem1971177 x h1). Qed.
Lemma lem1971179 : term409.
Proof. exact (fun h0 : term401 => @lem1971178 h0). Qed.
Lemma lem1971180 : term401.
Proof. exact (@lem1971179 (@lem1969849)). Qed.
Lemma lem1971181 (x : real) : term402 x.
Proof. exact (@lem1971180 x). Qed.
Lemma lem1971182 (x : real) : (term402 x) = (term403 x).
Proof. exact (eq_refl (term402 x)). Qed.
Lemma lem1971183 (x : real) : term403 x.
Proof. exact (EQ_MP (@lem1971182 x) (@lem1971181 x)). Qed.
Lemma lem1971184 (x : real) (y : real) : term404 x y.
Proof. exact (@lem1971183 x y). Qed.
Lemma lem1971185 (x : real) (y : real) : (term404 x y) = (term405 x y).
Proof. exact (eq_refl (term404 x y)). Qed.
Lemma lem1971196 (x : real) : (term410 x) = (term411 x).
Proof. exact (@lem1483533 (real_abs x) (term412 x)). Qed.
Lemma lem1971208 (x : real) : (term413 x) = (term414 x).
Proof. exact (@lem1483519 (real_abs x) (term412 x)). Qed.
Lemma lem1971209 (x : real) : (term415 x) = (term416 x).
Proof. exact (@lem1483476 term16 term17 (real_abs x)). Qed.
Lemma lem1971211 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1971212 : term20 = term21.
Proof. exact (@lem1971211 term22 term23). Qed.
Lemma lem1971213 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1971214 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1971215 : term26 = term23.
Proof. exact (EQ_MP (@lem1971214) (@lem1971213)). Qed.
Lemma lem1971216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971217 : term27 = term17.
Proof. exact (MK_COMB (@lem1971216) (@lem1971215)). Qed.
Lemma lem1971218 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1971219 : term21 = term28.
Proof. exact (MK_COMB (@lem1971218) (@lem1971217)). Qed.
Lemma lem1971220 : term20 = term28.
Proof. exact (TRANS (@lem1971212) (@lem1971219)). Qed.
Lemma lem1971221 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971222 : term29 = term30.
Proof. exact (MK_COMB (@lem1971221) (@lem1971220)). Qed.
Lemma lem1971223 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1971224 (x : real) : (term416 x) = (term417 x).
Proof. exact (MK_COMB (@lem1971222) (@lem1971223 x)). Qed.
Lemma lem1971225 (x : real) : (term415 x) = (term417 x).
Proof. exact (TRANS (@lem1971209 x) (@lem1971224 x)). Qed.
Lemma lem1971226 (x : real) : (term418 x) = (term418 x).
Proof. exact (eq_refl (term418 x)). Qed.
Lemma lem1971227 (x : real) : (term414 x) = (term419 x).
Proof. exact (MK_COMB (@lem1971226 x) (@lem1971225 x)). Qed.
Lemma lem1971228 (x : real) : (term419 x) = (term420 x).
Proof. exact (@lem1483442 term28 (real_abs x)). Qed.
Lemma lem1971231 : term421 = term16.
Proof. exact (@lem1367767 term22 term22). Qed.
Lemma lem1971232 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1971233 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1971234 : term90 = term23.
Proof. exact (EQ_MP (@lem1971233) (@lem1971232)). Qed.
Lemma lem1971235 : term23 = term90.
Proof. exact (SYM (@lem1971234)). Qed.
Lemma lem1971236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971237 : term17 = term91.
Proof. exact (MK_COMB (@lem1971236) (@lem1971235)). Qed.
Lemma lem1971238 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1971239 : term28 = term88.
Proof. exact (MK_COMB (@lem1971238) (@lem1971237)). Qed.
Lemma lem1971240 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1971241 : term422 = term423.
Proof. exact (MK_COMB (@lem1971240) (@lem1971239)). Qed.
Lemma lem1971242 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem1971243 : term424 = term421.
Proof. exact (MK_COMB (@lem1971241) (@lem1971242)). Qed.
Lemma lem1971244 : term424 = term16.
Proof. exact (TRANS (@lem1971243) (@lem1971231)). Qed.
Lemma lem1971245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971246 : term425 = term77.
Proof. exact (MK_COMB (@lem1971245) (@lem1971244)). Qed.
Lemma lem1971247 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1971248 (x : real) : (term420 x) = (term426 x).
Proof. exact (MK_COMB (@lem1971246) (@lem1971247 x)). Qed.
Lemma lem1971249 (x : real) : (term419 x) = (term426 x).
Proof. exact (TRANS (@lem1971228 x) (@lem1971248 x)). Qed.
Lemma lem1971250 (x : real) : (term414 x) = (term426 x).
Proof. exact (TRANS (@lem1971227 x) (@lem1971249 x)). Qed.
Lemma lem1971252 (x : real) : (term413 x) = (term426 x).
Proof. exact (TRANS (@lem1971208 x) (@lem1971250 x)). Qed.
Lemma lem1971253 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971254 (x : real) : (term427 x) = (term428 x).
Proof. exact (MK_COMB (@lem1971253) (@lem1971252 x)). Qed.
Lemma lem1971255 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971256 (x : real) : (term411 x) = (term429 x).
Proof. exact (MK_COMB (@lem1971254 x) (@lem1971255)). Qed.
Lemma lem1971266 (x : real) : (term410 x) = (term429 x).
Proof. exact (TRANS (@lem1971196 x) (@lem1971256 x)). Qed.
Lemma lem1971268 (x : real) (r : real) : (term430 x r) = (term431 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1971269 (x : real) : (term429 x) = (term432 x).
Proof. exact (@lem1971268 x term121). Qed.
Lemma lem1971276 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1971277 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971278 (x : real) : (term433 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1971277) (@lem1971276 x)). Qed.
Lemma lem1971279 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971280 (x : real) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem1971278 x) (@lem1971279)). Qed.
Lemma lem1971293 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1971294 (x : real) : (term432 x) = (term436 x).
Proof. exact (MK_COMB (@lem1971293 x) (@lem1971280 x)). Qed.
Lemma lem1971297 (x : real) : (term429 x) = (term436 x).
Proof. exact (TRANS (@lem1971269 x) (@lem1971294 x)). Qed.
Lemma lem1971298 (x : real) (h1 : term436 x) : term436 x.
Proof. exact (h1). Qed.
Lemma lem1971299 (x : real) (h1 : term436 x) : term435 x.
Proof. exact (proj2 (@lem1971298 x h1)). Qed.
Lemma lem1971300 (x : real) (h1 : term436 x) : term177 x.
Proof. exact (proj1 (@lem1971298 x h1)). Qed.
Lemma lem1971302 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971303 : term368 = term369.
Proof. exact (@lem1971302 (NUMERAL 0) term22). Qed.
Lemma lem1971304 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1971305 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1971306 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1971305 h1) (fun h1 : term369 = True => @lem1971304)). Qed.
Lemma lem1971307 : term369 = True.
Proof. exact (EQ_MP (@lem1971306) (@lem1971304)). Qed.
Lemma lem1971308 : term368 = True.
Proof. exact (TRANS (@lem1971303) (@lem1971307)). Qed.
Lemma lem1971309 : True = term368.
Proof. exact (SYM (@lem1971308)). Qed.
Lemma lem1971310 : term368.
Proof. exact (EQ_MP (@lem1971309) (@lem0)). Qed.
Lemma lem1971311 (x : real) (h1 : term436 x) : term437 x.
Proof. exact (conj (@lem1971310) (@lem1971299 x h1)). Qed.
Lemma lem1971313 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1971314 (x : real) : term438 x.
Proof. exact (@lem1971313 term71 x). Qed.
Lemma lem1971315 (x : real) (h1 : term436 x) : term434 x.
Proof. exact (@lem1971314 x (@lem1971311 x h1)). Qed.
Lemma lem1971316 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1971317 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971318 (x : real) : (term433 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1971317) (@lem1971316 x)). Qed.
Lemma lem1971319 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971320 (x : real) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem1971318 x) (@lem1971319)). Qed.
Lemma lem1971321 (x : real) (h1 : term436 x) : term435 x.
Proof. exact (EQ_MP (@lem1971320 x) (@lem1971315 x h1)). Qed.
Lemma lem1971323 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971324 : term368 = term369.
Proof. exact (@lem1971323 (NUMERAL 0) term22). Qed.
Lemma lem1971325 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1971326 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1971327 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1971326 h1) (fun h1 : term369 = True => @lem1971325)). Qed.
Lemma lem1971328 : term369 = True.
Proof. exact (EQ_MP (@lem1971327) (@lem1971325)). Qed.
Lemma lem1971329 : term368 = True.
Proof. exact (TRANS (@lem1971324) (@lem1971328)). Qed.
Lemma lem1971330 : True = term368.
Proof. exact (SYM (@lem1971329)). Qed.
Lemma lem1971331 : term368.
Proof. exact (EQ_MP (@lem1971330) (@lem0)). Qed.
Lemma lem1971332 (x : real) (h1 : term436 x) : term380 x.
Proof. exact (conj (@lem1971331) (@lem1971300 x h1)). Qed.
Lemma lem1971334 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1971335 (x : real) : term382 x.
Proof. exact (@lem1971334 term71 (term52 x)). Qed.
Lemma lem1971336 (x : real) (h1 : term436 x) : term383 x.
Proof. exact (@lem1971335 x (@lem1971332 x h1)). Qed.
Lemma lem1971337 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1971338 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971339 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1971338) (@lem1971337 x)). Qed.
Lemma lem1971340 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971341 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1971339 x) (@lem1971340)). Qed.
Lemma lem1971342 (x : real) (h1 : term436 x) : term177 x.
Proof. exact (EQ_MP (@lem1971341 x) (@lem1971336 x h1)). Qed.
Lemma lem1971343 (x : real) (h1 : term436 x) : term436 x.
Proof. exact (conj (@lem1971342 x h1) (@lem1971321 x h1)). Qed.
Lemma lem1971345 (x : real) (y : real) : term439 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1971346 (x : real) : term440 x.
Proof. exact (@lem1971345 (term52 x) x). Qed.
Lemma lem1971347 (x : real) (h1 : term436 x) : term396 x.
Proof. exact (@lem1971346 x (@lem1971343 x h1)). Qed.
Lemma lem1971348 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1971350 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971351 : term122 = term121.
Proof. exact (@lem1971350 term22). Qed.
Lemma lem1971352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971353 : term123 = term124.
Proof. exact (MK_COMB (@lem1971352) (@lem1971351)). Qed.
Lemma lem1971354 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971355 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1971353) (@lem1971354 x)). Qed.
Lemma lem1971356 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1971348 x) (@lem1971355 x)). Qed.
Lemma lem1971357 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1971358 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1971356 x) (@lem1971357 x)). Qed.
Lemma lem1971359 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971360 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1971359) (@lem1971358 x)). Qed.
Lemma lem1971361 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971362 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1971360 x) (@lem1971361)). Qed.
Lemma lem1971363 (x : real) (h1 : term436 x) : term145.
Proof. exact (EQ_MP (@lem1971362 x) (@lem1971347 x h1)). Qed.
Lemma lem1971365 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1971366 : term145 = term152.
Proof. exact (@lem1971365 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1971367 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1971368 : term145 = False.
Proof. exact (TRANS (@lem1971366) (@lem1971367)). Qed.
Lemma lem1971369 (x : real) (h1 : term436 x) : False.
Proof. exact (EQ_MP (@lem1971368) (@lem1971363 x h1)). Qed.
Lemma lem1971370 (x : real) (h1 : term429 x) : term429 x.
Proof. exact (h1). Qed.
Lemma lem1971371 (x : real) (h1 : term429 x) : term436 x.
Proof. exact (EQ_MP (@lem1971297 x) (@lem1971370 x h1)). Qed.
Lemma lem1971372 (x : real) (h1 : term429 x) : (term436 x) = False.
Proof. exact (prop_ext (fun h2 : term436 x => @lem1971369 x h2) (fun h2 : False => @lem1971371 x h1)). Qed.
Lemma lem1971373 (x : real) (h1 : term429 x) : False.
Proof. exact (EQ_MP (@lem1971372 x h1) (@lem1971371 x h1)). Qed.
Lemma lem1971374 (x : real) (h1 : term410 x) : term410 x.
Proof. exact (h1). Qed.
Lemma lem1971375 (x : real) (h1 : term410 x) : term429 x.
Proof. exact (EQ_MP (@lem1971266 x) (@lem1971374 x h1)). Qed.
Lemma lem1971376 (x : real) (h1 : term410 x) : (term429 x) = False.
Proof. exact (prop_ext (fun h2 : term429 x => @lem1971373 x h2) (fun h2 : False => @lem1971375 x h1)). Qed.
Lemma lem1971377 (x : real) (h1 : term410 x) : False.
Proof. exact (EQ_MP (@lem1971376 x h1) (@lem1971375 x h1)). Qed.
Lemma lem1971378 (x : real) : term441 x.
Proof. exact (fun h0 : term410 x => @lem1971377 x h0). Qed.
Lemma lem1971379 (x : real) : term442 x.
Proof. exact (@lem1386578 (term443 x)). Qed.
Lemma lem1971380 (x : real) : term443 x.
Proof. exact (@lem1971379 x (@lem1971378 x)). Qed.
Lemma lem1971381 (x : real) : (term443 x) = ((term443 x) = True).
Proof. exact (@lem7 (term443 x)). Qed.
Lemma lem1971383 (x : real) : term444 x.
Proof. exact (@lem1954889 x). Qed.
Lemma lem1971384 (x : real) : (term444 x) = (term445 x).
Proof. exact (eq_refl (term444 x)). Qed.
Lemma lem1971385 (x : real) : term445 x.
Proof. exact (EQ_MP (@lem1971384 x) (@lem1971383 x)). Qed.
Lemma lem1971386 (x : real) (y : real) : term446 x y.
Proof. exact (@lem1971385 x y). Qed.
Lemma lem1971387 (x : real) (y : real) : (term446 x y) = ((term447 x y) = (real_le x y)).
Proof. exact (eq_refl (term446 x y)). Qed.
Lemma lem1971390 (x : real) (h1 : (term3 x) = (term4 x)) : (term3 x) = (term4 x).
Proof. exact (h1). Qed.
Lemma lem1971391 (x : real) (h1 : (term3 x) = (term4 x)) : (term4 x) = (term3 x).
Proof. exact (SYM (@lem1971390 x h1)). Qed.
Lemma lem1971392 (x : real) (h1 : (term4 x) = (term3 x)) : (term4 x) = (term3 x).
Proof. exact (h1). Qed.
Lemma lem1971393 (x : real) (h1 : (term4 x) = (term3 x)) : (term3 x) = (term4 x).
Proof. exact (SYM (@lem1971392 x h1)). Qed.
Lemma lem1971394 (x : real) : ((term3 x) = (term4 x)) = ((term4 x) = (term3 x)).
Proof. exact (prop_ext (fun h1 : (term3 x) = (term4 x) => @lem1971391 x h1) (fun h1 : (term4 x) = (term3 x) => @lem1971393 x h1)). Qed.
Lemma lem1971395 : term448 = term449.
Proof. exact (fun_ext (fun x : real => @lem1971394 x)). Qed.
Lemma lem1971396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1971397 : term450 = term451.
Proof. exact (MK_COMB (@lem1971396) (@lem1971395)). Qed.
Lemma lem1971398 : term451.
Proof. exact (EQ_MP (@lem1971397) (@lem1921835)). Qed.
Lemma lem1971399 (x : real) : term452 x.
Proof. exact (@lem1971398 x). Qed.
Lemma lem1971400 (x : real) : (term452 x) = ((term4 x) = (term3 x)).
Proof. exact (eq_refl (term452 x)). Qed.
Lemma lem1971411 (x : real) (y : real) : (term453 x y) = (term454 x y).
Proof. exact (@lem1483554 (term170 x y) (term455 x y)). Qed.
Lemma lem1971424 (x : real) (y : real) : (term456 x y) = (term457 x y).
Proof. exact (@lem1483519 (term170 x y) (term455 x y)). Qed.
Lemma lem1971425 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1971426 (x : real) (y : real) : (term458 x y) = (term459 x y).
Proof. exact (MK_COMB (@lem1971425) (@lem1971424 x y)). Qed.
Lemma lem1971427 (x : real) (y : real) : (term459 x y) = (term460 x y).
Proof. exact (@lem1483512 (term457 x y)). Qed.
Lemma lem1971428 (x : real) (y : real) : (term460 x y) = (term461 x y).
Proof. exact (@lem1483508 (term170 x y) term16 (term462 x y)). Qed.
Lemma lem1971429 (x : real) (y : real) : (term463 x y) = (term464 x y).
Proof. exact (@lem1483476 term16 term16 (term455 x y)). Qed.
Lemma lem1971431 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971432 : term67 = term68.
Proof. exact (@lem1971431 term22 term22). Qed.
Lemma lem1971433 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971434 : term70 = term22.
Proof. exact (EQ_MP (@lem1971433) (@lem940073)). Qed.
Lemma lem1971435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971436 : term68 = term71.
Proof. exact (MK_COMB (@lem1971435) (@lem1971434)). Qed.
Lemma lem1971437 : term67 = term71.
Proof. exact (TRANS (@lem1971432) (@lem1971436)). Qed.
Lemma lem1971438 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971439 : term72 = term73.
Proof. exact (MK_COMB (@lem1971438) (@lem1971437)). Qed.
Lemma lem1971440 (x : real) (y : real) : (term455 x y) = (term455 x y).
Proof. exact (eq_refl (term455 x y)). Qed.
Lemma lem1971441 (x : real) (y : real) : (term464 x y) = (term465 x y).
Proof. exact (MK_COMB (@lem1971439) (@lem1971440 x y)). Qed.
Lemma lem1971442 (x : real) (y : real) : (term463 x y) = (term465 x y).
Proof. exact (TRANS (@lem1971429 x y) (@lem1971441 x y)). Qed.
Lemma lem1971443 (x : real) (y : real) : (term465 x y) = (term455 x y).
Proof. exact (@lem1483436 (term455 x y)). Qed.
Lemma lem1971444 (x : real) (y : real) : (term463 x y) = (term455 x y).
Proof. exact (TRANS (@lem1971442 x y) (@lem1971443 x y)). Qed.
Lemma lem1971447 (x : real) (y : real) : (term466 x y) = (term466 x y).
Proof. exact (eq_refl (term466 x y)). Qed.
Lemma lem1971448 (x : real) (y : real) : (term461 x y) = (term467 x y).
Proof. exact (MK_COMB (@lem1971447 x y) (@lem1971444 x y)). Qed.
Lemma lem1971449 (x : real) (y : real) : (term460 x y) = (term467 x y).
Proof. exact (TRANS (@lem1971428 x y) (@lem1971448 x y)). Qed.
Lemma lem1971450 (x : real) (y : real) : (term459 x y) = (term467 x y).
Proof. exact (TRANS (@lem1971427 x y) (@lem1971449 x y)). Qed.
Lemma lem1971451 (x : real) (y : real) : (term468 x y) = (term468 x y).
Proof. exact (eq_refl (term468 x y)). Qed.
Lemma lem1971452 (x : real) (y : real) : ((term458 x y) = (term459 x y)) = ((term458 x y) = (term467 x y)).
Proof. exact (MK_COMB (@lem1971451 x y) (@lem1971450 x y)). Qed.
Lemma lem1971453 (x : real) (y : real) : (term458 x y) = (term467 x y).
Proof. exact (EQ_MP (@lem1971452 x y) (@lem1971426 x y)). Qed.
Lemma lem1971454 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971455 (x : real) (y : real) : (term469 x y) = (term470 x y).
Proof. exact (MK_COMB (@lem1971454) (@lem1971453 x y)). Qed.
Lemma lem1971456 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971457 (x : real) (y : real) : (term471 x y) = (term472 x y).
Proof. exact (MK_COMB (@lem1971455 x y) (@lem1971456)). Qed.
Lemma lem1971458 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971459 (x : real) (y : real) : (term473 x y) = (term474 x y).
Proof. exact (MK_COMB (@lem1971458) (@lem1971424 x y)). Qed.
Lemma lem1971460 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971461 (x : real) (y : real) : (term475 x y) = (term476 x y).
Proof. exact (MK_COMB (@lem1971459 x y) (@lem1971460)). Qed.
Lemma lem1971462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1971463 (x : real) (y : real) : (term477 x y) = (term478 x y).
Proof. exact (MK_COMB (@lem1971462) (@lem1971461 x y)). Qed.
Lemma lem1971464 (x : real) (y : real) : (term454 x y) = (term479 x y).
Proof. exact (MK_COMB (@lem1971463 x y) (@lem1971457 x y)). Qed.
Lemma lem1971478 (x : real) (y : real) : (term453 x y) = (term479 x y).
Proof. exact (TRANS (@lem1971411 x y) (@lem1971464 x y)). Qed.
Lemma lem1971480 (a : real) (x : real) (r : real) : (term480 a x r) = (term481 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1971481 (x : real) (y : real) : (term476 x y) = (term482 x y).
Proof. exact (@lem1971480 (term170 x y) (term483 x y) term121). Qed.
Lemma lem1971488 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1971495 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1971496 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971497 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1971496) (@lem1971495 x)). Qed.
Lemma lem1971498 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1971497 x) (@lem1971488 y)). Qed.
Lemma lem1971499 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1971500 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1971502 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971503 : term67 = term68.
Proof. exact (@lem1971502 term22 term22). Qed.
Lemma lem1971504 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971505 : term70 = term22.
Proof. exact (EQ_MP (@lem1971504) (@lem940073)). Qed.
Lemma lem1971506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971507 : term68 = term71.
Proof. exact (MK_COMB (@lem1971506) (@lem1971505)). Qed.
Lemma lem1971508 : term67 = term71.
Proof. exact (TRANS (@lem1971503) (@lem1971507)). Qed.
Lemma lem1971509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971510 : term72 = term73.
Proof. exact (MK_COMB (@lem1971509) (@lem1971508)). Qed.
Lemma lem1971511 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971512 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1971510) (@lem1971511 y)). Qed.
Lemma lem1971513 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1971500 y) (@lem1971512 y)). Qed.
Lemma lem1971514 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1971515 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1971513 y) (@lem1971514 y)). Qed.
Lemma lem1971516 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971519 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1971516 x) (@lem1971515 y)). Qed.
Lemma lem1971520 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971499 x y) (@lem1971519 x y)). Qed.
Lemma lem1971521 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971498 x y) (@lem1971520 x y)). Qed.
Lemma lem1971524 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1971525 (x : real) (y : real) : (term487 x y) = (term488 x y).
Proof. exact (MK_COMB (@lem1971524) (@lem1971521 x y)). Qed.
Lemma lem1971526 (x : real) (y : real) : (term488 x y) = (term190 x y).
Proof. exact (@lem1483460 (term190 x y)). Qed.
Lemma lem1971527 (x : real) (y : real) : (term487 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971525 x y) (@lem1971526 x y)). Qed.
Lemma lem1971530 (x : real) (y : real) : (term201 x y) = (term201 x y).
Proof. exact (eq_refl (term201 x y)). Qed.
Lemma lem1971531 (x : real) (y : real) : (term489 x y) = (term490 x y).
Proof. exact (MK_COMB (@lem1971530 x y) (@lem1971527 x y)). Qed.
Lemma lem1971532 (x : real) (y : real) : (term490 x y) = (term491 x y).
Proof. exact (@lem1483484 (term52 x) (term170 x y) y). Qed.
Lemma lem1971533 (x : real) (y : real) : (term492 x y) = (term493 x y).
Proof. exact (@lem1483488 y (term170 x y)). Qed.
Lemma lem1971534 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971535 (x : real) (y : real) : (term491 x y) = (term494 x y).
Proof. exact (MK_COMB (@lem1971534 x) (@lem1971533 x y)). Qed.
Lemma lem1971536 (x : real) (y : real) : (term490 x y) = (term494 x y).
Proof. exact (TRANS (@lem1971532 x y) (@lem1971535 x y)). Qed.
Lemma lem1971537 (x : real) (y : real) : (term489 x y) = (term494 x y).
Proof. exact (TRANS (@lem1971531 x y) (@lem1971536 x y)). Qed.
Lemma lem1971538 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971539 (x : real) (y : real) : (term495 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem1971538) (@lem1971537 x y)). Qed.
Lemma lem1971540 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971541 (x : real) (y : real) : (term497 x y) = (term498 x y).
Proof. exact (MK_COMB (@lem1971539 x y) (@lem1971540)). Qed.
Lemma lem1971548 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1971555 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1971556 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971557 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1971556) (@lem1971555 x)). Qed.
Lemma lem1971558 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1971557 x) (@lem1971548 y)). Qed.
Lemma lem1971559 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1971560 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1971562 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971563 : term67 = term68.
Proof. exact (@lem1971562 term22 term22). Qed.
Lemma lem1971564 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971565 : term70 = term22.
Proof. exact (EQ_MP (@lem1971564) (@lem940073)). Qed.
Lemma lem1971566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971567 : term68 = term71.
Proof. exact (MK_COMB (@lem1971566) (@lem1971565)). Qed.
Lemma lem1971568 : term67 = term71.
Proof. exact (TRANS (@lem1971563) (@lem1971567)). Qed.
Lemma lem1971569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971570 : term72 = term73.
Proof. exact (MK_COMB (@lem1971569) (@lem1971568)). Qed.
Lemma lem1971571 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971572 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1971570) (@lem1971571 y)). Qed.
Lemma lem1971573 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1971560 y) (@lem1971572 y)). Qed.
Lemma lem1971574 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1971575 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1971573 y) (@lem1971574 y)). Qed.
Lemma lem1971576 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971579 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1971576 x) (@lem1971575 y)). Qed.
Lemma lem1971580 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971559 x y) (@lem1971579 x y)). Qed.
Lemma lem1971581 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971558 x y) (@lem1971580 x y)). Qed.
Lemma lem1971584 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1971585 (x : real) (y : real) : (term499 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1971584) (@lem1971581 x y)). Qed.
Lemma lem1971586 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483508 (term52 x) term16 y). Qed.
Lemma lem1971587 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1971588 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1971590 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971591 : term67 = term68.
Proof. exact (@lem1971590 term22 term22). Qed.
Lemma lem1971592 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971593 : term70 = term22.
Proof. exact (EQ_MP (@lem1971592) (@lem940073)). Qed.
Lemma lem1971594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971595 : term68 = term71.
Proof. exact (MK_COMB (@lem1971594) (@lem1971593)). Qed.
Lemma lem1971596 : term67 = term71.
Proof. exact (TRANS (@lem1971591) (@lem1971595)). Qed.
Lemma lem1971597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971598 : term72 = term73.
Proof. exact (MK_COMB (@lem1971597) (@lem1971596)). Qed.
Lemma lem1971599 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971600 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1971598) (@lem1971599 x)). Qed.
Lemma lem1971601 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1971588 x) (@lem1971600 x)). Qed.
Lemma lem1971602 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1971603 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1971601 x) (@lem1971602 x)). Qed.
Lemma lem1971604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1971605 (x : real) : (term200 x) = (real_add x).
Proof. exact (MK_COMB (@lem1971604) (@lem1971603 x)). Qed.
Lemma lem1971606 (x : real) (y : real) : (term196 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1971605 x) (@lem1971587 y)). Qed.
Lemma lem1971607 (x : real) (y : real) : (term195 x y) = (term40 x y).
Proof. exact (TRANS (@lem1971586 x y) (@lem1971606 x y)). Qed.
Lemma lem1971608 (x : real) (y : real) : (term499 x y) = (term40 x y).
Proof. exact (TRANS (@lem1971585 x y) (@lem1971607 x y)). Qed.
Lemma lem1971611 (x : real) (y : real) : (term201 x y) = (term201 x y).
Proof. exact (eq_refl (term201 x y)). Qed.
Lemma lem1971612 (x : real) (y : real) : (term500 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem1971611 x y) (@lem1971608 x y)). Qed.
Lemma lem1971613 (x : real) (y : real) : (term202 x y) = (term203 x y).
Proof. exact (@lem1483484 x (term170 x y) (term52 y)). Qed.
Lemma lem1971614 (x : real) (y : real) : (term204 x y) = (term205 x y).
Proof. exact (@lem1483488 (term52 y) (term170 x y)). Qed.
Lemma lem1971615 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1971616 (x : real) (y : real) : (term203 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1971615 x) (@lem1971614 x y)). Qed.
Lemma lem1971617 (x : real) (y : real) : (term202 x y) = (term206 x y).
Proof. exact (TRANS (@lem1971613 x y) (@lem1971616 x y)). Qed.
Lemma lem1971618 (x : real) (y : real) : (term500 x y) = (term206 x y).
Proof. exact (TRANS (@lem1971612 x y) (@lem1971617 x y)). Qed.
Lemma lem1971619 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971620 (x : real) (y : real) : (term501 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1971619) (@lem1971618 x y)). Qed.
Lemma lem1971621 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971622 (x : real) (y : real) : (term502 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem1971620 x y) (@lem1971621)). Qed.
Lemma lem1971623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1971624 (x : real) (y : real) : (term503 x y) = (term504 x y).
Proof. exact (MK_COMB (@lem1971623) (@lem1971622 x y)). Qed.
Lemma lem1971625 (x : real) (y : real) : (term482 x y) = (term505 x y).
Proof. exact (MK_COMB (@lem1971624 x y) (@lem1971541 x y)). Qed.
Lemma lem1971626 (x : real) (y : real) : (term476 x y) = (term505 x y).
Proof. exact (TRANS (@lem1971481 x y) (@lem1971625 x y)). Qed.
Lemma lem1971627 (x : real) (y : real) : (term506 x y) = (term505 x y).
Proof. exact (eq_refl (term506 x y)). Qed.
Lemma lem1971628 (x : real) (y : real) : (term505 x y) = (term506 x y).
Proof. exact (SYM (@lem1971627 x y)). Qed.
Lemma lem1971629 (x : real) (y : real) : (term506 x y) = (term507 x y).
Proof. exact (@lem1482981 (term508 x y) (real_sub x y)). Qed.
Lemma lem1971630 (x : real) (y : real) : (term505 x y) = (term507 x y).
Proof. exact (TRANS (@lem1971628 x y) (@lem1971629 x y)). Qed.
Lemma lem1971631 (x : real) (y : real) : (term509 x y) = (term510 x y).
Proof. exact (eq_refl (term509 x y)). Qed.
Lemma lem1971632 (x : real) (y : real) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem1971633 (x : real) (y : real) : (term511 x y) = (term512 x y).
Proof. exact (MK_COMB (@lem1971632 x y) (@lem1971631 x y)). Qed.
Lemma lem1971634 (x : real) (y : real) : (term513 x y) = (term514 x y).
Proof. exact (eq_refl (term513 x y)). Qed.
Lemma lem1971635 (x : real) (y : real) : (term244 x y) = (term244 x y).
Proof. exact (eq_refl (term244 x y)). Qed.
Lemma lem1971636 (x : real) (y : real) : (term515 x y) = (term516 x y).
Proof. exact (MK_COMB (@lem1971635 x y) (@lem1971634 x y)). Qed.
Lemma lem1971637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1971638 (x : real) (y : real) : (term517 x y) = (term518 x y).
Proof. exact (MK_COMB (@lem1971637) (@lem1971636 x y)). Qed.
Lemma lem1971639 (x : real) (y : real) : (term507 x y) = (term519 x y).
Proof. exact (MK_COMB (@lem1971638 x y) (@lem1971633 x y)). Qed.
Lemma lem1971640 (x : real) (y : real) : (term520 x y) = (term520 x y).
Proof. exact (eq_refl (term520 x y)). Qed.
Lemma lem1971641 (x : real) (y : real) : ((term505 x y) = (term507 x y)) = ((term505 x y) = (term519 x y)).
Proof. exact (MK_COMB (@lem1971640 x y) (@lem1971639 x y)). Qed.
Lemma lem1971642 (x : real) (y : real) : (term505 x y) = (term519 x y).
Proof. exact (EQ_MP (@lem1971641 x y) (@lem1971630 x y)). Qed.
Lemma lem1971643 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (@lem1483527 (real_sub x y) term121). Qed.
Lemma lem1971644 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971657 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1971658 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971659 (x : real) (y : real) : (term253 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem1971658) (@lem1971657 x y)). Qed.
Lemma lem1971660 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1971659 x y) (@lem1971644)). Qed.
Lemma lem1971661 (x : real) (y : real) : (term256 x y) = (term257 x y).
Proof. exact (@lem1483519 (term40 x y) term121). Qed.
Lemma lem1971663 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1971664 : term139 = term121.
Proof. exact (@lem1971663 term22). Qed.
Lemma lem1971665 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1971666 (x : real) (y : real) : (term257 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1971665 x y) (@lem1971664)). Qed.
Lemma lem1971667 (x : real) (y : real) : (term259 x y) = (term40 x y).
Proof. exact (@lem1483450 (term40 x y)). Qed.
Lemma lem1971668 (x : real) (y : real) : (term257 x y) = (term40 x y).
Proof. exact (TRANS (@lem1971666 x y) (@lem1971667 x y)). Qed.
Lemma lem1971669 (x : real) (y : real) : (term256 x y) = (term40 x y).
Proof. exact (TRANS (@lem1971661 x y) (@lem1971668 x y)). Qed.
Lemma lem1971670 (x : real) (y : real) : (term255 x y) = (term40 x y).
Proof. exact (TRANS (@lem1971660 x y) (@lem1971669 x y)). Qed.
Lemma lem1971671 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1971672 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1971671) (@lem1971670 x y)). Qed.
Lemma lem1971673 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971674 (x : real) (y : real) : (term252 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem1971672 x y) (@lem1971673)). Qed.
Lemma lem1971675 (x : real) (y : real) : (term251 x y) = (term262 x y).
Proof. exact (TRANS (@lem1971643 x y) (@lem1971674 x y)). Qed.
Lemma lem1971676 (x : real) (y : real) : (term268 x y) = (term269 x y).
Proof. exact (@lem1483525 (term270 x y) term121). Qed.
Lemma lem1971677 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971690 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1971699 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1971700 (x : real) (y : real) : (term271 x y) = (term272 x y).
Proof. exact (MK_COMB (@lem1971699 y) (@lem1971690 x y)). Qed.
Lemma lem1971701 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483484 x (term52 y) (term52 y)). Qed.
Lemma lem1971702 (y : real) : (term274 y) = (term275 y).
Proof. exact (@lem1483438 term16 term16 y). Qed.
Lemma lem1971703 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1971704 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1971705 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1971706 : term90 = term23.
Proof. exact (EQ_MP (@lem1971705) (@lem1971704)). Qed.
Lemma lem1971707 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971708 : term91 = term17.
Proof. exact (MK_COMB (@lem1971707) (@lem1971706)). Qed.
Lemma lem1971709 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1971710 : term88 = term28.
Proof. exact (MK_COMB (@lem1971709) (@lem1971708)). Qed.
Lemma lem1971711 : term87 = term28.
Proof. exact (TRANS (@lem1971703) (@lem1971710)). Qed.
Lemma lem1971712 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971713 : term92 = term30.
Proof. exact (MK_COMB (@lem1971712) (@lem1971711)). Qed.
Lemma lem1971714 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971715 (y : real) : (term275 y) = (term276 y).
Proof. exact (MK_COMB (@lem1971713) (@lem1971714 y)). Qed.
Lemma lem1971716 (y : real) : (term274 y) = (term276 y).
Proof. exact (TRANS (@lem1971702 y) (@lem1971715 y)). Qed.
Lemma lem1971717 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1971718 (x : real) (y : real) : (term273 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1971717 x) (@lem1971716 y)). Qed.
Lemma lem1971719 (x : real) (y : real) : (term272 x y) = (term277 x y).
Proof. exact (TRANS (@lem1971701 x y) (@lem1971718 x y)). Qed.
Lemma lem1971720 (x : real) (y : real) : (term271 x y) = (term277 x y).
Proof. exact (TRANS (@lem1971700 x y) (@lem1971719 x y)). Qed.
Lemma lem1971723 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1971724 (x : real) (y : real) : (term270 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1971723 x) (@lem1971720 x y)). Qed.
Lemma lem1971725 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (@lem1483490 x x (term276 y)). Qed.
Lemma lem1971726 (x : real) : (real_add x x) = (term280 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1971727 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1971728 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1971729 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1971730 : term90 = term23.
Proof. exact (EQ_MP (@lem1971729) (@lem1971728)). Qed.
Lemma lem1971731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971732 : term91 = term17.
Proof. exact (MK_COMB (@lem1971731) (@lem1971730)). Qed.
Lemma lem1971733 : term281 = term17.
Proof. exact (TRANS (@lem1971727) (@lem1971732)). Qed.
Lemma lem1971734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971735 : term282 = term109.
Proof. exact (MK_COMB (@lem1971734) (@lem1971733)). Qed.
Lemma lem1971736 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971737 (x : real) : (term280 x) = (term283 x).
Proof. exact (MK_COMB (@lem1971735) (@lem1971736 x)). Qed.
Lemma lem1971738 (x : real) : (real_add x x) = (term283 x).
Proof. exact (TRANS (@lem1971726 x) (@lem1971737 x)). Qed.
Lemma lem1971739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1971740 (x : real) : (term284 x) = (term285 x).
Proof. exact (MK_COMB (@lem1971739) (@lem1971738 x)). Qed.
Lemma lem1971741 (y : real) : (term276 y) = (term276 y).
Proof. exact (eq_refl (term276 y)). Qed.
Lemma lem1971742 (x : real) (y : real) : (term279 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1971740 x) (@lem1971741 y)). Qed.
Lemma lem1971743 (x : real) (y : real) : (term278 x y) = (term286 x y).
Proof. exact (TRANS (@lem1971725 x y) (@lem1971742 x y)). Qed.
Lemma lem1971744 (x : real) (y : real) : (term270 x y) = (term286 x y).
Proof. exact (TRANS (@lem1971724 x y) (@lem1971743 x y)). Qed.
Lemma lem1971745 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971746 (x : real) (y : real) : (term287 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem1971745) (@lem1971744 x y)). Qed.
Lemma lem1971747 (x : real) (y : real) : (term289 x y) = (term290 x y).
Proof. exact (MK_COMB (@lem1971746 x y) (@lem1971677)). Qed.
Lemma lem1971748 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (@lem1483519 (term286 x y) term121). Qed.
Lemma lem1971750 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1971751 : term139 = term121.
Proof. exact (@lem1971750 term22). Qed.
Lemma lem1971752 (x : real) (y : real) : (term292 x y) = (term292 x y).
Proof. exact (eq_refl (term292 x y)). Qed.
Lemma lem1971753 (x : real) (y : real) : (term291 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1971752 x y) (@lem1971751)). Qed.
Lemma lem1971754 (x : real) (y : real) : (term293 x y) = (term286 x y).
Proof. exact (@lem1483450 (term286 x y)). Qed.
Lemma lem1971755 (x : real) (y : real) : (term291 x y) = (term286 x y).
Proof. exact (TRANS (@lem1971753 x y) (@lem1971754 x y)). Qed.
Lemma lem1971756 (x : real) (y : real) : (term290 x y) = (term286 x y).
Proof. exact (TRANS (@lem1971748 x y) (@lem1971755 x y)). Qed.
Lemma lem1971757 (x : real) (y : real) : (term289 x y) = (term286 x y).
Proof. exact (TRANS (@lem1971747 x y) (@lem1971756 x y)). Qed.
Lemma lem1971758 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971759 (x : real) (y : real) : (term294 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1971758) (@lem1971757 x y)). Qed.
Lemma lem1971760 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971761 (x : real) (y : real) : (term269 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1971759 x y) (@lem1971760)). Qed.
Lemma lem1971762 (x : real) (y : real) : (term268 x y) = (term296 x y).
Proof. exact (TRANS (@lem1971676 x y) (@lem1971761 x y)). Qed.
Lemma lem1971763 (x : real) (y : real) : (term521 x y) = (term522 x y).
Proof. exact (@lem1483525 (term523 x y) term121). Qed.
Lemma lem1971764 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971777 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1971780 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1971781 (x : real) (y : real) : (term524 x y) = (term340 x y).
Proof. exact (MK_COMB (@lem1971780 y) (@lem1971777 x y)). Qed.
Lemma lem1971782 (x : real) (y : real) : (term340 x y) = (term341 x y).
Proof. exact (@lem1483484 x y (term52 y)). Qed.
Lemma lem1971783 (y : real) : (term323 y) = (term321 y).
Proof. exact (@lem1483442 term16 y). Qed.
Lemma lem1971785 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971786 : term122 = term121.
Proof. exact (@lem1971785 term22). Qed.
Lemma lem1971787 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971788 : term123 = term124.
Proof. exact (MK_COMB (@lem1971787) (@lem1971786)). Qed.
Lemma lem1971789 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971790 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1971788) (@lem1971789 y)). Qed.
Lemma lem1971791 (y : real) : (term323 y) = (term322 y).
Proof. exact (TRANS (@lem1971783 y) (@lem1971790 y)). Qed.
Lemma lem1971792 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1971793 (y : real) : (term323 y) = term121.
Proof. exact (TRANS (@lem1971791 y) (@lem1971792 y)). Qed.
Lemma lem1971794 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1971795 (y : real) (x : real) : (term341 x y) = (term182 x).
Proof. exact (MK_COMB (@lem1971794 x) (@lem1971793 y)). Qed.
Lemma lem1971796 (y : real) (x : real) : (term340 x y) = (term182 x).
Proof. exact (TRANS (@lem1971782 x y) (@lem1971795 y x)). Qed.
Lemma lem1971797 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1971798 (y : real) (x : real) : (term340 x y) = x.
Proof. exact (TRANS (@lem1971796 y x) (@lem1971797 x)). Qed.
Lemma lem1971799 (y : real) (x : real) : (term524 x y) = x.
Proof. exact (TRANS (@lem1971781 x y) (@lem1971798 y x)). Qed.
Lemma lem1971808 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971809 (y : real) (x : real) : (term523 x y) = (term320 x).
Proof. exact (MK_COMB (@lem1971808 x) (@lem1971799 y x)). Qed.
Lemma lem1971810 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1971812 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971813 : term122 = term121.
Proof. exact (@lem1971812 term22). Qed.
Lemma lem1971814 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971815 : term123 = term124.
Proof. exact (MK_COMB (@lem1971814) (@lem1971813)). Qed.
Lemma lem1971816 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971817 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1971815) (@lem1971816 x)). Qed.
Lemma lem1971818 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1971810 x) (@lem1971817 x)). Qed.
Lemma lem1971819 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1971820 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1971818 x) (@lem1971819 x)). Qed.
Lemma lem1971821 (x : real) (y : real) : (term523 x y) = term121.
Proof. exact (TRANS (@lem1971809 y x) (@lem1971820 x)). Qed.
Lemma lem1971822 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971823 (x : real) (y : real) : (term525 x y) = term302.
Proof. exact (MK_COMB (@lem1971822) (@lem1971821 x y)). Qed.
Lemma lem1971824 (x : real) (y : real) : (term526 x y) = term326.
Proof. exact (MK_COMB (@lem1971823 x y) (@lem1971764)). Qed.
Lemma lem1971825 : term326 = term327.
Proof. exact (@lem1483519 term121 term121). Qed.
Lemma lem1971827 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1971828 : term139 = term121.
Proof. exact (@lem1971827 term22). Qed.
Lemma lem1971829 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1971830 : term327 = term136.
Proof. exact (MK_COMB (@lem1971829) (@lem1971828)). Qed.
Lemma lem1971831 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1971832 : term327 = term121.
Proof. exact (TRANS (@lem1971830) (@lem1971831)). Qed.
Lemma lem1971833 : term326 = term121.
Proof. exact (TRANS (@lem1971825) (@lem1971832)). Qed.
Lemma lem1971834 (x : real) (y : real) : (term526 x y) = term121.
Proof. exact (TRANS (@lem1971824 x y) (@lem1971833)). Qed.
Lemma lem1971835 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971836 (x : real) (y : real) : (term527 x y) = term143.
Proof. exact (MK_COMB (@lem1971835) (@lem1971834 x y)). Qed.
Lemma lem1971837 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971838 (x : real) (y : real) : (term522 x y) = term145.
Proof. exact (MK_COMB (@lem1971836 x y) (@lem1971837)). Qed.
Lemma lem1971839 (x : real) (y : real) : (term521 x y) = term145.
Proof. exact (TRANS (@lem1971763 x y) (@lem1971838 x y)). Qed.
Lemma lem1971840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1971841 (x : real) (y : real) : (term528 x y) = (term529 x y).
Proof. exact (MK_COMB (@lem1971840) (@lem1971762 x y)). Qed.
Lemma lem1971842 (x : real) (y : real) : (term514 x y) = (term530 x y).
Proof. exact (MK_COMB (@lem1971841 x y) (@lem1971839 x y)). Qed.
Lemma lem1971843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1971844 (x : real) (y : real) : (term244 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem1971843) (@lem1971675 x y)). Qed.
Lemma lem1971845 (x : real) (y : real) : (term516 x y) = (term531 x y).
Proof. exact (MK_COMB (@lem1971844 x y) (@lem1971842 x y)). Qed.
Lemma lem1971846 (x : real) (y : real) : (term300 x y) = (term301 x y).
Proof. exact (@lem1483525 term121 (real_sub x y)). Qed.
Lemma lem1971859 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1971862 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1971863 (x : real) (y : real) : (term303 x y) = (term304 x y).
Proof. exact (MK_COMB (@lem1971862) (@lem1971859 x y)). Qed.
Lemma lem1971864 (x : real) (y : real) : (term304 x y) = (term305 x y).
Proof. exact (@lem1483519 term121 (term40 x y)). Qed.
Lemma lem1971865 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1971866 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1971868 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971869 : term67 = term68.
Proof. exact (@lem1971868 term22 term22). Qed.
Lemma lem1971870 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971871 : term70 = term22.
Proof. exact (EQ_MP (@lem1971870) (@lem940073)). Qed.
Lemma lem1971872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971873 : term68 = term71.
Proof. exact (MK_COMB (@lem1971872) (@lem1971871)). Qed.
Lemma lem1971874 : term67 = term71.
Proof. exact (TRANS (@lem1971869) (@lem1971873)). Qed.
Lemma lem1971875 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971876 : term72 = term73.
Proof. exact (MK_COMB (@lem1971875) (@lem1971874)). Qed.
Lemma lem1971877 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971878 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1971876) (@lem1971877 y)). Qed.
Lemma lem1971879 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1971866 y) (@lem1971878 y)). Qed.
Lemma lem1971880 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1971881 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1971879 y) (@lem1971880 y)). Qed.
Lemma lem1971884 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971885 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1971884 x) (@lem1971881 y)). Qed.
Lemma lem1971886 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971865 x y) (@lem1971885 x y)). Qed.
Lemma lem1971887 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1971888 (x : real) (y : real) : (term305 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1971887) (@lem1971886 x y)). Qed.
Lemma lem1971889 (x : real) (y : real) : (term308 x y) = (term190 x y).
Proof. exact (@lem1483448 (term190 x y)). Qed.
Lemma lem1971890 (x : real) (y : real) : (term305 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971888 x y) (@lem1971889 x y)). Qed.
Lemma lem1971891 (x : real) (y : real) : (term304 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971864 x y) (@lem1971890 x y)). Qed.
Lemma lem1971892 (x : real) (y : real) : (term303 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971863 x y) (@lem1971891 x y)). Qed.
Lemma lem1971893 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971894 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (MK_COMB (@lem1971893) (@lem1971892 x y)). Qed.
Lemma lem1971895 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971896 (x : real) (y : real) : (term301 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1971894 x y) (@lem1971895)). Qed.
Lemma lem1971897 (x : real) (y : real) : (term300 x y) = (term311 x y).
Proof. exact (TRANS (@lem1971846 x y) (@lem1971896 x y)). Qed.
Lemma lem1971898 (x : real) (y : real) : (term312 x y) = (term313 x y).
Proof. exact (@lem1483525 (term314 x y) term121). Qed.
Lemma lem1971899 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1971912 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1971913 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1971914 (x : real) (y : real) : (term315 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1971913) (@lem1971912 x y)). Qed.
Lemma lem1971915 (x : real) (y : real) : (term316 x y) = (term306 x y).
Proof. exact (@lem1483512 (term40 x y)). Qed.
Lemma lem1971916 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1971917 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1971919 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1971920 : term67 = term68.
Proof. exact (@lem1971919 term22 term22). Qed.
Lemma lem1971921 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1971922 : term70 = term22.
Proof. exact (EQ_MP (@lem1971921) (@lem940073)). Qed.
Lemma lem1971923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1971924 : term68 = term71.
Proof. exact (MK_COMB (@lem1971923) (@lem1971922)). Qed.
Lemma lem1971925 : term67 = term71.
Proof. exact (TRANS (@lem1971920) (@lem1971924)). Qed.
Lemma lem1971926 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971927 : term72 = term73.
Proof. exact (MK_COMB (@lem1971926) (@lem1971925)). Qed.
Lemma lem1971928 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971929 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1971927) (@lem1971928 y)). Qed.
Lemma lem1971930 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1971917 y) (@lem1971929 y)). Qed.
Lemma lem1971931 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1971932 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1971930 y) (@lem1971931 y)). Qed.
Lemma lem1971935 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971936 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1971935 x) (@lem1971932 y)). Qed.
Lemma lem1971937 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971916 x y) (@lem1971936 x y)). Qed.
Lemma lem1971938 (x : real) (y : real) : (term316 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971915 x y) (@lem1971937 x y)). Qed.
Lemma lem1971939 (x : real) (y : real) : (term315 x y) = (term190 x y).
Proof. exact (TRANS (@lem1971914 x y) (@lem1971938 x y)). Qed.
Lemma lem1971948 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1971949 (x : real) (y : real) : (term317 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem1971948 y) (@lem1971939 x y)). Qed.
Lemma lem1971950 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483484 (term52 x) (term52 y) y). Qed.
Lemma lem1971951 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1971953 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971954 : term122 = term121.
Proof. exact (@lem1971953 term22). Qed.
Lemma lem1971955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971956 : term123 = term124.
Proof. exact (MK_COMB (@lem1971955) (@lem1971954)). Qed.
Lemma lem1971957 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1971958 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1971956) (@lem1971957 y)). Qed.
Lemma lem1971959 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1971951 y) (@lem1971958 y)). Qed.
Lemma lem1971960 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1971961 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1971959 y) (@lem1971960 y)). Qed.
Lemma lem1971962 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1971963 (y : real) (x : real) : (term319 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1971962 x) (@lem1971961 y)). Qed.
Lemma lem1971964 (y : real) (x : real) : (term318 x y) = (term266 x).
Proof. exact (TRANS (@lem1971950 x y) (@lem1971963 y x)). Qed.
Lemma lem1971965 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1971966 (y : real) (x : real) : (term318 x y) = (term52 x).
Proof. exact (TRANS (@lem1971964 y x) (@lem1971965 x)). Qed.
Lemma lem1971967 (y : real) (x : real) : (term317 x y) = (term52 x).
Proof. exact (TRANS (@lem1971949 x y) (@lem1971966 y x)). Qed.
Lemma lem1971970 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1971971 (y : real) (x : real) : (term314 x y) = (term323 x).
Proof. exact (MK_COMB (@lem1971970 x) (@lem1971967 y x)). Qed.
Lemma lem1971972 (x : real) : (term323 x) = (term321 x).
Proof. exact (@lem1483442 term16 x). Qed.
Lemma lem1971974 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1971975 : term122 = term121.
Proof. exact (@lem1971974 term22). Qed.
Lemma lem1971976 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1971977 : term123 = term124.
Proof. exact (MK_COMB (@lem1971976) (@lem1971975)). Qed.
Lemma lem1971978 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1971979 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1971977) (@lem1971978 x)). Qed.
Lemma lem1971980 (x : real) : (term323 x) = (term322 x).
Proof. exact (TRANS (@lem1971972 x) (@lem1971979 x)). Qed.
Lemma lem1971981 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1971982 (x : real) : (term323 x) = term121.
Proof. exact (TRANS (@lem1971980 x) (@lem1971981 x)). Qed.
Lemma lem1971983 (x : real) (y : real) : (term314 x y) = term121.
Proof. exact (TRANS (@lem1971971 y x) (@lem1971982 x)). Qed.
Lemma lem1971984 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1971985 (x : real) (y : real) : (term324 x y) = term302.
Proof. exact (MK_COMB (@lem1971984) (@lem1971983 x y)). Qed.
Lemma lem1971986 (x : real) (y : real) : (term325 x y) = term326.
Proof. exact (MK_COMB (@lem1971985 x y) (@lem1971899)). Qed.
Lemma lem1971987 : term326 = term327.
Proof. exact (@lem1483519 term121 term121). Qed.
Lemma lem1971989 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1971990 : term139 = term121.
Proof. exact (@lem1971989 term22). Qed.
Lemma lem1971991 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1971992 : term327 = term136.
Proof. exact (MK_COMB (@lem1971991) (@lem1971990)). Qed.
Lemma lem1971993 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1971994 : term327 = term121.
Proof. exact (TRANS (@lem1971992) (@lem1971993)). Qed.
Lemma lem1971995 : term326 = term121.
Proof. exact (TRANS (@lem1971987) (@lem1971994)). Qed.
Lemma lem1971996 (x : real) (y : real) : (term325 x y) = term121.
Proof. exact (TRANS (@lem1971986 x y) (@lem1971995)). Qed.
Lemma lem1971997 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1971998 (x : real) (y : real) : (term328 x y) = term143.
Proof. exact (MK_COMB (@lem1971997) (@lem1971996 x y)). Qed.
Lemma lem1971999 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972000 (x : real) (y : real) : (term313 x y) = term145.
Proof. exact (MK_COMB (@lem1971998 x y) (@lem1971999)). Qed.
Lemma lem1972001 (x : real) (y : real) : (term312 x y) = term145.
Proof. exact (TRANS (@lem1971898 x y) (@lem1972000 x y)). Qed.
Lemma lem1972002 (x : real) (y : real) : (term532 x y) = (term533 x y).
Proof. exact (@lem1483525 (term534 x y) term121). Qed.
Lemma lem1972003 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972016 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1972017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972018 (x : real) (y : real) : (term315 x y) = (term316 x y).
Proof. exact (MK_COMB (@lem1972017) (@lem1972016 x y)). Qed.
Lemma lem1972019 (x : real) (y : real) : (term316 x y) = (term306 x y).
Proof. exact (@lem1483512 (term40 x y)). Qed.
Lemma lem1972020 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1972021 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972023 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972024 : term67 = term68.
Proof. exact (@lem1972023 term22 term22). Qed.
Lemma lem1972025 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972026 : term70 = term22.
Proof. exact (EQ_MP (@lem1972025) (@lem940073)). Qed.
Lemma lem1972027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972028 : term68 = term71.
Proof. exact (MK_COMB (@lem1972027) (@lem1972026)). Qed.
Lemma lem1972029 : term67 = term71.
Proof. exact (TRANS (@lem1972024) (@lem1972028)). Qed.
Lemma lem1972030 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972031 : term72 = term73.
Proof. exact (MK_COMB (@lem1972030) (@lem1972029)). Qed.
Lemma lem1972032 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972033 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972031) (@lem1972032 y)). Qed.
Lemma lem1972034 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972021 y) (@lem1972033 y)). Qed.
Lemma lem1972035 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972036 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972034 y) (@lem1972035 y)). Qed.
Lemma lem1972039 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972040 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972039 x) (@lem1972036 y)). Qed.
Lemma lem1972041 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972020 x y) (@lem1972040 x y)). Qed.
Lemma lem1972042 (x : real) (y : real) : (term316 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972019 x y) (@lem1972041 x y)). Qed.
Lemma lem1972043 (x : real) (y : real) : (term315 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972018 x y) (@lem1972042 x y)). Qed.
Lemma lem1972046 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1972047 (x : real) (y : real) : (term535 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem1972046 y) (@lem1972043 x y)). Qed.
Lemma lem1972048 (x : real) (y : real) : (term347 x y) = (term348 x y).
Proof. exact (@lem1483484 (term52 x) y y). Qed.
Lemma lem1972049 (y : real) : (real_add y y) = (term280 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1972050 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1972051 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972052 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972053 : term90 = term23.
Proof. exact (EQ_MP (@lem1972052) (@lem1972051)). Qed.
Lemma lem1972054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972055 : term91 = term17.
Proof. exact (MK_COMB (@lem1972054) (@lem1972053)). Qed.
Lemma lem1972056 : term281 = term17.
Proof. exact (TRANS (@lem1972050) (@lem1972055)). Qed.
Lemma lem1972057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972058 : term282 = term109.
Proof. exact (MK_COMB (@lem1972057) (@lem1972056)). Qed.
Lemma lem1972059 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972060 (y : real) : (term280 y) = (term283 y).
Proof. exact (MK_COMB (@lem1972058) (@lem1972059 y)). Qed.
Lemma lem1972061 (y : real) : (real_add y y) = (term283 y).
Proof. exact (TRANS (@lem1972049 y) (@lem1972060 y)). Qed.
Lemma lem1972062 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972063 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem1972062 x) (@lem1972061 y)). Qed.
Lemma lem1972064 (x : real) (y : real) : (term347 x y) = (term349 x y).
Proof. exact (TRANS (@lem1972048 x y) (@lem1972063 x y)). Qed.
Lemma lem1972065 (x : real) (y : real) : (term535 x y) = (term349 x y).
Proof. exact (TRANS (@lem1972047 x y) (@lem1972064 x y)). Qed.
Lemma lem1972074 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972075 (x : real) (y : real) : (term534 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1972074 x) (@lem1972065 x y)). Qed.
Lemma lem1972076 (x : real) (y : real) : (term351 x y) = (term352 x y).
Proof. exact (@lem1483490 (term52 x) (term52 x) (term283 y)). Qed.
Lemma lem1972077 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1483438 term16 term16 x). Qed.
Lemma lem1972078 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1972079 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972080 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972081 : term90 = term23.
Proof. exact (EQ_MP (@lem1972080) (@lem1972079)). Qed.
Lemma lem1972082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972083 : term91 = term17.
Proof. exact (MK_COMB (@lem1972082) (@lem1972081)). Qed.
Lemma lem1972084 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972085 : term88 = term28.
Proof. exact (MK_COMB (@lem1972084) (@lem1972083)). Qed.
Lemma lem1972086 : term87 = term28.
Proof. exact (TRANS (@lem1972078) (@lem1972085)). Qed.
Lemma lem1972087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972088 : term92 = term30.
Proof. exact (MK_COMB (@lem1972087) (@lem1972086)). Qed.
Lemma lem1972089 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972090 (x : real) : (term275 x) = (term276 x).
Proof. exact (MK_COMB (@lem1972088) (@lem1972089 x)). Qed.
Lemma lem1972091 (x : real) : (term274 x) = (term276 x).
Proof. exact (TRANS (@lem1972077 x) (@lem1972090 x)). Qed.
Lemma lem1972092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972093 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem1972092) (@lem1972091 x)). Qed.
Lemma lem1972094 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1972095 (x : real) (y : real) : (term352 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1972093 x) (@lem1972094 y)). Qed.
Lemma lem1972096 (x : real) (y : real) : (term351 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972076 x y) (@lem1972095 x y)). Qed.
Lemma lem1972097 (x : real) (y : real) : (term534 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972075 x y) (@lem1972096 x y)). Qed.
Lemma lem1972098 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972099 (x : real) (y : real) : (term536 x y) = (term537 x y).
Proof. exact (MK_COMB (@lem1972098) (@lem1972097 x y)). Qed.
Lemma lem1972100 (x : real) (y : real) : (term538 x y) = (term539 x y).
Proof. exact (MK_COMB (@lem1972099 x y) (@lem1972003)). Qed.
Lemma lem1972101 (x : real) (y : real) : (term539 x y) = (term540 x y).
Proof. exact (@lem1483519 (term355 x y) term121). Qed.
Lemma lem1972103 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972104 : term139 = term121.
Proof. exact (@lem1972103 term22). Qed.
Lemma lem1972105 (x : real) (y : real) : (term541 x y) = (term541 x y).
Proof. exact (eq_refl (term541 x y)). Qed.
Lemma lem1972106 (x : real) (y : real) : (term540 x y) = (term542 x y).
Proof. exact (MK_COMB (@lem1972105 x y) (@lem1972104)). Qed.
Lemma lem1972107 (x : real) (y : real) : (term542 x y) = (term355 x y).
Proof. exact (@lem1483450 (term355 x y)). Qed.
Lemma lem1972108 (x : real) (y : real) : (term540 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972106 x y) (@lem1972107 x y)). Qed.
Lemma lem1972109 (x : real) (y : real) : (term539 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972101 x y) (@lem1972108 x y)). Qed.
Lemma lem1972110 (x : real) (y : real) : (term538 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972100 x y) (@lem1972109 x y)). Qed.
Lemma lem1972111 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972112 (x : real) (y : real) : (term543 x y) = (term357 x y).
Proof. exact (MK_COMB (@lem1972111) (@lem1972110 x y)). Qed.
Lemma lem1972113 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972114 (x : real) (y : real) : (term533 x y) = (term359 x y).
Proof. exact (MK_COMB (@lem1972112 x y) (@lem1972113)). Qed.
Lemma lem1972115 (x : real) (y : real) : (term532 x y) = (term359 x y).
Proof. exact (TRANS (@lem1972002 x y) (@lem1972114 x y)). Qed.
Lemma lem1972116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972117 (x : real) (y : real) : (term544 x y) = term545.
Proof. exact (MK_COMB (@lem1972116) (@lem1972001 x y)). Qed.
Lemma lem1972118 (x : real) (y : real) : (term510 x y) = (term546 x y).
Proof. exact (MK_COMB (@lem1972117 x y) (@lem1972115 x y)). Qed.
Lemma lem1972119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972120 (x : real) (y : real) : (term239 x y) = (term330 x y).
Proof. exact (MK_COMB (@lem1972119) (@lem1971897 x y)). Qed.
Lemma lem1972121 (x : real) (y : real) : (term512 x y) = (term547 x y).
Proof. exact (MK_COMB (@lem1972120 x y) (@lem1972118 x y)). Qed.
Lemma lem1972122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1972123 (x : real) (y : real) : (term518 x y) = (term548 x y).
Proof. exact (MK_COMB (@lem1972122) (@lem1971845 x y)). Qed.
Lemma lem1972124 (x : real) (y : real) : (term519 x y) = (term549 x y).
Proof. exact (MK_COMB (@lem1972123 x y) (@lem1972121 x y)). Qed.
Lemma lem1972135 (x : real) (y : real) : (term505 x y) = (term549 x y).
Proof. exact (TRANS (@lem1971642 x y) (@lem1972124 x y)). Qed.
Lemma lem1972136 (x : real) (y : real) : (term476 x y) = (term549 x y).
Proof. exact (TRANS (@lem1971626 x y) (@lem1972135 x y)). Qed.
Lemma lem1972138 (a : real) (x : real) (r : real) : (term550 x a r) = (term481 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1972139 (x : real) (y : real) : (term472 x y) = (term551 x y).
Proof. exact (@lem1972138 (term455 x y) (real_sub x y) term121). Qed.
Lemma lem1972152 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1972155 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1972156 (x : real) (y : real) : (term337 x y) = (term338 x y).
Proof. exact (MK_COMB (@lem1972155) (@lem1972152 x y)). Qed.
Lemma lem1972157 (x : real) (y : real) : (term338 x y) = (term40 x y).
Proof. exact (@lem1483460 (term40 x y)). Qed.
Lemma lem1972158 (x : real) (y : real) : (term337 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972156 x y) (@lem1972157 x y)). Qed.
Lemma lem1972161 (x : real) (y : real) : (term552 x y) = (term552 x y).
Proof. exact (eq_refl (term552 x y)). Qed.
Lemma lem1972162 (x : real) (y : real) : (term553 x y) = (term554 x y).
Proof. exact (MK_COMB (@lem1972161 x y) (@lem1972158 x y)). Qed.
Lemma lem1972163 (x : real) (y : real) : (term554 x y) = (term555 x y).
Proof. exact (@lem1483484 x (term455 x y) (term52 y)). Qed.
Lemma lem1972164 (x : real) (y : real) : (term556 x y) = (term557 x y).
Proof. exact (@lem1483488 (term52 y) (term455 x y)). Qed.
Lemma lem1972165 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1972166 (x : real) (y : real) : (term555 x y) = (term558 x y).
Proof. exact (MK_COMB (@lem1972165 x) (@lem1972164 x y)). Qed.
Lemma lem1972167 (x : real) (y : real) : (term554 x y) = (term558 x y).
Proof. exact (TRANS (@lem1972163 x y) (@lem1972166 x y)). Qed.
Lemma lem1972168 (x : real) (y : real) : (term553 x y) = (term558 x y).
Proof. exact (TRANS (@lem1972162 x y) (@lem1972167 x y)). Qed.
Lemma lem1972169 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972170 (x : real) (y : real) : (term559 x y) = (term560 x y).
Proof. exact (MK_COMB (@lem1972169) (@lem1972168 x y)). Qed.
Lemma lem1972171 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972172 (x : real) (y : real) : (term561 x y) = (term562 x y).
Proof. exact (MK_COMB (@lem1972170 x y) (@lem1972171)). Qed.
Lemma lem1972185 (x : real) (y : real) : (real_sub x y) = (term40 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1972188 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1972189 (x : real) (y : real) : (term345 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem1972188) (@lem1972185 x y)). Qed.
Lemma lem1972190 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483508 x term16 (term52 y)). Qed.
Lemma lem1972191 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972193 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972194 : term67 = term68.
Proof. exact (@lem1972193 term22 term22). Qed.
Lemma lem1972195 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972196 : term70 = term22.
Proof. exact (EQ_MP (@lem1972195) (@lem940073)). Qed.
Lemma lem1972197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972198 : term68 = term71.
Proof. exact (MK_COMB (@lem1972197) (@lem1972196)). Qed.
Lemma lem1972199 : term67 = term71.
Proof. exact (TRANS (@lem1972194) (@lem1972198)). Qed.
Lemma lem1972200 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972201 : term72 = term73.
Proof. exact (MK_COMB (@lem1972200) (@lem1972199)). Qed.
Lemma lem1972202 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972203 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972201) (@lem1972202 y)). Qed.
Lemma lem1972204 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972191 y) (@lem1972203 y)). Qed.
Lemma lem1972205 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972206 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972204 y) (@lem1972205 y)). Qed.
Lemma lem1972209 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972210 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972209 x) (@lem1972206 y)). Qed.
Lemma lem1972211 (x : real) (y : real) : (term306 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972190 x y) (@lem1972210 x y)). Qed.
Lemma lem1972212 (x : real) (y : real) : (term345 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972189 x y) (@lem1972211 x y)). Qed.
Lemma lem1972215 (x : real) (y : real) : (term552 x y) = (term552 x y).
Proof. exact (eq_refl (term552 x y)). Qed.
Lemma lem1972216 (x : real) (y : real) : (term563 x y) = (term564 x y).
Proof. exact (MK_COMB (@lem1972215 x y) (@lem1972212 x y)). Qed.
Lemma lem1972217 (x : real) (y : real) : (term564 x y) = (term565 x y).
Proof. exact (@lem1483484 (term52 x) (term455 x y) y). Qed.
Lemma lem1972218 (x : real) (y : real) : (term566 x y) = (term567 x y).
Proof. exact (@lem1483488 y (term455 x y)). Qed.
Lemma lem1972219 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972220 (x : real) (y : real) : (term565 x y) = (term568 x y).
Proof. exact (MK_COMB (@lem1972219 x) (@lem1972218 x y)). Qed.
Lemma lem1972221 (x : real) (y : real) : (term564 x y) = (term568 x y).
Proof. exact (TRANS (@lem1972217 x y) (@lem1972220 x y)). Qed.
Lemma lem1972222 (x : real) (y : real) : (term563 x y) = (term568 x y).
Proof. exact (TRANS (@lem1972216 x y) (@lem1972221 x y)). Qed.
Lemma lem1972223 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972224 (x : real) (y : real) : (term569 x y) = (term570 x y).
Proof. exact (MK_COMB (@lem1972223) (@lem1972222 x y)). Qed.
Lemma lem1972225 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972226 (x : real) (y : real) : (term571 x y) = (term572 x y).
Proof. exact (MK_COMB (@lem1972224 x y) (@lem1972225)). Qed.
Lemma lem1972227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972228 (x : real) (y : real) : (term573 x y) = (term574 x y).
Proof. exact (MK_COMB (@lem1972227) (@lem1972226 x y)). Qed.
Lemma lem1972229 (x : real) (y : real) : (term551 x y) = (term575 x y).
Proof. exact (MK_COMB (@lem1972228 x y) (@lem1972172 x y)). Qed.
Lemma lem1972230 (x : real) (y : real) : (term472 x y) = (term575 x y).
Proof. exact (TRANS (@lem1972139 x y) (@lem1972229 x y)). Qed.
Lemma lem1972231 (x : real) (y : real) : (term576 x y) = (term575 x y).
Proof. exact (eq_refl (term576 x y)). Qed.
Lemma lem1972232 (x : real) (y : real) : (term575 x y) = (term576 x y).
Proof. exact (SYM (@lem1972231 x y)). Qed.
Lemma lem1972233 (x : real) (y : real) : (term576 x y) = (term577 x y).
Proof. exact (@lem1482981 (term578 x y) (term483 x y)). Qed.
Lemma lem1972234 (x : real) (y : real) : (term575 x y) = (term577 x y).
Proof. exact (TRANS (@lem1972232 x y) (@lem1972233 x y)). Qed.
Lemma lem1972235 (x : real) (y : real) : (term579 x y) = (term580 x y).
Proof. exact (eq_refl (term579 x y)). Qed.
Lemma lem1972236 (x : real) (y : real) : (term581 x y) = (term581 x y).
Proof. exact (eq_refl (term581 x y)). Qed.
Lemma lem1972237 (x : real) (y : real) : (term582 x y) = (term583 x y).
Proof. exact (MK_COMB (@lem1972236 x y) (@lem1972235 x y)). Qed.
Lemma lem1972238 (x : real) (y : real) : (term584 x y) = (term585 x y).
Proof. exact (eq_refl (term584 x y)). Qed.
Lemma lem1972239 (x : real) (y : real) : (term586 x y) = (term586 x y).
Proof. exact (eq_refl (term586 x y)). Qed.
Lemma lem1972240 (x : real) (y : real) : (term587 x y) = (term588 x y).
Proof. exact (MK_COMB (@lem1972239 x y) (@lem1972238 x y)). Qed.
Lemma lem1972241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1972242 (x : real) (y : real) : (term589 x y) = (term590 x y).
Proof. exact (MK_COMB (@lem1972241) (@lem1972240 x y)). Qed.
Lemma lem1972243 (x : real) (y : real) : (term577 x y) = (term591 x y).
Proof. exact (MK_COMB (@lem1972242 x y) (@lem1972237 x y)). Qed.
Lemma lem1972244 (x : real) (y : real) : (term592 x y) = (term592 x y).
Proof. exact (eq_refl (term592 x y)). Qed.
Lemma lem1972245 (x : real) (y : real) : ((term575 x y) = (term577 x y)) = ((term575 x y) = (term591 x y)).
Proof. exact (MK_COMB (@lem1972244 x y) (@lem1972243 x y)). Qed.
Lemma lem1972246 (x : real) (y : real) : (term575 x y) = (term591 x y).
Proof. exact (EQ_MP (@lem1972245 x y) (@lem1972234 x y)). Qed.
Lemma lem1972247 (x : real) (y : real) : (term593 x y) = (term594 x y).
Proof. exact (@lem1483527 (term483 x y) term121). Qed.
Lemma lem1972248 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972255 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972262 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972263 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972264 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972263) (@lem1972262 x)). Qed.
Lemma lem1972265 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972264 x) (@lem1972255 y)). Qed.
Lemma lem1972266 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972267 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972269 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972270 : term67 = term68.
Proof. exact (@lem1972269 term22 term22). Qed.
Lemma lem1972271 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972272 : term70 = term22.
Proof. exact (EQ_MP (@lem1972271) (@lem940073)). Qed.
Lemma lem1972273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972274 : term68 = term71.
Proof. exact (MK_COMB (@lem1972273) (@lem1972272)). Qed.
Lemma lem1972275 : term67 = term71.
Proof. exact (TRANS (@lem1972270) (@lem1972274)). Qed.
Lemma lem1972276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972277 : term72 = term73.
Proof. exact (MK_COMB (@lem1972276) (@lem1972275)). Qed.
Lemma lem1972278 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972279 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972277) (@lem1972278 y)). Qed.
Lemma lem1972280 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972267 y) (@lem1972279 y)). Qed.
Lemma lem1972281 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972282 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972280 y) (@lem1972281 y)). Qed.
Lemma lem1972283 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972286 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972283 x) (@lem1972282 y)). Qed.
Lemma lem1972287 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972266 x y) (@lem1972286 x y)). Qed.
Lemma lem1972288 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972265 x y) (@lem1972287 x y)). Qed.
Lemma lem1972289 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972290 (x : real) (y : real) : (term595 x y) = (term596 x y).
Proof. exact (MK_COMB (@lem1972289) (@lem1972288 x y)). Qed.
Lemma lem1972291 (x : real) (y : real) : (term597 x y) = (term598 x y).
Proof. exact (MK_COMB (@lem1972290 x y) (@lem1972248)). Qed.
Lemma lem1972292 (x : real) (y : real) : (term598 x y) = (term599 x y).
Proof. exact (@lem1483519 (term190 x y) term121). Qed.
Lemma lem1972294 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972295 : term139 = term121.
Proof. exact (@lem1972294 term22). Qed.
Lemma lem1972296 (x : real) (y : real) : (term600 x y) = (term600 x y).
Proof. exact (eq_refl (term600 x y)). Qed.
Lemma lem1972297 (x : real) (y : real) : (term599 x y) = (term601 x y).
Proof. exact (MK_COMB (@lem1972296 x y) (@lem1972295)). Qed.
Lemma lem1972298 (x : real) (y : real) : (term601 x y) = (term190 x y).
Proof. exact (@lem1483450 (term190 x y)). Qed.
Lemma lem1972299 (x : real) (y : real) : (term599 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972297 x y) (@lem1972298 x y)). Qed.
Lemma lem1972300 (x : real) (y : real) : (term598 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972292 x y) (@lem1972299 x y)). Qed.
Lemma lem1972301 (x : real) (y : real) : (term597 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972291 x y) (@lem1972300 x y)). Qed.
Lemma lem1972302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1972303 (x : real) (y : real) : (term602 x y) = (term603 x y).
Proof. exact (MK_COMB (@lem1972302) (@lem1972301 x y)). Qed.
Lemma lem1972304 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972305 (x : real) (y : real) : (term594 x y) = (term604 x y).
Proof. exact (MK_COMB (@lem1972303 x y) (@lem1972304)). Qed.
Lemma lem1972306 (x : real) (y : real) : (term593 x y) = (term604 x y).
Proof. exact (TRANS (@lem1972247 x y) (@lem1972305 x y)). Qed.
Lemma lem1972307 (x : real) (y : real) : (term605 x y) = (term606 x y).
Proof. exact (@lem1483525 (term607 x y) term121). Qed.
Lemma lem1972308 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972315 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972322 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972323 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972324 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972323) (@lem1972322 x)). Qed.
Lemma lem1972325 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972324 x) (@lem1972315 y)). Qed.
Lemma lem1972326 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972327 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972329 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972330 : term67 = term68.
Proof. exact (@lem1972329 term22 term22). Qed.
Lemma lem1972331 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972332 : term70 = term22.
Proof. exact (EQ_MP (@lem1972331) (@lem940073)). Qed.
Lemma lem1972333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972334 : term68 = term71.
Proof. exact (MK_COMB (@lem1972333) (@lem1972332)). Qed.
Lemma lem1972335 : term67 = term71.
Proof. exact (TRANS (@lem1972330) (@lem1972334)). Qed.
Lemma lem1972336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972337 : term72 = term73.
Proof. exact (MK_COMB (@lem1972336) (@lem1972335)). Qed.
Lemma lem1972338 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972339 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972337) (@lem1972338 y)). Qed.
Lemma lem1972340 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972327 y) (@lem1972339 y)). Qed.
Lemma lem1972341 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972342 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972340 y) (@lem1972341 y)). Qed.
Lemma lem1972343 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972346 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972343 x) (@lem1972342 y)). Qed.
Lemma lem1972347 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972326 x y) (@lem1972346 x y)). Qed.
Lemma lem1972348 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972325 x y) (@lem1972347 x y)). Qed.
Lemma lem1972351 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1972352 (x : real) (y : real) : (term608 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem1972351 y) (@lem1972348 x y)). Qed.
Lemma lem1972353 (x : real) (y : real) : (term347 x y) = (term348 x y).
Proof. exact (@lem1483484 (term52 x) y y). Qed.
Lemma lem1972354 (y : real) : (real_add y y) = (term280 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1972355 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1972356 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972357 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972358 : term90 = term23.
Proof. exact (EQ_MP (@lem1972357) (@lem1972356)). Qed.
Lemma lem1972359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972360 : term91 = term17.
Proof. exact (MK_COMB (@lem1972359) (@lem1972358)). Qed.
Lemma lem1972361 : term281 = term17.
Proof. exact (TRANS (@lem1972355) (@lem1972360)). Qed.
Lemma lem1972362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972363 : term282 = term109.
Proof. exact (MK_COMB (@lem1972362) (@lem1972361)). Qed.
Lemma lem1972364 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972365 (y : real) : (term280 y) = (term283 y).
Proof. exact (MK_COMB (@lem1972363) (@lem1972364 y)). Qed.
Lemma lem1972366 (y : real) : (real_add y y) = (term283 y).
Proof. exact (TRANS (@lem1972354 y) (@lem1972365 y)). Qed.
Lemma lem1972367 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972368 (x : real) (y : real) : (term348 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem1972367 x) (@lem1972366 y)). Qed.
Lemma lem1972369 (x : real) (y : real) : (term347 x y) = (term349 x y).
Proof. exact (TRANS (@lem1972353 x y) (@lem1972368 x y)). Qed.
Lemma lem1972370 (x : real) (y : real) : (term608 x y) = (term349 x y).
Proof. exact (TRANS (@lem1972352 x y) (@lem1972369 x y)). Qed.
Lemma lem1972379 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972380 (x : real) (y : real) : (term607 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1972379 x) (@lem1972370 x y)). Qed.
Lemma lem1972381 (x : real) (y : real) : (term351 x y) = (term352 x y).
Proof. exact (@lem1483490 (term52 x) (term52 x) (term283 y)). Qed.
Lemma lem1972382 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1483438 term16 term16 x). Qed.
Lemma lem1972383 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1972384 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972385 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972386 : term90 = term23.
Proof. exact (EQ_MP (@lem1972385) (@lem1972384)). Qed.
Lemma lem1972387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972388 : term91 = term17.
Proof. exact (MK_COMB (@lem1972387) (@lem1972386)). Qed.
Lemma lem1972389 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972390 : term88 = term28.
Proof. exact (MK_COMB (@lem1972389) (@lem1972388)). Qed.
Lemma lem1972391 : term87 = term28.
Proof. exact (TRANS (@lem1972383) (@lem1972390)). Qed.
Lemma lem1972392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972393 : term92 = term30.
Proof. exact (MK_COMB (@lem1972392) (@lem1972391)). Qed.
Lemma lem1972394 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972395 (x : real) : (term275 x) = (term276 x).
Proof. exact (MK_COMB (@lem1972393) (@lem1972394 x)). Qed.
Lemma lem1972396 (x : real) : (term274 x) = (term276 x).
Proof. exact (TRANS (@lem1972382 x) (@lem1972395 x)). Qed.
Lemma lem1972397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972398 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem1972397) (@lem1972396 x)). Qed.
Lemma lem1972399 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1972400 (x : real) (y : real) : (term352 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1972398 x) (@lem1972399 y)). Qed.
Lemma lem1972401 (x : real) (y : real) : (term351 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972381 x y) (@lem1972400 x y)). Qed.
Lemma lem1972402 (x : real) (y : real) : (term607 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972380 x y) (@lem1972401 x y)). Qed.
Lemma lem1972403 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972404 (x : real) (y : real) : (term609 x y) = (term537 x y).
Proof. exact (MK_COMB (@lem1972403) (@lem1972402 x y)). Qed.
Lemma lem1972405 (x : real) (y : real) : (term610 x y) = (term539 x y).
Proof. exact (MK_COMB (@lem1972404 x y) (@lem1972308)). Qed.
Lemma lem1972406 (x : real) (y : real) : (term539 x y) = (term540 x y).
Proof. exact (@lem1483519 (term355 x y) term121). Qed.
Lemma lem1972408 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972409 : term139 = term121.
Proof. exact (@lem1972408 term22). Qed.
Lemma lem1972410 (x : real) (y : real) : (term541 x y) = (term541 x y).
Proof. exact (eq_refl (term541 x y)). Qed.
Lemma lem1972411 (x : real) (y : real) : (term540 x y) = (term542 x y).
Proof. exact (MK_COMB (@lem1972410 x y) (@lem1972409)). Qed.
Lemma lem1972412 (x : real) (y : real) : (term542 x y) = (term355 x y).
Proof. exact (@lem1483450 (term355 x y)). Qed.
Lemma lem1972413 (x : real) (y : real) : (term540 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972411 x y) (@lem1972412 x y)). Qed.
Lemma lem1972414 (x : real) (y : real) : (term539 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972406 x y) (@lem1972413 x y)). Qed.
Lemma lem1972415 (x : real) (y : real) : (term610 x y) = (term355 x y).
Proof. exact (TRANS (@lem1972405 x y) (@lem1972414 x y)). Qed.
Lemma lem1972416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972417 (x : real) (y : real) : (term611 x y) = (term357 x y).
Proof. exact (MK_COMB (@lem1972416) (@lem1972415 x y)). Qed.
Lemma lem1972418 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972419 (x : real) (y : real) : (term606 x y) = (term359 x y).
Proof. exact (MK_COMB (@lem1972417 x y) (@lem1972418)). Qed.
Lemma lem1972420 (x : real) (y : real) : (term605 x y) = (term359 x y).
Proof. exact (TRANS (@lem1972307 x y) (@lem1972419 x y)). Qed.
Lemma lem1972421 (x : real) (y : real) : (term612 x y) = (term613 x y).
Proof. exact (@lem1483525 (term614 x y) term121). Qed.
Lemma lem1972422 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972429 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972436 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972437 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972438 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972437) (@lem1972436 x)). Qed.
Lemma lem1972439 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972438 x) (@lem1972429 y)). Qed.
Lemma lem1972440 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972441 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972443 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972444 : term67 = term68.
Proof. exact (@lem1972443 term22 term22). Qed.
Lemma lem1972445 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972446 : term70 = term22.
Proof. exact (EQ_MP (@lem1972445) (@lem940073)). Qed.
Lemma lem1972447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972448 : term68 = term71.
Proof. exact (MK_COMB (@lem1972447) (@lem1972446)). Qed.
Lemma lem1972449 : term67 = term71.
Proof. exact (TRANS (@lem1972444) (@lem1972448)). Qed.
Lemma lem1972450 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972451 : term72 = term73.
Proof. exact (MK_COMB (@lem1972450) (@lem1972449)). Qed.
Lemma lem1972452 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972453 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972451) (@lem1972452 y)). Qed.
Lemma lem1972454 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972441 y) (@lem1972453 y)). Qed.
Lemma lem1972455 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972456 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972454 y) (@lem1972455 y)). Qed.
Lemma lem1972457 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972460 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972457 x) (@lem1972456 y)). Qed.
Lemma lem1972461 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972440 x y) (@lem1972460 x y)). Qed.
Lemma lem1972462 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972439 x y) (@lem1972461 x y)). Qed.
Lemma lem1972471 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1972472 (x : real) (y : real) : (term615 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem1972471 y) (@lem1972462 x y)). Qed.
Lemma lem1972473 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483484 (term52 x) (term52 y) y). Qed.
Lemma lem1972474 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1972476 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1972477 : term122 = term121.
Proof. exact (@lem1972476 term22). Qed.
Lemma lem1972478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972479 : term123 = term124.
Proof. exact (MK_COMB (@lem1972478) (@lem1972477)). Qed.
Lemma lem1972480 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972481 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1972479) (@lem1972480 y)). Qed.
Lemma lem1972482 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1972474 y) (@lem1972481 y)). Qed.
Lemma lem1972483 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1972484 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1972482 y) (@lem1972483 y)). Qed.
Lemma lem1972485 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972486 (y : real) (x : real) : (term319 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1972485 x) (@lem1972484 y)). Qed.
Lemma lem1972487 (y : real) (x : real) : (term318 x y) = (term266 x).
Proof. exact (TRANS (@lem1972473 x y) (@lem1972486 y x)). Qed.
Lemma lem1972488 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1972489 (y : real) (x : real) : (term318 x y) = (term52 x).
Proof. exact (TRANS (@lem1972487 y x) (@lem1972488 x)). Qed.
Lemma lem1972490 (y : real) (x : real) : (term615 x y) = (term52 x).
Proof. exact (TRANS (@lem1972472 x y) (@lem1972489 y x)). Qed.
Lemma lem1972493 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1972494 (y : real) (x : real) : (term614 x y) = (term323 x).
Proof. exact (MK_COMB (@lem1972493 x) (@lem1972490 y x)). Qed.
Lemma lem1972495 (x : real) : (term323 x) = (term321 x).
Proof. exact (@lem1483442 term16 x). Qed.
Lemma lem1972497 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1972498 : term122 = term121.
Proof. exact (@lem1972497 term22). Qed.
Lemma lem1972499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972500 : term123 = term124.
Proof. exact (MK_COMB (@lem1972499) (@lem1972498)). Qed.
Lemma lem1972501 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972502 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1972500) (@lem1972501 x)). Qed.
Lemma lem1972503 (x : real) : (term323 x) = (term322 x).
Proof. exact (TRANS (@lem1972495 x) (@lem1972502 x)). Qed.
Lemma lem1972504 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1972505 (x : real) : (term323 x) = term121.
Proof. exact (TRANS (@lem1972503 x) (@lem1972504 x)). Qed.
Lemma lem1972506 (x : real) (y : real) : (term614 x y) = term121.
Proof. exact (TRANS (@lem1972494 y x) (@lem1972505 x)). Qed.
Lemma lem1972507 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972508 (x : real) (y : real) : (term616 x y) = term302.
Proof. exact (MK_COMB (@lem1972507) (@lem1972506 x y)). Qed.
Lemma lem1972509 (x : real) (y : real) : (term617 x y) = term326.
Proof. exact (MK_COMB (@lem1972508 x y) (@lem1972422)). Qed.
Lemma lem1972510 : term326 = term327.
Proof. exact (@lem1483519 term121 term121). Qed.
Lemma lem1972512 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972513 : term139 = term121.
Proof. exact (@lem1972512 term22). Qed.
Lemma lem1972514 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1972515 : term327 = term136.
Proof. exact (MK_COMB (@lem1972514) (@lem1972513)). Qed.
Lemma lem1972516 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1972517 : term327 = term121.
Proof. exact (TRANS (@lem1972515) (@lem1972516)). Qed.
Lemma lem1972518 : term326 = term121.
Proof. exact (TRANS (@lem1972510) (@lem1972517)). Qed.
Lemma lem1972519 (x : real) (y : real) : (term617 x y) = term121.
Proof. exact (TRANS (@lem1972509 x y) (@lem1972518)). Qed.
Lemma lem1972520 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972521 (x : real) (y : real) : (term618 x y) = term143.
Proof. exact (MK_COMB (@lem1972520) (@lem1972519 x y)). Qed.
Lemma lem1972522 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972523 (x : real) (y : real) : (term613 x y) = term145.
Proof. exact (MK_COMB (@lem1972521 x y) (@lem1972522)). Qed.
Lemma lem1972524 (x : real) (y : real) : (term612 x y) = term145.
Proof. exact (TRANS (@lem1972421 x y) (@lem1972523 x y)). Qed.
Lemma lem1972525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972526 (x : real) (y : real) : (term619 x y) = (term361 x y).
Proof. exact (MK_COMB (@lem1972525) (@lem1972420 x y)). Qed.
Lemma lem1972527 (x : real) (y : real) : (term585 x y) = (term362 x y).
Proof. exact (MK_COMB (@lem1972526 x y) (@lem1972524 x y)). Qed.
Lemma lem1972528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972529 (x : real) (y : real) : (term586 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1972528) (@lem1972306 x y)). Qed.
Lemma lem1972530 (x : real) (y : real) : (term588 x y) = (term621 x y).
Proof. exact (MK_COMB (@lem1972529 x y) (@lem1972527 x y)). Qed.
Lemma lem1972531 (x : real) (y : real) : (term622 x y) = (term623 x y).
Proof. exact (@lem1483525 term121 (term483 x y)). Qed.
Lemma lem1972538 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972545 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972546 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972547 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972546) (@lem1972545 x)). Qed.
Lemma lem1972548 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972547 x) (@lem1972538 y)). Qed.
Lemma lem1972549 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972550 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972552 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972553 : term67 = term68.
Proof. exact (@lem1972552 term22 term22). Qed.
Lemma lem1972554 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972555 : term70 = term22.
Proof. exact (EQ_MP (@lem1972554) (@lem940073)). Qed.
Lemma lem1972556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972557 : term68 = term71.
Proof. exact (MK_COMB (@lem1972556) (@lem1972555)). Qed.
Lemma lem1972558 : term67 = term71.
Proof. exact (TRANS (@lem1972553) (@lem1972557)). Qed.
Lemma lem1972559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972560 : term72 = term73.
Proof. exact (MK_COMB (@lem1972559) (@lem1972558)). Qed.
Lemma lem1972561 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972562 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972560) (@lem1972561 y)). Qed.
Lemma lem1972563 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972550 y) (@lem1972562 y)). Qed.
Lemma lem1972564 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972565 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972563 y) (@lem1972564 y)). Qed.
Lemma lem1972566 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972569 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972566 x) (@lem1972565 y)). Qed.
Lemma lem1972570 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972549 x y) (@lem1972569 x y)). Qed.
Lemma lem1972571 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972548 x y) (@lem1972570 x y)). Qed.
Lemma lem1972574 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1972575 (x : real) (y : real) : (term624 x y) = (term625 x y).
Proof. exact (MK_COMB (@lem1972574) (@lem1972571 x y)). Qed.
Lemma lem1972576 (x : real) (y : real) : (term625 x y) = (term626 x y).
Proof. exact (@lem1483519 term121 (term190 x y)). Qed.
Lemma lem1972577 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483508 (term52 x) term16 y). Qed.
Lemma lem1972578 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1972579 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1972581 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972582 : term67 = term68.
Proof. exact (@lem1972581 term22 term22). Qed.
Lemma lem1972583 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972584 : term70 = term22.
Proof. exact (EQ_MP (@lem1972583) (@lem940073)). Qed.
Lemma lem1972585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972586 : term68 = term71.
Proof. exact (MK_COMB (@lem1972585) (@lem1972584)). Qed.
Lemma lem1972587 : term67 = term71.
Proof. exact (TRANS (@lem1972582) (@lem1972586)). Qed.
Lemma lem1972588 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972589 : term72 = term73.
Proof. exact (MK_COMB (@lem1972588) (@lem1972587)). Qed.
Lemma lem1972590 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972591 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1972589) (@lem1972590 x)). Qed.
Lemma lem1972592 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1972579 x) (@lem1972591 x)). Qed.
Lemma lem1972593 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1972594 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1972592 x) (@lem1972593 x)). Qed.
Lemma lem1972595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972596 (x : real) : (term200 x) = (real_add x).
Proof. exact (MK_COMB (@lem1972595) (@lem1972594 x)). Qed.
Lemma lem1972597 (x : real) (y : real) : (term196 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1972596 x) (@lem1972578 y)). Qed.
Lemma lem1972598 (x : real) (y : real) : (term195 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972577 x y) (@lem1972597 x y)). Qed.
Lemma lem1972599 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1972600 (x : real) (y : real) : (term626 x y) = (term627 x y).
Proof. exact (MK_COMB (@lem1972599) (@lem1972598 x y)). Qed.
Lemma lem1972601 (x : real) (y : real) : (term627 x y) = (term40 x y).
Proof. exact (@lem1483448 (term40 x y)). Qed.
Lemma lem1972602 (x : real) (y : real) : (term626 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972600 x y) (@lem1972601 x y)). Qed.
Lemma lem1972603 (x : real) (y : real) : (term625 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972576 x y) (@lem1972602 x y)). Qed.
Lemma lem1972604 (x : real) (y : real) : (term624 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972575 x y) (@lem1972603 x y)). Qed.
Lemma lem1972605 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972606 (x : real) (y : real) : (term628 x y) = (term629 x y).
Proof. exact (MK_COMB (@lem1972605) (@lem1972604 x y)). Qed.
Lemma lem1972607 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972608 (x : real) (y : real) : (term623 x y) = (term630 x y).
Proof. exact (MK_COMB (@lem1972606 x y) (@lem1972607)). Qed.
Lemma lem1972609 (x : real) (y : real) : (term622 x y) = (term630 x y).
Proof. exact (TRANS (@lem1972531 x y) (@lem1972608 x y)). Qed.
Lemma lem1972610 (x : real) (y : real) : (term631 x y) = (term632 x y).
Proof. exact (@lem1483525 (term633 x y) term121). Qed.
Lemma lem1972611 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972618 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972625 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972626 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972627 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972626) (@lem1972625 x)). Qed.
Lemma lem1972628 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972627 x) (@lem1972618 y)). Qed.
Lemma lem1972629 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972630 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972632 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972633 : term67 = term68.
Proof. exact (@lem1972632 term22 term22). Qed.
Lemma lem1972634 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972635 : term70 = term22.
Proof. exact (EQ_MP (@lem1972634) (@lem940073)). Qed.
Lemma lem1972636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972637 : term68 = term71.
Proof. exact (MK_COMB (@lem1972636) (@lem1972635)). Qed.
Lemma lem1972638 : term67 = term71.
Proof. exact (TRANS (@lem1972633) (@lem1972637)). Qed.
Lemma lem1972639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972640 : term72 = term73.
Proof. exact (MK_COMB (@lem1972639) (@lem1972638)). Qed.
Lemma lem1972641 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972642 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972640) (@lem1972641 y)). Qed.
Lemma lem1972643 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972630 y) (@lem1972642 y)). Qed.
Lemma lem1972644 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972645 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972643 y) (@lem1972644 y)). Qed.
Lemma lem1972646 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972649 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972646 x) (@lem1972645 y)). Qed.
Lemma lem1972650 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972629 x y) (@lem1972649 x y)). Qed.
Lemma lem1972651 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972628 x y) (@lem1972650 x y)). Qed.
Lemma lem1972652 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972653 (x : real) (y : real) : (term634 x y) = (term635 x y).
Proof. exact (MK_COMB (@lem1972652) (@lem1972651 x y)). Qed.
Lemma lem1972654 (x : real) (y : real) : (term635 x y) = (term195 x y).
Proof. exact (@lem1483512 (term190 x y)). Qed.
Lemma lem1972655 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483508 (term52 x) term16 y). Qed.
Lemma lem1972656 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1972657 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1972659 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972660 : term67 = term68.
Proof. exact (@lem1972659 term22 term22). Qed.
Lemma lem1972661 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972662 : term70 = term22.
Proof. exact (EQ_MP (@lem1972661) (@lem940073)). Qed.
Lemma lem1972663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972664 : term68 = term71.
Proof. exact (MK_COMB (@lem1972663) (@lem1972662)). Qed.
Lemma lem1972665 : term67 = term71.
Proof. exact (TRANS (@lem1972660) (@lem1972664)). Qed.
Lemma lem1972666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972667 : term72 = term73.
Proof. exact (MK_COMB (@lem1972666) (@lem1972665)). Qed.
Lemma lem1972668 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972669 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1972667) (@lem1972668 x)). Qed.
Lemma lem1972670 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1972657 x) (@lem1972669 x)). Qed.
Lemma lem1972671 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1972672 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1972670 x) (@lem1972671 x)). Qed.
Lemma lem1972673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972674 (x : real) : (term200 x) = (real_add x).
Proof. exact (MK_COMB (@lem1972673) (@lem1972672 x)). Qed.
Lemma lem1972675 (x : real) (y : real) : (term196 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1972674 x) (@lem1972656 y)). Qed.
Lemma lem1972676 (x : real) (y : real) : (term195 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972655 x y) (@lem1972675 x y)). Qed.
Lemma lem1972677 (x : real) (y : real) : (term635 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972654 x y) (@lem1972676 x y)). Qed.
Lemma lem1972678 (x : real) (y : real) : (term634 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972653 x y) (@lem1972677 x y)). Qed.
Lemma lem1972681 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1972682 (x : real) (y : real) : (term636 x y) = (term340 x y).
Proof. exact (MK_COMB (@lem1972681 y) (@lem1972678 x y)). Qed.
Lemma lem1972683 (x : real) (y : real) : (term340 x y) = (term341 x y).
Proof. exact (@lem1483484 x y (term52 y)). Qed.
Lemma lem1972684 (y : real) : (term323 y) = (term321 y).
Proof. exact (@lem1483442 term16 y). Qed.
Lemma lem1972686 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1972687 : term122 = term121.
Proof. exact (@lem1972686 term22). Qed.
Lemma lem1972688 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972689 : term123 = term124.
Proof. exact (MK_COMB (@lem1972688) (@lem1972687)). Qed.
Lemma lem1972690 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972691 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1972689) (@lem1972690 y)). Qed.
Lemma lem1972692 (y : real) : (term323 y) = (term322 y).
Proof. exact (TRANS (@lem1972684 y) (@lem1972691 y)). Qed.
Lemma lem1972693 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1972694 (y : real) : (term323 y) = term121.
Proof. exact (TRANS (@lem1972692 y) (@lem1972693 y)). Qed.
Lemma lem1972695 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1972696 (y : real) (x : real) : (term341 x y) = (term182 x).
Proof. exact (MK_COMB (@lem1972695 x) (@lem1972694 y)). Qed.
Lemma lem1972697 (y : real) (x : real) : (term340 x y) = (term182 x).
Proof. exact (TRANS (@lem1972683 x y) (@lem1972696 y x)). Qed.
Lemma lem1972698 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1972699 (y : real) (x : real) : (term340 x y) = x.
Proof. exact (TRANS (@lem1972697 y x) (@lem1972698 x)). Qed.
Lemma lem1972700 (y : real) (x : real) : (term636 x y) = x.
Proof. exact (TRANS (@lem1972682 x y) (@lem1972699 y x)). Qed.
Lemma lem1972709 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972710 (y : real) (x : real) : (term633 x y) = (term320 x).
Proof. exact (MK_COMB (@lem1972709 x) (@lem1972700 y x)). Qed.
Lemma lem1972711 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1972713 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1972714 : term122 = term121.
Proof. exact (@lem1972713 term22). Qed.
Lemma lem1972715 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972716 : term123 = term124.
Proof. exact (MK_COMB (@lem1972715) (@lem1972714)). Qed.
Lemma lem1972717 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972718 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1972716) (@lem1972717 x)). Qed.
Lemma lem1972719 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1972711 x) (@lem1972718 x)). Qed.
Lemma lem1972720 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1972721 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1972719 x) (@lem1972720 x)). Qed.
Lemma lem1972722 (x : real) (y : real) : (term633 x y) = term121.
Proof. exact (TRANS (@lem1972710 y x) (@lem1972721 x)). Qed.
Lemma lem1972723 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972724 (x : real) (y : real) : (term637 x y) = term302.
Proof. exact (MK_COMB (@lem1972723) (@lem1972722 x y)). Qed.
Lemma lem1972725 (x : real) (y : real) : (term638 x y) = term326.
Proof. exact (MK_COMB (@lem1972724 x y) (@lem1972611)). Qed.
Lemma lem1972726 : term326 = term327.
Proof. exact (@lem1483519 term121 term121). Qed.
Lemma lem1972728 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972729 : term139 = term121.
Proof. exact (@lem1972728 term22). Qed.
Lemma lem1972730 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1972731 : term327 = term136.
Proof. exact (MK_COMB (@lem1972730) (@lem1972729)). Qed.
Lemma lem1972732 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1972733 : term327 = term121.
Proof. exact (TRANS (@lem1972731) (@lem1972732)). Qed.
Lemma lem1972734 : term326 = term121.
Proof. exact (TRANS (@lem1972726) (@lem1972733)). Qed.
Lemma lem1972735 (x : real) (y : real) : (term638 x y) = term121.
Proof. exact (TRANS (@lem1972725 x y) (@lem1972734)). Qed.
Lemma lem1972736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972737 (x : real) (y : real) : (term639 x y) = term143.
Proof. exact (MK_COMB (@lem1972736) (@lem1972735 x y)). Qed.
Lemma lem1972738 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972739 (x : real) (y : real) : (term632 x y) = term145.
Proof. exact (MK_COMB (@lem1972737 x y) (@lem1972738)). Qed.
Lemma lem1972740 (x : real) (y : real) : (term631 x y) = term145.
Proof. exact (TRANS (@lem1972610 x y) (@lem1972739 x y)). Qed.
Lemma lem1972741 (x : real) (y : real) : (term640 x y) = (term641 x y).
Proof. exact (@lem1483525 (term642 x y) term121). Qed.
Lemma lem1972742 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972749 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1972756 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1972757 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972758 (x : real) : (term484 x) = (term485 x).
Proof. exact (MK_COMB (@lem1972757) (@lem1972756 x)). Qed.
Lemma lem1972759 (x : real) (y : real) : (term483 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1972758 x) (@lem1972749 y)). Qed.
Lemma lem1972760 (x : real) (y : real) : (term486 x y) = (term307 x y).
Proof. exact (@lem1483519 (term52 x) (term52 y)). Qed.
Lemma lem1972761 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1972763 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972764 : term67 = term68.
Proof. exact (@lem1972763 term22 term22). Qed.
Lemma lem1972765 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972766 : term70 = term22.
Proof. exact (EQ_MP (@lem1972765) (@lem940073)). Qed.
Lemma lem1972767 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972768 : term68 = term71.
Proof. exact (MK_COMB (@lem1972767) (@lem1972766)). Qed.
Lemma lem1972769 : term67 = term71.
Proof. exact (TRANS (@lem1972764) (@lem1972768)). Qed.
Lemma lem1972770 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972771 : term72 = term73.
Proof. exact (MK_COMB (@lem1972770) (@lem1972769)). Qed.
Lemma lem1972772 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972773 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1972771) (@lem1972772 y)). Qed.
Lemma lem1972774 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1972761 y) (@lem1972773 y)). Qed.
Lemma lem1972775 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1972776 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1972774 y) (@lem1972775 y)). Qed.
Lemma lem1972777 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1972780 (x : real) (y : real) : (term307 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1972777 x) (@lem1972776 y)). Qed.
Lemma lem1972781 (x : real) (y : real) : (term486 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972760 x y) (@lem1972780 x y)). Qed.
Lemma lem1972782 (x : real) (y : real) : (term483 x y) = (term190 x y).
Proof. exact (TRANS (@lem1972759 x y) (@lem1972781 x y)). Qed.
Lemma lem1972783 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972784 (x : real) (y : real) : (term634 x y) = (term635 x y).
Proof. exact (MK_COMB (@lem1972783) (@lem1972782 x y)). Qed.
Lemma lem1972785 (x : real) (y : real) : (term635 x y) = (term195 x y).
Proof. exact (@lem1483512 (term190 x y)). Qed.
Lemma lem1972786 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483508 (term52 x) term16 y). Qed.
Lemma lem1972787 (y : real) : (term52 y) = (term52 y).
Proof. exact (eq_refl (term52 y)). Qed.
Lemma lem1972788 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1972790 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1972791 : term67 = term68.
Proof. exact (@lem1972790 term22 term22). Qed.
Lemma lem1972792 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1972793 : term70 = term22.
Proof. exact (EQ_MP (@lem1972792) (@lem940073)). Qed.
Lemma lem1972794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972795 : term68 = term71.
Proof. exact (MK_COMB (@lem1972794) (@lem1972793)). Qed.
Lemma lem1972796 : term67 = term71.
Proof. exact (TRANS (@lem1972791) (@lem1972795)). Qed.
Lemma lem1972797 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972798 : term72 = term73.
Proof. exact (MK_COMB (@lem1972797) (@lem1972796)). Qed.
Lemma lem1972799 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972800 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1972798) (@lem1972799 x)). Qed.
Lemma lem1972801 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1972788 x) (@lem1972800 x)). Qed.
Lemma lem1972802 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1972803 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1972801 x) (@lem1972802 x)). Qed.
Lemma lem1972804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972805 (x : real) : (term200 x) = (real_add x).
Proof. exact (MK_COMB (@lem1972804) (@lem1972803 x)). Qed.
Lemma lem1972806 (x : real) (y : real) : (term196 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1972805 x) (@lem1972787 y)). Qed.
Lemma lem1972807 (x : real) (y : real) : (term195 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972786 x y) (@lem1972806 x y)). Qed.
Lemma lem1972808 (x : real) (y : real) : (term635 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972785 x y) (@lem1972807 x y)). Qed.
Lemma lem1972809 (x : real) (y : real) : (term634 x y) = (term40 x y).
Proof. exact (TRANS (@lem1972784 x y) (@lem1972808 x y)). Qed.
Lemma lem1972818 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1972819 (x : real) (y : real) : (term643 x y) = (term272 x y).
Proof. exact (MK_COMB (@lem1972818 y) (@lem1972809 x y)). Qed.
Lemma lem1972820 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483484 x (term52 y) (term52 y)). Qed.
Lemma lem1972821 (y : real) : (term274 y) = (term275 y).
Proof. exact (@lem1483438 term16 term16 y). Qed.
Lemma lem1972822 : term87 = term88.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem1972823 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972824 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972825 : term90 = term23.
Proof. exact (EQ_MP (@lem1972824) (@lem1972823)). Qed.
Lemma lem1972826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972827 : term91 = term17.
Proof. exact (MK_COMB (@lem1972826) (@lem1972825)). Qed.
Lemma lem1972828 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1972829 : term88 = term28.
Proof. exact (MK_COMB (@lem1972828) (@lem1972827)). Qed.
Lemma lem1972830 : term87 = term28.
Proof. exact (TRANS (@lem1972822) (@lem1972829)). Qed.
Lemma lem1972831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972832 : term92 = term30.
Proof. exact (MK_COMB (@lem1972831) (@lem1972830)). Qed.
Lemma lem1972833 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1972834 (y : real) : (term275 y) = (term276 y).
Proof. exact (MK_COMB (@lem1972832) (@lem1972833 y)). Qed.
Lemma lem1972835 (y : real) : (term274 y) = (term276 y).
Proof. exact (TRANS (@lem1972821 y) (@lem1972834 y)). Qed.
Lemma lem1972836 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1972837 (x : real) (y : real) : (term273 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1972836 x) (@lem1972835 y)). Qed.
Lemma lem1972838 (x : real) (y : real) : (term272 x y) = (term277 x y).
Proof. exact (TRANS (@lem1972820 x y) (@lem1972837 x y)). Qed.
Lemma lem1972839 (x : real) (y : real) : (term643 x y) = (term277 x y).
Proof. exact (TRANS (@lem1972819 x y) (@lem1972838 x y)). Qed.
Lemma lem1972842 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1972843 (x : real) (y : real) : (term642 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1972842 x) (@lem1972839 x y)). Qed.
Lemma lem1972844 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (@lem1483490 x x (term276 y)). Qed.
Lemma lem1972845 (x : real) : (real_add x x) = (term280 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1972846 : term281 = term91.
Proof. exact (@lem1367770 term22 term22). Qed.
Lemma lem1972847 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1972848 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1972849 : term90 = term23.
Proof. exact (EQ_MP (@lem1972848) (@lem1972847)). Qed.
Lemma lem1972850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1972851 : term91 = term17.
Proof. exact (MK_COMB (@lem1972850) (@lem1972849)). Qed.
Lemma lem1972852 : term281 = term17.
Proof. exact (TRANS (@lem1972846) (@lem1972851)). Qed.
Lemma lem1972853 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1972854 : term282 = term109.
Proof. exact (MK_COMB (@lem1972853) (@lem1972852)). Qed.
Lemma lem1972855 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1972856 (x : real) : (term280 x) = (term283 x).
Proof. exact (MK_COMB (@lem1972854) (@lem1972855 x)). Qed.
Lemma lem1972857 (x : real) : (real_add x x) = (term283 x).
Proof. exact (TRANS (@lem1972845 x) (@lem1972856 x)). Qed.
Lemma lem1972858 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1972859 (x : real) : (term284 x) = (term285 x).
Proof. exact (MK_COMB (@lem1972858) (@lem1972857 x)). Qed.
Lemma lem1972860 (y : real) : (term276 y) = (term276 y).
Proof. exact (eq_refl (term276 y)). Qed.
Lemma lem1972861 (x : real) (y : real) : (term279 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1972859 x) (@lem1972860 y)). Qed.
Lemma lem1972862 (x : real) (y : real) : (term278 x y) = (term286 x y).
Proof. exact (TRANS (@lem1972844 x y) (@lem1972861 x y)). Qed.
Lemma lem1972863 (x : real) (y : real) : (term642 x y) = (term286 x y).
Proof. exact (TRANS (@lem1972843 x y) (@lem1972862 x y)). Qed.
Lemma lem1972864 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1972865 (x : real) (y : real) : (term644 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem1972864) (@lem1972863 x y)). Qed.
Lemma lem1972866 (x : real) (y : real) : (term645 x y) = (term290 x y).
Proof. exact (MK_COMB (@lem1972865 x y) (@lem1972742)). Qed.
Lemma lem1972867 (x : real) (y : real) : (term290 x y) = (term291 x y).
Proof. exact (@lem1483519 (term286 x y) term121). Qed.
Lemma lem1972869 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1972870 : term139 = term121.
Proof. exact (@lem1972869 term22). Qed.
Lemma lem1972871 (x : real) (y : real) : (term292 x y) = (term292 x y).
Proof. exact (eq_refl (term292 x y)). Qed.
Lemma lem1972872 (x : real) (y : real) : (term291 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1972871 x y) (@lem1972870)). Qed.
Lemma lem1972873 (x : real) (y : real) : (term293 x y) = (term286 x y).
Proof. exact (@lem1483450 (term286 x y)). Qed.
Lemma lem1972874 (x : real) (y : real) : (term291 x y) = (term286 x y).
Proof. exact (TRANS (@lem1972872 x y) (@lem1972873 x y)). Qed.
Lemma lem1972875 (x : real) (y : real) : (term290 x y) = (term286 x y).
Proof. exact (TRANS (@lem1972867 x y) (@lem1972874 x y)). Qed.
Lemma lem1972876 (x : real) (y : real) : (term645 x y) = (term286 x y).
Proof. exact (TRANS (@lem1972866 x y) (@lem1972875 x y)). Qed.
Lemma lem1972877 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1972878 (x : real) (y : real) : (term646 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1972877) (@lem1972876 x y)). Qed.
Lemma lem1972879 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1972880 (x : real) (y : real) : (term641 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1972878 x y) (@lem1972879)). Qed.
Lemma lem1972881 (x : real) (y : real) : (term640 x y) = (term296 x y).
Proof. exact (TRANS (@lem1972741 x y) (@lem1972880 x y)). Qed.
Lemma lem1972882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972883 (x : real) (y : real) : (term647 x y) = term545.
Proof. exact (MK_COMB (@lem1972882) (@lem1972740 x y)). Qed.
Lemma lem1972884 (x : real) (y : real) : (term580 x y) = (term648 x y).
Proof. exact (MK_COMB (@lem1972883 x y) (@lem1972881 x y)). Qed.
Lemma lem1972885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1972886 (x : real) (y : real) : (term581 x y) = (term649 x y).
Proof. exact (MK_COMB (@lem1972885) (@lem1972609 x y)). Qed.
Lemma lem1972887 (x : real) (y : real) : (term583 x y) = (term650 x y).
Proof. exact (MK_COMB (@lem1972886 x y) (@lem1972884 x y)). Qed.
Lemma lem1972888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1972889 (x : real) (y : real) : (term590 x y) = (term651 x y).
Proof. exact (MK_COMB (@lem1972888) (@lem1972530 x y)). Qed.
Lemma lem1972890 (x : real) (y : real) : (term591 x y) = (term652 x y).
Proof. exact (MK_COMB (@lem1972889 x y) (@lem1972887 x y)). Qed.
Lemma lem1972901 (x : real) (y : real) : (term575 x y) = (term652 x y).
Proof. exact (TRANS (@lem1972246 x y) (@lem1972890 x y)). Qed.
Lemma lem1972902 (x : real) (y : real) : (term472 x y) = (term652 x y).
Proof. exact (TRANS (@lem1972230 x y) (@lem1972901 x y)). Qed.
Lemma lem1972903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1972904 (x : real) (y : real) : (term478 x y) = (term653 x y).
Proof. exact (MK_COMB (@lem1972903) (@lem1972136 x y)). Qed.
Lemma lem1972905 (x : real) (y : real) : (term479 x y) = (term654 x y).
Proof. exact (MK_COMB (@lem1972904 x y) (@lem1972902 x y)). Qed.
Lemma lem1972906 (x : real) (y : real) (h1 : term654 x y) : term654 x y.
Proof. exact (h1). Qed.
Lemma lem1972907 (x : real) (y : real) (h1 : term549 x y) : term549 x y.
Proof. exact (h1). Qed.
Lemma lem1972908 (x : real) (y : real) (h1 : term531 x y) : term531 x y.
Proof. exact (h1). Qed.
Lemma lem1972909 (x : real) (y : real) (h1 : term531 x y) : term530 x y.
Proof. exact (proj2 (@lem1972908 x y h1)). Qed.
Lemma lem1972911 (x : real) (y : real) (h1 : term531 x y) : term145.
Proof. exact (proj2 (@lem1972909 x y h1)). Qed.
Lemma lem1972914 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1972915 : term145 = term152.
Proof. exact (@lem1972914 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1972916 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1972917 : term145 = False.
Proof. exact (TRANS (@lem1972915) (@lem1972916)). Qed.
Lemma lem1972918 (x : real) (y : real) (h1 : term531 x y) : False.
Proof. exact (EQ_MP (@lem1972917) (@lem1972911 x y h1)). Qed.
Lemma lem1972919 (x : real) (y : real) (h1 : term547 x y) : term547 x y.
Proof. exact (h1). Qed.
Lemma lem1972920 (x : real) (y : real) (h1 : term547 x y) : term546 x y.
Proof. exact (proj2 (@lem1972919 x y h1)). Qed.
Lemma lem1972923 (x : real) (y : real) (h1 : term547 x y) : term145.
Proof. exact (proj1 (@lem1972920 x y h1)). Qed.
Lemma lem1972925 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1972926 : term145 = term152.
Proof. exact (@lem1972925 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1972927 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1972928 : term145 = False.
Proof. exact (TRANS (@lem1972926) (@lem1972927)). Qed.
Lemma lem1972929 (x : real) (y : real) (h1 : term547 x y) : False.
Proof. exact (EQ_MP (@lem1972928) (@lem1972923 x y h1)). Qed.
Lemma lem1972930 (x : real) (y : real) (h1 : term549 x y) : False.
Proof. exact (or_elim (@lem1972907 x y h1) (fun h0 : term531 x y => @lem1972918 x y h0) (fun h0 : term547 x y => @lem1972929 x y h0)). Qed.
Lemma lem1972931 (x : real) (y : real) (h1 : term652 x y) : term652 x y.
Proof. exact (h1). Qed.
Lemma lem1972932 (x : real) (y : real) (h1 : term621 x y) : term621 x y.
Proof. exact (h1). Qed.
Lemma lem1972933 (x : real) (y : real) (h1 : term621 x y) : term362 x y.
Proof. exact (proj2 (@lem1972932 x y h1)). Qed.
Lemma lem1972935 (x : real) (y : real) (h1 : term621 x y) : term145.
Proof. exact (proj2 (@lem1972933 x y h1)). Qed.
Lemma lem1972938 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1972939 : term145 = term152.
Proof. exact (@lem1972938 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1972940 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1972941 : term145 = False.
Proof. exact (TRANS (@lem1972939) (@lem1972940)). Qed.
Lemma lem1972942 (x : real) (y : real) (h1 : term621 x y) : False.
Proof. exact (EQ_MP (@lem1972941) (@lem1972935 x y h1)). Qed.
Lemma lem1972943 (x : real) (y : real) (h1 : term650 x y) : term650 x y.
Proof. exact (h1). Qed.
Lemma lem1972944 (x : real) (y : real) (h1 : term650 x y) : term648 x y.
Proof. exact (proj2 (@lem1972943 x y h1)). Qed.
Lemma lem1972947 (x : real) (y : real) (h1 : term650 x y) : term145.
Proof. exact (proj1 (@lem1972944 x y h1)). Qed.
Lemma lem1972949 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1972950 : term145 = term152.
Proof. exact (@lem1972949 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1972951 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1972952 : term145 = False.
Proof. exact (TRANS (@lem1972950) (@lem1972951)). Qed.
Lemma lem1972953 (x : real) (y : real) (h1 : term650 x y) : False.
Proof. exact (EQ_MP (@lem1972952) (@lem1972947 x y h1)). Qed.
Lemma lem1972954 (x : real) (y : real) (h1 : term652 x y) : False.
Proof. exact (or_elim (@lem1972931 x y h1) (fun h0 : term621 x y => @lem1972942 x y h0) (fun h0 : term650 x y => @lem1972953 x y h0)). Qed.
Lemma lem1972955 (x : real) (y : real) (h1 : term654 x y) : False.
Proof. exact (or_elim (@lem1972906 x y h1) (fun h0 : term549 x y => @lem1972930 x y h0) (fun h0 : term652 x y => @lem1972954 x y h0)). Qed.
Lemma lem1972956 (x : real) (y : real) (h1 : term479 x y) : term479 x y.
Proof. exact (h1). Qed.
Lemma lem1972957 (x : real) (y : real) (h1 : term479 x y) : term654 x y.
Proof. exact (EQ_MP (@lem1972905 x y) (@lem1972956 x y h1)). Qed.
Lemma lem1972958 (x : real) (y : real) (h1 : term479 x y) : (term654 x y) = False.
Proof. exact (prop_ext (fun h2 : term654 x y => @lem1972955 x y h2) (fun h2 : False => @lem1972957 x y h1)). Qed.
Lemma lem1972959 (x : real) (y : real) (h1 : term479 x y) : False.
Proof. exact (EQ_MP (@lem1972958 x y h1) (@lem1972957 x y h1)). Qed.
Lemma lem1972960 (x : real) (y : real) (h1 : term453 x y) : term453 x y.
Proof. exact (h1). Qed.
Lemma lem1972961 (x : real) (y : real) (h1 : term453 x y) : term479 x y.
Proof. exact (EQ_MP (@lem1971478 x y) (@lem1972960 x y h1)). Qed.
Lemma lem1972962 (x : real) (y : real) (h1 : term453 x y) : (term479 x y) = False.
Proof. exact (prop_ext (fun h2 : term479 x y => @lem1972959 x y h2) (fun h2 : False => @lem1972961 x y h1)). Qed.
Lemma lem1972963 (x : real) (y : real) (h1 : term453 x y) : False.
Proof. exact (EQ_MP (@lem1972962 x y h1) (@lem1972961 x y h1)). Qed.
Lemma lem1972964 (x : real) (y : real) : term655 x y.
Proof. exact (fun h0 : term453 x y => @lem1972963 x y h0). Qed.
Lemma lem1972965 (x : real) (y : real) : term656 x y.
Proof. exact (@lem1386578 ((term170 x y) = (term455 x y))). Qed.
Lemma lem1972967 (y : real) : term657 y.
Proof. exact (@lem9784 (term178 y)). Qed.
Lemma lem1972968 (y : real) : (term657 y) = (term658 y).
Proof. exact (eq_refl (term657 y)). Qed.
Lemma lem1972969 (y : real) : term658 y.
Proof. exact (EQ_MP (@lem1972968 y) (@lem1972967 y)). Qed.
Lemma lem1972970 (y : real) (h1 : term178 y) : term178 y.
Proof. exact (h1). Qed.
Lemma lem1972971 (y : real) (h1 : term171 y) : term171 y.
Proof. exact (h1). Qed.
Lemma lem1972972 (h1 : term401) : term401.
Proof. exact (h1). Qed.
Lemma lem1972973 (x : real) (h1 : term401) : term402 x.
Proof. exact (@lem1972972 h1 x). Qed.
Lemma lem1972974 (x : real) : (term402 x) = (term403 x).
Proof. exact (eq_refl (term402 x)). Qed.
Lemma lem1972975 (x : real) (h1 : term401) : term403 x.
Proof. exact (EQ_MP (@lem1972974 x) (@lem1972973 x h1)). Qed.
Lemma lem1972976 (x : real) (y : real) (h1 : term401) : term404 x y.
Proof. exact (@lem1972975 x h1 y). Qed.
Lemma lem1972977 (x : real) (y : real) : (term404 x y) = (term405 x y).
Proof. exact (eq_refl (term404 x y)). Qed.
Lemma lem1972978 (x : real) (y : real) (h1 : term401) : term405 x y.
Proof. exact (EQ_MP (@lem1972977 x y) (@lem1972976 x y h1)). Qed.
Lemma lem1972979 (x : real) (y : real) (h1 : term406 x y) : term406 x y.
Proof. exact (h1). Qed.
Lemma lem1972980 (x : real) (y : real) (h1 : term401) (h2 : term406 x y) : term407 x y.
Proof. exact (@lem1972978 x y h1 (@lem1972979 x y h2)). Qed.
Lemma lem1972981 (x : real) (y : real) (h1 : term406 x y) : term408 x y.
Proof. exact (fun h0 : term401 => @lem1972980 x y h0 h1). Qed.
Lemma lem1972982 (h1 : term401) : term401.
Proof. exact (h1). Qed.
Lemma lem1972983 (x : real) (y : real) (h1 : term401) (h2 : term406 x y) : term407 x y.
Proof. exact (@lem1972981 x y h2 (@lem1972982 h1)). Qed.
Lemma lem1972984 (x : real) (y : real) (h1 : term401) : term405 x y.
Proof. exact (fun h0 : term406 x y => @lem1972983 x y h1 h0). Qed.
Lemma lem1972985 (x : real) (h1 : term401) : term403 x.
Proof. exact (fun y : real => @lem1972984 x y h1). Qed.
Lemma lem1972986 (h1 : term401) : term401.
Proof. exact (fun x : real => @lem1972985 x h1). Qed.
Lemma lem1972987 : term409.
Proof. exact (fun h0 : term401 => @lem1972986 h0). Qed.
Lemma lem1972988 : term401.
Proof. exact (@lem1972987 (@lem1969849)). Qed.
Lemma lem1972989 (x : real) : term402 x.
Proof. exact (@lem1972988 x). Qed.
Lemma lem1972990 (x : real) : (term402 x) = (term403 x).
Proof. exact (eq_refl (term402 x)). Qed.
Lemma lem1972991 (x : real) : term403 x.
Proof. exact (EQ_MP (@lem1972990 x) (@lem1972989 x)). Qed.
Lemma lem1972992 (x : real) (y : real) : term404 x y.
Proof. exact (@lem1972991 x y). Qed.
Lemma lem1972993 (x : real) (y : real) : (term404 x y) = (term405 x y).
Proof. exact (eq_refl (term404 x y)). Qed.
Lemma lem1973004 (x : real) : (term410 x) = (term411 x).
Proof. exact (@lem1483533 (real_abs x) (term412 x)). Qed.
Lemma lem1973016 (x : real) : (term413 x) = (term414 x).
Proof. exact (@lem1483519 (real_abs x) (term412 x)). Qed.
Lemma lem1973017 (x : real) : (term415 x) = (term416 x).
Proof. exact (@lem1483476 term16 term17 (real_abs x)). Qed.
Lemma lem1973019 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1973020 : term20 = term21.
Proof. exact (@lem1973019 term22 term23). Qed.
Lemma lem1973021 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1973022 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1973023 : term26 = term23.
Proof. exact (EQ_MP (@lem1973022) (@lem1973021)). Qed.
Lemma lem1973024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1973025 : term27 = term17.
Proof. exact (MK_COMB (@lem1973024) (@lem1973023)). Qed.
Lemma lem1973026 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1973027 : term21 = term28.
Proof. exact (MK_COMB (@lem1973026) (@lem1973025)). Qed.
Lemma lem1973028 : term20 = term28.
Proof. exact (TRANS (@lem1973020) (@lem1973027)). Qed.
Lemma lem1973029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973030 : term29 = term30.
Proof. exact (MK_COMB (@lem1973029) (@lem1973028)). Qed.
Lemma lem1973031 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1973032 (x : real) : (term416 x) = (term417 x).
Proof. exact (MK_COMB (@lem1973030) (@lem1973031 x)). Qed.
Lemma lem1973033 (x : real) : (term415 x) = (term417 x).
Proof. exact (TRANS (@lem1973017 x) (@lem1973032 x)). Qed.
Lemma lem1973034 (x : real) : (term418 x) = (term418 x).
Proof. exact (eq_refl (term418 x)). Qed.
Lemma lem1973035 (x : real) : (term414 x) = (term419 x).
Proof. exact (MK_COMB (@lem1973034 x) (@lem1973033 x)). Qed.
Lemma lem1973036 (x : real) : (term419 x) = (term420 x).
Proof. exact (@lem1483442 term28 (real_abs x)). Qed.
Lemma lem1973039 : term421 = term16.
Proof. exact (@lem1367767 term22 term22). Qed.
Lemma lem1973040 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1973041 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1973042 : term90 = term23.
Proof. exact (EQ_MP (@lem1973041) (@lem1973040)). Qed.
Lemma lem1973043 : term23 = term90.
Proof. exact (SYM (@lem1973042)). Qed.
Lemma lem1973044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1973045 : term17 = term91.
Proof. exact (MK_COMB (@lem1973044) (@lem1973043)). Qed.
Lemma lem1973046 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1973047 : term28 = term88.
Proof. exact (MK_COMB (@lem1973046) (@lem1973045)). Qed.
Lemma lem1973048 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1973049 : term422 = term423.
Proof. exact (MK_COMB (@lem1973048) (@lem1973047)). Qed.
Lemma lem1973050 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem1973051 : term424 = term421.
Proof. exact (MK_COMB (@lem1973049) (@lem1973050)). Qed.
Lemma lem1973052 : term424 = term16.
Proof. exact (TRANS (@lem1973051) (@lem1973039)). Qed.
Lemma lem1973053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973054 : term425 = term77.
Proof. exact (MK_COMB (@lem1973053) (@lem1973052)). Qed.
Lemma lem1973055 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1973056 (x : real) : (term420 x) = (term426 x).
Proof. exact (MK_COMB (@lem1973054) (@lem1973055 x)). Qed.
Lemma lem1973057 (x : real) : (term419 x) = (term426 x).
Proof. exact (TRANS (@lem1973036 x) (@lem1973056 x)). Qed.
Lemma lem1973058 (x : real) : (term414 x) = (term426 x).
Proof. exact (TRANS (@lem1973035 x) (@lem1973057 x)). Qed.
Lemma lem1973060 (x : real) : (term413 x) = (term426 x).
Proof. exact (TRANS (@lem1973016 x) (@lem1973058 x)). Qed.
Lemma lem1973061 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973062 (x : real) : (term427 x) = (term428 x).
Proof. exact (MK_COMB (@lem1973061) (@lem1973060 x)). Qed.
Lemma lem1973063 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973064 (x : real) : (term411 x) = (term429 x).
Proof. exact (MK_COMB (@lem1973062 x) (@lem1973063)). Qed.
Lemma lem1973074 (x : real) : (term410 x) = (term429 x).
Proof. exact (TRANS (@lem1973004 x) (@lem1973064 x)). Qed.
Lemma lem1973076 (x : real) (r : real) : (term430 x r) = (term431 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1973077 (x : real) : (term429 x) = (term432 x).
Proof. exact (@lem1973076 x term121). Qed.
Lemma lem1973084 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1973085 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973086 (x : real) : (term433 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1973085) (@lem1973084 x)). Qed.
Lemma lem1973087 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973088 (x : real) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem1973086 x) (@lem1973087)). Qed.
Lemma lem1973101 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1973102 (x : real) : (term432 x) = (term436 x).
Proof. exact (MK_COMB (@lem1973101 x) (@lem1973088 x)). Qed.
Lemma lem1973105 (x : real) : (term429 x) = (term436 x).
Proof. exact (TRANS (@lem1973077 x) (@lem1973102 x)). Qed.
Lemma lem1973106 (x : real) (h1 : term436 x) : term436 x.
Proof. exact (h1). Qed.
Lemma lem1973107 (x : real) (h1 : term436 x) : term435 x.
Proof. exact (proj2 (@lem1973106 x h1)). Qed.
Lemma lem1973108 (x : real) (h1 : term436 x) : term177 x.
Proof. exact (proj1 (@lem1973106 x h1)). Qed.
Lemma lem1973110 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973111 : term368 = term369.
Proof. exact (@lem1973110 (NUMERAL 0) term22). Qed.
Lemma lem1973112 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973113 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973114 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973113 h1) (fun h1 : term369 = True => @lem1973112)). Qed.
Lemma lem1973115 : term369 = True.
Proof. exact (EQ_MP (@lem1973114) (@lem1973112)). Qed.
Lemma lem1973116 : term368 = True.
Proof. exact (TRANS (@lem1973111) (@lem1973115)). Qed.
Lemma lem1973117 : True = term368.
Proof. exact (SYM (@lem1973116)). Qed.
Lemma lem1973118 : term368.
Proof. exact (EQ_MP (@lem1973117) (@lem0)). Qed.
Lemma lem1973119 (x : real) (h1 : term436 x) : term437 x.
Proof. exact (conj (@lem1973118) (@lem1973107 x h1)). Qed.
Lemma lem1973121 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1973122 (x : real) : term438 x.
Proof. exact (@lem1973121 term71 x). Qed.
Lemma lem1973123 (x : real) (h1 : term436 x) : term434 x.
Proof. exact (@lem1973122 x (@lem1973119 x h1)). Qed.
Lemma lem1973124 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1973125 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973126 (x : real) : (term433 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1973125) (@lem1973124 x)). Qed.
Lemma lem1973127 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973128 (x : real) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem1973126 x) (@lem1973127)). Qed.
Lemma lem1973129 (x : real) (h1 : term436 x) : term435 x.
Proof. exact (EQ_MP (@lem1973128 x) (@lem1973123 x h1)). Qed.
Lemma lem1973131 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973132 : term368 = term369.
Proof. exact (@lem1973131 (NUMERAL 0) term22). Qed.
Lemma lem1973133 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973134 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973135 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973134 h1) (fun h1 : term369 = True => @lem1973133)). Qed.
Lemma lem1973136 : term369 = True.
Proof. exact (EQ_MP (@lem1973135) (@lem1973133)). Qed.
Lemma lem1973137 : term368 = True.
Proof. exact (TRANS (@lem1973132) (@lem1973136)). Qed.
Lemma lem1973138 : True = term368.
Proof. exact (SYM (@lem1973137)). Qed.
Lemma lem1973139 : term368.
Proof. exact (EQ_MP (@lem1973138) (@lem0)). Qed.
Lemma lem1973140 (x : real) (h1 : term436 x) : term380 x.
Proof. exact (conj (@lem1973139) (@lem1973108 x h1)). Qed.
Lemma lem1973142 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1973143 (x : real) : term382 x.
Proof. exact (@lem1973142 term71 (term52 x)). Qed.
Lemma lem1973144 (x : real) (h1 : term436 x) : term383 x.
Proof. exact (@lem1973143 x (@lem1973140 x h1)). Qed.
Lemma lem1973145 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1973146 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973147 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1973146) (@lem1973145 x)). Qed.
Lemma lem1973148 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973149 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1973147 x) (@lem1973148)). Qed.
Lemma lem1973150 (x : real) (h1 : term436 x) : term177 x.
Proof. exact (EQ_MP (@lem1973149 x) (@lem1973144 x h1)). Qed.
Lemma lem1973151 (x : real) (h1 : term436 x) : term436 x.
Proof. exact (conj (@lem1973150 x h1) (@lem1973129 x h1)). Qed.
Lemma lem1973153 (x : real) (y : real) : term439 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1973154 (x : real) : term440 x.
Proof. exact (@lem1973153 (term52 x) x). Qed.
Lemma lem1973155 (x : real) (h1 : term436 x) : term396 x.
Proof. exact (@lem1973154 x (@lem1973151 x h1)). Qed.
Lemma lem1973156 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1973158 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1973159 : term122 = term121.
Proof. exact (@lem1973158 term22). Qed.
Lemma lem1973160 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973161 : term123 = term124.
Proof. exact (MK_COMB (@lem1973160) (@lem1973159)). Qed.
Lemma lem1973162 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1973163 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1973161) (@lem1973162 x)). Qed.
Lemma lem1973164 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1973156 x) (@lem1973163 x)). Qed.
Lemma lem1973165 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1973166 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1973164 x) (@lem1973165 x)). Qed.
Lemma lem1973167 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973168 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1973167) (@lem1973166 x)). Qed.
Lemma lem1973169 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973170 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1973168 x) (@lem1973169)). Qed.
Lemma lem1973171 (x : real) (h1 : term436 x) : term145.
Proof. exact (EQ_MP (@lem1973170 x) (@lem1973155 x h1)). Qed.
Lemma lem1973173 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973174 : term145 = term152.
Proof. exact (@lem1973173 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1973175 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1973176 : term145 = False.
Proof. exact (TRANS (@lem1973174) (@lem1973175)). Qed.
Lemma lem1973177 (x : real) (h1 : term436 x) : False.
Proof. exact (EQ_MP (@lem1973176) (@lem1973171 x h1)). Qed.
Lemma lem1973178 (x : real) (h1 : term429 x) : term429 x.
Proof. exact (h1). Qed.
Lemma lem1973179 (x : real) (h1 : term429 x) : term436 x.
Proof. exact (EQ_MP (@lem1973105 x) (@lem1973178 x h1)). Qed.
Lemma lem1973180 (x : real) (h1 : term429 x) : (term436 x) = False.
Proof. exact (prop_ext (fun h2 : term436 x => @lem1973177 x h2) (fun h2 : False => @lem1973179 x h1)). Qed.
Lemma lem1973181 (x : real) (h1 : term429 x) : False.
Proof. exact (EQ_MP (@lem1973180 x h1) (@lem1973179 x h1)). Qed.
Lemma lem1973182 (x : real) (h1 : term410 x) : term410 x.
Proof. exact (h1). Qed.
Lemma lem1973183 (x : real) (h1 : term410 x) : term429 x.
Proof. exact (EQ_MP (@lem1973074 x) (@lem1973182 x h1)). Qed.
Lemma lem1973184 (x : real) (h1 : term410 x) : (term429 x) = False.
Proof. exact (prop_ext (fun h2 : term429 x => @lem1973181 x h2) (fun h2 : False => @lem1973183 x h1)). Qed.
Lemma lem1973185 (x : real) (h1 : term410 x) : False.
Proof. exact (EQ_MP (@lem1973184 x h1) (@lem1973183 x h1)). Qed.
Lemma lem1973186 (x : real) : term441 x.
Proof. exact (fun h0 : term410 x => @lem1973185 x h0). Qed.
Lemma lem1973187 (x : real) : term442 x.
Proof. exact (@lem1386578 (term443 x)). Qed.
Lemma lem1973188 (x : real) : term443 x.
Proof. exact (@lem1973187 x (@lem1973186 x)). Qed.
Lemma lem1973189 (x : real) : (term443 x) = ((term443 x) = True).
Proof. exact (@lem7 (term443 x)). Qed.
Lemma lem1973191 (x : real) : term444 x.
Proof. exact (@lem1954889 x). Qed.
Lemma lem1973192 (x : real) : (term444 x) = (term445 x).
Proof. exact (eq_refl (term444 x)). Qed.
Lemma lem1973193 (x : real) : term445 x.
Proof. exact (EQ_MP (@lem1973192 x) (@lem1973191 x)). Qed.
Lemma lem1973194 (x : real) (y : real) : term446 x y.
Proof. exact (@lem1973193 x y). Qed.
Lemma lem1973195 (x : real) (y : real) : (term446 x y) = ((term447 x y) = (real_le x y)).
Proof. exact (eq_refl (term446 x y)). Qed.
Lemma lem1973197 (x : real) : term657 x.
Proof. exact (@lem9784 (term178 x)). Qed.
Lemma lem1973198 (x : real) : (term657 x) = (term658 x).
Proof. exact (eq_refl (term657 x)). Qed.
Lemma lem1973199 (x : real) : term658 x.
Proof. exact (EQ_MP (@lem1973198 x) (@lem1973197 x)). Qed.
Lemma lem1973200 (x : real) (h1 : term178 x) : term178 x.
Proof. exact (h1). Qed.
Lemma lem1973201 (x : real) (h1 : term171 x) : term171 x.
Proof. exact (h1). Qed.
Lemma lem1973202 (x : real) : term659 x.
Proof. exact (@lem1533617 x). Qed.
Lemma lem1973203 (x : real) : (term659 x) = (term660 x).
Proof. exact (eq_refl (term659 x)). Qed.
Lemma lem1973204 (x : real) : term660 x.
Proof. exact (EQ_MP (@lem1973203 x) (@lem1973202 x)). Qed.
Lemma lem1973205 (x : real) (y : real) : term661 x y.
Proof. exact (@lem1973204 x y). Qed.
Lemma lem1973206 (y : real) (x : real) : (term661 x y) = ((term170 x y) = (term170 y x)).
Proof. exact (eq_refl (term661 x y)). Qed.
Lemma lem1973208 (P : type1626) (h1 : term662 P) : term662 P.
Proof. exact (h1). Qed.
Lemma lem1973209 (P : type1626) (h1 : term663 P) : term663 P.
Proof. exact (h1). Qed.
Lemma lem1973210 (P : type1626) (h1 : term663 P) (h2 : term662 P) : term664 P.
Proof. exact (@lem1973208 P h2 (@lem1973209 P h1)). Qed.
Lemma lem1973211 (P : type1626) (h1 : term663 P) : term665 P.
Proof. exact (fun h0 : term662 P => @lem1973210 P h1 h0). Qed.
Lemma lem1973212 (P : type1626) (h1 : term662 P) : term662 P.
Proof. exact (h1). Qed.
Lemma lem1973213 (P : type1626) (h1 : term663 P) (h2 : term662 P) : term664 P.
Proof. exact (@lem1973211 P h1 (@lem1973212 P h2)). Qed.
Lemma lem1973214 (P : type1626) (h1 : term662 P) : term662 P.
Proof. exact (fun h0 : term663 P => @lem1973213 P h0 h1). Qed.
Lemma lem1973215 (P : type1626) : term666 P.
Proof. exact (fun h0 : term662 P => @lem1973214 P h0). Qed.
Lemma lem1973218 (P : type1626) : term662 P.
Proof. exact (@lem1973215 P (@lem1864819 P)). Qed.
Lemma lem1973219 : term667.
Proof. exact (@lem1973218 term668). Qed.
Lemma lem1973220 (x : real) : (term669 x) = (term670 x).
Proof. exact (eq_refl (term669 x)). Qed.
Lemma lem1973221 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1973222 (x : real) (y : real) : (term671 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem1973220 x) (@lem1973221 y)). Qed.
Lemma lem1973223 (x : real) (y : real) : (term672 x y) = (term673 x y).
Proof. exact (eq_refl (term672 x y)). Qed.
Lemma lem1973224 (x : real) (y : real) : (term671 x y) = (term673 x y).
Proof. exact (TRANS (@lem1973222 x y) (@lem1973223 x y)). Qed.
Lemma lem1973225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1973226 (x : real) (y : real) : (term674 x y) = (term675 x y).
Proof. exact (MK_COMB (@lem1973225) (@lem1973224 x y)). Qed.
Lemma lem1973227 (y : real) : (term669 y) = (term670 y).
Proof. exact (eq_refl (term669 y)). Qed.
Lemma lem1973228 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1973229 (y : real) (x : real) : (term671 y x) = (term672 y x).
Proof. exact (MK_COMB (@lem1973227 y) (@lem1973228 x)). Qed.
Lemma lem1973230 (y : real) (x : real) : (term672 y x) = (term673 y x).
Proof. exact (eq_refl (term672 y x)). Qed.
Lemma lem1973231 (y : real) (x : real) : (term671 y x) = (term673 y x).
Proof. exact (TRANS (@lem1973229 y x) (@lem1973230 y x)). Qed.
Lemma lem1973232 (y : real) (x : real) : ((term671 x y) = (term671 y x)) = ((term673 x y) = (term673 y x)).
Proof. exact (MK_COMB (@lem1973226 x y) (@lem1973231 y x)). Qed.
Lemma lem1973233 (x : real) : (term676 x) = (term677 x).
Proof. exact (fun_ext (fun y : real => @lem1973232 y x)). Qed.
Lemma lem1973234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973235 (x : real) : (term678 x) = (term679 x).
Proof. exact (MK_COMB (@lem1973234) (@lem1973233 x)). Qed.
Lemma lem1973236 : term680 = term681.
Proof. exact (fun_ext (fun x : real => @lem1973235 x)). Qed.
Lemma lem1973237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973238 : term682 = term683.
Proof. exact (MK_COMB (@lem1973237) (@lem1973236)). Qed.
Lemma lem1973239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1973240 : term684 = term685.
Proof. exact (MK_COMB (@lem1973239) (@lem1973238)). Qed.
Lemma lem1973241 (x : real) : (term669 x) = (term670 x).
Proof. exact (eq_refl (term669 x)). Qed.
Lemma lem1973242 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1973243 (x : real) (y : real) : (term671 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem1973241 x) (@lem1973242 y)). Qed.
Lemma lem1973244 (x : real) (y : real) : (term672 x y) = (term673 x y).
Proof. exact (eq_refl (term672 x y)). Qed.
Lemma lem1973245 (x : real) (y : real) : (term671 x y) = (term673 x y).
Proof. exact (TRANS (@lem1973243 x y) (@lem1973244 x y)). Qed.
Lemma lem1973246 (x : real) (y : real) : (term686 x y) = (term686 x y).
Proof. exact (eq_refl (term686 x y)). Qed.
Lemma lem1973247 (x : real) (y : real) : (term687 x y) = (term688 x y).
Proof. exact (MK_COMB (@lem1973246 x y) (@lem1973245 x y)). Qed.
Lemma lem1973248 (x : real) : (term689 x) = (term690 x).
Proof. exact (fun_ext (fun y : real => @lem1973247 x y)). Qed.
Lemma lem1973249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973250 (x : real) : (term691 x) = (term692 x).
Proof. exact (MK_COMB (@lem1973249) (@lem1973248 x)). Qed.
Lemma lem1973251 : term693 = term694.
Proof. exact (fun_ext (fun x : real => @lem1973250 x)). Qed.
Lemma lem1973252 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973253 : term695 = term696.
Proof. exact (MK_COMB (@lem1973252) (@lem1973251)). Qed.
Lemma lem1973254 : term697 = term698.
Proof. exact (MK_COMB (@lem1973240) (@lem1973253)). Qed.
Lemma lem1973255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1973256 : term699 = term700.
Proof. exact (MK_COMB (@lem1973255) (@lem1973254)). Qed.
Lemma lem1973257 (x : real) : (term669 x) = (term670 x).
Proof. exact (eq_refl (term669 x)). Qed.
Lemma lem1973258 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1973259 (x : real) (y : real) : (term671 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem1973257 x) (@lem1973258 y)). Qed.
Lemma lem1973260 (x : real) (y : real) : (term672 x y) = (term673 x y).
Proof. exact (eq_refl (term672 x y)). Qed.
Lemma lem1973261 (x : real) (y : real) : (term671 x y) = (term673 x y).
Proof. exact (TRANS (@lem1973259 x y) (@lem1973260 x y)). Qed.
Lemma lem1973262 (x : real) : (term701 x) = (term670 x).
Proof. exact (fun_ext (fun y : real => @lem1973261 x y)). Qed.
Lemma lem1973263 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973264 (x : real) : (term702 x) = (term703 x).
Proof. exact (MK_COMB (@lem1973263) (@lem1973262 x)). Qed.
Lemma lem1973265 : term704 = term705.
Proof. exact (fun_ext (fun x : real => @lem1973264 x)). Qed.
Lemma lem1973266 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973267 : term706 = term707.
Proof. exact (MK_COMB (@lem1973266) (@lem1973265)). Qed.
Lemma lem1973268 : term667 = term708.
Proof. exact (MK_COMB (@lem1973256) (@lem1973267)). Qed.
Lemma lem1973269 : term708.
Proof. exact (EQ_MP (@lem1973268) (@lem1973219)). Qed.
Lemma lem1973286 (y : real) (x : real) : (term170 x y) = (term170 y x).
Proof. exact (EQ_MP (@lem1973206 y x) (@lem1973205 x y)). Qed.
Lemma lem1973287 (x : real) (y : real) : (term709 y x) = (term709 x y).
Proof. exact (@lem1973286 (sqrt x) (sqrt y)). Qed.
Lemma lem1973291 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1973292 (x : real) (y : real) : (term710 y x) = (term710 x y).
Proof. exact (MK_COMB (@lem1973291) (@lem1973287 x y)). Qed.
Lemma lem1973294 (y : real) (x : real) : (term170 x y) = (term170 y x).
Proof. exact (EQ_MP (@lem1973206 y x) (@lem1973205 x y)). Qed.
Lemma lem1973295 (x : real) (y : real) : (term170 y x) = (term170 x y).
Proof. exact (@lem1973294 x y). Qed.
Lemma lem1973298 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1973299 (x : real) (y : real) : (term711 y x) = (term711 x y).
Proof. exact (MK_COMB (@lem1973298) (@lem1973295 x y)). Qed.
Lemma lem1973300 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1973301 (x : real) (y : real) : (term712 y x) = (term712 x y).
Proof. exact (MK_COMB (@lem1973300) (@lem1973299 x y)). Qed.
Lemma lem1973302 (x : real) (y : real) : (term673 y x) = (term673 x y).
Proof. exact (MK_COMB (@lem1973292 x y) (@lem1973301 x y)). Qed.
Lemma lem1973303 (x : real) (y : real) : (term675 x y) = (term675 x y).
Proof. exact (eq_refl (term675 x y)). Qed.
Lemma lem1973304 (x : real) (y : real) : ((term673 x y) = (term673 y x)) = ((term673 x y) = (term673 x y)).
Proof. exact (MK_COMB (@lem1973303 x y) (@lem1973302 x y)). Qed.
Lemma lem1973306 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1973307 (x : Prop) : (x = x) = True.
Proof. exact (@lem1973306 Prop x). Qed.
Lemma lem1973308 (x : real) (y : real) : ((term673 x y) = (term673 x y)) = True.
Proof. exact (@lem1973307 (term673 x y)). Qed.
Lemma lem1973309 (y : real) (x : real) : ((term673 x y) = (term673 y x)) = True.
Proof. exact (TRANS (@lem1973304 x y) (@lem1973308 x y)). Qed.
Lemma lem1973310 (x : real) : (term677 x) = term713.
Proof. exact (fun_ext (fun y : real => @lem1973309 y x)). Qed.
Lemma lem1973311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973312 (x : real) : (term679 x) = term714.
Proof. exact (MK_COMB (@lem1973311) (@lem1973310 x)). Qed.
Lemma lem1973314 {A : Type'} (t : Prop) : (term715 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1973315 (t : Prop) : (term716 t) = t.
Proof. exact (@lem1973314 real t). Qed.
Lemma lem1973316 : term714 = True.
Proof. exact (@lem1973315 True). Qed.
Lemma lem1973317 (x : real) : (term679 x) = True.
Proof. exact (TRANS (@lem1973312 x) (@lem1973316)). Qed.
Lemma lem1973318 : term681 = term713.
Proof. exact (fun_ext (fun x : real => @lem1973317 x)). Qed.
Lemma lem1973319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1973320 : term683 = term714.
Proof. exact (MK_COMB (@lem1973319) (@lem1973318)). Qed.
Lemma lem1973322 {A : Type'} (t : Prop) : (term715 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1973323 (t : Prop) : (term716 t) = t.
Proof. exact (@lem1973322 real t). Qed.
Lemma lem1973324 : term714 = True.
Proof. exact (@lem1973323 True). Qed.
Lemma lem1973325 : term683 = True.
Proof. exact (TRANS (@lem1973320) (@lem1973324)). Qed.
Lemma lem1973326 : True = term683.
Proof. exact (SYM (@lem1973325)). Qed.
Lemma lem1973327 : term683.
Proof. exact (EQ_MP (@lem1973326) (@lem0)). Qed.
Lemma lem1973328 (x : real) (y : real) (h1 : real_le x y) : real_le x y.
Proof. exact (h1). Qed.
Lemma lem1973329 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem1973330 (x : real) (h1 : term717) : term718 x.
Proof. exact (@lem1973329 h1 x). Qed.
Lemma lem1973331 (x : real) : (term718 x) = (term719 x).
Proof. exact (eq_refl (term718 x)). Qed.
Lemma lem1973332 (x : real) (h1 : term717) : term719 x.
Proof. exact (EQ_MP (@lem1973331 x) (@lem1973330 x h1)). Qed.
Lemma lem1973333 (x : real) (y : real) (h1 : term717) : term720 x y.
Proof. exact (@lem1973332 x h1 y). Qed.
Lemma lem1973334 (y : real) (x : real) : (term720 x y) = (term721 y x).
Proof. exact (eq_refl (term720 x y)). Qed.
Lemma lem1973335 (y : real) (x : real) (h1 : term717) : term721 y x.
Proof. exact (EQ_MP (@lem1973334 y x) (@lem1973333 x y h1)). Qed.
Lemma lem1973336 (y : real) (x : real) (z : real) (h1 : term717) : term722 y x z.
Proof. exact (@lem1973335 y x h1 z). Qed.
Lemma lem1973337 (y : real) (x : real) (z : real) : (term722 y x z) = (term723 y x z).
Proof. exact (eq_refl (term722 y x z)). Qed.
Lemma lem1973338 (y : real) (x : real) (z : real) (h1 : term717) : term723 y x z.
Proof. exact (EQ_MP (@lem1973337 y x z) (@lem1973336 y x z h1)). Qed.
Lemma lem1973339 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term724 x y z.
Proof. exact (h1). Qed.
Lemma lem1973340 (x : real) (y : real) (z : real) (h1 : term717) (h2 : term724 x y z) : real_le x z.
Proof. exact (@lem1973338 y x z h1 (@lem1973339 x y z h2)). Qed.
Lemma lem1973341 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term725 x z.
Proof. exact (fun h0 : term717 => @lem1973340 x y z h0 h1). Qed.
Lemma lem1973342 (x : real) (z : real) (h1 : term726 x z) : term726 x z.
Proof. exact (h1). Qed.
Lemma lem1973343 (x : real) (z : real) (h1 : term726 x z) : term725 x z.
Proof. exact (ex_elim (@lem1973342 x z h1) (fun y : real => fun h0 : term727 x z y => @lem1973341 x y z h0)). Qed.
Lemma lem1973344 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem1973345 (x : real) (z : real) (h1 : term717) (h2 : term726 x z) : real_le x z.
Proof. exact (@lem1973343 x z h2 (@lem1973344 h1)). Qed.
Lemma lem1973346 (x : real) (z : real) (h1 : term717) : term728 x z.
Proof. exact (fun h0 : term726 x z => @lem1973345 x z h1 h0). Qed.
Lemma lem1973347 (x : real) (h1 : term717) : term729 x.
Proof. exact (fun z : real => @lem1973346 x z h1). Qed.
Lemma lem1973348 (h1 : term717) : term730.
Proof. exact (fun x : real => @lem1973347 x h1). Qed.
Lemma lem1973349 : term731.
Proof. exact (fun h0 : term717 => @lem1973348 h0). Qed.
Lemma lem1973350 : term730.
Proof. exact (@lem1973349 (@lem1339577)). Qed.
Lemma lem1973351 (x : real) : term732 x.
Proof. exact (@lem1973350 x). Qed.
Lemma lem1973352 (x : real) : (term732 x) = (term729 x).
Proof. exact (eq_refl (term732 x)). Qed.
Lemma lem1973353 (x : real) : term729 x.
Proof. exact (EQ_MP (@lem1973352 x) (@lem1973351 x)). Qed.
Lemma lem1973354 (x : real) (z : real) : term733 x z.
Proof. exact (@lem1973353 x z). Qed.
Lemma lem1973355 (x : real) (z : real) : (term733 x z) = (term728 x z).
Proof. exact (eq_refl (term733 x z)). Qed.
Lemma lem1973358 (x : real) (z : real) : term728 x z.
Proof. exact (EQ_MP (@lem1973355 x z) (@lem1973354 x z)). Qed.
Lemma lem1973359 (x : real) (y : real) : term734 x y.
Proof. exact (@lem1973358 (term709 x y) (term712 x y)). Qed.
Lemma lem1973363 (x : real) (y : real) : (term447 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem1973195 x y) (@lem1973194 x y)). Qed.
Lemma lem1973364 (x : real) (y : real) : (term735 x y) = (term736 x y).
Proof. exact (@lem1973363 (term170 x y) (term711 x y)). Qed.
Lemma lem1973366 (x : real) : (term443 x) = True.
Proof. exact (EQ_MP (@lem1973189 x) (@lem1973188 x)). Qed.
Lemma lem1973367 (x : real) (y : real) : (term736 x y) = True.
Proof. exact (@lem1973366 (real_sub x y)). Qed.
Lemma lem1973368 (x : real) (y : real) : (term735 x y) = True.
Proof. exact (TRANS (@lem1973364 x y) (@lem1973367 x y)). Qed.
Lemma lem1973369 (x : real) (y : real) : (term737 x y) = (term737 x y).
Proof. exact (eq_refl (term737 x y)). Qed.
Lemma lem1973370 (x : real) (y : real) : (term738 x y) = (term739 x y).
Proof. exact (MK_COMB (@lem1973369 x y) (@lem1973368 x y)). Qed.
Lemma lem1973372 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1973373 (x : real) (y : real) : (term739 x y) = (term407 x y).
Proof. exact (@lem1973372 (term407 x y)). Qed.
Lemma lem1973374 (x : real) (y : real) : (term738 x y) = (term407 x y).
Proof. exact (TRANS (@lem1973370 x y) (@lem1973373 x y)). Qed.
Lemma lem1973375 (x : real) (y : real) : (term407 x y) = (term738 x y).
Proof. exact (SYM (@lem1973374 x y)). Qed.
Lemma lem1973377 (x : real) (y : real) : term405 x y.
Proof. exact (EQ_MP (@lem1972993 x y) (@lem1972992 x y)). Qed.
Lemma lem1973395 (x : real) (y : real) : (term740 x y) = (term741 x y).
Proof. exact (@lem17045 (term178 x) (term178 y)). Qed.
Lemma lem1973397 (x : real) : (term742 x) = (term742 x).
Proof. exact (eq_refl (term742 x)). Qed.
Lemma lem1973398 (x : real) (y : real) : (term743 x y) = (term744 x y).
Proof. exact (MK_COMB (@lem1973397 x) (@lem1973395 x y)). Qed.
Lemma lem1973399 (x : real) (y : real) : (term745 x y) = (term743 x y).
Proof. exact (@lem17362 (term178 x) (term406 x y)). Qed.
Lemma lem1973400 (x : real) (y : real) : (term745 x y) = (term744 x y).
Proof. exact (TRANS (@lem1973399 x y) (@lem1973398 x y)). Qed.
Lemma lem1973402 (x : real) (y : real) : (term746 x y) = (term746 x y).
Proof. exact (eq_refl (term746 x y)). Qed.
Lemma lem1973403 (x : real) (y : real) : (term747 x y) = (term748 x y).
Proof. exact (MK_COMB (@lem1973402 x y) (@lem1973400 x y)). Qed.
Lemma lem1973404 (x : real) (y : real) : (term749 x y) = (term747 x y).
Proof. exact (@lem17362 (real_le x y) (term750 x y)). Qed.
Lemma lem1973424 (x : real) (y : real) : (term749 x y) = (term748 x y).
Proof. exact (TRANS (@lem1973404 x y) (@lem1973403 x y)). Qed.
Lemma lem1973425 (y : real) (x : real) : (real_le x y) = (term251 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1973431 (y : real) (x : real) : (real_sub y x) = (term40 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1973436 (x : real) (y : real) : (term40 y x) = (term190 x y).
Proof. exact (@lem1483488 (term52 x) y). Qed.
Lemma lem1973438 (x : real) (y : real) : (real_sub y x) = (term190 x y).
Proof. exact (TRANS (@lem1973431 y x) (@lem1973436 x y)). Qed.
Lemma lem1973439 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973440 (x : real) (y : real) : (term751 y x) = (term603 x y).
Proof. exact (MK_COMB (@lem1973439) (@lem1973438 x y)). Qed.
Lemma lem1973441 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973442 (x : real) (y : real) : (term251 y x) = (term604 x y).
Proof. exact (MK_COMB (@lem1973440 x y) (@lem1973441)). Qed.
Lemma lem1973443 (x : real) (y : real) : (real_le x y) = (term604 x y).
Proof. exact (TRANS (@lem1973425 y x) (@lem1973442 x y)). Qed.
Lemma lem1973444 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem1483523 x term121). Qed.
Lemma lem1973450 (x : real) : (term180 x) = (term181 x).
Proof. exact (@lem1483519 x term121). Qed.
Lemma lem1973452 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1973453 : term139 = term121.
Proof. exact (@lem1973452 term22). Qed.
Lemma lem1973454 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1973455 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1973454 x) (@lem1973453)). Qed.
Lemma lem1973456 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1973457 (x : real) : (term181 x) = x.
Proof. exact (TRANS (@lem1973455 x) (@lem1973456 x)). Qed.
Lemma lem1973459 (x : real) : (term180 x) = x.
Proof. exact (TRANS (@lem1973450 x) (@lem1973457 x)). Qed.
Lemma lem1973460 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973461 (x : real) : (term183 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1973460) (@lem1973459 x)). Qed.
Lemma lem1973462 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973463 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1973461 x) (@lem1973462)). Qed.
Lemma lem1973464 (x : real) : (term178 x) = (term184 x).
Proof. exact (TRANS (@lem1973444 x) (@lem1973463 x)). Qed.
Lemma lem1973465 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483533 term121 x). Qed.
Lemma lem1973471 (x : real) : (term173 x) = (term174 x).
Proof. exact (@lem1483519 term121 x). Qed.
Lemma lem1973476 (x : real) : (term174 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1973478 (x : real) : (term173 x) = (term52 x).
Proof. exact (TRANS (@lem1973471 x) (@lem1973476 x)). Qed.
Lemma lem1973479 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973480 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1973479) (@lem1973478 x)). Qed.
Lemma lem1973481 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973482 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1973480 x) (@lem1973481)). Qed.
Lemma lem1973483 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1973465 x) (@lem1973482 x)). Qed.
Lemma lem1973484 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483533 term121 y). Qed.
Lemma lem1973490 (y : real) : (term173 y) = (term174 y).
Proof. exact (@lem1483519 term121 y). Qed.
Lemma lem1973495 (y : real) : (term174 y) = (term52 y).
Proof. exact (@lem1483448 (term52 y)). Qed.
Lemma lem1973497 (y : real) : (term173 y) = (term52 y).
Proof. exact (TRANS (@lem1973490 y) (@lem1973495 y)). Qed.
Lemma lem1973498 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973499 (y : real) : (term175 y) = (term176 y).
Proof. exact (MK_COMB (@lem1973498) (@lem1973497 y)). Qed.
Lemma lem1973500 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973501 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1973499 y) (@lem1973500)). Qed.
Lemma lem1973502 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1973484 y) (@lem1973501 y)). Qed.
Lemma lem1973503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1973504 (x : real) : (term752 x) = (term753 x).
Proof. exact (MK_COMB (@lem1973503) (@lem1973483 x)). Qed.
Lemma lem1973505 (x : real) (y : real) : (term741 x y) = (term754 x y).
Proof. exact (MK_COMB (@lem1973504 x) (@lem1973502 y)). Qed.
Lemma lem1973506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1973507 (x : real) : (term742 x) = (term755 x).
Proof. exact (MK_COMB (@lem1973506) (@lem1973464 x)). Qed.
Lemma lem1973508 (x : real) (y : real) : (term744 x y) = (term756 x y).
Proof. exact (MK_COMB (@lem1973507 x) (@lem1973505 x y)). Qed.
Lemma lem1973509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1973510 (x : real) (y : real) : (term746 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1973509) (@lem1973443 x y)). Qed.
Lemma lem1973511 (x : real) (y : real) : (term748 x y) = (term757 x y).
Proof. exact (MK_COMB (@lem1973510 x y) (@lem1973508 x y)). Qed.
Lemma lem1973518 (x : real) (y : real) : (term749 x y) = (term757 x y).
Proof. exact (TRANS (@lem1973424 x y) (@lem1973511 x y)). Qed.
Lemma lem1973535 (x : real) (y : real) : (term756 x y) = (term758 x y).
Proof. exact (@lem19158 (term177 x) (term184 x) (term177 y)). Qed.
Lemma lem1973538 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (eq_refl (term620 x y)). Qed.
Lemma lem1973539 (x : real) (y : real) : (term757 x y) = (term759 x y).
Proof. exact (MK_COMB (@lem1973538 x y) (@lem1973535 x y)). Qed.
Lemma lem1973546 (x : real) (y : real) : (term759 x y) = (term760 x y).
Proof. exact (@lem19158 (term761 x) (term604 x y) (term762 x y)). Qed.
Lemma lem1973547 (x : real) (y : real) : (term757 x y) = (term760 x y).
Proof. exact (TRANS (@lem1973539 x y) (@lem1973546 x y)). Qed.
Lemma lem1973548 (x : real) (y : real) : (term749 x y) = (term760 x y).
Proof. exact (TRANS (@lem1973518 x y) (@lem1973547 x y)). Qed.
Lemma lem1973558 (x : real) (y : real) (h1 : term760 x y) : term760 x y.
Proof. exact (h1). Qed.
Lemma lem1973559 (y : real) (x : real) (h1 : term763 y x) : term763 y x.
Proof. exact (h1). Qed.
Lemma lem1973560 (y : real) (x : real) (h1 : term763 y x) : term761 x.
Proof. exact (proj2 (@lem1973559 y x h1)). Qed.
Lemma lem1973562 (y : real) (x : real) (h1 : term763 y x) : term177 x.
Proof. exact (proj2 (@lem1973560 y x h1)). Qed.
Lemma lem1973563 (y : real) (x : real) (h1 : term763 y x) : term184 x.
Proof. exact (proj1 (@lem1973560 y x h1)). Qed.
Lemma lem1973565 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973566 : term368 = term369.
Proof. exact (@lem1973565 (NUMERAL 0) term22). Qed.
Lemma lem1973567 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973568 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973569 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973568 h1) (fun h1 : term369 = True => @lem1973567)). Qed.
Lemma lem1973570 : term369 = True.
Proof. exact (EQ_MP (@lem1973569) (@lem1973567)). Qed.
Lemma lem1973571 : term368 = True.
Proof. exact (TRANS (@lem1973566) (@lem1973570)). Qed.
Lemma lem1973572 : True = term368.
Proof. exact (SYM (@lem1973571)). Qed.
Lemma lem1973573 : term368.
Proof. exact (EQ_MP (@lem1973572) (@lem0)). Qed.
Lemma lem1973574 (y : real) (x : real) (h1 : term763 y x) : term371 x.
Proof. exact (conj (@lem1973573) (@lem1973563 y x h1)). Qed.
Lemma lem1973576 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1973577 (x : real) : term373 x.
Proof. exact (@lem1973576 term71 x). Qed.
Lemma lem1973578 (y : real) (x : real) (h1 : term763 y x) : term374 x.
Proof. exact (@lem1973577 x (@lem1973574 y x h1)). Qed.
Lemma lem1973579 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1973580 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973581 (x : real) : (term375 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1973580) (@lem1973579 x)). Qed.
Lemma lem1973582 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973583 (x : real) : (term374 x) = (term184 x).
Proof. exact (MK_COMB (@lem1973581 x) (@lem1973582)). Qed.
Lemma lem1973584 (y : real) (x : real) (h1 : term763 y x) : term184 x.
Proof. exact (EQ_MP (@lem1973583 x) (@lem1973578 y x h1)). Qed.
Lemma lem1973586 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973587 : term368 = term369.
Proof. exact (@lem1973586 (NUMERAL 0) term22). Qed.
Lemma lem1973588 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973589 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973590 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973589 h1) (fun h1 : term369 = True => @lem1973588)). Qed.
Lemma lem1973591 : term369 = True.
Proof. exact (EQ_MP (@lem1973590) (@lem1973588)). Qed.
Lemma lem1973592 : term368 = True.
Proof. exact (TRANS (@lem1973587) (@lem1973591)). Qed.
Lemma lem1973593 : True = term368.
Proof. exact (SYM (@lem1973592)). Qed.
Lemma lem1973594 : term368.
Proof. exact (EQ_MP (@lem1973593) (@lem0)). Qed.
Lemma lem1973595 (y : real) (x : real) (h1 : term763 y x) : term380 x.
Proof. exact (conj (@lem1973594) (@lem1973562 y x h1)). Qed.
Lemma lem1973597 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1973598 (x : real) : term382 x.
Proof. exact (@lem1973597 term71 (term52 x)). Qed.
Lemma lem1973599 (y : real) (x : real) (h1 : term763 y x) : term383 x.
Proof. exact (@lem1973598 x (@lem1973595 y x h1)). Qed.
Lemma lem1973600 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1973601 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973602 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1973601) (@lem1973600 x)). Qed.
Lemma lem1973603 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973604 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1973602 x) (@lem1973603)). Qed.
Lemma lem1973605 (y : real) (x : real) (h1 : term763 y x) : term177 x.
Proof. exact (EQ_MP (@lem1973604 x) (@lem1973599 y x h1)). Qed.
Lemma lem1973606 (y : real) (x : real) (h1 : term763 y x) : term394 x.
Proof. exact (conj (@lem1973605 y x h1) (@lem1973584 y x h1)). Qed.
Lemma lem1973608 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1973609 (x : real) : term395 x.
Proof. exact (@lem1973608 (term52 x) x). Qed.
Lemma lem1973610 (y : real) (x : real) (h1 : term763 y x) : term396 x.
Proof. exact (@lem1973609 x (@lem1973606 y x h1)). Qed.
Lemma lem1973611 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1973613 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1973614 : term122 = term121.
Proof. exact (@lem1973613 term22). Qed.
Lemma lem1973615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973616 : term123 = term124.
Proof. exact (MK_COMB (@lem1973615) (@lem1973614)). Qed.
Lemma lem1973617 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1973618 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1973616) (@lem1973617 x)). Qed.
Lemma lem1973619 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1973611 x) (@lem1973618 x)). Qed.
Lemma lem1973620 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1973621 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1973619 x) (@lem1973620 x)). Qed.
Lemma lem1973622 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973623 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1973622) (@lem1973621 x)). Qed.
Lemma lem1973624 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973625 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1973623 x) (@lem1973624)). Qed.
Lemma lem1973626 (y : real) (x : real) (h1 : term763 y x) : term145.
Proof. exact (EQ_MP (@lem1973625 x) (@lem1973610 y x h1)). Qed.
Lemma lem1973628 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973629 : term145 = term152.
Proof. exact (@lem1973628 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1973630 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1973631 : term145 = False.
Proof. exact (TRANS (@lem1973629) (@lem1973630)). Qed.
Lemma lem1973632 (y : real) (x : real) (h1 : term763 y x) : False.
Proof. exact (EQ_MP (@lem1973631) (@lem1973626 y x h1)). Qed.
Lemma lem1973633 (x : real) (y : real) (h1 : term764 x y) : term764 x y.
Proof. exact (h1). Qed.
Lemma lem1973634 (x : real) (y : real) (h1 : term764 x y) : term762 x y.
Proof. exact (proj2 (@lem1973633 x y h1)). Qed.
Lemma lem1973635 (x : real) (y : real) (h1 : term764 x y) : term604 x y.
Proof. exact (proj1 (@lem1973633 x y h1)). Qed.
Lemma lem1973636 (x : real) (y : real) (h1 : term764 x y) : term177 y.
Proof. exact (proj2 (@lem1973634 x y h1)). Qed.
Lemma lem1973637 (x : real) (y : real) (h1 : term764 x y) : term184 x.
Proof. exact (proj1 (@lem1973634 x y h1)). Qed.
Lemma lem1973639 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973640 : term368 = term369.
Proof. exact (@lem1973639 (NUMERAL 0) term22). Qed.
Lemma lem1973641 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973642 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973643 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973642 h1) (fun h1 : term369 = True => @lem1973641)). Qed.
Lemma lem1973644 : term369 = True.
Proof. exact (EQ_MP (@lem1973643) (@lem1973641)). Qed.
Lemma lem1973645 : term368 = True.
Proof. exact (TRANS (@lem1973640) (@lem1973644)). Qed.
Lemma lem1973646 : True = term368.
Proof. exact (SYM (@lem1973645)). Qed.
Lemma lem1973647 : term368.
Proof. exact (EQ_MP (@lem1973646) (@lem0)). Qed.
Lemma lem1973648 (x : real) (y : real) (h1 : term764 x y) : term371 x.
Proof. exact (conj (@lem1973647) (@lem1973637 x y h1)). Qed.
Lemma lem1973650 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1973651 (x : real) : term373 x.
Proof. exact (@lem1973650 term71 x). Qed.
Lemma lem1973652 (x : real) (y : real) (h1 : term764 x y) : term374 x.
Proof. exact (@lem1973651 x (@lem1973648 x y h1)). Qed.
Lemma lem1973653 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1973654 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973655 (x : real) : (term375 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1973654) (@lem1973653 x)). Qed.
Lemma lem1973656 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973657 (x : real) : (term374 x) = (term184 x).
Proof. exact (MK_COMB (@lem1973655 x) (@lem1973656)). Qed.
Lemma lem1973658 (x : real) (y : real) (h1 : term764 x y) : term184 x.
Proof. exact (EQ_MP (@lem1973657 x) (@lem1973652 x y h1)). Qed.
Lemma lem1973660 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973661 : term368 = term369.
Proof. exact (@lem1973660 (NUMERAL 0) term22). Qed.
Lemma lem1973662 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973663 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973664 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973663 h1) (fun h1 : term369 = True => @lem1973662)). Qed.
Lemma lem1973665 : term369 = True.
Proof. exact (EQ_MP (@lem1973664) (@lem1973662)). Qed.
Lemma lem1973666 : term368 = True.
Proof. exact (TRANS (@lem1973661) (@lem1973665)). Qed.
Lemma lem1973667 : True = term368.
Proof. exact (SYM (@lem1973666)). Qed.
Lemma lem1973668 : term368.
Proof. exact (EQ_MP (@lem1973667) (@lem0)). Qed.
Lemma lem1973669 (x : real) (y : real) (h1 : term764 x y) : term765 x y.
Proof. exact (conj (@lem1973668) (@lem1973635 x y h1)). Qed.
Lemma lem1973671 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1973672 (x : real) (y : real) : term766 x y.
Proof. exact (@lem1973671 term71 (term190 x y)). Qed.
Lemma lem1973673 (x : real) (y : real) (h1 : term764 x y) : term767 x y.
Proof. exact (@lem1973672 x y (@lem1973669 x y h1)). Qed.
Lemma lem1973674 (x : real) (y : real) : (term488 x y) = (term190 x y).
Proof. exact (@lem1483460 (term190 x y)). Qed.
Lemma lem1973675 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973676 (x : real) (y : real) : (term768 x y) = (term603 x y).
Proof. exact (MK_COMB (@lem1973675) (@lem1973674 x y)). Qed.
Lemma lem1973677 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973678 (x : real) (y : real) : (term767 x y) = (term604 x y).
Proof. exact (MK_COMB (@lem1973676 x y) (@lem1973677)). Qed.
Lemma lem1973679 (x : real) (y : real) (h1 : term764 x y) : term604 x y.
Proof. exact (EQ_MP (@lem1973678 x y) (@lem1973673 x y h1)). Qed.
Lemma lem1973681 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973682 : term368 = term369.
Proof. exact (@lem1973681 (NUMERAL 0) term22). Qed.
Lemma lem1973683 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973684 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973685 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973684 h1) (fun h1 : term369 = True => @lem1973683)). Qed.
Lemma lem1973686 : term369 = True.
Proof. exact (EQ_MP (@lem1973685) (@lem1973683)). Qed.
Lemma lem1973687 : term368 = True.
Proof. exact (TRANS (@lem1973682) (@lem1973686)). Qed.
Lemma lem1973688 : True = term368.
Proof. exact (SYM (@lem1973687)). Qed.
Lemma lem1973689 : term368.
Proof. exact (EQ_MP (@lem1973688) (@lem0)). Qed.
Lemma lem1973690 (x : real) (y : real) (h1 : term764 x y) : term380 y.
Proof. exact (conj (@lem1973689) (@lem1973636 x y h1)). Qed.
Lemma lem1973692 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1973693 (y : real) : term382 y.
Proof. exact (@lem1973692 term71 (term52 y)). Qed.
Lemma lem1973694 (x : real) (y : real) (h1 : term764 x y) : term383 y.
Proof. exact (@lem1973693 y (@lem1973690 x y h1)). Qed.
Lemma lem1973695 (y : real) : (term384 y) = (term52 y).
Proof. exact (@lem1483460 (term52 y)). Qed.
Lemma lem1973696 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973697 (y : real) : (term385 y) = (term176 y).
Proof. exact (MK_COMB (@lem1973696) (@lem1973695 y)). Qed.
Lemma lem1973698 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973699 (y : real) : (term383 y) = (term177 y).
Proof. exact (MK_COMB (@lem1973697 y) (@lem1973698)). Qed.
Lemma lem1973700 (x : real) (y : real) (h1 : term764 x y) : term177 y.
Proof. exact (EQ_MP (@lem1973699 y) (@lem1973694 x y h1)). Qed.
Lemma lem1973701 (x : real) (y : real) (h1 : term764 x y) : term769 x y.
Proof. exact (conj (@lem1973700 x y h1) (@lem1973679 x y h1)). Qed.
Lemma lem1973703 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1973704 (x : real) (y : real) : term770 x y.
Proof. exact (@lem1973703 (term52 y) (term190 x y)). Qed.
Lemma lem1973705 (x : real) (y : real) (h1 : term764 x y) : term771 x y.
Proof. exact (@lem1973704 x y (@lem1973701 x y h1)). Qed.
Lemma lem1973706 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483484 (term52 x) (term52 y) y). Qed.
Lemma lem1973707 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1973709 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1973710 : term122 = term121.
Proof. exact (@lem1973709 term22). Qed.
Lemma lem1973711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973712 : term123 = term124.
Proof. exact (MK_COMB (@lem1973711) (@lem1973710)). Qed.
Lemma lem1973713 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1973714 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1973712) (@lem1973713 y)). Qed.
Lemma lem1973715 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1973707 y) (@lem1973714 y)). Qed.
Lemma lem1973716 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1973717 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1973715 y) (@lem1973716 y)). Qed.
Lemma lem1973718 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1973719 (y : real) (x : real) : (term319 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1973718 x) (@lem1973717 y)). Qed.
Lemma lem1973720 (y : real) (x : real) : (term318 x y) = (term266 x).
Proof. exact (TRANS (@lem1973706 x y) (@lem1973719 y x)). Qed.
Lemma lem1973721 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1973722 (y : real) (x : real) : (term318 x y) = (term52 x).
Proof. exact (TRANS (@lem1973720 y x) (@lem1973721 x)). Qed.
Lemma lem1973723 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973724 (y : real) (x : real) : (term772 x y) = (term176 x).
Proof. exact (MK_COMB (@lem1973723) (@lem1973722 y x)). Qed.
Lemma lem1973725 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973726 (y : real) (x : real) : (term771 x y) = (term177 x).
Proof. exact (MK_COMB (@lem1973724 y x) (@lem1973725)). Qed.
Lemma lem1973727 (x : real) (y : real) (h1 : term764 x y) : term177 x.
Proof. exact (EQ_MP (@lem1973726 y x) (@lem1973705 x y h1)). Qed.
Lemma lem1973729 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973730 : term368 = term369.
Proof. exact (@lem1973729 (NUMERAL 0) term22). Qed.
Lemma lem1973731 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1973732 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1973733 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1973732 h1) (fun h1 : term369 = True => @lem1973731)). Qed.
Lemma lem1973734 : term369 = True.
Proof. exact (EQ_MP (@lem1973733) (@lem1973731)). Qed.
Lemma lem1973735 : term368 = True.
Proof. exact (TRANS (@lem1973730) (@lem1973734)). Qed.
Lemma lem1973736 : True = term368.
Proof. exact (SYM (@lem1973735)). Qed.
Lemma lem1973737 : term368.
Proof. exact (EQ_MP (@lem1973736) (@lem0)). Qed.
Lemma lem1973738 (x : real) (y : real) (h1 : term764 x y) : term380 x.
Proof. exact (conj (@lem1973737) (@lem1973727 x y h1)). Qed.
Lemma lem1973740 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1973741 (x : real) : term382 x.
Proof. exact (@lem1973740 term71 (term52 x)). Qed.
Lemma lem1973742 (x : real) (y : real) (h1 : term764 x y) : term383 x.
Proof. exact (@lem1973741 x (@lem1973738 x y h1)). Qed.
Lemma lem1973743 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1973744 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973745 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1973744) (@lem1973743 x)). Qed.
Lemma lem1973746 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973747 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1973745 x) (@lem1973746)). Qed.
Lemma lem1973748 (x : real) (y : real) (h1 : term764 x y) : term177 x.
Proof. exact (EQ_MP (@lem1973747 x) (@lem1973742 x y h1)). Qed.
Lemma lem1973749 (x : real) (y : real) (h1 : term764 x y) : term394 x.
Proof. exact (conj (@lem1973748 x y h1) (@lem1973658 x y h1)). Qed.
Lemma lem1973751 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1973752 (x : real) : term395 x.
Proof. exact (@lem1973751 (term52 x) x). Qed.
Lemma lem1973753 (x : real) (y : real) (h1 : term764 x y) : term396 x.
Proof. exact (@lem1973752 x (@lem1973749 x y h1)). Qed.
Lemma lem1973754 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1973756 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1973757 : term122 = term121.
Proof. exact (@lem1973756 term22). Qed.
Lemma lem1973758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1973759 : term123 = term124.
Proof. exact (MK_COMB (@lem1973758) (@lem1973757)). Qed.
Lemma lem1973760 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1973761 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1973759) (@lem1973760 x)). Qed.
Lemma lem1973762 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1973754 x) (@lem1973761 x)). Qed.
Lemma lem1973763 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1973764 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1973762 x) (@lem1973763 x)). Qed.
Lemma lem1973765 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973766 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1973765) (@lem1973764 x)). Qed.
Lemma lem1973767 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973768 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1973766 x) (@lem1973767)). Qed.
Lemma lem1973769 (x : real) (y : real) (h1 : term764 x y) : term145.
Proof. exact (EQ_MP (@lem1973768 x) (@lem1973753 x y h1)). Qed.
Lemma lem1973771 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1973772 : term145 = term152.
Proof. exact (@lem1973771 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1973773 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1973774 : term145 = False.
Proof. exact (TRANS (@lem1973772) (@lem1973773)). Qed.
Lemma lem1973775 (x : real) (y : real) (h1 : term764 x y) : False.
Proof. exact (EQ_MP (@lem1973774) (@lem1973769 x y h1)). Qed.
Lemma lem1973776 (x : real) (y : real) (h1 : term760 x y) : False.
Proof. exact (or_elim (@lem1973558 x y h1) (fun h0 : term763 y x => @lem1973632 y x h0) (fun h0 : term764 x y => @lem1973775 x y h0)). Qed.
Lemma lem1973778 (x : real) (y : real) (h1 : term760 x y) : term760 x y.
Proof. exact (h1). Qed.
Lemma lem1973779 (x : real) (y : real) (h1 : term760 x y) : (term760 x y) = False.
Proof. exact (prop_ext (fun h2 : term760 x y => @lem1973776 x y h1) (fun h2 : False => @lem1973778 x y h1)). Qed.
Lemma lem1973780 (x : real) (y : real) (h1 : term760 x y) : False.
Proof. exact (EQ_MP (@lem1973779 x y h1) (@lem1973778 x y h1)). Qed.
Lemma lem1973781 (x : real) (y : real) (h1 : term749 x y) : term749 x y.
Proof. exact (h1). Qed.
Lemma lem1973782 (x : real) (y : real) (h1 : term749 x y) : term760 x y.
Proof. exact (EQ_MP (@lem1973548 x y) (@lem1973781 x y h1)). Qed.
Lemma lem1973783 (x : real) (y : real) (h1 : term749 x y) : (term760 x y) = False.
Proof. exact (prop_ext (fun h2 : term760 x y => @lem1973780 x y h2) (fun h2 : False => @lem1973782 x y h1)). Qed.
Lemma lem1973784 (x : real) (y : real) (h1 : term749 x y) : False.
Proof. exact (EQ_MP (@lem1973783 x y h1) (@lem1973782 x y h1)). Qed.
Lemma lem1973785 (x : real) (y : real) : term773 x y.
Proof. exact (fun h0 : term749 x y => @lem1973784 x y h0). Qed.
Lemma lem1973786 (x : real) (y : real) : term774 x y.
Proof. exact (@lem1386578 (term775 x y)). Qed.
Lemma lem1973787 (x : real) (y : real) : term775 x y.
Proof. exact (@lem1973786 x y (@lem1973785 x y)). Qed.
Lemma lem1973788 (x : real) (y : real) (h1 : real_le x y) : term750 x y.
Proof. exact (@lem1973787 x y (@lem1973328 x y h1)). Qed.
Lemma lem1973789 (y : real) (x : real) (h1 : real_le x y) (h2 : term178 x) : term406 x y.
Proof. exact (@lem1973788 x y h1 (@lem1973200 x h2)). Qed.
Lemma lem1973790 (y : real) (x : real) (h1 : real_le x y) (h2 : term178 x) : term407 x y.
Proof. exact (@lem1973377 x y (@lem1973789 y x h1 h2)). Qed.
Lemma lem1973791 (y : real) (x : real) (h1 : real_le x y) (h2 : term178 x) : term738 x y.
Proof. exact (EQ_MP (@lem1973375 x y) (@lem1973790 y x h1 h2)). Qed.
Lemma lem1973792 (y : real) (x : real) (h1 : real_le x y) (h2 : term178 x) : term776 x y.
Proof. exact (ex_intro (term777 x y) (term778 x y) (@lem1973791 y x h1 h2)). Qed.
Lemma lem1973793 (y : real) (x : real) (h1 : real_le x y) (h2 : term178 x) : term673 x y.
Proof. exact (@lem1973359 x y (@lem1973792 y x h1 h2)). Qed.
Lemma lem1973795 (x : real) (y : real) : (term170 x y) = (term455 x y).
Proof. exact (@lem1972965 x y (@lem1972964 x y)). Qed.
Lemma lem1973796 (x : real) (y : real) : (term709 x y) = (term779 x y).
Proof. exact (@lem1973795 (sqrt x) (sqrt y)). Qed.
Lemma lem1973797 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1973798 (x : real) (y : real) : (term710 x y) = (term780 x y).
Proof. exact (MK_COMB (@lem1973797) (@lem1973796 x y)). Qed.
Lemma lem1973800 (x : real) (y : real) : (term170 x y) = (term455 x y).
Proof. exact (@lem1972965 x y (@lem1972964 x y)). Qed.
Lemma lem1973801 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1973802 (x : real) (y : real) : (term711 x y) = (term781 x y).
Proof. exact (MK_COMB (@lem1973801) (@lem1973800 x y)). Qed.
Lemma lem1973803 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1973804 (x : real) (y : real) : (term712 x y) = (term782 x y).
Proof. exact (MK_COMB (@lem1973803) (@lem1973802 x y)). Qed.
Lemma lem1973805 (x : real) (y : real) : (term673 x y) = (term783 x y).
Proof. exact (MK_COMB (@lem1973798 x y) (@lem1973804 x y)). Qed.
Lemma lem1973806 (x : real) (y : real) : (term783 x y) = (term673 x y).
Proof. exact (SYM (@lem1973805 x y)). Qed.
Lemma lem1973808 (x : real) : (term4 x) = (term3 x).
Proof. exact (EQ_MP (@lem1971400 x) (@lem1971399 x)). Qed.
Lemma lem1973809 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1973810 (x : real) : (term784 x) = (term785 x).
Proof. exact (MK_COMB (@lem1973809) (@lem1973808 x)). Qed.
Lemma lem1973812 (x : real) : (term4 x) = (term3 x).
Proof. exact (EQ_MP (@lem1971400 x) (@lem1971399 x)). Qed.
Lemma lem1973813 (y : real) : (term4 y) = (term3 y).
Proof. exact (@lem1973812 y). Qed.
Lemma lem1973814 (x : real) (y : real) : (term786 x y) = (term787 x y).
Proof. exact (MK_COMB (@lem1973810 x) (@lem1973813 y)). Qed.
Lemma lem1973815 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1973816 (x : real) (y : real) : (term779 x y) = (term788 x y).
Proof. exact (MK_COMB (@lem1973815) (@lem1973814 x y)). Qed.
Lemma lem1973817 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1973818 (x : real) (y : real) : (term780 x y) = (term789 x y).
Proof. exact (MK_COMB (@lem1973817) (@lem1973816 x y)). Qed.
Lemma lem1973819 (x : real) (y : real) : (term782 x y) = (term782 x y).
Proof. exact (eq_refl (term782 x y)). Qed.
Lemma lem1973820 (x : real) (y : real) : (term783 x y) = (term790 x y).
Proof. exact (MK_COMB (@lem1973818 x y) (@lem1973819 x y)). Qed.
Lemma lem1973821 (x : real) (y : real) : (term790 x y) = (term783 x y).
Proof. exact (SYM (@lem1973820 x y)). Qed.
Lemma lem1973822 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem1973823 (x : real) (h1 : term717) : term718 x.
Proof. exact (@lem1973822 h1 x). Qed.
Lemma lem1973824 (x : real) : (term718 x) = (term719 x).
Proof. exact (eq_refl (term718 x)). Qed.
Lemma lem1973825 (x : real) (h1 : term717) : term719 x.
Proof. exact (EQ_MP (@lem1973824 x) (@lem1973823 x h1)). Qed.
Lemma lem1973826 (x : real) (y : real) (h1 : term717) : term720 x y.
Proof. exact (@lem1973825 x h1 y). Qed.
Lemma lem1973827 (y : real) (x : real) : (term720 x y) = (term721 y x).
Proof. exact (eq_refl (term720 x y)). Qed.
Lemma lem1973828 (y : real) (x : real) (h1 : term717) : term721 y x.
Proof. exact (EQ_MP (@lem1973827 y x) (@lem1973826 x y h1)). Qed.
Lemma lem1973829 (y : real) (x : real) (z : real) (h1 : term717) : term722 y x z.
Proof. exact (@lem1973828 y x h1 z). Qed.
Lemma lem1973830 (y : real) (x : real) (z : real) : (term722 y x z) = (term723 y x z).
Proof. exact (eq_refl (term722 y x z)). Qed.
Lemma lem1973831 (y : real) (x : real) (z : real) (h1 : term717) : term723 y x z.
Proof. exact (EQ_MP (@lem1973830 y x z) (@lem1973829 y x z h1)). Qed.
Lemma lem1973832 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term724 x y z.
Proof. exact (h1). Qed.
Lemma lem1973833 (x : real) (y : real) (z : real) (h1 : term717) (h2 : term724 x y z) : real_le x z.
Proof. exact (@lem1973831 y x z h1 (@lem1973832 x y z h2)). Qed.
Lemma lem1973834 (x : real) (y : real) (z : real) (h1 : term724 x y z) : term725 x z.
Proof. exact (fun h0 : term717 => @lem1973833 x y z h0 h1). Qed.
Lemma lem1973835 (x : real) (z : real) (h1 : term726 x z) : term726 x z.
Proof. exact (h1). Qed.
Lemma lem1973836 (x : real) (z : real) (h1 : term726 x z) : term725 x z.
Proof. exact (ex_elim (@lem1973835 x z h1) (fun y : real => fun h0 : term727 x z y => @lem1973834 x y z h0)). Qed.
Lemma lem1973837 (h1 : term717) : term717.
Proof. exact (h1). Qed.
Lemma lem1973838 (x : real) (z : real) (h1 : term717) (h2 : term726 x z) : real_le x z.
Proof. exact (@lem1973836 x z h2 (@lem1973837 h1)). Qed.
Lemma lem1973839 (x : real) (z : real) (h1 : term717) : term728 x z.
Proof. exact (fun h0 : term726 x z => @lem1973838 x z h1 h0). Qed.
Lemma lem1973840 (x : real) (h1 : term717) : term729 x.
Proof. exact (fun z : real => @lem1973839 x z h1). Qed.
Lemma lem1973841 (h1 : term717) : term730.
Proof. exact (fun x : real => @lem1973840 x h1). Qed.
Lemma lem1973842 : term731.
Proof. exact (fun h0 : term717 => @lem1973841 h0). Qed.
Lemma lem1973843 : term730.
Proof. exact (@lem1973842 (@lem1339577)). Qed.
Lemma lem1973844 (x : real) : term732 x.
Proof. exact (@lem1973843 x). Qed.
Lemma lem1973845 (x : real) : (term732 x) = (term729 x).
Proof. exact (eq_refl (term732 x)). Qed.
Lemma lem1973846 (x : real) : term729 x.
Proof. exact (EQ_MP (@lem1973845 x) (@lem1973844 x)). Qed.
Lemma lem1973847 (x : real) (z : real) : term733 x z.
Proof. exact (@lem1973846 x z). Qed.
Lemma lem1973848 (x : real) (z : real) : (term733 x z) = (term728 x z).
Proof. exact (eq_refl (term733 x z)). Qed.
Lemma lem1973851 (x : real) (z : real) : term728 x z.
Proof. exact (EQ_MP (@lem1973848 x z) (@lem1973847 x z)). Qed.
Lemma lem1973852 (x : real) (y : real) : term791 x y.
Proof. exact (@lem1973851 (term788 x y) (term782 x y)). Qed.
Lemma lem1973856 (x : real) (y : real) : (term447 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem1971387 x y) (@lem1971386 x y)). Qed.
Lemma lem1973857 (x : real) (y : real) : (term792 x y) = (term793 x y).
Proof. exact (@lem1973856 (term455 x y) (term781 x y)). Qed.
Lemma lem1973859 (x : real) : (term443 x) = True.
Proof. exact (EQ_MP (@lem1971381 x) (@lem1971380 x)). Qed.
Lemma lem1973860 (x : real) (y : real) : (term793 x y) = True.
Proof. exact (@lem1973859 (term483 x y)). Qed.
Lemma lem1973861 (x : real) (y : real) : (term792 x y) = True.
Proof. exact (TRANS (@lem1973857 x y) (@lem1973860 x y)). Qed.
Lemma lem1973862 (x : real) (y : real) : (term794 x y) = (term794 x y).
Proof. exact (eq_refl (term794 x y)). Qed.
Lemma lem1973863 (x : real) (y : real) : (term795 x y) = (term796 x y).
Proof. exact (MK_COMB (@lem1973862 x y) (@lem1973861 x y)). Qed.
Lemma lem1973865 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1973866 (x : real) (y : real) : (term796 x y) = (term797 x y).
Proof. exact (@lem1973865 (term797 x y)). Qed.
Lemma lem1973867 (x : real) (y : real) : (term795 x y) = (term797 x y).
Proof. exact (TRANS (@lem1973863 x y) (@lem1973866 x y)). Qed.
Lemma lem1973868 (x : real) (y : real) : (term797 x y) = (term795 x y).
Proof. exact (SYM (@lem1973867 x y)). Qed.
Lemma lem1973870 (x : real) (y : real) : term405 x y.
Proof. exact (EQ_MP (@lem1971185 x y) (@lem1971184 x y)). Qed.
Lemma lem1973871 (x : real) (y : real) : term798 x y.
Proof. exact (@lem1973870 (real_neg x) (real_neg y)). Qed.
Lemma lem1973892 (x : real) (y : real) : (term799 x y) = (term800 x y).
Proof. exact (@lem17045 (term801 x) (term801 y)). Qed.
Lemma lem1973894 (y : real) : (term185 y) = (term185 y).
Proof. exact (eq_refl (term185 y)). Qed.
Lemma lem1973895 (x : real) (y : real) : (term802 x y) = (term803 x y).
Proof. exact (MK_COMB (@lem1973894 y) (@lem1973892 x y)). Qed.
Lemma lem1973896 (x : real) (y : real) : (term804 x y) = (term802 x y).
Proof. exact (@lem17362 (term171 y) (term805 x y)). Qed.
Lemma lem1973897 (x : real) (y : real) : (term804 x y) = (term803 x y).
Proof. exact (TRANS (@lem1973896 x y) (@lem1973895 x y)). Qed.
Lemma lem1973899 (x : real) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem1973900 (x : real) (y : real) : (term806 x y) = (term807 x y).
Proof. exact (MK_COMB (@lem1973899 x) (@lem1973897 x y)). Qed.
Lemma lem1973901 (x : real) (y : real) : (term808 x y) = (term806 x y).
Proof. exact (@lem17362 (term171 x) (term809 x y)). Qed.
Lemma lem1973902 (x : real) (y : real) : (term808 x y) = (term807 x y).
Proof. exact (TRANS (@lem1973901 x y) (@lem1973900 x y)). Qed.
Lemma lem1973904 (x : real) (y : real) : (term746 x y) = (term746 x y).
Proof. exact (eq_refl (term746 x y)). Qed.
Lemma lem1973905 (x : real) (y : real) : (term810 x y) = (term811 x y).
Proof. exact (MK_COMB (@lem1973904 x y) (@lem1973902 x y)). Qed.
Lemma lem1973906 (x : real) (y : real) : (term812 x y) = (term810 x y).
Proof. exact (@lem17362 (real_le x y) (term813 x y)). Qed.
Lemma lem1973934 (x : real) (y : real) : (term812 x y) = (term811 x y).
Proof. exact (TRANS (@lem1973906 x y) (@lem1973905 x y)). Qed.
Lemma lem1973935 (y : real) (x : real) : (real_le x y) = (term251 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1973941 (y : real) (x : real) : (real_sub y x) = (term40 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1973946 (x : real) (y : real) : (term40 y x) = (term190 x y).
Proof. exact (@lem1483488 (term52 x) y). Qed.
Lemma lem1973948 (x : real) (y : real) : (real_sub y x) = (term190 x y).
Proof. exact (TRANS (@lem1973941 y x) (@lem1973946 x y)). Qed.
Lemma lem1973949 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1973950 (x : real) (y : real) : (term751 y x) = (term603 x y).
Proof. exact (MK_COMB (@lem1973949) (@lem1973948 x y)). Qed.
Lemma lem1973951 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973952 (x : real) (y : real) : (term251 y x) = (term604 x y).
Proof. exact (MK_COMB (@lem1973950 x y) (@lem1973951)). Qed.
Lemma lem1973953 (x : real) (y : real) : (real_le x y) = (term604 x y).
Proof. exact (TRANS (@lem1973935 y x) (@lem1973952 x y)). Qed.
Lemma lem1973954 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483533 term121 x). Qed.
Lemma lem1973960 (x : real) : (term173 x) = (term174 x).
Proof. exact (@lem1483519 term121 x). Qed.
Lemma lem1973965 (x : real) : (term174 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1973967 (x : real) : (term173 x) = (term52 x).
Proof. exact (TRANS (@lem1973960 x) (@lem1973965 x)). Qed.
Lemma lem1973968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973969 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1973968) (@lem1973967 x)). Qed.
Lemma lem1973970 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973971 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1973969 x) (@lem1973970)). Qed.
Lemma lem1973972 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1973954 x) (@lem1973971 x)). Qed.
Lemma lem1973973 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483533 term121 y). Qed.
Lemma lem1973979 (y : real) : (term173 y) = (term174 y).
Proof. exact (@lem1483519 term121 y). Qed.
Lemma lem1973984 (y : real) : (term174 y) = (term52 y).
Proof. exact (@lem1483448 (term52 y)). Qed.
Lemma lem1973986 (y : real) : (term173 y) = (term52 y).
Proof. exact (TRANS (@lem1973979 y) (@lem1973984 y)). Qed.
Lemma lem1973987 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1973988 (y : real) : (term175 y) = (term176 y).
Proof. exact (MK_COMB (@lem1973987) (@lem1973986 y)). Qed.
Lemma lem1973989 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1973990 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1973988 y) (@lem1973989)). Qed.
Lemma lem1973991 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1973973 y) (@lem1973990 y)). Qed.
Lemma lem1973992 (x : real) : (term814 x) = (term815 x).
Proof. exact (@lem1483533 term121 (real_neg x)). Qed.
Lemma lem1973999 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1974002 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1974003 (x : real) : (term816 x) = (term817 x).
Proof. exact (MK_COMB (@lem1974002) (@lem1973999 x)). Qed.
Lemma lem1974004 (x : real) : (term817 x) = (term818 x).
Proof. exact (@lem1483519 term121 (term52 x)). Qed.
Lemma lem1974005 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1483476 term16 term16 x). Qed.
Lemma lem1974007 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1974008 : term67 = term68.
Proof. exact (@lem1974007 term22 term22). Qed.
Lemma lem1974009 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1974010 : term70 = term22.
Proof. exact (EQ_MP (@lem1974009) (@lem940073)). Qed.
Lemma lem1974011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974012 : term68 = term71.
Proof. exact (MK_COMB (@lem1974011) (@lem1974010)). Qed.
Lemma lem1974013 : term67 = term71.
Proof. exact (TRANS (@lem1974008) (@lem1974012)). Qed.
Lemma lem1974014 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974015 : term72 = term73.
Proof. exact (MK_COMB (@lem1974014) (@lem1974013)). Qed.
Lemma lem1974016 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1974017 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1974015) (@lem1974016 x)). Qed.
Lemma lem1974018 (x : real) : (term197 x) = (term199 x).
Proof. exact (TRANS (@lem1974005 x) (@lem1974017 x)). Qed.
Lemma lem1974019 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1974020 (x : real) : (term197 x) = x.
Proof. exact (TRANS (@lem1974018 x) (@lem1974019 x)). Qed.
Lemma lem1974021 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1974022 (x : real) : (term818 x) = (term819 x).
Proof. exact (MK_COMB (@lem1974021) (@lem1974020 x)). Qed.
Lemma lem1974023 (x : real) : (term819 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1974024 (x : real) : (term818 x) = x.
Proof. exact (TRANS (@lem1974022 x) (@lem1974023 x)). Qed.
Lemma lem1974025 (x : real) : (term817 x) = x.
Proof. exact (TRANS (@lem1974004 x) (@lem1974024 x)). Qed.
Lemma lem1974026 (x : real) : (term816 x) = x.
Proof. exact (TRANS (@lem1974003 x) (@lem1974025 x)). Qed.
Lemma lem1974027 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974028 (x : real) : (term820 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1974027) (@lem1974026 x)). Qed.
Lemma lem1974029 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974030 (x : real) : (term815 x) = (term435 x).
Proof. exact (MK_COMB (@lem1974028 x) (@lem1974029)). Qed.
Lemma lem1974031 (x : real) : (term814 x) = (term435 x).
Proof. exact (TRANS (@lem1973992 x) (@lem1974030 x)). Qed.
Lemma lem1974032 (y : real) : (term814 y) = (term815 y).
Proof. exact (@lem1483533 term121 (real_neg y)). Qed.
Lemma lem1974039 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1974042 : term302 = term302.
Proof. exact (eq_refl term302). Qed.
Lemma lem1974043 (y : real) : (term816 y) = (term817 y).
Proof. exact (MK_COMB (@lem1974042) (@lem1974039 y)). Qed.
Lemma lem1974044 (y : real) : (term817 y) = (term818 y).
Proof. exact (@lem1483519 term121 (term52 y)). Qed.
Lemma lem1974045 (y : real) : (term197 y) = (term198 y).
Proof. exact (@lem1483476 term16 term16 y). Qed.
Lemma lem1974047 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1974048 : term67 = term68.
Proof. exact (@lem1974047 term22 term22). Qed.
Lemma lem1974049 : (term69 = (BIT1 0)) = (term70 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1974050 : term70 = term22.
Proof. exact (EQ_MP (@lem1974049) (@lem940073)). Qed.
Lemma lem1974051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974052 : term68 = term71.
Proof. exact (MK_COMB (@lem1974051) (@lem1974050)). Qed.
Lemma lem1974053 : term67 = term71.
Proof. exact (TRANS (@lem1974048) (@lem1974052)). Qed.
Lemma lem1974054 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974055 : term72 = term73.
Proof. exact (MK_COMB (@lem1974054) (@lem1974053)). Qed.
Lemma lem1974056 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1974057 (y : real) : (term198 y) = (term199 y).
Proof. exact (MK_COMB (@lem1974055) (@lem1974056 y)). Qed.
Lemma lem1974058 (y : real) : (term197 y) = (term199 y).
Proof. exact (TRANS (@lem1974045 y) (@lem1974057 y)). Qed.
Lemma lem1974059 (y : real) : (term199 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1974060 (y : real) : (term197 y) = y.
Proof. exact (TRANS (@lem1974058 y) (@lem1974059 y)). Qed.
Lemma lem1974061 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem1974062 (y : real) : (term818 y) = (term819 y).
Proof. exact (MK_COMB (@lem1974061) (@lem1974060 y)). Qed.
Lemma lem1974063 (y : real) : (term819 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1974064 (y : real) : (term818 y) = y.
Proof. exact (TRANS (@lem1974062 y) (@lem1974063 y)). Qed.
Lemma lem1974065 (y : real) : (term817 y) = y.
Proof. exact (TRANS (@lem1974044 y) (@lem1974064 y)). Qed.
Lemma lem1974066 (y : real) : (term816 y) = y.
Proof. exact (TRANS (@lem1974043 y) (@lem1974065 y)). Qed.
Lemma lem1974067 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974068 (y : real) : (term820 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1974067) (@lem1974066 y)). Qed.
Lemma lem1974069 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974070 (y : real) : (term815 y) = (term435 y).
Proof. exact (MK_COMB (@lem1974068 y) (@lem1974069)). Qed.
Lemma lem1974071 (y : real) : (term814 y) = (term435 y).
Proof. exact (TRANS (@lem1974032 y) (@lem1974070 y)). Qed.
Lemma lem1974072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1974073 (x : real) : (term821 x) = (term822 x).
Proof. exact (MK_COMB (@lem1974072) (@lem1974031 x)). Qed.
Lemma lem1974074 (x : real) (y : real) : (term800 x y) = (term823 x y).
Proof. exact (MK_COMB (@lem1974073 x) (@lem1974071 y)). Qed.
Lemma lem1974075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974076 (y : real) : (term185 y) = (term186 y).
Proof. exact (MK_COMB (@lem1974075) (@lem1973991 y)). Qed.
Lemma lem1974077 (x : real) (y : real) : (term803 x y) = (term824 x y).
Proof. exact (MK_COMB (@lem1974076 y) (@lem1974074 x y)). Qed.
Lemma lem1974078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974079 (x : real) : (term185 x) = (term186 x).
Proof. exact (MK_COMB (@lem1974078) (@lem1973972 x)). Qed.
Lemma lem1974080 (x : real) (y : real) : (term807 x y) = (term825 x y).
Proof. exact (MK_COMB (@lem1974079 x) (@lem1974077 x y)). Qed.
Lemma lem1974081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974082 (x : real) (y : real) : (term746 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1974081) (@lem1973953 x y)). Qed.
Lemma lem1974083 (x : real) (y : real) : (term811 x y) = (term826 x y).
Proof. exact (MK_COMB (@lem1974082 x y) (@lem1974080 x y)). Qed.
Lemma lem1974090 (x : real) (y : real) : (term812 x y) = (term826 x y).
Proof. exact (TRANS (@lem1973934 x y) (@lem1974083 x y)). Qed.
Lemma lem1974107 (x : real) (y : real) : (term824 x y) = (term827 x y).
Proof. exact (@lem19158 (term435 x) (term177 y) (term435 y)). Qed.
Lemma lem1974110 (x : real) : (term186 x) = (term186 x).
Proof. exact (eq_refl (term186 x)). Qed.
Lemma lem1974111 (x : real) (y : real) : (term825 x y) = (term828 x y).
Proof. exact (MK_COMB (@lem1974110 x) (@lem1974107 x y)). Qed.
Lemma lem1974118 (x : real) (y : real) : (term828 x y) = (term829 x y).
Proof. exact (@lem19158 (term830 y x) (term177 x) (term436 y)). Qed.
Lemma lem1974119 (x : real) (y : real) : (term825 x y) = (term829 x y).
Proof. exact (TRANS (@lem1974111 x y) (@lem1974118 x y)). Qed.
Lemma lem1974122 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (eq_refl (term620 x y)). Qed.
Lemma lem1974123 (x : real) (y : real) : (term826 x y) = (term831 x y).
Proof. exact (MK_COMB (@lem1974122 x y) (@lem1974119 x y)). Qed.
Lemma lem1974130 (x : real) (y : real) : (term831 x y) = (term832 x y).
Proof. exact (@lem19158 (term833 y x) (term604 x y) (term834 x y)). Qed.
Lemma lem1974131 (x : real) (y : real) : (term826 x y) = (term832 x y).
Proof. exact (TRANS (@lem1974123 x y) (@lem1974130 x y)). Qed.
Lemma lem1974132 (x : real) (y : real) : (term812 x y) = (term832 x y).
Proof. exact (TRANS (@lem1974090 x y) (@lem1974131 x y)). Qed.
Lemma lem1974142 (x : real) (y : real) (h1 : term832 x y) : term832 x y.
Proof. exact (h1). Qed.
Lemma lem1974143 (y : real) (x : real) (h1 : term835 y x) : term835 y x.
Proof. exact (h1). Qed.
Lemma lem1974144 (y : real) (x : real) (h1 : term835 y x) : term833 y x.
Proof. exact (proj2 (@lem1974143 y x h1)). Qed.
Lemma lem1974145 (y : real) (x : real) (h1 : term835 y x) : term604 x y.
Proof. exact (proj1 (@lem1974143 y x h1)). Qed.
Lemma lem1974146 (y : real) (x : real) (h1 : term835 y x) : term830 y x.
Proof. exact (proj2 (@lem1974144 y x h1)). Qed.
Lemma lem1974148 (y : real) (x : real) (h1 : term835 y x) : term435 x.
Proof. exact (proj2 (@lem1974146 y x h1)). Qed.
Lemma lem1974149 (y : real) (x : real) (h1 : term835 y x) : term177 y.
Proof. exact (proj1 (@lem1974146 y x h1)). Qed.
Lemma lem1974151 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974152 : term368 = term369.
Proof. exact (@lem1974151 (NUMERAL 0) term22). Qed.
Lemma lem1974153 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974154 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974155 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974154 h1) (fun h1 : term369 = True => @lem1974153)). Qed.
Lemma lem1974156 : term369 = True.
Proof. exact (EQ_MP (@lem1974155) (@lem1974153)). Qed.
Lemma lem1974157 : term368 = True.
Proof. exact (TRANS (@lem1974152) (@lem1974156)). Qed.
Lemma lem1974158 : True = term368.
Proof. exact (SYM (@lem1974157)). Qed.
Lemma lem1974159 : term368.
Proof. exact (EQ_MP (@lem1974158) (@lem0)). Qed.
Lemma lem1974160 (y : real) (x : real) (h1 : term835 y x) : term437 x.
Proof. exact (conj (@lem1974159) (@lem1974148 y x h1)). Qed.
Lemma lem1974162 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1974163 (x : real) : term438 x.
Proof. exact (@lem1974162 term71 x). Qed.
Lemma lem1974164 (y : real) (x : real) (h1 : term835 y x) : term434 x.
Proof. exact (@lem1974163 x (@lem1974160 y x h1)). Qed.
Lemma lem1974165 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1974166 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974167 (x : real) : (term433 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1974166) (@lem1974165 x)). Qed.
Lemma lem1974168 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974169 (x : real) : (term434 x) = (term435 x).
Proof. exact (MK_COMB (@lem1974167 x) (@lem1974168)). Qed.
Lemma lem1974170 (y : real) (x : real) (h1 : term835 y x) : term435 x.
Proof. exact (EQ_MP (@lem1974169 x) (@lem1974164 y x h1)). Qed.
Lemma lem1974172 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974173 : term368 = term369.
Proof. exact (@lem1974172 (NUMERAL 0) term22). Qed.
Lemma lem1974174 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974175 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974176 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974175 h1) (fun h1 : term369 = True => @lem1974174)). Qed.
Lemma lem1974177 : term369 = True.
Proof. exact (EQ_MP (@lem1974176) (@lem1974174)). Qed.
Lemma lem1974178 : term368 = True.
Proof. exact (TRANS (@lem1974173) (@lem1974177)). Qed.
Lemma lem1974179 : True = term368.
Proof. exact (SYM (@lem1974178)). Qed.
Lemma lem1974180 : term368.
Proof. exact (EQ_MP (@lem1974179) (@lem0)). Qed.
Lemma lem1974181 (y : real) (x : real) (h1 : term835 y x) : term765 x y.
Proof. exact (conj (@lem1974180) (@lem1974145 y x h1)). Qed.
Lemma lem1974183 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1974184 (x : real) (y : real) : term766 x y.
Proof. exact (@lem1974183 term71 (term190 x y)). Qed.
Lemma lem1974185 (y : real) (x : real) (h1 : term835 y x) : term767 x y.
Proof. exact (@lem1974184 x y (@lem1974181 y x h1)). Qed.
Lemma lem1974186 (x : real) (y : real) : (term488 x y) = (term190 x y).
Proof. exact (@lem1483460 (term190 x y)). Qed.
Lemma lem1974187 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1974188 (x : real) (y : real) : (term768 x y) = (term603 x y).
Proof. exact (MK_COMB (@lem1974187) (@lem1974186 x y)). Qed.
Lemma lem1974189 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974190 (x : real) (y : real) : (term767 x y) = (term604 x y).
Proof. exact (MK_COMB (@lem1974188 x y) (@lem1974189)). Qed.
Lemma lem1974191 (y : real) (x : real) (h1 : term835 y x) : term604 x y.
Proof. exact (EQ_MP (@lem1974190 x y) (@lem1974185 y x h1)). Qed.
Lemma lem1974193 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974194 : term368 = term369.
Proof. exact (@lem1974193 (NUMERAL 0) term22). Qed.
Lemma lem1974195 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974196 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974197 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974196 h1) (fun h1 : term369 = True => @lem1974195)). Qed.
Lemma lem1974198 : term369 = True.
Proof. exact (EQ_MP (@lem1974197) (@lem1974195)). Qed.
Lemma lem1974199 : term368 = True.
Proof. exact (TRANS (@lem1974194) (@lem1974198)). Qed.
Lemma lem1974200 : True = term368.
Proof. exact (SYM (@lem1974199)). Qed.
Lemma lem1974201 : term368.
Proof. exact (EQ_MP (@lem1974200) (@lem0)). Qed.
Lemma lem1974202 (y : real) (x : real) (h1 : term835 y x) : term380 y.
Proof. exact (conj (@lem1974201) (@lem1974149 y x h1)). Qed.
Lemma lem1974204 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1974205 (y : real) : term382 y.
Proof. exact (@lem1974204 term71 (term52 y)). Qed.
Lemma lem1974206 (y : real) (x : real) (h1 : term835 y x) : term383 y.
Proof. exact (@lem1974205 y (@lem1974202 y x h1)). Qed.
Lemma lem1974207 (y : real) : (term384 y) = (term52 y).
Proof. exact (@lem1483460 (term52 y)). Qed.
Lemma lem1974208 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974209 (y : real) : (term385 y) = (term176 y).
Proof. exact (MK_COMB (@lem1974208) (@lem1974207 y)). Qed.
Lemma lem1974210 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974211 (y : real) : (term383 y) = (term177 y).
Proof. exact (MK_COMB (@lem1974209 y) (@lem1974210)). Qed.
Lemma lem1974212 (y : real) (x : real) (h1 : term835 y x) : term177 y.
Proof. exact (EQ_MP (@lem1974211 y) (@lem1974206 y x h1)). Qed.
Lemma lem1974213 (y : real) (x : real) (h1 : term835 y x) : term769 x y.
Proof. exact (conj (@lem1974212 y x h1) (@lem1974191 y x h1)). Qed.
Lemma lem1974215 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1974216 (x : real) (y : real) : term770 x y.
Proof. exact (@lem1974215 (term52 y) (term190 x y)). Qed.
Lemma lem1974217 (y : real) (x : real) (h1 : term835 y x) : term771 x y.
Proof. exact (@lem1974216 x y (@lem1974213 y x h1)). Qed.
Lemma lem1974218 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483484 (term52 x) (term52 y) y). Qed.
Lemma lem1974219 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1974221 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1974222 : term122 = term121.
Proof. exact (@lem1974221 term22). Qed.
Lemma lem1974223 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974224 : term123 = term124.
Proof. exact (MK_COMB (@lem1974223) (@lem1974222)). Qed.
Lemma lem1974225 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1974226 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1974224) (@lem1974225 y)). Qed.
Lemma lem1974227 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1974219 y) (@lem1974226 y)). Qed.
Lemma lem1974228 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1974229 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1974227 y) (@lem1974228 y)). Qed.
Lemma lem1974230 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1974231 (y : real) (x : real) : (term319 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1974230 x) (@lem1974229 y)). Qed.
Lemma lem1974232 (y : real) (x : real) : (term318 x y) = (term266 x).
Proof. exact (TRANS (@lem1974218 x y) (@lem1974231 y x)). Qed.
Lemma lem1974233 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1974234 (y : real) (x : real) : (term318 x y) = (term52 x).
Proof. exact (TRANS (@lem1974232 y x) (@lem1974233 x)). Qed.
Lemma lem1974235 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974236 (y : real) (x : real) : (term772 x y) = (term176 x).
Proof. exact (MK_COMB (@lem1974235) (@lem1974234 y x)). Qed.
Lemma lem1974237 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974238 (y : real) (x : real) : (term771 x y) = (term177 x).
Proof. exact (MK_COMB (@lem1974236 y x) (@lem1974237)). Qed.
Lemma lem1974239 (y : real) (x : real) (h1 : term835 y x) : term177 x.
Proof. exact (EQ_MP (@lem1974238 y x) (@lem1974217 y x h1)). Qed.
Lemma lem1974241 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974242 : term368 = term369.
Proof. exact (@lem1974241 (NUMERAL 0) term22). Qed.
Lemma lem1974243 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974244 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974245 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974244 h1) (fun h1 : term369 = True => @lem1974243)). Qed.
Lemma lem1974246 : term369 = True.
Proof. exact (EQ_MP (@lem1974245) (@lem1974243)). Qed.
Lemma lem1974247 : term368 = True.
Proof. exact (TRANS (@lem1974242) (@lem1974246)). Qed.
Lemma lem1974248 : True = term368.
Proof. exact (SYM (@lem1974247)). Qed.
Lemma lem1974249 : term368.
Proof. exact (EQ_MP (@lem1974248) (@lem0)). Qed.
Lemma lem1974250 (y : real) (x : real) (h1 : term835 y x) : term380 x.
Proof. exact (conj (@lem1974249) (@lem1974239 y x h1)). Qed.
Lemma lem1974252 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1974253 (x : real) : term382 x.
Proof. exact (@lem1974252 term71 (term52 x)). Qed.
Lemma lem1974254 (y : real) (x : real) (h1 : term835 y x) : term383 x.
Proof. exact (@lem1974253 x (@lem1974250 y x h1)). Qed.
Lemma lem1974255 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1974256 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974257 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1974256) (@lem1974255 x)). Qed.
Lemma lem1974258 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974259 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1974257 x) (@lem1974258)). Qed.
Lemma lem1974260 (y : real) (x : real) (h1 : term835 y x) : term177 x.
Proof. exact (EQ_MP (@lem1974259 x) (@lem1974254 y x h1)). Qed.
Lemma lem1974261 (y : real) (x : real) (h1 : term835 y x) : term436 x.
Proof. exact (conj (@lem1974260 y x h1) (@lem1974170 y x h1)). Qed.
Lemma lem1974263 (x : real) (y : real) : term439 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1974264 (x : real) : term440 x.
Proof. exact (@lem1974263 (term52 x) x). Qed.
Lemma lem1974265 (y : real) (x : real) (h1 : term835 y x) : term396 x.
Proof. exact (@lem1974264 x (@lem1974261 y x h1)). Qed.
Lemma lem1974266 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1974268 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1974269 : term122 = term121.
Proof. exact (@lem1974268 term22). Qed.
Lemma lem1974270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974271 : term123 = term124.
Proof. exact (MK_COMB (@lem1974270) (@lem1974269)). Qed.
Lemma lem1974272 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1974273 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1974271) (@lem1974272 x)). Qed.
Lemma lem1974274 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1974266 x) (@lem1974273 x)). Qed.
Lemma lem1974275 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1974276 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1974274 x) (@lem1974275 x)). Qed.
Lemma lem1974277 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974278 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1974277) (@lem1974276 x)). Qed.
Lemma lem1974279 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974280 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1974278 x) (@lem1974279)). Qed.
Lemma lem1974281 (y : real) (x : real) (h1 : term835 y x) : term145.
Proof. exact (EQ_MP (@lem1974280 x) (@lem1974265 y x h1)). Qed.
Lemma lem1974283 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974284 : term145 = term152.
Proof. exact (@lem1974283 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1974285 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1974286 : term145 = False.
Proof. exact (TRANS (@lem1974284) (@lem1974285)). Qed.
Lemma lem1974287 (y : real) (x : real) (h1 : term835 y x) : False.
Proof. exact (EQ_MP (@lem1974286) (@lem1974281 y x h1)). Qed.
Lemma lem1974288 (x : real) (y : real) (h1 : term836 x y) : term836 x y.
Proof. exact (h1). Qed.
Lemma lem1974289 (x : real) (y : real) (h1 : term836 x y) : term834 x y.
Proof. exact (proj2 (@lem1974288 x y h1)). Qed.
Lemma lem1974291 (x : real) (y : real) (h1 : term836 x y) : term436 y.
Proof. exact (proj2 (@lem1974289 x y h1)). Qed.
Lemma lem1974293 (x : real) (y : real) (h1 : term836 x y) : term435 y.
Proof. exact (proj2 (@lem1974291 x y h1)). Qed.
Lemma lem1974294 (x : real) (y : real) (h1 : term836 x y) : term177 y.
Proof. exact (proj1 (@lem1974291 x y h1)). Qed.
Lemma lem1974296 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974297 : term368 = term369.
Proof. exact (@lem1974296 (NUMERAL 0) term22). Qed.
Lemma lem1974298 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974299 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974300 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974299 h1) (fun h1 : term369 = True => @lem1974298)). Qed.
Lemma lem1974301 : term369 = True.
Proof. exact (EQ_MP (@lem1974300) (@lem1974298)). Qed.
Lemma lem1974302 : term368 = True.
Proof. exact (TRANS (@lem1974297) (@lem1974301)). Qed.
Lemma lem1974303 : True = term368.
Proof. exact (SYM (@lem1974302)). Qed.
Lemma lem1974304 : term368.
Proof. exact (EQ_MP (@lem1974303) (@lem0)). Qed.
Lemma lem1974305 (x : real) (y : real) (h1 : term836 x y) : term437 y.
Proof. exact (conj (@lem1974304) (@lem1974293 x y h1)). Qed.
Lemma lem1974307 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1974308 (y : real) : term438 y.
Proof. exact (@lem1974307 term71 y). Qed.
Lemma lem1974309 (x : real) (y : real) (h1 : term836 x y) : term434 y.
Proof. exact (@lem1974308 y (@lem1974305 x y h1)). Qed.
Lemma lem1974310 (y : real) : (term199 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1974311 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974312 (y : real) : (term433 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1974311) (@lem1974310 y)). Qed.
Lemma lem1974313 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974314 (y : real) : (term434 y) = (term435 y).
Proof. exact (MK_COMB (@lem1974312 y) (@lem1974313)). Qed.
Lemma lem1974315 (x : real) (y : real) (h1 : term836 x y) : term435 y.
Proof. exact (EQ_MP (@lem1974314 y) (@lem1974309 x y h1)). Qed.
Lemma lem1974317 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974318 : term368 = term369.
Proof. exact (@lem1974317 (NUMERAL 0) term22). Qed.
Lemma lem1974319 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1974320 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1974321 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1974320 h1) (fun h1 : term369 = True => @lem1974319)). Qed.
Lemma lem1974322 : term369 = True.
Proof. exact (EQ_MP (@lem1974321) (@lem1974319)). Qed.
Lemma lem1974323 : term368 = True.
Proof. exact (TRANS (@lem1974318) (@lem1974322)). Qed.
Lemma lem1974324 : True = term368.
Proof. exact (SYM (@lem1974323)). Qed.
Lemma lem1974325 : term368.
Proof. exact (EQ_MP (@lem1974324) (@lem0)). Qed.
Lemma lem1974326 (x : real) (y : real) (h1 : term836 x y) : term380 y.
Proof. exact (conj (@lem1974325) (@lem1974294 x y h1)). Qed.
Lemma lem1974328 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1974329 (y : real) : term382 y.
Proof. exact (@lem1974328 term71 (term52 y)). Qed.
Lemma lem1974330 (x : real) (y : real) (h1 : term836 x y) : term383 y.
Proof. exact (@lem1974329 y (@lem1974326 x y h1)). Qed.
Lemma lem1974331 (y : real) : (term384 y) = (term52 y).
Proof. exact (@lem1483460 (term52 y)). Qed.
Lemma lem1974332 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974333 (y : real) : (term385 y) = (term176 y).
Proof. exact (MK_COMB (@lem1974332) (@lem1974331 y)). Qed.
Lemma lem1974334 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974335 (y : real) : (term383 y) = (term177 y).
Proof. exact (MK_COMB (@lem1974333 y) (@lem1974334)). Qed.
Lemma lem1974336 (x : real) (y : real) (h1 : term836 x y) : term177 y.
Proof. exact (EQ_MP (@lem1974335 y) (@lem1974330 x y h1)). Qed.
Lemma lem1974337 (x : real) (y : real) (h1 : term836 x y) : term436 y.
Proof. exact (conj (@lem1974336 x y h1) (@lem1974315 x y h1)). Qed.
Lemma lem1974339 (x : real) (y : real) : term439 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1974340 (y : real) : term440 y.
Proof. exact (@lem1974339 (term52 y) y). Qed.
Lemma lem1974341 (x : real) (y : real) (h1 : term836 x y) : term396 y.
Proof. exact (@lem1974340 y (@lem1974337 x y h1)). Qed.
Lemma lem1974342 (y : real) : (term320 y) = (term321 y).
Proof. exact (@lem1483440 term16 y). Qed.
Lemma lem1974344 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1974345 : term122 = term121.
Proof. exact (@lem1974344 term22). Qed.
Lemma lem1974346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974347 : term123 = term124.
Proof. exact (MK_COMB (@lem1974346) (@lem1974345)). Qed.
Lemma lem1974348 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1974349 (y : real) : (term321 y) = (term322 y).
Proof. exact (MK_COMB (@lem1974347) (@lem1974348 y)). Qed.
Lemma lem1974350 (y : real) : (term320 y) = (term322 y).
Proof. exact (TRANS (@lem1974342 y) (@lem1974349 y)). Qed.
Lemma lem1974351 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1974352 (y : real) : (term320 y) = term121.
Proof. exact (TRANS (@lem1974350 y) (@lem1974351 y)). Qed.
Lemma lem1974353 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974354 (y : real) : (term397 y) = term143.
Proof. exact (MK_COMB (@lem1974353) (@lem1974352 y)). Qed.
Lemma lem1974355 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974356 (y : real) : (term396 y) = term145.
Proof. exact (MK_COMB (@lem1974354 y) (@lem1974355)). Qed.
Lemma lem1974357 (x : real) (y : real) (h1 : term836 x y) : term145.
Proof. exact (EQ_MP (@lem1974356 y) (@lem1974341 x y h1)). Qed.
Lemma lem1974359 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1974360 : term145 = term152.
Proof. exact (@lem1974359 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1974361 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1974362 : term145 = False.
Proof. exact (TRANS (@lem1974360) (@lem1974361)). Qed.
Lemma lem1974363 (x : real) (y : real) (h1 : term836 x y) : False.
Proof. exact (EQ_MP (@lem1974362) (@lem1974357 x y h1)). Qed.
Lemma lem1974364 (x : real) (y : real) (h1 : term832 x y) : False.
Proof. exact (or_elim (@lem1974142 x y h1) (fun h0 : term835 y x => @lem1974287 y x h0) (fun h0 : term836 x y => @lem1974363 x y h0)). Qed.
Lemma lem1974366 (x : real) (y : real) (h1 : term832 x y) : term832 x y.
Proof. exact (h1). Qed.
Lemma lem1974367 (x : real) (y : real) (h1 : term832 x y) : (term832 x y) = False.
Proof. exact (prop_ext (fun h2 : term832 x y => @lem1974364 x y h1) (fun h2 : False => @lem1974366 x y h1)). Qed.
Lemma lem1974368 (x : real) (y : real) (h1 : term832 x y) : False.
Proof. exact (EQ_MP (@lem1974367 x y h1) (@lem1974366 x y h1)). Qed.
Lemma lem1974369 (x : real) (y : real) (h1 : term812 x y) : term812 x y.
Proof. exact (h1). Qed.
Lemma lem1974370 (x : real) (y : real) (h1 : term812 x y) : term832 x y.
Proof. exact (EQ_MP (@lem1974132 x y) (@lem1974369 x y h1)). Qed.
Lemma lem1974371 (x : real) (y : real) (h1 : term812 x y) : (term832 x y) = False.
Proof. exact (prop_ext (fun h2 : term832 x y => @lem1974368 x y h2) (fun h2 : False => @lem1974370 x y h1)). Qed.
Lemma lem1974372 (x : real) (y : real) (h1 : term812 x y) : False.
Proof. exact (EQ_MP (@lem1974371 x y h1) (@lem1974370 x y h1)). Qed.
Lemma lem1974373 (x : real) (y : real) : term837 x y.
Proof. exact (fun h0 : term812 x y => @lem1974372 x y h0). Qed.
Lemma lem1974374 (x : real) (y : real) : term838 x y.
Proof. exact (@lem1386578 (term839 x y)). Qed.
Lemma lem1974375 (x : real) (y : real) : term839 x y.
Proof. exact (@lem1974374 x y (@lem1974373 x y)). Qed.
Lemma lem1974376 (x : real) (y : real) (h1 : real_le x y) : term813 x y.
Proof. exact (@lem1974375 x y (@lem1973328 x y h1)). Qed.
Lemma lem1974377 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) : term809 x y.
Proof. exact (@lem1974376 x y h2 (@lem1973201 x h1)). Qed.
Lemma lem1974378 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term805 x y.
Proof. exact (@lem1974377 x y h1 h3 (@lem1972971 y h2)). Qed.
Lemma lem1974379 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term797 x y.
Proof. exact (@lem1973871 x y (@lem1974378 x y h1 h2 h3)). Qed.
Lemma lem1974380 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term795 x y.
Proof. exact (EQ_MP (@lem1973868 x y) (@lem1974379 x y h1 h2 h3)). Qed.
Lemma lem1974381 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term840 x y.
Proof. exact (ex_intro (term841 x y) (term842 x y) (@lem1974380 x y h1 h2 h3)). Qed.
Lemma lem1974382 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term790 x y.
Proof. exact (@lem1973852 x y (@lem1974381 x y h1 h2 h3)). Qed.
Lemma lem1974383 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term783 x y.
Proof. exact (EQ_MP (@lem1973821 x y) (@lem1974382 x y h1 h2 h3)). Qed.
Lemma lem1974384 (x : real) (y : real) (h1 : term171 x) (h2 : term171 y) (h3 : real_le x y) : term673 x y.
Proof. exact (EQ_MP (@lem1973806 x y) (@lem1974383 x y h1 h2 h3)). Qed.
Lemma lem1974385 (x : real) (y : real) (h1 : term169 x y) : term169 x y.
Proof. exact (h1). Qed.
Lemma lem1974386 (x : real) (y : real) (h1 : term169 x y) : (term170 x y) = (real_sub y x).
Proof. exact (@lem1971163 y x (@lem1974385 x y h1)). Qed.
Lemma lem1974392 (x : real) : term843 x.
Proof. exact (@lem1948346 x). Qed.
Lemma lem1974393 (x : real) : (term843 x) = ((term844 x) = (term178 x)).
Proof. exact (eq_refl (term843 x)). Qed.
Lemma lem1974397 (x : real) : term845 x.
Proof. exact (@lem82 (term178 x)). Qed.
Lemma lem1974399 (y : real) : (term178 y) = ((term178 y) = True).
Proof. exact (@lem7 (term178 y)). Qed.
Lemma lem1974402 (y : real) (x : real) : term400 y x.
Proof. exact (fun h0 : term169 x y => @lem1974386 x y h0). Qed.
Lemma lem1974403 (y : real) (x : real) : term846 y x.
Proof. exact (@lem1974402 (sqrt y) (sqrt x)). Qed.
Lemma lem1974407 (x : real) : (term844 x) = (term178 x).
Proof. exact (EQ_MP (@lem1974393 x) (@lem1974392 x)). Qed.
Lemma lem1974409 (x : real) (h1 : term171 x) : (term178 x) = False.
Proof. exact (@lem1974397 x (@lem1973201 x h1)). Qed.
Lemma lem1974410 (x : real) (h1 : term171 x) : (term844 x) = False.
Proof. exact (TRANS (@lem1974407 x) (@lem1974409 x h1)). Qed.
Lemma lem1974411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1974412 (x : real) (h1 : term171 x) : (term847 x) = (~ False).
Proof. exact (MK_COMB (@lem1974411) (@lem1974410 x h1)). Qed.
Lemma lem1974414 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1974415 (x : real) (h1 : term171 x) : (term847 x) = True.
Proof. exact (TRANS (@lem1974412 x h1) (@lem1974414)). Qed.
Lemma lem1974416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974417 (x : real) (h1 : term171 x) : (term848 x) = (and True).
Proof. exact (MK_COMB (@lem1974416) (@lem1974415 x h1)). Qed.
Lemma lem1974419 (x : real) : (term844 x) = (term178 x).
Proof. exact (EQ_MP (@lem1974393 x) (@lem1974392 x)). Qed.
Lemma lem1974420 (y : real) : (term844 y) = (term178 y).
Proof. exact (@lem1974419 y). Qed.
Lemma lem1974422 (y : real) (h1 : term178 y) : (term178 y) = True.
Proof. exact (EQ_MP (@lem1974399 y) (@lem1972970 y h1)). Qed.
Lemma lem1974423 (y : real) (h1 : term178 y) : (term844 y) = True.
Proof. exact (TRANS (@lem1974420 y) (@lem1974422 y h1)). Qed.
Lemma lem1974424 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term849 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1974417 x h1) (@lem1974423 y h2)). Qed.
Lemma lem1974426 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1974427 : (True /\ True) = True.
Proof. exact (@lem1974426 True). Qed.
Lemma lem1974428 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term849 x y) = True.
Proof. exact (TRANS (@lem1974424 x y h1 h2) (@lem1974427)). Qed.
Lemma lem1974429 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : True = (term849 x y).
Proof. exact (SYM (@lem1974428 x y h1 h2)). Qed.
Lemma lem1974430 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : term849 x y.
Proof. exact (EQ_MP (@lem1974429 x y h1 h2) (@lem0)). Qed.
Lemma lem1974431 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term709 x y) = (term850 y x).
Proof. exact (@lem1974403 y x (@lem1974430 x y h1 h2)). Qed.
Lemma lem1974432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1974433 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term710 x y) = (term851 y x).
Proof. exact (MK_COMB (@lem1974432) (@lem1974431 x y h1 h2)). Qed.
Lemma lem1974435 (y : real) (x : real) : term400 y x.
Proof. exact (fun h0 : term169 x y => @lem1974386 x y h0). Qed.
Lemma lem1974439 (x : real) (h1 : term171 x) : (term178 x) = False.
Proof. exact (@lem1974397 x (@lem1973201 x h1)). Qed.
Lemma lem1974440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1974441 (x : real) (h1 : term171 x) : (term171 x) = (~ False).
Proof. exact (MK_COMB (@lem1974440) (@lem1974439 x h1)). Qed.
Lemma lem1974443 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1974444 (x : real) (h1 : term171 x) : (term171 x) = True.
Proof. exact (TRANS (@lem1974441 x h1) (@lem1974443)). Qed.
Lemma lem1974445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974446 (x : real) (h1 : term171 x) : (term185 x) = (and True).
Proof. exact (MK_COMB (@lem1974445) (@lem1974444 x h1)). Qed.
Lemma lem1974448 (y : real) (h1 : term178 y) : (term178 y) = True.
Proof. exact (EQ_MP (@lem1974399 y) (@lem1972970 y h1)). Qed.
Lemma lem1974449 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term169 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1974446 x h1) (@lem1974448 y h2)). Qed.
Lemma lem1974451 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1974452 : (True /\ True) = True.
Proof. exact (@lem1974451 True). Qed.
Lemma lem1974453 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term169 x y) = True.
Proof. exact (TRANS (@lem1974449 x y h1 h2) (@lem1974452)). Qed.
Lemma lem1974454 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : True = (term169 x y).
Proof. exact (SYM (@lem1974453 x y h1 h2)). Qed.
Lemma lem1974455 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : term169 x y.
Proof. exact (EQ_MP (@lem1974454 x y h1 h2) (@lem0)). Qed.
Lemma lem1974456 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term170 x y) = (real_sub y x).
Proof. exact (@lem1974435 y x (@lem1974455 x y h1 h2)). Qed.
Lemma lem1974457 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1974458 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term711 x y) = (term852 y x).
Proof. exact (MK_COMB (@lem1974457) (@lem1974456 x y h1 h2)). Qed.
Lemma lem1974459 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1974460 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term712 x y) = (term853 y x).
Proof. exact (MK_COMB (@lem1974459) (@lem1974458 x y h1 h2)). Qed.
Lemma lem1974461 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term673 x y) = (term854 y x).
Proof. exact (MK_COMB (@lem1974433 x y h1 h2) (@lem1974460 x y h1 h2)). Qed.
Lemma lem1974462 (x : real) (y : real) (h1 : term171 x) (h2 : term178 y) : (term854 y x) = (term673 x y).
Proof. exact (SYM (@lem1974461 x y h1 h2)). Qed.
Lemma lem1974464 (x : real) (y : real) : term162 x y.
Proof. exact (EQ_MP (@lem1970213 x y) (@lem1970212 x y)). Qed.
Lemma lem1974465 (y : real) (x : real) : term855 y x.
Proof. exact (@lem1974464 (term850 y x) (term852 y x)). Qed.
Lemma lem1974469 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (@lem1970187 x y (@lem1970186 x y)). Qed.
Lemma lem1974470 (x : real) (y : real) : (term856 x y) = (term857 x y).
Proof. exact (@lem1974469 (term3 x) (sqrt y)). Qed.
Lemma lem1974471 : term858 = term858.
Proof. exact (eq_refl term858). Qed.
Lemma lem1974472 (x : real) (y : real) : (term157 x y) = (term859 x y).
Proof. exact (MK_COMB (@lem1974471) (@lem1974470 x y)). Qed.
Lemma lem1974473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1974474 (x : real) (y : real) : (term860 x y) = (term861 x y).
Proof. exact (MK_COMB (@lem1974473) (@lem1974472 x y)). Qed.
Lemma lem1974476 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (@lem1970187 x y (@lem1970186 x y)). Qed.
Lemma lem1974477 (y : real) (x : real) : (term862 y x) = (term863 y x).
Proof. exact (@lem1974476 (sqrt y) (sqrt x)). Qed.
Lemma lem1974478 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1974479 (y : real) (x : real) : (term864 y x) = (term865 y x).
Proof. exact (MK_COMB (@lem1974478) (@lem1974477 y x)). Qed.
Lemma lem1974480 (y : real) (x : real) : (term852 y x) = (term852 y x).
Proof. exact (eq_refl (term852 y x)). Qed.
Lemma lem1974481 (y : real) (x : real) : (term866 y x) = (term867 y x).
Proof. exact (MK_COMB (@lem1974479 y x) (@lem1974480 y x)). Qed.
Lemma lem1974482 (y : real) (x : real) : (term868 y x) = (term869 y x).
Proof. exact (MK_COMB (@lem1974474 x y) (@lem1974481 y x)). Qed.
Lemma lem1974485 (y : real) (x : real) : (term869 y x) = (term868 y x).
Proof. exact (SYM (@lem1974482 y x)). Qed.
Lemma lem1974489 (x : real) : (term6 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1969857 x) (@lem1969856 x)). Qed.
Lemma lem1974490 (x : real) : (term870 x) = (term1 x).
Proof. exact (@lem1974489 (real_neg x)). Qed.
Lemma lem1974491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1974492 (x : real) : (term871 x) = (term872 x).
Proof. exact (MK_COMB (@lem1974491) (@lem1974490 x)). Qed.
Lemma lem1974494 (x : real) : (term6 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1969857 x) (@lem1969856 x)). Qed.
Lemma lem1974495 (y : real) : (term6 y) = (real_abs y).
Proof. exact (@lem1974494 y). Qed.
Lemma lem1974496 (x : real) (y : real) : (term873 x y) = (term874 x y).
Proof. exact (MK_COMB (@lem1974492 x) (@lem1974495 y)). Qed.
Lemma lem1974497 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974498 (x : real) (y : real) : (term875 x y) = (term876 x y).
Proof. exact (MK_COMB (@lem1974497) (@lem1974496 x y)). Qed.
Lemma lem1974499 (x : real) (y : real) : (term877 x y) = (term877 x y).
Proof. exact (eq_refl (term877 x y)). Qed.
Lemma lem1974500 (x : real) (y : real) : (term857 x y) = (term878 x y).
Proof. exact (MK_COMB (@lem1974498 x y) (@lem1974499 x y)). Qed.
Lemma lem1974501 : term858 = term858.
Proof. exact (eq_refl term858). Qed.
Lemma lem1974502 (x : real) (y : real) : (term859 x y) = (term879 x y).
Proof. exact (MK_COMB (@lem1974501) (@lem1974500 x y)). Qed.
Lemma lem1974503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1974504 (x : real) (y : real) : (term861 x y) = (term880 x y).
Proof. exact (MK_COMB (@lem1974503) (@lem1974502 x y)). Qed.
Lemma lem1974506 (x : real) : (term6 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1969857 x) (@lem1969856 x)). Qed.
Lemma lem1974507 (y : real) : (term6 y) = (real_abs y).
Proof. exact (@lem1974506 y). Qed.
Lemma lem1974508 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1974509 (y : real) : (term881 y) = (term418 y).
Proof. exact (MK_COMB (@lem1974508) (@lem1974507 y)). Qed.
Lemma lem1974511 (x : real) : (term6 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1969857 x) (@lem1969856 x)). Qed.
Lemma lem1974512 (y : real) (x : real) : (term882 y x) = (term883 y x).
Proof. exact (MK_COMB (@lem1974509 y) (@lem1974511 x)). Qed.
Lemma lem1974513 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974514 (y : real) (x : real) : (term884 y x) = (term885 y x).
Proof. exact (MK_COMB (@lem1974513) (@lem1974512 y x)). Qed.
Lemma lem1974515 (y : real) (x : real) : (term886 y x) = (term886 y x).
Proof. exact (eq_refl (term886 y x)). Qed.
Lemma lem1974516 (y : real) (x : real) : (term863 y x) = (term887 y x).
Proof. exact (MK_COMB (@lem1974514 y x) (@lem1974515 y x)). Qed.
Lemma lem1974517 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1974518 (y : real) (x : real) : (term865 y x) = (term888 y x).
Proof. exact (MK_COMB (@lem1974517) (@lem1974516 y x)). Qed.
Lemma lem1974519 (y : real) (x : real) : (term852 y x) = (term852 y x).
Proof. exact (eq_refl (term852 y x)). Qed.
Lemma lem1974520 (y : real) (x : real) : (term867 y x) = (term889 y x).
Proof. exact (MK_COMB (@lem1974518 y x) (@lem1974519 y x)). Qed.
Lemma lem1974521 (y : real) (x : real) : (term869 y x) = (term890 y x).
Proof. exact (MK_COMB (@lem1974504 x y) (@lem1974520 y x)). Qed.
Lemma lem1974524 (y : real) (x : real) : (term890 y x) = (term869 y x).
Proof. exact (SYM (@lem1974521 y x)). Qed.
Lemma lem1974528 (x : real) : (term1 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1969851 x) (@lem1969850 x)). Qed.
Lemma lem1974529 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1974530 (x : real) : (term872 x) = (term418 x).
Proof. exact (MK_COMB (@lem1974529) (@lem1974528 x)). Qed.
Lemma lem1974531 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1974532 (x : real) (y : real) : (term874 x y) = (term883 x y).
Proof. exact (MK_COMB (@lem1974530 x) (@lem1974531 y)). Qed.
Lemma lem1974533 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974534 (x : real) (y : real) : (term876 x y) = (term885 x y).
Proof. exact (MK_COMB (@lem1974533) (@lem1974532 x y)). Qed.
Lemma lem1974536 (x : real) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem1969854 x) (@lem1969853 x)). Qed.
Lemma lem1974537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974538 (x : real) : (term891 x) = (term892 x).
Proof. exact (MK_COMB (@lem1974537) (@lem1974536 x)). Qed.
Lemma lem1974539 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (eq_refl (sqrt y)). Qed.
Lemma lem1974540 (x : real) (y : real) : (term893 x y) = (term894 x y).
Proof. exact (MK_COMB (@lem1974538 x) (@lem1974539 y)). Qed.
Lemma lem1974541 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1974542 (x : real) (y : real) : (term877 x y) = (term895 x y).
Proof. exact (MK_COMB (@lem1974541) (@lem1974540 x y)). Qed.
Lemma lem1974543 (x : real) (y : real) : (term878 x y) = (term896 x y).
Proof. exact (MK_COMB (@lem1974534 x y) (@lem1974542 x y)). Qed.
Lemma lem1974544 : term858 = term858.
Proof. exact (eq_refl term858). Qed.
Lemma lem1974545 (x : real) (y : real) : (term879 x y) = (term897 x y).
Proof. exact (MK_COMB (@lem1974544) (@lem1974543 x y)). Qed.
Lemma lem1974546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1974547 (x : real) (y : real) : (term880 x y) = (term898 x y).
Proof. exact (MK_COMB (@lem1974546) (@lem1974545 x y)). Qed.
Lemma lem1974548 (y : real) (x : real) : (term889 y x) = (term889 y x).
Proof. exact (eq_refl (term889 y x)). Qed.
Lemma lem1974549 (y : real) (x : real) : (term890 y x) = (term899 y x).
Proof. exact (MK_COMB (@lem1974547 x y) (@lem1974548 y x)). Qed.
Lemma lem1974552 (y : real) (x : real) : (term899 y x) = (term890 y x).
Proof. exact (SYM (@lem1974549 y x)). Qed.
Lemma lem1974573 (y : real) (x : real) : (term900 y x) = (term901 y x).
Proof. exact (@lem17362 (term897 x y) (term889 y x)). Qed.
Lemma lem1974575 (y : real) : (term742 y) = (term742 y).
Proof. exact (eq_refl (term742 y)). Qed.
Lemma lem1974576 (y : real) (x : real) : (term902 y x) = (term903 y x).
Proof. exact (MK_COMB (@lem1974575 y) (@lem1974573 y x)). Qed.
Lemma lem1974577 (y : real) (x : real) : (term904 y x) = (term902 y x).
Proof. exact (@lem17362 (term178 y) (term899 y x)). Qed.
Lemma lem1974578 (y : real) (x : real) : (term904 y x) = (term903 y x).
Proof. exact (TRANS (@lem1974577 y x) (@lem1974576 y x)). Qed.
Lemma lem1974580 (x : real) : (term185 x) = (term185 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem1974581 (y : real) (x : real) : (term905 y x) = (term906 y x).
Proof. exact (MK_COMB (@lem1974580 x) (@lem1974578 y x)). Qed.
Lemma lem1974582 (y : real) (x : real) : (term907 y x) = (term905 y x).
Proof. exact (@lem17362 (term171 x) (term908 y x)). Qed.
Lemma lem1974583 (y : real) (x : real) : (term907 y x) = (term906 y x).
Proof. exact (TRANS (@lem1974582 y x) (@lem1974581 y x)). Qed.
Lemma lem1974585 (x : real) (y : real) : (term746 x y) = (term746 x y).
Proof. exact (eq_refl (term746 x y)). Qed.
Lemma lem1974586 (y : real) (x : real) : (term909 y x) = (term910 y x).
Proof. exact (MK_COMB (@lem1974585 x y) (@lem1974583 y x)). Qed.
Lemma lem1974587 (y : real) (x : real) : (term911 y x) = (term909 y x).
Proof. exact (@lem17362 (real_le x y) (term912 y x)). Qed.
Lemma lem1974611 (y : real) (x : real) : (term911 y x) = (term910 y x).
Proof. exact (TRANS (@lem1974587 y x) (@lem1974586 y x)). Qed.
Lemma lem1974612 (y : real) (x : real) : (real_le x y) = (term251 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1974618 (y : real) (x : real) : (real_sub y x) = (term40 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1974623 (x : real) (y : real) : (term40 y x) = (term190 x y).
Proof. exact (@lem1483488 (term52 x) y). Qed.
Lemma lem1974625 (x : real) (y : real) : (real_sub y x) = (term190 x y).
Proof. exact (TRANS (@lem1974618 y x) (@lem1974623 x y)). Qed.
Lemma lem1974626 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1974627 (x : real) (y : real) : (term751 y x) = (term603 x y).
Proof. exact (MK_COMB (@lem1974626) (@lem1974625 x y)). Qed.
Lemma lem1974628 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974629 (x : real) (y : real) : (term251 y x) = (term604 x y).
Proof. exact (MK_COMB (@lem1974627 x y) (@lem1974628)). Qed.
Lemma lem1974630 (x : real) (y : real) : (real_le x y) = (term604 x y).
Proof. exact (TRANS (@lem1974612 y x) (@lem1974629 x y)). Qed.
Lemma lem1974631 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483533 term121 x). Qed.
Lemma lem1974637 (x : real) : (term173 x) = (term174 x).
Proof. exact (@lem1483519 term121 x). Qed.
Lemma lem1974642 (x : real) : (term174 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1974644 (x : real) : (term173 x) = (term52 x).
Proof. exact (TRANS (@lem1974637 x) (@lem1974642 x)). Qed.
Lemma lem1974645 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974646 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1974645) (@lem1974644 x)). Qed.
Lemma lem1974647 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974648 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1974646 x) (@lem1974647)). Qed.
Lemma lem1974649 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1974631 x) (@lem1974648 x)). Qed.
Lemma lem1974650 (y : real) : (term178 y) = (term179 y).
Proof. exact (@lem1483523 y term121). Qed.
Lemma lem1974656 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483519 y term121). Qed.
Lemma lem1974658 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1974659 : term139 = term121.
Proof. exact (@lem1974658 term22). Qed.
Lemma lem1974660 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1974661 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem1974660 y) (@lem1974659)). Qed.
Lemma lem1974662 (y : real) : (term182 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1974663 (y : real) : (term181 y) = y.
Proof. exact (TRANS (@lem1974661 y) (@lem1974662 y)). Qed.
Lemma lem1974665 (y : real) : (term180 y) = y.
Proof. exact (TRANS (@lem1974656 y) (@lem1974663 y)). Qed.
Lemma lem1974666 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1974667 (y : real) : (term183 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1974666) (@lem1974665 y)). Qed.
Lemma lem1974668 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974669 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1974667 y) (@lem1974668)). Qed.
Lemma lem1974670 (y : real) : (term178 y) = (term184 y).
Proof. exact (TRANS (@lem1974650 y) (@lem1974669 y)). Qed.
Lemma lem1974671 (x : real) (y : real) : (term897 x y) = (term913 x y).
Proof. exact (@lem1483523 (term896 x y) term121). Qed.
Lemma lem1974672 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974673 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (eq_refl (sqrt y)). Qed.
Lemma lem1974680 (x : real) : (term4 x) = (term914 x).
Proof. exact (@lem1483512 (sqrt x)). Qed.
Lemma lem1974681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974682 (x : real) : (term892 x) = (term915 x).
Proof. exact (MK_COMB (@lem1974681) (@lem1974680 x)). Qed.
Lemma lem1974683 (x : real) (y : real) : (term894 x y) = (term916 x y).
Proof. exact (MK_COMB (@lem1974682 x) (@lem1974673 y)). Qed.
Lemma lem1974688 (x : real) (y : real) : (term916 x y) = (term917 x y).
Proof. exact (@lem1483472 term16 (sqrt x) (sqrt y)). Qed.
Lemma lem1974689 (x : real) (y : real) : (term894 x y) = (term917 x y).
Proof. exact (TRANS (@lem1974683 x y) (@lem1974688 x y)). Qed.
Lemma lem1974692 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1974693 (x : real) (y : real) : (term895 x y) = (term918 x y).
Proof. exact (MK_COMB (@lem1974692) (@lem1974689 x y)). Qed.
Lemma lem1974694 (x : real) (y : real) : (term918 x y) = (term919 x y).
Proof. exact (@lem1483476 term17 term16 (term920 x y)). Qed.
Lemma lem1974696 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1974697 : term922 = term923.
Proof. exact (@lem1974696 term23 term22). Qed.
Lemma lem1974698 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1974699 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1974700 : term925 = term23.
Proof. exact (EQ_MP (@lem1974699) (@lem1974698)). Qed.
Lemma lem1974701 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974702 : term926 = term17.
Proof. exact (MK_COMB (@lem1974701) (@lem1974700)). Qed.
Lemma lem1974703 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1974704 : term923 = term28.
Proof. exact (MK_COMB (@lem1974703) (@lem1974702)). Qed.
Lemma lem1974705 : term922 = term28.
Proof. exact (TRANS (@lem1974697) (@lem1974704)). Qed.
Lemma lem1974706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974707 : term927 = term30.
Proof. exact (MK_COMB (@lem1974706) (@lem1974705)). Qed.
Lemma lem1974708 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1974709 (x : real) (y : real) : (term919 x y) = (term928 x y).
Proof. exact (MK_COMB (@lem1974707) (@lem1974708 x y)). Qed.
Lemma lem1974710 (x : real) (y : real) : (term918 x y) = (term928 x y).
Proof. exact (TRANS (@lem1974694 x y) (@lem1974709 x y)). Qed.
Lemma lem1974711 (x : real) (y : real) : (term895 x y) = (term928 x y).
Proof. exact (TRANS (@lem1974693 x y) (@lem1974710 x y)). Qed.
Lemma lem1974720 (x : real) (y : real) : (term885 x y) = (term885 x y).
Proof. exact (eq_refl (term885 x y)). Qed.
Lemma lem1974721 (x : real) (y : real) : (term896 x y) = (term929 x y).
Proof. exact (MK_COMB (@lem1974720 x y) (@lem1974711 x y)). Qed.
Lemma lem1974722 (x : real) (y : real) : (term929 x y) = (term930 x y).
Proof. exact (@lem1483519 (term883 x y) (term928 x y)). Qed.
Lemma lem1974723 (x : real) (y : real) : (term931 x y) = (term932 x y).
Proof. exact (@lem1483476 term16 term28 (term920 x y)). Qed.
Lemma lem1974725 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1974726 : term107 = term27.
Proof. exact (@lem1974725 term22 term23). Qed.
Lemma lem1974727 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1974728 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1974729 : term26 = term23.
Proof. exact (EQ_MP (@lem1974728) (@lem1974727)). Qed.
Lemma lem1974730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974731 : term27 = term17.
Proof. exact (MK_COMB (@lem1974730) (@lem1974729)). Qed.
Lemma lem1974732 : term107 = term17.
Proof. exact (TRANS (@lem1974726) (@lem1974731)). Qed.
Lemma lem1974733 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974734 : term108 = term109.
Proof. exact (MK_COMB (@lem1974733) (@lem1974732)). Qed.
Lemma lem1974735 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1974736 (x : real) (y : real) : (term932 x y) = (term886 x y).
Proof. exact (MK_COMB (@lem1974734) (@lem1974735 x y)). Qed.
Lemma lem1974737 (x : real) (y : real) : (term931 x y) = (term886 x y).
Proof. exact (TRANS (@lem1974723 x y) (@lem1974736 x y)). Qed.
Lemma lem1974738 (x : real) (y : real) : (term933 x y) = (term933 x y).
Proof. exact (eq_refl (term933 x y)). Qed.
Lemma lem1974739 (x : real) (y : real) : (term930 x y) = (term934 x y).
Proof. exact (MK_COMB (@lem1974738 x y) (@lem1974737 x y)). Qed.
Lemma lem1974740 (x : real) (y : real) : (term934 x y) = (term935 x y).
Proof. exact (@lem1483488 (term886 x y) (term883 x y)). Qed.
Lemma lem1974741 (x : real) (y : real) : (term930 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974739 x y) (@lem1974740 x y)). Qed.
Lemma lem1974742 (x : real) (y : real) : (term929 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974722 x y) (@lem1974741 x y)). Qed.
Lemma lem1974743 (x : real) (y : real) : (term896 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974721 x y) (@lem1974742 x y)). Qed.
Lemma lem1974744 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974745 (x : real) (y : real) : (term936 x y) = (term937 x y).
Proof. exact (MK_COMB (@lem1974744) (@lem1974743 x y)). Qed.
Lemma lem1974746 (x : real) (y : real) : (term938 x y) = (term939 x y).
Proof. exact (MK_COMB (@lem1974745 x y) (@lem1974672)). Qed.
Lemma lem1974747 (x : real) (y : real) : (term939 x y) = (term940 x y).
Proof. exact (@lem1483519 (term935 x y) term121). Qed.
Lemma lem1974749 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1974750 : term139 = term121.
Proof. exact (@lem1974749 term22). Qed.
Lemma lem1974751 (x : real) (y : real) : (term941 x y) = (term941 x y).
Proof. exact (eq_refl (term941 x y)). Qed.
Lemma lem1974752 (x : real) (y : real) : (term940 x y) = (term942 x y).
Proof. exact (MK_COMB (@lem1974751 x y) (@lem1974750)). Qed.
Lemma lem1974753 (x : real) (y : real) : (term942 x y) = (term935 x y).
Proof. exact (@lem1483450 (term935 x y)). Qed.
Lemma lem1974754 (x : real) (y : real) : (term940 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974752 x y) (@lem1974753 x y)). Qed.
Lemma lem1974755 (x : real) (y : real) : (term939 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974747 x y) (@lem1974754 x y)). Qed.
Lemma lem1974756 (x : real) (y : real) : (term938 x y) = (term935 x y).
Proof. exact (TRANS (@lem1974746 x y) (@lem1974755 x y)). Qed.
Lemma lem1974757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1974758 (x : real) (y : real) : (term943 x y) = (term944 x y).
Proof. exact (MK_COMB (@lem1974757) (@lem1974756 x y)). Qed.
Lemma lem1974759 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974760 (x : real) (y : real) : (term913 x y) = (term945 x y).
Proof. exact (MK_COMB (@lem1974758 x y) (@lem1974759)). Qed.
Lemma lem1974761 (x : real) (y : real) : (term897 x y) = (term945 x y).
Proof. exact (TRANS (@lem1974671 x y) (@lem1974760 x y)). Qed.
Lemma lem1974762 (y : real) (x : real) : (term946 y x) = (term947 y x).
Proof. exact (@lem1483533 (term887 y x) (term852 y x)). Qed.
Lemma lem1974768 (y : real) (x : real) : (real_sub y x) = (term40 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1974773 (x : real) (y : real) : (term40 y x) = (term190 x y).
Proof. exact (@lem1483488 (term52 x) y). Qed.
Lemma lem1974775 (x : real) (y : real) : (real_sub y x) = (term190 x y).
Proof. exact (TRANS (@lem1974768 y x) (@lem1974773 x y)). Qed.
Lemma lem1974778 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1974779 (x : real) (y : real) : (term852 y x) = (term948 x y).
Proof. exact (MK_COMB (@lem1974778) (@lem1974775 x y)). Qed.
Lemma lem1974780 (x : real) (y : real) : (term948 x y) = (term949 x y).
Proof. exact (@lem1483508 (term52 x) term17 y). Qed.
Lemma lem1974781 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1974782 (x : real) : (term950 x) = (term951 x).
Proof. exact (@lem1483476 term17 term16 x). Qed.
Lemma lem1974784 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1974785 : term922 = term923.
Proof. exact (@lem1974784 term23 term22). Qed.
Lemma lem1974786 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1974787 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1974788 : term925 = term23.
Proof. exact (EQ_MP (@lem1974787) (@lem1974786)). Qed.
Lemma lem1974789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974790 : term926 = term17.
Proof. exact (MK_COMB (@lem1974789) (@lem1974788)). Qed.
Lemma lem1974791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1974792 : term923 = term28.
Proof. exact (MK_COMB (@lem1974791) (@lem1974790)). Qed.
Lemma lem1974793 : term922 = term28.
Proof. exact (TRANS (@lem1974785) (@lem1974792)). Qed.
Lemma lem1974794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974795 : term927 = term30.
Proof. exact (MK_COMB (@lem1974794) (@lem1974793)). Qed.
Lemma lem1974796 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1974797 (x : real) : (term951 x) = (term276 x).
Proof. exact (MK_COMB (@lem1974795) (@lem1974796 x)). Qed.
Lemma lem1974798 (x : real) : (term950 x) = (term276 x).
Proof. exact (TRANS (@lem1974782 x) (@lem1974797 x)). Qed.
Lemma lem1974799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1974800 (x : real) : (term952 x) = (term354 x).
Proof. exact (MK_COMB (@lem1974799) (@lem1974798 x)). Qed.
Lemma lem1974801 (x : real) (y : real) : (term949 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1974800 x) (@lem1974781 y)). Qed.
Lemma lem1974802 (x : real) (y : real) : (term948 x y) = (term355 x y).
Proof. exact (TRANS (@lem1974780 x y) (@lem1974801 x y)). Qed.
Lemma lem1974803 (x : real) (y : real) : (term852 y x) = (term355 x y).
Proof. exact (TRANS (@lem1974779 x y) (@lem1974802 x y)). Qed.
Lemma lem1974810 (x : real) (y : real) : (term920 y x) = (term920 x y).
Proof. exact (@lem1483474 (sqrt x) (sqrt y)). Qed.
Lemma lem1974813 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1974816 (x : real) (y : real) : (term886 y x) = (term886 x y).
Proof. exact (MK_COMB (@lem1974813) (@lem1974810 x y)). Qed.
Lemma lem1974823 (x : real) (y : real) : (term883 y x) = (term883 x y).
Proof. exact (@lem1483488 (real_abs x) (real_abs y)). Qed.
Lemma lem1974824 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974825 (x : real) (y : real) : (term885 y x) = (term885 x y).
Proof. exact (MK_COMB (@lem1974824) (@lem1974823 x y)). Qed.
Lemma lem1974826 (x : real) (y : real) : (term887 y x) = (term887 x y).
Proof. exact (MK_COMB (@lem1974825 x y) (@lem1974816 x y)). Qed.
Lemma lem1974827 (x : real) (y : real) : (term887 x y) = (term953 x y).
Proof. exact (@lem1483519 (term883 x y) (term886 x y)). Qed.
Lemma lem1974828 (x : real) (y : real) : (term954 x y) = (term955 x y).
Proof. exact (@lem1483476 term16 term17 (term920 x y)). Qed.
Lemma lem1974830 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1974831 : term20 = term21.
Proof. exact (@lem1974830 term22 term23). Qed.
Lemma lem1974832 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1974833 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1974834 : term26 = term23.
Proof. exact (EQ_MP (@lem1974833) (@lem1974832)). Qed.
Lemma lem1974835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974836 : term27 = term17.
Proof. exact (MK_COMB (@lem1974835) (@lem1974834)). Qed.
Lemma lem1974837 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1974838 : term21 = term28.
Proof. exact (MK_COMB (@lem1974837) (@lem1974836)). Qed.
Lemma lem1974839 : term20 = term28.
Proof. exact (TRANS (@lem1974831) (@lem1974838)). Qed.
Lemma lem1974840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974841 : term29 = term30.
Proof. exact (MK_COMB (@lem1974840) (@lem1974839)). Qed.
Lemma lem1974842 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1974843 (x : real) (y : real) : (term955 x y) = (term928 x y).
Proof. exact (MK_COMB (@lem1974841) (@lem1974842 x y)). Qed.
Lemma lem1974844 (x : real) (y : real) : (term954 x y) = (term928 x y).
Proof. exact (TRANS (@lem1974828 x y) (@lem1974843 x y)). Qed.
Lemma lem1974845 (x : real) (y : real) : (term933 x y) = (term933 x y).
Proof. exact (eq_refl (term933 x y)). Qed.
Lemma lem1974846 (x : real) (y : real) : (term953 x y) = (term956 x y).
Proof. exact (MK_COMB (@lem1974845 x y) (@lem1974844 x y)). Qed.
Lemma lem1974847 (x : real) (y : real) : (term956 x y) = (term957 x y).
Proof. exact (@lem1483488 (term928 x y) (term883 x y)). Qed.
Lemma lem1974848 (x : real) (y : real) : (term953 x y) = (term957 x y).
Proof. exact (TRANS (@lem1974846 x y) (@lem1974847 x y)). Qed.
Lemma lem1974849 (x : real) (y : real) : (term887 x y) = (term957 x y).
Proof. exact (TRANS (@lem1974827 x y) (@lem1974848 x y)). Qed.
Lemma lem1974850 (x : real) (y : real) : (term887 y x) = (term957 x y).
Proof. exact (TRANS (@lem1974826 x y) (@lem1974849 x y)). Qed.
Lemma lem1974851 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1974852 (x : real) (y : real) : (term958 y x) = (term959 x y).
Proof. exact (MK_COMB (@lem1974851) (@lem1974850 x y)). Qed.
Lemma lem1974853 (x : real) (y : real) : (term960 y x) = (term961 x y).
Proof. exact (MK_COMB (@lem1974852 x y) (@lem1974803 x y)). Qed.
Lemma lem1974854 (x : real) (y : real) : (term961 x y) = (term962 x y).
Proof. exact (@lem1483519 (term957 x y) (term355 x y)). Qed.
Lemma lem1974855 (x : real) (y : real) : (term963 x y) = (term964 x y).
Proof. exact (@lem1483508 (term276 x) term16 (term283 y)). Qed.
Lemma lem1974856 (y : real) : (term965 y) = (term966 y).
Proof. exact (@lem1483476 term16 term17 y). Qed.
Lemma lem1974858 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1974859 : term20 = term21.
Proof. exact (@lem1974858 term22 term23). Qed.
Lemma lem1974860 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1974861 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1974862 : term26 = term23.
Proof. exact (EQ_MP (@lem1974861) (@lem1974860)). Qed.
Lemma lem1974863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974864 : term27 = term17.
Proof. exact (MK_COMB (@lem1974863) (@lem1974862)). Qed.
Lemma lem1974865 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1974866 : term21 = term28.
Proof. exact (MK_COMB (@lem1974865) (@lem1974864)). Qed.
Lemma lem1974867 : term20 = term28.
Proof. exact (TRANS (@lem1974859) (@lem1974866)). Qed.
Lemma lem1974868 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974869 : term29 = term30.
Proof. exact (MK_COMB (@lem1974868) (@lem1974867)). Qed.
Lemma lem1974870 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1974871 (y : real) : (term966 y) = (term276 y).
Proof. exact (MK_COMB (@lem1974869) (@lem1974870 y)). Qed.
Lemma lem1974872 (y : real) : (term965 y) = (term276 y).
Proof. exact (TRANS (@lem1974856 y) (@lem1974871 y)). Qed.
Lemma lem1974873 (x : real) : (term967 x) = (term968 x).
Proof. exact (@lem1483476 term16 term28 x). Qed.
Lemma lem1974875 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1974876 : term107 = term27.
Proof. exact (@lem1974875 term22 term23). Qed.
Lemma lem1974877 : term24 = term25.
Proof. exact (@lem996238 term25). Qed.
Lemma lem1974878 : (term24 = term25) = (term26 = term23).
Proof. exact (@lem1007663 (BIT1 0) term25 term25). Qed.
Lemma lem1974879 : term26 = term23.
Proof. exact (EQ_MP (@lem1974878) (@lem1974877)). Qed.
Lemma lem1974880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1974881 : term27 = term17.
Proof. exact (MK_COMB (@lem1974880) (@lem1974879)). Qed.
Lemma lem1974882 : term107 = term17.
Proof. exact (TRANS (@lem1974876) (@lem1974881)). Qed.
Lemma lem1974883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1974884 : term108 = term109.
Proof. exact (MK_COMB (@lem1974883) (@lem1974882)). Qed.
Lemma lem1974885 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1974886 (x : real) : (term968 x) = (term283 x).
Proof. exact (MK_COMB (@lem1974884) (@lem1974885 x)). Qed.
Lemma lem1974887 (x : real) : (term967 x) = (term283 x).
Proof. exact (TRANS (@lem1974873 x) (@lem1974886 x)). Qed.
Lemma lem1974888 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1974889 (x : real) : (term969 x) = (term285 x).
Proof. exact (MK_COMB (@lem1974888) (@lem1974887 x)). Qed.
Lemma lem1974890 (x : real) (y : real) : (term964 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1974889 x) (@lem1974872 y)). Qed.
Lemma lem1974891 (x : real) (y : real) : (term963 x y) = (term286 x y).
Proof. exact (TRANS (@lem1974855 x y) (@lem1974890 x y)). Qed.
Lemma lem1974892 (x : real) (y : real) : (term970 x y) = (term970 x y).
Proof. exact (eq_refl (term970 x y)). Qed.
Lemma lem1974893 (x : real) (y : real) : (term962 x y) = (term971 x y).
Proof. exact (MK_COMB (@lem1974892 x y) (@lem1974891 x y)). Qed.
Lemma lem1974894 (x : real) (y : real) : (term971 x y) = (term972 x y).
Proof. exact (@lem1483482 (term928 x y) (term883 x y) (term286 x y)). Qed.
Lemma lem1974895 (x : real) (y : real) : (term973 x y) = (term974 x y).
Proof. exact (@lem1483484 (term283 x) (term883 x y) (term276 y)). Qed.
Lemma lem1974896 (x : real) (y : real) : (term975 x y) = (term976 x y).
Proof. exact (@lem1483488 (term276 y) (term883 x y)). Qed.
Lemma lem1974897 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1974898 (x : real) (y : real) : (term974 x y) = (term977 x y).
Proof. exact (MK_COMB (@lem1974897 x) (@lem1974896 x y)). Qed.
Lemma lem1974899 (x : real) (y : real) : (term973 x y) = (term977 x y).
Proof. exact (TRANS (@lem1974895 x y) (@lem1974898 x y)). Qed.
Lemma lem1974900 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1974901 (x : real) (y : real) : (term972 x y) = (term979 x y).
Proof. exact (MK_COMB (@lem1974900 x y) (@lem1974899 x y)). Qed.
Lemma lem1974902 (x : real) (y : real) : (term971 x y) = (term979 x y).
Proof. exact (TRANS (@lem1974894 x y) (@lem1974901 x y)). Qed.
Lemma lem1974903 (x : real) (y : real) : (term962 x y) = (term979 x y).
Proof. exact (TRANS (@lem1974893 x y) (@lem1974902 x y)). Qed.
Lemma lem1974904 (x : real) (y : real) : (term961 x y) = (term979 x y).
Proof. exact (TRANS (@lem1974854 x y) (@lem1974903 x y)). Qed.
Lemma lem1974905 (x : real) (y : real) : (term960 y x) = (term979 x y).
Proof. exact (TRANS (@lem1974853 x y) (@lem1974904 x y)). Qed.
Lemma lem1974906 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1974907 (x : real) (y : real) : (term980 y x) = (term981 x y).
Proof. exact (MK_COMB (@lem1974906) (@lem1974905 x y)). Qed.
Lemma lem1974908 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974909 (x : real) (y : real) : (term947 y x) = (term982 x y).
Proof. exact (MK_COMB (@lem1974907 x y) (@lem1974908)). Qed.
Lemma lem1974910 (x : real) (y : real) : (term946 y x) = (term982 x y).
Proof. exact (TRANS (@lem1974762 y x) (@lem1974909 x y)). Qed.
Lemma lem1974911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974912 (x : real) (y : real) : (term983 x y) = (term984 x y).
Proof. exact (MK_COMB (@lem1974911) (@lem1974761 x y)). Qed.
Lemma lem1974913 (x : real) (y : real) : (term901 y x) = (term985 x y).
Proof. exact (MK_COMB (@lem1974912 x y) (@lem1974910 x y)). Qed.
Lemma lem1974914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974915 (y : real) : (term742 y) = (term755 y).
Proof. exact (MK_COMB (@lem1974914) (@lem1974670 y)). Qed.
Lemma lem1974916 (x : real) (y : real) : (term903 y x) = (term986 x y).
Proof. exact (MK_COMB (@lem1974915 y) (@lem1974913 x y)). Qed.
Lemma lem1974917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974918 (x : real) : (term185 x) = (term186 x).
Proof. exact (MK_COMB (@lem1974917) (@lem1974649 x)). Qed.
Lemma lem1974919 (x : real) (y : real) : (term906 y x) = (term987 x y).
Proof. exact (MK_COMB (@lem1974918 x) (@lem1974916 x y)). Qed.
Lemma lem1974920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1974921 (x : real) (y : real) : (term746 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1974920) (@lem1974630 x y)). Qed.
Lemma lem1974922 (x : real) (y : real) : (term910 y x) = (term988 x y).
Proof. exact (MK_COMB (@lem1974921 x y) (@lem1974919 x y)). Qed.
Lemma lem1974955 (x : real) (y : real) : (term911 y x) = (term988 x y).
Proof. exact (TRANS (@lem1974611 y x) (@lem1974922 x y)). Qed.
Lemma lem1974957 (x : real) (y : real) : (term989 y x) = (term988 x y).
Proof. exact (eq_refl (term989 y x)). Qed.
Lemma lem1974958 (y : real) (x : real) : (term988 x y) = (term989 y x).
Proof. exact (SYM (@lem1974957 x y)). Qed.
Lemma lem1974959 (y : real) (x : real) : (term989 y x) = (term990 y x).
Proof. exact (@lem1482981 (term991 x y) x). Qed.
Lemma lem1974960 (y : real) (x : real) : (term988 x y) = (term990 y x).
Proof. exact (TRANS (@lem1974958 y x) (@lem1974959 y x)). Qed.
Lemma lem1974961 (x : real) (y : real) : (term992 y x) = (term993 x y).
Proof. exact (eq_refl (term992 y x)). Qed.
Lemma lem1974962 (x : real) : (term994 x) = (term994 x).
Proof. exact (eq_refl (term994 x)). Qed.
Lemma lem1974963 (x : real) (y : real) : (term995 y x) = (term996 x y).
Proof. exact (MK_COMB (@lem1974962 x) (@lem1974961 x y)). Qed.
Lemma lem1974964 (x : real) (y : real) : (term997 y x) = (term998 x y).
Proof. exact (eq_refl (term997 y x)). Qed.
Lemma lem1974965 (x : real) : (term755 x) = (term755 x).
Proof. exact (eq_refl (term755 x)). Qed.
Lemma lem1974966 (x : real) (y : real) : (term999 y x) = (term1000 x y).
Proof. exact (MK_COMB (@lem1974965 x) (@lem1974964 x y)). Qed.
Lemma lem1974967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1974968 (x : real) (y : real) : (term1001 y x) = (term1002 x y).
Proof. exact (MK_COMB (@lem1974967) (@lem1974966 x y)). Qed.
Lemma lem1974969 (x : real) (y : real) : (term990 y x) = (term1003 x y).
Proof. exact (MK_COMB (@lem1974968 x y) (@lem1974963 x y)). Qed.
Lemma lem1974970 (x : real) (y : real) : (term1004 x y) = (term1004 x y).
Proof. exact (eq_refl (term1004 x y)). Qed.
Lemma lem1974971 (x : real) (y : real) : ((term988 x y) = (term990 y x)) = ((term988 x y) = (term1003 x y)).
Proof. exact (MK_COMB (@lem1974970 x y) (@lem1974969 x y)). Qed.
Lemma lem1974972 (x : real) (y : real) : (term988 x y) = (term1003 x y).
Proof. exact (EQ_MP (@lem1974971 x y) (@lem1974960 y x)). Qed.
Lemma lem1974973 (x : real) : (term184 x) = (term179 x).
Proof. exact (@lem1483527 x term121). Qed.
Lemma lem1974979 (x : real) : (term180 x) = (term181 x).
Proof. exact (@lem1483519 x term121). Qed.
Lemma lem1974981 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1974982 : term139 = term121.
Proof. exact (@lem1974981 term22). Qed.
Lemma lem1974983 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1974984 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1974983 x) (@lem1974982)). Qed.
Lemma lem1974985 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1974986 (x : real) : (term181 x) = x.
Proof. exact (TRANS (@lem1974984 x) (@lem1974985 x)). Qed.
Lemma lem1974988 (x : real) : (term180 x) = x.
Proof. exact (TRANS (@lem1974979 x) (@lem1974986 x)). Qed.
Lemma lem1974989 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1974990 (x : real) : (term183 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1974989) (@lem1974988 x)). Qed.
Lemma lem1974991 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1974992 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1974990 x) (@lem1974991)). Qed.
Lemma lem1974993 (x : real) : (term184 x) = (term184 x).
Proof. exact (TRANS (@lem1974973 x) (@lem1974992 x)). Qed.
Lemma lem1974994 (x : real) (y : real) : (term604 x y) = (term1005 x y).
Proof. exact (@lem1483527 (term190 x y) term121). Qed.
Lemma lem1975012 (x : real) (y : real) : (term598 x y) = (term599 x y).
Proof. exact (@lem1483519 (term190 x y) term121). Qed.
Lemma lem1975014 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975015 : term139 = term121.
Proof. exact (@lem1975014 term22). Qed.
Lemma lem1975016 (x : real) (y : real) : (term600 x y) = (term600 x y).
Proof. exact (eq_refl (term600 x y)). Qed.
Lemma lem1975017 (x : real) (y : real) : (term599 x y) = (term601 x y).
Proof. exact (MK_COMB (@lem1975016 x y) (@lem1975015)). Qed.
Lemma lem1975018 (x : real) (y : real) : (term601 x y) = (term190 x y).
Proof. exact (@lem1483450 (term190 x y)). Qed.
Lemma lem1975019 (x : real) (y : real) : (term599 x y) = (term190 x y).
Proof. exact (TRANS (@lem1975017 x y) (@lem1975018 x y)). Qed.
Lemma lem1975021 (x : real) (y : real) : (term598 x y) = (term190 x y).
Proof. exact (TRANS (@lem1975012 x y) (@lem1975019 x y)). Qed.
Lemma lem1975022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975023 (x : real) (y : real) : (term1006 x y) = (term603 x y).
Proof. exact (MK_COMB (@lem1975022) (@lem1975021 x y)). Qed.
Lemma lem1975024 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975025 (x : real) (y : real) : (term1005 x y) = (term604 x y).
Proof. exact (MK_COMB (@lem1975023 x y) (@lem1975024)). Qed.
Lemma lem1975026 (x : real) (y : real) : (term604 x y) = (term604 x y).
Proof. exact (TRANS (@lem1974994 x y) (@lem1975025 x y)). Qed.
Lemma lem1975027 (x : real) : (term177 x) = (term263 x).
Proof. exact (@lem1483525 (term52 x) term121). Qed.
Lemma lem1975039 (x : real) : (term264 x) = (term265 x).
Proof. exact (@lem1483519 (term52 x) term121). Qed.
Lemma lem1975041 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975042 : term139 = term121.
Proof. exact (@lem1975041 term22). Qed.
Lemma lem1975043 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1975044 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1975043 x) (@lem1975042)). Qed.
Lemma lem1975045 (x : real) : (term266 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1975046 (x : real) : (term265 x) = (term52 x).
Proof. exact (TRANS (@lem1975044 x) (@lem1975045 x)). Qed.
Lemma lem1975048 (x : real) : (term264 x) = (term52 x).
Proof. exact (TRANS (@lem1975039 x) (@lem1975046 x)). Qed.
Lemma lem1975049 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975050 (x : real) : (term267 x) = (term176 x).
Proof. exact (MK_COMB (@lem1975049) (@lem1975048 x)). Qed.
Lemma lem1975051 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975052 (x : real) : (term263 x) = (term177 x).
Proof. exact (MK_COMB (@lem1975050 x) (@lem1975051)). Qed.
Lemma lem1975053 (x : real) : (term177 x) = (term177 x).
Proof. exact (TRANS (@lem1975027 x) (@lem1975052 x)). Qed.
Lemma lem1975054 (y : real) : (term184 y) = (term179 y).
Proof. exact (@lem1483527 y term121). Qed.
Lemma lem1975060 (y : real) : (term180 y) = (term181 y).
Proof. exact (@lem1483519 y term121). Qed.
Lemma lem1975062 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975063 : term139 = term121.
Proof. exact (@lem1975062 term22). Qed.
Lemma lem1975064 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1975065 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem1975064 y) (@lem1975063)). Qed.
Lemma lem1975066 (y : real) : (term182 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1975067 (y : real) : (term181 y) = y.
Proof. exact (TRANS (@lem1975065 y) (@lem1975066 y)). Qed.
Lemma lem1975069 (y : real) : (term180 y) = y.
Proof. exact (TRANS (@lem1975060 y) (@lem1975067 y)). Qed.
Lemma lem1975070 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975071 (y : real) : (term183 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1975070) (@lem1975069 y)). Qed.
Lemma lem1975072 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975073 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1975071 y) (@lem1975072)). Qed.
Lemma lem1975074 (y : real) : (term184 y) = (term184 y).
Proof. exact (TRANS (@lem1975054 y) (@lem1975073 y)). Qed.
Lemma lem1975075 (x : real) (y : real) : (term1007 x y) = (term1008 x y).
Proof. exact (@lem1483527 (term1009 x y) term121). Qed.
Lemma lem1975105 (x : real) (y : real) : (term1010 x y) = (term1011 x y).
Proof. exact (@lem1483519 (term1009 x y) term121). Qed.
Lemma lem1975107 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975108 : term139 = term121.
Proof. exact (@lem1975107 term22). Qed.
Lemma lem1975109 (x : real) (y : real) : (term1012 x y) = (term1012 x y).
Proof. exact (eq_refl (term1012 x y)). Qed.
Lemma lem1975110 (x : real) (y : real) : (term1011 x y) = (term1013 x y).
Proof. exact (MK_COMB (@lem1975109 x y) (@lem1975108)). Qed.
Lemma lem1975111 (x : real) (y : real) : (term1013 x y) = (term1009 x y).
Proof. exact (@lem1483450 (term1009 x y)). Qed.
Lemma lem1975112 (x : real) (y : real) : (term1011 x y) = (term1009 x y).
Proof. exact (TRANS (@lem1975110 x y) (@lem1975111 x y)). Qed.
Lemma lem1975114 (x : real) (y : real) : (term1010 x y) = (term1009 x y).
Proof. exact (TRANS (@lem1975105 x y) (@lem1975112 x y)). Qed.
Lemma lem1975115 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975116 (x : real) (y : real) : (term1014 x y) = (term1015 x y).
Proof. exact (MK_COMB (@lem1975115) (@lem1975114 x y)). Qed.
Lemma lem1975117 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975118 (x : real) (y : real) : (term1008 x y) = (term1007 x y).
Proof. exact (MK_COMB (@lem1975116 x y) (@lem1975117)). Qed.
Lemma lem1975119 (x : real) (y : real) : (term1007 x y) = (term1007 x y).
Proof. exact (TRANS (@lem1975075 x y) (@lem1975118 x y)). Qed.
Lemma lem1975120 (x : real) (y : real) : (term1016 x y) = (term1017 x y).
Proof. exact (@lem1483525 (term1018 x y) term121). Qed.
Lemma lem1975121 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975144 (x : real) (y : real) : (term1019 x y) = (term1020 x y).
Proof. exact (@lem1483484 x (term276 y) (real_abs y)). Qed.
Lemma lem1975153 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1975154 (x : real) (y : real) : (term1021 x y) = (term1022 x y).
Proof. exact (MK_COMB (@lem1975153 x) (@lem1975144 x y)). Qed.
Lemma lem1975155 (x : real) (y : real) : (term1022 x y) = (term1023 x y).
Proof. exact (@lem1483490 (term283 x) x (term1024 y)). Qed.
Lemma lem1975156 (x : real) : (term1025 x) = (term1026 x).
Proof. exact (@lem1483440 term17 x). Qed.
Lemma lem1975157 : term1027 = term1028.
Proof. exact (@lem1367770 term23 term22). Qed.
Lemma lem1975158 : term1029 = term1030.
Proof. exact (@lem706949). Qed.
Lemma lem1975159 : (term1029 = term1030) = (term1031 = term1032).
Proof. exact (@lem1006570 term25 (BIT1 0) term1030). Qed.
Lemma lem1975160 : term1031 = term1032.
Proof. exact (EQ_MP (@lem1975159) (@lem1975158)). Qed.
Lemma lem1975161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1975162 : term1028 = term1033.
Proof. exact (MK_COMB (@lem1975161) (@lem1975160)). Qed.
Lemma lem1975163 : term1027 = term1033.
Proof. exact (TRANS (@lem1975157) (@lem1975162)). Qed.
Lemma lem1975164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1975165 : term1034 = term1035.
Proof. exact (MK_COMB (@lem1975164) (@lem1975163)). Qed.
Lemma lem1975166 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1975167 (x : real) : (term1026 x) = (term1036 x).
Proof. exact (MK_COMB (@lem1975165) (@lem1975166 x)). Qed.
Lemma lem1975168 (x : real) : (term1025 x) = (term1036 x).
Proof. exact (TRANS (@lem1975156 x) (@lem1975167 x)). Qed.
Lemma lem1975169 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975170 (x : real) : (term1037 x) = (term1038 x).
Proof. exact (MK_COMB (@lem1975169) (@lem1975168 x)). Qed.
Lemma lem1975171 (y : real) : (term1024 y) = (term1024 y).
Proof. exact (eq_refl (term1024 y)). Qed.
Lemma lem1975172 (x : real) (y : real) : (term1023 x y) = (term1039 x y).
Proof. exact (MK_COMB (@lem1975170 x) (@lem1975171 y)). Qed.
Lemma lem1975173 (x : real) (y : real) : (term1022 x y) = (term1039 x y).
Proof. exact (TRANS (@lem1975155 x y) (@lem1975172 x y)). Qed.
Lemma lem1975174 (x : real) (y : real) : (term1021 x y) = (term1039 x y).
Proof. exact (TRANS (@lem1975154 x y) (@lem1975173 x y)). Qed.
Lemma lem1975189 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1975192 (x : real) (y : real) : (term1018 x y) = (term1040 x y).
Proof. exact (MK_COMB (@lem1975189 x y) (@lem1975174 x y)). Qed.
Lemma lem1975193 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975194 (x : real) (y : real) : (term1041 x y) = (term1042 x y).
Proof. exact (MK_COMB (@lem1975193) (@lem1975192 x y)). Qed.
Lemma lem1975195 (x : real) (y : real) : (term1043 x y) = (term1044 x y).
Proof. exact (MK_COMB (@lem1975194 x y) (@lem1975121)). Qed.
Lemma lem1975196 (x : real) (y : real) : (term1044 x y) = (term1045 x y).
Proof. exact (@lem1483519 (term1040 x y) term121). Qed.
Lemma lem1975198 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975199 : term139 = term121.
Proof. exact (@lem1975198 term22). Qed.
Lemma lem1975200 (x : real) (y : real) : (term1046 x y) = (term1046 x y).
Proof. exact (eq_refl (term1046 x y)). Qed.
Lemma lem1975201 (x : real) (y : real) : (term1045 x y) = (term1047 x y).
Proof. exact (MK_COMB (@lem1975200 x y) (@lem1975199)). Qed.
Lemma lem1975202 (x : real) (y : real) : (term1047 x y) = (term1040 x y).
Proof. exact (@lem1483450 (term1040 x y)). Qed.
Lemma lem1975203 (x : real) (y : real) : (term1045 x y) = (term1040 x y).
Proof. exact (TRANS (@lem1975201 x y) (@lem1975202 x y)). Qed.
Lemma lem1975204 (x : real) (y : real) : (term1044 x y) = (term1040 x y).
Proof. exact (TRANS (@lem1975196 x y) (@lem1975203 x y)). Qed.
Lemma lem1975205 (x : real) (y : real) : (term1043 x y) = (term1040 x y).
Proof. exact (TRANS (@lem1975195 x y) (@lem1975204 x y)). Qed.
Lemma lem1975206 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975207 (x : real) (y : real) : (term1048 x y) = (term1049 x y).
Proof. exact (MK_COMB (@lem1975206) (@lem1975205 x y)). Qed.
Lemma lem1975208 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975209 (x : real) (y : real) : (term1017 x y) = (term1050 x y).
Proof. exact (MK_COMB (@lem1975207 x y) (@lem1975208)). Qed.
Lemma lem1975210 (x : real) (y : real) : (term1016 x y) = (term1050 x y).
Proof. exact (TRANS (@lem1975120 x y) (@lem1975209 x y)). Qed.
Lemma lem1975211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975212 (x : real) (y : real) : (term1051 x y) = (term1051 x y).
Proof. exact (MK_COMB (@lem1975211) (@lem1975119 x y)). Qed.
Lemma lem1975213 (x : real) (y : real) : (term1052 x y) = (term1053 x y).
Proof. exact (MK_COMB (@lem1975212 x y) (@lem1975210 x y)). Qed.
Lemma lem1975214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975215 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975214) (@lem1975074 y)). Qed.
Lemma lem1975216 (x : real) (y : real) : (term1054 x y) = (term1055 x y).
Proof. exact (MK_COMB (@lem1975215 y) (@lem1975213 x y)). Qed.
Lemma lem1975217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975218 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975217) (@lem1975053 x)). Qed.
Lemma lem1975219 (x : real) (y : real) : (term1056 x y) = (term1057 x y).
Proof. exact (MK_COMB (@lem1975218 x) (@lem1975216 x y)). Qed.
Lemma lem1975220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975221 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1975220) (@lem1975026 x y)). Qed.
Lemma lem1975222 (x : real) (y : real) : (term998 x y) = (term1058 x y).
Proof. exact (MK_COMB (@lem1975221 x y) (@lem1975219 x y)). Qed.
Lemma lem1975223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975224 (x : real) : (term755 x) = (term755 x).
Proof. exact (MK_COMB (@lem1975223) (@lem1974993 x)). Qed.
Lemma lem1975225 (x : real) (y : real) : (term1000 x y) = (term1059 x y).
Proof. exact (MK_COMB (@lem1975224 x) (@lem1975222 x y)). Qed.
Lemma lem1975226 (x : real) : (term1060 x) = (term172 x).
Proof. exact (@lem1483525 term121 x). Qed.
Lemma lem1975232 (x : real) : (term173 x) = (term174 x).
Proof. exact (@lem1483519 term121 x). Qed.
Lemma lem1975237 (x : real) : (term174 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1975239 (x : real) : (term173 x) = (term52 x).
Proof. exact (TRANS (@lem1975232 x) (@lem1975237 x)). Qed.
Lemma lem1975240 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975241 (x : real) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1975240) (@lem1975239 x)). Qed.
Lemma lem1975242 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975243 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1975241 x) (@lem1975242)). Qed.
Lemma lem1975244 (x : real) : (term1060 x) = (term177 x).
Proof. exact (TRANS (@lem1975226 x) (@lem1975243 x)). Qed.
Lemma lem1975245 (x : real) (y : real) : (term1061 x y) = (term1062 x y).
Proof. exact (@lem1483527 (term1063 x y) term121). Qed.
Lemma lem1975246 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975247 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1975254 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1975255 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975256 (x : real) : (term1064 x) = (term215 x).
Proof. exact (MK_COMB (@lem1975255) (@lem1975254 x)). Qed.
Lemma lem1975259 (x : real) (y : real) : (term1065 x y) = (term1066 x y).
Proof. exact (MK_COMB (@lem1975256 x) (@lem1975247 y)). Qed.
Lemma lem1975274 (x : real) (y : real) : (term1067 x y) = (term1067 x y).
Proof. exact (eq_refl (term1067 x y)). Qed.
Lemma lem1975277 (x : real) (y : real) : (term1063 x y) = (term1068 x y).
Proof. exact (MK_COMB (@lem1975274 x y) (@lem1975259 x y)). Qed.
Lemma lem1975278 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975279 (x : real) (y : real) : (term1069 x y) = (term1070 x y).
Proof. exact (MK_COMB (@lem1975278) (@lem1975277 x y)). Qed.
Lemma lem1975280 (x : real) (y : real) : (term1071 x y) = (term1072 x y).
Proof. exact (MK_COMB (@lem1975279 x y) (@lem1975246)). Qed.
Lemma lem1975281 (x : real) (y : real) : (term1072 x y) = (term1073 x y).
Proof. exact (@lem1483519 (term1068 x y) term121). Qed.
Lemma lem1975283 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975284 : term139 = term121.
Proof. exact (@lem1975283 term22). Qed.
Lemma lem1975285 (x : real) (y : real) : (term1074 x y) = (term1074 x y).
Proof. exact (eq_refl (term1074 x y)). Qed.
Lemma lem1975286 (x : real) (y : real) : (term1073 x y) = (term1075 x y).
Proof. exact (MK_COMB (@lem1975285 x y) (@lem1975284)). Qed.
Lemma lem1975287 (x : real) (y : real) : (term1075 x y) = (term1068 x y).
Proof. exact (@lem1483450 (term1068 x y)). Qed.
Lemma lem1975288 (x : real) (y : real) : (term1073 x y) = (term1068 x y).
Proof. exact (TRANS (@lem1975286 x y) (@lem1975287 x y)). Qed.
Lemma lem1975289 (x : real) (y : real) : (term1072 x y) = (term1068 x y).
Proof. exact (TRANS (@lem1975281 x y) (@lem1975288 x y)). Qed.
Lemma lem1975290 (x : real) (y : real) : (term1071 x y) = (term1068 x y).
Proof. exact (TRANS (@lem1975280 x y) (@lem1975289 x y)). Qed.
Lemma lem1975291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975292 (x : real) (y : real) : (term1076 x y) = (term1077 x y).
Proof. exact (MK_COMB (@lem1975291) (@lem1975290 x y)). Qed.
Lemma lem1975293 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975294 (x : real) (y : real) : (term1062 x y) = (term1078 x y).
Proof. exact (MK_COMB (@lem1975292 x y) (@lem1975293)). Qed.
Lemma lem1975295 (x : real) (y : real) : (term1061 x y) = (term1078 x y).
Proof. exact (TRANS (@lem1975245 x y) (@lem1975294 x y)). Qed.
Lemma lem1975296 (x : real) (y : real) : (term1079 x y) = (term1080 x y).
Proof. exact (@lem1483525 (term1081 x y) term121). Qed.
Lemma lem1975297 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975298 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1975305 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1975306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975307 (x : real) : (term1064 x) = (term215 x).
Proof. exact (MK_COMB (@lem1975306) (@lem1975305 x)). Qed.
Lemma lem1975310 (x : real) (y : real) : (term1065 x y) = (term1066 x y).
Proof. exact (MK_COMB (@lem1975307 x) (@lem1975298 y)). Qed.
Lemma lem1975319 (y : real) : (term354 y) = (term354 y).
Proof. exact (eq_refl (term354 y)). Qed.
Lemma lem1975320 (x : real) (y : real) : (term1082 x y) = (term1083 x y).
Proof. exact (MK_COMB (@lem1975319 y) (@lem1975310 x y)). Qed.
Lemma lem1975325 (x : real) (y : real) : (term1083 x y) = (term1084 x y).
Proof. exact (@lem1483484 (term52 x) (term276 y) (real_abs y)). Qed.
Lemma lem1975326 (x : real) (y : real) : (term1082 x y) = (term1084 x y).
Proof. exact (TRANS (@lem1975320 x y) (@lem1975325 x y)). Qed.
Lemma lem1975335 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1975336 (x : real) (y : real) : (term1085 x y) = (term1086 x y).
Proof. exact (MK_COMB (@lem1975335 x) (@lem1975326 x y)). Qed.
Lemma lem1975337 (x : real) (y : real) : (term1086 x y) = (term1087 x y).
Proof. exact (@lem1483490 (term283 x) (term52 x) (term1024 y)). Qed.
Lemma lem1975338 (x : real) : (term1088 x) = (term1089 x).
Proof. exact (@lem1483438 term17 term16 x). Qed.
Lemma lem1975341 : term1090 = term71.
Proof. exact (@lem1367769 term22 term22). Qed.
Lemma lem1975342 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1975343 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1975344 : term90 = term23.
Proof. exact (EQ_MP (@lem1975343) (@lem1975342)). Qed.
Lemma lem1975345 : term23 = term90.
Proof. exact (SYM (@lem1975344)). Qed.
Lemma lem1975346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1975347 : term17 = term91.
Proof. exact (MK_COMB (@lem1975346) (@lem1975345)). Qed.
Lemma lem1975348 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975349 : term1091 = term1092.
Proof. exact (MK_COMB (@lem1975348) (@lem1975347)). Qed.
Lemma lem1975350 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1975351 : term1093 = term1090.
Proof. exact (MK_COMB (@lem1975349) (@lem1975350)). Qed.
Lemma lem1975352 : term1093 = term71.
Proof. exact (TRANS (@lem1975351) (@lem1975341)). Qed.
Lemma lem1975353 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1975354 : term1094 = term73.
Proof. exact (MK_COMB (@lem1975353) (@lem1975352)). Qed.
Lemma lem1975355 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1975356 (x : real) : (term1089 x) = (term199 x).
Proof. exact (MK_COMB (@lem1975354) (@lem1975355 x)). Qed.
Lemma lem1975357 (x : real) : (term1088 x) = (term199 x).
Proof. exact (TRANS (@lem1975338 x) (@lem1975356 x)). Qed.
Lemma lem1975358 (x : real) : (term199 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1975359 (x : real) : (term1088 x) = x.
Proof. exact (TRANS (@lem1975357 x) (@lem1975358 x)). Qed.
Lemma lem1975360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975361 (x : real) : (term1095 x) = (real_add x).
Proof. exact (MK_COMB (@lem1975360) (@lem1975359 x)). Qed.
Lemma lem1975362 (y : real) : (term1024 y) = (term1024 y).
Proof. exact (eq_refl (term1024 y)). Qed.
Lemma lem1975363 (x : real) (y : real) : (term1087 x y) = (term1020 x y).
Proof. exact (MK_COMB (@lem1975361 x) (@lem1975362 y)). Qed.
Lemma lem1975364 (x : real) (y : real) : (term1086 x y) = (term1020 x y).
Proof. exact (TRANS (@lem1975337 x y) (@lem1975363 x y)). Qed.
Lemma lem1975365 (x : real) (y : real) : (term1085 x y) = (term1020 x y).
Proof. exact (TRANS (@lem1975336 x y) (@lem1975364 x y)). Qed.
Lemma lem1975380 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1975383 (x : real) (y : real) : (term1081 x y) = (term1096 x y).
Proof. exact (MK_COMB (@lem1975380 x y) (@lem1975365 x y)). Qed.
Lemma lem1975384 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975385 (x : real) (y : real) : (term1097 x y) = (term1098 x y).
Proof. exact (MK_COMB (@lem1975384) (@lem1975383 x y)). Qed.
Lemma lem1975386 (x : real) (y : real) : (term1099 x y) = (term1100 x y).
Proof. exact (MK_COMB (@lem1975385 x y) (@lem1975297)). Qed.
Lemma lem1975387 (x : real) (y : real) : (term1100 x y) = (term1101 x y).
Proof. exact (@lem1483519 (term1096 x y) term121). Qed.
Lemma lem1975389 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975390 : term139 = term121.
Proof. exact (@lem1975389 term22). Qed.
Lemma lem1975391 (x : real) (y : real) : (term1102 x y) = (term1102 x y).
Proof. exact (eq_refl (term1102 x y)). Qed.
Lemma lem1975392 (x : real) (y : real) : (term1101 x y) = (term1103 x y).
Proof. exact (MK_COMB (@lem1975391 x y) (@lem1975390)). Qed.
Lemma lem1975393 (x : real) (y : real) : (term1103 x y) = (term1096 x y).
Proof. exact (@lem1483450 (term1096 x y)). Qed.
Lemma lem1975394 (x : real) (y : real) : (term1101 x y) = (term1096 x y).
Proof. exact (TRANS (@lem1975392 x y) (@lem1975393 x y)). Qed.
Lemma lem1975395 (x : real) (y : real) : (term1100 x y) = (term1096 x y).
Proof. exact (TRANS (@lem1975387 x y) (@lem1975394 x y)). Qed.
Lemma lem1975396 (x : real) (y : real) : (term1099 x y) = (term1096 x y).
Proof. exact (TRANS (@lem1975386 x y) (@lem1975395 x y)). Qed.
Lemma lem1975397 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975398 (x : real) (y : real) : (term1104 x y) = (term1105 x y).
Proof. exact (MK_COMB (@lem1975397) (@lem1975396 x y)). Qed.
Lemma lem1975399 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975400 (x : real) (y : real) : (term1080 x y) = (term1106 x y).
Proof. exact (MK_COMB (@lem1975398 x y) (@lem1975399)). Qed.
Lemma lem1975401 (x : real) (y : real) : (term1079 x y) = (term1106 x y).
Proof. exact (TRANS (@lem1975296 x y) (@lem1975400 x y)). Qed.
Lemma lem1975402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975403 (x : real) (y : real) : (term1107 x y) = (term1108 x y).
Proof. exact (MK_COMB (@lem1975402) (@lem1975295 x y)). Qed.
Lemma lem1975404 (x : real) (y : real) : (term1109 x y) = (term1110 x y).
Proof. exact (MK_COMB (@lem1975403 x y) (@lem1975401 x y)). Qed.
Lemma lem1975405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975406 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975405) (@lem1975074 y)). Qed.
Lemma lem1975407 (x : real) (y : real) : (term1111 x y) = (term1112 x y).
Proof. exact (MK_COMB (@lem1975406 y) (@lem1975404 x y)). Qed.
Lemma lem1975408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975409 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975408) (@lem1975053 x)). Qed.
Lemma lem1975410 (x : real) (y : real) : (term1113 x y) = (term1114 x y).
Proof. exact (MK_COMB (@lem1975409 x) (@lem1975407 x y)). Qed.
Lemma lem1975411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975412 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1975411) (@lem1975026 x y)). Qed.
Lemma lem1975413 (x : real) (y : real) : (term993 x y) = (term1115 x y).
Proof. exact (MK_COMB (@lem1975412 x y) (@lem1975410 x y)). Qed.
Lemma lem1975414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975415 (x : real) : (term994 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975414) (@lem1975244 x)). Qed.
Lemma lem1975416 (x : real) (y : real) : (term996 x y) = (term1116 x y).
Proof. exact (MK_COMB (@lem1975415 x) (@lem1975413 x y)). Qed.
Lemma lem1975417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1975418 (x : real) (y : real) : (term1002 x y) = (term1117 x y).
Proof. exact (MK_COMB (@lem1975417) (@lem1975225 x y)). Qed.
Lemma lem1975419 (x : real) (y : real) : (term1003 x y) = (term1118 x y).
Proof. exact (MK_COMB (@lem1975418 x y) (@lem1975416 x y)). Qed.
Lemma lem1975420 (x : real) (y : real) : (term988 x y) = (term1118 x y).
Proof. exact (TRANS (@lem1974972 x y) (@lem1975419 x y)). Qed.
Lemma lem1975422 (x : real) (y : real) : (term1119 x y) = (term1116 x y).
Proof. exact (eq_refl (term1119 x y)). Qed.
Lemma lem1975423 (x : real) (y : real) : (term1116 x y) = (term1119 x y).
Proof. exact (SYM (@lem1975422 x y)). Qed.
Lemma lem1975424 (x : real) (y : real) : (term1119 x y) = (term1120 x y).
Proof. exact (@lem1482981 (term1121 x y) y). Qed.
Lemma lem1975425 (x : real) (y : real) : (term1116 x y) = (term1120 x y).
Proof. exact (TRANS (@lem1975423 x y) (@lem1975424 x y)). Qed.
Lemma lem1975426 (x : real) (y : real) : (term1122 x y) = (term1123 x y).
Proof. exact (eq_refl (term1122 x y)). Qed.
Lemma lem1975427 (y : real) : (term994 y) = (term994 y).
Proof. exact (eq_refl (term994 y)). Qed.
Lemma lem1975428 (x : real) (y : real) : (term1124 x y) = (term1125 x y).
Proof. exact (MK_COMB (@lem1975427 y) (@lem1975426 x y)). Qed.
Lemma lem1975429 (x : real) (y : real) : (term1126 x y) = (term1127 x y).
Proof. exact (eq_refl (term1126 x y)). Qed.
Lemma lem1975430 (y : real) : (term755 y) = (term755 y).
Proof. exact (eq_refl (term755 y)). Qed.
Lemma lem1975431 (x : real) (y : real) : (term1128 x y) = (term1129 x y).
Proof. exact (MK_COMB (@lem1975430 y) (@lem1975429 x y)). Qed.
Lemma lem1975432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1975433 (x : real) (y : real) : (term1130 x y) = (term1131 x y).
Proof. exact (MK_COMB (@lem1975432) (@lem1975431 x y)). Qed.
Lemma lem1975434 (x : real) (y : real) : (term1120 x y) = (term1132 x y).
Proof. exact (MK_COMB (@lem1975433 x y) (@lem1975428 x y)). Qed.
Lemma lem1975435 (x : real) (y : real) : (term1133 x y) = (term1133 x y).
Proof. exact (eq_refl (term1133 x y)). Qed.
Lemma lem1975436 (x : real) (y : real) : ((term1116 x y) = (term1120 x y)) = ((term1116 x y) = (term1132 x y)).
Proof. exact (MK_COMB (@lem1975435 x y) (@lem1975434 x y)). Qed.
Lemma lem1975437 (x : real) (y : real) : (term1116 x y) = (term1132 x y).
Proof. exact (EQ_MP (@lem1975436 x y) (@lem1975425 x y)). Qed.
Lemma lem1975438 (x : real) (y : real) : (term1134 x y) = (term1135 x y).
Proof. exact (@lem1483527 (term1136 x y) term121). Qed.
Lemma lem1975474 (x : real) (y : real) : (term1137 x y) = (term1138 x y).
Proof. exact (@lem1483519 (term1136 x y) term121). Qed.
Lemma lem1975476 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975477 : term139 = term121.
Proof. exact (@lem1975476 term22). Qed.
Lemma lem1975478 (x : real) (y : real) : (term1139 x y) = (term1139 x y).
Proof. exact (eq_refl (term1139 x y)). Qed.
Lemma lem1975479 (x : real) (y : real) : (term1138 x y) = (term1140 x y).
Proof. exact (MK_COMB (@lem1975478 x y) (@lem1975477)). Qed.
Lemma lem1975480 (x : real) (y : real) : (term1140 x y) = (term1136 x y).
Proof. exact (@lem1483450 (term1136 x y)). Qed.
Lemma lem1975481 (x : real) (y : real) : (term1138 x y) = (term1136 x y).
Proof. exact (TRANS (@lem1975479 x y) (@lem1975480 x y)). Qed.
Lemma lem1975483 (x : real) (y : real) : (term1137 x y) = (term1136 x y).
Proof. exact (TRANS (@lem1975474 x y) (@lem1975481 x y)). Qed.
Lemma lem1975484 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975485 (x : real) (y : real) : (term1141 x y) = (term1142 x y).
Proof. exact (MK_COMB (@lem1975484) (@lem1975483 x y)). Qed.
Lemma lem1975486 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975487 (x : real) (y : real) : (term1135 x y) = (term1134 x y).
Proof. exact (MK_COMB (@lem1975485 x y) (@lem1975486)). Qed.
Lemma lem1975488 (x : real) (y : real) : (term1134 x y) = (term1134 x y).
Proof. exact (TRANS (@lem1975438 x y) (@lem1975487 x y)). Qed.
Lemma lem1975489 (x : real) (y : real) : (term1143 x y) = (term1144 x y).
Proof. exact (@lem1483525 (term1145 x y) term121). Qed.
Lemma lem1975490 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975502 (y : real) : (term1146 y) = (term1147 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1975505 : term421 = term16.
Proof. exact (@lem1367767 term22 term22). Qed.
Lemma lem1975506 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1975507 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1975508 : term90 = term23.
Proof. exact (EQ_MP (@lem1975507) (@lem1975506)). Qed.
Lemma lem1975509 : term23 = term90.
Proof. exact (SYM (@lem1975508)). Qed.
Lemma lem1975510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1975511 : term17 = term91.
Proof. exact (MK_COMB (@lem1975510) (@lem1975509)). Qed.
Lemma lem1975512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1975513 : term28 = term88.
Proof. exact (MK_COMB (@lem1975512) (@lem1975511)). Qed.
Lemma lem1975514 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975515 : term422 = term423.
Proof. exact (MK_COMB (@lem1975514) (@lem1975513)). Qed.
Lemma lem1975516 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem1975517 : term424 = term421.
Proof. exact (MK_COMB (@lem1975515) (@lem1975516)). Qed.
Lemma lem1975518 : term424 = term16.
Proof. exact (TRANS (@lem1975517) (@lem1975505)). Qed.
Lemma lem1975519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1975520 : term425 = term77.
Proof. exact (MK_COMB (@lem1975519) (@lem1975518)). Qed.
Lemma lem1975521 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1975522 (y : real) : (term1147 y) = (term52 y).
Proof. exact (MK_COMB (@lem1975520) (@lem1975521 y)). Qed.
Lemma lem1975524 (y : real) : (term1146 y) = (term52 y).
Proof. exact (TRANS (@lem1975502 y) (@lem1975522 y)). Qed.
Lemma lem1975527 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1975530 (x : real) (y : real) : (term1148 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1975527 x) (@lem1975524 y)). Qed.
Lemma lem1975545 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1975548 (x : real) (y : real) : (term1145 x y) = (term1149 x y).
Proof. exact (MK_COMB (@lem1975545 x y) (@lem1975530 x y)). Qed.
Lemma lem1975549 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975550 (x : real) (y : real) : (term1150 x y) = (term1151 x y).
Proof. exact (MK_COMB (@lem1975549) (@lem1975548 x y)). Qed.
Lemma lem1975551 (x : real) (y : real) : (term1152 x y) = (term1153 x y).
Proof. exact (MK_COMB (@lem1975550 x y) (@lem1975490)). Qed.
Lemma lem1975552 (x : real) (y : real) : (term1153 x y) = (term1154 x y).
Proof. exact (@lem1483519 (term1149 x y) term121). Qed.
Lemma lem1975554 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975555 : term139 = term121.
Proof. exact (@lem1975554 term22). Qed.
Lemma lem1975556 (x : real) (y : real) : (term1155 x y) = (term1155 x y).
Proof. exact (eq_refl (term1155 x y)). Qed.
Lemma lem1975557 (x : real) (y : real) : (term1154 x y) = (term1156 x y).
Proof. exact (MK_COMB (@lem1975556 x y) (@lem1975555)). Qed.
Lemma lem1975558 (x : real) (y : real) : (term1156 x y) = (term1149 x y).
Proof. exact (@lem1483450 (term1149 x y)). Qed.
Lemma lem1975559 (x : real) (y : real) : (term1154 x y) = (term1149 x y).
Proof. exact (TRANS (@lem1975557 x y) (@lem1975558 x y)). Qed.
Lemma lem1975560 (x : real) (y : real) : (term1153 x y) = (term1149 x y).
Proof. exact (TRANS (@lem1975552 x y) (@lem1975559 x y)). Qed.
Lemma lem1975561 (x : real) (y : real) : (term1152 x y) = (term1149 x y).
Proof. exact (TRANS (@lem1975551 x y) (@lem1975560 x y)). Qed.
Lemma lem1975562 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975563 (x : real) (y : real) : (term1157 x y) = (term1158 x y).
Proof. exact (MK_COMB (@lem1975562) (@lem1975561 x y)). Qed.
Lemma lem1975564 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975565 (x : real) (y : real) : (term1144 x y) = (term1159 x y).
Proof. exact (MK_COMB (@lem1975563 x y) (@lem1975564)). Qed.
Lemma lem1975566 (x : real) (y : real) : (term1143 x y) = (term1159 x y).
Proof. exact (TRANS (@lem1975489 x y) (@lem1975565 x y)). Qed.
Lemma lem1975567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975568 (x : real) (y : real) : (term1160 x y) = (term1160 x y).
Proof. exact (MK_COMB (@lem1975567) (@lem1975488 x y)). Qed.
Lemma lem1975569 (x : real) (y : real) : (term1161 x y) = (term1162 x y).
Proof. exact (MK_COMB (@lem1975568 x y) (@lem1975566 x y)). Qed.
Lemma lem1975570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975571 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975570) (@lem1975074 y)). Qed.
Lemma lem1975572 (x : real) (y : real) : (term1163 x y) = (term1164 x y).
Proof. exact (MK_COMB (@lem1975571 y) (@lem1975569 x y)). Qed.
Lemma lem1975573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975574 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975573) (@lem1975053 x)). Qed.
Lemma lem1975575 (x : real) (y : real) : (term1165 x y) = (term1166 x y).
Proof. exact (MK_COMB (@lem1975574 x) (@lem1975572 x y)). Qed.
Lemma lem1975576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975577 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1975576) (@lem1975026 x y)). Qed.
Lemma lem1975578 (x : real) (y : real) : (term1167 x y) = (term1168 x y).
Proof. exact (MK_COMB (@lem1975577 x y) (@lem1975575 x y)). Qed.
Lemma lem1975579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975580 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975579) (@lem1975053 x)). Qed.
Lemma lem1975581 (x : real) (y : real) : (term1127 x y) = (term1169 x y).
Proof. exact (MK_COMB (@lem1975580 x) (@lem1975578 x y)). Qed.
Lemma lem1975582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975583 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975582) (@lem1975074 y)). Qed.
Lemma lem1975584 (x : real) (y : real) : (term1129 x y) = (term1170 x y).
Proof. exact (MK_COMB (@lem1975583 y) (@lem1975581 x y)). Qed.
Lemma lem1975585 (y : real) : (term1060 y) = (term172 y).
Proof. exact (@lem1483525 term121 y). Qed.
Lemma lem1975591 (y : real) : (term173 y) = (term174 y).
Proof. exact (@lem1483519 term121 y). Qed.
Lemma lem1975596 (y : real) : (term174 y) = (term52 y).
Proof. exact (@lem1483448 (term52 y)). Qed.
Lemma lem1975598 (y : real) : (term173 y) = (term52 y).
Proof. exact (TRANS (@lem1975591 y) (@lem1975596 y)). Qed.
Lemma lem1975599 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975600 (y : real) : (term175 y) = (term176 y).
Proof. exact (MK_COMB (@lem1975599) (@lem1975598 y)). Qed.
Lemma lem1975601 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975602 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1975600 y) (@lem1975601)). Qed.
Lemma lem1975603 (y : real) : (term1060 y) = (term177 y).
Proof. exact (TRANS (@lem1975585 y) (@lem1975602 y)). Qed.
Lemma lem1975604 (x : real) (y : real) : (term1171 x y) = (term1172 x y).
Proof. exact (@lem1483527 (term1173 x y) term121). Qed.
Lemma lem1975605 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975612 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1975621 (x : real) : (term215 x) = (term215 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1975624 (x : real) (y : real) : (term1174 x y) = (term1175 x y).
Proof. exact (MK_COMB (@lem1975621 x) (@lem1975612 y)). Qed.
Lemma lem1975639 (x : real) (y : real) : (term1067 x y) = (term1067 x y).
Proof. exact (eq_refl (term1067 x y)). Qed.
Lemma lem1975642 (x : real) (y : real) : (term1173 x y) = (term1176 x y).
Proof. exact (MK_COMB (@lem1975639 x y) (@lem1975624 x y)). Qed.
Lemma lem1975643 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975644 (x : real) (y : real) : (term1177 x y) = (term1178 x y).
Proof. exact (MK_COMB (@lem1975643) (@lem1975642 x y)). Qed.
Lemma lem1975645 (x : real) (y : real) : (term1179 x y) = (term1180 x y).
Proof. exact (MK_COMB (@lem1975644 x y) (@lem1975605)). Qed.
Lemma lem1975646 (x : real) (y : real) : (term1180 x y) = (term1181 x y).
Proof. exact (@lem1483519 (term1176 x y) term121). Qed.
Lemma lem1975648 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975649 : term139 = term121.
Proof. exact (@lem1975648 term22). Qed.
Lemma lem1975650 (x : real) (y : real) : (term1182 x y) = (term1182 x y).
Proof. exact (eq_refl (term1182 x y)). Qed.
Lemma lem1975651 (x : real) (y : real) : (term1181 x y) = (term1183 x y).
Proof. exact (MK_COMB (@lem1975650 x y) (@lem1975649)). Qed.
Lemma lem1975652 (x : real) (y : real) : (term1183 x y) = (term1176 x y).
Proof. exact (@lem1483450 (term1176 x y)). Qed.
Lemma lem1975653 (x : real) (y : real) : (term1181 x y) = (term1176 x y).
Proof. exact (TRANS (@lem1975651 x y) (@lem1975652 x y)). Qed.
Lemma lem1975654 (x : real) (y : real) : (term1180 x y) = (term1176 x y).
Proof. exact (TRANS (@lem1975646 x y) (@lem1975653 x y)). Qed.
Lemma lem1975655 (x : real) (y : real) : (term1179 x y) = (term1176 x y).
Proof. exact (TRANS (@lem1975645 x y) (@lem1975654 x y)). Qed.
Lemma lem1975656 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975657 (x : real) (y : real) : (term1184 x y) = (term1185 x y).
Proof. exact (MK_COMB (@lem1975656) (@lem1975655 x y)). Qed.
Lemma lem1975658 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975659 (x : real) (y : real) : (term1172 x y) = (term1186 x y).
Proof. exact (MK_COMB (@lem1975657 x y) (@lem1975658)). Qed.
Lemma lem1975660 (x : real) (y : real) : (term1171 x y) = (term1186 x y).
Proof. exact (TRANS (@lem1975604 x y) (@lem1975659 x y)). Qed.
Lemma lem1975661 (x : real) (y : real) : (term1187 x y) = (term1188 x y).
Proof. exact (@lem1483525 (term1189 x y) term121). Qed.
Lemma lem1975662 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975669 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1975678 (y : real) : (term354 y) = (term354 y).
Proof. exact (eq_refl (term354 y)). Qed.
Lemma lem1975679 (y : real) : (term1190 y) = (term1191 y).
Proof. exact (MK_COMB (@lem1975678 y) (@lem1975669 y)). Qed.
Lemma lem1975680 (y : real) : (term1191 y) = (term1192 y).
Proof. exact (@lem1483438 term28 term16 y). Qed.
Lemma lem1975681 : term1193 = term1194.
Proof. exact (@lem1367763 term23 term22). Qed.
Lemma lem1975682 : term1029 = term1030.
Proof. exact (@lem706949). Qed.
Lemma lem1975683 : (term1029 = term1030) = (term1031 = term1032).
Proof. exact (@lem1006570 term25 (BIT1 0) term1030). Qed.
Lemma lem1975684 : term1031 = term1032.
Proof. exact (EQ_MP (@lem1975683) (@lem1975682)). Qed.
Lemma lem1975685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1975686 : term1028 = term1033.
Proof. exact (MK_COMB (@lem1975685) (@lem1975684)). Qed.
Lemma lem1975687 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1975688 : term1194 = term1195.
Proof. exact (MK_COMB (@lem1975687) (@lem1975686)). Qed.
Lemma lem1975689 : term1193 = term1195.
Proof. exact (TRANS (@lem1975681) (@lem1975688)). Qed.
Lemma lem1975690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1975691 : term1196 = term1197.
Proof. exact (MK_COMB (@lem1975690) (@lem1975689)). Qed.
Lemma lem1975692 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1975693 (y : real) : (term1192 y) = (term1198 y).
Proof. exact (MK_COMB (@lem1975691) (@lem1975692 y)). Qed.
Lemma lem1975694 (y : real) : (term1191 y) = (term1198 y).
Proof. exact (TRANS (@lem1975680 y) (@lem1975693 y)). Qed.
Lemma lem1975695 (y : real) : (term1190 y) = (term1198 y).
Proof. exact (TRANS (@lem1975679 y) (@lem1975694 y)). Qed.
Lemma lem1975698 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1975701 (x : real) (y : real) : (term1199 x y) = (term1200 x y).
Proof. exact (MK_COMB (@lem1975698 x) (@lem1975695 y)). Qed.
Lemma lem1975716 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1975719 (x : real) (y : real) : (term1189 x y) = (term1201 x y).
Proof. exact (MK_COMB (@lem1975716 x y) (@lem1975701 x y)). Qed.
Lemma lem1975720 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975721 (x : real) (y : real) : (term1202 x y) = (term1203 x y).
Proof. exact (MK_COMB (@lem1975720) (@lem1975719 x y)). Qed.
Lemma lem1975722 (x : real) (y : real) : (term1204 x y) = (term1205 x y).
Proof. exact (MK_COMB (@lem1975721 x y) (@lem1975662)). Qed.
Lemma lem1975723 (x : real) (y : real) : (term1205 x y) = (term1206 x y).
Proof. exact (@lem1483519 (term1201 x y) term121). Qed.
Lemma lem1975725 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975726 : term139 = term121.
Proof. exact (@lem1975725 term22). Qed.
Lemma lem1975727 (x : real) (y : real) : (term1207 x y) = (term1207 x y).
Proof. exact (eq_refl (term1207 x y)). Qed.
Lemma lem1975728 (x : real) (y : real) : (term1206 x y) = (term1208 x y).
Proof. exact (MK_COMB (@lem1975727 x y) (@lem1975726)). Qed.
Lemma lem1975729 (x : real) (y : real) : (term1208 x y) = (term1201 x y).
Proof. exact (@lem1483450 (term1201 x y)). Qed.
Lemma lem1975730 (x : real) (y : real) : (term1206 x y) = (term1201 x y).
Proof. exact (TRANS (@lem1975728 x y) (@lem1975729 x y)). Qed.
Lemma lem1975731 (x : real) (y : real) : (term1205 x y) = (term1201 x y).
Proof. exact (TRANS (@lem1975723 x y) (@lem1975730 x y)). Qed.
Lemma lem1975732 (x : real) (y : real) : (term1204 x y) = (term1201 x y).
Proof. exact (TRANS (@lem1975722 x y) (@lem1975731 x y)). Qed.
Lemma lem1975733 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975734 (x : real) (y : real) : (term1209 x y) = (term1210 x y).
Proof. exact (MK_COMB (@lem1975733) (@lem1975732 x y)). Qed.
Lemma lem1975735 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975736 (x : real) (y : real) : (term1188 x y) = (term1211 x y).
Proof. exact (MK_COMB (@lem1975734 x y) (@lem1975735)). Qed.
Lemma lem1975737 (x : real) (y : real) : (term1187 x y) = (term1211 x y).
Proof. exact (TRANS (@lem1975661 x y) (@lem1975736 x y)). Qed.
Lemma lem1975738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975739 (x : real) (y : real) : (term1212 x y) = (term1213 x y).
Proof. exact (MK_COMB (@lem1975738) (@lem1975660 x y)). Qed.
Lemma lem1975740 (x : real) (y : real) : (term1214 x y) = (term1215 x y).
Proof. exact (MK_COMB (@lem1975739 x y) (@lem1975737 x y)). Qed.
Lemma lem1975741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975742 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975741) (@lem1975074 y)). Qed.
Lemma lem1975743 (x : real) (y : real) : (term1216 x y) = (term1217 x y).
Proof. exact (MK_COMB (@lem1975742 y) (@lem1975740 x y)). Qed.
Lemma lem1975744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975745 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975744) (@lem1975053 x)). Qed.
Lemma lem1975746 (x : real) (y : real) : (term1218 x y) = (term1219 x y).
Proof. exact (MK_COMB (@lem1975745 x) (@lem1975743 x y)). Qed.
Lemma lem1975747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975748 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1975747) (@lem1975026 x y)). Qed.
Lemma lem1975749 (x : real) (y : real) : (term1220 x y) = (term1221 x y).
Proof. exact (MK_COMB (@lem1975748 x y) (@lem1975746 x y)). Qed.
Lemma lem1975750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975751 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975750) (@lem1975053 x)). Qed.
Lemma lem1975752 (x : real) (y : real) : (term1123 x y) = (term1222 x y).
Proof. exact (MK_COMB (@lem1975751 x) (@lem1975749 x y)). Qed.
Lemma lem1975753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975754 (y : real) : (term994 y) = (term186 y).
Proof. exact (MK_COMB (@lem1975753) (@lem1975603 y)). Qed.
Lemma lem1975755 (x : real) (y : real) : (term1125 x y) = (term1223 x y).
Proof. exact (MK_COMB (@lem1975754 y) (@lem1975752 x y)). Qed.
Lemma lem1975756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1975757 (x : real) (y : real) : (term1131 x y) = (term1224 x y).
Proof. exact (MK_COMB (@lem1975756) (@lem1975584 x y)). Qed.
Lemma lem1975758 (x : real) (y : real) : (term1132 x y) = (term1225 x y).
Proof. exact (MK_COMB (@lem1975757 x y) (@lem1975755 x y)). Qed.
Lemma lem1975770 (x : real) (y : real) : (term1116 x y) = (term1225 x y).
Proof. exact (TRANS (@lem1975437 x y) (@lem1975758 x y)). Qed.
Lemma lem1975772 (x : real) (y : real) : (term1226 x y) = (term1059 x y).
Proof. exact (eq_refl (term1226 x y)). Qed.
Lemma lem1975773 (x : real) (y : real) : (term1059 x y) = (term1226 x y).
Proof. exact (SYM (@lem1975772 x y)). Qed.
Lemma lem1975774 (x : real) (y : real) : (term1226 x y) = (term1227 x y).
Proof. exact (@lem1482981 (term1228 x y) y). Qed.
Lemma lem1975775 (x : real) (y : real) : (term1059 x y) = (term1227 x y).
Proof. exact (TRANS (@lem1975773 x y) (@lem1975774 x y)). Qed.
Lemma lem1975776 (x : real) (y : real) : (term1229 x y) = (term1230 x y).
Proof. exact (eq_refl (term1229 x y)). Qed.
Lemma lem1975777 (y : real) : (term994 y) = (term994 y).
Proof. exact (eq_refl (term994 y)). Qed.
Lemma lem1975778 (x : real) (y : real) : (term1231 x y) = (term1232 x y).
Proof. exact (MK_COMB (@lem1975777 y) (@lem1975776 x y)). Qed.
Lemma lem1975779 (x : real) (y : real) : (term1233 x y) = (term1234 x y).
Proof. exact (eq_refl (term1233 x y)). Qed.
Lemma lem1975780 (y : real) : (term755 y) = (term755 y).
Proof. exact (eq_refl (term755 y)). Qed.
Lemma lem1975781 (x : real) (y : real) : (term1235 x y) = (term1236 x y).
Proof. exact (MK_COMB (@lem1975780 y) (@lem1975779 x y)). Qed.
Lemma lem1975782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1975783 (x : real) (y : real) : (term1237 x y) = (term1238 x y).
Proof. exact (MK_COMB (@lem1975782) (@lem1975781 x y)). Qed.
Lemma lem1975784 (x : real) (y : real) : (term1227 x y) = (term1239 x y).
Proof. exact (MK_COMB (@lem1975783 x y) (@lem1975778 x y)). Qed.
Lemma lem1975785 (x : real) (y : real) : (term1240 x y) = (term1240 x y).
Proof. exact (eq_refl (term1240 x y)). Qed.
Lemma lem1975786 (x : real) (y : real) : ((term1059 x y) = (term1227 x y)) = ((term1059 x y) = (term1239 x y)).
Proof. exact (MK_COMB (@lem1975785 x y) (@lem1975784 x y)). Qed.
Lemma lem1975787 (x : real) (y : real) : (term1059 x y) = (term1239 x y).
Proof. exact (EQ_MP (@lem1975786 x y) (@lem1975775 x y)). Qed.
Lemma lem1975788 (x : real) (y : real) : (term1241 x y) = (term1242 x y).
Proof. exact (@lem1483527 (term1243 x y) term121). Qed.
Lemma lem1975818 (x : real) (y : real) : (term1244 x y) = (term1245 x y).
Proof. exact (@lem1483519 (term1243 x y) term121). Qed.
Lemma lem1975820 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975821 : term139 = term121.
Proof. exact (@lem1975820 term22). Qed.
Lemma lem1975822 (x : real) (y : real) : (term1246 x y) = (term1246 x y).
Proof. exact (eq_refl (term1246 x y)). Qed.
Lemma lem1975823 (x : real) (y : real) : (term1245 x y) = (term1247 x y).
Proof. exact (MK_COMB (@lem1975822 x y) (@lem1975821)). Qed.
Lemma lem1975824 (x : real) (y : real) : (term1247 x y) = (term1243 x y).
Proof. exact (@lem1483450 (term1243 x y)). Qed.
Lemma lem1975825 (x : real) (y : real) : (term1245 x y) = (term1243 x y).
Proof. exact (TRANS (@lem1975823 x y) (@lem1975824 x y)). Qed.
Lemma lem1975827 (x : real) (y : real) : (term1244 x y) = (term1243 x y).
Proof. exact (TRANS (@lem1975818 x y) (@lem1975825 x y)). Qed.
Lemma lem1975828 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975829 (x : real) (y : real) : (term1248 x y) = (term1249 x y).
Proof. exact (MK_COMB (@lem1975828) (@lem1975827 x y)). Qed.
Lemma lem1975830 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975831 (x : real) (y : real) : (term1242 x y) = (term1241 x y).
Proof. exact (MK_COMB (@lem1975829 x y) (@lem1975830)). Qed.
Lemma lem1975832 (x : real) (y : real) : (term1241 x y) = (term1241 x y).
Proof. exact (TRANS (@lem1975788 x y) (@lem1975831 x y)). Qed.
Lemma lem1975833 (x : real) (y : real) : (term1250 x y) = (term1251 x y).
Proof. exact (@lem1483525 (term1252 x y) term121). Qed.
Lemma lem1975834 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975846 (y : real) : (term1146 y) = (term1147 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1975849 : term421 = term16.
Proof. exact (@lem1367767 term22 term22). Qed.
Lemma lem1975850 : term89 = term25.
Proof. exact (@lem706885). Qed.
Lemma lem1975851 : (term89 = term25) = (term90 = term23).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term25). Qed.
Lemma lem1975852 : term90 = term23.
Proof. exact (EQ_MP (@lem1975851) (@lem1975850)). Qed.
Lemma lem1975853 : term23 = term90.
Proof. exact (SYM (@lem1975852)). Qed.
Lemma lem1975854 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1975855 : term17 = term91.
Proof. exact (MK_COMB (@lem1975854) (@lem1975853)). Qed.
Lemma lem1975856 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1975857 : term28 = term88.
Proof. exact (MK_COMB (@lem1975856) (@lem1975855)). Qed.
Lemma lem1975858 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1975859 : term422 = term423.
Proof. exact (MK_COMB (@lem1975858) (@lem1975857)). Qed.
Lemma lem1975860 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem1975861 : term424 = term421.
Proof. exact (MK_COMB (@lem1975859) (@lem1975860)). Qed.
Lemma lem1975862 : term424 = term16.
Proof. exact (TRANS (@lem1975861) (@lem1975849)). Qed.
Lemma lem1975863 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1975864 : term425 = term77.
Proof. exact (MK_COMB (@lem1975863) (@lem1975862)). Qed.
Lemma lem1975865 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1975866 (y : real) : (term1147 y) = (term52 y).
Proof. exact (MK_COMB (@lem1975864) (@lem1975865 y)). Qed.
Lemma lem1975868 (y : real) : (term1146 y) = (term52 y).
Proof. exact (TRANS (@lem1975846 y) (@lem1975866 y)). Qed.
Lemma lem1975877 (x : real) : (term1038 x) = (term1038 x).
Proof. exact (eq_refl (term1038 x)). Qed.
Lemma lem1975880 (x : real) (y : real) : (term1253 x y) = (term1254 x y).
Proof. exact (MK_COMB (@lem1975877 x) (@lem1975868 y)). Qed.
Lemma lem1975895 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1975898 (x : real) (y : real) : (term1252 x y) = (term1255 x y).
Proof. exact (MK_COMB (@lem1975895 x y) (@lem1975880 x y)). Qed.
Lemma lem1975899 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975900 (x : real) (y : real) : (term1256 x y) = (term1257 x y).
Proof. exact (MK_COMB (@lem1975899) (@lem1975898 x y)). Qed.
Lemma lem1975901 (x : real) (y : real) : (term1258 x y) = (term1259 x y).
Proof. exact (MK_COMB (@lem1975900 x y) (@lem1975834)). Qed.
Lemma lem1975902 (x : real) (y : real) : (term1259 x y) = (term1260 x y).
Proof. exact (@lem1483519 (term1255 x y) term121). Qed.
Lemma lem1975904 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975905 : term139 = term121.
Proof. exact (@lem1975904 term22). Qed.
Lemma lem1975906 (x : real) (y : real) : (term1261 x y) = (term1261 x y).
Proof. exact (eq_refl (term1261 x y)). Qed.
Lemma lem1975907 (x : real) (y : real) : (term1260 x y) = (term1262 x y).
Proof. exact (MK_COMB (@lem1975906 x y) (@lem1975905)). Qed.
Lemma lem1975908 (x : real) (y : real) : (term1262 x y) = (term1255 x y).
Proof. exact (@lem1483450 (term1255 x y)). Qed.
Lemma lem1975909 (x : real) (y : real) : (term1260 x y) = (term1255 x y).
Proof. exact (TRANS (@lem1975907 x y) (@lem1975908 x y)). Qed.
Lemma lem1975910 (x : real) (y : real) : (term1259 x y) = (term1255 x y).
Proof. exact (TRANS (@lem1975902 x y) (@lem1975909 x y)). Qed.
Lemma lem1975911 (x : real) (y : real) : (term1258 x y) = (term1255 x y).
Proof. exact (TRANS (@lem1975901 x y) (@lem1975910 x y)). Qed.
Lemma lem1975912 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1975913 (x : real) (y : real) : (term1263 x y) = (term1264 x y).
Proof. exact (MK_COMB (@lem1975912) (@lem1975911 x y)). Qed.
Lemma lem1975914 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975915 (x : real) (y : real) : (term1251 x y) = (term1265 x y).
Proof. exact (MK_COMB (@lem1975913 x y) (@lem1975914)). Qed.
Lemma lem1975916 (x : real) (y : real) : (term1250 x y) = (term1265 x y).
Proof. exact (TRANS (@lem1975833 x y) (@lem1975915 x y)). Qed.
Lemma lem1975917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975918 (x : real) (y : real) : (term1266 x y) = (term1266 x y).
Proof. exact (MK_COMB (@lem1975917) (@lem1975832 x y)). Qed.
Lemma lem1975919 (x : real) (y : real) : (term1267 x y) = (term1268 x y).
Proof. exact (MK_COMB (@lem1975918 x y) (@lem1975916 x y)). Qed.
Lemma lem1975920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975921 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975920) (@lem1975074 y)). Qed.
Lemma lem1975922 (x : real) (y : real) : (term1269 x y) = (term1270 x y).
Proof. exact (MK_COMB (@lem1975921 y) (@lem1975919 x y)). Qed.
Lemma lem1975923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975924 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1975923) (@lem1975053 x)). Qed.
Lemma lem1975925 (x : real) (y : real) : (term1271 x y) = (term1272 x y).
Proof. exact (MK_COMB (@lem1975924 x) (@lem1975922 x y)). Qed.
Lemma lem1975926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975927 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1975926) (@lem1975026 x y)). Qed.
Lemma lem1975928 (x : real) (y : real) : (term1273 x y) = (term1274 x y).
Proof. exact (MK_COMB (@lem1975927 x y) (@lem1975925 x y)). Qed.
Lemma lem1975929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975930 (x : real) : (term755 x) = (term755 x).
Proof. exact (MK_COMB (@lem1975929) (@lem1974993 x)). Qed.
Lemma lem1975931 (x : real) (y : real) : (term1234 x y) = (term1275 x y).
Proof. exact (MK_COMB (@lem1975930 x) (@lem1975928 x y)). Qed.
Lemma lem1975932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1975933 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1975932) (@lem1975074 y)). Qed.
Lemma lem1975934 (x : real) (y : real) : (term1236 x y) = (term1276 x y).
Proof. exact (MK_COMB (@lem1975933 y) (@lem1975931 x y)). Qed.
Lemma lem1975935 (x : real) (y : real) : (term1277 x y) = (term1278 x y).
Proof. exact (@lem1483527 (term1279 x y) term121). Qed.
Lemma lem1975936 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975943 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1975946 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1975949 (x : real) (y : real) : (term1280 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1975946 x) (@lem1975943 y)). Qed.
Lemma lem1975964 (x : real) (y : real) : (term1067 x y) = (term1067 x y).
Proof. exact (eq_refl (term1067 x y)). Qed.
Lemma lem1975967 (x : real) (y : real) : (term1279 x y) = (term1281 x y).
Proof. exact (MK_COMB (@lem1975964 x y) (@lem1975949 x y)). Qed.
Lemma lem1975968 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1975969 (x : real) (y : real) : (term1282 x y) = (term1283 x y).
Proof. exact (MK_COMB (@lem1975968) (@lem1975967 x y)). Qed.
Lemma lem1975970 (x : real) (y : real) : (term1284 x y) = (term1285 x y).
Proof. exact (MK_COMB (@lem1975969 x y) (@lem1975936)). Qed.
Lemma lem1975971 (x : real) (y : real) : (term1285 x y) = (term1286 x y).
Proof. exact (@lem1483519 (term1281 x y) term121). Qed.
Lemma lem1975973 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1975974 : term139 = term121.
Proof. exact (@lem1975973 term22). Qed.
Lemma lem1975975 (x : real) (y : real) : (term1287 x y) = (term1287 x y).
Proof. exact (eq_refl (term1287 x y)). Qed.
Lemma lem1975976 (x : real) (y : real) : (term1286 x y) = (term1288 x y).
Proof. exact (MK_COMB (@lem1975975 x y) (@lem1975974)). Qed.
Lemma lem1975977 (x : real) (y : real) : (term1288 x y) = (term1281 x y).
Proof. exact (@lem1483450 (term1281 x y)). Qed.
Lemma lem1975978 (x : real) (y : real) : (term1286 x y) = (term1281 x y).
Proof. exact (TRANS (@lem1975976 x y) (@lem1975977 x y)). Qed.
Lemma lem1975979 (x : real) (y : real) : (term1285 x y) = (term1281 x y).
Proof. exact (TRANS (@lem1975971 x y) (@lem1975978 x y)). Qed.
Lemma lem1975980 (x : real) (y : real) : (term1284 x y) = (term1281 x y).
Proof. exact (TRANS (@lem1975970 x y) (@lem1975979 x y)). Qed.
Lemma lem1975981 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1975982 (x : real) (y : real) : (term1289 x y) = (term1290 x y).
Proof. exact (MK_COMB (@lem1975981) (@lem1975980 x y)). Qed.
Lemma lem1975983 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975984 (x : real) (y : real) : (term1278 x y) = (term1291 x y).
Proof. exact (MK_COMB (@lem1975982 x y) (@lem1975983)). Qed.
Lemma lem1975985 (x : real) (y : real) : (term1277 x y) = (term1291 x y).
Proof. exact (TRANS (@lem1975935 x y) (@lem1975984 x y)). Qed.
Lemma lem1975986 (x : real) (y : real) : (term1292 x y) = (term1293 x y).
Proof. exact (@lem1483525 (term1294 x y) term121). Qed.
Lemma lem1975987 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1975994 (y : real) : (real_neg y) = (term52 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1976003 (y : real) : (term354 y) = (term354 y).
Proof. exact (eq_refl (term354 y)). Qed.
Lemma lem1976004 (y : real) : (term1190 y) = (term1191 y).
Proof. exact (MK_COMB (@lem1976003 y) (@lem1975994 y)). Qed.
Lemma lem1976005 (y : real) : (term1191 y) = (term1192 y).
Proof. exact (@lem1483438 term28 term16 y). Qed.
Lemma lem1976006 : term1193 = term1194.
Proof. exact (@lem1367763 term23 term22). Qed.
Lemma lem1976007 : term1029 = term1030.
Proof. exact (@lem706949). Qed.
Lemma lem1976008 : (term1029 = term1030) = (term1031 = term1032).
Proof. exact (@lem1006570 term25 (BIT1 0) term1030). Qed.
Lemma lem1976009 : term1031 = term1032.
Proof. exact (EQ_MP (@lem1976008) (@lem1976007)). Qed.
Lemma lem1976010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976011 : term1028 = term1033.
Proof. exact (MK_COMB (@lem1976010) (@lem1976009)). Qed.
Lemma lem1976012 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976013 : term1194 = term1195.
Proof. exact (MK_COMB (@lem1976012) (@lem1976011)). Qed.
Lemma lem1976014 : term1193 = term1195.
Proof. exact (TRANS (@lem1976006) (@lem1976013)). Qed.
Lemma lem1976015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976016 : term1196 = term1197.
Proof. exact (MK_COMB (@lem1976015) (@lem1976014)). Qed.
Lemma lem1976017 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976018 (y : real) : (term1192 y) = (term1198 y).
Proof. exact (MK_COMB (@lem1976016) (@lem1976017 y)). Qed.
Lemma lem1976019 (y : real) : (term1191 y) = (term1198 y).
Proof. exact (TRANS (@lem1976005 y) (@lem1976018 y)). Qed.
Lemma lem1976020 (y : real) : (term1190 y) = (term1198 y).
Proof. exact (TRANS (@lem1976004 y) (@lem1976019 y)). Qed.
Lemma lem1976029 (x : real) : (term1038 x) = (term1038 x).
Proof. exact (eq_refl (term1038 x)). Qed.
Lemma lem1976032 (x : real) (y : real) : (term1295 x y) = (term1296 x y).
Proof. exact (MK_COMB (@lem1976029 x) (@lem1976020 y)). Qed.
Lemma lem1976047 (x : real) (y : real) : (term978 x y) = (term978 x y).
Proof. exact (eq_refl (term978 x y)). Qed.
Lemma lem1976050 (x : real) (y : real) : (term1294 x y) = (term1297 x y).
Proof. exact (MK_COMB (@lem1976047 x y) (@lem1976032 x y)). Qed.
Lemma lem1976051 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1976052 (x : real) (y : real) : (term1298 x y) = (term1299 x y).
Proof. exact (MK_COMB (@lem1976051) (@lem1976050 x y)). Qed.
Lemma lem1976053 (x : real) (y : real) : (term1300 x y) = (term1301 x y).
Proof. exact (MK_COMB (@lem1976052 x y) (@lem1975987)). Qed.
Lemma lem1976054 (x : real) (y : real) : (term1301 x y) = (term1302 x y).
Proof. exact (@lem1483519 (term1297 x y) term121). Qed.
Lemma lem1976056 (x : nat) : (term140 x) = term121.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1976057 : term139 = term121.
Proof. exact (@lem1976056 term22). Qed.
Lemma lem1976058 (x : real) (y : real) : (term1303 x y) = (term1303 x y).
Proof. exact (eq_refl (term1303 x y)). Qed.
Lemma lem1976059 (x : real) (y : real) : (term1302 x y) = (term1304 x y).
Proof. exact (MK_COMB (@lem1976058 x y) (@lem1976057)). Qed.
Lemma lem1976060 (x : real) (y : real) : (term1304 x y) = (term1297 x y).
Proof. exact (@lem1483450 (term1297 x y)). Qed.
Lemma lem1976061 (x : real) (y : real) : (term1302 x y) = (term1297 x y).
Proof. exact (TRANS (@lem1976059 x y) (@lem1976060 x y)). Qed.
Lemma lem1976062 (x : real) (y : real) : (term1301 x y) = (term1297 x y).
Proof. exact (TRANS (@lem1976054 x y) (@lem1976061 x y)). Qed.
Lemma lem1976063 (x : real) (y : real) : (term1300 x y) = (term1297 x y).
Proof. exact (TRANS (@lem1976053 x y) (@lem1976062 x y)). Qed.
Lemma lem1976064 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976065 (x : real) (y : real) : (term1305 x y) = (term1306 x y).
Proof. exact (MK_COMB (@lem1976064) (@lem1976063 x y)). Qed.
Lemma lem1976066 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976067 (x : real) (y : real) : (term1293 x y) = (term1307 x y).
Proof. exact (MK_COMB (@lem1976065 x y) (@lem1976066)). Qed.
Lemma lem1976068 (x : real) (y : real) : (term1292 x y) = (term1307 x y).
Proof. exact (TRANS (@lem1975986 x y) (@lem1976067 x y)). Qed.
Lemma lem1976069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976070 (x : real) (y : real) : (term1308 x y) = (term1309 x y).
Proof. exact (MK_COMB (@lem1976069) (@lem1975985 x y)). Qed.
Lemma lem1976071 (x : real) (y : real) : (term1310 x y) = (term1311 x y).
Proof. exact (MK_COMB (@lem1976070 x y) (@lem1976068 x y)). Qed.
Lemma lem1976072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976073 (y : real) : (term755 y) = (term755 y).
Proof. exact (MK_COMB (@lem1976072) (@lem1975074 y)). Qed.
Lemma lem1976074 (x : real) (y : real) : (term1312 x y) = (term1313 x y).
Proof. exact (MK_COMB (@lem1976073 y) (@lem1976071 x y)). Qed.
Lemma lem1976075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976076 (x : real) : (term186 x) = (term186 x).
Proof. exact (MK_COMB (@lem1976075) (@lem1975053 x)). Qed.
Lemma lem1976077 (x : real) (y : real) : (term1314 x y) = (term1315 x y).
Proof. exact (MK_COMB (@lem1976076 x) (@lem1976074 x y)). Qed.
Lemma lem1976078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976079 (x : real) (y : real) : (term620 x y) = (term620 x y).
Proof. exact (MK_COMB (@lem1976078) (@lem1975026 x y)). Qed.
Lemma lem1976080 (x : real) (y : real) : (term1316 x y) = (term1317 x y).
Proof. exact (MK_COMB (@lem1976079 x y) (@lem1976077 x y)). Qed.
Lemma lem1976081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976082 (x : real) : (term755 x) = (term755 x).
Proof. exact (MK_COMB (@lem1976081) (@lem1974993 x)). Qed.
Lemma lem1976083 (x : real) (y : real) : (term1230 x y) = (term1318 x y).
Proof. exact (MK_COMB (@lem1976082 x) (@lem1976080 x y)). Qed.
Lemma lem1976084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1976085 (y : real) : (term994 y) = (term186 y).
Proof. exact (MK_COMB (@lem1976084) (@lem1975603 y)). Qed.
Lemma lem1976086 (x : real) (y : real) : (term1232 x y) = (term1319 x y).
Proof. exact (MK_COMB (@lem1976085 y) (@lem1976083 x y)). Qed.
Lemma lem1976087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1976088 (x : real) (y : real) : (term1238 x y) = (term1320 x y).
Proof. exact (MK_COMB (@lem1976087) (@lem1975934 x y)). Qed.
Lemma lem1976089 (x : real) (y : real) : (term1239 x y) = (term1321 x y).
Proof. exact (MK_COMB (@lem1976088 x y) (@lem1976086 x y)). Qed.
Lemma lem1976101 (x : real) (y : real) : (term1059 x y) = (term1321 x y).
Proof. exact (TRANS (@lem1975787 x y) (@lem1976089 x y)). Qed.
Lemma lem1976102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1976103 (x : real) (y : real) : (term1117 x y) = (term1322 x y).
Proof. exact (MK_COMB (@lem1976102) (@lem1976101 x y)). Qed.
Lemma lem1976104 (x : real) (y : real) : (term1118 x y) = (term1323 x y).
Proof. exact (MK_COMB (@lem1976103 x y) (@lem1975770 x y)). Qed.
Lemma lem1976106 (x : real) (y : real) : (term988 x y) = (term1323 x y).
Proof. exact (TRANS (@lem1975420 x y) (@lem1976104 x y)). Qed.
Lemma lem1976107 (x : real) (y : real) (h1 : term1323 x y) : term1323 x y.
Proof. exact (h1). Qed.
Lemma lem1976108 (x : real) (y : real) (h1 : term1321 x y) : term1321 x y.
Proof. exact (h1). Qed.
Lemma lem1976109 (x : real) (y : real) (h1 : term1276 x y) : term1276 x y.
Proof. exact (h1). Qed.
Lemma lem1976110 (x : real) (y : real) (h1 : term1276 x y) : term1275 x y.
Proof. exact (proj2 (@lem1976109 x y h1)). Qed.
Lemma lem1976112 (x : real) (y : real) (h1 : term1276 x y) : term1274 x y.
Proof. exact (proj2 (@lem1976110 x y h1)). Qed.
Lemma lem1976113 (x : real) (y : real) (h1 : term1276 x y) : term184 x.
Proof. exact (proj1 (@lem1976110 x y h1)). Qed.
Lemma lem1976114 (x : real) (y : real) (h1 : term1276 x y) : term1272 x y.
Proof. exact (proj2 (@lem1976112 x y h1)). Qed.
Lemma lem1976117 (x : real) (y : real) (h1 : term1276 x y) : term177 x.
Proof. exact (proj1 (@lem1976114 x y h1)). Qed.
Lemma lem1976123 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976124 : term368 = term369.
Proof. exact (@lem1976123 (NUMERAL 0) term22). Qed.
Lemma lem1976125 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1976126 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1976127 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1976126 h1) (fun h1 : term369 = True => @lem1976125)). Qed.
Lemma lem1976128 : term369 = True.
Proof. exact (EQ_MP (@lem1976127) (@lem1976125)). Qed.
Lemma lem1976129 : term368 = True.
Proof. exact (TRANS (@lem1976124) (@lem1976128)). Qed.
Lemma lem1976130 : True = term368.
Proof. exact (SYM (@lem1976129)). Qed.
Lemma lem1976131 : term368.
Proof. exact (EQ_MP (@lem1976130) (@lem0)). Qed.
Lemma lem1976132 (x : real) (y : real) (h1 : term1276 x y) : term371 x.
Proof. exact (conj (@lem1976131) (@lem1976113 x y h1)). Qed.
Lemma lem1976134 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976135 (x : real) : term373 x.
Proof. exact (@lem1976134 term71 x). Qed.
Lemma lem1976136 (x : real) (y : real) (h1 : term1276 x y) : term374 x.
Proof. exact (@lem1976135 x (@lem1976132 x y h1)). Qed.
Lemma lem1976137 (x : real) : (term199 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1976138 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1976139 (x : real) : (term375 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1976138) (@lem1976137 x)). Qed.
Lemma lem1976140 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976141 (x : real) : (term374 x) = (term184 x).
Proof. exact (MK_COMB (@lem1976139 x) (@lem1976140)). Qed.
Lemma lem1976142 (x : real) (y : real) (h1 : term1276 x y) : term184 x.
Proof. exact (EQ_MP (@lem1976141 x) (@lem1976136 x y h1)). Qed.
Lemma lem1976144 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976145 : term368 = term369.
Proof. exact (@lem1976144 (NUMERAL 0) term22). Qed.
Lemma lem1976146 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1976147 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1976148 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1976147 h1) (fun h1 : term369 = True => @lem1976146)). Qed.
Lemma lem1976149 : term369 = True.
Proof. exact (EQ_MP (@lem1976148) (@lem1976146)). Qed.
Lemma lem1976150 : term368 = True.
Proof. exact (TRANS (@lem1976145) (@lem1976149)). Qed.
Lemma lem1976151 : True = term368.
Proof. exact (SYM (@lem1976150)). Qed.
Lemma lem1976152 : term368.
Proof. exact (EQ_MP (@lem1976151) (@lem0)). Qed.
Lemma lem1976153 (x : real) (y : real) (h1 : term1276 x y) : term380 x.
Proof. exact (conj (@lem1976152) (@lem1976117 x y h1)). Qed.
Lemma lem1976155 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976156 (x : real) : term382 x.
Proof. exact (@lem1976155 term71 (term52 x)). Qed.
Lemma lem1976157 (x : real) (y : real) (h1 : term1276 x y) : term383 x.
Proof. exact (@lem1976156 x (@lem1976153 x y h1)). Qed.
Lemma lem1976158 (x : real) : (term384 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1976159 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976160 (x : real) : (term385 x) = (term176 x).
Proof. exact (MK_COMB (@lem1976159) (@lem1976158 x)). Qed.
Lemma lem1976161 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976162 (x : real) : (term383 x) = (term177 x).
Proof. exact (MK_COMB (@lem1976160 x) (@lem1976161)). Qed.
Lemma lem1976163 (x : real) (y : real) (h1 : term1276 x y) : term177 x.
Proof. exact (EQ_MP (@lem1976162 x) (@lem1976157 x y h1)). Qed.
Lemma lem1976164 (x : real) (y : real) (h1 : term1276 x y) : term394 x.
Proof. exact (conj (@lem1976163 x y h1) (@lem1976142 x y h1)). Qed.
Lemma lem1976166 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976167 (x : real) : term395 x.
Proof. exact (@lem1976166 (term52 x) x). Qed.
Lemma lem1976168 (x : real) (y : real) (h1 : term1276 x y) : term396 x.
Proof. exact (@lem1976167 x (@lem1976164 x y h1)). Qed.
Lemma lem1976169 (x : real) : (term320 x) = (term321 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1976171 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976172 : term122 = term121.
Proof. exact (@lem1976171 term22). Qed.
Lemma lem1976173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976174 : term123 = term124.
Proof. exact (MK_COMB (@lem1976173) (@lem1976172)). Qed.
Lemma lem1976175 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976176 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1976174) (@lem1976175 x)). Qed.
Lemma lem1976177 (x : real) : (term320 x) = (term322 x).
Proof. exact (TRANS (@lem1976169 x) (@lem1976176 x)). Qed.
Lemma lem1976178 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1976179 (x : real) : (term320 x) = term121.
Proof. exact (TRANS (@lem1976177 x) (@lem1976178 x)). Qed.
Lemma lem1976180 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976181 (x : real) : (term397 x) = term143.
Proof. exact (MK_COMB (@lem1976180) (@lem1976179 x)). Qed.
Lemma lem1976182 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976183 (x : real) : (term396 x) = term145.
Proof. exact (MK_COMB (@lem1976181 x) (@lem1976182)). Qed.
Lemma lem1976184 (x : real) (y : real) (h1 : term1276 x y) : term145.
Proof. exact (EQ_MP (@lem1976183 x) (@lem1976168 x y h1)). Qed.
Lemma lem1976186 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976187 : term145 = term152.
Proof. exact (@lem1976186 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1976188 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1976189 : term145 = False.
Proof. exact (TRANS (@lem1976187) (@lem1976188)). Qed.
Lemma lem1976190 (x : real) (y : real) (h1 : term1276 x y) : False.
Proof. exact (EQ_MP (@lem1976189) (@lem1976184 x y h1)). Qed.
Lemma lem1976191 (x : real) (y : real) (h1 : term1319 x y) : term1319 x y.
Proof. exact (h1). Qed.
Lemma lem1976192 (x : real) (y : real) (h1 : term1319 x y) : term1318 x y.
Proof. exact (proj2 (@lem1976191 x y h1)). Qed.
Lemma lem1976194 (x : real) (y : real) (h1 : term1319 x y) : term1317 x y.
Proof. exact (proj2 (@lem1976192 x y h1)). Qed.
Lemma lem1976196 (x : real) (y : real) (h1 : term1319 x y) : term1315 x y.
Proof. exact (proj2 (@lem1976194 x y h1)). Qed.
Lemma lem1976197 (x : real) (y : real) (h1 : term1319 x y) : term604 x y.
Proof. exact (proj1 (@lem1976194 x y h1)). Qed.
Lemma lem1976198 (x : real) (y : real) (h1 : term1319 x y) : term1313 x y.
Proof. exact (proj2 (@lem1976196 x y h1)). Qed.
Lemma lem1976200 (x : real) (y : real) (h1 : term1319 x y) : term1311 x y.
Proof. exact (proj2 (@lem1976198 x y h1)). Qed.
Lemma lem1976202 (x : real) (y : real) (h1 : term1319 x y) : term1307 x y.
Proof. exact (proj2 (@lem1976200 x y h1)). Qed.
Lemma lem1976203 (x : real) (y : real) (h1 : term1319 x y) : term1291 x y.
Proof. exact (proj1 (@lem1976200 x y h1)). Qed.
Lemma lem1976205 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976206 : term1324 = term1325.
Proof. exact (@lem1976205 (NUMERAL 0) term1326). Qed.
Lemma lem1976207 : term1327 = term1328.
Proof. exact (@lem913187). Qed.
Lemma lem1976208 (h1 : term1327 = term1328) : term1325 = True.
Proof. exact (@lem1009824 term1329 0 term1328 h1). Qed.
Lemma lem1976209 : (term1327 = term1328) = (term1325 = True).
Proof. exact (prop_ext (fun h1 : term1327 = term1328 => @lem1976208 h1) (fun h1 : term1325 = True => @lem1976207)). Qed.
Lemma lem1976210 : term1325 = True.
Proof. exact (EQ_MP (@lem1976209) (@lem1976207)). Qed.
Lemma lem1976211 : term1324 = True.
Proof. exact (TRANS (@lem1976206) (@lem1976210)). Qed.
Lemma lem1976212 : True = term1324.
Proof. exact (SYM (@lem1976211)). Qed.
Lemma lem1976213 : term1324.
Proof. exact (EQ_MP (@lem1976212) (@lem0)). Qed.
Lemma lem1976214 (x : real) (y : real) (h1 : term1319 x y) : term1330 x y.
Proof. exact (conj (@lem1976213) (@lem1976197 x y h1)). Qed.
Lemma lem1976216 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976217 (x : real) (y : real) : term1331 x y.
Proof. exact (@lem1976216 term1332 (term190 x y)). Qed.
Lemma lem1976218 (x : real) (y : real) (h1 : term1319 x y) : term1333 x y.
Proof. exact (@lem1976217 x y (@lem1976214 x y h1)). Qed.
Lemma lem1976219 (x : real) (y : real) : (term1334 x y) = (term1335 x y).
Proof. exact (@lem1483508 (term52 x) term1332 y). Qed.
Lemma lem1976220 (y : real) : (term1336 y) = (term1336 y).
Proof. exact (eq_refl (term1336 y)). Qed.
Lemma lem1976221 (x : real) : (term1337 x) = (term1338 x).
Proof. exact (@lem1483476 term1332 term16 x). Qed.
Lemma lem1976223 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976224 : term1339 = term1340.
Proof. exact (@lem1976223 term1326 term22). Qed.
Lemma lem1976225 : term1341 = term1328.
Proof. exact (@lem996237 term1328). Qed.
Lemma lem1976226 : (term1341 = term1328) = (term1342 = term1326).
Proof. exact (@lem1007663 term1328 (BIT1 0) term1328). Qed.
Lemma lem1976227 : term1342 = term1326.
Proof. exact (EQ_MP (@lem1976226) (@lem1976225)). Qed.
Lemma lem1976228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976229 : term1343 = term1332.
Proof. exact (MK_COMB (@lem1976228) (@lem1976227)). Qed.
Lemma lem1976230 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976231 : term1340 = term1344.
Proof. exact (MK_COMB (@lem1976230) (@lem1976229)). Qed.
Lemma lem1976232 : term1339 = term1344.
Proof. exact (TRANS (@lem1976224) (@lem1976231)). Qed.
Lemma lem1976233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976234 : term1345 = term1346.
Proof. exact (MK_COMB (@lem1976233) (@lem1976232)). Qed.
Lemma lem1976235 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976236 (x : real) : (term1338 x) = (term1347 x).
Proof. exact (MK_COMB (@lem1976234) (@lem1976235 x)). Qed.
Lemma lem1976237 (x : real) : (term1337 x) = (term1347 x).
Proof. exact (TRANS (@lem1976221 x) (@lem1976236 x)). Qed.
Lemma lem1976238 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976239 (x : real) : (term1348 x) = (term1349 x).
Proof. exact (MK_COMB (@lem1976238) (@lem1976237 x)). Qed.
Lemma lem1976240 (x : real) (y : real) : (term1335 x y) = (term1350 x y).
Proof. exact (MK_COMB (@lem1976239 x) (@lem1976220 y)). Qed.
Lemma lem1976241 (x : real) (y : real) : (term1334 x y) = (term1350 x y).
Proof. exact (TRANS (@lem1976219 x y) (@lem1976240 x y)). Qed.
Lemma lem1976242 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1976243 (x : real) (y : real) : (term1351 x y) = (term1352 x y).
Proof. exact (MK_COMB (@lem1976242) (@lem1976241 x y)). Qed.
Lemma lem1976244 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976245 (x : real) (y : real) : (term1333 x y) = (term1353 x y).
Proof. exact (MK_COMB (@lem1976243 x y) (@lem1976244)). Qed.
Lemma lem1976246 (x : real) (y : real) (h1 : term1319 x y) : term1353 x y.
Proof. exact (EQ_MP (@lem1976245 x y) (@lem1976218 x y h1)). Qed.
Lemma lem1976248 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976249 : term1354 = term1355.
Proof. exact (@lem1976248 (NUMERAL 0) term23). Qed.
Lemma lem1976250 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976251 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976252 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976251 h1) (fun h1 : term1355 = True => @lem1976250)). Qed.
Lemma lem1976253 : term1355 = True.
Proof. exact (EQ_MP (@lem1976252) (@lem1976250)). Qed.
Lemma lem1976254 : term1354 = True.
Proof. exact (TRANS (@lem1976249) (@lem1976253)). Qed.
Lemma lem1976255 : True = term1354.
Proof. exact (SYM (@lem1976254)). Qed.
Lemma lem1976256 : term1354.
Proof. exact (EQ_MP (@lem1976255) (@lem0)). Qed.
Lemma lem1976257 (x : real) (y : real) (h1 : term1319 x y) : term1357 x y.
Proof. exact (conj (@lem1976256) (@lem1976203 x y h1)). Qed.
Lemma lem1976259 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976260 (x : real) (y : real) : term1358 x y.
Proof. exact (@lem1976259 term17 (term1281 x y)). Qed.
Lemma lem1976261 (x : real) (y : real) (h1 : term1319 x y) : term1359 x y.
Proof. exact (@lem1976260 x y (@lem1976257 x y h1)). Qed.
Lemma lem1976262 (x : real) (y : real) : (term1360 x y) = (term1361 x y).
Proof. exact (@lem1483508 (term886 x y) term17 (term40 x y)). Qed.
Lemma lem1976263 (x : real) (y : real) : (term1362 x y) = (term1363 x y).
Proof. exact (@lem1483508 x term17 (term52 y)). Qed.
Lemma lem1976264 (y : real) : (term950 y) = (term951 y).
Proof. exact (@lem1483476 term17 term16 y). Qed.
Lemma lem1976266 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976267 : term922 = term923.
Proof. exact (@lem1976266 term23 term22). Qed.
Lemma lem1976268 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1976269 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1976270 : term925 = term23.
Proof. exact (EQ_MP (@lem1976269) (@lem1976268)). Qed.
Lemma lem1976271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976272 : term926 = term17.
Proof. exact (MK_COMB (@lem1976271) (@lem1976270)). Qed.
Lemma lem1976273 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976274 : term923 = term28.
Proof. exact (MK_COMB (@lem1976273) (@lem1976272)). Qed.
Lemma lem1976275 : term922 = term28.
Proof. exact (TRANS (@lem1976267) (@lem1976274)). Qed.
Lemma lem1976276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976277 : term927 = term30.
Proof. exact (MK_COMB (@lem1976276) (@lem1976275)). Qed.
Lemma lem1976278 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976279 (y : real) : (term951 y) = (term276 y).
Proof. exact (MK_COMB (@lem1976277) (@lem1976278 y)). Qed.
Lemma lem1976280 (y : real) : (term950 y) = (term276 y).
Proof. exact (TRANS (@lem1976264 y) (@lem1976279 y)). Qed.
Lemma lem1976283 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1976284 (x : real) (y : real) : (term1363 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1976283 x) (@lem1976280 y)). Qed.
Lemma lem1976285 (x : real) (y : real) : (term1362 x y) = (term286 x y).
Proof. exact (TRANS (@lem1976263 x y) (@lem1976284 x y)). Qed.
Lemma lem1976286 (x : real) (y : real) : (term1364 x y) = (term1365 x y).
Proof. exact (@lem1483476 term17 term17 (term920 x y)). Qed.
Lemma lem1976288 (m : nat) (n : nat) : (term1366 m n) = (term66 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1976289 : term1367 = term1368.
Proof. exact (@lem1976288 term23 term23). Qed.
Lemma lem1976290 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976291 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976290) (@lem940073)). Qed.
Lemma lem1976292 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976293 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976292) (@lem1976291)). Qed.
Lemma lem1976294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976295 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976294) (@lem1976293)). Qed.
Lemma lem1976296 : term1367 = term1373.
Proof. exact (TRANS (@lem1976289) (@lem1976295)). Qed.
Lemma lem1976297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976298 : term1374 = term1375.
Proof. exact (MK_COMB (@lem1976297) (@lem1976296)). Qed.
Lemma lem1976299 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976300 (x : real) (y : real) : (term1365 x y) = (term1376 x y).
Proof. exact (MK_COMB (@lem1976298) (@lem1976299 x y)). Qed.
Lemma lem1976301 (x : real) (y : real) : (term1364 x y) = (term1376 x y).
Proof. exact (TRANS (@lem1976286 x y) (@lem1976300 x y)). Qed.
Lemma lem1976302 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976303 (x : real) (y : real) : (term1377 x y) = (term1378 x y).
Proof. exact (MK_COMB (@lem1976302) (@lem1976301 x y)). Qed.
Lemma lem1976304 (x : real) (y : real) : (term1361 x y) = (term1379 x y).
Proof. exact (MK_COMB (@lem1976303 x y) (@lem1976285 x y)). Qed.
Lemma lem1976305 (x : real) (y : real) : (term1360 x y) = (term1379 x y).
Proof. exact (TRANS (@lem1976262 x y) (@lem1976304 x y)). Qed.
Lemma lem1976306 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1976307 (x : real) (y : real) : (term1380 x y) = (term1381 x y).
Proof. exact (MK_COMB (@lem1976306) (@lem1976305 x y)). Qed.
Lemma lem1976308 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976309 (x : real) (y : real) : (term1359 x y) = (term1382 x y).
Proof. exact (MK_COMB (@lem1976307 x y) (@lem1976308)). Qed.
Lemma lem1976310 (x : real) (y : real) (h1 : term1319 x y) : term1382 x y.
Proof. exact (EQ_MP (@lem1976309 x y) (@lem1976261 x y h1)). Qed.
Lemma lem1976312 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976313 : term1354 = term1355.
Proof. exact (@lem1976312 (NUMERAL 0) term23). Qed.
Lemma lem1976314 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976315 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976316 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976315 h1) (fun h1 : term1355 = True => @lem1976314)). Qed.
Lemma lem1976317 : term1355 = True.
Proof. exact (EQ_MP (@lem1976316) (@lem1976314)). Qed.
Lemma lem1976318 : term1354 = True.
Proof. exact (TRANS (@lem1976313) (@lem1976317)). Qed.
Lemma lem1976319 : True = term1354.
Proof. exact (SYM (@lem1976318)). Qed.
Lemma lem1976320 : term1354.
Proof. exact (EQ_MP (@lem1976319) (@lem0)). Qed.
Lemma lem1976321 (x : real) (y : real) (h1 : term1319 x y) : term1383 x y.
Proof. exact (conj (@lem1976320) (@lem1976202 x y h1)). Qed.
Lemma lem1976323 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976324 (x : real) (y : real) : term1384 x y.
Proof. exact (@lem1976323 term17 (term1297 x y)). Qed.
Lemma lem1976325 (x : real) (y : real) (h1 : term1319 x y) : term1385 x y.
Proof. exact (@lem1976324 x y (@lem1976321 x y h1)). Qed.
Lemma lem1976326 (x : real) (y : real) : (term1386 x y) = (term1387 x y).
Proof. exact (@lem1483508 (term928 x y) term17 (term1296 x y)). Qed.
Lemma lem1976327 (x : real) (y : real) : (term1388 x y) = (term1389 x y).
Proof. exact (@lem1483508 (term1036 x) term17 (term1198 y)). Qed.
Lemma lem1976328 (y : real) : (term1390 y) = (term1391 y).
Proof. exact (@lem1483476 term17 term1195 y). Qed.
Lemma lem1976330 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976331 : term1392 = term1393.
Proof. exact (@lem1976330 term23 term1032). Qed.
Lemma lem1976332 : term1394 = term1030.
Proof. exact (@lem996238 term1030). Qed.
Lemma lem1976333 : (term1394 = term1030) = (term1395 = term1396).
Proof. exact (@lem996664 (BIT1 0) term1030 term1030). Qed.
Lemma lem1976334 : term1395 = term1396.
Proof. exact (EQ_MP (@lem1976333) (@lem1976332)). Qed.
Lemma lem1976335 : (term1395 = term1396) = (term1397 = term1398).
Proof. exact (@lem1007663 term25 term1030 term1396). Qed.
Lemma lem1976336 : term1397 = term1398.
Proof. exact (EQ_MP (@lem1976335) (@lem1976334)). Qed.
Lemma lem1976337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976338 : term1399 = term1400.
Proof. exact (MK_COMB (@lem1976337) (@lem1976336)). Qed.
Lemma lem1976339 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976340 : term1393 = term1401.
Proof. exact (MK_COMB (@lem1976339) (@lem1976338)). Qed.
Lemma lem1976341 : term1392 = term1401.
Proof. exact (TRANS (@lem1976331) (@lem1976340)). Qed.
Lemma lem1976342 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976343 : term1402 = term1403.
Proof. exact (MK_COMB (@lem1976342) (@lem1976341)). Qed.
Lemma lem1976344 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976345 (y : real) : (term1391 y) = (term1404 y).
Proof. exact (MK_COMB (@lem1976343) (@lem1976344 y)). Qed.
Lemma lem1976346 (y : real) : (term1390 y) = (term1404 y).
Proof. exact (TRANS (@lem1976328 y) (@lem1976345 y)). Qed.
Lemma lem1976347 (x : real) : (term1405 x) = (term1406 x).
Proof. exact (@lem1483476 term17 term1033 x). Qed.
Lemma lem1976349 (m : nat) (n : nat) : (term1366 m n) = (term66 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1976350 : term1407 = term1399.
Proof. exact (@lem1976349 term23 term1032). Qed.
Lemma lem1976351 : term1394 = term1030.
Proof. exact (@lem996238 term1030). Qed.
Lemma lem1976352 : (term1394 = term1030) = (term1395 = term1396).
Proof. exact (@lem996664 (BIT1 0) term1030 term1030). Qed.
Lemma lem1976353 : term1395 = term1396.
Proof. exact (EQ_MP (@lem1976352) (@lem1976351)). Qed.
Lemma lem1976354 : (term1395 = term1396) = (term1397 = term1398).
Proof. exact (@lem1007663 term25 term1030 term1396). Qed.
Lemma lem1976355 : term1397 = term1398.
Proof. exact (EQ_MP (@lem1976354) (@lem1976353)). Qed.
Lemma lem1976356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976357 : term1399 = term1400.
Proof. exact (MK_COMB (@lem1976356) (@lem1976355)). Qed.
Lemma lem1976358 : term1407 = term1400.
Proof. exact (TRANS (@lem1976350) (@lem1976357)). Qed.
Lemma lem1976359 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976360 : term1408 = term1409.
Proof. exact (MK_COMB (@lem1976359) (@lem1976358)). Qed.
Lemma lem1976361 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976362 (x : real) : (term1406 x) = (term1410 x).
Proof. exact (MK_COMB (@lem1976360) (@lem1976361 x)). Qed.
Lemma lem1976363 (x : real) : (term1405 x) = (term1410 x).
Proof. exact (TRANS (@lem1976347 x) (@lem1976362 x)). Qed.
Lemma lem1976364 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976365 (x : real) : (term1411 x) = (term1412 x).
Proof. exact (MK_COMB (@lem1976364) (@lem1976363 x)). Qed.
Lemma lem1976366 (x : real) (y : real) : (term1389 x y) = (term1413 x y).
Proof. exact (MK_COMB (@lem1976365 x) (@lem1976346 y)). Qed.
Lemma lem1976367 (x : real) (y : real) : (term1388 x y) = (term1413 x y).
Proof. exact (TRANS (@lem1976327 x y) (@lem1976366 x y)). Qed.
Lemma lem1976368 (x : real) (y : real) : (term1414 x y) = (term1415 x y).
Proof. exact (@lem1483476 term17 term28 (term920 x y)). Qed.
Lemma lem1976370 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976371 : term1416 = term1417.
Proof. exact (@lem1976370 term23 term23). Qed.
Lemma lem1976372 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976373 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976372) (@lem940073)). Qed.
Lemma lem1976374 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976375 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976374) (@lem1976373)). Qed.
Lemma lem1976376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976377 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976376) (@lem1976375)). Qed.
Lemma lem1976378 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976379 : term1417 = term1418.
Proof. exact (MK_COMB (@lem1976378) (@lem1976377)). Qed.
Lemma lem1976380 : term1416 = term1418.
Proof. exact (TRANS (@lem1976371) (@lem1976379)). Qed.
Lemma lem1976381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976382 : term1419 = term1420.
Proof. exact (MK_COMB (@lem1976381) (@lem1976380)). Qed.
Lemma lem1976383 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976384 (x : real) (y : real) : (term1415 x y) = (term1421 x y).
Proof. exact (MK_COMB (@lem1976382) (@lem1976383 x y)). Qed.
Lemma lem1976385 (x : real) (y : real) : (term1414 x y) = (term1421 x y).
Proof. exact (TRANS (@lem1976368 x y) (@lem1976384 x y)). Qed.
Lemma lem1976386 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976387 (x : real) (y : real) : (term1422 x y) = (term1423 x y).
Proof. exact (MK_COMB (@lem1976386) (@lem1976385 x y)). Qed.
Lemma lem1976388 (x : real) (y : real) : (term1387 x y) = (term1424 x y).
Proof. exact (MK_COMB (@lem1976387 x y) (@lem1976367 x y)). Qed.
Lemma lem1976389 (x : real) (y : real) : (term1386 x y) = (term1424 x y).
Proof. exact (TRANS (@lem1976326 x y) (@lem1976388 x y)). Qed.
Lemma lem1976390 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976391 (x : real) (y : real) : (term1425 x y) = (term1426 x y).
Proof. exact (MK_COMB (@lem1976390) (@lem1976389 x y)). Qed.
Lemma lem1976392 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976393 (x : real) (y : real) : (term1385 x y) = (term1427 x y).
Proof. exact (MK_COMB (@lem1976391 x y) (@lem1976392)). Qed.
Lemma lem1976394 (x : real) (y : real) (h1 : term1319 x y) : term1427 x y.
Proof. exact (EQ_MP (@lem1976393 x y) (@lem1976325 x y h1)). Qed.
Lemma lem1976395 (x : real) (y : real) (h1 : term1319 x y) : term1428 x y.
Proof. exact (conj (@lem1976394 x y h1) (@lem1976310 x y h1)). Qed.
Lemma lem1976397 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976398 (x : real) (y : real) : term1429 x y.
Proof. exact (@lem1976397 (term1424 x y) (term1379 x y)). Qed.
Lemma lem1976399 (x : real) (y : real) (h1 : term1319 x y) : term1430 x y.
Proof. exact (@lem1976398 x y (@lem1976395 x y h1)). Qed.
Lemma lem1976400 (x : real) (y : real) : (term1431 x y) = (term1432 x y).
Proof. exact (@lem1483480 (term1421 x y) (term1376 x y) (term1413 x y) (term286 x y)). Qed.
Lemma lem1976401 (x : real) (y : real) : (term1433 x y) = (term1434 x y).
Proof. exact (@lem1483438 term1418 term1373 (term920 x y)). Qed.
Lemma lem1976403 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976404 : term1435 = term121.
Proof. exact (@lem1976403 term1372). Qed.
Lemma lem1976405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976406 : term1436 = term124.
Proof. exact (MK_COMB (@lem1976405) (@lem1976404)). Qed.
Lemma lem1976407 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976408 (x : real) (y : real) : (term1434 x y) = (term1437 x y).
Proof. exact (MK_COMB (@lem1976406) (@lem1976407 x y)). Qed.
Lemma lem1976409 (x : real) (y : real) : (term1433 x y) = (term1437 x y).
Proof. exact (TRANS (@lem1976401 x y) (@lem1976408 x y)). Qed.
Lemma lem1976410 (x : real) (y : real) : (term1437 x y) = term121.
Proof. exact (@lem1483446 (term920 x y)). Qed.
Lemma lem1976411 (x : real) (y : real) : (term1433 x y) = term121.
Proof. exact (TRANS (@lem1976409 x y) (@lem1976410 x y)). Qed.
Lemma lem1976412 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976413 (x : real) (y : real) : (term1438 x y) = term127.
Proof. exact (MK_COMB (@lem1976412) (@lem1976411 x y)). Qed.
Lemma lem1976414 (x : real) (y : real) : (term1439 x y) = (term1440 x y).
Proof. exact (@lem1483480 (term1410 x) (term283 x) (term1404 y) (term276 y)). Qed.
Lemma lem1976415 (x : real) : (term1441 x) = (term1442 x).
Proof. exact (@lem1483438 term1400 term17 x). Qed.
Lemma lem1976416 : term1443 = term1444.
Proof. exact (@lem1367770 term1398 term23). Qed.
Lemma lem1976417 : term1445 = term1328.
Proof. exact (@lem707207). Qed.
Lemma lem1976418 : (term1445 = term1328) = (term1446 = term1326).
Proof. exact (@lem1006570 term1396 term25 term1328). Qed.
Lemma lem1976419 : term1446 = term1326.
Proof. exact (EQ_MP (@lem1976418) (@lem1976417)). Qed.
Lemma lem1976420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976421 : term1444 = term1332.
Proof. exact (MK_COMB (@lem1976420) (@lem1976419)). Qed.
Lemma lem1976422 : term1443 = term1332.
Proof. exact (TRANS (@lem1976416) (@lem1976421)). Qed.
Lemma lem1976423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976424 : term1447 = term1448.
Proof. exact (MK_COMB (@lem1976423) (@lem1976422)). Qed.
Lemma lem1976425 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976426 (x : real) : (term1442 x) = (term1336 x).
Proof. exact (MK_COMB (@lem1976424) (@lem1976425 x)). Qed.
Lemma lem1976427 (x : real) : (term1441 x) = (term1336 x).
Proof. exact (TRANS (@lem1976415 x) (@lem1976426 x)). Qed.
Lemma lem1976428 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976429 (x : real) : (term1449 x) = (term1450 x).
Proof. exact (MK_COMB (@lem1976428) (@lem1976427 x)). Qed.
Lemma lem1976430 (y : real) : (term1451 y) = (term1452 y).
Proof. exact (@lem1483438 term1401 term28 y). Qed.
Lemma lem1976431 : term1453 = term1454.
Proof. exact (@lem1367763 term1398 term23). Qed.
Lemma lem1976432 : term1445 = term1328.
Proof. exact (@lem707207). Qed.
Lemma lem1976433 : (term1445 = term1328) = (term1446 = term1326).
Proof. exact (@lem1006570 term1396 term25 term1328). Qed.
Lemma lem1976434 : term1446 = term1326.
Proof. exact (EQ_MP (@lem1976433) (@lem1976432)). Qed.
Lemma lem1976435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976436 : term1444 = term1332.
Proof. exact (MK_COMB (@lem1976435) (@lem1976434)). Qed.
Lemma lem1976437 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976438 : term1454 = term1344.
Proof. exact (MK_COMB (@lem1976437) (@lem1976436)). Qed.
Lemma lem1976439 : term1453 = term1344.
Proof. exact (TRANS (@lem1976431) (@lem1976438)). Qed.
Lemma lem1976440 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976441 : term1455 = term1346.
Proof. exact (MK_COMB (@lem1976440) (@lem1976439)). Qed.
Lemma lem1976442 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976443 (y : real) : (term1452 y) = (term1347 y).
Proof. exact (MK_COMB (@lem1976441) (@lem1976442 y)). Qed.
Lemma lem1976444 (y : real) : (term1451 y) = (term1347 y).
Proof. exact (TRANS (@lem1976430 y) (@lem1976443 y)). Qed.
Lemma lem1976445 (x : real) (y : real) : (term1440 x y) = (term1456 x y).
Proof. exact (MK_COMB (@lem1976429 x) (@lem1976444 y)). Qed.
Lemma lem1976446 (x : real) (y : real) : (term1439 x y) = (term1456 x y).
Proof. exact (TRANS (@lem1976414 x y) (@lem1976445 x y)). Qed.
Lemma lem1976447 (x : real) (y : real) : (term1432 x y) = (term1457 x y).
Proof. exact (MK_COMB (@lem1976413 x y) (@lem1976446 x y)). Qed.
Lemma lem1976448 (x : real) (y : real) : (term1431 x y) = (term1457 x y).
Proof. exact (TRANS (@lem1976400 x y) (@lem1976447 x y)). Qed.
Lemma lem1976449 (x : real) (y : real) : (term1457 x y) = (term1456 x y).
Proof. exact (@lem1483448 (term1456 x y)). Qed.
Lemma lem1976450 (x : real) (y : real) : (term1431 x y) = (term1456 x y).
Proof. exact (TRANS (@lem1976448 x y) (@lem1976449 x y)). Qed.
Lemma lem1976451 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976452 (x : real) (y : real) : (term1458 x y) = (term1459 x y).
Proof. exact (MK_COMB (@lem1976451) (@lem1976450 x y)). Qed.
Lemma lem1976453 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976454 (x : real) (y : real) : (term1430 x y) = (term1460 x y).
Proof. exact (MK_COMB (@lem1976452 x y) (@lem1976453)). Qed.
Lemma lem1976455 (x : real) (y : real) (h1 : term1319 x y) : term1460 x y.
Proof. exact (EQ_MP (@lem1976454 x y) (@lem1976399 x y h1)). Qed.
Lemma lem1976457 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976458 : term368 = term369.
Proof. exact (@lem1976457 (NUMERAL 0) term22). Qed.
Lemma lem1976459 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1976460 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1976461 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1976460 h1) (fun h1 : term369 = True => @lem1976459)). Qed.
Lemma lem1976462 : term369 = True.
Proof. exact (EQ_MP (@lem1976461) (@lem1976459)). Qed.
Lemma lem1976463 : term368 = True.
Proof. exact (TRANS (@lem1976458) (@lem1976462)). Qed.
Lemma lem1976464 : True = term368.
Proof. exact (SYM (@lem1976463)). Qed.
Lemma lem1976465 : term368.
Proof. exact (EQ_MP (@lem1976464) (@lem0)). Qed.
Lemma lem1976466 (x : real) (y : real) (h1 : term1319 x y) : term1461 x y.
Proof. exact (conj (@lem1976465) (@lem1976455 x y h1)). Qed.
Lemma lem1976468 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976469 (x : real) (y : real) : term1462 x y.
Proof. exact (@lem1976468 term71 (term1456 x y)). Qed.
Lemma lem1976470 (x : real) (y : real) (h1 : term1319 x y) : term1463 x y.
Proof. exact (@lem1976469 x y (@lem1976466 x y h1)). Qed.
Lemma lem1976471 (x : real) (y : real) : (term1464 x y) = (term1456 x y).
Proof. exact (@lem1483460 (term1456 x y)). Qed.
Lemma lem1976472 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976473 (x : real) (y : real) : (term1465 x y) = (term1459 x y).
Proof. exact (MK_COMB (@lem1976472) (@lem1976471 x y)). Qed.
Lemma lem1976474 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976475 (x : real) (y : real) : (term1463 x y) = (term1460 x y).
Proof. exact (MK_COMB (@lem1976473 x y) (@lem1976474)). Qed.
Lemma lem1976476 (x : real) (y : real) (h1 : term1319 x y) : term1460 x y.
Proof. exact (EQ_MP (@lem1976475 x y) (@lem1976470 x y h1)). Qed.
Lemma lem1976477 (x : real) (y : real) (h1 : term1319 x y) : term1466 x y.
Proof. exact (conj (@lem1976476 x y h1) (@lem1976246 x y h1)). Qed.
Lemma lem1976479 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976480 (x : real) (y : real) : term1467 x y.
Proof. exact (@lem1976479 (term1456 x y) (term1350 x y)). Qed.
Lemma lem1976481 (x : real) (y : real) (h1 : term1319 x y) : term1468 x y.
Proof. exact (@lem1976480 x y (@lem1976477 x y h1)). Qed.
Lemma lem1976482 (x : real) (y : real) : (term1469 x y) = (term1470 x y).
Proof. exact (@lem1483480 (term1336 x) (term1347 x) (term1347 y) (term1336 y)). Qed.
Lemma lem1976483 (x : real) : (term1471 x) = (term1472 x).
Proof. exact (@lem1483438 term1332 term1344 x). Qed.
Lemma lem1976485 (m : nat) : (term1473 m) = term121.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1976486 : term1474 = term121.
Proof. exact (@lem1976485 term1326). Qed.
Lemma lem1976487 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976488 : term1475 = term124.
Proof. exact (MK_COMB (@lem1976487) (@lem1976486)). Qed.
Lemma lem1976489 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976490 (x : real) : (term1472 x) = (term322 x).
Proof. exact (MK_COMB (@lem1976488) (@lem1976489 x)). Qed.
Lemma lem1976491 (x : real) : (term1471 x) = (term322 x).
Proof. exact (TRANS (@lem1976483 x) (@lem1976490 x)). Qed.
Lemma lem1976492 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1976493 (x : real) : (term1471 x) = term121.
Proof. exact (TRANS (@lem1976491 x) (@lem1976492 x)). Qed.
Lemma lem1976494 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976495 (x : real) : (term1476 x) = term127.
Proof. exact (MK_COMB (@lem1976494) (@lem1976493 x)). Qed.
Lemma lem1976496 (y : real) : (term1477 y) = (term1478 y).
Proof. exact (@lem1483438 term1344 term1332 y). Qed.
Lemma lem1976498 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976499 : term1479 = term121.
Proof. exact (@lem1976498 term1326). Qed.
Lemma lem1976500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976501 : term1480 = term124.
Proof. exact (MK_COMB (@lem1976500) (@lem1976499)). Qed.
Lemma lem1976502 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976503 (y : real) : (term1478 y) = (term322 y).
Proof. exact (MK_COMB (@lem1976501) (@lem1976502 y)). Qed.
Lemma lem1976504 (y : real) : (term1477 y) = (term322 y).
Proof. exact (TRANS (@lem1976496 y) (@lem1976503 y)). Qed.
Lemma lem1976505 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1976506 (y : real) : (term1477 y) = term121.
Proof. exact (TRANS (@lem1976504 y) (@lem1976505 y)). Qed.
Lemma lem1976507 (x : real) (y : real) : (term1470 x y) = term136.
Proof. exact (MK_COMB (@lem1976495 x) (@lem1976506 y)). Qed.
Lemma lem1976508 (x : real) (y : real) : (term1469 x y) = term136.
Proof. exact (TRANS (@lem1976482 x y) (@lem1976507 x y)). Qed.
Lemma lem1976509 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1976510 (x : real) (y : real) : (term1469 x y) = term121.
Proof. exact (TRANS (@lem1976508 x y) (@lem1976509)). Qed.
Lemma lem1976511 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976512 (x : real) (y : real) : (term1481 x y) = term143.
Proof. exact (MK_COMB (@lem1976511) (@lem1976510 x y)). Qed.
Lemma lem1976513 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976514 (x : real) (y : real) : (term1468 x y) = term145.
Proof. exact (MK_COMB (@lem1976512 x y) (@lem1976513)). Qed.
Lemma lem1976515 (x : real) (y : real) (h1 : term1319 x y) : term145.
Proof. exact (EQ_MP (@lem1976514 x y) (@lem1976481 x y h1)). Qed.
Lemma lem1976517 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976518 : term145 = term152.
Proof. exact (@lem1976517 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1976519 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1976520 : term145 = False.
Proof. exact (TRANS (@lem1976518) (@lem1976519)). Qed.
Lemma lem1976521 (x : real) (y : real) (h1 : term1319 x y) : False.
Proof. exact (EQ_MP (@lem1976520) (@lem1976515 x y h1)). Qed.
Lemma lem1976522 (x : real) (y : real) (h1 : term1321 x y) : False.
Proof. exact (or_elim (@lem1976108 x y h1) (fun h0 : term1276 x y => @lem1976190 x y h0) (fun h0 : term1319 x y => @lem1976521 x y h0)). Qed.
Lemma lem1976523 (x : real) (y : real) (h1 : term1225 x y) : term1225 x y.
Proof. exact (h1). Qed.
Lemma lem1976524 (x : real) (y : real) (h1 : term1170 x y) : term1170 x y.
Proof. exact (h1). Qed.
Lemma lem1976525 (x : real) (y : real) (h1 : term1170 x y) : term1169 x y.
Proof. exact (proj2 (@lem1976524 x y h1)). Qed.
Lemma lem1976527 (x : real) (y : real) (h1 : term1170 x y) : term1168 x y.
Proof. exact (proj2 (@lem1976525 x y h1)). Qed.
Lemma lem1976529 (x : real) (y : real) (h1 : term1170 x y) : term1166 x y.
Proof. exact (proj2 (@lem1976527 x y h1)). Qed.
Lemma lem1976531 (x : real) (y : real) (h1 : term1170 x y) : term1164 x y.
Proof. exact (proj2 (@lem1976529 x y h1)). Qed.
Lemma lem1976533 (x : real) (y : real) (h1 : term1170 x y) : term1162 x y.
Proof. exact (proj2 (@lem1976531 x y h1)). Qed.
Lemma lem1976535 (x : real) (y : real) (h1 : term1170 x y) : term1159 x y.
Proof. exact (proj2 (@lem1976533 x y h1)). Qed.
Lemma lem1976536 (x : real) (y : real) (h1 : term1170 x y) : term1134 x y.
Proof. exact (proj1 (@lem1976533 x y h1)). Qed.
Lemma lem1976538 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976539 : term1354 = term1355.
Proof. exact (@lem1976538 (NUMERAL 0) term23). Qed.
Lemma lem1976540 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976541 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976542 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976541 h1) (fun h1 : term1355 = True => @lem1976540)). Qed.
Lemma lem1976543 : term1355 = True.
Proof. exact (EQ_MP (@lem1976542) (@lem1976540)). Qed.
Lemma lem1976544 : term1354 = True.
Proof. exact (TRANS (@lem1976539) (@lem1976543)). Qed.
Lemma lem1976545 : True = term1354.
Proof. exact (SYM (@lem1976544)). Qed.
Lemma lem1976546 : term1354.
Proof. exact (EQ_MP (@lem1976545) (@lem0)). Qed.
Lemma lem1976547 (x : real) (y : real) (h1 : term1170 x y) : term1482 x y.
Proof. exact (conj (@lem1976546) (@lem1976536 x y h1)). Qed.
Lemma lem1976549 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976550 (x : real) (y : real) : term1483 x y.
Proof. exact (@lem1976549 term17 (term1136 x y)). Qed.
Lemma lem1976551 (x : real) (y : real) (h1 : term1170 x y) : term1484 x y.
Proof. exact (@lem1976550 x y (@lem1976547 x y h1)). Qed.
Lemma lem1976552 (x : real) (y : real) : (term1485 x y) = (term1486 x y).
Proof. exact (@lem1483508 (term886 x y) term17 (term190 x y)). Qed.
Lemma lem1976553 (x : real) (y : real) : (term948 x y) = (term949 x y).
Proof. exact (@lem1483508 (term52 x) term17 y). Qed.
Lemma lem1976554 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1976555 (x : real) : (term950 x) = (term951 x).
Proof. exact (@lem1483476 term17 term16 x). Qed.
Lemma lem1976557 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976558 : term922 = term923.
Proof. exact (@lem1976557 term23 term22). Qed.
Lemma lem1976559 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1976560 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1976561 : term925 = term23.
Proof. exact (EQ_MP (@lem1976560) (@lem1976559)). Qed.
Lemma lem1976562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976563 : term926 = term17.
Proof. exact (MK_COMB (@lem1976562) (@lem1976561)). Qed.
Lemma lem1976564 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976565 : term923 = term28.
Proof. exact (MK_COMB (@lem1976564) (@lem1976563)). Qed.
Lemma lem1976566 : term922 = term28.
Proof. exact (TRANS (@lem1976558) (@lem1976565)). Qed.
Lemma lem1976567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976568 : term927 = term30.
Proof. exact (MK_COMB (@lem1976567) (@lem1976566)). Qed.
Lemma lem1976569 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976570 (x : real) : (term951 x) = (term276 x).
Proof. exact (MK_COMB (@lem1976568) (@lem1976569 x)). Qed.
Lemma lem1976571 (x : real) : (term950 x) = (term276 x).
Proof. exact (TRANS (@lem1976555 x) (@lem1976570 x)). Qed.
Lemma lem1976572 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976573 (x : real) : (term952 x) = (term354 x).
Proof. exact (MK_COMB (@lem1976572) (@lem1976571 x)). Qed.
Lemma lem1976574 (x : real) (y : real) : (term949 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1976573 x) (@lem1976554 y)). Qed.
Lemma lem1976575 (x : real) (y : real) : (term948 x y) = (term355 x y).
Proof. exact (TRANS (@lem1976553 x y) (@lem1976574 x y)). Qed.
Lemma lem1976576 (x : real) (y : real) : (term1364 x y) = (term1365 x y).
Proof. exact (@lem1483476 term17 term17 (term920 x y)). Qed.
Lemma lem1976578 (m : nat) (n : nat) : (term1366 m n) = (term66 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1976579 : term1367 = term1368.
Proof. exact (@lem1976578 term23 term23). Qed.
Lemma lem1976580 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976581 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976580) (@lem940073)). Qed.
Lemma lem1976582 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976583 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976582) (@lem1976581)). Qed.
Lemma lem1976584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976585 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976584) (@lem1976583)). Qed.
Lemma lem1976586 : term1367 = term1373.
Proof. exact (TRANS (@lem1976579) (@lem1976585)). Qed.
Lemma lem1976587 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976588 : term1374 = term1375.
Proof. exact (MK_COMB (@lem1976587) (@lem1976586)). Qed.
Lemma lem1976589 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976590 (x : real) (y : real) : (term1365 x y) = (term1376 x y).
Proof. exact (MK_COMB (@lem1976588) (@lem1976589 x y)). Qed.
Lemma lem1976591 (x : real) (y : real) : (term1364 x y) = (term1376 x y).
Proof. exact (TRANS (@lem1976576 x y) (@lem1976590 x y)). Qed.
Lemma lem1976592 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976593 (x : real) (y : real) : (term1377 x y) = (term1378 x y).
Proof. exact (MK_COMB (@lem1976592) (@lem1976591 x y)). Qed.
Lemma lem1976594 (x : real) (y : real) : (term1486 x y) = (term1487 x y).
Proof. exact (MK_COMB (@lem1976593 x y) (@lem1976575 x y)). Qed.
Lemma lem1976595 (x : real) (y : real) : (term1485 x y) = (term1487 x y).
Proof. exact (TRANS (@lem1976552 x y) (@lem1976594 x y)). Qed.
Lemma lem1976596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1976597 (x : real) (y : real) : (term1488 x y) = (term1489 x y).
Proof. exact (MK_COMB (@lem1976596) (@lem1976595 x y)). Qed.
Lemma lem1976598 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976599 (x : real) (y : real) : (term1484 x y) = (term1490 x y).
Proof. exact (MK_COMB (@lem1976597 x y) (@lem1976598)). Qed.
Lemma lem1976600 (x : real) (y : real) (h1 : term1170 x y) : term1490 x y.
Proof. exact (EQ_MP (@lem1976599 x y) (@lem1976551 x y h1)). Qed.
Lemma lem1976602 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976603 : term1354 = term1355.
Proof. exact (@lem1976602 (NUMERAL 0) term23). Qed.
Lemma lem1976604 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976605 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976606 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976605 h1) (fun h1 : term1355 = True => @lem1976604)). Qed.
Lemma lem1976607 : term1355 = True.
Proof. exact (EQ_MP (@lem1976606) (@lem1976604)). Qed.
Lemma lem1976608 : term1354 = True.
Proof. exact (TRANS (@lem1976603) (@lem1976607)). Qed.
Lemma lem1976609 : True = term1354.
Proof. exact (SYM (@lem1976608)). Qed.
Lemma lem1976610 : term1354.
Proof. exact (EQ_MP (@lem1976609) (@lem0)). Qed.
Lemma lem1976611 (x : real) (y : real) (h1 : term1170 x y) : term1491 x y.
Proof. exact (conj (@lem1976610) (@lem1976535 x y h1)). Qed.
Lemma lem1976613 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976614 (x : real) (y : real) : term1492 x y.
Proof. exact (@lem1976613 term17 (term1149 x y)). Qed.
Lemma lem1976615 (x : real) (y : real) (h1 : term1170 x y) : term1493 x y.
Proof. exact (@lem1976614 x y (@lem1976611 x y h1)). Qed.
Lemma lem1976616 (x : real) (y : real) : (term1494 x y) = (term1495 x y).
Proof. exact (@lem1483508 (term928 x y) term17 (term40 x y)). Qed.
Lemma lem1976617 (x : real) (y : real) : (term1362 x y) = (term1363 x y).
Proof. exact (@lem1483508 x term17 (term52 y)). Qed.
Lemma lem1976618 (y : real) : (term950 y) = (term951 y).
Proof. exact (@lem1483476 term17 term16 y). Qed.
Lemma lem1976620 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976621 : term922 = term923.
Proof. exact (@lem1976620 term23 term22). Qed.
Lemma lem1976622 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1976623 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1976624 : term925 = term23.
Proof. exact (EQ_MP (@lem1976623) (@lem1976622)). Qed.
Lemma lem1976625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976626 : term926 = term17.
Proof. exact (MK_COMB (@lem1976625) (@lem1976624)). Qed.
Lemma lem1976627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976628 : term923 = term28.
Proof. exact (MK_COMB (@lem1976627) (@lem1976626)). Qed.
Lemma lem1976629 : term922 = term28.
Proof. exact (TRANS (@lem1976621) (@lem1976628)). Qed.
Lemma lem1976630 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976631 : term927 = term30.
Proof. exact (MK_COMB (@lem1976630) (@lem1976629)). Qed.
Lemma lem1976632 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976633 (y : real) : (term951 y) = (term276 y).
Proof. exact (MK_COMB (@lem1976631) (@lem1976632 y)). Qed.
Lemma lem1976634 (y : real) : (term950 y) = (term276 y).
Proof. exact (TRANS (@lem1976618 y) (@lem1976633 y)). Qed.
Lemma lem1976637 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1976638 (x : real) (y : real) : (term1363 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1976637 x) (@lem1976634 y)). Qed.
Lemma lem1976639 (x : real) (y : real) : (term1362 x y) = (term286 x y).
Proof. exact (TRANS (@lem1976617 x y) (@lem1976638 x y)). Qed.
Lemma lem1976640 (x : real) (y : real) : (term1414 x y) = (term1415 x y).
Proof. exact (@lem1483476 term17 term28 (term920 x y)). Qed.
Lemma lem1976642 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976643 : term1416 = term1417.
Proof. exact (@lem1976642 term23 term23). Qed.
Lemma lem1976644 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976645 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976644) (@lem940073)). Qed.
Lemma lem1976646 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976647 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976646) (@lem1976645)). Qed.
Lemma lem1976648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976649 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976648) (@lem1976647)). Qed.
Lemma lem1976650 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976651 : term1417 = term1418.
Proof. exact (MK_COMB (@lem1976650) (@lem1976649)). Qed.
Lemma lem1976652 : term1416 = term1418.
Proof. exact (TRANS (@lem1976643) (@lem1976651)). Qed.
Lemma lem1976653 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976654 : term1419 = term1420.
Proof. exact (MK_COMB (@lem1976653) (@lem1976652)). Qed.
Lemma lem1976655 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976656 (x : real) (y : real) : (term1415 x y) = (term1421 x y).
Proof. exact (MK_COMB (@lem1976654) (@lem1976655 x y)). Qed.
Lemma lem1976657 (x : real) (y : real) : (term1414 x y) = (term1421 x y).
Proof. exact (TRANS (@lem1976640 x y) (@lem1976656 x y)). Qed.
Lemma lem1976658 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976659 (x : real) (y : real) : (term1422 x y) = (term1423 x y).
Proof. exact (MK_COMB (@lem1976658) (@lem1976657 x y)). Qed.
Lemma lem1976660 (x : real) (y : real) : (term1495 x y) = (term1496 x y).
Proof. exact (MK_COMB (@lem1976659 x y) (@lem1976639 x y)). Qed.
Lemma lem1976661 (x : real) (y : real) : (term1494 x y) = (term1496 x y).
Proof. exact (TRANS (@lem1976616 x y) (@lem1976660 x y)). Qed.
Lemma lem1976662 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976663 (x : real) (y : real) : (term1497 x y) = (term1498 x y).
Proof. exact (MK_COMB (@lem1976662) (@lem1976661 x y)). Qed.
Lemma lem1976664 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976665 (x : real) (y : real) : (term1493 x y) = (term1499 x y).
Proof. exact (MK_COMB (@lem1976663 x y) (@lem1976664)). Qed.
Lemma lem1976666 (x : real) (y : real) (h1 : term1170 x y) : term1499 x y.
Proof. exact (EQ_MP (@lem1976665 x y) (@lem1976615 x y h1)). Qed.
Lemma lem1976667 (x : real) (y : real) (h1 : term1170 x y) : term1500 x y.
Proof. exact (conj (@lem1976666 x y h1) (@lem1976600 x y h1)). Qed.
Lemma lem1976669 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976670 (x : real) (y : real) : term1501 x y.
Proof. exact (@lem1976669 (term1496 x y) (term1487 x y)). Qed.
Lemma lem1976671 (x : real) (y : real) (h1 : term1170 x y) : term1502 x y.
Proof. exact (@lem1976670 x y (@lem1976667 x y h1)). Qed.
Lemma lem1976672 (x : real) (y : real) : (term1503 x y) = (term1504 x y).
Proof. exact (@lem1483480 (term1421 x y) (term1376 x y) (term286 x y) (term355 x y)). Qed.
Lemma lem1976673 (x : real) (y : real) : (term1433 x y) = (term1434 x y).
Proof. exact (@lem1483438 term1418 term1373 (term920 x y)). Qed.
Lemma lem1976675 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976676 : term1435 = term121.
Proof. exact (@lem1976675 term1372). Qed.
Lemma lem1976677 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976678 : term1436 = term124.
Proof. exact (MK_COMB (@lem1976677) (@lem1976676)). Qed.
Lemma lem1976679 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976680 (x : real) (y : real) : (term1434 x y) = (term1437 x y).
Proof. exact (MK_COMB (@lem1976678) (@lem1976679 x y)). Qed.
Lemma lem1976681 (x : real) (y : real) : (term1433 x y) = (term1437 x y).
Proof. exact (TRANS (@lem1976673 x y) (@lem1976680 x y)). Qed.
Lemma lem1976682 (x : real) (y : real) : (term1437 x y) = term121.
Proof. exact (@lem1483446 (term920 x y)). Qed.
Lemma lem1976683 (x : real) (y : real) : (term1433 x y) = term121.
Proof. exact (TRANS (@lem1976681 x y) (@lem1976682 x y)). Qed.
Lemma lem1976684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976685 (x : real) (y : real) : (term1438 x y) = term127.
Proof. exact (MK_COMB (@lem1976684) (@lem1976683 x y)). Qed.
Lemma lem1976686 (x : real) (y : real) : (term1505 x y) = (term1506 x y).
Proof. exact (@lem1483480 (term283 x) (term276 x) (term276 y) (term283 y)). Qed.
Lemma lem1976687 (x : real) : (term1507 x) = (term1508 x).
Proof. exact (@lem1483438 term17 term28 x). Qed.
Lemma lem1976689 (m : nat) : (term1473 m) = term121.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1976690 : term1509 = term121.
Proof. exact (@lem1976689 term23). Qed.
Lemma lem1976691 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976692 : term1510 = term124.
Proof. exact (MK_COMB (@lem1976691) (@lem1976690)). Qed.
Lemma lem1976693 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976694 (x : real) : (term1508 x) = (term322 x).
Proof. exact (MK_COMB (@lem1976692) (@lem1976693 x)). Qed.
Lemma lem1976695 (x : real) : (term1507 x) = (term322 x).
Proof. exact (TRANS (@lem1976687 x) (@lem1976694 x)). Qed.
Lemma lem1976696 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1976697 (x : real) : (term1507 x) = term121.
Proof. exact (TRANS (@lem1976695 x) (@lem1976696 x)). Qed.
Lemma lem1976698 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976699 (x : real) : (term1511 x) = term127.
Proof. exact (MK_COMB (@lem1976698) (@lem1976697 x)). Qed.
Lemma lem1976700 (y : real) : (term1512 y) = (term1513 y).
Proof. exact (@lem1483438 term28 term17 y). Qed.
Lemma lem1976702 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976703 : term132 = term121.
Proof. exact (@lem1976702 term23). Qed.
Lemma lem1976704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976705 : term133 = term124.
Proof. exact (MK_COMB (@lem1976704) (@lem1976703)). Qed.
Lemma lem1976706 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976707 (y : real) : (term1513 y) = (term322 y).
Proof. exact (MK_COMB (@lem1976705) (@lem1976706 y)). Qed.
Lemma lem1976708 (y : real) : (term1512 y) = (term322 y).
Proof. exact (TRANS (@lem1976700 y) (@lem1976707 y)). Qed.
Lemma lem1976709 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1976710 (y : real) : (term1512 y) = term121.
Proof. exact (TRANS (@lem1976708 y) (@lem1976709 y)). Qed.
Lemma lem1976711 (x : real) (y : real) : (term1506 x y) = term136.
Proof. exact (MK_COMB (@lem1976699 x) (@lem1976710 y)). Qed.
Lemma lem1976712 (x : real) (y : real) : (term1505 x y) = term136.
Proof. exact (TRANS (@lem1976686 x y) (@lem1976711 x y)). Qed.
Lemma lem1976713 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1976714 (x : real) (y : real) : (term1505 x y) = term121.
Proof. exact (TRANS (@lem1976712 x y) (@lem1976713)). Qed.
Lemma lem1976715 (x : real) (y : real) : (term1504 x y) = term136.
Proof. exact (MK_COMB (@lem1976685 x y) (@lem1976714 x y)). Qed.
Lemma lem1976716 (x : real) (y : real) : (term1503 x y) = term136.
Proof. exact (TRANS (@lem1976672 x y) (@lem1976715 x y)). Qed.
Lemma lem1976717 : term136 = term121.
Proof. exact (@lem1483448 term121). Qed.
Lemma lem1976718 (x : real) (y : real) : (term1503 x y) = term121.
Proof. exact (TRANS (@lem1976716 x y) (@lem1976717)). Qed.
Lemma lem1976719 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976720 (x : real) (y : real) : (term1514 x y) = term143.
Proof. exact (MK_COMB (@lem1976719) (@lem1976718 x y)). Qed.
Lemma lem1976721 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976722 (x : real) (y : real) : (term1502 x y) = term145.
Proof. exact (MK_COMB (@lem1976720 x y) (@lem1976721)). Qed.
Lemma lem1976723 (x : real) (y : real) (h1 : term1170 x y) : term145.
Proof. exact (EQ_MP (@lem1976722 x y) (@lem1976671 x y h1)). Qed.
Lemma lem1976725 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976726 : term145 = term152.
Proof. exact (@lem1976725 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1976727 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1976728 : term145 = False.
Proof. exact (TRANS (@lem1976726) (@lem1976727)). Qed.
Lemma lem1976729 (x : real) (y : real) (h1 : term1170 x y) : False.
Proof. exact (EQ_MP (@lem1976728) (@lem1976723 x y h1)). Qed.
Lemma lem1976730 (x : real) (y : real) (h1 : term1223 x y) : term1223 x y.
Proof. exact (h1). Qed.
Lemma lem1976731 (x : real) (y : real) (h1 : term1223 x y) : term1222 x y.
Proof. exact (proj2 (@lem1976730 x y h1)). Qed.
Lemma lem1976733 (x : real) (y : real) (h1 : term1223 x y) : term1221 x y.
Proof. exact (proj2 (@lem1976731 x y h1)). Qed.
Lemma lem1976735 (x : real) (y : real) (h1 : term1223 x y) : term1219 x y.
Proof. exact (proj2 (@lem1976733 x y h1)). Qed.
Lemma lem1976737 (x : real) (y : real) (h1 : term1223 x y) : term1217 x y.
Proof. exact (proj2 (@lem1976735 x y h1)). Qed.
Lemma lem1976739 (x : real) (y : real) (h1 : term1223 x y) : term1215 x y.
Proof. exact (proj2 (@lem1976737 x y h1)). Qed.
Lemma lem1976740 (x : real) (y : real) (h1 : term1223 x y) : term184 y.
Proof. exact (proj1 (@lem1976737 x y h1)). Qed.
Lemma lem1976741 (x : real) (y : real) (h1 : term1223 x y) : term1211 x y.
Proof. exact (proj2 (@lem1976739 x y h1)). Qed.
Lemma lem1976742 (x : real) (y : real) (h1 : term1223 x y) : term1186 x y.
Proof. exact (proj1 (@lem1976739 x y h1)). Qed.
Lemma lem1976744 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976745 : term1324 = term1325.
Proof. exact (@lem1976744 (NUMERAL 0) term1326). Qed.
Lemma lem1976746 : term1327 = term1328.
Proof. exact (@lem913187). Qed.
Lemma lem1976747 (h1 : term1327 = term1328) : term1325 = True.
Proof. exact (@lem1009824 term1329 0 term1328 h1). Qed.
Lemma lem1976748 : (term1327 = term1328) = (term1325 = True).
Proof. exact (prop_ext (fun h1 : term1327 = term1328 => @lem1976747 h1) (fun h1 : term1325 = True => @lem1976746)). Qed.
Lemma lem1976749 : term1325 = True.
Proof. exact (EQ_MP (@lem1976748) (@lem1976746)). Qed.
Lemma lem1976750 : term1324 = True.
Proof. exact (TRANS (@lem1976745) (@lem1976749)). Qed.
Lemma lem1976751 : True = term1324.
Proof. exact (SYM (@lem1976750)). Qed.
Lemma lem1976752 : term1324.
Proof. exact (EQ_MP (@lem1976751) (@lem0)). Qed.
Lemma lem1976753 (x : real) (y : real) (h1 : term1223 x y) : term1515 y.
Proof. exact (conj (@lem1976752) (@lem1976740 x y h1)). Qed.
Lemma lem1976755 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976756 (y : real) : term1516 y.
Proof. exact (@lem1976755 term1332 y). Qed.
Lemma lem1976763 (x : real) (y : real) (h1 : term1223 x y) : term1517 y.
Proof. exact (@lem1976756 y (@lem1976753 x y h1)). Qed.
Lemma lem1976765 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976766 : term1354 = term1355.
Proof. exact (@lem1976765 (NUMERAL 0) term23). Qed.
Lemma lem1976767 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976768 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976769 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976768 h1) (fun h1 : term1355 = True => @lem1976767)). Qed.
Lemma lem1976770 : term1355 = True.
Proof. exact (EQ_MP (@lem1976769) (@lem1976767)). Qed.
Lemma lem1976771 : term1354 = True.
Proof. exact (TRANS (@lem1976766) (@lem1976770)). Qed.
Lemma lem1976772 : True = term1354.
Proof. exact (SYM (@lem1976771)). Qed.
Lemma lem1976773 : term1354.
Proof. exact (EQ_MP (@lem1976772) (@lem0)). Qed.
Lemma lem1976774 (x : real) (y : real) (h1 : term1223 x y) : term1518 x y.
Proof. exact (conj (@lem1976773) (@lem1976742 x y h1)). Qed.
Lemma lem1976776 (x : real) (y : real) : term372 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1976777 (x : real) (y : real) : term1519 x y.
Proof. exact (@lem1976776 term17 (term1176 x y)). Qed.
Lemma lem1976778 (x : real) (y : real) (h1 : term1223 x y) : term1520 x y.
Proof. exact (@lem1976777 x y (@lem1976774 x y h1)). Qed.
Lemma lem1976779 (x : real) (y : real) : (term1521 x y) = (term1522 x y).
Proof. exact (@lem1483508 (term886 x y) term17 (term1175 x y)). Qed.
Lemma lem1976780 (x : real) (y : real) : (term1523 x y) = (term1524 x y).
Proof. exact (@lem1483508 (term52 x) term17 (term52 y)). Qed.
Lemma lem1976781 (y : real) : (term950 y) = (term951 y).
Proof. exact (@lem1483476 term17 term16 y). Qed.
Lemma lem1976783 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976784 : term922 = term923.
Proof. exact (@lem1976783 term23 term22). Qed.
Lemma lem1976785 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1976786 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1976787 : term925 = term23.
Proof. exact (EQ_MP (@lem1976786) (@lem1976785)). Qed.
Lemma lem1976788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976789 : term926 = term17.
Proof. exact (MK_COMB (@lem1976788) (@lem1976787)). Qed.
Lemma lem1976790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976791 : term923 = term28.
Proof. exact (MK_COMB (@lem1976790) (@lem1976789)). Qed.
Lemma lem1976792 : term922 = term28.
Proof. exact (TRANS (@lem1976784) (@lem1976791)). Qed.
Lemma lem1976793 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976794 : term927 = term30.
Proof. exact (MK_COMB (@lem1976793) (@lem1976792)). Qed.
Lemma lem1976795 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976796 (y : real) : (term951 y) = (term276 y).
Proof. exact (MK_COMB (@lem1976794) (@lem1976795 y)). Qed.
Lemma lem1976797 (y : real) : (term950 y) = (term276 y).
Proof. exact (TRANS (@lem1976781 y) (@lem1976796 y)). Qed.
Lemma lem1976798 (x : real) : (term950 x) = (term951 x).
Proof. exact (@lem1483476 term17 term16 x). Qed.
Lemma lem1976800 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976801 : term922 = term923.
Proof. exact (@lem1976800 term23 term22). Qed.
Lemma lem1976802 : term924 = term25.
Proof. exact (@lem996237 term25). Qed.
Lemma lem1976803 : (term924 = term25) = (term925 = term23).
Proof. exact (@lem1007663 term25 (BIT1 0) term25). Qed.
Lemma lem1976804 : term925 = term23.
Proof. exact (EQ_MP (@lem1976803) (@lem1976802)). Qed.
Lemma lem1976805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976806 : term926 = term17.
Proof. exact (MK_COMB (@lem1976805) (@lem1976804)). Qed.
Lemma lem1976807 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976808 : term923 = term28.
Proof. exact (MK_COMB (@lem1976807) (@lem1976806)). Qed.
Lemma lem1976809 : term922 = term28.
Proof. exact (TRANS (@lem1976801) (@lem1976808)). Qed.
Lemma lem1976810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976811 : term927 = term30.
Proof. exact (MK_COMB (@lem1976810) (@lem1976809)). Qed.
Lemma lem1976812 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976813 (x : real) : (term951 x) = (term276 x).
Proof. exact (MK_COMB (@lem1976811) (@lem1976812 x)). Qed.
Lemma lem1976814 (x : real) : (term950 x) = (term276 x).
Proof. exact (TRANS (@lem1976798 x) (@lem1976813 x)). Qed.
Lemma lem1976815 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976816 (x : real) : (term952 x) = (term354 x).
Proof. exact (MK_COMB (@lem1976815) (@lem1976814 x)). Qed.
Lemma lem1976817 (x : real) (y : real) : (term1524 x y) = (term1525 x y).
Proof. exact (MK_COMB (@lem1976816 x) (@lem1976797 y)). Qed.
Lemma lem1976818 (x : real) (y : real) : (term1523 x y) = (term1525 x y).
Proof. exact (TRANS (@lem1976780 x y) (@lem1976817 x y)). Qed.
Lemma lem1976819 (x : real) (y : real) : (term1364 x y) = (term1365 x y).
Proof. exact (@lem1483476 term17 term17 (term920 x y)). Qed.
Lemma lem1976821 (m : nat) (n : nat) : (term1366 m n) = (term66 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1976822 : term1367 = term1368.
Proof. exact (@lem1976821 term23 term23). Qed.
Lemma lem1976823 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976824 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976823) (@lem940073)). Qed.
Lemma lem1976825 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976826 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976825) (@lem1976824)). Qed.
Lemma lem1976827 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976828 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976827) (@lem1976826)). Qed.
Lemma lem1976829 : term1367 = term1373.
Proof. exact (TRANS (@lem1976822) (@lem1976828)). Qed.
Lemma lem1976830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976831 : term1374 = term1375.
Proof. exact (MK_COMB (@lem1976830) (@lem1976829)). Qed.
Lemma lem1976832 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976833 (x : real) (y : real) : (term1365 x y) = (term1376 x y).
Proof. exact (MK_COMB (@lem1976831) (@lem1976832 x y)). Qed.
Lemma lem1976834 (x : real) (y : real) : (term1364 x y) = (term1376 x y).
Proof. exact (TRANS (@lem1976819 x y) (@lem1976833 x y)). Qed.
Lemma lem1976835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976836 (x : real) (y : real) : (term1377 x y) = (term1378 x y).
Proof. exact (MK_COMB (@lem1976835) (@lem1976834 x y)). Qed.
Lemma lem1976837 (x : real) (y : real) : (term1522 x y) = (term1526 x y).
Proof. exact (MK_COMB (@lem1976836 x y) (@lem1976818 x y)). Qed.
Lemma lem1976838 (x : real) (y : real) : (term1521 x y) = (term1526 x y).
Proof. exact (TRANS (@lem1976779 x y) (@lem1976837 x y)). Qed.
Lemma lem1976839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1976840 (x : real) (y : real) : (term1527 x y) = (term1528 x y).
Proof. exact (MK_COMB (@lem1976839) (@lem1976838 x y)). Qed.
Lemma lem1976841 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976842 (x : real) (y : real) : (term1520 x y) = (term1529 x y).
Proof. exact (MK_COMB (@lem1976840 x y) (@lem1976841)). Qed.
Lemma lem1976843 (x : real) (y : real) (h1 : term1223 x y) : term1529 x y.
Proof. exact (EQ_MP (@lem1976842 x y) (@lem1976778 x y h1)). Qed.
Lemma lem1976845 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976846 : term1354 = term1355.
Proof. exact (@lem1976845 (NUMERAL 0) term23). Qed.
Lemma lem1976847 : term1356 = term25.
Proof. exact (@lem912803). Qed.
Lemma lem1976848 (h1 : term1356 = term25) : term1355 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term25 h1). Qed.
Lemma lem1976849 : (term1356 = term25) = (term1355 = True).
Proof. exact (prop_ext (fun h1 : term1356 = term25 => @lem1976848 h1) (fun h1 : term1355 = True => @lem1976847)). Qed.
Lemma lem1976850 : term1355 = True.
Proof. exact (EQ_MP (@lem1976849) (@lem1976847)). Qed.
Lemma lem1976851 : term1354 = True.
Proof. exact (TRANS (@lem1976846) (@lem1976850)). Qed.
Lemma lem1976852 : True = term1354.
Proof. exact (SYM (@lem1976851)). Qed.
Lemma lem1976853 : term1354.
Proof. exact (EQ_MP (@lem1976852) (@lem0)). Qed.
Lemma lem1976854 (x : real) (y : real) (h1 : term1223 x y) : term1530 x y.
Proof. exact (conj (@lem1976853) (@lem1976741 x y h1)). Qed.
Lemma lem1976856 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976857 (x : real) (y : real) : term1531 x y.
Proof. exact (@lem1976856 term17 (term1201 x y)). Qed.
Lemma lem1976858 (x : real) (y : real) (h1 : term1223 x y) : term1532 x y.
Proof. exact (@lem1976857 x y (@lem1976854 x y h1)). Qed.
Lemma lem1976859 (x : real) (y : real) : (term1533 x y) = (term1534 x y).
Proof. exact (@lem1483508 (term928 x y) term17 (term1200 x y)). Qed.
Lemma lem1976860 (x : real) (y : real) : (term1535 x y) = (term1536 x y).
Proof. exact (@lem1483508 x term17 (term1198 y)). Qed.
Lemma lem1976861 (y : real) : (term1390 y) = (term1391 y).
Proof. exact (@lem1483476 term17 term1195 y). Qed.
Lemma lem1976863 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976864 : term1392 = term1393.
Proof. exact (@lem1976863 term23 term1032). Qed.
Lemma lem1976865 : term1394 = term1030.
Proof. exact (@lem996238 term1030). Qed.
Lemma lem1976866 : (term1394 = term1030) = (term1395 = term1396).
Proof. exact (@lem996664 (BIT1 0) term1030 term1030). Qed.
Lemma lem1976867 : term1395 = term1396.
Proof. exact (EQ_MP (@lem1976866) (@lem1976865)). Qed.
Lemma lem1976868 : (term1395 = term1396) = (term1397 = term1398).
Proof. exact (@lem1007663 term25 term1030 term1396). Qed.
Lemma lem1976869 : term1397 = term1398.
Proof. exact (EQ_MP (@lem1976868) (@lem1976867)). Qed.
Lemma lem1976870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976871 : term1399 = term1400.
Proof. exact (MK_COMB (@lem1976870) (@lem1976869)). Qed.
Lemma lem1976872 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976873 : term1393 = term1401.
Proof. exact (MK_COMB (@lem1976872) (@lem1976871)). Qed.
Lemma lem1976874 : term1392 = term1401.
Proof. exact (TRANS (@lem1976864) (@lem1976873)). Qed.
Lemma lem1976875 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976876 : term1402 = term1403.
Proof. exact (MK_COMB (@lem1976875) (@lem1976874)). Qed.
Lemma lem1976877 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976878 (y : real) : (term1391 y) = (term1404 y).
Proof. exact (MK_COMB (@lem1976876) (@lem1976877 y)). Qed.
Lemma lem1976879 (y : real) : (term1390 y) = (term1404 y).
Proof. exact (TRANS (@lem1976861 y) (@lem1976878 y)). Qed.
Lemma lem1976882 (x : real) : (term285 x) = (term285 x).
Proof. exact (eq_refl (term285 x)). Qed.
Lemma lem1976883 (x : real) (y : real) : (term1536 x y) = (term1537 x y).
Proof. exact (MK_COMB (@lem1976882 x) (@lem1976879 y)). Qed.
Lemma lem1976884 (x : real) (y : real) : (term1535 x y) = (term1537 x y).
Proof. exact (TRANS (@lem1976860 x y) (@lem1976883 x y)). Qed.
Lemma lem1976885 (x : real) (y : real) : (term1414 x y) = (term1415 x y).
Proof. exact (@lem1483476 term17 term28 (term920 x y)). Qed.
Lemma lem1976887 (m : nat) (n : nat) : (term921 m n) = (term19 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1976888 : term1416 = term1417.
Proof. exact (@lem1976887 term23 term23). Qed.
Lemma lem1976889 : (term69 = (BIT1 0)) = (term1369 = term1370).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1976890 : term1369 = term1370.
Proof. exact (EQ_MP (@lem1976889) (@lem940073)). Qed.
Lemma lem1976891 : (term1369 = term1370) = (term1371 = term1372).
Proof. exact (@lem1008952 term25 term1370). Qed.
Lemma lem1976892 : term1371 = term1372.
Proof. exact (EQ_MP (@lem1976891) (@lem1976890)). Qed.
Lemma lem1976893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976894 : term1368 = term1373.
Proof. exact (MK_COMB (@lem1976893) (@lem1976892)). Qed.
Lemma lem1976895 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976896 : term1417 = term1418.
Proof. exact (MK_COMB (@lem1976895) (@lem1976894)). Qed.
Lemma lem1976897 : term1416 = term1418.
Proof. exact (TRANS (@lem1976888) (@lem1976896)). Qed.
Lemma lem1976898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976899 : term1419 = term1420.
Proof. exact (MK_COMB (@lem1976898) (@lem1976897)). Qed.
Lemma lem1976900 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976901 (x : real) (y : real) : (term1415 x y) = (term1421 x y).
Proof. exact (MK_COMB (@lem1976899) (@lem1976900 x y)). Qed.
Lemma lem1976902 (x : real) (y : real) : (term1414 x y) = (term1421 x y).
Proof. exact (TRANS (@lem1976885 x y) (@lem1976901 x y)). Qed.
Lemma lem1976903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976904 (x : real) (y : real) : (term1422 x y) = (term1423 x y).
Proof. exact (MK_COMB (@lem1976903) (@lem1976902 x y)). Qed.
Lemma lem1976905 (x : real) (y : real) : (term1534 x y) = (term1538 x y).
Proof. exact (MK_COMB (@lem1976904 x y) (@lem1976884 x y)). Qed.
Lemma lem1976906 (x : real) (y : real) : (term1533 x y) = (term1538 x y).
Proof. exact (TRANS (@lem1976859 x y) (@lem1976905 x y)). Qed.
Lemma lem1976907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976908 (x : real) (y : real) : (term1539 x y) = (term1540 x y).
Proof. exact (MK_COMB (@lem1976907) (@lem1976906 x y)). Qed.
Lemma lem1976909 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976910 (x : real) (y : real) : (term1532 x y) = (term1541 x y).
Proof. exact (MK_COMB (@lem1976908 x y) (@lem1976909)). Qed.
Lemma lem1976911 (x : real) (y : real) (h1 : term1223 x y) : term1541 x y.
Proof. exact (EQ_MP (@lem1976910 x y) (@lem1976858 x y h1)). Qed.
Lemma lem1976912 (x : real) (y : real) (h1 : term1223 x y) : term1542 x y.
Proof. exact (conj (@lem1976911 x y h1) (@lem1976843 x y h1)). Qed.
Lemma lem1976914 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976915 (x : real) (y : real) : term1543 x y.
Proof. exact (@lem1976914 (term1538 x y) (term1526 x y)). Qed.
Lemma lem1976916 (x : real) (y : real) (h1 : term1223 x y) : term1544 x y.
Proof. exact (@lem1976915 x y (@lem1976912 x y h1)). Qed.
Lemma lem1976917 (x : real) (y : real) : (term1545 x y) = (term1546 x y).
Proof. exact (@lem1483480 (term1421 x y) (term1376 x y) (term1537 x y) (term1525 x y)). Qed.
Lemma lem1976918 (x : real) (y : real) : (term1433 x y) = (term1434 x y).
Proof. exact (@lem1483438 term1418 term1373 (term920 x y)). Qed.
Lemma lem1976920 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1976921 : term1435 = term121.
Proof. exact (@lem1976920 term1372). Qed.
Lemma lem1976922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976923 : term1436 = term124.
Proof. exact (MK_COMB (@lem1976922) (@lem1976921)). Qed.
Lemma lem1976924 (x : real) (y : real) : (term920 x y) = (term920 x y).
Proof. exact (eq_refl (term920 x y)). Qed.
Lemma lem1976925 (x : real) (y : real) : (term1434 x y) = (term1437 x y).
Proof. exact (MK_COMB (@lem1976923) (@lem1976924 x y)). Qed.
Lemma lem1976926 (x : real) (y : real) : (term1433 x y) = (term1437 x y).
Proof. exact (TRANS (@lem1976918 x y) (@lem1976925 x y)). Qed.
Lemma lem1976927 (x : real) (y : real) : (term1437 x y) = term121.
Proof. exact (@lem1483446 (term920 x y)). Qed.
Lemma lem1976928 (x : real) (y : real) : (term1433 x y) = term121.
Proof. exact (TRANS (@lem1976926 x y) (@lem1976927 x y)). Qed.
Lemma lem1976929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976930 (x : real) (y : real) : (term1438 x y) = term127.
Proof. exact (MK_COMB (@lem1976929) (@lem1976928 x y)). Qed.
Lemma lem1976931 (x : real) (y : real) : (term1547 x y) = (term1548 x y).
Proof. exact (@lem1483480 (term283 x) (term276 x) (term1404 y) (term276 y)). Qed.
Lemma lem1976932 (x : real) : (term1507 x) = (term1508 x).
Proof. exact (@lem1483438 term17 term28 x). Qed.
Lemma lem1976934 (m : nat) : (term1473 m) = term121.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1976935 : term1509 = term121.
Proof. exact (@lem1976934 term23). Qed.
Lemma lem1976936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976937 : term1510 = term124.
Proof. exact (MK_COMB (@lem1976936) (@lem1976935)). Qed.
Lemma lem1976938 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1976939 (x : real) : (term1508 x) = (term322 x).
Proof. exact (MK_COMB (@lem1976937) (@lem1976938 x)). Qed.
Lemma lem1976940 (x : real) : (term1507 x) = (term322 x).
Proof. exact (TRANS (@lem1976932 x) (@lem1976939 x)). Qed.
Lemma lem1976941 (x : real) : (term322 x) = term121.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1976942 (x : real) : (term1507 x) = term121.
Proof. exact (TRANS (@lem1976940 x) (@lem1976941 x)). Qed.
Lemma lem1976943 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1976944 (x : real) : (term1511 x) = term127.
Proof. exact (MK_COMB (@lem1976943) (@lem1976942 x)). Qed.
Lemma lem1976945 (y : real) : (term1451 y) = (term1452 y).
Proof. exact (@lem1483438 term1401 term28 y). Qed.
Lemma lem1976946 : term1453 = term1454.
Proof. exact (@lem1367763 term1398 term23). Qed.
Lemma lem1976947 : term1445 = term1328.
Proof. exact (@lem707207). Qed.
Lemma lem1976948 : (term1445 = term1328) = (term1446 = term1326).
Proof. exact (@lem1006570 term1396 term25 term1328). Qed.
Lemma lem1976949 : term1446 = term1326.
Proof. exact (EQ_MP (@lem1976948) (@lem1976947)). Qed.
Lemma lem1976950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1976951 : term1444 = term1332.
Proof. exact (MK_COMB (@lem1976950) (@lem1976949)). Qed.
Lemma lem1976952 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1976953 : term1454 = term1344.
Proof. exact (MK_COMB (@lem1976952) (@lem1976951)). Qed.
Lemma lem1976954 : term1453 = term1344.
Proof. exact (TRANS (@lem1976946) (@lem1976953)). Qed.
Lemma lem1976955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1976956 : term1455 = term1346.
Proof. exact (MK_COMB (@lem1976955) (@lem1976954)). Qed.
Lemma lem1976957 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1976958 (y : real) : (term1452 y) = (term1347 y).
Proof. exact (MK_COMB (@lem1976956) (@lem1976957 y)). Qed.
Lemma lem1976959 (y : real) : (term1451 y) = (term1347 y).
Proof. exact (TRANS (@lem1976945 y) (@lem1976958 y)). Qed.
Lemma lem1976960 (x : real) (y : real) : (term1548 x y) = (term1549 y).
Proof. exact (MK_COMB (@lem1976944 x) (@lem1976959 y)). Qed.
Lemma lem1976961 (x : real) (y : real) : (term1547 x y) = (term1549 y).
Proof. exact (TRANS (@lem1976931 x y) (@lem1976960 x y)). Qed.
Lemma lem1976962 (y : real) : (term1549 y) = (term1347 y).
Proof. exact (@lem1483448 (term1347 y)). Qed.
Lemma lem1976963 (x : real) (y : real) : (term1547 x y) = (term1347 y).
Proof. exact (TRANS (@lem1976961 x y) (@lem1976962 y)). Qed.
Lemma lem1976964 (x : real) (y : real) : (term1546 x y) = (term1549 y).
Proof. exact (MK_COMB (@lem1976930 x y) (@lem1976963 x y)). Qed.
Lemma lem1976965 (x : real) (y : real) : (term1545 x y) = (term1549 y).
Proof. exact (TRANS (@lem1976917 x y) (@lem1976964 x y)). Qed.
Lemma lem1976966 (y : real) : (term1549 y) = (term1347 y).
Proof. exact (@lem1483448 (term1347 y)). Qed.
Lemma lem1976967 (x : real) (y : real) : (term1545 x y) = (term1347 y).
Proof. exact (TRANS (@lem1976965 x y) (@lem1976966 y)). Qed.
Lemma lem1976968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976969 (x : real) (y : real) : (term1550 x y) = (term1551 y).
Proof. exact (MK_COMB (@lem1976968) (@lem1976967 x y)). Qed.
Lemma lem1976970 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976971 (x : real) (y : real) : (term1544 x y) = (term1552 y).
Proof. exact (MK_COMB (@lem1976969 x y) (@lem1976970)). Qed.
Lemma lem1976972 (x : real) (y : real) (h1 : term1223 x y) : term1552 y.
Proof. exact (EQ_MP (@lem1976971 x y) (@lem1976916 x y h1)). Qed.
Lemma lem1976974 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1976975 : term368 = term369.
Proof. exact (@lem1976974 (NUMERAL 0) term22). Qed.
Lemma lem1976976 : term370 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1976977 (h1 : term370 = (BIT1 0)) : term369 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1976978 : (term370 = (BIT1 0)) = (term369 = True).
Proof. exact (prop_ext (fun h1 : term370 = (BIT1 0) => @lem1976977 h1) (fun h1 : term369 = True => @lem1976976)). Qed.
Lemma lem1976979 : term369 = True.
Proof. exact (EQ_MP (@lem1976978) (@lem1976976)). Qed.
Lemma lem1976980 : term368 = True.
Proof. exact (TRANS (@lem1976975) (@lem1976979)). Qed.
Lemma lem1976981 : True = term368.
Proof. exact (SYM (@lem1976980)). Qed.
Lemma lem1976982 : term368.
Proof. exact (EQ_MP (@lem1976981) (@lem0)). Qed.
Lemma lem1976983 (x : real) (y : real) (h1 : term1223 x y) : term1553 y.
Proof. exact (conj (@lem1976982) (@lem1976972 x y h1)). Qed.
Lemma lem1976985 (x : real) (y : real) : term381 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1976986 (y : real) : term1554 y.
Proof. exact (@lem1976985 term71 (term1347 y)). Qed.
Lemma lem1976987 (x : real) (y : real) (h1 : term1223 x y) : term1555 y.
Proof. exact (@lem1976986 y (@lem1976983 x y h1)). Qed.
Lemma lem1976988 (y : real) : (term1556 y) = (term1347 y).
Proof. exact (@lem1483460 (term1347 y)). Qed.
Lemma lem1976989 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1976990 (y : real) : (term1557 y) = (term1551 y).
Proof. exact (MK_COMB (@lem1976989) (@lem1976988 y)). Qed.
Lemma lem1976991 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1976992 (y : real) : (term1555 y) = (term1552 y).
Proof. exact (MK_COMB (@lem1976990 y) (@lem1976991)). Qed.
Lemma lem1976993 (x : real) (y : real) (h1 : term1223 x y) : term1552 y.
Proof. exact (EQ_MP (@lem1976992 y) (@lem1976987 x y h1)). Qed.
Lemma lem1976994 (x : real) (y : real) (h1 : term1223 x y) : term1558 y.
Proof. exact (conj (@lem1976993 x y h1) (@lem1976763 x y h1)). Qed.
Lemma lem1976996 (x : real) (y : real) : term387 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1976997 (y : real) : term1559 y.
Proof. exact (@lem1976996 (term1347 y) (term1336 y)). Qed.
Lemma lem1976998 (x : real) (y : real) (h1 : term1223 x y) : term1560 y.
Proof. exact (@lem1976997 y (@lem1976994 x y h1)). Qed.
Lemma lem1976999 (y : real) : (term1477 y) = (term1478 y).
Proof. exact (@lem1483438 term1344 term1332 y). Qed.
Lemma lem1977001 (m : nat) : (term120 m) = term121.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1977002 : term1479 = term121.
Proof. exact (@lem1977001 term1326). Qed.
Lemma lem1977003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1977004 : term1480 = term124.
Proof. exact (MK_COMB (@lem1977003) (@lem1977002)). Qed.
Lemma lem1977005 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1977006 (y : real) : (term1478 y) = (term322 y).
Proof. exact (MK_COMB (@lem1977004) (@lem1977005 y)). Qed.
Lemma lem1977007 (y : real) : (term1477 y) = (term322 y).
Proof. exact (TRANS (@lem1976999 y) (@lem1977006 y)). Qed.
Lemma lem1977008 (y : real) : (term322 y) = term121.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1977009 (y : real) : (term1477 y) = term121.
Proof. exact (TRANS (@lem1977007 y) (@lem1977008 y)). Qed.
Lemma lem1977010 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1977011 (y : real) : (term1561 y) = term143.
Proof. exact (MK_COMB (@lem1977010) (@lem1977009 y)). Qed.
Lemma lem1977012 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem1977013 (y : real) : (term1560 y) = term145.
Proof. exact (MK_COMB (@lem1977011 y) (@lem1977012)). Qed.
Lemma lem1977014 (x : real) (y : real) (h1 : term1223 x y) : term145.
Proof. exact (EQ_MP (@lem1977013 y) (@lem1976998 x y h1)). Qed.
Lemma lem1977016 (n : nat) (m : nat) : (term151 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1977017 : term145 = term152.
Proof. exact (@lem1977016 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1977018 : term152 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1977019 : term145 = False.
Proof. exact (TRANS (@lem1977017) (@lem1977018)). Qed.
Lemma lem1977020 (x : real) (y : real) (h1 : term1223 x y) : False.
Proof. exact (EQ_MP (@lem1977019) (@lem1977014 x y h1)). Qed.
Lemma lem1977021 (x : real) (y : real) (h1 : term1225 x y) : False.
Proof. exact (or_elim (@lem1976523 x y h1) (fun h0 : term1170 x y => @lem1976729 x y h0) (fun h0 : term1223 x y => @lem1977020 x y h0)). Qed.
Lemma lem1977022 (x : real) (y : real) (h1 : term1323 x y) : False.
Proof. exact (or_elim (@lem1976107 x y h1) (fun h0 : term1321 x y => @lem1976522 x y h0) (fun h0 : term1225 x y => @lem1977021 x y h0)). Qed.
Lemma lem1977023 (x : real) (y : real) (h1 : term988 x y) : term988 x y.
Proof. exact (h1). Qed.
Lemma lem1977024 (x : real) (y : real) (h1 : term988 x y) : term1323 x y.
Proof. exact (EQ_MP (@lem1976106 x y) (@lem1977023 x y h1)). Qed.
Lemma lem1977025 (x : real) (y : real) (h1 : term988 x y) : (term1323 x y) = False.
Proof. exact (prop_ext (fun h2 : term1323 x y => @lem1977022 x y h2) (fun h2 : False => @lem1977024 x y h1)). Qed.
Lemma lem1977026 (x : real) (y : real) (h1 : term988 x y) : False.
Proof. exact (EQ_MP (@lem1977025 x y h1) (@lem1977024 x y h1)). Qed.
Lemma lem1977027 (y : real) (x : real) (h1 : term911 y x) : term911 y x.
Proof. exact (h1). Qed.
Lemma lem1977028 (y : real) (x : real) (h1 : term911 y x) : term988 x y.
Proof. exact (EQ_MP (@lem1974955 x y) (@lem1977027 y x h1)). Qed.
Lemma lem1977029 (y : real) (x : real) (h1 : term911 y x) : (term988 x y) = False.
Proof. exact (prop_ext (fun h2 : term988 x y => @lem1977026 x y h2) (fun h2 : False => @lem1977028 y x h1)). Qed.
Lemma lem1977030 (y : real) (x : real) (h1 : term911 y x) : False.
Proof. exact (EQ_MP (@lem1977029 y x h1) (@lem1977028 y x h1)). Qed.
Lemma lem1977031 (y : real) (x : real) : term1562 y x.
Proof. exact (fun h0 : term911 y x => @lem1977030 y x h0). Qed.
Lemma lem1977032 (y : real) (x : real) : term1563 y x.
Proof. exact (@lem1386578 (term1564 y x)). Qed.
Lemma lem1977033 (y : real) (x : real) : term1564 y x.
Proof. exact (@lem1977032 y x (@lem1977031 y x)). Qed.
Lemma lem1977034 (x : real) (y : real) (h1 : real_le x y) : term912 y x.
Proof. exact (@lem1977033 y x (@lem1973328 x y h1)). Qed.
Lemma lem1977035 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) : term908 y x.
Proof. exact (@lem1977034 x y h2 (@lem1973201 x h1)). Qed.
Lemma lem1977036 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term899 y x.
Proof. exact (@lem1977035 x y h1 h2 (@lem1972970 y h3)). Qed.
Lemma lem1977037 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term890 y x.
Proof. exact (EQ_MP (@lem1974552 y x) (@lem1977036 x y h1 h2 h3)). Qed.
Lemma lem1977038 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term869 y x.
Proof. exact (EQ_MP (@lem1974524 y x) (@lem1977037 x y h1 h2 h3)). Qed.
Lemma lem1977039 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term868 y x.
Proof. exact (EQ_MP (@lem1974485 y x) (@lem1977038 x y h1 h2 h3)). Qed.
Lemma lem1977040 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term866 y x.
Proof. exact (@lem1977039 x y h1 h2 h3 (@lem1970191 x y)). Qed.
Lemma lem1977041 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term854 y x.
Proof. exact (@lem1974465 y x (@lem1977040 x y h1 h2 h3)). Qed.
Lemma lem1977042 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) (h3 : term178 y) : term673 x y.
Proof. exact (EQ_MP (@lem1974462 x y h1 h3) (@lem1977041 x y h1 h2 h3)). Qed.
Lemma lem1977043 (x : real) (y : real) (h1 : term171 x) (h2 : real_le x y) : term673 x y.
Proof. exact (or_elim (@lem1972969 y) (fun h0 : term178 y => @lem1977042 x y h1 h2 h0) (fun h0 : term171 y => @lem1974384 x y h1 h0 h2)). Qed.
Lemma lem1977044 (x : real) (y : real) (h1 : real_le x y) : term673 x y.
Proof. exact (or_elim (@lem1973199 x) (fun h0 : term178 x => @lem1973793 y x h1 h0) (fun h0 : term171 x => @lem1977043 x y h0 h1)). Qed.
Lemma lem1977045 (x : real) (y : real) : term688 x y.
Proof. exact (fun h0 : real_le x y => @lem1977044 x y h0). Qed.
Lemma lem1977050 (x : real) : term692 x.
Proof. exact (fun y : real => @lem1977045 x y). Qed.
Lemma lem1977055 : term696.
Proof. exact (fun x : real => @lem1977050 x). Qed.
Lemma lem1977056 : term698.
Proof. exact (conj (@lem1973327) (@lem1977055)). Qed.
Lemma lem1977057 : term707.
Proof. exact (@lem1973269 (@lem1977056)). Qed.

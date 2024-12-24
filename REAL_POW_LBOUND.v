Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LBOUND_term_abbrevs.
Require Import REAL_ADD_RID_spec.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_OF_NUM_SUC_spec.
Require Import REAL_POS_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1340049_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483452_spec.
Require Import thm1483454_spec.
Require Import thm1483460_spec.
Require Import thm1483474_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483486_spec.
Require Import thm1483488_spec.
Require Import thm1483498_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1703857 (n : real) (x : real) : (term0 n x) = (term1 n x).
Proof. exact (@lem17646 (term2 n x) (term3 n x)). Qed.
Lemma lem1703858 (n : real) (x : real) : (term2 n x) = (term4 n x).
Proof. exact (@lem1483523 (term5 n x) (term6 n x)). Qed.
Lemma lem1703870 (x : real) (n : real) : (term7 n x) = (term8 x n).
Proof. exact (@lem1483452 x (term9 n)). Qed.
Lemma lem1703871 (n : real) (x : real) : (term8 x n) = (term10 n x).
Proof. exact (@lem1483508 n x term11). Qed.
Lemma lem1703872 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1483474 term11 x). Qed.
Lemma lem1703873 (x : real) : (term13 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1703874 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem1703872 x) (@lem1703873 x)). Qed.
Lemma lem1703875 (n : real) (x : real) : (real_mul x n) = (real_mul n x).
Proof. exact (@lem1483474 n x). Qed.
Lemma lem1703876 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1703877 (n : real) (x : real) : (term14 x n) = (term14 n x).
Proof. exact (MK_COMB (@lem1703876) (@lem1703875 n x)). Qed.
Lemma lem1703878 (n : real) (x : real) : (term10 n x) = (term15 n x).
Proof. exact (MK_COMB (@lem1703877 n x) (@lem1703874 x)). Qed.
Lemma lem1703879 (n : real) (x : real) : (term8 x n) = (term15 n x).
Proof. exact (TRANS (@lem1703871 n x) (@lem1703878 n x)). Qed.
Lemma lem1703881 (n : real) (x : real) : (term7 n x) = (term15 n x).
Proof. exact (TRANS (@lem1703870 x n) (@lem1703879 n x)). Qed.
Lemma lem1703884 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1703885 (n : real) (x : real) : (term6 n x) = (term17 n x).
Proof. exact (MK_COMB (@lem1703884) (@lem1703881 n x)). Qed.
Lemma lem1703886 (n : real) (x : real) : (term17 n x) = (term18 n x).
Proof. exact (@lem1483484 (real_mul n x) term11 x). Qed.
Lemma lem1703887 (x : real) : (term19 x) = (term9 x).
Proof. exact (@lem1483488 x term11). Qed.
Lemma lem1703888 (n : real) (x : real) : (term14 n x) = (term14 n x).
Proof. exact (eq_refl (term14 n x)). Qed.
Lemma lem1703889 (n : real) (x : real) : (term18 n x) = (term20 n x).
Proof. exact (MK_COMB (@lem1703888 n x) (@lem1703887 x)). Qed.
Lemma lem1703890 (n : real) (x : real) : (term17 n x) = (term20 n x).
Proof. exact (TRANS (@lem1703886 n x) (@lem1703889 n x)). Qed.
Lemma lem1703891 (n : real) (x : real) : (term6 n x) = (term20 n x).
Proof. exact (TRANS (@lem1703885 n x) (@lem1703890 n x)). Qed.
Lemma lem1703904 (n : real) (x : real) : (term21 n x) = (term22 n x).
Proof. exact (@lem1483488 (real_mul n x) term11). Qed.
Lemma lem1703911 (x : real) : (term19 x) = (term9 x).
Proof. exact (@lem1483488 x term11). Qed.
Lemma lem1703912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1703913 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1703912) (@lem1703911 x)). Qed.
Lemma lem1703914 (n : real) (x : real) : (term5 n x) = (term25 n x).
Proof. exact (MK_COMB (@lem1703913 x) (@lem1703904 n x)). Qed.
Lemma lem1703915 (n : real) (x : real) : (term25 n x) = (term26 n x).
Proof. exact (@lem1483454 x term11 (term22 n x)). Qed.
Lemma lem1703916 (n : real) (x : real) : (term27 n x) = (term28 n x).
Proof. exact (@lem1483508 (real_mul n x) x term11). Qed.
Lemma lem1703917 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1483474 term11 x). Qed.
Lemma lem1703918 (x : real) : (term13 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1703919 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem1703917 x) (@lem1703918 x)). Qed.
Lemma lem1703920 (n : real) (x : real) : (term29 n x) = (term30 n x).
Proof. exact (@lem1483478 n x x). Qed.
Lemma lem1703921 (x : real) : (real_mul x x) = (term31 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1703922 (n : real) : (real_mul n) = (real_mul n).
Proof. exact (eq_refl (real_mul n)). Qed.
Lemma lem1703923 (n : real) (x : real) : (term30 n x) = (term32 n x).
Proof. exact (MK_COMB (@lem1703922 n) (@lem1703921 x)). Qed.
Lemma lem1703924 (n : real) (x : real) : (term29 n x) = (term32 n x).
Proof. exact (TRANS (@lem1703920 n x) (@lem1703923 n x)). Qed.
Lemma lem1703925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1703926 (n : real) (x : real) : (term33 n x) = (term34 n x).
Proof. exact (MK_COMB (@lem1703925) (@lem1703924 n x)). Qed.
Lemma lem1703927 (n : real) (x : real) : (term28 n x) = (term35 n x).
Proof. exact (MK_COMB (@lem1703926 n x) (@lem1703919 x)). Qed.
Lemma lem1703928 (n : real) (x : real) : (term27 n x) = (term35 n x).
Proof. exact (TRANS (@lem1703916 n x) (@lem1703927 n x)). Qed.
Lemma lem1703929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1703930 (n : real) (x : real) : (term36 n x) = (term37 n x).
Proof. exact (MK_COMB (@lem1703929) (@lem1703928 n x)). Qed.
Lemma lem1703931 (n : real) (x : real) : (term38 n x) = (term39 n x).
Proof. exact (@lem1483508 (real_mul n x) term11 term11). Qed.
Lemma lem1703933 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1703934 : term42 = term43.
Proof. exact (@lem1703933 term44 term44). Qed.
Lemma lem1703935 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1703936 : term46 = term44.
Proof. exact (EQ_MP (@lem1703935) (@lem940073)). Qed.
Lemma lem1703937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1703938 : term43 = term11.
Proof. exact (MK_COMB (@lem1703937) (@lem1703936)). Qed.
Lemma lem1703939 : term42 = term11.
Proof. exact (TRANS (@lem1703934) (@lem1703938)). Qed.
Lemma lem1703942 (n : real) (x : real) : (term47 n x) = (real_mul n x).
Proof. exact (@lem1483436 (real_mul n x)). Qed.
Lemma lem1703943 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1703944 (n : real) (x : real) : (term48 n x) = (term14 n x).
Proof. exact (MK_COMB (@lem1703943) (@lem1703942 n x)). Qed.
Lemma lem1703945 (n : real) (x : real) : (term39 n x) = (term22 n x).
Proof. exact (MK_COMB (@lem1703944 n x) (@lem1703939)). Qed.
Lemma lem1703946 (n : real) (x : real) : (term38 n x) = (term22 n x).
Proof. exact (TRANS (@lem1703931 n x) (@lem1703945 n x)). Qed.
Lemma lem1703947 (n : real) (x : real) : (term26 n x) = (term49 n x).
Proof. exact (MK_COMB (@lem1703930 n x) (@lem1703946 n x)). Qed.
Lemma lem1703948 (n : real) (x : real) : (term25 n x) = (term49 n x).
Proof. exact (TRANS (@lem1703915 n x) (@lem1703947 n x)). Qed.
Lemma lem1703949 (n : real) (x : real) : (term49 n x) = (term50 n x).
Proof. exact (@lem1483482 (term32 n x) x (term22 n x)). Qed.
Lemma lem1703954 (n : real) (x : real) : (term51 n x) = (term20 n x).
Proof. exact (@lem1483484 (real_mul n x) x term11). Qed.
Lemma lem1703955 (n : real) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (eq_refl (term34 n x)). Qed.
Lemma lem1703956 (n : real) (x : real) : (term50 n x) = (term52 n x).
Proof. exact (MK_COMB (@lem1703955 n x) (@lem1703954 n x)). Qed.
Lemma lem1703957 (n : real) (x : real) : (term49 n x) = (term52 n x).
Proof. exact (TRANS (@lem1703949 n x) (@lem1703956 n x)). Qed.
Lemma lem1703958 (n : real) (x : real) : (term25 n x) = (term52 n x).
Proof. exact (TRANS (@lem1703948 n x) (@lem1703957 n x)). Qed.
Lemma lem1703959 (n : real) (x : real) : (term5 n x) = (term52 n x).
Proof. exact (TRANS (@lem1703914 n x) (@lem1703958 n x)). Qed.
Lemma lem1703960 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1703961 (n : real) (x : real) : (term53 n x) = (term54 n x).
Proof. exact (MK_COMB (@lem1703960) (@lem1703959 n x)). Qed.
Lemma lem1703962 (n : real) (x : real) : (term55 n x) = (term56 n x).
Proof. exact (MK_COMB (@lem1703961 n x) (@lem1703891 n x)). Qed.
Lemma lem1703963 (n : real) (x : real) : (term56 n x) = (term57 n x).
Proof. exact (@lem1483519 (term52 n x) (term20 n x)). Qed.
Lemma lem1703964 (n : real) (x : real) : (term58 n x) = (term59 n x).
Proof. exact (@lem1483508 (real_mul n x) term60 (term9 x)). Qed.
Lemma lem1703965 (x : real) : (term61 x) = (term62 x).
Proof. exact (@lem1483508 x term60 term11). Qed.
Lemma lem1703967 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1703968 : term65 = term66.
Proof. exact (@lem1703967 term44 term44). Qed.
Lemma lem1703969 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1703970 : term46 = term44.
Proof. exact (EQ_MP (@lem1703969) (@lem940073)). Qed.
Lemma lem1703971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1703972 : term43 = term11.
Proof. exact (MK_COMB (@lem1703971) (@lem1703970)). Qed.
Lemma lem1703973 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1703974 : term66 = term60.
Proof. exact (MK_COMB (@lem1703973) (@lem1703972)). Qed.
Lemma lem1703975 : term65 = term60.
Proof. exact (TRANS (@lem1703968) (@lem1703974)). Qed.
Lemma lem1703978 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1703979 (x : real) : (term62 x) = (term68 x).
Proof. exact (MK_COMB (@lem1703978 x) (@lem1703975)). Qed.
Lemma lem1703980 (x : real) : (term61 x) = (term68 x).
Proof. exact (TRANS (@lem1703965 x) (@lem1703979 x)). Qed.
Lemma lem1703983 (n : real) (x : real) : (term69 n x) = (term69 n x).
Proof. exact (eq_refl (term69 n x)). Qed.
Lemma lem1703984 (n : real) (x : real) : (term59 n x) = (term70 n x).
Proof. exact (MK_COMB (@lem1703983 n x) (@lem1703980 x)). Qed.
Lemma lem1703985 (n : real) (x : real) : (term58 n x) = (term70 n x).
Proof. exact (TRANS (@lem1703964 n x) (@lem1703984 n x)). Qed.
Lemma lem1703986 (n : real) (x : real) : (term71 n x) = (term71 n x).
Proof. exact (eq_refl (term71 n x)). Qed.
Lemma lem1703987 (n : real) (x : real) : (term57 n x) = (term72 n x).
Proof. exact (MK_COMB (@lem1703986 n x) (@lem1703985 n x)). Qed.
Lemma lem1703988 (n : real) (x : real) : (term72 n x) = (term73 n x).
Proof. exact (@lem1483482 (term32 n x) (term20 n x) (term70 n x)). Qed.
Lemma lem1703989 (n : real) (x : real) : (term74 n x) = (term75 n x).
Proof. exact (@lem1483480 (real_mul n x) (term76 n x) (term9 x) (term68 x)). Qed.
Lemma lem1703990 (n : real) (x : real) : (term77 n x) = (term78 n x).
Proof. exact (@lem1483442 term60 (real_mul n x)). Qed.
Lemma lem1703992 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1703993 : term81 = term80.
Proof. exact (@lem1703992 term44). Qed.
Lemma lem1703994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1703995 : term82 = term83.
Proof. exact (MK_COMB (@lem1703994) (@lem1703993)). Qed.
Lemma lem1703996 (n : real) (x : real) : (real_mul n x) = (real_mul n x).
Proof. exact (eq_refl (real_mul n x)). Qed.
Lemma lem1703997 (n : real) (x : real) : (term78 n x) = (term84 n x).
Proof. exact (MK_COMB (@lem1703995) (@lem1703996 n x)). Qed.
Lemma lem1703998 (n : real) (x : real) : (term77 n x) = (term84 n x).
Proof. exact (TRANS (@lem1703990 n x) (@lem1703997 n x)). Qed.
Lemma lem1703999 (n : real) (x : real) : (term84 n x) = term80.
Proof. exact (@lem1483446 (real_mul n x)). Qed.
Lemma lem1704000 (n : real) (x : real) : (term77 n x) = term80.
Proof. exact (TRANS (@lem1703998 n x) (@lem1703999 n x)). Qed.
Lemma lem1704001 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704002 (n : real) (x : real) : (term85 n x) = term86.
Proof. exact (MK_COMB (@lem1704001) (@lem1704000 n x)). Qed.
Lemma lem1704003 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483480 x (term89 x) term11 term60). Qed.
Lemma lem1704004 (x : real) : (term90 x) = (term91 x).
Proof. exact (@lem1483442 term60 x). Qed.
Lemma lem1704006 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704007 : term81 = term80.
Proof. exact (@lem1704006 term44). Qed.
Lemma lem1704008 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704009 : term82 = term83.
Proof. exact (MK_COMB (@lem1704008) (@lem1704007)). Qed.
Lemma lem1704010 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1704011 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1704009) (@lem1704010 x)). Qed.
Lemma lem1704012 (x : real) : (term90 x) = (term92 x).
Proof. exact (TRANS (@lem1704004 x) (@lem1704011 x)). Qed.
Lemma lem1704013 (x : real) : (term92 x) = term80.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1704014 (x : real) : (term90 x) = term80.
Proof. exact (TRANS (@lem1704012 x) (@lem1704013 x)). Qed.
Lemma lem1704015 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704016 (x : real) : (term93 x) = term86.
Proof. exact (MK_COMB (@lem1704015) (@lem1704014 x)). Qed.
Lemma lem1704018 (m : nat) : (term94 m) = term80.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1704019 : term95 = term80.
Proof. exact (@lem1704018 term44). Qed.
Lemma lem1704020 (x : real) : (term88 x) = term96.
Proof. exact (MK_COMB (@lem1704016 x) (@lem1704019)). Qed.
Lemma lem1704021 (x : real) : (term87 x) = term96.
Proof. exact (TRANS (@lem1704003 x) (@lem1704020 x)). Qed.
Lemma lem1704022 : term96 = term80.
Proof. exact (@lem1483448 term80). Qed.
Lemma lem1704023 (x : real) : (term87 x) = term80.
Proof. exact (TRANS (@lem1704021 x) (@lem1704022)). Qed.
Lemma lem1704024 (n : real) (x : real) : (term75 n x) = term96.
Proof. exact (MK_COMB (@lem1704002 n x) (@lem1704023 x)). Qed.
Lemma lem1704025 (n : real) (x : real) : (term74 n x) = term96.
Proof. exact (TRANS (@lem1703989 n x) (@lem1704024 n x)). Qed.
Lemma lem1704026 : term96 = term80.
Proof. exact (@lem1483448 term80). Qed.
Lemma lem1704027 (n : real) (x : real) : (term74 n x) = term80.
Proof. exact (TRANS (@lem1704025 n x) (@lem1704026)). Qed.
Lemma lem1704028 (n : real) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (eq_refl (term34 n x)). Qed.
Lemma lem1704029 (n : real) (x : real) : (term73 n x) = (term97 n x).
Proof. exact (MK_COMB (@lem1704028 n x) (@lem1704027 n x)). Qed.
Lemma lem1704030 (n : real) (x : real) : (term72 n x) = (term97 n x).
Proof. exact (TRANS (@lem1703988 n x) (@lem1704029 n x)). Qed.
Lemma lem1704031 (n : real) (x : real) : (term97 n x) = (term32 n x).
Proof. exact (@lem1483450 (term32 n x)). Qed.
Lemma lem1704032 (n : real) (x : real) : (term72 n x) = (term32 n x).
Proof. exact (TRANS (@lem1704030 n x) (@lem1704031 n x)). Qed.
Lemma lem1704033 (n : real) (x : real) : (term57 n x) = (term32 n x).
Proof. exact (TRANS (@lem1703987 n x) (@lem1704032 n x)). Qed.
Lemma lem1704034 (n : real) (x : real) : (term56 n x) = (term32 n x).
Proof. exact (TRANS (@lem1703963 n x) (@lem1704033 n x)). Qed.
Lemma lem1704035 (n : real) (x : real) : (term55 n x) = (term32 n x).
Proof. exact (TRANS (@lem1703962 n x) (@lem1704034 n x)). Qed.
Lemma lem1704036 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704037 (n : real) (x : real) : (term98 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1704036) (@lem1704035 n x)). Qed.
Lemma lem1704038 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704039 (n : real) (x : real) : (term4 n x) = (term100 n x).
Proof. exact (MK_COMB (@lem1704037 n x) (@lem1704038)). Qed.
Lemma lem1704040 (n : real) (x : real) : (term2 n x) = (term100 n x).
Proof. exact (TRANS (@lem1703858 n x) (@lem1704039 n x)). Qed.
Lemma lem1704041 (n : real) (x : real) : (term101 n x) = (term102 n x).
Proof. exact (@lem1483533 term80 (term30 n x)). Qed.
Lemma lem1704048 (x : real) : (real_mul x x) = (term31 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1704051 (n : real) : (real_mul n) = (real_mul n).
Proof. exact (eq_refl (real_mul n)). Qed.
Lemma lem1704054 (n : real) (x : real) : (term30 n x) = (term32 n x).
Proof. exact (MK_COMB (@lem1704051 n) (@lem1704048 x)). Qed.
Lemma lem1704057 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem1704058 (n : real) (x : real) : (term104 n x) = (term105 n x).
Proof. exact (MK_COMB (@lem1704057) (@lem1704054 n x)). Qed.
Lemma lem1704059 (n : real) (x : real) : (term105 n x) = (term106 n x).
Proof. exact (@lem1483519 term80 (term32 n x)). Qed.
Lemma lem1704064 (n : real) (x : real) : (term106 n x) = (term107 n x).
Proof. exact (@lem1483448 (term107 n x)). Qed.
Lemma lem1704065 (n : real) (x : real) : (term105 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704059 n x) (@lem1704064 n x)). Qed.
Lemma lem1704066 (n : real) (x : real) : (term104 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704058 n x) (@lem1704065 n x)). Qed.
Lemma lem1704067 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704068 (n : real) (x : real) : (term108 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1704067) (@lem1704066 n x)). Qed.
Lemma lem1704069 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704070 (n : real) (x : real) : (term102 n x) = (term110 n x).
Proof. exact (MK_COMB (@lem1704068 n x) (@lem1704069)). Qed.
Lemma lem1704071 (n : real) (x : real) : (term101 n x) = (term110 n x).
Proof. exact (TRANS (@lem1704041 n x) (@lem1704070 n x)). Qed.
Lemma lem1704072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704073 (n : real) (x : real) : (term111 n x) = (term112 n x).
Proof. exact (MK_COMB (@lem1704072) (@lem1704040 n x)). Qed.
Lemma lem1704074 (n : real) (x : real) : (term113 n x) = (term114 n x).
Proof. exact (MK_COMB (@lem1704073 n x) (@lem1704071 n x)). Qed.
Lemma lem1704075 (n : real) (x : real) : (term115 n x) = (term116 n x).
Proof. exact (@lem1483533 (term6 n x) (term5 n x)). Qed.
Lemma lem1704088 (n : real) (x : real) : (term21 n x) = (term22 n x).
Proof. exact (@lem1483488 (real_mul n x) term11). Qed.
Lemma lem1704095 (x : real) : (term19 x) = (term9 x).
Proof. exact (@lem1483488 x term11). Qed.
Lemma lem1704096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704097 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1704096) (@lem1704095 x)). Qed.
Lemma lem1704098 (n : real) (x : real) : (term5 n x) = (term25 n x).
Proof. exact (MK_COMB (@lem1704097 x) (@lem1704088 n x)). Qed.
Lemma lem1704099 (n : real) (x : real) : (term25 n x) = (term26 n x).
Proof. exact (@lem1483454 x term11 (term22 n x)). Qed.
Lemma lem1704100 (n : real) (x : real) : (term27 n x) = (term28 n x).
Proof. exact (@lem1483508 (real_mul n x) x term11). Qed.
Lemma lem1704101 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1483474 term11 x). Qed.
Lemma lem1704102 (x : real) : (term13 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1704103 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem1704101 x) (@lem1704102 x)). Qed.
Lemma lem1704104 (n : real) (x : real) : (term29 n x) = (term30 n x).
Proof. exact (@lem1483478 n x x). Qed.
Lemma lem1704105 (x : real) : (real_mul x x) = (term31 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1704106 (n : real) : (real_mul n) = (real_mul n).
Proof. exact (eq_refl (real_mul n)). Qed.
Lemma lem1704107 (n : real) (x : real) : (term30 n x) = (term32 n x).
Proof. exact (MK_COMB (@lem1704106 n) (@lem1704105 x)). Qed.
Lemma lem1704108 (n : real) (x : real) : (term29 n x) = (term32 n x).
Proof. exact (TRANS (@lem1704104 n x) (@lem1704107 n x)). Qed.
Lemma lem1704109 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704110 (n : real) (x : real) : (term33 n x) = (term34 n x).
Proof. exact (MK_COMB (@lem1704109) (@lem1704108 n x)). Qed.
Lemma lem1704111 (n : real) (x : real) : (term28 n x) = (term35 n x).
Proof. exact (MK_COMB (@lem1704110 n x) (@lem1704103 x)). Qed.
Lemma lem1704112 (n : real) (x : real) : (term27 n x) = (term35 n x).
Proof. exact (TRANS (@lem1704100 n x) (@lem1704111 n x)). Qed.
Lemma lem1704113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704114 (n : real) (x : real) : (term36 n x) = (term37 n x).
Proof. exact (MK_COMB (@lem1704113) (@lem1704112 n x)). Qed.
Lemma lem1704115 (n : real) (x : real) : (term38 n x) = (term39 n x).
Proof. exact (@lem1483508 (real_mul n x) term11 term11). Qed.
Lemma lem1704117 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem1704118 : term42 = term43.
Proof. exact (@lem1704117 term44 term44). Qed.
Lemma lem1704119 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1704120 : term46 = term44.
Proof. exact (EQ_MP (@lem1704119) (@lem940073)). Qed.
Lemma lem1704121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1704122 : term43 = term11.
Proof. exact (MK_COMB (@lem1704121) (@lem1704120)). Qed.
Lemma lem1704123 : term42 = term11.
Proof. exact (TRANS (@lem1704118) (@lem1704122)). Qed.
Lemma lem1704126 (n : real) (x : real) : (term47 n x) = (real_mul n x).
Proof. exact (@lem1483436 (real_mul n x)). Qed.
Lemma lem1704127 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704128 (n : real) (x : real) : (term48 n x) = (term14 n x).
Proof. exact (MK_COMB (@lem1704127) (@lem1704126 n x)). Qed.
Lemma lem1704129 (n : real) (x : real) : (term39 n x) = (term22 n x).
Proof. exact (MK_COMB (@lem1704128 n x) (@lem1704123)). Qed.
Lemma lem1704130 (n : real) (x : real) : (term38 n x) = (term22 n x).
Proof. exact (TRANS (@lem1704115 n x) (@lem1704129 n x)). Qed.
Lemma lem1704131 (n : real) (x : real) : (term26 n x) = (term49 n x).
Proof. exact (MK_COMB (@lem1704114 n x) (@lem1704130 n x)). Qed.
Lemma lem1704132 (n : real) (x : real) : (term25 n x) = (term49 n x).
Proof. exact (TRANS (@lem1704099 n x) (@lem1704131 n x)). Qed.
Lemma lem1704133 (n : real) (x : real) : (term49 n x) = (term50 n x).
Proof. exact (@lem1483482 (term32 n x) x (term22 n x)). Qed.
Lemma lem1704138 (n : real) (x : real) : (term51 n x) = (term20 n x).
Proof. exact (@lem1483484 (real_mul n x) x term11). Qed.
Lemma lem1704139 (n : real) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (eq_refl (term34 n x)). Qed.
Lemma lem1704140 (n : real) (x : real) : (term50 n x) = (term52 n x).
Proof. exact (MK_COMB (@lem1704139 n x) (@lem1704138 n x)). Qed.
Lemma lem1704141 (n : real) (x : real) : (term49 n x) = (term52 n x).
Proof. exact (TRANS (@lem1704133 n x) (@lem1704140 n x)). Qed.
Lemma lem1704142 (n : real) (x : real) : (term25 n x) = (term52 n x).
Proof. exact (TRANS (@lem1704132 n x) (@lem1704141 n x)). Qed.
Lemma lem1704143 (n : real) (x : real) : (term5 n x) = (term52 n x).
Proof. exact (TRANS (@lem1704098 n x) (@lem1704142 n x)). Qed.
Lemma lem1704155 (x : real) (n : real) : (term7 n x) = (term8 x n).
Proof. exact (@lem1483452 x (term9 n)). Qed.
Lemma lem1704156 (n : real) (x : real) : (term8 x n) = (term10 n x).
Proof. exact (@lem1483508 n x term11). Qed.
Lemma lem1704157 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1483474 term11 x). Qed.
Lemma lem1704158 (x : real) : (term13 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1704159 (x : real) : (term12 x) = x.
Proof. exact (TRANS (@lem1704157 x) (@lem1704158 x)). Qed.
Lemma lem1704160 (n : real) (x : real) : (real_mul x n) = (real_mul n x).
Proof. exact (@lem1483474 n x). Qed.
Lemma lem1704161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704162 (n : real) (x : real) : (term14 x n) = (term14 n x).
Proof. exact (MK_COMB (@lem1704161) (@lem1704160 n x)). Qed.
Lemma lem1704163 (n : real) (x : real) : (term10 n x) = (term15 n x).
Proof. exact (MK_COMB (@lem1704162 n x) (@lem1704159 x)). Qed.
Lemma lem1704164 (n : real) (x : real) : (term8 x n) = (term15 n x).
Proof. exact (TRANS (@lem1704156 n x) (@lem1704163 n x)). Qed.
Lemma lem1704166 (n : real) (x : real) : (term7 n x) = (term15 n x).
Proof. exact (TRANS (@lem1704155 x n) (@lem1704164 n x)). Qed.
Lemma lem1704169 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1704170 (n : real) (x : real) : (term6 n x) = (term17 n x).
Proof. exact (MK_COMB (@lem1704169) (@lem1704166 n x)). Qed.
Lemma lem1704171 (n : real) (x : real) : (term17 n x) = (term18 n x).
Proof. exact (@lem1483484 (real_mul n x) term11 x). Qed.
Lemma lem1704172 (x : real) : (term19 x) = (term9 x).
Proof. exact (@lem1483488 x term11). Qed.
Lemma lem1704173 (n : real) (x : real) : (term14 n x) = (term14 n x).
Proof. exact (eq_refl (term14 n x)). Qed.
Lemma lem1704174 (n : real) (x : real) : (term18 n x) = (term20 n x).
Proof. exact (MK_COMB (@lem1704173 n x) (@lem1704172 x)). Qed.
Lemma lem1704175 (n : real) (x : real) : (term17 n x) = (term20 n x).
Proof. exact (TRANS (@lem1704171 n x) (@lem1704174 n x)). Qed.
Lemma lem1704176 (n : real) (x : real) : (term6 n x) = (term20 n x).
Proof. exact (TRANS (@lem1704170 n x) (@lem1704175 n x)). Qed.
Lemma lem1704177 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1704178 (n : real) (x : real) : (term117 n x) = (term118 n x).
Proof. exact (MK_COMB (@lem1704177) (@lem1704176 n x)). Qed.
Lemma lem1704179 (n : real) (x : real) : (term119 n x) = (term120 n x).
Proof. exact (MK_COMB (@lem1704178 n x) (@lem1704143 n x)). Qed.
Lemma lem1704180 (n : real) (x : real) : (term120 n x) = (term121 n x).
Proof. exact (@lem1483519 (term20 n x) (term52 n x)). Qed.
Lemma lem1704181 (n : real) (x : real) : (term122 n x) = (term123 n x).
Proof. exact (@lem1483508 (term32 n x) term60 (term20 n x)). Qed.
Lemma lem1704182 (n : real) (x : real) : (term58 n x) = (term59 n x).
Proof. exact (@lem1483508 (real_mul n x) term60 (term9 x)). Qed.
Lemma lem1704183 (x : real) : (term61 x) = (term62 x).
Proof. exact (@lem1483508 x term60 term11). Qed.
Lemma lem1704185 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1704186 : term65 = term66.
Proof. exact (@lem1704185 term44 term44). Qed.
Lemma lem1704187 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1704188 : term46 = term44.
Proof. exact (EQ_MP (@lem1704187) (@lem940073)). Qed.
Lemma lem1704189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1704190 : term43 = term11.
Proof. exact (MK_COMB (@lem1704189) (@lem1704188)). Qed.
Lemma lem1704191 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1704192 : term66 = term60.
Proof. exact (MK_COMB (@lem1704191) (@lem1704190)). Qed.
Lemma lem1704193 : term65 = term60.
Proof. exact (TRANS (@lem1704186) (@lem1704192)). Qed.
Lemma lem1704196 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1704197 (x : real) : (term62 x) = (term68 x).
Proof. exact (MK_COMB (@lem1704196 x) (@lem1704193)). Qed.
Lemma lem1704198 (x : real) : (term61 x) = (term68 x).
Proof. exact (TRANS (@lem1704183 x) (@lem1704197 x)). Qed.
Lemma lem1704201 (n : real) (x : real) : (term69 n x) = (term69 n x).
Proof. exact (eq_refl (term69 n x)). Qed.
Lemma lem1704202 (n : real) (x : real) : (term59 n x) = (term70 n x).
Proof. exact (MK_COMB (@lem1704201 n x) (@lem1704198 x)). Qed.
Lemma lem1704203 (n : real) (x : real) : (term58 n x) = (term70 n x).
Proof. exact (TRANS (@lem1704182 n x) (@lem1704202 n x)). Qed.
Lemma lem1704206 (n : real) (x : real) : (term124 n x) = (term124 n x).
Proof. exact (eq_refl (term124 n x)). Qed.
Lemma lem1704207 (n : real) (x : real) : (term123 n x) = (term125 n x).
Proof. exact (MK_COMB (@lem1704206 n x) (@lem1704203 n x)). Qed.
Lemma lem1704208 (n : real) (x : real) : (term122 n x) = (term125 n x).
Proof. exact (TRANS (@lem1704181 n x) (@lem1704207 n x)). Qed.
Lemma lem1704209 (n : real) (x : real) : (term126 n x) = (term126 n x).
Proof. exact (eq_refl (term126 n x)). Qed.
Lemma lem1704210 (n : real) (x : real) : (term121 n x) = (term127 n x).
Proof. exact (MK_COMB (@lem1704209 n x) (@lem1704208 n x)). Qed.
Lemma lem1704211 (n : real) (x : real) : (term127 n x) = (term128 n x).
Proof. exact (@lem1483484 (term107 n x) (term20 n x) (term70 n x)). Qed.
Lemma lem1704212 (n : real) (x : real) : (term74 n x) = (term75 n x).
Proof. exact (@lem1483480 (real_mul n x) (term76 n x) (term9 x) (term68 x)). Qed.
Lemma lem1704213 (n : real) (x : real) : (term77 n x) = (term78 n x).
Proof. exact (@lem1483442 term60 (real_mul n x)). Qed.
Lemma lem1704215 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704216 : term81 = term80.
Proof. exact (@lem1704215 term44). Qed.
Lemma lem1704217 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704218 : term82 = term83.
Proof. exact (MK_COMB (@lem1704217) (@lem1704216)). Qed.
Lemma lem1704219 (n : real) (x : real) : (real_mul n x) = (real_mul n x).
Proof. exact (eq_refl (real_mul n x)). Qed.
Lemma lem1704220 (n : real) (x : real) : (term78 n x) = (term84 n x).
Proof. exact (MK_COMB (@lem1704218) (@lem1704219 n x)). Qed.
Lemma lem1704221 (n : real) (x : real) : (term77 n x) = (term84 n x).
Proof. exact (TRANS (@lem1704213 n x) (@lem1704220 n x)). Qed.
Lemma lem1704222 (n : real) (x : real) : (term84 n x) = term80.
Proof. exact (@lem1483446 (real_mul n x)). Qed.
Lemma lem1704223 (n : real) (x : real) : (term77 n x) = term80.
Proof. exact (TRANS (@lem1704221 n x) (@lem1704222 n x)). Qed.
Lemma lem1704224 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704225 (n : real) (x : real) : (term85 n x) = term86.
Proof. exact (MK_COMB (@lem1704224) (@lem1704223 n x)). Qed.
Lemma lem1704226 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483480 x (term89 x) term11 term60). Qed.
Lemma lem1704227 (x : real) : (term90 x) = (term91 x).
Proof. exact (@lem1483442 term60 x). Qed.
Lemma lem1704229 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704230 : term81 = term80.
Proof. exact (@lem1704229 term44). Qed.
Lemma lem1704231 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704232 : term82 = term83.
Proof. exact (MK_COMB (@lem1704231) (@lem1704230)). Qed.
Lemma lem1704233 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1704234 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1704232) (@lem1704233 x)). Qed.
Lemma lem1704235 (x : real) : (term90 x) = (term92 x).
Proof. exact (TRANS (@lem1704227 x) (@lem1704234 x)). Qed.
Lemma lem1704236 (x : real) : (term92 x) = term80.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1704237 (x : real) : (term90 x) = term80.
Proof. exact (TRANS (@lem1704235 x) (@lem1704236 x)). Qed.
Lemma lem1704238 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704239 (x : real) : (term93 x) = term86.
Proof. exact (MK_COMB (@lem1704238) (@lem1704237 x)). Qed.
Lemma lem1704241 (m : nat) : (term94 m) = term80.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1704242 : term95 = term80.
Proof. exact (@lem1704241 term44). Qed.
Lemma lem1704243 (x : real) : (term88 x) = term96.
Proof. exact (MK_COMB (@lem1704239 x) (@lem1704242)). Qed.
Lemma lem1704244 (x : real) : (term87 x) = term96.
Proof. exact (TRANS (@lem1704226 x) (@lem1704243 x)). Qed.
Lemma lem1704245 : term96 = term80.
Proof. exact (@lem1483448 term80). Qed.
Lemma lem1704246 (x : real) : (term87 x) = term80.
Proof. exact (TRANS (@lem1704244 x) (@lem1704245)). Qed.
Lemma lem1704247 (n : real) (x : real) : (term75 n x) = term96.
Proof. exact (MK_COMB (@lem1704225 n x) (@lem1704246 x)). Qed.
Lemma lem1704248 (n : real) (x : real) : (term74 n x) = term96.
Proof. exact (TRANS (@lem1704212 n x) (@lem1704247 n x)). Qed.
Lemma lem1704249 : term96 = term80.
Proof. exact (@lem1483448 term80). Qed.
Lemma lem1704250 (n : real) (x : real) : (term74 n x) = term80.
Proof. exact (TRANS (@lem1704248 n x) (@lem1704249)). Qed.
Lemma lem1704251 (n : real) (x : real) : (term124 n x) = (term124 n x).
Proof. exact (eq_refl (term124 n x)). Qed.
Lemma lem1704252 (n : real) (x : real) : (term128 n x) = (term129 n x).
Proof. exact (MK_COMB (@lem1704251 n x) (@lem1704250 n x)). Qed.
Lemma lem1704253 (n : real) (x : real) : (term127 n x) = (term129 n x).
Proof. exact (TRANS (@lem1704211 n x) (@lem1704252 n x)). Qed.
Lemma lem1704254 (n : real) (x : real) : (term129 n x) = (term107 n x).
Proof. exact (@lem1483450 (term107 n x)). Qed.
Lemma lem1704255 (n : real) (x : real) : (term127 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704253 n x) (@lem1704254 n x)). Qed.
Lemma lem1704256 (n : real) (x : real) : (term121 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704210 n x) (@lem1704255 n x)). Qed.
Lemma lem1704257 (n : real) (x : real) : (term120 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704180 n x) (@lem1704256 n x)). Qed.
Lemma lem1704258 (n : real) (x : real) : (term119 n x) = (term107 n x).
Proof. exact (TRANS (@lem1704179 n x) (@lem1704257 n x)). Qed.
Lemma lem1704259 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704260 (n : real) (x : real) : (term130 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1704259) (@lem1704258 n x)). Qed.
Lemma lem1704261 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704262 (n : real) (x : real) : (term116 n x) = (term110 n x).
Proof. exact (MK_COMB (@lem1704260 n x) (@lem1704261)). Qed.
Lemma lem1704263 (n : real) (x : real) : (term115 n x) = (term110 n x).
Proof. exact (TRANS (@lem1704075 n x) (@lem1704262 n x)). Qed.
Lemma lem1704264 (n : real) (x : real) : (term3 n x) = (term131 n x).
Proof. exact (@lem1483523 (term30 n x) term80). Qed.
Lemma lem1704265 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704272 (x : real) : (real_mul x x) = (term31 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1704275 (n : real) : (real_mul n) = (real_mul n).
Proof. exact (eq_refl (real_mul n)). Qed.
Lemma lem1704278 (n : real) (x : real) : (term30 n x) = (term32 n x).
Proof. exact (MK_COMB (@lem1704275 n) (@lem1704272 x)). Qed.
Lemma lem1704279 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1704280 (n : real) (x : real) : (term132 n x) = (term133 n x).
Proof. exact (MK_COMB (@lem1704279) (@lem1704278 n x)). Qed.
Lemma lem1704281 (n : real) (x : real) : (term134 n x) = (term135 n x).
Proof. exact (MK_COMB (@lem1704280 n x) (@lem1704265)). Qed.
Lemma lem1704282 (n : real) (x : real) : (term135 n x) = (term136 n x).
Proof. exact (@lem1483519 (term32 n x) term80). Qed.
Lemma lem1704284 (x : nat) : (term137 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1704285 : term138 = term80.
Proof. exact (@lem1704284 term44). Qed.
Lemma lem1704286 (n : real) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (eq_refl (term34 n x)). Qed.
Lemma lem1704287 (n : real) (x : real) : (term136 n x) = (term97 n x).
Proof. exact (MK_COMB (@lem1704286 n x) (@lem1704285)). Qed.
Lemma lem1704288 (n : real) (x : real) : (term97 n x) = (term32 n x).
Proof. exact (@lem1483450 (term32 n x)). Qed.
Lemma lem1704289 (n : real) (x : real) : (term136 n x) = (term32 n x).
Proof. exact (TRANS (@lem1704287 n x) (@lem1704288 n x)). Qed.
Lemma lem1704290 (n : real) (x : real) : (term135 n x) = (term32 n x).
Proof. exact (TRANS (@lem1704282 n x) (@lem1704289 n x)). Qed.
Lemma lem1704291 (n : real) (x : real) : (term134 n x) = (term32 n x).
Proof. exact (TRANS (@lem1704281 n x) (@lem1704290 n x)). Qed.
Lemma lem1704292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704293 (n : real) (x : real) : (term139 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1704292) (@lem1704291 n x)). Qed.
Lemma lem1704294 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704295 (n : real) (x : real) : (term131 n x) = (term100 n x).
Proof. exact (MK_COMB (@lem1704293 n x) (@lem1704294)). Qed.
Lemma lem1704296 (n : real) (x : real) : (term3 n x) = (term100 n x).
Proof. exact (TRANS (@lem1704264 n x) (@lem1704295 n x)). Qed.
Lemma lem1704297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704298 (n : real) (x : real) : (term140 n x) = (term141 n x).
Proof. exact (MK_COMB (@lem1704297) (@lem1704263 n x)). Qed.
Lemma lem1704299 (n : real) (x : real) : (term142 n x) = (term143 n x).
Proof. exact (MK_COMB (@lem1704298 n x) (@lem1704296 n x)). Qed.
Lemma lem1704300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1704301 (n : real) (x : real) : (term144 n x) = (term145 n x).
Proof. exact (MK_COMB (@lem1704300) (@lem1704074 n x)). Qed.
Lemma lem1704302 (n : real) (x : real) : (term1 n x) = (term146 n x).
Proof. exact (MK_COMB (@lem1704301 n x) (@lem1704299 n x)). Qed.
Lemma lem1704327 (n : real) (x : real) : (term0 n x) = (term146 n x).
Proof. exact (TRANS (@lem1703857 n x) (@lem1704302 n x)). Qed.
Lemma lem1704337 (n : real) (x : real) (h1 : term146 n x) : term146 n x.
Proof. exact (h1). Qed.
Lemma lem1704338 (n : real) (x : real) (h1 : term114 n x) : term114 n x.
Proof. exact (h1). Qed.
Lemma lem1704339 (n : real) (x : real) (h1 : term114 n x) : term110 n x.
Proof. exact (proj2 (@lem1704338 n x h1)). Qed.
Lemma lem1704340 (n : real) (x : real) (h1 : term114 n x) : term100 n x.
Proof. exact (proj1 (@lem1704338 n x h1)). Qed.
Lemma lem1704342 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704343 : term148 = term149.
Proof. exact (@lem1704342 (NUMERAL 0) term44). Qed.
Lemma lem1704344 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704345 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704346 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704345 h1) (fun h1 : term149 = True => @lem1704344)). Qed.
Lemma lem1704347 : term149 = True.
Proof. exact (EQ_MP (@lem1704346) (@lem1704344)). Qed.
Lemma lem1704348 : term148 = True.
Proof. exact (TRANS (@lem1704343) (@lem1704347)). Qed.
Lemma lem1704349 : True = term148.
Proof. exact (SYM (@lem1704348)). Qed.
Lemma lem1704350 : term148.
Proof. exact (EQ_MP (@lem1704349) (@lem0)). Qed.
Lemma lem1704351 (n : real) (x : real) (h1 : term114 n x) : term151 n x.
Proof. exact (conj (@lem1704350) (@lem1704340 n x h1)). Qed.
Lemma lem1704353 (x : real) (y : real) : term152 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1704354 (n : real) (x : real) : term153 n x.
Proof. exact (@lem1704353 term11 (term32 n x)). Qed.
Lemma lem1704355 (n : real) (x : real) (h1 : term114 n x) : term154 n x.
Proof. exact (@lem1704354 n x (@lem1704351 n x h1)). Qed.
Lemma lem1704356 (n : real) (x : real) : (term155 n x) = (term32 n x).
Proof. exact (@lem1483460 (term32 n x)). Qed.
Lemma lem1704357 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704358 (n : real) (x : real) : (term156 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1704357) (@lem1704356 n x)). Qed.
Lemma lem1704359 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704360 (n : real) (x : real) : (term154 n x) = (term100 n x).
Proof. exact (MK_COMB (@lem1704358 n x) (@lem1704359)). Qed.
Lemma lem1704361 (n : real) (x : real) (h1 : term114 n x) : term100 n x.
Proof. exact (EQ_MP (@lem1704360 n x) (@lem1704355 n x h1)). Qed.
Lemma lem1704363 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704364 : term148 = term149.
Proof. exact (@lem1704363 (NUMERAL 0) term44). Qed.
Lemma lem1704365 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704366 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704367 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704366 h1) (fun h1 : term149 = True => @lem1704365)). Qed.
Lemma lem1704368 : term149 = True.
Proof. exact (EQ_MP (@lem1704367) (@lem1704365)). Qed.
Lemma lem1704369 : term148 = True.
Proof. exact (TRANS (@lem1704364) (@lem1704368)). Qed.
Lemma lem1704370 : True = term148.
Proof. exact (SYM (@lem1704369)). Qed.
Lemma lem1704371 : term148.
Proof. exact (EQ_MP (@lem1704370) (@lem0)). Qed.
Lemma lem1704372 (n : real) (x : real) (h1 : term114 n x) : term157 n x.
Proof. exact (conj (@lem1704371) (@lem1704339 n x h1)). Qed.
Lemma lem1704374 (x : real) (y : real) : term158 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1704375 (n : real) (x : real) : term159 n x.
Proof. exact (@lem1704374 term11 (term107 n x)). Qed.
Lemma lem1704376 (n : real) (x : real) (h1 : term114 n x) : term160 n x.
Proof. exact (@lem1704375 n x (@lem1704372 n x h1)). Qed.
Lemma lem1704377 (n : real) (x : real) : (term161 n x) = (term107 n x).
Proof. exact (@lem1483460 (term107 n x)). Qed.
Lemma lem1704378 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704379 (n : real) (x : real) : (term162 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1704378) (@lem1704377 n x)). Qed.
Lemma lem1704380 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704381 (n : real) (x : real) : (term160 n x) = (term110 n x).
Proof. exact (MK_COMB (@lem1704379 n x) (@lem1704380)). Qed.
Lemma lem1704382 (n : real) (x : real) (h1 : term114 n x) : term110 n x.
Proof. exact (EQ_MP (@lem1704381 n x) (@lem1704376 n x h1)). Qed.
Lemma lem1704383 (n : real) (x : real) (h1 : term114 n x) : term143 n x.
Proof. exact (conj (@lem1704382 n x h1) (@lem1704361 n x h1)). Qed.
Lemma lem1704385 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1704386 (n : real) (x : real) : term164 n x.
Proof. exact (@lem1704385 (term107 n x) (term32 n x)). Qed.
Lemma lem1704387 (n : real) (x : real) (h1 : term114 n x) : term165 n x.
Proof. exact (@lem1704386 n x (@lem1704383 n x h1)). Qed.
Lemma lem1704388 (n : real) (x : real) : (term166 n x) = (term167 n x).
Proof. exact (@lem1483440 term60 (term32 n x)). Qed.
Lemma lem1704390 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704391 : term81 = term80.
Proof. exact (@lem1704390 term44). Qed.
Lemma lem1704392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704393 : term82 = term83.
Proof. exact (MK_COMB (@lem1704392) (@lem1704391)). Qed.
Lemma lem1704394 (n : real) (x : real) : (term32 n x) = (term32 n x).
Proof. exact (eq_refl (term32 n x)). Qed.
Lemma lem1704395 (n : real) (x : real) : (term167 n x) = (term168 n x).
Proof. exact (MK_COMB (@lem1704393) (@lem1704394 n x)). Qed.
Lemma lem1704396 (n : real) (x : real) : (term166 n x) = (term168 n x).
Proof. exact (TRANS (@lem1704388 n x) (@lem1704395 n x)). Qed.
Lemma lem1704397 (n : real) (x : real) : (term168 n x) = term80.
Proof. exact (@lem1483446 (term32 n x)). Qed.
Lemma lem1704398 (n : real) (x : real) : (term166 n x) = term80.
Proof. exact (TRANS (@lem1704396 n x) (@lem1704397 n x)). Qed.
Lemma lem1704399 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704400 (n : real) (x : real) : (term169 n x) = term170.
Proof. exact (MK_COMB (@lem1704399) (@lem1704398 n x)). Qed.
Lemma lem1704401 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704402 (n : real) (x : real) : (term165 n x) = term171.
Proof. exact (MK_COMB (@lem1704400 n x) (@lem1704401)). Qed.
Lemma lem1704403 (n : real) (x : real) (h1 : term114 n x) : term171.
Proof. exact (EQ_MP (@lem1704402 n x) (@lem1704387 n x h1)). Qed.
Lemma lem1704405 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704406 : term171 = term172.
Proof. exact (@lem1704405 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1704407 : term172 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1704408 : term171 = False.
Proof. exact (TRANS (@lem1704406) (@lem1704407)). Qed.
Lemma lem1704409 (n : real) (x : real) (h1 : term114 n x) : False.
Proof. exact (EQ_MP (@lem1704408) (@lem1704403 n x h1)). Qed.
Lemma lem1704410 (n : real) (x : real) (h1 : term143 n x) : term143 n x.
Proof. exact (h1). Qed.
Lemma lem1704411 (n : real) (x : real) (h1 : term143 n x) : term100 n x.
Proof. exact (proj2 (@lem1704410 n x h1)). Qed.
Lemma lem1704412 (n : real) (x : real) (h1 : term143 n x) : term110 n x.
Proof. exact (proj1 (@lem1704410 n x h1)). Qed.
Lemma lem1704414 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704415 : term148 = term149.
Proof. exact (@lem1704414 (NUMERAL 0) term44). Qed.
Lemma lem1704416 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704417 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704418 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704417 h1) (fun h1 : term149 = True => @lem1704416)). Qed.
Lemma lem1704419 : term149 = True.
Proof. exact (EQ_MP (@lem1704418) (@lem1704416)). Qed.
Lemma lem1704420 : term148 = True.
Proof. exact (TRANS (@lem1704415) (@lem1704419)). Qed.
Lemma lem1704421 : True = term148.
Proof. exact (SYM (@lem1704420)). Qed.
Lemma lem1704422 : term148.
Proof. exact (EQ_MP (@lem1704421) (@lem0)). Qed.
Lemma lem1704423 (n : real) (x : real) (h1 : term143 n x) : term151 n x.
Proof. exact (conj (@lem1704422) (@lem1704411 n x h1)). Qed.
Lemma lem1704425 (x : real) (y : real) : term152 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1704426 (n : real) (x : real) : term153 n x.
Proof. exact (@lem1704425 term11 (term32 n x)). Qed.
Lemma lem1704427 (n : real) (x : real) (h1 : term143 n x) : term154 n x.
Proof. exact (@lem1704426 n x (@lem1704423 n x h1)). Qed.
Lemma lem1704428 (n : real) (x : real) : (term155 n x) = (term32 n x).
Proof. exact (@lem1483460 (term32 n x)). Qed.
Lemma lem1704429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704430 (n : real) (x : real) : (term156 n x) = (term99 n x).
Proof. exact (MK_COMB (@lem1704429) (@lem1704428 n x)). Qed.
Lemma lem1704431 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704432 (n : real) (x : real) : (term154 n x) = (term100 n x).
Proof. exact (MK_COMB (@lem1704430 n x) (@lem1704431)). Qed.
Lemma lem1704433 (n : real) (x : real) (h1 : term143 n x) : term100 n x.
Proof. exact (EQ_MP (@lem1704432 n x) (@lem1704427 n x h1)). Qed.
Lemma lem1704435 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704436 : term148 = term149.
Proof. exact (@lem1704435 (NUMERAL 0) term44). Qed.
Lemma lem1704437 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704438 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704439 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704438 h1) (fun h1 : term149 = True => @lem1704437)). Qed.
Lemma lem1704440 : term149 = True.
Proof. exact (EQ_MP (@lem1704439) (@lem1704437)). Qed.
Lemma lem1704441 : term148 = True.
Proof. exact (TRANS (@lem1704436) (@lem1704440)). Qed.
Lemma lem1704442 : True = term148.
Proof. exact (SYM (@lem1704441)). Qed.
Lemma lem1704443 : term148.
Proof. exact (EQ_MP (@lem1704442) (@lem0)). Qed.
Lemma lem1704444 (n : real) (x : real) (h1 : term143 n x) : term157 n x.
Proof. exact (conj (@lem1704443) (@lem1704412 n x h1)). Qed.
Lemma lem1704446 (x : real) (y : real) : term158 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1704447 (n : real) (x : real) : term159 n x.
Proof. exact (@lem1704446 term11 (term107 n x)). Qed.
Lemma lem1704448 (n : real) (x : real) (h1 : term143 n x) : term160 n x.
Proof. exact (@lem1704447 n x (@lem1704444 n x h1)). Qed.
Lemma lem1704449 (n : real) (x : real) : (term161 n x) = (term107 n x).
Proof. exact (@lem1483460 (term107 n x)). Qed.
Lemma lem1704450 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704451 (n : real) (x : real) : (term162 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1704450) (@lem1704449 n x)). Qed.
Lemma lem1704452 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704453 (n : real) (x : real) : (term160 n x) = (term110 n x).
Proof. exact (MK_COMB (@lem1704451 n x) (@lem1704452)). Qed.
Lemma lem1704454 (n : real) (x : real) (h1 : term143 n x) : term110 n x.
Proof. exact (EQ_MP (@lem1704453 n x) (@lem1704448 n x h1)). Qed.
Lemma lem1704455 (n : real) (x : real) (h1 : term143 n x) : term143 n x.
Proof. exact (conj (@lem1704454 n x h1) (@lem1704433 n x h1)). Qed.
Lemma lem1704457 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1704458 (n : real) (x : real) : term164 n x.
Proof. exact (@lem1704457 (term107 n x) (term32 n x)). Qed.
Lemma lem1704459 (n : real) (x : real) (h1 : term143 n x) : term165 n x.
Proof. exact (@lem1704458 n x (@lem1704455 n x h1)). Qed.
Lemma lem1704460 (n : real) (x : real) : (term166 n x) = (term167 n x).
Proof. exact (@lem1483440 term60 (term32 n x)). Qed.
Lemma lem1704462 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704463 : term81 = term80.
Proof. exact (@lem1704462 term44). Qed.
Lemma lem1704464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704465 : term82 = term83.
Proof. exact (MK_COMB (@lem1704464) (@lem1704463)). Qed.
Lemma lem1704466 (n : real) (x : real) : (term32 n x) = (term32 n x).
Proof. exact (eq_refl (term32 n x)). Qed.
Lemma lem1704467 (n : real) (x : real) : (term167 n x) = (term168 n x).
Proof. exact (MK_COMB (@lem1704465) (@lem1704466 n x)). Qed.
Lemma lem1704468 (n : real) (x : real) : (term166 n x) = (term168 n x).
Proof. exact (TRANS (@lem1704460 n x) (@lem1704467 n x)). Qed.
Lemma lem1704469 (n : real) (x : real) : (term168 n x) = term80.
Proof. exact (@lem1483446 (term32 n x)). Qed.
Lemma lem1704470 (n : real) (x : real) : (term166 n x) = term80.
Proof. exact (TRANS (@lem1704468 n x) (@lem1704469 n x)). Qed.
Lemma lem1704471 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704472 (n : real) (x : real) : (term169 n x) = term170.
Proof. exact (MK_COMB (@lem1704471) (@lem1704470 n x)). Qed.
Lemma lem1704473 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704474 (n : real) (x : real) : (term165 n x) = term171.
Proof. exact (MK_COMB (@lem1704472 n x) (@lem1704473)). Qed.
Lemma lem1704475 (n : real) (x : real) (h1 : term143 n x) : term171.
Proof. exact (EQ_MP (@lem1704474 n x) (@lem1704459 n x h1)). Qed.
Lemma lem1704477 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704478 : term171 = term172.
Proof. exact (@lem1704477 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1704479 : term172 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1704480 : term171 = False.
Proof. exact (TRANS (@lem1704478) (@lem1704479)). Qed.
Lemma lem1704481 (n : real) (x : real) (h1 : term143 n x) : False.
Proof. exact (EQ_MP (@lem1704480) (@lem1704475 n x h1)). Qed.
Lemma lem1704482 (n : real) (x : real) (h1 : term146 n x) : False.
Proof. exact (or_elim (@lem1704337 n x h1) (fun h0 : term114 n x => @lem1704409 n x h0) (fun h0 : term143 n x => @lem1704481 n x h0)). Qed.
Lemma lem1704484 (n : real) (x : real) (h1 : term146 n x) : term146 n x.
Proof. exact (h1). Qed.
Lemma lem1704485 (n : real) (x : real) (h1 : term146 n x) : (term146 n x) = False.
Proof. exact (prop_ext (fun h2 : term146 n x => @lem1704482 n x h1) (fun h2 : False => @lem1704484 n x h1)). Qed.
Lemma lem1704486 (n : real) (x : real) (h1 : term146 n x) : False.
Proof. exact (EQ_MP (@lem1704485 n x h1) (@lem1704484 n x h1)). Qed.
Lemma lem1704487 (n : real) (x : real) (h1 : term0 n x) : term0 n x.
Proof. exact (h1). Qed.
Lemma lem1704488 (n : real) (x : real) (h1 : term0 n x) : term146 n x.
Proof. exact (EQ_MP (@lem1704327 n x) (@lem1704487 n x h1)). Qed.
Lemma lem1704489 (n : real) (x : real) (h1 : term0 n x) : (term146 n x) = False.
Proof. exact (prop_ext (fun h2 : term146 n x => @lem1704486 n x h2) (fun h2 : False => @lem1704488 n x h1)). Qed.
Lemma lem1704490 (n : real) (x : real) (h1 : term0 n x) : False.
Proof. exact (EQ_MP (@lem1704489 n x h1) (@lem1704488 n x h1)). Qed.
Lemma lem1704491 (n : real) (x : real) : term173 n x.
Proof. exact (fun h0 : term0 n x => @lem1704490 n x h0). Qed.
Lemma lem1704492 (n : real) (x : real) : term174 n x.
Proof. exact (@lem1386578 ((term2 n x) = (term3 n x))). Qed.
Lemma lem1704514 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem17362 (term177 x) (term178 x)). Qed.
Lemma lem1704515 (x : real) : (term177 x) = (term179 x).
Proof. exact (@lem1483523 x term80). Qed.
Lemma lem1704521 (x : real) : (term180 x) = (term181 x).
Proof. exact (@lem1483519 x term80). Qed.
Lemma lem1704523 (x : nat) : (term137 x) = term80.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1704524 : term138 = term80.
Proof. exact (@lem1704523 term44). Qed.
Lemma lem1704525 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1704526 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1704525 x) (@lem1704524)). Qed.
Lemma lem1704527 (x : real) : (term182 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1704528 (x : real) : (term181 x) = x.
Proof. exact (TRANS (@lem1704526 x) (@lem1704527 x)). Qed.
Lemma lem1704530 (x : real) : (term180 x) = x.
Proof. exact (TRANS (@lem1704521 x) (@lem1704528 x)). Qed.
Lemma lem1704531 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704532 (x : real) : (term183 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1704531) (@lem1704530 x)). Qed.
Lemma lem1704533 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704534 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1704532 x) (@lem1704533)). Qed.
Lemma lem1704535 (x : real) : (term177 x) = (term184 x).
Proof. exact (TRANS (@lem1704515 x) (@lem1704534 x)). Qed.
Lemma lem1704536 (x : real) : (term185 x) = (term186 x).
Proof. exact (@lem1483533 term80 (term19 x)). Qed.
Lemma lem1704543 (x : real) : (term19 x) = (term9 x).
Proof. exact (@lem1483488 x term11). Qed.
Lemma lem1704546 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem1704547 (x : real) : (term187 x) = (term188 x).
Proof. exact (MK_COMB (@lem1704546) (@lem1704543 x)). Qed.
Lemma lem1704548 (x : real) : (term188 x) = (term189 x).
Proof. exact (@lem1483519 term80 (term9 x)). Qed.
Lemma lem1704549 (x : real) : (term61 x) = (term62 x).
Proof. exact (@lem1483508 x term60 term11). Qed.
Lemma lem1704551 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1704552 : term65 = term66.
Proof. exact (@lem1704551 term44 term44). Qed.
Lemma lem1704553 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1704554 : term46 = term44.
Proof. exact (EQ_MP (@lem1704553) (@lem940073)). Qed.
Lemma lem1704555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1704556 : term43 = term11.
Proof. exact (MK_COMB (@lem1704555) (@lem1704554)). Qed.
Lemma lem1704557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1704558 : term66 = term60.
Proof. exact (MK_COMB (@lem1704557) (@lem1704556)). Qed.
Lemma lem1704559 : term65 = term60.
Proof. exact (TRANS (@lem1704552) (@lem1704558)). Qed.
Lemma lem1704562 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1704563 (x : real) : (term62 x) = (term68 x).
Proof. exact (MK_COMB (@lem1704562 x) (@lem1704559)). Qed.
Lemma lem1704564 (x : real) : (term61 x) = (term68 x).
Proof. exact (TRANS (@lem1704549 x) (@lem1704563 x)). Qed.
Lemma lem1704565 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem1704566 (x : real) : (term189 x) = (term190 x).
Proof. exact (MK_COMB (@lem1704565) (@lem1704564 x)). Qed.
Lemma lem1704567 (x : real) : (term190 x) = (term68 x).
Proof. exact (@lem1483448 (term68 x)). Qed.
Lemma lem1704568 (x : real) : (term189 x) = (term68 x).
Proof. exact (TRANS (@lem1704566 x) (@lem1704567 x)). Qed.
Lemma lem1704569 (x : real) : (term188 x) = (term68 x).
Proof. exact (TRANS (@lem1704548 x) (@lem1704568 x)). Qed.
Lemma lem1704570 (x : real) : (term187 x) = (term68 x).
Proof. exact (TRANS (@lem1704547 x) (@lem1704569 x)). Qed.
Lemma lem1704571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704572 (x : real) : (term191 x) = (term192 x).
Proof. exact (MK_COMB (@lem1704571) (@lem1704570 x)). Qed.
Lemma lem1704573 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704574 (x : real) : (term186 x) = (term193 x).
Proof. exact (MK_COMB (@lem1704572 x) (@lem1704573)). Qed.
Lemma lem1704575 (x : real) : (term185 x) = (term193 x).
Proof. exact (TRANS (@lem1704536 x) (@lem1704574 x)). Qed.
Lemma lem1704576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704577 (x : real) : (term194 x) = (term195 x).
Proof. exact (MK_COMB (@lem1704576) (@lem1704535 x)). Qed.
Lemma lem1704578 (x : real) : (term176 x) = (term196 x).
Proof. exact (MK_COMB (@lem1704577 x) (@lem1704575 x)). Qed.
Lemma lem1704593 (x : real) : (term175 x) = (term196 x).
Proof. exact (TRANS (@lem1704514 x) (@lem1704578 x)). Qed.
Lemma lem1704597 (x : real) (h1 : term196 x) : term196 x.
Proof. exact (h1). Qed.
Lemma lem1704598 (x : real) (h1 : term196 x) : term193 x.
Proof. exact (proj2 (@lem1704597 x h1)). Qed.
Lemma lem1704599 (x : real) (h1 : term196 x) : term184 x.
Proof. exact (proj1 (@lem1704597 x h1)). Qed.
Lemma lem1704601 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704602 : term148 = term149.
Proof. exact (@lem1704601 (NUMERAL 0) term44). Qed.
Lemma lem1704603 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704604 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704605 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704604 h1) (fun h1 : term149 = True => @lem1704603)). Qed.
Lemma lem1704606 : term149 = True.
Proof. exact (EQ_MP (@lem1704605) (@lem1704603)). Qed.
Lemma lem1704607 : term148 = True.
Proof. exact (TRANS (@lem1704602) (@lem1704606)). Qed.
Lemma lem1704608 : True = term148.
Proof. exact (SYM (@lem1704607)). Qed.
Lemma lem1704609 : term148.
Proof. exact (EQ_MP (@lem1704608) (@lem0)). Qed.
Lemma lem1704610 (x : real) (h1 : term196 x) : term197 x.
Proof. exact (conj (@lem1704609) (@lem1704599 x h1)). Qed.
Lemma lem1704612 (x : real) (y : real) : term152 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1704613 (x : real) : term198 x.
Proof. exact (@lem1704612 term11 x). Qed.
Lemma lem1704614 (x : real) (h1 : term196 x) : term199 x.
Proof. exact (@lem1704613 x (@lem1704610 x h1)). Qed.
Lemma lem1704615 (x : real) : (term13 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1704616 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1704617 (x : real) : (term200 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1704616) (@lem1704615 x)). Qed.
Lemma lem1704618 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704619 (x : real) : (term199 x) = (term184 x).
Proof. exact (MK_COMB (@lem1704617 x) (@lem1704618)). Qed.
Lemma lem1704620 (x : real) (h1 : term196 x) : term184 x.
Proof. exact (EQ_MP (@lem1704619 x) (@lem1704614 x h1)). Qed.
Lemma lem1704622 (n : nat) (m : nat) : (term147 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1704623 : term148 = term149.
Proof. exact (@lem1704622 (NUMERAL 0) term44). Qed.
Lemma lem1704624 : term150 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1704625 (h1 : term150 = (BIT1 0)) : term149 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1704626 : (term150 = (BIT1 0)) = (term149 = True).
Proof. exact (prop_ext (fun h1 : term150 = (BIT1 0) => @lem1704625 h1) (fun h1 : term149 = True => @lem1704624)). Qed.
Lemma lem1704627 : term149 = True.
Proof. exact (EQ_MP (@lem1704626) (@lem1704624)). Qed.
Lemma lem1704628 : term148 = True.
Proof. exact (TRANS (@lem1704623) (@lem1704627)). Qed.
Lemma lem1704629 : True = term148.
Proof. exact (SYM (@lem1704628)). Qed.
Lemma lem1704630 : term148.
Proof. exact (EQ_MP (@lem1704629) (@lem0)). Qed.
Lemma lem1704631 (x : real) (h1 : term196 x) : term201 x.
Proof. exact (conj (@lem1704630) (@lem1704598 x h1)). Qed.
Lemma lem1704633 (x : real) (y : real) : term158 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1704634 (x : real) : term202 x.
Proof. exact (@lem1704633 term11 (term68 x)). Qed.
Lemma lem1704635 (x : real) (h1 : term196 x) : term203 x.
Proof. exact (@lem1704634 x (@lem1704631 x h1)). Qed.
Lemma lem1704636 (x : real) : (term204 x) = (term68 x).
Proof. exact (@lem1483460 (term68 x)). Qed.
Lemma lem1704637 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704638 (x : real) : (term205 x) = (term192 x).
Proof. exact (MK_COMB (@lem1704637) (@lem1704636 x)). Qed.
Lemma lem1704639 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704640 (x : real) : (term203 x) = (term193 x).
Proof. exact (MK_COMB (@lem1704638 x) (@lem1704639)). Qed.
Lemma lem1704641 (x : real) (h1 : term196 x) : term193 x.
Proof. exact (EQ_MP (@lem1704640 x) (@lem1704635 x h1)). Qed.
Lemma lem1704642 (x : real) (h1 : term196 x) : term206 x.
Proof. exact (conj (@lem1704641 x h1) (@lem1704620 x h1)). Qed.
Lemma lem1704644 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1704645 (x : real) : term207 x.
Proof. exact (@lem1704644 (term68 x) x). Qed.
Lemma lem1704646 (x : real) (h1 : term196 x) : term208 x.
Proof. exact (@lem1704645 x (@lem1704642 x h1)). Qed.
Lemma lem1704647 (x : real) : (term209 x) = (term210 x).
Proof. exact (@lem1483486 (term89 x) x term60). Qed.
Lemma lem1704648 (x : real) : (term211 x) = (term91 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1704650 (m : nat) : (term79 m) = term80.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1704651 : term81 = term80.
Proof. exact (@lem1704650 term44). Qed.
Lemma lem1704652 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704653 : term82 = term83.
Proof. exact (MK_COMB (@lem1704652) (@lem1704651)). Qed.
Lemma lem1704654 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1704655 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1704653) (@lem1704654 x)). Qed.
Lemma lem1704656 (x : real) : (term211 x) = (term92 x).
Proof. exact (TRANS (@lem1704648 x) (@lem1704655 x)). Qed.
Lemma lem1704657 (x : real) : (term92 x) = term80.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1704658 (x : real) : (term211 x) = term80.
Proof. exact (TRANS (@lem1704656 x) (@lem1704657 x)). Qed.
Lemma lem1704659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1704660 (x : real) : (term212 x) = term86.
Proof. exact (MK_COMB (@lem1704659) (@lem1704658 x)). Qed.
Lemma lem1704661 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1704662 (x : real) : (term210 x) = term213.
Proof. exact (MK_COMB (@lem1704660 x) (@lem1704661)). Qed.
Lemma lem1704663 (x : real) : (term209 x) = term213.
Proof. exact (TRANS (@lem1704647 x) (@lem1704662 x)). Qed.
Lemma lem1704664 : term213 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1704665 (x : real) : (term209 x) = term60.
Proof. exact (TRANS (@lem1704663 x) (@lem1704664)). Qed.
Lemma lem1704666 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1704667 (x : real) : (term214 x) = term215.
Proof. exact (MK_COMB (@lem1704666) (@lem1704665 x)). Qed.
Lemma lem1704668 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem1704669 (x : real) : (term208 x) = term216.
Proof. exact (MK_COMB (@lem1704667 x) (@lem1704668)). Qed.
Lemma lem1704670 (x : real) (h1 : term196 x) : term216.
Proof. exact (EQ_MP (@lem1704669 x) (@lem1704646 x h1)). Qed.
Lemma lem1704672 (m : nat) (n : nat) : (term217 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1704673 : term216 = False.
Proof. exact (@lem1704672 term44 (NUMERAL 0)). Qed.
Lemma lem1704674 (x : real) (h1 : term196 x) : False.
Proof. exact (EQ_MP (@lem1704673) (@lem1704670 x h1)). Qed.
Lemma lem1704676 (x : real) (h1 : term196 x) : term196 x.
Proof. exact (h1). Qed.
Lemma lem1704677 (x : real) (h1 : term196 x) : (term196 x) = False.
Proof. exact (prop_ext (fun h2 : term196 x => @lem1704674 x h1) (fun h2 : False => @lem1704676 x h1)). Qed.
Lemma lem1704678 (x : real) (h1 : term196 x) : False.
Proof. exact (EQ_MP (@lem1704677 x h1) (@lem1704676 x h1)). Qed.
Lemma lem1704679 (x : real) (h1 : term175 x) : term175 x.
Proof. exact (h1). Qed.
Lemma lem1704680 (x : real) (h1 : term175 x) : term196 x.
Proof. exact (EQ_MP (@lem1704593 x) (@lem1704679 x h1)). Qed.
Lemma lem1704681 (x : real) (h1 : term175 x) : (term196 x) = False.
Proof. exact (prop_ext (fun h2 : term196 x => @lem1704678 x h2) (fun h2 : False => @lem1704680 x h1)). Qed.
Lemma lem1704682 (x : real) (h1 : term175 x) : False.
Proof. exact (EQ_MP (@lem1704681 x h1) (@lem1704680 x h1)). Qed.
Lemma lem1704683 (x : real) : term218 x.
Proof. exact (fun h0 : term175 x => @lem1704682 x h0). Qed.
Lemma lem1704684 (x : real) : term219 x.
Proof. exact (@lem1386578 (term220 x)). Qed.
Lemma lem1704685 (x : real) : term220 x.
Proof. exact (@lem1704684 x (@lem1704683 x)). Qed.
Lemma lem1704686 (h1 : term221) : term221.
Proof. exact (h1). Qed.
Lemma lem1704687 (x : real) (h1 : term221) : term222 x.
Proof. exact (@lem1704686 h1 x). Qed.
Lemma lem1704688 (x : real) : (term222 x) = (term223 x).
Proof. exact (eq_refl (term222 x)). Qed.
Lemma lem1704689 (x : real) (h1 : term221) : term223 x.
Proof. exact (EQ_MP (@lem1704688 x) (@lem1704687 x h1)). Qed.
Lemma lem1704690 (x : real) (y : real) (h1 : term221) : term224 x y.
Proof. exact (@lem1704689 x h1 y). Qed.
Lemma lem1704691 (y : real) (x : real) : (term224 x y) = (term225 y x).
Proof. exact (eq_refl (term224 x y)). Qed.
Lemma lem1704692 (y : real) (x : real) (h1 : term221) : term225 y x.
Proof. exact (EQ_MP (@lem1704691 y x) (@lem1704690 x y h1)). Qed.
Lemma lem1704693 (y : real) (x : real) (z : real) (h1 : term221) : term226 y x z.
Proof. exact (@lem1704692 y x h1 z). Qed.
Lemma lem1704694 (y : real) (x : real) (z : real) : (term226 y x z) = (term227 y x z).
Proof. exact (eq_refl (term226 y x z)). Qed.
Lemma lem1704695 (y : real) (x : real) (z : real) (h1 : term221) : term227 y x z.
Proof. exact (EQ_MP (@lem1704694 y x z) (@lem1704693 y x z h1)). Qed.
Lemma lem1704696 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term228 x y z.
Proof. exact (h1). Qed.
Lemma lem1704697 (x : real) (y : real) (z : real) (h1 : term221) (h2 : term228 x y z) : real_le x z.
Proof. exact (@lem1704695 y x z h1 (@lem1704696 x y z h2)). Qed.
Lemma lem1704698 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term229 x z.
Proof. exact (fun h0 : term221 => @lem1704697 x y z h0 h1). Qed.
Lemma lem1704699 (x : real) (z : real) (h1 : term230 x z) : term230 x z.
Proof. exact (h1). Qed.
Lemma lem1704700 (x : real) (z : real) (h1 : term230 x z) : term229 x z.
Proof. exact (ex_elim (@lem1704699 x z h1) (fun y : real => fun h0 : term231 x z y => @lem1704698 x y z h0)). Qed.
Lemma lem1704701 (h1 : term221) : term221.
Proof. exact (h1). Qed.
Lemma lem1704702 (x : real) (z : real) (h1 : term221) (h2 : term230 x z) : real_le x z.
Proof. exact (@lem1704700 x z h2 (@lem1704701 h1)). Qed.
Lemma lem1704703 (x : real) (z : real) (h1 : term221) : term232 x z.
Proof. exact (fun h0 : term230 x z => @lem1704702 x z h1 h0). Qed.
Lemma lem1704704 (x : real) (h1 : term221) : term233 x.
Proof. exact (fun z : real => @lem1704703 x z h1). Qed.
Lemma lem1704705 (h1 : term221) : term234.
Proof. exact (fun x : real => @lem1704704 x h1). Qed.
Lemma lem1704706 : term235.
Proof. exact (fun h0 : term221 => @lem1704705 h0). Qed.
Lemma lem1704707 : term234.
Proof. exact (@lem1704706 (@lem1339577)). Qed.
Lemma lem1704708 (x : real) : term236 x.
Proof. exact (@lem1704707 x). Qed.
Lemma lem1704709 (x : real) : (term236 x) = (term233 x).
Proof. exact (eq_refl (term236 x)). Qed.
Lemma lem1704710 (x : real) : term233 x.
Proof. exact (EQ_MP (@lem1704709 x) (@lem1704708 x)). Qed.
Lemma lem1704711 (x : real) (z : real) : term237 x z.
Proof. exact (@lem1704710 x z). Qed.
Lemma lem1704712 (x : real) (z : real) : (term237 x z) = (term232 x z).
Proof. exact (eq_refl (term237 x z)). Qed.
Lemma lem1704715 (n : nat) (h1 : (term238 n) = (term239 n)) : (term238 n) = (term239 n).
Proof. exact (h1). Qed.
Lemma lem1704716 (n : nat) (h1 : (term238 n) = (term239 n)) : (term239 n) = (term238 n).
Proof. exact (SYM (@lem1704715 n h1)). Qed.
Lemma lem1704717 (n : nat) (h1 : (term239 n) = (term238 n)) : (term239 n) = (term238 n).
Proof. exact (h1). Qed.
Lemma lem1704718 (n : nat) (h1 : (term239 n) = (term238 n)) : (term238 n) = (term239 n).
Proof. exact (SYM (@lem1704717 n h1)). Qed.
Lemma lem1704719 (n : nat) : ((term238 n) = (term239 n)) = ((term239 n) = (term238 n)).
Proof. exact (prop_ext (fun h1 : (term238 n) = (term239 n) => @lem1704716 n h1) (fun h1 : (term239 n) = (term238 n) => @lem1704718 n h1)). Qed.
Lemma lem1704720 : term240 = term241.
Proof. exact (fun_ext (fun n : nat => @lem1704719 n)). Qed.
Lemma lem1704721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1704722 : term242 = term243.
Proof. exact (MK_COMB (@lem1704721) (@lem1704720)). Qed.
Lemma lem1704723 : term243.
Proof. exact (EQ_MP (@lem1704722) (@lem1484068)). Qed.
Lemma lem1704724 (n : nat) : term244 n.
Proof. exact (@lem1704723 n). Qed.
Lemma lem1704725 (n : nat) : (term244 n) = ((term239 n) = (term238 n)).
Proof. exact (eq_refl (term244 n)). Qed.
Lemma lem1704727 (x : real) : term245 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1704728 (x : real) : (term245 x) = (real_le x x).
Proof. exact (eq_refl (term245 x)). Qed.
Lemma lem1704729 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1704728 x) (@lem1704727 x)). Qed.
Lemma lem1704730 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1704732 (x : real) : term246 x.
Proof. exact (@lem1361590 x). Qed.
Lemma lem1704733 (x : real) : (term246 x) = ((term182 x) = x).
Proof. exact (eq_refl (term246 x)). Qed.
Lemma lem1704735 (x : real) : term247 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1704736 (x : real) : (term247 x) = ((term92 x) = term80).
Proof. exact (eq_refl (term247 x)). Qed.
Lemma lem1704738 (x : real) : term248 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1704739 (x : real) (n : nat) : term249 x n.
Proof. exact (@lem1704738 x n). Qed.
Lemma lem1704740 (x : real) (n : nat) : (term249 x n) = ((term250 x n) = (term251 x n)).
Proof. exact (eq_refl (term249 x n)). Qed.
Lemma lem1704743 {A : Type'} (P : Prop) : term252 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem1704744 {A : Type'} (P : Prop) : (term252 A P) = (term253 A P).
Proof. exact (eq_refl (term252 A P)). Qed.
Lemma lem1704745 {A : Type'} (P : Prop) : term253 A P.
Proof. exact (EQ_MP (@lem1704744 A P) (@lem1704743 A P)). Qed.
Lemma lem1704746 {A : Type'} (P : Prop) (Q : A -> Prop) : term254 A P Q.
Proof. exact (@lem1704745 A P Q). Qed.
Lemma lem1704747 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = ((term255 A P Q) = (term256 A P Q)).
Proof. exact (eq_refl (term254 A P Q)). Qed.
Lemma lem1704750 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem1704747 A P Q) (@lem1704746 A P Q)). Qed.
Lemma lem1704751 (P : Prop) (Q : nat -> Prop) : (term257 P Q) = (term258 P Q).
Proof. exact (@lem1704750 nat P Q). Qed.
Lemma lem1704752 (x : real) : (term259 x) = (term260 x).
Proof. exact (@lem1704751 (term177 x) (term261 x)). Qed.
Lemma lem1704753 (x : real) (n : nat) : (term262 x n) = (term263 x n).
Proof. exact (eq_refl (term262 x n)). Qed.
Lemma lem1704754 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1704755 (x : real) (n : nat) : (term265 x n) = (term266 x n).
Proof. exact (MK_COMB (@lem1704754 x) (@lem1704753 x n)). Qed.
Lemma lem1704756 (x : real) : (term267 x) = (term268 x).
Proof. exact (fun_ext (fun n : nat => @lem1704755 x n)). Qed.
Lemma lem1704757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1704758 (x : real) : (term259 x) = (term269 x).
Proof. exact (MK_COMB (@lem1704757) (@lem1704756 x)). Qed.
Lemma lem1704759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1704760 (x : real) : (term270 x) = (term271 x).
Proof. exact (MK_COMB (@lem1704759) (@lem1704758 x)). Qed.
Lemma lem1704761 (x : real) (n : nat) : (term262 x n) = (term263 x n).
Proof. exact (eq_refl (term262 x n)). Qed.
Lemma lem1704762 (x : real) : (term272 x) = (term261 x).
Proof. exact (fun_ext (fun n : nat => @lem1704761 x n)). Qed.
Lemma lem1704763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1704764 (x : real) : (term273 x) = (term274 x).
Proof. exact (MK_COMB (@lem1704763) (@lem1704762 x)). Qed.
Lemma lem1704765 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1704766 (x : real) : (term260 x) = (term275 x).
Proof. exact (MK_COMB (@lem1704765 x) (@lem1704764 x)). Qed.
Lemma lem1704767 (x : real) : ((term259 x) = (term260 x)) = ((term269 x) = (term275 x)).
Proof. exact (MK_COMB (@lem1704760 x) (@lem1704766 x)). Qed.
Lemma lem1704768 (x : real) : (term269 x) = (term275 x).
Proof. exact (EQ_MP (@lem1704767 x) (@lem1704752 x)). Qed.
Lemma lem1704775 (x : real) : (term275 x) = (term269 x).
Proof. exact (SYM (@lem1704768 x)). Qed.
Lemma lem1704776 (x : real) (h1 : term177 x) : term177 x.
Proof. exact (h1). Qed.
Lemma lem1704778 (P : nat -> Prop) : term276 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1704779 (x : real) : term277 x.
Proof. exact (@lem1704778 (term261 x)). Qed.
Lemma lem1704780 (x : real) : (term278 x) = (term279 x).
Proof. exact (eq_refl (term278 x)). Qed.
Lemma lem1704781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704782 (x : real) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem1704781) (@lem1704780 x)). Qed.
Lemma lem1704783 (x : real) (n : nat) : (term262 x n) = (term263 x n).
Proof. exact (eq_refl (term262 x n)). Qed.
Lemma lem1704784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1704785 (x : real) (n : nat) : (term282 x n) = (term283 x n).
Proof. exact (MK_COMB (@lem1704784) (@lem1704783 x n)). Qed.
Lemma lem1704786 (x : real) (n : nat) : (term284 x n) = (term285 x n).
Proof. exact (eq_refl (term284 x n)). Qed.
Lemma lem1704787 (x : real) (n : nat) : (term286 x n) = (term287 x n).
Proof. exact (MK_COMB (@lem1704785 x n) (@lem1704786 x n)). Qed.
Lemma lem1704788 (x : real) : (term288 x) = (term289 x).
Proof. exact (fun_ext (fun n : nat => @lem1704787 x n)). Qed.
Lemma lem1704789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1704790 (x : real) : (term290 x) = (term291 x).
Proof. exact (MK_COMB (@lem1704789) (@lem1704788 x)). Qed.
Lemma lem1704791 (x : real) : (term292 x) = (term293 x).
Proof. exact (MK_COMB (@lem1704782 x) (@lem1704790 x)). Qed.
Lemma lem1704792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1704793 (x : real) : (term294 x) = (term295 x).
Proof. exact (MK_COMB (@lem1704792) (@lem1704791 x)). Qed.
Lemma lem1704794 (x : real) (n : nat) : (term262 x n) = (term263 x n).
Proof. exact (eq_refl (term262 x n)). Qed.
Lemma lem1704795 (x : real) : (term272 x) = (term261 x).
Proof. exact (fun_ext (fun n : nat => @lem1704794 x n)). Qed.
Lemma lem1704796 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1704797 (x : real) : (term273 x) = (term274 x).
Proof. exact (MK_COMB (@lem1704796) (@lem1704795 x)). Qed.
Lemma lem1704798 (x : real) : (term277 x) = (term296 x).
Proof. exact (MK_COMB (@lem1704793 x) (@lem1704797 x)). Qed.
Lemma lem1704799 (x : real) : term296 x.
Proof. exact (EQ_MP (@lem1704798 x) (@lem1704779 x)). Qed.
Lemma lem1704800 (x : real) (n : nat) (h1 : term263 x n) : term263 x n.
Proof. exact (h1). Qed.
Lemma lem1704804 (x : real) : (term92 x) = term80.
Proof. exact (EQ_MP (@lem1704736 x) (@lem1704735 x)). Qed.
Lemma lem1704805 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1704806 (x : real) : (term297 x) = term298.
Proof. exact (MK_COMB (@lem1704805) (@lem1704804 x)). Qed.
Lemma lem1704808 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1704733 x) (@lem1704732 x)). Qed.
Lemma lem1704809 : term298 = term11.
Proof. exact (@lem1704808 term11). Qed.
Lemma lem1704810 (x : real) : (term297 x) = term11.
Proof. exact (TRANS (@lem1704806 x) (@lem1704809)). Qed.
Lemma lem1704811 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1704812 (x : real) : (term299 x) = term300.
Proof. exact (MK_COMB (@lem1704811) (@lem1704810 x)). Qed.
Lemma lem1704814 (x : real) : (term301 x) = term11.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1704815 (x : real) : (term302 x) = term11.
Proof. exact (@lem1704814 (term19 x)). Qed.
Lemma lem1704816 (x : real) : (term279 x) = term303.
Proof. exact (MK_COMB (@lem1704812 x) (@lem1704815 x)). Qed.
Lemma lem1704818 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1704730 x) (@lem1704729 x)). Qed.
Lemma lem1704819 : term303 = True.
Proof. exact (@lem1704818 term11). Qed.
Lemma lem1704820 (x : real) : (term279 x) = True.
Proof. exact (TRANS (@lem1704816 x) (@lem1704819)). Qed.
Lemma lem1704821 (x : real) : True = (term279 x).
Proof. exact (SYM (@lem1704820 x)). Qed.
Lemma lem1704822 (x : real) : term279 x.
Proof. exact (EQ_MP (@lem1704821 x) (@lem0)). Qed.
Lemma lem1704826 (x : real) (n : nat) : (term250 x n) = (term251 x n).
Proof. exact (EQ_MP (@lem1704740 x n) (@lem1704739 x n)). Qed.
Lemma lem1704827 (x : real) (n : nat) : (term304 x n) = (term305 x n).
Proof. exact (@lem1704826 (term19 x) n). Qed.
Lemma lem1704828 (n : nat) (x : real) : (term306 n x) = (term306 n x).
Proof. exact (eq_refl (term306 n x)). Qed.
Lemma lem1704829 (x : real) (n : nat) : (term285 x n) = (term307 x n).
Proof. exact (MK_COMB (@lem1704828 n x) (@lem1704827 x n)). Qed.
Lemma lem1704832 (x : real) (n : nat) : (term307 x n) = (term285 x n).
Proof. exact (SYM (@lem1704829 x n)). Qed.
Lemma lem1704834 (n : nat) : (term239 n) = (term238 n).
Proof. exact (EQ_MP (@lem1704725 n) (@lem1704724 n)). Qed.
Lemma lem1704835 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1704836 (n : nat) : (term308 n) = (term309 n).
Proof. exact (MK_COMB (@lem1704835) (@lem1704834 n)). Qed.
Lemma lem1704837 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1704838 (n : nat) (x : real) : (term310 n x) = (term311 n x).
Proof. exact (MK_COMB (@lem1704836 n) (@lem1704837 x)). Qed.
Lemma lem1704839 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1704840 (n : nat) (x : real) : (term312 n x) = (term313 n x).
Proof. exact (MK_COMB (@lem1704839) (@lem1704838 n x)). Qed.
Lemma lem1704841 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1704842 (n : nat) (x : real) : (term306 n x) = (term314 n x).
Proof. exact (MK_COMB (@lem1704841) (@lem1704840 n x)). Qed.
Lemma lem1704843 (x : real) (n : nat) : (term305 x n) = (term305 x n).
Proof. exact (eq_refl (term305 x n)). Qed.
Lemma lem1704844 (x : real) (n : nat) : (term307 x n) = (term315 x n).
Proof. exact (MK_COMB (@lem1704842 n x) (@lem1704843 x n)). Qed.
Lemma lem1704845 (x : real) (n : nat) : (term315 x n) = (term307 x n).
Proof. exact (SYM (@lem1704844 x n)). Qed.
Lemma lem1704847 (x : real) (z : real) : term232 x z.
Proof. exact (EQ_MP (@lem1704712 x z) (@lem1704711 x z)). Qed.
Lemma lem1704848 (x : real) (n : nat) : term316 x n.
Proof. exact (@lem1704847 (term313 n x) (term305 x n)). Qed.
Lemma lem1704849 (x : real) (h1 : term177 x) : term177 x.
Proof. exact (h1). Qed.
Lemma lem1704850 (x : real) (h1 : term177 x) : term178 x.
Proof. exact (@lem1704685 x (@lem1704849 x h1)). Qed.
Lemma lem1704851 (x : real) : (term178 x) = ((term178 x) = True).
Proof. exact (@lem7 (term178 x)). Qed.
Lemma lem1704852 (x : real) (h1 : term177 x) : (term178 x) = True.
Proof. exact (EQ_MP (@lem1704851 x) (@lem1704850 x h1)). Qed.
Lemma lem1704858 (x : real) : term317 x.
Proof. exact (@lem1583207 x). Qed.
Lemma lem1704859 (x : real) : (term317 x) = (term318 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1704860 (x : real) : term318 x.
Proof. exact (EQ_MP (@lem1704859 x) (@lem1704858 x)). Qed.
Lemma lem1704861 (x : real) (y : real) : term319 x y.
Proof. exact (@lem1704860 x y). Qed.
Lemma lem1704862 (y : real) (x : real) : (term319 x y) = (term320 y x).
Proof. exact (eq_refl (term319 x y)). Qed.
Lemma lem1704863 (y : real) (x : real) : term320 y x.
Proof. exact (EQ_MP (@lem1704862 y x) (@lem1704861 x y)). Qed.
Lemma lem1704864 (y : real) (x : real) (z : real) : term321 y x z.
Proof. exact (@lem1704863 y x z). Qed.
Lemma lem1704865 (y : real) (x : real) (z : real) : (term321 y x z) = (term322 y x z).
Proof. exact (eq_refl (term321 y x z)). Qed.
Lemma lem1704866 (y : real) (x : real) (z : real) : term322 y x z.
Proof. exact (EQ_MP (@lem1704865 y x z) (@lem1704864 y x z)). Qed.
Lemma lem1704867 (x : real) (y : real) (z : real) (h1 : term323 x y z) : term323 x y z.
Proof. exact (h1). Qed.
Lemma lem1704868 (x : real) (y : real) (z : real) (h1 : term323 x y z) : term324 y x z.
Proof. exact (@lem1704866 y x z (@lem1704867 x y z h1)). Qed.
Lemma lem1704869 (y : real) (x : real) (z : real) : (term324 y x z) = ((term324 y x z) = True).
Proof. exact (@lem7 (term324 y x z)). Qed.
Lemma lem1704870 (x : real) (y : real) (z : real) (h1 : term323 x y z) : (term324 y x z) = True.
Proof. exact (EQ_MP (@lem1704869 y x z) (@lem1704868 x y z h1)). Qed.
Lemma lem1704876 (x : real) : (term177 x) = ((term177 x) = True).
Proof. exact (@lem7 (term177 x)). Qed.
Lemma lem1704878 (x : real) (n : nat) : (term263 x n) = ((term263 x n) = True).
Proof. exact (@lem7 (term263 x n)). Qed.
Lemma lem1704883 (y : real) (x : real) (z : real) : term325 y x z.
Proof. exact (fun h0 : term323 x y z => @lem1704870 x y z h0). Qed.
Lemma lem1704884 (x : real) (n : nat) : term326 x n.
Proof. exact (@lem1704883 (term327 n x) (term19 x) (term328 x n)). Qed.
Lemma lem1704888 (x : real) : term329 x.
Proof. exact (fun h0 : term177 x => @lem1704852 x h0). Qed.
Lemma lem1704890 (x : real) (h1 : term177 x) : (term177 x) = True.
Proof. exact (EQ_MP (@lem1704876 x) (@lem1704776 x h1)). Qed.
Lemma lem1704891 (x : real) (h1 : term177 x) : True = (term177 x).
Proof. exact (SYM (@lem1704890 x h1)). Qed.
Lemma lem1704892 (x : real) (h1 : term177 x) : term177 x.
Proof. exact (EQ_MP (@lem1704891 x h1) (@lem0)). Qed.
Lemma lem1704893 (x : real) (h1 : term177 x) : (term178 x) = True.
Proof. exact (@lem1704888 x (@lem1704892 x h1)). Qed.
Lemma lem1704894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704895 (x : real) (h1 : term177 x) : (term330 x) = (and True).
Proof. exact (MK_COMB (@lem1704894) (@lem1704893 x h1)). Qed.
Lemma lem1704897 (x : real) (n : nat) (h1 : term263 x n) : (term263 x n) = True.
Proof. exact (EQ_MP (@lem1704878 x n) (@lem1704800 x n h1)). Qed.
Lemma lem1704898 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term331 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1704895 x h1) (@lem1704897 x n h2)). Qed.
Lemma lem1704900 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1704901 : (True /\ True) = True.
Proof. exact (@lem1704900 True). Qed.
Lemma lem1704902 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term331 x n) = True.
Proof. exact (TRANS (@lem1704898 x n h1 h2) (@lem1704901)). Qed.
Lemma lem1704903 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : True = (term331 x n).
Proof. exact (SYM (@lem1704902 x n h1 h2)). Qed.
Lemma lem1704904 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term331 x n.
Proof. exact (EQ_MP (@lem1704903 x n h1 h2) (@lem0)). Qed.
Lemma lem1704905 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term332 x n) = True.
Proof. exact (@lem1704884 x n (@lem1704904 x n h1 h2)). Qed.
Lemma lem1704906 (n : nat) (x : real) : (term333 n x) = (term333 n x).
Proof. exact (eq_refl (term333 n x)). Qed.
Lemma lem1704907 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term334 x n) = (term335 n x).
Proof. exact (MK_COMB (@lem1704906 n x) (@lem1704905 x n h1 h2)). Qed.
Lemma lem1704909 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1704910 (n : nat) (x : real) : (term335 n x) = (term336 n x).
Proof. exact (@lem1704909 (term336 n x)). Qed.
Lemma lem1704911 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term334 x n) = (term336 n x).
Proof. exact (TRANS (@lem1704907 x n h1 h2) (@lem1704910 n x)). Qed.
Lemma lem1704912 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : (term336 n x) = (term334 x n).
Proof. exact (SYM (@lem1704911 x n h1 h2)). Qed.
Lemma lem1704913 (n : nat) : term337 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1704914 (n : nat) : (term337 n) = (term338 n).
Proof. exact (eq_refl (term337 n)). Qed.
Lemma lem1704915 (n : nat) : term338 n.
Proof. exact (EQ_MP (@lem1704914 n) (@lem1704913 n)). Qed.
Lemma lem1704916 (n : nat) : (term338 n) = ((term338 n) = True).
Proof. exact (@lem7 (term338 n)). Qed.
Lemma lem1704918 (x : real) : term339 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1704919 (x : real) : (term339 x) = (term340 x).
Proof. exact (eq_refl (term339 x)). Qed.
Lemma lem1704920 (x : real) : term340 x.
Proof. exact (EQ_MP (@lem1704919 x) (@lem1704918 x)). Qed.
Lemma lem1704921 (x : real) (y : real) : term341 x y.
Proof. exact (@lem1704920 x y). Qed.
Lemma lem1704922 (x : real) (y : real) : (term341 x y) = (term342 x y).
Proof. exact (eq_refl (term341 x y)). Qed.
Lemma lem1704923 (x : real) (y : real) : term342 x y.
Proof. exact (EQ_MP (@lem1704922 x y) (@lem1704921 x y)). Qed.
Lemma lem1704924 (x : real) (y : real) (h1 : term343 x y) : term343 x y.
Proof. exact (h1). Qed.
Lemma lem1704925 (x : real) (y : real) (h1 : term343 x y) : term344 x y.
Proof. exact (@lem1704923 x y (@lem1704924 x y h1)). Qed.
Lemma lem1704926 (x : real) (y : real) : (term344 x y) = ((term344 x y) = True).
Proof. exact (@lem7 (term344 x y)). Qed.
Lemma lem1704927 (x : real) (y : real) (h1 : term343 x y) : (term344 x y) = True.
Proof. exact (EQ_MP (@lem1704926 x y) (@lem1704925 x y h1)). Qed.
Lemma lem1704933 (x : real) : (term177 x) = ((term177 x) = True).
Proof. exact (@lem7 (term177 x)). Qed.
Lemma lem1704938 (n : real) (x : real) : (term2 n x) = (term3 n x).
Proof. exact (@lem1704492 n x (@lem1704491 n x)). Qed.
Lemma lem1704939 (n : nat) (x : real) : (term336 n x) = (term345 n x).
Proof. exact (@lem1704938 (real_of_num n) x). Qed.
Lemma lem1704941 (x : real) (y : real) : term346 x y.
Proof. exact (fun h0 : term343 x y => @lem1704927 x y h0). Qed.
Lemma lem1704942 (n : nat) (x : real) : term347 n x.
Proof. exact (@lem1704941 (real_of_num n) (real_mul x x)). Qed.
Lemma lem1704946 (n : nat) : (term338 n) = True.
Proof. exact (EQ_MP (@lem1704916 n) (@lem1704915 n)). Qed.
Lemma lem1704947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1704948 (n : nat) : (term348 n) = (and True).
Proof. exact (MK_COMB (@lem1704947) (@lem1704946 n)). Qed.
Lemma lem1704950 (x : real) (y : real) : term346 x y.
Proof. exact (fun h0 : term343 x y => @lem1704927 x y h0). Qed.
Lemma lem1704951 (x : real) : term349 x.
Proof. exact (@lem1704950 x x). Qed.
Lemma lem1704953 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1704954 (x : real) : (term350 x) = (term177 x).
Proof. exact (@lem1704953 (term177 x)). Qed.
Lemma lem1704956 (x : real) (h1 : term177 x) : (term177 x) = True.
Proof. exact (EQ_MP (@lem1704933 x) (@lem1704776 x h1)). Qed.
Lemma lem1704957 (x : real) (h1 : term177 x) : (term350 x) = True.
Proof. exact (TRANS (@lem1704954 x) (@lem1704956 x h1)). Qed.
Lemma lem1704958 (x : real) (h1 : term177 x) : True = (term350 x).
Proof. exact (SYM (@lem1704957 x h1)). Qed.
Lemma lem1704959 (x : real) (h1 : term177 x) : term350 x.
Proof. exact (EQ_MP (@lem1704958 x h1) (@lem0)). Qed.
Lemma lem1704960 (x : real) (h1 : term177 x) : (term351 x) = True.
Proof. exact (@lem1704951 x (@lem1704959 x h1)). Qed.
Lemma lem1704961 (n : nat) (x : real) (h1 : term177 x) : (term352 n x) = (True /\ True).
Proof. exact (MK_COMB (@lem1704948 n) (@lem1704960 x h1)). Qed.
Lemma lem1704963 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1704964 : (True /\ True) = True.
Proof. exact (@lem1704963 True). Qed.
Lemma lem1704965 (n : nat) (x : real) (h1 : term177 x) : (term352 n x) = True.
Proof. exact (TRANS (@lem1704961 n x h1) (@lem1704964)). Qed.
Lemma lem1704966 (n : nat) (x : real) (h1 : term177 x) : True = (term352 n x).
Proof. exact (SYM (@lem1704965 n x h1)). Qed.
Lemma lem1704967 (n : nat) (x : real) (h1 : term177 x) : term352 n x.
Proof. exact (EQ_MP (@lem1704966 n x h1) (@lem0)). Qed.
Lemma lem1704968 (n : nat) (x : real) (h1 : term177 x) : (term345 n x) = True.
Proof. exact (@lem1704942 n x (@lem1704967 n x h1)). Qed.
Lemma lem1704969 (n : nat) (x : real) (h1 : term177 x) : (term336 n x) = True.
Proof. exact (TRANS (@lem1704939 n x) (@lem1704968 n x h1)). Qed.
Lemma lem1704970 (n : nat) (x : real) (h1 : term177 x) : True = (term336 n x).
Proof. exact (SYM (@lem1704969 n x h1)). Qed.
Lemma lem1704971 (n : nat) (x : real) (h1 : term177 x) : term336 n x.
Proof. exact (EQ_MP (@lem1704970 n x h1) (@lem0)). Qed.
Lemma lem1704972 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term334 x n.
Proof. exact (EQ_MP (@lem1704912 x n h1 h2) (@lem1704971 n x h1)). Qed.
Lemma lem1704973 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term353 x n.
Proof. exact (ex_intro (term354 x n) (term355 n x) (@lem1704972 x n h1 h2)). Qed.
Lemma lem1704974 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term315 x n.
Proof. exact (@lem1704848 x n (@lem1704973 x n h1 h2)). Qed.
Lemma lem1704975 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term307 x n.
Proof. exact (EQ_MP (@lem1704845 x n) (@lem1704974 x n h1 h2)). Qed.
Lemma lem1704976 (x : real) (n : nat) (h1 : term177 x) (h2 : term263 x n) : term285 x n.
Proof. exact (EQ_MP (@lem1704832 x n) (@lem1704975 x n h1 h2)). Qed.
Lemma lem1704977 (n : nat) (x : real) (h1 : term177 x) : term287 x n.
Proof. exact (fun h0 : term263 x n => @lem1704976 x n h1 h0). Qed.
Lemma lem1704982 (x : real) (h1 : term177 x) : term291 x.
Proof. exact (fun n : nat => @lem1704977 n x h1). Qed.
Lemma lem1704983 (x : real) (h1 : term177 x) : term293 x.
Proof. exact (conj (@lem1704822 x) (@lem1704982 x h1)). Qed.
Lemma lem1704984 (x : real) (h1 : term177 x) : term274 x.
Proof. exact (@lem1704799 x (@lem1704983 x h1)). Qed.
Lemma lem1704985 (x : real) : term275 x.
Proof. exact (fun h0 : term177 x => @lem1704984 x h0). Qed.
Lemma lem1704986 (x : real) : term269 x.
Proof. exact (EQ_MP (@lem1704775 x) (@lem1704985 x)). Qed.
Lemma lem1704991 : term356.
Proof. exact (fun x : real => @lem1704986 x). Qed.

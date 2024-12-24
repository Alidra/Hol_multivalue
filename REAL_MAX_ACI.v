Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_ACI_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
Require Import thm1482709_spec.
Require Import thm1482710_spec.
Require Import thm1483205_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
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
Require Import thm17045_spec.
Require Import thm940073_spec.
Lemma lem1574894 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17045 ((real_max x x) = x) ((term2 x y) = (real_max x y))). Qed.
Lemma lem1574896 (y : real) (x : real) (z : real) : (term3 y x z) = (term3 y x z).
Proof. exact (eq_refl (term3 y x z)). Qed.
Lemma lem1574897 (z : real) (x : real) (y : real) : (term4 z x y) = (term5 z x y).
Proof. exact (MK_COMB (@lem1574896 y x z) (@lem1574894 x y)). Qed.
Lemma lem1574898 (z : real) (x : real) (y : real) : (term6 z x y) = (term4 z x y).
Proof. exact (@lem17045 ((term7 x y z) = (term7 y x z)) (term8 x y)). Qed.
Lemma lem1574899 (z : real) (x : real) (y : real) : (term6 z x y) = (term5 z x y).
Proof. exact (TRANS (@lem1574898 z x y) (@lem1574897 z x y)). Qed.
Lemma lem1574901 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1574902 (z : real) (x : real) (y : real) : (term10 z x y) = (term11 z x y).
Proof. exact (MK_COMB (@lem1574901 x y z) (@lem1574899 z x y)). Qed.
Lemma lem1574903 (z : real) (x : real) (y : real) : (term12 z x y) = (term10 z x y).
Proof. exact (@lem17045 ((term13 x y z) = (term7 x y z)) (term14 z x y)). Qed.
Lemma lem1574904 (z : real) (x : real) (y : real) : (term12 z x y) = (term11 z x y).
Proof. exact (TRANS (@lem1574903 z x y) (@lem1574902 z x y)). Qed.
Lemma lem1574906 (y : real) (x : real) : (term15 y x) = (term15 y x).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1574907 (z : real) (x : real) (y : real) : (term16 z x y) = (term17 z x y).
Proof. exact (MK_COMB (@lem1574906 y x) (@lem1574904 z x y)). Qed.
Lemma lem1574908 (z : real) (x : real) (y : real) : (term18 z x y) = (term16 z x y).
Proof. exact (@lem17045 ((real_max x y) = (real_max y x)) (term19 z x y)). Qed.
Lemma lem1574938 (z : real) (x : real) (y : real) : (term18 z x y) = (term17 z x y).
Proof. exact (TRANS (@lem1574908 z x y) (@lem1574907 z x y)). Qed.
Lemma lem1574939 (y : real) (x : real) : (term20 y x) = (term21 y x).
Proof. exact (@lem1483554 (real_max x y) (real_max y x)). Qed.
Lemma lem1574952 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1483519 (real_max x y) (real_max y x)). Qed.
Lemma lem1574953 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1574954 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1574953) (@lem1574952 y x)). Qed.
Lemma lem1574955 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1483512 (term23 y x)). Qed.
Lemma lem1574956 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (@lem1483508 (real_max x y) term28 (term29 y x)). Qed.
Lemma lem1574957 (y : real) (x : real) : (term30 y x) = (term31 y x).
Proof. exact (@lem1483476 term28 term28 (real_max y x)). Qed.
Lemma lem1574959 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1574960 : term34 = term35.
Proof. exact (@lem1574959 term36 term36). Qed.
Lemma lem1574961 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1574962 : term38 = term36.
Proof. exact (EQ_MP (@lem1574961) (@lem940073)). Qed.
Lemma lem1574963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1574964 : term35 = term39.
Proof. exact (MK_COMB (@lem1574963) (@lem1574962)). Qed.
Lemma lem1574965 : term34 = term39.
Proof. exact (TRANS (@lem1574960) (@lem1574964)). Qed.
Lemma lem1574966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1574967 : term40 = term41.
Proof. exact (MK_COMB (@lem1574966) (@lem1574965)). Qed.
Lemma lem1574968 (y : real) (x : real) : (real_max y x) = (real_max y x).
Proof. exact (eq_refl (real_max y x)). Qed.
Lemma lem1574969 (y : real) (x : real) : (term31 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1574967) (@lem1574968 y x)). Qed.
Lemma lem1574970 (y : real) (x : real) : (term30 y x) = (term42 y x).
Proof. exact (TRANS (@lem1574957 y x) (@lem1574969 y x)). Qed.
Lemma lem1574971 (y : real) (x : real) : (term42 y x) = (real_max y x).
Proof. exact (@lem1483436 (real_max y x)). Qed.
Lemma lem1574972 (y : real) (x : real) : (term30 y x) = (real_max y x).
Proof. exact (TRANS (@lem1574970 y x) (@lem1574971 y x)). Qed.
Lemma lem1574975 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1574976 (y : real) (x : real) : (term27 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1574975 x y) (@lem1574972 y x)). Qed.
Lemma lem1574977 (y : real) (x : real) : (term26 y x) = (term44 y x).
Proof. exact (TRANS (@lem1574956 y x) (@lem1574976 y x)). Qed.
Lemma lem1574978 (y : real) (x : real) : (term25 y x) = (term44 y x).
Proof. exact (TRANS (@lem1574955 y x) (@lem1574977 y x)). Qed.
Lemma lem1574979 (y : real) (x : real) : (term45 y x) = (term45 y x).
Proof. exact (eq_refl (term45 y x)). Qed.
Lemma lem1574980 (y : real) (x : real) : ((term24 y x) = (term25 y x)) = ((term24 y x) = (term44 y x)).
Proof. exact (MK_COMB (@lem1574979 y x) (@lem1574978 y x)). Qed.
Lemma lem1574981 (y : real) (x : real) : (term24 y x) = (term44 y x).
Proof. exact (EQ_MP (@lem1574980 y x) (@lem1574954 y x)). Qed.
Lemma lem1574982 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574983 (y : real) (x : real) : (term46 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1574982) (@lem1574981 y x)). Qed.
Lemma lem1574984 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1574985 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1574983 y x) (@lem1574984)). Qed.
Lemma lem1574986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1574987 (y : real) (x : real) : (term51 y x) = (term52 y x).
Proof. exact (MK_COMB (@lem1574986) (@lem1574952 y x)). Qed.
Lemma lem1574988 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1574989 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1574987 y x) (@lem1574988)). Qed.
Lemma lem1574990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1574991 (y : real) (x : real) : (term55 y x) = (term56 y x).
Proof. exact (MK_COMB (@lem1574990) (@lem1574989 y x)). Qed.
Lemma lem1574992 (y : real) (x : real) : (term21 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1574991 y x) (@lem1574985 y x)). Qed.
Lemma lem1574993 (y : real) (x : real) : (term20 y x) = (term57 y x).
Proof. exact (TRANS (@lem1574939 y x) (@lem1574992 y x)). Qed.
Lemma lem1574994 (x : real) (y : real) (z : real) : (term58 x y z) = (term59 x y z).
Proof. exact (@lem1483554 (term13 x y z) (term7 x y z)). Qed.
Lemma lem1575000 (x : real) (y : real) (z : real) : (term60 x y z) = (term61 x y z).
Proof. exact (@lem1483519 (term13 x y z) (term7 x y z)). Qed.
Lemma lem1575005 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483488 (term63 x y z) (term13 x y z)). Qed.
Lemma lem1575007 (x : real) (y : real) (z : real) : (term60 x y z) = (term62 x y z).
Proof. exact (TRANS (@lem1575000 x y z) (@lem1575005 x y z)). Qed.
Lemma lem1575008 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1575009 (x : real) (y : real) (z : real) : (term64 x y z) = (term65 x y z).
Proof. exact (MK_COMB (@lem1575008) (@lem1575007 x y z)). Qed.
Lemma lem1575010 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem1483512 (term62 x y z)). Qed.
Lemma lem1575011 (x : real) (y : real) (z : real) : (term66 x y z) = (term67 x y z).
Proof. exact (@lem1483508 (term63 x y z) term28 (term13 x y z)). Qed.
Lemma lem1575012 (x : real) (y : real) (z : real) : (term68 x y z) = (term68 x y z).
Proof. exact (eq_refl (term68 x y z)). Qed.
Lemma lem1575013 (x : real) (y : real) (z : real) : (term69 x y z) = (term70 x y z).
Proof. exact (@lem1483476 term28 term28 (term7 x y z)). Qed.
Lemma lem1575015 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1575016 : term34 = term35.
Proof. exact (@lem1575015 term36 term36). Qed.
Lemma lem1575017 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1575018 : term38 = term36.
Proof. exact (EQ_MP (@lem1575017) (@lem940073)). Qed.
Lemma lem1575019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1575020 : term35 = term39.
Proof. exact (MK_COMB (@lem1575019) (@lem1575018)). Qed.
Lemma lem1575021 : term34 = term39.
Proof. exact (TRANS (@lem1575016) (@lem1575020)). Qed.
Lemma lem1575022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575023 : term40 = term41.
Proof. exact (MK_COMB (@lem1575022) (@lem1575021)). Qed.
Lemma lem1575024 (x : real) (y : real) (z : real) : (term7 x y z) = (term7 x y z).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1575025 (x : real) (y : real) (z : real) : (term70 x y z) = (term71 x y z).
Proof. exact (MK_COMB (@lem1575023) (@lem1575024 x y z)). Qed.
Lemma lem1575026 (x : real) (y : real) (z : real) : (term69 x y z) = (term71 x y z).
Proof. exact (TRANS (@lem1575013 x y z) (@lem1575025 x y z)). Qed.
Lemma lem1575027 (x : real) (y : real) (z : real) : (term71 x y z) = (term7 x y z).
Proof. exact (@lem1483436 (term7 x y z)). Qed.
Lemma lem1575028 (x : real) (y : real) (z : real) : (term69 x y z) = (term7 x y z).
Proof. exact (TRANS (@lem1575026 x y z) (@lem1575027 x y z)). Qed.
Lemma lem1575029 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1575030 (x : real) (y : real) (z : real) : (term72 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1575029) (@lem1575028 x y z)). Qed.
Lemma lem1575031 (x : real) (y : real) (z : real) : (term67 x y z) = (term74 x y z).
Proof. exact (MK_COMB (@lem1575030 x y z) (@lem1575012 x y z)). Qed.
Lemma lem1575032 (x : real) (y : real) (z : real) : (term66 x y z) = (term74 x y z).
Proof. exact (TRANS (@lem1575011 x y z) (@lem1575031 x y z)). Qed.
Lemma lem1575033 (x : real) (y : real) (z : real) : (term65 x y z) = (term74 x y z).
Proof. exact (TRANS (@lem1575010 x y z) (@lem1575032 x y z)). Qed.
Lemma lem1575034 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (eq_refl (term75 x y z)). Qed.
Lemma lem1575035 (x : real) (y : real) (z : real) : ((term64 x y z) = (term65 x y z)) = ((term64 x y z) = (term74 x y z)).
Proof. exact (MK_COMB (@lem1575034 x y z) (@lem1575033 x y z)). Qed.
Lemma lem1575036 (x : real) (y : real) (z : real) : (term64 x y z) = (term74 x y z).
Proof. exact (EQ_MP (@lem1575035 x y z) (@lem1575009 x y z)). Qed.
Lemma lem1575037 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575038 (x : real) (y : real) (z : real) : (term76 x y z) = (term77 x y z).
Proof. exact (MK_COMB (@lem1575037) (@lem1575036 x y z)). Qed.
Lemma lem1575039 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575040 (x : real) (y : real) (z : real) : (term78 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1575038 x y z) (@lem1575039)). Qed.
Lemma lem1575041 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575042 (x : real) (y : real) (z : real) : (term80 x y z) = (term81 x y z).
Proof. exact (MK_COMB (@lem1575041) (@lem1575007 x y z)). Qed.
Lemma lem1575043 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575044 (x : real) (y : real) (z : real) : (term82 x y z) = (term83 x y z).
Proof. exact (MK_COMB (@lem1575042 x y z) (@lem1575043)). Qed.
Lemma lem1575045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575046 (x : real) (y : real) (z : real) : (term84 x y z) = (term85 x y z).
Proof. exact (MK_COMB (@lem1575045) (@lem1575044 x y z)). Qed.
Lemma lem1575047 (x : real) (y : real) (z : real) : (term59 x y z) = (term86 x y z).
Proof. exact (MK_COMB (@lem1575046 x y z) (@lem1575040 x y z)). Qed.
Lemma lem1575048 (x : real) (y : real) (z : real) : (term58 x y z) = (term86 x y z).
Proof. exact (TRANS (@lem1574994 x y z) (@lem1575047 x y z)). Qed.
Lemma lem1575049 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1483554 (term7 x y z) (term7 y x z)). Qed.
Lemma lem1575062 (y : real) (x : real) (z : real) : (term89 y x z) = (term90 y x z).
Proof. exact (@lem1483519 (term7 x y z) (term7 y x z)). Qed.
Lemma lem1575063 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1575064 (y : real) (x : real) (z : real) : (term91 y x z) = (term92 y x z).
Proof. exact (MK_COMB (@lem1575063) (@lem1575062 y x z)). Qed.
Lemma lem1575065 (y : real) (x : real) (z : real) : (term92 y x z) = (term93 y x z).
Proof. exact (@lem1483512 (term90 y x z)). Qed.
Lemma lem1575066 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1483508 (term7 x y z) term28 (term63 y x z)). Qed.
Lemma lem1575067 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (@lem1483476 term28 term28 (term7 y x z)). Qed.
Lemma lem1575069 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1575070 : term34 = term35.
Proof. exact (@lem1575069 term36 term36). Qed.
Lemma lem1575071 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1575072 : term38 = term36.
Proof. exact (EQ_MP (@lem1575071) (@lem940073)). Qed.
Lemma lem1575073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1575074 : term35 = term39.
Proof. exact (MK_COMB (@lem1575073) (@lem1575072)). Qed.
Lemma lem1575075 : term34 = term39.
Proof. exact (TRANS (@lem1575070) (@lem1575074)). Qed.
Lemma lem1575076 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575077 : term40 = term41.
Proof. exact (MK_COMB (@lem1575076) (@lem1575075)). Qed.
Lemma lem1575078 (y : real) (x : real) (z : real) : (term7 y x z) = (term7 y x z).
Proof. exact (eq_refl (term7 y x z)). Qed.
Lemma lem1575079 (y : real) (x : real) (z : real) : (term70 y x z) = (term71 y x z).
Proof. exact (MK_COMB (@lem1575077) (@lem1575078 y x z)). Qed.
Lemma lem1575080 (y : real) (x : real) (z : real) : (term69 y x z) = (term71 y x z).
Proof. exact (TRANS (@lem1575067 y x z) (@lem1575079 y x z)). Qed.
Lemma lem1575081 (y : real) (x : real) (z : real) : (term71 y x z) = (term7 y x z).
Proof. exact (@lem1483436 (term7 y x z)). Qed.
Lemma lem1575082 (y : real) (x : real) (z : real) : (term69 y x z) = (term7 y x z).
Proof. exact (TRANS (@lem1575080 y x z) (@lem1575081 y x z)). Qed.
Lemma lem1575085 (x : real) (y : real) (z : real) : (term95 x y z) = (term95 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1575086 (y : real) (x : real) (z : real) : (term94 y x z) = (term96 y x z).
Proof. exact (MK_COMB (@lem1575085 x y z) (@lem1575082 y x z)). Qed.
Lemma lem1575087 (y : real) (x : real) (z : real) : (term93 y x z) = (term96 y x z).
Proof. exact (TRANS (@lem1575066 y x z) (@lem1575086 y x z)). Qed.
Lemma lem1575088 (y : real) (x : real) (z : real) : (term92 y x z) = (term96 y x z).
Proof. exact (TRANS (@lem1575065 y x z) (@lem1575087 y x z)). Qed.
Lemma lem1575089 (y : real) (x : real) (z : real) : (term97 y x z) = (term97 y x z).
Proof. exact (eq_refl (term97 y x z)). Qed.
Lemma lem1575090 (y : real) (x : real) (z : real) : ((term91 y x z) = (term92 y x z)) = ((term91 y x z) = (term96 y x z)).
Proof. exact (MK_COMB (@lem1575089 y x z) (@lem1575088 y x z)). Qed.
Lemma lem1575091 (y : real) (x : real) (z : real) : (term91 y x z) = (term96 y x z).
Proof. exact (EQ_MP (@lem1575090 y x z) (@lem1575064 y x z)). Qed.
Lemma lem1575092 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575093 (y : real) (x : real) (z : real) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1575092) (@lem1575091 y x z)). Qed.
Lemma lem1575094 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575095 (y : real) (x : real) (z : real) : (term100 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem1575093 y x z) (@lem1575094)). Qed.
Lemma lem1575096 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575097 (y : real) (x : real) (z : real) : (term102 y x z) = (term103 y x z).
Proof. exact (MK_COMB (@lem1575096) (@lem1575062 y x z)). Qed.
Lemma lem1575098 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575099 (y : real) (x : real) (z : real) : (term104 y x z) = (term105 y x z).
Proof. exact (MK_COMB (@lem1575097 y x z) (@lem1575098)). Qed.
Lemma lem1575100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575101 (y : real) (x : real) (z : real) : (term106 y x z) = (term107 y x z).
Proof. exact (MK_COMB (@lem1575100) (@lem1575099 y x z)). Qed.
Lemma lem1575102 (y : real) (x : real) (z : real) : (term88 y x z) = (term108 y x z).
Proof. exact (MK_COMB (@lem1575101 y x z) (@lem1575095 y x z)). Qed.
Lemma lem1575103 (y : real) (x : real) (z : real) : (term87 y x z) = (term108 y x z).
Proof. exact (TRANS (@lem1575049 y x z) (@lem1575102 y x z)). Qed.
Lemma lem1575104 (x : real) : (term109 x) = (term110 x).
Proof. exact (@lem1483554 (real_max x x) x). Qed.
Lemma lem1575110 (x : real) : (term111 x) = (term112 x).
Proof. exact (@lem1483519 (real_max x x) x). Qed.
Lemma lem1575115 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem1483488 (term114 x) (real_max x x)). Qed.
Lemma lem1575117 (x : real) : (term111 x) = (term113 x).
Proof. exact (TRANS (@lem1575110 x) (@lem1575115 x)). Qed.
Lemma lem1575118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1575119 (x : real) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem1575118) (@lem1575117 x)). Qed.
Lemma lem1575120 (x : real) : (term116 x) = (term117 x).
Proof. exact (@lem1483512 (term113 x)). Qed.
Lemma lem1575121 (x : real) : (term117 x) = (term118 x).
Proof. exact (@lem1483508 (term114 x) term28 (real_max x x)). Qed.
Lemma lem1575122 (x : real) : (term119 x) = (term119 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1575123 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483476 term28 term28 x). Qed.
Lemma lem1575125 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1575126 : term34 = term35.
Proof. exact (@lem1575125 term36 term36). Qed.
Lemma lem1575127 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1575128 : term38 = term36.
Proof. exact (EQ_MP (@lem1575127) (@lem940073)). Qed.
Lemma lem1575129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1575130 : term35 = term39.
Proof. exact (MK_COMB (@lem1575129) (@lem1575128)). Qed.
Lemma lem1575131 : term34 = term39.
Proof. exact (TRANS (@lem1575126) (@lem1575130)). Qed.
Lemma lem1575132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575133 : term40 = term41.
Proof. exact (MK_COMB (@lem1575132) (@lem1575131)). Qed.
Lemma lem1575134 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1575135 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1575133) (@lem1575134 x)). Qed.
Lemma lem1575136 (x : real) : (term120 x) = (term122 x).
Proof. exact (TRANS (@lem1575123 x) (@lem1575135 x)). Qed.
Lemma lem1575137 (x : real) : (term122 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1575138 (x : real) : (term120 x) = x.
Proof. exact (TRANS (@lem1575136 x) (@lem1575137 x)). Qed.
Lemma lem1575139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1575140 (x : real) : (term123 x) = (real_add x).
Proof. exact (MK_COMB (@lem1575139) (@lem1575138 x)). Qed.
Lemma lem1575141 (x : real) : (term118 x) = (term124 x).
Proof. exact (MK_COMB (@lem1575140 x) (@lem1575122 x)). Qed.
Lemma lem1575142 (x : real) : (term117 x) = (term124 x).
Proof. exact (TRANS (@lem1575121 x) (@lem1575141 x)). Qed.
Lemma lem1575143 (x : real) : (term116 x) = (term124 x).
Proof. exact (TRANS (@lem1575120 x) (@lem1575142 x)). Qed.
Lemma lem1575144 (x : real) : (term125 x) = (term125 x).
Proof. exact (eq_refl (term125 x)). Qed.
Lemma lem1575145 (x : real) : ((term115 x) = (term116 x)) = ((term115 x) = (term124 x)).
Proof. exact (MK_COMB (@lem1575144 x) (@lem1575143 x)). Qed.
Lemma lem1575146 (x : real) : (term115 x) = (term124 x).
Proof. exact (EQ_MP (@lem1575145 x) (@lem1575119 x)). Qed.
Lemma lem1575147 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575148 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1575147) (@lem1575146 x)). Qed.
Lemma lem1575149 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575150 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1575148 x) (@lem1575149)). Qed.
Lemma lem1575151 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575152 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1575151) (@lem1575117 x)). Qed.
Lemma lem1575153 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575154 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1575152 x) (@lem1575153)). Qed.
Lemma lem1575155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575156 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1575155) (@lem1575154 x)). Qed.
Lemma lem1575157 (x : real) : (term110 x) = (term136 x).
Proof. exact (MK_COMB (@lem1575156 x) (@lem1575150 x)). Qed.
Lemma lem1575158 (x : real) : (term109 x) = (term136 x).
Proof. exact (TRANS (@lem1575104 x) (@lem1575157 x)). Qed.
Lemma lem1575159 (x : real) (y : real) : (term137 x y) = (term138 x y).
Proof. exact (@lem1483554 (term2 x y) (real_max x y)). Qed.
Lemma lem1575165 (x : real) (y : real) : (term139 x y) = (term140 x y).
Proof. exact (@lem1483519 (term2 x y) (real_max x y)). Qed.
Lemma lem1575170 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (@lem1483488 (term29 x y) (term2 x y)). Qed.
Lemma lem1575172 (x : real) (y : real) : (term139 x y) = (term141 x y).
Proof. exact (TRANS (@lem1575165 x y) (@lem1575170 x y)). Qed.
Lemma lem1575173 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1575174 (x : real) (y : real) : (term142 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1575173) (@lem1575172 x y)). Qed.
Lemma lem1575175 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (@lem1483512 (term141 x y)). Qed.
Lemma lem1575176 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1483508 (term29 x y) term28 (term2 x y)). Qed.
Lemma lem1575177 (x : real) (y : real) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem1575178 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483476 term28 term28 (real_max x y)). Qed.
Lemma lem1575180 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1575181 : term34 = term35.
Proof. exact (@lem1575180 term36 term36). Qed.
Lemma lem1575182 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1575183 : term38 = term36.
Proof. exact (EQ_MP (@lem1575182) (@lem940073)). Qed.
Lemma lem1575184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1575185 : term35 = term39.
Proof. exact (MK_COMB (@lem1575184) (@lem1575183)). Qed.
Lemma lem1575186 : term34 = term39.
Proof. exact (TRANS (@lem1575181) (@lem1575185)). Qed.
Lemma lem1575187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575188 : term40 = term41.
Proof. exact (MK_COMB (@lem1575187) (@lem1575186)). Qed.
Lemma lem1575189 (x : real) (y : real) : (real_max x y) = (real_max x y).
Proof. exact (eq_refl (real_max x y)). Qed.
Lemma lem1575190 (x : real) (y : real) : (term31 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1575188) (@lem1575189 x y)). Qed.
Lemma lem1575191 (x : real) (y : real) : (term30 x y) = (term42 x y).
Proof. exact (TRANS (@lem1575178 x y) (@lem1575190 x y)). Qed.
Lemma lem1575192 (x : real) (y : real) : (term42 x y) = (real_max x y).
Proof. exact (@lem1483436 (real_max x y)). Qed.
Lemma lem1575193 (x : real) (y : real) : (term30 x y) = (real_max x y).
Proof. exact (TRANS (@lem1575191 x y) (@lem1575192 x y)). Qed.
Lemma lem1575194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1575195 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1575194) (@lem1575193 x y)). Qed.
Lemma lem1575196 (x : real) (y : real) : (term145 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1575195 x y) (@lem1575177 x y)). Qed.
Lemma lem1575197 (x : real) (y : real) : (term144 x y) = (term149 x y).
Proof. exact (TRANS (@lem1575176 x y) (@lem1575196 x y)). Qed.
Lemma lem1575198 (x : real) (y : real) : (term143 x y) = (term149 x y).
Proof. exact (TRANS (@lem1575175 x y) (@lem1575197 x y)). Qed.
Lemma lem1575199 (x : real) (y : real) : (term150 x y) = (term150 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1575200 (x : real) (y : real) : ((term142 x y) = (term143 x y)) = ((term142 x y) = (term149 x y)).
Proof. exact (MK_COMB (@lem1575199 x y) (@lem1575198 x y)). Qed.
Lemma lem1575201 (x : real) (y : real) : (term142 x y) = (term149 x y).
Proof. exact (EQ_MP (@lem1575200 x y) (@lem1575174 x y)). Qed.
Lemma lem1575202 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575203 (x : real) (y : real) : (term151 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem1575202) (@lem1575201 x y)). Qed.
Lemma lem1575204 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575205 (x : real) (y : real) : (term153 x y) = (term154 x y).
Proof. exact (MK_COMB (@lem1575203 x y) (@lem1575204)). Qed.
Lemma lem1575206 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575207 (x : real) (y : real) : (term155 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem1575206) (@lem1575172 x y)). Qed.
Lemma lem1575208 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575209 (x : real) (y : real) : (term157 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1575207 x y) (@lem1575208)). Qed.
Lemma lem1575210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575211 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1575210) (@lem1575209 x y)). Qed.
Lemma lem1575212 (x : real) (y : real) : (term138 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1575211 x y) (@lem1575205 x y)). Qed.
Lemma lem1575213 (x : real) (y : real) : (term137 x y) = (term161 x y).
Proof. exact (TRANS (@lem1575159 x y) (@lem1575212 x y)). Qed.
Lemma lem1575214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575215 (x : real) : (term162 x) = (term163 x).
Proof. exact (MK_COMB (@lem1575214) (@lem1575158 x)). Qed.
Lemma lem1575216 (x : real) (y : real) : (term1 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1575215 x) (@lem1575213 x y)). Qed.
Lemma lem1575217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575218 (y : real) (x : real) (z : real) : (term3 y x z) = (term165 y x z).
Proof. exact (MK_COMB (@lem1575217) (@lem1575103 y x z)). Qed.
Lemma lem1575219 (z : real) (x : real) (y : real) : (term5 z x y) = (term166 z x y).
Proof. exact (MK_COMB (@lem1575218 y x z) (@lem1575216 x y)). Qed.
Lemma lem1575220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575221 (x : real) (y : real) (z : real) : (term9 x y z) = (term167 x y z).
Proof. exact (MK_COMB (@lem1575220) (@lem1575048 x y z)). Qed.
Lemma lem1575222 (z : real) (x : real) (y : real) : (term11 z x y) = (term168 z x y).
Proof. exact (MK_COMB (@lem1575221 x y z) (@lem1575219 z x y)). Qed.
Lemma lem1575223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575224 (y : real) (x : real) : (term15 y x) = (term169 y x).
Proof. exact (MK_COMB (@lem1575223) (@lem1574993 y x)). Qed.
Lemma lem1575225 (z : real) (x : real) (y : real) : (term17 z x y) = (term170 z x y).
Proof. exact (MK_COMB (@lem1575224 y x) (@lem1575222 z x y)). Qed.
Lemma lem1575270 (z : real) (x : real) (y : real) : (term18 z x y) = (term170 z x y).
Proof. exact (TRANS (@lem1574938 z x y) (@lem1575225 z x y)). Qed.
Lemma lem1575272 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1575273 (y : real) (x : real) : (term54 y x) = (term173 y x).
Proof. exact (@lem1575272 y (real_max x y) x term48). Qed.
Lemma lem1575286 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 (term114 x) (real_max x y)). Qed.
Lemma lem1575287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575288 (x : real) (y : real) : (term176 y x) = (term177 x y).
Proof. exact (MK_COMB (@lem1575287) (@lem1575286 x y)). Qed.
Lemma lem1575289 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575290 (x : real) (y : real) : (term178 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1575288 x y) (@lem1575289)). Qed.
Lemma lem1575303 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (@lem1483488 (term114 y) (real_max x y)). Qed.
Lemma lem1575304 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575305 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1575304) (@lem1575303 x y)). Qed.
Lemma lem1575306 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575307 (x : real) (y : real) : (term184 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1575305 x y) (@lem1575306)). Qed.
Lemma lem1575308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575309 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1575308) (@lem1575307 x y)). Qed.
Lemma lem1575310 (x : real) (y : real) : (term173 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1575309 x y) (@lem1575290 x y)). Qed.
Lemma lem1575311 (x : real) (y : real) : (term54 y x) = (term188 x y).
Proof. exact (TRANS (@lem1575273 y x) (@lem1575310 x y)). Qed.
Lemma lem1575312 (x : real) (y : real) : (term189 x y) = (term188 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1575313 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (SYM (@lem1575312 x y)). Qed.
Lemma lem1575314 (y : real) (x : real) : (term189 x y) = (term190 y x).
Proof. exact (@lem1483205 y (term191 y x) x). Qed.
Lemma lem1575315 (y : real) (x : real) : (term188 x y) = (term190 y x).
Proof. exact (TRANS (@lem1575313 x y) (@lem1575314 y x)). Qed.
Lemma lem1575316 (y : real) (x : real) : (term192 y x) = (term193 y x).
Proof. exact (eq_refl (term192 y x)). Qed.
Lemma lem1575317 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1575318 (y : real) (x : real) : (term195 y x) = (term196 y x).
Proof. exact (MK_COMB (@lem1575317 x y) (@lem1575316 y x)). Qed.
Lemma lem1575319 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (eq_refl (term197 x y)). Qed.
Lemma lem1575320 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1575321 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1575320 y x) (@lem1575319 x y)). Qed.
Lemma lem1575322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575323 (x : real) (y : real) : (term202 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1575322) (@lem1575321 x y)). Qed.
Lemma lem1575324 (y : real) (x : real) : (term190 y x) = (term204 y x).
Proof. exact (MK_COMB (@lem1575323 x y) (@lem1575318 y x)). Qed.
Lemma lem1575325 (x : real) (y : real) : (term205 x y) = (term205 x y).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem1575326 (y : real) (x : real) : ((term188 x y) = (term190 y x)) = ((term188 x y) = (term204 y x)).
Proof. exact (MK_COMB (@lem1575325 x y) (@lem1575324 y x)). Qed.
Lemma lem1575327 (y : real) (x : real) : (term188 x y) = (term204 y x).
Proof. exact (EQ_MP (@lem1575326 y x) (@lem1575315 y x)). Qed.
Lemma lem1575328 (y : real) (x : real) : (real_ge y x) = (term206 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1575334 (y : real) (x : real) : (real_sub y x) = (term207 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1575339 (x : real) (y : real) : (term207 y x) = (term208 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1575341 (x : real) (y : real) : (real_sub y x) = (term208 x y).
Proof. exact (TRANS (@lem1575334 y x) (@lem1575339 x y)). Qed.
Lemma lem1575342 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1575343 (x : real) (y : real) : (term209 y x) = (term210 x y).
Proof. exact (MK_COMB (@lem1575342) (@lem1575341 x y)). Qed.
Lemma lem1575344 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575345 (x : real) (y : real) : (term206 y x) = (term211 x y).
Proof. exact (MK_COMB (@lem1575343 x y) (@lem1575344)). Qed.
Lemma lem1575346 (x : real) (y : real) : (real_ge y x) = (term211 x y).
Proof. exact (TRANS (@lem1575328 y x) (@lem1575345 x y)). Qed.
Lemma lem1575347 (y : real) : (term212 y) = (term213 y).
Proof. exact (@lem1483525 (term214 y) term48). Qed.
Lemma lem1575348 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575360 (y : real) : (term214 y) = (term215 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1575362 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1575363 : term217 = term48.
Proof. exact (@lem1575362 term36). Qed.
Lemma lem1575364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575365 : term218 = term219.
Proof. exact (MK_COMB (@lem1575364) (@lem1575363)). Qed.
Lemma lem1575366 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1575367 (y : real) : (term215 y) = (term220 y).
Proof. exact (MK_COMB (@lem1575365) (@lem1575366 y)). Qed.
Lemma lem1575368 (y : real) : (term214 y) = (term220 y).
Proof. exact (TRANS (@lem1575360 y) (@lem1575367 y)). Qed.
Lemma lem1575369 (y : real) : (term220 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1575371 (y : real) : (term214 y) = term48.
Proof. exact (TRANS (@lem1575368 y) (@lem1575369 y)). Qed.
Lemma lem1575372 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1575373 (y : real) : (term221 y) = term222.
Proof. exact (MK_COMB (@lem1575372) (@lem1575371 y)). Qed.
Lemma lem1575374 (y : real) : (term223 y) = term224.
Proof. exact (MK_COMB (@lem1575373 y) (@lem1575348)). Qed.
Lemma lem1575375 : term224 = term225.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1575377 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575378 : term227 = term48.
Proof. exact (@lem1575377 term36). Qed.
Lemma lem1575379 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem1575380 : term225 = term229.
Proof. exact (MK_COMB (@lem1575379) (@lem1575378)). Qed.
Lemma lem1575381 : term229 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1575382 : term225 = term48.
Proof. exact (TRANS (@lem1575380) (@lem1575381)). Qed.
Lemma lem1575383 : term224 = term48.
Proof. exact (TRANS (@lem1575375) (@lem1575382)). Qed.
Lemma lem1575384 (y : real) : (term223 y) = term48.
Proof. exact (TRANS (@lem1575374 y) (@lem1575383)). Qed.
Lemma lem1575385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575386 (y : real) : (term230 y) = term231.
Proof. exact (MK_COMB (@lem1575385) (@lem1575384 y)). Qed.
Lemma lem1575387 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575388 (y : real) : (term213 y) = term232.
Proof. exact (MK_COMB (@lem1575386 y) (@lem1575387)). Qed.
Lemma lem1575389 (y : real) : (term212 y) = term232.
Proof. exact (TRANS (@lem1575347 y) (@lem1575388 y)). Qed.
Lemma lem1575390 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (@lem1483525 (term208 x y) term48). Qed.
Lemma lem1575408 (x : real) (y : real) : (term235 x y) = (term236 x y).
Proof. exact (@lem1483519 (term208 x y) term48). Qed.
Lemma lem1575410 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575411 : term227 = term48.
Proof. exact (@lem1575410 term36). Qed.
Lemma lem1575412 (x : real) (y : real) : (term237 x y) = (term237 x y).
Proof. exact (eq_refl (term237 x y)). Qed.
Lemma lem1575413 (x : real) (y : real) : (term236 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1575412 x y) (@lem1575411)). Qed.
Lemma lem1575414 (x : real) (y : real) : (term238 x y) = (term208 x y).
Proof. exact (@lem1483450 (term208 x y)). Qed.
Lemma lem1575415 (x : real) (y : real) : (term236 x y) = (term208 x y).
Proof. exact (TRANS (@lem1575413 x y) (@lem1575414 x y)). Qed.
Lemma lem1575417 (x : real) (y : real) : (term235 x y) = (term208 x y).
Proof. exact (TRANS (@lem1575408 x y) (@lem1575415 x y)). Qed.
Lemma lem1575418 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575419 (x : real) (y : real) : (term239 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1575418) (@lem1575417 x y)). Qed.
Lemma lem1575420 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575421 (x : real) (y : real) : (term234 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem1575419 x y) (@lem1575420)). Qed.
Lemma lem1575422 (x : real) (y : real) : (term233 x y) = (term233 x y).
Proof. exact (TRANS (@lem1575390 x y) (@lem1575421 x y)). Qed.
Lemma lem1575423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575424 (y : real) : (term241 y) = term242.
Proof. exact (MK_COMB (@lem1575423) (@lem1575389 y)). Qed.
Lemma lem1575425 (x : real) (y : real) : (term198 x y) = (term243 x y).
Proof. exact (MK_COMB (@lem1575424 y) (@lem1575422 x y)). Qed.
Lemma lem1575426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575427 (x : real) (y : real) : (term199 y x) = (term244 x y).
Proof. exact (MK_COMB (@lem1575426) (@lem1575346 x y)). Qed.
Lemma lem1575428 (x : real) (y : real) : (term201 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1575427 x y) (@lem1575425 x y)). Qed.
Lemma lem1575429 (x : real) (y : real) : (real_gt x y) = (term246 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1575442 (x : real) (y : real) : (real_sub x y) = (term207 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1575443 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575444 (x : real) (y : real) : (term247 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem1575443) (@lem1575442 x y)). Qed.
Lemma lem1575445 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575446 (x : real) (y : real) : (term246 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1575444 x y) (@lem1575445)). Qed.
Lemma lem1575447 (x : real) (y : real) : (real_gt x y) = (term249 x y).
Proof. exact (TRANS (@lem1575429 x y) (@lem1575446 x y)). Qed.
Lemma lem1575448 (y : real) (x : real) : (term233 y x) = (term234 y x).
Proof. exact (@lem1483525 (term208 y x) term48). Qed.
Lemma lem1575449 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575462 (x : real) (y : real) : (term208 y x) = (term207 x y).
Proof. exact (@lem1483488 x (term114 y)). Qed.
Lemma lem1575463 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1575464 (x : real) (y : real) : (term250 y x) = (term251 x y).
Proof. exact (MK_COMB (@lem1575463) (@lem1575462 x y)). Qed.
Lemma lem1575465 (x : real) (y : real) : (term235 y x) = (term252 x y).
Proof. exact (MK_COMB (@lem1575464 x y) (@lem1575449)). Qed.
Lemma lem1575466 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (@lem1483519 (term207 x y) term48). Qed.
Lemma lem1575468 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575469 : term227 = term48.
Proof. exact (@lem1575468 term36). Qed.
Lemma lem1575470 (x : real) (y : real) : (term254 x y) = (term254 x y).
Proof. exact (eq_refl (term254 x y)). Qed.
Lemma lem1575471 (x : real) (y : real) : (term253 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1575470 x y) (@lem1575469)). Qed.
Lemma lem1575472 (x : real) (y : real) : (term255 x y) = (term207 x y).
Proof. exact (@lem1483450 (term207 x y)). Qed.
Lemma lem1575473 (x : real) (y : real) : (term253 x y) = (term207 x y).
Proof. exact (TRANS (@lem1575471 x y) (@lem1575472 x y)). Qed.
Lemma lem1575474 (x : real) (y : real) : (term252 x y) = (term207 x y).
Proof. exact (TRANS (@lem1575466 x y) (@lem1575473 x y)). Qed.
Lemma lem1575475 (x : real) (y : real) : (term235 y x) = (term207 x y).
Proof. exact (TRANS (@lem1575465 x y) (@lem1575474 x y)). Qed.
Lemma lem1575476 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575477 (x : real) (y : real) : (term239 y x) = (term248 x y).
Proof. exact (MK_COMB (@lem1575476) (@lem1575475 x y)). Qed.
Lemma lem1575478 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575479 (x : real) (y : real) : (term234 y x) = (term249 x y).
Proof. exact (MK_COMB (@lem1575477 x y) (@lem1575478)). Qed.
Lemma lem1575480 (x : real) (y : real) : (term233 y x) = (term249 x y).
Proof. exact (TRANS (@lem1575448 y x) (@lem1575479 x y)). Qed.
Lemma lem1575481 (x : real) : (term212 x) = (term213 x).
Proof. exact (@lem1483525 (term214 x) term48). Qed.
Lemma lem1575482 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575494 (x : real) : (term214 x) = (term215 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1575496 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1575497 : term217 = term48.
Proof. exact (@lem1575496 term36). Qed.
Lemma lem1575498 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575499 : term218 = term219.
Proof. exact (MK_COMB (@lem1575498) (@lem1575497)). Qed.
Lemma lem1575500 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1575501 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1575499) (@lem1575500 x)). Qed.
Lemma lem1575502 (x : real) : (term214 x) = (term220 x).
Proof. exact (TRANS (@lem1575494 x) (@lem1575501 x)). Qed.
Lemma lem1575503 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1575505 (x : real) : (term214 x) = term48.
Proof. exact (TRANS (@lem1575502 x) (@lem1575503 x)). Qed.
Lemma lem1575506 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1575507 (x : real) : (term221 x) = term222.
Proof. exact (MK_COMB (@lem1575506) (@lem1575505 x)). Qed.
Lemma lem1575508 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1575507 x) (@lem1575482)). Qed.
Lemma lem1575509 : term224 = term225.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1575511 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575512 : term227 = term48.
Proof. exact (@lem1575511 term36). Qed.
Lemma lem1575513 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem1575514 : term225 = term229.
Proof. exact (MK_COMB (@lem1575513) (@lem1575512)). Qed.
Lemma lem1575515 : term229 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1575516 : term225 = term48.
Proof. exact (TRANS (@lem1575514) (@lem1575515)). Qed.
Lemma lem1575517 : term224 = term48.
Proof. exact (TRANS (@lem1575509) (@lem1575516)). Qed.
Lemma lem1575518 (x : real) : (term223 x) = term48.
Proof. exact (TRANS (@lem1575508 x) (@lem1575517)). Qed.
Lemma lem1575519 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575520 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1575519) (@lem1575518 x)). Qed.
Lemma lem1575521 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575522 (x : real) : (term213 x) = term232.
Proof. exact (MK_COMB (@lem1575520 x) (@lem1575521)). Qed.
Lemma lem1575523 (x : real) : (term212 x) = term232.
Proof. exact (TRANS (@lem1575481 x) (@lem1575522 x)). Qed.
Lemma lem1575524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575525 (x : real) (y : real) : (term256 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1575524) (@lem1575480 x y)). Qed.
Lemma lem1575526 (x : real) (y : real) : (term193 y x) = (term258 x y).
Proof. exact (MK_COMB (@lem1575525 x y) (@lem1575523 x)). Qed.
Lemma lem1575527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575528 (x : real) (y : real) : (term194 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1575527) (@lem1575447 x y)). Qed.
Lemma lem1575529 (x : real) (y : real) : (term196 y x) = (term259 x y).
Proof. exact (MK_COMB (@lem1575528 x y) (@lem1575526 x y)). Qed.
Lemma lem1575530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575531 (x : real) (y : real) : (term203 x y) = (term260 x y).
Proof. exact (MK_COMB (@lem1575530) (@lem1575428 x y)). Qed.
Lemma lem1575532 (x : real) (y : real) : (term204 y x) = (term261 x y).
Proof. exact (MK_COMB (@lem1575531 x y) (@lem1575529 x y)). Qed.
Lemma lem1575543 (x : real) (y : real) : (term188 x y) = (term261 x y).
Proof. exact (TRANS (@lem1575327 y x) (@lem1575532 x y)). Qed.
Lemma lem1575544 (x : real) (y : real) : (term54 y x) = (term261 x y).
Proof. exact (TRANS (@lem1575311 x y) (@lem1575543 x y)). Qed.
Lemma lem1575546 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1575547 (x : real) (y : real) : (term50 y x) = (term173 x y).
Proof. exact (@lem1575546 x (real_max y x) y term48). Qed.
Lemma lem1575560 (y : real) (x : real) : (term174 x y) = (term175 y x).
Proof. exact (@lem1483488 (term114 y) (real_max y x)). Qed.
Lemma lem1575561 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575562 (y : real) (x : real) : (term176 x y) = (term177 y x).
Proof. exact (MK_COMB (@lem1575561) (@lem1575560 y x)). Qed.
Lemma lem1575563 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575564 (y : real) (x : real) : (term178 x y) = (term179 y x).
Proof. exact (MK_COMB (@lem1575562 y x) (@lem1575563)). Qed.
Lemma lem1575577 (y : real) (x : real) : (term180 y x) = (term181 y x).
Proof. exact (@lem1483488 (term114 x) (real_max y x)). Qed.
Lemma lem1575578 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575579 (y : real) (x : real) : (term182 y x) = (term183 y x).
Proof. exact (MK_COMB (@lem1575578) (@lem1575577 y x)). Qed.
Lemma lem1575580 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575581 (y : real) (x : real) : (term184 y x) = (term185 y x).
Proof. exact (MK_COMB (@lem1575579 y x) (@lem1575580)). Qed.
Lemma lem1575582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575583 (y : real) (x : real) : (term186 y x) = (term187 y x).
Proof. exact (MK_COMB (@lem1575582) (@lem1575581 y x)). Qed.
Lemma lem1575584 (y : real) (x : real) : (term173 x y) = (term188 y x).
Proof. exact (MK_COMB (@lem1575583 y x) (@lem1575564 y x)). Qed.
Lemma lem1575585 (y : real) (x : real) : (term50 y x) = (term188 y x).
Proof. exact (TRANS (@lem1575547 x y) (@lem1575584 y x)). Qed.
Lemma lem1575586 (y : real) (x : real) : (term189 y x) = (term188 y x).
Proof. exact (eq_refl (term189 y x)). Qed.
Lemma lem1575587 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (SYM (@lem1575586 y x)). Qed.
Lemma lem1575588 (x : real) (y : real) : (term189 y x) = (term190 x y).
Proof. exact (@lem1483205 x (term191 x y) y). Qed.
Lemma lem1575589 (x : real) (y : real) : (term188 y x) = (term190 x y).
Proof. exact (TRANS (@lem1575587 y x) (@lem1575588 x y)). Qed.
Lemma lem1575590 (x : real) (y : real) : (term192 x y) = (term193 x y).
Proof. exact (eq_refl (term192 x y)). Qed.
Lemma lem1575591 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1575592 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1575591 y x) (@lem1575590 x y)). Qed.
Lemma lem1575593 (y : real) (x : real) : (term197 y x) = (term198 y x).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1575594 (x : real) (y : real) : (term199 x y) = (term199 x y).
Proof. exact (eq_refl (term199 x y)). Qed.
Lemma lem1575595 (y : real) (x : real) : (term200 y x) = (term201 y x).
Proof. exact (MK_COMB (@lem1575594 x y) (@lem1575593 y x)). Qed.
Lemma lem1575596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575597 (y : real) (x : real) : (term202 y x) = (term203 y x).
Proof. exact (MK_COMB (@lem1575596) (@lem1575595 y x)). Qed.
Lemma lem1575598 (x : real) (y : real) : (term190 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1575597 y x) (@lem1575592 x y)). Qed.
Lemma lem1575599 (y : real) (x : real) : (term205 y x) = (term205 y x).
Proof. exact (eq_refl (term205 y x)). Qed.
Lemma lem1575600 (x : real) (y : real) : ((term188 y x) = (term190 x y)) = ((term188 y x) = (term204 x y)).
Proof. exact (MK_COMB (@lem1575599 y x) (@lem1575598 x y)). Qed.
Lemma lem1575601 (x : real) (y : real) : (term188 y x) = (term204 x y).
Proof. exact (EQ_MP (@lem1575600 x y) (@lem1575589 x y)). Qed.
Lemma lem1575602 (x : real) (y : real) : (real_ge x y) = (term206 x y).
Proof. exact (@lem1483527 x y). Qed.
Lemma lem1575615 (x : real) (y : real) : (real_sub x y) = (term207 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1575616 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1575617 (x : real) (y : real) : (term209 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1575616) (@lem1575615 x y)). Qed.
Lemma lem1575618 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575619 (x : real) (y : real) : (term206 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1575617 x y) (@lem1575618)). Qed.
Lemma lem1575620 (x : real) (y : real) : (real_ge x y) = (term264 x y).
Proof. exact (TRANS (@lem1575602 x y) (@lem1575619 x y)). Qed.
Lemma lem1575621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575622 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1575621) (@lem1575523 x)). Qed.
Lemma lem1575623 (x : real) (y : real) : (term198 y x) = (term265 x y).
Proof. exact (MK_COMB (@lem1575622 x) (@lem1575480 x y)). Qed.
Lemma lem1575624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575625 (x : real) (y : real) : (term199 x y) = (term266 x y).
Proof. exact (MK_COMB (@lem1575624) (@lem1575620 x y)). Qed.
Lemma lem1575626 (x : real) (y : real) : (term201 y x) = (term267 x y).
Proof. exact (MK_COMB (@lem1575625 x y) (@lem1575623 x y)). Qed.
Lemma lem1575627 (y : real) (x : real) : (real_gt y x) = (term246 y x).
Proof. exact (@lem1483525 y x). Qed.
Lemma lem1575633 (y : real) (x : real) : (real_sub y x) = (term207 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1575638 (x : real) (y : real) : (term207 y x) = (term208 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1575640 (x : real) (y : real) : (real_sub y x) = (term208 x y).
Proof. exact (TRANS (@lem1575633 y x) (@lem1575638 x y)). Qed.
Lemma lem1575641 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575642 (x : real) (y : real) : (term247 y x) = (term240 x y).
Proof. exact (MK_COMB (@lem1575641) (@lem1575640 x y)). Qed.
Lemma lem1575643 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575644 (x : real) (y : real) : (term246 y x) = (term233 x y).
Proof. exact (MK_COMB (@lem1575642 x y) (@lem1575643)). Qed.
Lemma lem1575645 (x : real) (y : real) : (real_gt y x) = (term233 x y).
Proof. exact (TRANS (@lem1575627 y x) (@lem1575644 x y)). Qed.
Lemma lem1575646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575647 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1575646) (@lem1575422 x y)). Qed.
Lemma lem1575648 (x : real) (y : real) : (term193 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1575647 x y) (@lem1575389 y)). Qed.
Lemma lem1575649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575650 (x : real) (y : real) : (term194 y x) = (term256 x y).
Proof. exact (MK_COMB (@lem1575649) (@lem1575645 x y)). Qed.
Lemma lem1575651 (x : real) (y : real) : (term196 x y) = (term269 x y).
Proof. exact (MK_COMB (@lem1575650 x y) (@lem1575648 x y)). Qed.
Lemma lem1575652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575653 (x : real) (y : real) : (term203 y x) = (term270 x y).
Proof. exact (MK_COMB (@lem1575652) (@lem1575626 x y)). Qed.
Lemma lem1575654 (x : real) (y : real) : (term204 x y) = (term271 x y).
Proof. exact (MK_COMB (@lem1575653 x y) (@lem1575651 x y)). Qed.
Lemma lem1575665 (x : real) (y : real) : (term188 y x) = (term271 x y).
Proof. exact (TRANS (@lem1575601 x y) (@lem1575654 x y)). Qed.
Lemma lem1575666 (x : real) (y : real) : (term50 y x) = (term271 x y).
Proof. exact (TRANS (@lem1575585 y x) (@lem1575665 x y)). Qed.
Lemma lem1575667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575668 (x : real) (y : real) : (term56 y x) = (term272 x y).
Proof. exact (MK_COMB (@lem1575667) (@lem1575544 x y)). Qed.
Lemma lem1575669 (x : real) (y : real) : (term57 y x) = (term273 x y).
Proof. exact (MK_COMB (@lem1575668 x y) (@lem1575666 x y)). Qed.
Lemma lem1575671 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1575672 (x : real) (y : real) (z : real) : (term83 x y z) = (term274 x y z).
Proof. exact (@lem1575671 x (term13 x y z) (real_max y z) term48). Qed.
Lemma lem1575685 (x : real) (y : real) (z : real) : (term275 x y z) = (term276 x y z).
Proof. exact (@lem1483488 (term29 y z) (term13 x y z)). Qed.
Lemma lem1575686 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575687 (x : real) (y : real) (z : real) : (term277 x y z) = (term278 x y z).
Proof. exact (MK_COMB (@lem1575686) (@lem1575685 x y z)). Qed.
Lemma lem1575688 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575689 (x : real) (y : real) (z : real) : (term279 x y z) = (term280 x y z).
Proof. exact (MK_COMB (@lem1575687 x y z) (@lem1575688)). Qed.
Lemma lem1575702 (x : real) (y : real) (z : real) : (term281 y z x) = (term282 x y z).
Proof. exact (@lem1483488 (term114 x) (term13 x y z)). Qed.
Lemma lem1575703 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575704 (x : real) (y : real) (z : real) : (term283 y z x) = (term284 x y z).
Proof. exact (MK_COMB (@lem1575703) (@lem1575702 x y z)). Qed.
Lemma lem1575705 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575706 (x : real) (y : real) (z : real) : (term285 y z x) = (term286 x y z).
Proof. exact (MK_COMB (@lem1575704 x y z) (@lem1575705)). Qed.
Lemma lem1575707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575708 (x : real) (y : real) (z : real) : (term287 y z x) = (term288 x y z).
Proof. exact (MK_COMB (@lem1575707) (@lem1575706 x y z)). Qed.
Lemma lem1575709 (x : real) (y : real) (z : real) : (term274 x y z) = (term289 x y z).
Proof. exact (MK_COMB (@lem1575708 x y z) (@lem1575689 x y z)). Qed.
Lemma lem1575710 (x : real) (y : real) (z : real) : (term83 x y z) = (term289 x y z).
Proof. exact (TRANS (@lem1575672 x y z) (@lem1575709 x y z)). Qed.
Lemma lem1575712 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1575713 (x : real) (y : real) (z : real) : (term280 x y z) = (term290 x y z).
Proof. exact (@lem1575712 y (term13 x y z) z term48). Qed.
Lemma lem1575726 (x : real) (y : real) (z : real) : (term291 x y z) = (term292 x y z).
Proof. exact (@lem1483488 (term114 z) (term13 x y z)). Qed.
Lemma lem1575727 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575728 (x : real) (y : real) (z : real) : (term293 x y z) = (term294 x y z).
Proof. exact (MK_COMB (@lem1575727) (@lem1575726 x y z)). Qed.
Lemma lem1575729 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575730 (x : real) (y : real) (z : real) : (term295 x y z) = (term296 x y z).
Proof. exact (MK_COMB (@lem1575728 x y z) (@lem1575729)). Qed.
Lemma lem1575743 (x : real) (y : real) (z : real) : (term297 x z y) = (term298 x y z).
Proof. exact (@lem1483488 (term114 y) (term13 x y z)). Qed.
Lemma lem1575744 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575745 (x : real) (y : real) (z : real) : (term299 x z y) = (term300 x y z).
Proof. exact (MK_COMB (@lem1575744) (@lem1575743 x y z)). Qed.
Lemma lem1575746 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575747 (x : real) (y : real) (z : real) : (term301 x z y) = (term302 x y z).
Proof. exact (MK_COMB (@lem1575745 x y z) (@lem1575746)). Qed.
Lemma lem1575748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575749 (x : real) (y : real) (z : real) : (term303 x z y) = (term304 x y z).
Proof. exact (MK_COMB (@lem1575748) (@lem1575747 x y z)). Qed.
Lemma lem1575750 (x : real) (y : real) (z : real) : (term290 x y z) = (term305 x y z).
Proof. exact (MK_COMB (@lem1575749 x y z) (@lem1575730 x y z)). Qed.
Lemma lem1575751 (x : real) (y : real) (z : real) : (term280 x y z) = (term305 x y z).
Proof. exact (TRANS (@lem1575713 x y z) (@lem1575750 x y z)). Qed.
Lemma lem1575752 (x : real) (y : real) (z : real) : (term288 x y z) = (term288 x y z).
Proof. exact (eq_refl (term288 x y z)). Qed.
Lemma lem1575753 (x : real) (y : real) (z : real) : (term289 x y z) = (term306 x y z).
Proof. exact (MK_COMB (@lem1575752 x y z) (@lem1575751 x y z)). Qed.
Lemma lem1575754 (x : real) (y : real) (z : real) : (term83 x y z) = (term306 x y z).
Proof. exact (TRANS (@lem1575710 x y z) (@lem1575753 x y z)). Qed.
Lemma lem1575755 (x : real) (y : real) (z : real) : (term307 x y z) = (term306 x y z).
Proof. exact (eq_refl (term307 x y z)). Qed.
Lemma lem1575756 (x : real) (y : real) (z : real) : (term306 x y z) = (term307 x y z).
Proof. exact (SYM (@lem1575755 x y z)). Qed.
Lemma lem1575757 (z : real) (x : real) (y : real) : (term307 x y z) = (term308 z x y).
Proof. exact (@lem1483205 z (term309 x y z) (real_max x y)). Qed.
Lemma lem1575758 (z : real) (x : real) (y : real) : (term306 x y z) = (term308 z x y).
Proof. exact (TRANS (@lem1575756 x y z) (@lem1575757 z x y)). Qed.
Lemma lem1575759 (z : real) (x : real) (y : real) : (term310 z x y) = (term311 z x y).
Proof. exact (eq_refl (term310 z x y)). Qed.
Lemma lem1575760 (x : real) (y : real) (z : real) : (term312 x y z) = (term312 x y z).
Proof. exact (eq_refl (term312 x y z)). Qed.
Lemma lem1575761 (z : real) (x : real) (y : real) : (term313 z x y) = (term314 z x y).
Proof. exact (MK_COMB (@lem1575760 x y z) (@lem1575759 z x y)). Qed.
Lemma lem1575762 (x : real) (y : real) (z : real) : (term315 x y z) = (term316 x y z).
Proof. exact (eq_refl (term315 x y z)). Qed.
Lemma lem1575763 (z : real) (x : real) (y : real) : (term317 z x y) = (term317 z x y).
Proof. exact (eq_refl (term317 z x y)). Qed.
Lemma lem1575764 (x : real) (y : real) (z : real) : (term318 x y z) = (term319 x y z).
Proof. exact (MK_COMB (@lem1575763 z x y) (@lem1575762 x y z)). Qed.
Lemma lem1575765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1575766 (x : real) (y : real) (z : real) : (term320 x y z) = (term321 x y z).
Proof. exact (MK_COMB (@lem1575765) (@lem1575764 x y z)). Qed.
Lemma lem1575767 (z : real) (x : real) (y : real) : (term308 z x y) = (term322 z x y).
Proof. exact (MK_COMB (@lem1575766 x y z) (@lem1575761 z x y)). Qed.
Lemma lem1575768 (x : real) (y : real) (z : real) : (term323 x y z) = (term323 x y z).
Proof. exact (eq_refl (term323 x y z)). Qed.
Lemma lem1575769 (z : real) (x : real) (y : real) : ((term306 x y z) = (term308 z x y)) = ((term306 x y z) = (term322 z x y)).
Proof. exact (MK_COMB (@lem1575768 x y z) (@lem1575767 z x y)). Qed.
Lemma lem1575770 (z : real) (x : real) (y : real) : (term306 x y z) = (term322 z x y).
Proof. exact (EQ_MP (@lem1575769 z x y) (@lem1575758 z x y)). Qed.
Lemma lem1575771 (z : real) (x : real) (y : real) : (term324 z x y) = (term325 z x y).
Proof. exact (@lem1483527 z (real_max x y)). Qed.
Lemma lem1575784 (z : real) (x : real) (y : real) : (term326 z x y) = (term327 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1575785 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1575786 (z : real) (x : real) (y : real) : (term328 z x y) = (term329 z x y).
Proof. exact (MK_COMB (@lem1575785) (@lem1575784 z x y)). Qed.
Lemma lem1575787 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575788 (z : real) (x : real) (y : real) : (term325 z x y) = (term330 z x y).
Proof. exact (MK_COMB (@lem1575786 z x y) (@lem1575787)). Qed.
Lemma lem1575789 (z : real) (x : real) (y : real) : (term324 z x y) = (term330 z x y).
Proof. exact (TRANS (@lem1575771 z x y) (@lem1575788 z x y)). Qed.
Lemma lem1575790 (x : real) (z : real) : (term233 x z) = (term234 x z).
Proof. exact (@lem1483525 (term208 x z) term48). Qed.
Lemma lem1575808 (x : real) (z : real) : (term235 x z) = (term236 x z).
Proof. exact (@lem1483519 (term208 x z) term48). Qed.
Lemma lem1575810 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575811 : term227 = term48.
Proof. exact (@lem1575810 term36). Qed.
Lemma lem1575812 (x : real) (z : real) : (term237 x z) = (term237 x z).
Proof. exact (eq_refl (term237 x z)). Qed.
Lemma lem1575813 (x : real) (z : real) : (term236 x z) = (term238 x z).
Proof. exact (MK_COMB (@lem1575812 x z) (@lem1575811)). Qed.
Lemma lem1575814 (x : real) (z : real) : (term238 x z) = (term208 x z).
Proof. exact (@lem1483450 (term208 x z)). Qed.
Lemma lem1575815 (x : real) (z : real) : (term236 x z) = (term208 x z).
Proof. exact (TRANS (@lem1575813 x z) (@lem1575814 x z)). Qed.
Lemma lem1575817 (x : real) (z : real) : (term235 x z) = (term208 x z).
Proof. exact (TRANS (@lem1575808 x z) (@lem1575815 x z)). Qed.
Lemma lem1575818 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575819 (x : real) (z : real) : (term239 x z) = (term240 x z).
Proof. exact (MK_COMB (@lem1575818) (@lem1575817 x z)). Qed.
Lemma lem1575820 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575821 (x : real) (z : real) : (term234 x z) = (term233 x z).
Proof. exact (MK_COMB (@lem1575819 x z) (@lem1575820)). Qed.
Lemma lem1575822 (x : real) (z : real) : (term233 x z) = (term233 x z).
Proof. exact (TRANS (@lem1575790 x z) (@lem1575821 x z)). Qed.
Lemma lem1575823 (y : real) (z : real) : (term233 y z) = (term234 y z).
Proof. exact (@lem1483525 (term208 y z) term48). Qed.
Lemma lem1575841 (y : real) (z : real) : (term235 y z) = (term236 y z).
Proof. exact (@lem1483519 (term208 y z) term48). Qed.
Lemma lem1575843 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575844 : term227 = term48.
Proof. exact (@lem1575843 term36). Qed.
Lemma lem1575845 (y : real) (z : real) : (term237 y z) = (term237 y z).
Proof. exact (eq_refl (term237 y z)). Qed.
Lemma lem1575846 (y : real) (z : real) : (term236 y z) = (term238 y z).
Proof. exact (MK_COMB (@lem1575845 y z) (@lem1575844)). Qed.
Lemma lem1575847 (y : real) (z : real) : (term238 y z) = (term208 y z).
Proof. exact (@lem1483450 (term208 y z)). Qed.
Lemma lem1575848 (y : real) (z : real) : (term236 y z) = (term208 y z).
Proof. exact (TRANS (@lem1575846 y z) (@lem1575847 y z)). Qed.
Lemma lem1575850 (y : real) (z : real) : (term235 y z) = (term208 y z).
Proof. exact (TRANS (@lem1575841 y z) (@lem1575848 y z)). Qed.
Lemma lem1575851 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575852 (y : real) (z : real) : (term239 y z) = (term240 y z).
Proof. exact (MK_COMB (@lem1575851) (@lem1575850 y z)). Qed.
Lemma lem1575853 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575854 (y : real) (z : real) : (term234 y z) = (term233 y z).
Proof. exact (MK_COMB (@lem1575852 y z) (@lem1575853)). Qed.
Lemma lem1575855 (y : real) (z : real) : (term233 y z) = (term233 y z).
Proof. exact (TRANS (@lem1575823 y z) (@lem1575854 y z)). Qed.
Lemma lem1575856 (z : real) : (term212 z) = (term213 z).
Proof. exact (@lem1483525 (term214 z) term48). Qed.
Lemma lem1575857 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575869 (z : real) : (term214 z) = (term215 z).
Proof. exact (@lem1483440 term28 z). Qed.
Lemma lem1575871 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1575872 : term217 = term48.
Proof. exact (@lem1575871 term36). Qed.
Lemma lem1575873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1575874 : term218 = term219.
Proof. exact (MK_COMB (@lem1575873) (@lem1575872)). Qed.
Lemma lem1575875 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1575876 (z : real) : (term215 z) = (term220 z).
Proof. exact (MK_COMB (@lem1575874) (@lem1575875 z)). Qed.
Lemma lem1575877 (z : real) : (term214 z) = (term220 z).
Proof. exact (TRANS (@lem1575869 z) (@lem1575876 z)). Qed.
Lemma lem1575878 (z : real) : (term220 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1575880 (z : real) : (term214 z) = term48.
Proof. exact (TRANS (@lem1575877 z) (@lem1575878 z)). Qed.
Lemma lem1575881 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1575882 (z : real) : (term221 z) = term222.
Proof. exact (MK_COMB (@lem1575881) (@lem1575880 z)). Qed.
Lemma lem1575883 (z : real) : (term223 z) = term224.
Proof. exact (MK_COMB (@lem1575882 z) (@lem1575857)). Qed.
Lemma lem1575884 : term224 = term225.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1575886 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575887 : term227 = term48.
Proof. exact (@lem1575886 term36). Qed.
Lemma lem1575888 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem1575889 : term225 = term229.
Proof. exact (MK_COMB (@lem1575888) (@lem1575887)). Qed.
Lemma lem1575890 : term229 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1575891 : term225 = term48.
Proof. exact (TRANS (@lem1575889) (@lem1575890)). Qed.
Lemma lem1575892 : term224 = term48.
Proof. exact (TRANS (@lem1575884) (@lem1575891)). Qed.
Lemma lem1575893 (z : real) : (term223 z) = term48.
Proof. exact (TRANS (@lem1575883 z) (@lem1575892)). Qed.
Lemma lem1575894 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575895 (z : real) : (term230 z) = term231.
Proof. exact (MK_COMB (@lem1575894) (@lem1575893 z)). Qed.
Lemma lem1575896 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575897 (z : real) : (term213 z) = term232.
Proof. exact (MK_COMB (@lem1575895 z) (@lem1575896)). Qed.
Lemma lem1575898 (z : real) : (term212 z) = term232.
Proof. exact (TRANS (@lem1575856 z) (@lem1575897 z)). Qed.
Lemma lem1575899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575900 (y : real) (z : real) : (term256 y z) = (term256 y z).
Proof. exact (MK_COMB (@lem1575899) (@lem1575855 y z)). Qed.
Lemma lem1575901 (y : real) (z : real) : (term193 y z) = (term268 y z).
Proof. exact (MK_COMB (@lem1575900 y z) (@lem1575898 z)). Qed.
Lemma lem1575902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575903 (x : real) (z : real) : (term256 x z) = (term256 x z).
Proof. exact (MK_COMB (@lem1575902) (@lem1575822 x z)). Qed.
Lemma lem1575904 (x : real) (y : real) (z : real) : (term316 x y z) = (term331 x y z).
Proof. exact (MK_COMB (@lem1575903 x z) (@lem1575901 y z)). Qed.
Lemma lem1575905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1575906 (z : real) (x : real) (y : real) : (term317 z x y) = (term332 z x y).
Proof. exact (MK_COMB (@lem1575905) (@lem1575789 z x y)). Qed.
Lemma lem1575907 (x : real) (y : real) (z : real) : (term319 x y z) = (term333 x y z).
Proof. exact (MK_COMB (@lem1575906 z x y) (@lem1575904 x y z)). Qed.
Lemma lem1575908 (x : real) (y : real) (z : real) : (term334 x y z) = (term335 x y z).
Proof. exact (@lem1483525 (real_max x y) z). Qed.
Lemma lem1575914 (x : real) (y : real) (z : real) : (term336 x y z) = (term337 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1575919 (z : real) (x : real) (y : real) : (term337 x y z) = (term338 z x y).
Proof. exact (@lem1483488 (term114 z) (real_max x y)). Qed.
Lemma lem1575921 (z : real) (x : real) (y : real) : (term336 x y z) = (term338 z x y).
Proof. exact (TRANS (@lem1575914 x y z) (@lem1575919 z x y)). Qed.
Lemma lem1575922 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575923 (z : real) (x : real) (y : real) : (term339 x y z) = (term340 z x y).
Proof. exact (MK_COMB (@lem1575922) (@lem1575921 z x y)). Qed.
Lemma lem1575924 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575925 (z : real) (x : real) (y : real) : (term335 x y z) = (term341 z x y).
Proof. exact (MK_COMB (@lem1575923 z x y) (@lem1575924)). Qed.
Lemma lem1575926 (z : real) (x : real) (y : real) : (term334 x y z) = (term341 z x y).
Proof. exact (TRANS (@lem1575908 x y z) (@lem1575925 z x y)). Qed.
Lemma lem1575927 (x : real) (y : real) : (term179 x y) = (term342 x y).
Proof. exact (@lem1483525 (term175 x y) term48). Qed.
Lemma lem1575945 (x : real) (y : real) : (term343 x y) = (term344 x y).
Proof. exact (@lem1483519 (term175 x y) term48). Qed.
Lemma lem1575947 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575948 : term227 = term48.
Proof. exact (@lem1575947 term36). Qed.
Lemma lem1575949 (x : real) (y : real) : (term345 x y) = (term345 x y).
Proof. exact (eq_refl (term345 x y)). Qed.
Lemma lem1575950 (x : real) (y : real) : (term344 x y) = (term346 x y).
Proof. exact (MK_COMB (@lem1575949 x y) (@lem1575948)). Qed.
Lemma lem1575951 (x : real) (y : real) : (term346 x y) = (term175 x y).
Proof. exact (@lem1483450 (term175 x y)). Qed.
Lemma lem1575952 (x : real) (y : real) : (term344 x y) = (term175 x y).
Proof. exact (TRANS (@lem1575950 x y) (@lem1575951 x y)). Qed.
Lemma lem1575954 (x : real) (y : real) : (term343 x y) = (term175 x y).
Proof. exact (TRANS (@lem1575945 x y) (@lem1575952 x y)). Qed.
Lemma lem1575955 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575956 (x : real) (y : real) : (term347 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem1575955) (@lem1575954 x y)). Qed.
Lemma lem1575957 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575958 (x : real) (y : real) : (term342 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1575956 x y) (@lem1575957)). Qed.
Lemma lem1575959 (x : real) (y : real) : (term179 x y) = (term179 x y).
Proof. exact (TRANS (@lem1575927 x y) (@lem1575958 x y)). Qed.
Lemma lem1575960 (x : real) (y : real) : (term185 x y) = (term348 x y).
Proof. exact (@lem1483525 (term181 x y) term48). Qed.
Lemma lem1575978 (x : real) (y : real) : (term349 x y) = (term350 x y).
Proof. exact (@lem1483519 (term181 x y) term48). Qed.
Lemma lem1575980 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1575981 : term227 = term48.
Proof. exact (@lem1575980 term36). Qed.
Lemma lem1575982 (x : real) (y : real) : (term351 x y) = (term351 x y).
Proof. exact (eq_refl (term351 x y)). Qed.
Lemma lem1575983 (x : real) (y : real) : (term350 x y) = (term352 x y).
Proof. exact (MK_COMB (@lem1575982 x y) (@lem1575981)). Qed.
Lemma lem1575984 (x : real) (y : real) : (term352 x y) = (term181 x y).
Proof. exact (@lem1483450 (term181 x y)). Qed.
Lemma lem1575985 (x : real) (y : real) : (term350 x y) = (term181 x y).
Proof. exact (TRANS (@lem1575983 x y) (@lem1575984 x y)). Qed.
Lemma lem1575987 (x : real) (y : real) : (term349 x y) = (term181 x y).
Proof. exact (TRANS (@lem1575978 x y) (@lem1575985 x y)). Qed.
Lemma lem1575988 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1575989 (x : real) (y : real) : (term353 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1575988) (@lem1575987 x y)). Qed.
Lemma lem1575990 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1575991 (x : real) (y : real) : (term348 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1575989 x y) (@lem1575990)). Qed.
Lemma lem1575992 (x : real) (y : real) : (term185 x y) = (term185 x y).
Proof. exact (TRANS (@lem1575960 x y) (@lem1575991 x y)). Qed.
Lemma lem1575993 (z : real) (x : real) (y : real) : (term341 z x y) = (term354 z x y).
Proof. exact (@lem1483525 (term338 z x y) term48). Qed.
Lemma lem1576011 (z : real) (x : real) (y : real) : (term355 z x y) = (term356 z x y).
Proof. exact (@lem1483519 (term338 z x y) term48). Qed.
Lemma lem1576013 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576014 : term227 = term48.
Proof. exact (@lem1576013 term36). Qed.
Lemma lem1576015 (z : real) (x : real) (y : real) : (term357 z x y) = (term357 z x y).
Proof. exact (eq_refl (term357 z x y)). Qed.
Lemma lem1576016 (z : real) (x : real) (y : real) : (term356 z x y) = (term358 z x y).
Proof. exact (MK_COMB (@lem1576015 z x y) (@lem1576014)). Qed.
Lemma lem1576017 (z : real) (x : real) (y : real) : (term358 z x y) = (term338 z x y).
Proof. exact (@lem1483450 (term338 z x y)). Qed.
Lemma lem1576018 (z : real) (x : real) (y : real) : (term356 z x y) = (term338 z x y).
Proof. exact (TRANS (@lem1576016 z x y) (@lem1576017 z x y)). Qed.
Lemma lem1576020 (z : real) (x : real) (y : real) : (term355 z x y) = (term338 z x y).
Proof. exact (TRANS (@lem1576011 z x y) (@lem1576018 z x y)). Qed.
Lemma lem1576021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576022 (z : real) (x : real) (y : real) : (term359 z x y) = (term340 z x y).
Proof. exact (MK_COMB (@lem1576021) (@lem1576020 z x y)). Qed.
Lemma lem1576023 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576024 (z : real) (x : real) (y : real) : (term354 z x y) = (term341 z x y).
Proof. exact (MK_COMB (@lem1576022 z x y) (@lem1576023)). Qed.
Lemma lem1576025 (z : real) (x : real) (y : real) : (term341 z x y) = (term341 z x y).
Proof. exact (TRANS (@lem1575993 z x y) (@lem1576024 z x y)). Qed.
Lemma lem1576026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576027 (x : real) (y : real) : (term187 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1576026) (@lem1575992 x y)). Qed.
Lemma lem1576028 (z : real) (x : real) (y : real) : (term360 z x y) = (term360 z x y).
Proof. exact (MK_COMB (@lem1576027 x y) (@lem1576025 z x y)). Qed.
Lemma lem1576029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576030 (x : real) (y : real) : (term361 x y) = (term361 x y).
Proof. exact (MK_COMB (@lem1576029) (@lem1575959 x y)). Qed.
Lemma lem1576031 (z : real) (x : real) (y : real) : (term311 z x y) = (term311 z x y).
Proof. exact (MK_COMB (@lem1576030 x y) (@lem1576028 z x y)). Qed.
Lemma lem1576032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576033 (z : real) (x : real) (y : real) : (term312 x y z) = (term362 z x y).
Proof. exact (MK_COMB (@lem1576032) (@lem1575926 z x y)). Qed.
Lemma lem1576034 (z : real) (x : real) (y : real) : (term314 z x y) = (term363 z x y).
Proof. exact (MK_COMB (@lem1576033 z x y) (@lem1576031 z x y)). Qed.
Lemma lem1576035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576036 (x : real) (y : real) (z : real) : (term321 x y z) = (term364 x y z).
Proof. exact (MK_COMB (@lem1576035) (@lem1575907 x y z)). Qed.
Lemma lem1576037 (z : real) (x : real) (y : real) : (term322 z x y) = (term365 z x y).
Proof. exact (MK_COMB (@lem1576036 x y z) (@lem1576034 z x y)). Qed.
Lemma lem1576038 (z : real) (x : real) (y : real) : (term306 x y z) = (term365 z x y).
Proof. exact (TRANS (@lem1575770 z x y) (@lem1576037 z x y)). Qed.
Lemma lem1576040 (z : real) (x : real) (y : real) : (term366 z x y) = (term363 z x y).
Proof. exact (eq_refl (term366 z x y)). Qed.
Lemma lem1576041 (z : real) (x : real) (y : real) : (term363 z x y) = (term366 z x y).
Proof. exact (SYM (@lem1576040 z x y)). Qed.
Lemma lem1576042 (y : real) (z : real) (x : real) : (term366 z x y) = (term367 y z x).
Proof. exact (@lem1483205 y (term368 x y z) x). Qed.
Lemma lem1576043 (y : real) (z : real) (x : real) : (term363 z x y) = (term367 y z x).
Proof. exact (TRANS (@lem1576041 z x y) (@lem1576042 y z x)). Qed.
Lemma lem1576044 (y : real) (z : real) (x : real) : (term369 y z x) = (term370 y z x).
Proof. exact (eq_refl (term369 y z x)). Qed.
Lemma lem1576045 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1576046 (y : real) (z : real) (x : real) : (term371 y z x) = (term372 y z x).
Proof. exact (MK_COMB (@lem1576045 x y) (@lem1576044 y z x)). Qed.
Lemma lem1576047 (x : real) (z : real) (y : real) : (term373 x z y) = (term374 x z y).
Proof. exact (eq_refl (term373 x z y)). Qed.
Lemma lem1576048 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1576049 (x : real) (z : real) (y : real) : (term375 x z y) = (term376 x z y).
Proof. exact (MK_COMB (@lem1576048 y x) (@lem1576047 x z y)). Qed.
Lemma lem1576050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576051 (x : real) (z : real) (y : real) : (term377 x z y) = (term378 x z y).
Proof. exact (MK_COMB (@lem1576050) (@lem1576049 x z y)). Qed.
Lemma lem1576052 (y : real) (z : real) (x : real) : (term367 y z x) = (term379 y z x).
Proof. exact (MK_COMB (@lem1576051 x z y) (@lem1576046 y z x)). Qed.
Lemma lem1576053 (z : real) (x : real) (y : real) : (term380 z x y) = (term380 z x y).
Proof. exact (eq_refl (term380 z x y)). Qed.
Lemma lem1576054 (y : real) (z : real) (x : real) : ((term363 z x y) = (term367 y z x)) = ((term363 z x y) = (term379 y z x)).
Proof. exact (MK_COMB (@lem1576053 z x y) (@lem1576052 y z x)). Qed.
Lemma lem1576055 (y : real) (z : real) (x : real) : (term363 z x y) = (term379 y z x).
Proof. exact (EQ_MP (@lem1576054 y z x) (@lem1576043 y z x)). Qed.
Lemma lem1576056 (z : real) (y : real) : (term233 z y) = (term234 z y).
Proof. exact (@lem1483525 (term208 z y) term48). Qed.
Lemma lem1576057 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576070 (y : real) (z : real) : (term208 z y) = (term207 y z).
Proof. exact (@lem1483488 y (term114 z)). Qed.
Lemma lem1576071 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1576072 (y : real) (z : real) : (term250 z y) = (term251 y z).
Proof. exact (MK_COMB (@lem1576071) (@lem1576070 y z)). Qed.
Lemma lem1576073 (y : real) (z : real) : (term235 z y) = (term252 y z).
Proof. exact (MK_COMB (@lem1576072 y z) (@lem1576057)). Qed.
Lemma lem1576074 (y : real) (z : real) : (term252 y z) = (term253 y z).
Proof. exact (@lem1483519 (term207 y z) term48). Qed.
Lemma lem1576076 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576077 : term227 = term48.
Proof. exact (@lem1576076 term36). Qed.
Lemma lem1576078 (y : real) (z : real) : (term254 y z) = (term254 y z).
Proof. exact (eq_refl (term254 y z)). Qed.
Lemma lem1576079 (y : real) (z : real) : (term253 y z) = (term255 y z).
Proof. exact (MK_COMB (@lem1576078 y z) (@lem1576077)). Qed.
Lemma lem1576080 (y : real) (z : real) : (term255 y z) = (term207 y z).
Proof. exact (@lem1483450 (term207 y z)). Qed.
Lemma lem1576081 (y : real) (z : real) : (term253 y z) = (term207 y z).
Proof. exact (TRANS (@lem1576079 y z) (@lem1576080 y z)). Qed.
Lemma lem1576082 (y : real) (z : real) : (term252 y z) = (term207 y z).
Proof. exact (TRANS (@lem1576074 y z) (@lem1576081 y z)). Qed.
Lemma lem1576083 (y : real) (z : real) : (term235 z y) = (term207 y z).
Proof. exact (TRANS (@lem1576073 y z) (@lem1576082 y z)). Qed.
Lemma lem1576084 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576085 (y : real) (z : real) : (term239 z y) = (term248 y z).
Proof. exact (MK_COMB (@lem1576084) (@lem1576083 y z)). Qed.
Lemma lem1576086 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576087 (y : real) (z : real) : (term234 z y) = (term249 y z).
Proof. exact (MK_COMB (@lem1576085 y z) (@lem1576086)). Qed.
Lemma lem1576088 (y : real) (z : real) : (term233 z y) = (term249 y z).
Proof. exact (TRANS (@lem1576056 z y) (@lem1576087 y z)). Qed.
Lemma lem1576089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576090 (y : real) : (term241 y) = term242.
Proof. exact (MK_COMB (@lem1576089) (@lem1575389 y)). Qed.
Lemma lem1576091 (y : real) (z : real) : (term198 z y) = (term265 y z).
Proof. exact (MK_COMB (@lem1576090 y) (@lem1576088 y z)). Qed.
Lemma lem1576092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576093 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1576092) (@lem1575422 x y)). Qed.
Lemma lem1576094 (x : real) (y : real) (z : real) : (term381 x z y) = (term382 x y z).
Proof. exact (MK_COMB (@lem1576093 x y) (@lem1576091 y z)). Qed.
Lemma lem1576095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576096 (y : real) (z : real) : (term256 z y) = (term257 y z).
Proof. exact (MK_COMB (@lem1576095) (@lem1576088 y z)). Qed.
Lemma lem1576097 (x : real) (y : real) (z : real) : (term374 x z y) = (term383 x y z).
Proof. exact (MK_COMB (@lem1576096 y z) (@lem1576094 x y z)). Qed.
Lemma lem1576098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576099 (x : real) (y : real) : (term199 y x) = (term244 x y).
Proof. exact (MK_COMB (@lem1576098) (@lem1575346 x y)). Qed.
Lemma lem1576100 (x : real) (y : real) (z : real) : (term376 x z y) = (term384 x y z).
Proof. exact (MK_COMB (@lem1576099 x y) (@lem1576097 x y z)). Qed.
Lemma lem1576101 (z : real) (x : real) : (term233 z x) = (term234 z x).
Proof. exact (@lem1483525 (term208 z x) term48). Qed.
Lemma lem1576102 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576115 (x : real) (z : real) : (term208 z x) = (term207 x z).
Proof. exact (@lem1483488 x (term114 z)). Qed.
Lemma lem1576116 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1576117 (x : real) (z : real) : (term250 z x) = (term251 x z).
Proof. exact (MK_COMB (@lem1576116) (@lem1576115 x z)). Qed.
Lemma lem1576118 (x : real) (z : real) : (term235 z x) = (term252 x z).
Proof. exact (MK_COMB (@lem1576117 x z) (@lem1576102)). Qed.
Lemma lem1576119 (x : real) (z : real) : (term252 x z) = (term253 x z).
Proof. exact (@lem1483519 (term207 x z) term48). Qed.
Lemma lem1576121 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576122 : term227 = term48.
Proof. exact (@lem1576121 term36). Qed.
Lemma lem1576123 (x : real) (z : real) : (term254 x z) = (term254 x z).
Proof. exact (eq_refl (term254 x z)). Qed.
Lemma lem1576124 (x : real) (z : real) : (term253 x z) = (term255 x z).
Proof. exact (MK_COMB (@lem1576123 x z) (@lem1576122)). Qed.
Lemma lem1576125 (x : real) (z : real) : (term255 x z) = (term207 x z).
Proof. exact (@lem1483450 (term207 x z)). Qed.
Lemma lem1576126 (x : real) (z : real) : (term253 x z) = (term207 x z).
Proof. exact (TRANS (@lem1576124 x z) (@lem1576125 x z)). Qed.
Lemma lem1576127 (x : real) (z : real) : (term252 x z) = (term207 x z).
Proof. exact (TRANS (@lem1576119 x z) (@lem1576126 x z)). Qed.
Lemma lem1576128 (x : real) (z : real) : (term235 z x) = (term207 x z).
Proof. exact (TRANS (@lem1576118 x z) (@lem1576127 x z)). Qed.
Lemma lem1576129 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576130 (x : real) (z : real) : (term239 z x) = (term248 x z).
Proof. exact (MK_COMB (@lem1576129) (@lem1576128 x z)). Qed.
Lemma lem1576131 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576132 (x : real) (z : real) : (term234 z x) = (term249 x z).
Proof. exact (MK_COMB (@lem1576130 x z) (@lem1576131)). Qed.
Lemma lem1576133 (x : real) (z : real) : (term233 z x) = (term249 x z).
Proof. exact (TRANS (@lem1576101 z x) (@lem1576132 x z)). Qed.
Lemma lem1576134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576135 (x : real) (y : real) : (term256 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1576134) (@lem1575480 x y)). Qed.
Lemma lem1576136 (y : real) (x : real) (z : real) : (term385 y z x) = (term386 y x z).
Proof. exact (MK_COMB (@lem1576135 x y) (@lem1576133 x z)). Qed.
Lemma lem1576137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576138 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1576137) (@lem1575523 x)). Qed.
Lemma lem1576139 (y : real) (x : real) (z : real) : (term387 y z x) = (term388 y x z).
Proof. exact (MK_COMB (@lem1576138 x) (@lem1576136 y x z)). Qed.
Lemma lem1576140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576141 (x : real) (z : real) : (term256 z x) = (term257 x z).
Proof. exact (MK_COMB (@lem1576140) (@lem1576133 x z)). Qed.
Lemma lem1576142 (y : real) (x : real) (z : real) : (term370 y z x) = (term389 y x z).
Proof. exact (MK_COMB (@lem1576141 x z) (@lem1576139 y x z)). Qed.
Lemma lem1576143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576144 (x : real) (y : real) : (term194 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1576143) (@lem1575447 x y)). Qed.
Lemma lem1576145 (y : real) (x : real) (z : real) : (term372 y z x) = (term390 y x z).
Proof. exact (MK_COMB (@lem1576144 x y) (@lem1576142 y x z)). Qed.
Lemma lem1576146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576147 (x : real) (y : real) (z : real) : (term378 x z y) = (term391 x y z).
Proof. exact (MK_COMB (@lem1576146) (@lem1576100 x y z)). Qed.
Lemma lem1576148 (y : real) (x : real) (z : real) : (term379 y z x) = (term392 y x z).
Proof. exact (MK_COMB (@lem1576147 x y z) (@lem1576145 y x z)). Qed.
Lemma lem1576160 (y : real) (x : real) (z : real) : (term363 z x y) = (term392 y x z).
Proof. exact (TRANS (@lem1576055 y z x) (@lem1576148 y x z)). Qed.
Lemma lem1576162 (x : real) (a : real) (y : real) (r : real) : (term393 a x y r) = (term394 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576163 (x : real) (z : real) (y : real) : (term330 z x y) = (term395 x z y).
Proof. exact (@lem1576162 x z y term48). Qed.
Lemma lem1576176 (y : real) (z : real) : (term207 z y) = (term208 y z).
Proof. exact (@lem1483488 (term114 y) z). Qed.
Lemma lem1576177 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576178 (y : real) (z : real) : (term263 z y) = (term210 y z).
Proof. exact (MK_COMB (@lem1576177) (@lem1576176 y z)). Qed.
Lemma lem1576179 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576180 (y : real) (z : real) : (term264 z y) = (term211 y z).
Proof. exact (MK_COMB (@lem1576178 y z) (@lem1576179)). Qed.
Lemma lem1576193 (x : real) (z : real) : (term207 z x) = (term208 x z).
Proof. exact (@lem1483488 (term114 x) z). Qed.
Lemma lem1576194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576195 (x : real) (z : real) : (term263 z x) = (term210 x z).
Proof. exact (MK_COMB (@lem1576194) (@lem1576193 x z)). Qed.
Lemma lem1576196 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576197 (x : real) (z : real) : (term264 z x) = (term211 x z).
Proof. exact (MK_COMB (@lem1576195 x z) (@lem1576196)). Qed.
Lemma lem1576198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576199 (x : real) (z : real) : (term266 z x) = (term244 x z).
Proof. exact (MK_COMB (@lem1576198) (@lem1576197 x z)). Qed.
Lemma lem1576200 (x : real) (y : real) (z : real) : (term395 x z y) = (term396 x y z).
Proof. exact (MK_COMB (@lem1576199 x z) (@lem1576180 y z)). Qed.
Lemma lem1576201 (x : real) (y : real) (z : real) : (term330 z x y) = (term396 x y z).
Proof. exact (TRANS (@lem1576163 x z y) (@lem1576200 x y z)). Qed.
Lemma lem1576202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576203 (x : real) (y : real) (z : real) : (term332 z x y) = (term397 x y z).
Proof. exact (MK_COMB (@lem1576202) (@lem1576201 x y z)). Qed.
Lemma lem1576204 (x : real) (y : real) (z : real) : (term331 x y z) = (term331 x y z).
Proof. exact (eq_refl (term331 x y z)). Qed.
Lemma lem1576207 (x : real) (y : real) (z : real) : (term333 x y z) = (term398 x y z).
Proof. exact (MK_COMB (@lem1576203 x y z) (@lem1576204 x y z)). Qed.
Lemma lem1576208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576209 (x : real) (y : real) (z : real) : (term364 x y z) = (term399 x y z).
Proof. exact (MK_COMB (@lem1576208) (@lem1576207 x y z)). Qed.
Lemma lem1576210 (y : real) (x : real) (z : real) : (term365 z x y) = (term400 y x z).
Proof. exact (MK_COMB (@lem1576209 x y z) (@lem1576160 y x z)). Qed.
Lemma lem1576211 (y : real) (x : real) (z : real) : (term306 x y z) = (term400 y x z).
Proof. exact (TRANS (@lem1576038 z x y) (@lem1576210 y x z)). Qed.
Lemma lem1576212 (y : real) (x : real) (z : real) : (term83 x y z) = (term400 y x z).
Proof. exact (TRANS (@lem1575754 x y z) (@lem1576211 y x z)). Qed.
Lemma lem1576214 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576215 (x : real) (y : real) (z : real) : (term79 x y z) = (term401 x y z).
Proof. exact (@lem1576214 (real_max x y) (term7 x y z) z term48). Qed.
Lemma lem1576228 (x : real) (y : real) (z : real) : (term402 x y z) = (term403 x y z).
Proof. exact (@lem1483488 (term114 z) (term7 x y z)). Qed.
Lemma lem1576229 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576230 (x : real) (y : real) (z : real) : (term404 x y z) = (term405 x y z).
Proof. exact (MK_COMB (@lem1576229) (@lem1576228 x y z)). Qed.
Lemma lem1576231 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576232 (x : real) (y : real) (z : real) : (term406 x y z) = (term407 x y z).
Proof. exact (MK_COMB (@lem1576230 x y z) (@lem1576231)). Qed.
Lemma lem1576245 (x : real) (y : real) (z : real) : (term408 z x y) = (term409 x y z).
Proof. exact (@lem1483488 (term29 x y) (term7 x y z)). Qed.
Lemma lem1576246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576247 (x : real) (y : real) (z : real) : (term410 z x y) = (term411 x y z).
Proof. exact (MK_COMB (@lem1576246) (@lem1576245 x y z)). Qed.
Lemma lem1576248 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576249 (x : real) (y : real) (z : real) : (term412 z x y) = (term413 x y z).
Proof. exact (MK_COMB (@lem1576247 x y z) (@lem1576248)). Qed.
Lemma lem1576250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576251 (x : real) (y : real) (z : real) : (term414 z x y) = (term415 x y z).
Proof. exact (MK_COMB (@lem1576250) (@lem1576249 x y z)). Qed.
Lemma lem1576252 (x : real) (y : real) (z : real) : (term401 x y z) = (term416 x y z).
Proof. exact (MK_COMB (@lem1576251 x y z) (@lem1576232 x y z)). Qed.
Lemma lem1576253 (x : real) (y : real) (z : real) : (term79 x y z) = (term416 x y z).
Proof. exact (TRANS (@lem1576215 x y z) (@lem1576252 x y z)). Qed.
Lemma lem1576255 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576256 (x : real) (z : real) (y : real) : (term413 x y z) = (term417 x z y).
Proof. exact (@lem1576255 x (term7 x y z) y term48). Qed.
Lemma lem1576269 (x : real) (y : real) (z : real) : (term418 x z y) = (term419 x y z).
Proof. exact (@lem1483488 (term114 y) (term7 x y z)). Qed.
Lemma lem1576270 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576271 (x : real) (y : real) (z : real) : (term420 x z y) = (term421 x y z).
Proof. exact (MK_COMB (@lem1576270) (@lem1576269 x y z)). Qed.
Lemma lem1576272 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576273 (x : real) (y : real) (z : real) : (term422 x z y) = (term423 x y z).
Proof. exact (MK_COMB (@lem1576271 x y z) (@lem1576272)). Qed.
Lemma lem1576286 (x : real) (y : real) (z : real) : (term424 y z x) = (term425 x y z).
Proof. exact (@lem1483488 (term114 x) (term7 x y z)). Qed.
Lemma lem1576287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576288 (x : real) (y : real) (z : real) : (term426 y z x) = (term427 x y z).
Proof. exact (MK_COMB (@lem1576287) (@lem1576286 x y z)). Qed.
Lemma lem1576289 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576290 (x : real) (y : real) (z : real) : (term428 y z x) = (term429 x y z).
Proof. exact (MK_COMB (@lem1576288 x y z) (@lem1576289)). Qed.
Lemma lem1576291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576292 (x : real) (y : real) (z : real) : (term430 y z x) = (term431 x y z).
Proof. exact (MK_COMB (@lem1576291) (@lem1576290 x y z)). Qed.
Lemma lem1576293 (x : real) (y : real) (z : real) : (term417 x z y) = (term432 x y z).
Proof. exact (MK_COMB (@lem1576292 x y z) (@lem1576273 x y z)). Qed.
Lemma lem1576294 (x : real) (y : real) (z : real) : (term413 x y z) = (term432 x y z).
Proof. exact (TRANS (@lem1576256 x z y) (@lem1576293 x y z)). Qed.
Lemma lem1576295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576296 (x : real) (y : real) (z : real) : (term415 x y z) = (term433 x y z).
Proof. exact (MK_COMB (@lem1576295) (@lem1576294 x y z)). Qed.
Lemma lem1576297 (x : real) (y : real) (z : real) : (term407 x y z) = (term407 x y z).
Proof. exact (eq_refl (term407 x y z)). Qed.
Lemma lem1576298 (x : real) (y : real) (z : real) : (term416 x y z) = (term434 x y z).
Proof. exact (MK_COMB (@lem1576296 x y z) (@lem1576297 x y z)). Qed.
Lemma lem1576299 (x : real) (y : real) (z : real) : (term79 x y z) = (term434 x y z).
Proof. exact (TRANS (@lem1576253 x y z) (@lem1576298 x y z)). Qed.
Lemma lem1576300 (x : real) (y : real) (z : real) : (term435 x y z) = (term434 x y z).
Proof. exact (eq_refl (term435 x y z)). Qed.
Lemma lem1576301 (x : real) (y : real) (z : real) : (term434 x y z) = (term435 x y z).
Proof. exact (SYM (@lem1576300 x y z)). Qed.
Lemma lem1576302 (y : real) (z : real) (x : real) : (term435 x y z) = (term436 y z x).
Proof. exact (@lem1483205 (real_max y z) (term437 x y z) x). Qed.
Lemma lem1576303 (y : real) (z : real) (x : real) : (term434 x y z) = (term436 y z x).
Proof. exact (TRANS (@lem1576301 x y z) (@lem1576302 y z x)). Qed.
Lemma lem1576304 (y : real) (z : real) (x : real) : (term438 y z x) = (term439 y z x).
Proof. exact (eq_refl (term438 y z x)). Qed.
Lemma lem1576305 (x : real) (y : real) (z : real) : (term440 x y z) = (term440 x y z).
Proof. exact (eq_refl (term440 x y z)). Qed.
Lemma lem1576306 (y : real) (z : real) (x : real) : (term441 y z x) = (term442 y z x).
Proof. exact (MK_COMB (@lem1576305 x y z) (@lem1576304 y z x)). Qed.
Lemma lem1576307 (x : real) (y : real) (z : real) : (term443 x y z) = (term444 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1576308 (y : real) (z : real) (x : real) : (term445 y z x) = (term445 y z x).
Proof. exact (eq_refl (term445 y z x)). Qed.
Lemma lem1576309 (x : real) (y : real) (z : real) : (term446 x y z) = (term447 x y z).
Proof. exact (MK_COMB (@lem1576308 y z x) (@lem1576307 x y z)). Qed.
Lemma lem1576310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576311 (x : real) (y : real) (z : real) : (term448 x y z) = (term449 x y z).
Proof. exact (MK_COMB (@lem1576310) (@lem1576309 x y z)). Qed.
Lemma lem1576312 (y : real) (z : real) (x : real) : (term436 y z x) = (term450 y z x).
Proof. exact (MK_COMB (@lem1576311 x y z) (@lem1576306 y z x)). Qed.
Lemma lem1576313 (x : real) (y : real) (z : real) : (term451 x y z) = (term451 x y z).
Proof. exact (eq_refl (term451 x y z)). Qed.
Lemma lem1576314 (y : real) (z : real) (x : real) : ((term434 x y z) = (term436 y z x)) = ((term434 x y z) = (term450 y z x)).
Proof. exact (MK_COMB (@lem1576313 x y z) (@lem1576312 y z x)). Qed.
Lemma lem1576315 (y : real) (z : real) (x : real) : (term434 x y z) = (term450 y z x).
Proof. exact (EQ_MP (@lem1576314 y z x) (@lem1576303 y z x)). Qed.
Lemma lem1576316 (y : real) (z : real) (x : real) : (term452 y z x) = (term453 y z x).
Proof. exact (@lem1483527 (real_max y z) x). Qed.
Lemma lem1576322 (y : real) (z : real) (x : real) : (term336 y z x) = (term337 y z x).
Proof. exact (@lem1483519 (real_max y z) x). Qed.
Lemma lem1576327 (x : real) (y : real) (z : real) : (term337 y z x) = (term338 x y z).
Proof. exact (@lem1483488 (term114 x) (real_max y z)). Qed.
Lemma lem1576329 (x : real) (y : real) (z : real) : (term336 y z x) = (term338 x y z).
Proof. exact (TRANS (@lem1576322 y z x) (@lem1576327 x y z)). Qed.
Lemma lem1576330 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576331 (x : real) (y : real) (z : real) : (term454 y z x) = (term455 x y z).
Proof. exact (MK_COMB (@lem1576330) (@lem1576329 x y z)). Qed.
Lemma lem1576332 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576333 (x : real) (y : real) (z : real) : (term453 y z x) = (term456 x y z).
Proof. exact (MK_COMB (@lem1576331 x y z) (@lem1576332)). Qed.
Lemma lem1576334 (x : real) (y : real) (z : real) : (term452 y z x) = (term456 x y z).
Proof. exact (TRANS (@lem1576316 y z x) (@lem1576333 x y z)). Qed.
Lemma lem1576335 (x : real) (y : real) (z : real) : (term341 x y z) = (term354 x y z).
Proof. exact (@lem1483525 (term338 x y z) term48). Qed.
Lemma lem1576353 (x : real) (y : real) (z : real) : (term355 x y z) = (term356 x y z).
Proof. exact (@lem1483519 (term338 x y z) term48). Qed.
Lemma lem1576355 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576356 : term227 = term48.
Proof. exact (@lem1576355 term36). Qed.
Lemma lem1576357 (x : real) (y : real) (z : real) : (term357 x y z) = (term357 x y z).
Proof. exact (eq_refl (term357 x y z)). Qed.
Lemma lem1576358 (x : real) (y : real) (z : real) : (term356 x y z) = (term358 x y z).
Proof. exact (MK_COMB (@lem1576357 x y z) (@lem1576356)). Qed.
Lemma lem1576359 (x : real) (y : real) (z : real) : (term358 x y z) = (term338 x y z).
Proof. exact (@lem1483450 (term338 x y z)). Qed.
Lemma lem1576360 (x : real) (y : real) (z : real) : (term356 x y z) = (term338 x y z).
Proof. exact (TRANS (@lem1576358 x y z) (@lem1576359 x y z)). Qed.
Lemma lem1576362 (x : real) (y : real) (z : real) : (term355 x y z) = (term338 x y z).
Proof. exact (TRANS (@lem1576353 x y z) (@lem1576360 x y z)). Qed.
Lemma lem1576363 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576364 (x : real) (y : real) (z : real) : (term359 x y z) = (term340 x y z).
Proof. exact (MK_COMB (@lem1576363) (@lem1576362 x y z)). Qed.
Lemma lem1576365 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576366 (x : real) (y : real) (z : real) : (term354 x y z) = (term341 x y z).
Proof. exact (MK_COMB (@lem1576364 x y z) (@lem1576365)). Qed.
Lemma lem1576367 (x : real) (y : real) (z : real) : (term341 x y z) = (term341 x y z).
Proof. exact (TRANS (@lem1576335 x y z) (@lem1576366 x y z)). Qed.
Lemma lem1576368 (y : real) (z : real) : (term179 y z) = (term342 y z).
Proof. exact (@lem1483525 (term175 y z) term48). Qed.
Lemma lem1576386 (y : real) (z : real) : (term343 y z) = (term344 y z).
Proof. exact (@lem1483519 (term175 y z) term48). Qed.
Lemma lem1576388 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576389 : term227 = term48.
Proof. exact (@lem1576388 term36). Qed.
Lemma lem1576390 (y : real) (z : real) : (term345 y z) = (term345 y z).
Proof. exact (eq_refl (term345 y z)). Qed.
Lemma lem1576391 (y : real) (z : real) : (term344 y z) = (term346 y z).
Proof. exact (MK_COMB (@lem1576390 y z) (@lem1576389)). Qed.
Lemma lem1576392 (y : real) (z : real) : (term346 y z) = (term175 y z).
Proof. exact (@lem1483450 (term175 y z)). Qed.
Lemma lem1576393 (y : real) (z : real) : (term344 y z) = (term175 y z).
Proof. exact (TRANS (@lem1576391 y z) (@lem1576392 y z)). Qed.
Lemma lem1576395 (y : real) (z : real) : (term343 y z) = (term175 y z).
Proof. exact (TRANS (@lem1576386 y z) (@lem1576393 y z)). Qed.
Lemma lem1576396 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576397 (y : real) (z : real) : (term347 y z) = (term177 y z).
Proof. exact (MK_COMB (@lem1576396) (@lem1576395 y z)). Qed.
Lemma lem1576398 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576399 (y : real) (z : real) : (term342 y z) = (term179 y z).
Proof. exact (MK_COMB (@lem1576397 y z) (@lem1576398)). Qed.
Lemma lem1576400 (y : real) (z : real) : (term179 y z) = (term179 y z).
Proof. exact (TRANS (@lem1576368 y z) (@lem1576399 y z)). Qed.
Lemma lem1576401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576402 (x : real) (y : real) (z : real) : (term362 x y z) = (term362 x y z).
Proof. exact (MK_COMB (@lem1576401) (@lem1576367 x y z)). Qed.
Lemma lem1576403 (x : real) (y : real) (z : real) : (term457 x y z) = (term457 x y z).
Proof. exact (MK_COMB (@lem1576402 x y z) (@lem1576400 y z)). Qed.
Lemma lem1576404 (y : real) (z : real) : (term185 y z) = (term348 y z).
Proof. exact (@lem1483525 (term181 y z) term48). Qed.
Lemma lem1576422 (y : real) (z : real) : (term349 y z) = (term350 y z).
Proof. exact (@lem1483519 (term181 y z) term48). Qed.
Lemma lem1576424 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576425 : term227 = term48.
Proof. exact (@lem1576424 term36). Qed.
Lemma lem1576426 (y : real) (z : real) : (term351 y z) = (term351 y z).
Proof. exact (eq_refl (term351 y z)). Qed.
Lemma lem1576427 (y : real) (z : real) : (term350 y z) = (term352 y z).
Proof. exact (MK_COMB (@lem1576426 y z) (@lem1576425)). Qed.
Lemma lem1576428 (y : real) (z : real) : (term352 y z) = (term181 y z).
Proof. exact (@lem1483450 (term181 y z)). Qed.
Lemma lem1576429 (y : real) (z : real) : (term350 y z) = (term181 y z).
Proof. exact (TRANS (@lem1576427 y z) (@lem1576428 y z)). Qed.
Lemma lem1576431 (y : real) (z : real) : (term349 y z) = (term181 y z).
Proof. exact (TRANS (@lem1576422 y z) (@lem1576429 y z)). Qed.
Lemma lem1576432 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576433 (y : real) (z : real) : (term353 y z) = (term183 y z).
Proof. exact (MK_COMB (@lem1576432) (@lem1576431 y z)). Qed.
Lemma lem1576434 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576435 (y : real) (z : real) : (term348 y z) = (term185 y z).
Proof. exact (MK_COMB (@lem1576433 y z) (@lem1576434)). Qed.
Lemma lem1576436 (y : real) (z : real) : (term185 y z) = (term185 y z).
Proof. exact (TRANS (@lem1576404 y z) (@lem1576435 y z)). Qed.
Lemma lem1576437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576438 (x : real) (y : real) (z : real) : (term458 x y z) = (term458 x y z).
Proof. exact (MK_COMB (@lem1576437) (@lem1576403 x y z)). Qed.
Lemma lem1576439 (x : real) (y : real) (z : real) : (term444 x y z) = (term444 x y z).
Proof. exact (MK_COMB (@lem1576438 x y z) (@lem1576436 y z)). Qed.
Lemma lem1576440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576441 (x : real) (y : real) (z : real) : (term445 y z x) = (term459 x y z).
Proof. exact (MK_COMB (@lem1576440) (@lem1576334 x y z)). Qed.
Lemma lem1576442 (x : real) (y : real) (z : real) : (term447 x y z) = (term460 x y z).
Proof. exact (MK_COMB (@lem1576441 x y z) (@lem1576439 x y z)). Qed.
Lemma lem1576443 (x : real) (y : real) (z : real) : (term461 x y z) = (term462 x y z).
Proof. exact (@lem1483525 x (real_max y z)). Qed.
Lemma lem1576456 (x : real) (y : real) (z : real) : (term326 x y z) = (term327 x y z).
Proof. exact (@lem1483519 x (real_max y z)). Qed.
Lemma lem1576457 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576458 (x : real) (y : real) (z : real) : (term463 x y z) = (term464 x y z).
Proof. exact (MK_COMB (@lem1576457) (@lem1576456 x y z)). Qed.
Lemma lem1576459 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576460 (x : real) (y : real) (z : real) : (term462 x y z) = (term465 x y z).
Proof. exact (MK_COMB (@lem1576458 x y z) (@lem1576459)). Qed.
Lemma lem1576461 (x : real) (y : real) (z : real) : (term461 x y z) = (term465 x y z).
Proof. exact (TRANS (@lem1576443 x y z) (@lem1576460 x y z)). Qed.
Lemma lem1576462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576463 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1576462) (@lem1575523 x)). Qed.
Lemma lem1576464 (x : real) (y : real) : (term198 y x) = (term265 x y).
Proof. exact (MK_COMB (@lem1576463 x) (@lem1575480 x y)). Qed.
Lemma lem1576465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576466 (x : real) (y : real) : (term466 y x) = (term467 x y).
Proof. exact (MK_COMB (@lem1576465) (@lem1576464 x y)). Qed.
Lemma lem1576467 (y : real) (x : real) (z : real) : (term439 y z x) = (term468 y x z).
Proof. exact (MK_COMB (@lem1576466 x y) (@lem1576133 x z)). Qed.
Lemma lem1576468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576469 (x : real) (y : real) (z : real) : (term440 x y z) = (term469 x y z).
Proof. exact (MK_COMB (@lem1576468) (@lem1576461 x y z)). Qed.
Lemma lem1576470 (y : real) (x : real) (z : real) : (term442 y z x) = (term470 y x z).
Proof. exact (MK_COMB (@lem1576469 x y z) (@lem1576467 y x z)). Qed.
Lemma lem1576471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576472 (x : real) (y : real) (z : real) : (term449 x y z) = (term471 x y z).
Proof. exact (MK_COMB (@lem1576471) (@lem1576442 x y z)). Qed.
Lemma lem1576473 (y : real) (x : real) (z : real) : (term450 y z x) = (term472 y x z).
Proof. exact (MK_COMB (@lem1576472 x y z) (@lem1576470 y x z)). Qed.
Lemma lem1576474 (y : real) (x : real) (z : real) : (term434 x y z) = (term472 y x z).
Proof. exact (TRANS (@lem1576315 y z x) (@lem1576473 y x z)). Qed.
Lemma lem1576476 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576515 (y : real) (x : real) (z : real) : (term465 x y z) = (term386 y x z).
Proof. exact (@lem1576476 y x z term48). Qed.
Lemma lem1576516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576517 (y : real) (x : real) (z : real) : (term469 x y z) = (term473 y x z).
Proof. exact (MK_COMB (@lem1576516) (@lem1576515 y x z)). Qed.
Lemma lem1576518 (y : real) (x : real) (z : real) : (term468 y x z) = (term468 y x z).
Proof. exact (eq_refl (term468 y x z)). Qed.
Lemma lem1576521 (y : real) (x : real) (z : real) : (term470 y x z) = (term474 y x z).
Proof. exact (MK_COMB (@lem1576517 y x z) (@lem1576518 y x z)). Qed.
Lemma lem1576523 (x : real) (y : real) (z : real) : (term475 x y z) = (term460 x y z).
Proof. exact (eq_refl (term475 x y z)). Qed.
Lemma lem1576524 (x : real) (y : real) (z : real) : (term460 x y z) = (term475 x y z).
Proof. exact (SYM (@lem1576523 x y z)). Qed.
Lemma lem1576525 (x : real) (z : real) (y : real) : (term475 x y z) = (term476 x z y).
Proof. exact (@lem1483205 z (term477 x y z) y). Qed.
Lemma lem1576526 (x : real) (z : real) (y : real) : (term460 x y z) = (term476 x z y).
Proof. exact (TRANS (@lem1576524 x y z) (@lem1576525 x z y)). Qed.
Lemma lem1576527 (x : real) (z : real) (y : real) : (term478 x z y) = (term479 x z y).
Proof. exact (eq_refl (term478 x z y)). Qed.
Lemma lem1576528 (y : real) (z : real) : (term194 y z) = (term194 y z).
Proof. exact (eq_refl (term194 y z)). Qed.
Lemma lem1576529 (x : real) (z : real) (y : real) : (term480 x z y) = (term481 x z y).
Proof. exact (MK_COMB (@lem1576528 y z) (@lem1576527 x z y)). Qed.
Lemma lem1576530 (x : real) (y : real) (z : real) : (term482 x y z) = (term483 x y z).
Proof. exact (eq_refl (term482 x y z)). Qed.
Lemma lem1576531 (z : real) (y : real) : (term199 z y) = (term199 z y).
Proof. exact (eq_refl (term199 z y)). Qed.
Lemma lem1576532 (x : real) (y : real) (z : real) : (term484 x y z) = (term485 x y z).
Proof. exact (MK_COMB (@lem1576531 z y) (@lem1576530 x y z)). Qed.
Lemma lem1576533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576534 (x : real) (y : real) (z : real) : (term486 x y z) = (term487 x y z).
Proof. exact (MK_COMB (@lem1576533) (@lem1576532 x y z)). Qed.
Lemma lem1576535 (x : real) (z : real) (y : real) : (term476 x z y) = (term488 x z y).
Proof. exact (MK_COMB (@lem1576534 x y z) (@lem1576529 x z y)). Qed.
Lemma lem1576536 (x : real) (y : real) (z : real) : (term489 x y z) = (term489 x y z).
Proof. exact (eq_refl (term489 x y z)). Qed.
Lemma lem1576537 (x : real) (z : real) (y : real) : ((term460 x y z) = (term476 x z y)) = ((term460 x y z) = (term488 x z y)).
Proof. exact (MK_COMB (@lem1576536 x y z) (@lem1576535 x z y)). Qed.
Lemma lem1576538 (x : real) (z : real) (y : real) : (term460 x y z) = (term488 x z y).
Proof. exact (EQ_MP (@lem1576537 x z y) (@lem1576526 x z y)). Qed.
Lemma lem1576539 (z : real) (y : real) : (real_ge z y) = (term206 z y).
Proof. exact (@lem1483527 z y). Qed.
Lemma lem1576545 (z : real) (y : real) : (real_sub z y) = (term207 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1576550 (y : real) (z : real) : (term207 z y) = (term208 y z).
Proof. exact (@lem1483488 (term114 y) z). Qed.
Lemma lem1576552 (y : real) (z : real) : (real_sub z y) = (term208 y z).
Proof. exact (TRANS (@lem1576545 z y) (@lem1576550 y z)). Qed.
Lemma lem1576553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576554 (y : real) (z : real) : (term209 z y) = (term210 y z).
Proof. exact (MK_COMB (@lem1576553) (@lem1576552 y z)). Qed.
Lemma lem1576555 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576556 (y : real) (z : real) : (term206 z y) = (term211 y z).
Proof. exact (MK_COMB (@lem1576554 y z) (@lem1576555)). Qed.
Lemma lem1576557 (y : real) (z : real) : (real_ge z y) = (term211 y z).
Proof. exact (TRANS (@lem1576539 z y) (@lem1576556 y z)). Qed.
Lemma lem1576558 (x : real) (z : real) : (term211 x z) = (term490 x z).
Proof. exact (@lem1483527 (term208 x z) term48). Qed.
Lemma lem1576576 (x : real) (z : real) : (term235 x z) = (term236 x z).
Proof. exact (@lem1483519 (term208 x z) term48). Qed.
Lemma lem1576578 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576579 : term227 = term48.
Proof. exact (@lem1576578 term36). Qed.
Lemma lem1576580 (x : real) (z : real) : (term237 x z) = (term237 x z).
Proof. exact (eq_refl (term237 x z)). Qed.
Lemma lem1576581 (x : real) (z : real) : (term236 x z) = (term238 x z).
Proof. exact (MK_COMB (@lem1576580 x z) (@lem1576579)). Qed.
Lemma lem1576582 (x : real) (z : real) : (term238 x z) = (term208 x z).
Proof. exact (@lem1483450 (term208 x z)). Qed.
Lemma lem1576583 (x : real) (z : real) : (term236 x z) = (term208 x z).
Proof. exact (TRANS (@lem1576581 x z) (@lem1576582 x z)). Qed.
Lemma lem1576585 (x : real) (z : real) : (term235 x z) = (term208 x z).
Proof. exact (TRANS (@lem1576576 x z) (@lem1576583 x z)). Qed.
Lemma lem1576586 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576587 (x : real) (z : real) : (term491 x z) = (term210 x z).
Proof. exact (MK_COMB (@lem1576586) (@lem1576585 x z)). Qed.
Lemma lem1576588 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576589 (x : real) (z : real) : (term490 x z) = (term211 x z).
Proof. exact (MK_COMB (@lem1576587 x z) (@lem1576588)). Qed.
Lemma lem1576590 (x : real) (z : real) : (term211 x z) = (term211 x z).
Proof. exact (TRANS (@lem1576558 x z) (@lem1576589 x z)). Qed.
Lemma lem1576591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576592 (x : real) (z : real) : (term256 x z) = (term256 x z).
Proof. exact (MK_COMB (@lem1576591) (@lem1575822 x z)). Qed.
Lemma lem1576593 (x : real) (y : real) (z : real) : (term385 x y z) = (term385 x y z).
Proof. exact (MK_COMB (@lem1576592 x z) (@lem1575855 y z)). Qed.
Lemma lem1576594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576595 (x : real) (y : real) (z : real) : (term492 x y z) = (term492 x y z).
Proof. exact (MK_COMB (@lem1576594) (@lem1576593 x y z)). Qed.
Lemma lem1576596 (x : real) (y : real) (z : real) : (term493 x y z) = (term494 x y z).
Proof. exact (MK_COMB (@lem1576595 x y z) (@lem1575898 z)). Qed.
Lemma lem1576597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576598 (x : real) (z : real) : (term244 x z) = (term244 x z).
Proof. exact (MK_COMB (@lem1576597) (@lem1576590 x z)). Qed.
Lemma lem1576599 (x : real) (y : real) (z : real) : (term483 x y z) = (term495 x y z).
Proof. exact (MK_COMB (@lem1576598 x z) (@lem1576596 x y z)). Qed.
Lemma lem1576600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576601 (y : real) (z : real) : (term199 z y) = (term244 y z).
Proof. exact (MK_COMB (@lem1576600) (@lem1576557 y z)). Qed.
Lemma lem1576602 (x : real) (y : real) (z : real) : (term485 x y z) = (term496 x y z).
Proof. exact (MK_COMB (@lem1576601 y z) (@lem1576599 x y z)). Qed.
Lemma lem1576603 (y : real) (z : real) : (real_gt y z) = (term246 y z).
Proof. exact (@lem1483525 y z). Qed.
Lemma lem1576616 (y : real) (z : real) : (real_sub y z) = (term207 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1576617 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576618 (y : real) (z : real) : (term247 y z) = (term248 y z).
Proof. exact (MK_COMB (@lem1576617) (@lem1576616 y z)). Qed.
Lemma lem1576619 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576620 (y : real) (z : real) : (term246 y z) = (term249 y z).
Proof. exact (MK_COMB (@lem1576618 y z) (@lem1576619)). Qed.
Lemma lem1576621 (y : real) (z : real) : (real_gt y z) = (term249 y z).
Proof. exact (TRANS (@lem1576603 y z) (@lem1576620 y z)). Qed.
Lemma lem1576622 (x : real) (y : real) : (term211 x y) = (term490 x y).
Proof. exact (@lem1483527 (term208 x y) term48). Qed.
Lemma lem1576640 (x : real) (y : real) : (term235 x y) = (term236 x y).
Proof. exact (@lem1483519 (term208 x y) term48). Qed.
Lemma lem1576642 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1576643 : term227 = term48.
Proof. exact (@lem1576642 term36). Qed.
Lemma lem1576644 (x : real) (y : real) : (term237 x y) = (term237 x y).
Proof. exact (eq_refl (term237 x y)). Qed.
Lemma lem1576645 (x : real) (y : real) : (term236 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1576644 x y) (@lem1576643)). Qed.
Lemma lem1576646 (x : real) (y : real) : (term238 x y) = (term208 x y).
Proof. exact (@lem1483450 (term208 x y)). Qed.
Lemma lem1576647 (x : real) (y : real) : (term236 x y) = (term208 x y).
Proof. exact (TRANS (@lem1576645 x y) (@lem1576646 x y)). Qed.
Lemma lem1576649 (x : real) (y : real) : (term235 x y) = (term208 x y).
Proof. exact (TRANS (@lem1576640 x y) (@lem1576647 x y)). Qed.
Lemma lem1576650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1576651 (x : real) (y : real) : (term491 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1576650) (@lem1576649 x y)). Qed.
Lemma lem1576652 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576653 (x : real) (y : real) : (term490 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1576651 x y) (@lem1576652)). Qed.
Lemma lem1576654 (x : real) (y : real) : (term211 x y) = (term211 x y).
Proof. exact (TRANS (@lem1576622 x y) (@lem1576653 x y)). Qed.
Lemma lem1576655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576656 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1576655) (@lem1575422 x y)). Qed.
Lemma lem1576657 (x : real) (y : real) : (term193 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1576656 x y) (@lem1575389 y)). Qed.
Lemma lem1576658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576659 (x : real) (y : real) : (term497 x y) = (term498 x y).
Proof. exact (MK_COMB (@lem1576658) (@lem1576657 x y)). Qed.
Lemma lem1576660 (x : real) (y : real) (z : real) : (term499 x z y) = (term500 x y z).
Proof. exact (MK_COMB (@lem1576659 x y) (@lem1576088 y z)). Qed.
Lemma lem1576661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576662 (x : real) (y : real) : (term244 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1576661) (@lem1576654 x y)). Qed.
Lemma lem1576663 (x : real) (y : real) (z : real) : (term479 x z y) = (term501 x y z).
Proof. exact (MK_COMB (@lem1576662 x y) (@lem1576660 x y z)). Qed.
Lemma lem1576664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576665 (y : real) (z : real) : (term194 y z) = (term257 y z).
Proof. exact (MK_COMB (@lem1576664) (@lem1576621 y z)). Qed.
Lemma lem1576666 (x : real) (y : real) (z : real) : (term481 x z y) = (term502 x y z).
Proof. exact (MK_COMB (@lem1576665 y z) (@lem1576663 x y z)). Qed.
Lemma lem1576667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576668 (x : real) (y : real) (z : real) : (term487 x y z) = (term503 x y z).
Proof. exact (MK_COMB (@lem1576667) (@lem1576602 x y z)). Qed.
Lemma lem1576669 (x : real) (y : real) (z : real) : (term488 x z y) = (term504 x y z).
Proof. exact (MK_COMB (@lem1576668 x y z) (@lem1576666 x y z)). Qed.
Lemma lem1576681 (x : real) (y : real) (z : real) : (term460 x y z) = (term504 x y z).
Proof. exact (TRANS (@lem1576538 x z y) (@lem1576669 x y z)). Qed.
Lemma lem1576682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576683 (x : real) (y : real) (z : real) : (term471 x y z) = (term505 x y z).
Proof. exact (MK_COMB (@lem1576682) (@lem1576681 x y z)). Qed.
Lemma lem1576684 (y : real) (x : real) (z : real) : (term472 y x z) = (term506 y x z).
Proof. exact (MK_COMB (@lem1576683 x y z) (@lem1576521 y x z)). Qed.
Lemma lem1576685 (y : real) (x : real) (z : real) : (term434 x y z) = (term506 y x z).
Proof. exact (TRANS (@lem1576474 y x z) (@lem1576684 y x z)). Qed.
Lemma lem1576686 (y : real) (x : real) (z : real) : (term79 x y z) = (term506 y x z).
Proof. exact (TRANS (@lem1576299 x y z) (@lem1576685 y x z)). Qed.
Lemma lem1576687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576688 (y : real) (x : real) (z : real) : (term85 x y z) = (term507 y x z).
Proof. exact (MK_COMB (@lem1576687) (@lem1576212 y x z)). Qed.
Lemma lem1576689 (y : real) (x : real) (z : real) : (term86 x y z) = (term508 y x z).
Proof. exact (MK_COMB (@lem1576688 y x z) (@lem1576686 y x z)). Qed.
Lemma lem1576691 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576692 (y : real) (x : real) (z : real) : (term105 y x z) = (term509 y x z).
Proof. exact (@lem1576691 y (term7 x y z) (real_max x z) term48). Qed.
Lemma lem1576705 (x : real) (y : real) (z : real) : (term510 y x z) = (term511 x y z).
Proof. exact (@lem1483488 (term29 x z) (term7 x y z)). Qed.
Lemma lem1576706 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576707 (x : real) (y : real) (z : real) : (term512 y x z) = (term513 x y z).
Proof. exact (MK_COMB (@lem1576706) (@lem1576705 x y z)). Qed.
Lemma lem1576708 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576709 (x : real) (y : real) (z : real) : (term514 y x z) = (term515 x y z).
Proof. exact (MK_COMB (@lem1576707 x y z) (@lem1576708)). Qed.
Lemma lem1576722 (x : real) (y : real) (z : real) : (term418 x z y) = (term419 x y z).
Proof. exact (@lem1483488 (term114 y) (term7 x y z)). Qed.
Lemma lem1576723 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576724 (x : real) (y : real) (z : real) : (term420 x z y) = (term421 x y z).
Proof. exact (MK_COMB (@lem1576723) (@lem1576722 x y z)). Qed.
Lemma lem1576725 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576726 (x : real) (y : real) (z : real) : (term422 x z y) = (term423 x y z).
Proof. exact (MK_COMB (@lem1576724 x y z) (@lem1576725)). Qed.
Lemma lem1576727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576728 (x : real) (y : real) (z : real) : (term516 x z y) = (term517 x y z).
Proof. exact (MK_COMB (@lem1576727) (@lem1576726 x y z)). Qed.
Lemma lem1576729 (x : real) (y : real) (z : real) : (term509 y x z) = (term518 x y z).
Proof. exact (MK_COMB (@lem1576728 x y z) (@lem1576709 x y z)). Qed.
Lemma lem1576730 (x : real) (y : real) (z : real) : (term105 y x z) = (term518 x y z).
Proof. exact (TRANS (@lem1576692 y x z) (@lem1576729 x y z)). Qed.
Lemma lem1576732 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576733 (x : real) (y : real) (z : real) : (term515 x y z) = (term519 x y z).
Proof. exact (@lem1576732 x (term7 x y z) z term48). Qed.
Lemma lem1576746 (x : real) (y : real) (z : real) : (term402 x y z) = (term403 x y z).
Proof. exact (@lem1483488 (term114 z) (term7 x y z)). Qed.
Lemma lem1576747 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576748 (x : real) (y : real) (z : real) : (term404 x y z) = (term405 x y z).
Proof. exact (MK_COMB (@lem1576747) (@lem1576746 x y z)). Qed.
Lemma lem1576749 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576750 (x : real) (y : real) (z : real) : (term406 x y z) = (term407 x y z).
Proof. exact (MK_COMB (@lem1576748 x y z) (@lem1576749)). Qed.
Lemma lem1576763 (x : real) (y : real) (z : real) : (term424 y z x) = (term425 x y z).
Proof. exact (@lem1483488 (term114 x) (term7 x y z)). Qed.
Lemma lem1576764 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576765 (x : real) (y : real) (z : real) : (term426 y z x) = (term427 x y z).
Proof. exact (MK_COMB (@lem1576764) (@lem1576763 x y z)). Qed.
Lemma lem1576766 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576767 (x : real) (y : real) (z : real) : (term428 y z x) = (term429 x y z).
Proof. exact (MK_COMB (@lem1576765 x y z) (@lem1576766)). Qed.
Lemma lem1576768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576769 (x : real) (y : real) (z : real) : (term430 y z x) = (term431 x y z).
Proof. exact (MK_COMB (@lem1576768) (@lem1576767 x y z)). Qed.
Lemma lem1576770 (x : real) (y : real) (z : real) : (term519 x y z) = (term520 x y z).
Proof. exact (MK_COMB (@lem1576769 x y z) (@lem1576750 x y z)). Qed.
Lemma lem1576771 (x : real) (y : real) (z : real) : (term515 x y z) = (term520 x y z).
Proof. exact (TRANS (@lem1576733 x y z) (@lem1576770 x y z)). Qed.
Lemma lem1576772 (x : real) (y : real) (z : real) : (term517 x y z) = (term517 x y z).
Proof. exact (eq_refl (term517 x y z)). Qed.
Lemma lem1576773 (x : real) (y : real) (z : real) : (term518 x y z) = (term521 x y z).
Proof. exact (MK_COMB (@lem1576772 x y z) (@lem1576771 x y z)). Qed.
Lemma lem1576774 (x : real) (y : real) (z : real) : (term105 y x z) = (term521 x y z).
Proof. exact (TRANS (@lem1576730 x y z) (@lem1576773 x y z)). Qed.
Lemma lem1576775 (x : real) (y : real) (z : real) : (term522 x y z) = (term521 x y z).
Proof. exact (eq_refl (term522 x y z)). Qed.
Lemma lem1576776 (x : real) (y : real) (z : real) : (term521 x y z) = (term522 x y z).
Proof. exact (SYM (@lem1576775 x y z)). Qed.
Lemma lem1576777 (y : real) (z : real) (x : real) : (term522 x y z) = (term523 y z x).
Proof. exact (@lem1483205 (real_max y z) (term309 y x z) x). Qed.
Lemma lem1576778 (y : real) (z : real) (x : real) : (term521 x y z) = (term523 y z x).
Proof. exact (TRANS (@lem1576776 x y z) (@lem1576777 y z x)). Qed.
Lemma lem1576779 (y : real) (z : real) (x : real) : (term524 y z x) = (term381 y z x).
Proof. exact (eq_refl (term524 y z x)). Qed.
Lemma lem1576780 (x : real) (y : real) (z : real) : (term440 x y z) = (term440 x y z).
Proof. exact (eq_refl (term440 x y z)). Qed.
Lemma lem1576781 (y : real) (z : real) (x : real) : (term525 y z x) = (term526 y z x).
Proof. exact (MK_COMB (@lem1576780 x y z) (@lem1576779 y z x)). Qed.
Lemma lem1576782 (x : real) (y : real) (z : real) : (term527 x y z) = (term528 x y z).
Proof. exact (eq_refl (term527 x y z)). Qed.
Lemma lem1576783 (y : real) (z : real) (x : real) : (term445 y z x) = (term445 y z x).
Proof. exact (eq_refl (term445 y z x)). Qed.
Lemma lem1576784 (x : real) (y : real) (z : real) : (term529 x y z) = (term530 x y z).
Proof. exact (MK_COMB (@lem1576783 y z x) (@lem1576782 x y z)). Qed.
Lemma lem1576785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576786 (x : real) (y : real) (z : real) : (term531 x y z) = (term532 x y z).
Proof. exact (MK_COMB (@lem1576785) (@lem1576784 x y z)). Qed.
Lemma lem1576787 (y : real) (z : real) (x : real) : (term523 y z x) = (term533 y z x).
Proof. exact (MK_COMB (@lem1576786 x y z) (@lem1576781 y z x)). Qed.
Lemma lem1576788 (x : real) (y : real) (z : real) : (term534 x y z) = (term534 x y z).
Proof. exact (eq_refl (term534 x y z)). Qed.
Lemma lem1576789 (y : real) (z : real) (x : real) : ((term521 x y z) = (term523 y z x)) = ((term521 x y z) = (term533 y z x)).
Proof. exact (MK_COMB (@lem1576788 x y z) (@lem1576787 y z x)). Qed.
Lemma lem1576790 (y : real) (z : real) (x : real) : (term521 x y z) = (term533 y z x).
Proof. exact (EQ_MP (@lem1576789 y z x) (@lem1576778 y z x)). Qed.
Lemma lem1576791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576792 (x : real) (y : real) (z : real) : (term362 x y z) = (term362 x y z).
Proof. exact (MK_COMB (@lem1576791) (@lem1576367 x y z)). Qed.
Lemma lem1576793 (x : real) (y : real) (z : real) : (term535 x y z) = (term535 x y z).
Proof. exact (MK_COMB (@lem1576792 x y z) (@lem1576436 y z)). Qed.
Lemma lem1576794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576795 (y : real) (z : real) : (term361 y z) = (term361 y z).
Proof. exact (MK_COMB (@lem1576794) (@lem1576400 y z)). Qed.
Lemma lem1576796 (x : real) (y : real) (z : real) : (term528 x y z) = (term528 x y z).
Proof. exact (MK_COMB (@lem1576795 y z) (@lem1576793 x y z)). Qed.
Lemma lem1576797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576798 (x : real) (y : real) (z : real) : (term445 y z x) = (term459 x y z).
Proof. exact (MK_COMB (@lem1576797) (@lem1576334 x y z)). Qed.
Lemma lem1576799 (x : real) (y : real) (z : real) : (term530 x y z) = (term536 x y z).
Proof. exact (MK_COMB (@lem1576798 x y z) (@lem1576796 x y z)). Qed.
Lemma lem1576800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576801 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1576800) (@lem1575523 x)). Qed.
Lemma lem1576802 (x : real) (z : real) : (term198 z x) = (term265 x z).
Proof. exact (MK_COMB (@lem1576801 x) (@lem1576133 x z)). Qed.
Lemma lem1576803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576804 (x : real) (y : real) : (term256 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1576803) (@lem1575480 x y)). Qed.
Lemma lem1576805 (y : real) (x : real) (z : real) : (term381 y z x) = (term537 y x z).
Proof. exact (MK_COMB (@lem1576804 x y) (@lem1576802 x z)). Qed.
Lemma lem1576806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576807 (x : real) (y : real) (z : real) : (term440 x y z) = (term469 x y z).
Proof. exact (MK_COMB (@lem1576806) (@lem1576461 x y z)). Qed.
Lemma lem1576808 (y : real) (x : real) (z : real) : (term526 y z x) = (term538 y x z).
Proof. exact (MK_COMB (@lem1576807 x y z) (@lem1576805 y x z)). Qed.
Lemma lem1576809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576810 (x : real) (y : real) (z : real) : (term532 x y z) = (term539 x y z).
Proof. exact (MK_COMB (@lem1576809) (@lem1576799 x y z)). Qed.
Lemma lem1576811 (y : real) (x : real) (z : real) : (term533 y z x) = (term540 y x z).
Proof. exact (MK_COMB (@lem1576810 x y z) (@lem1576808 y x z)). Qed.
Lemma lem1576812 (y : real) (x : real) (z : real) : (term521 x y z) = (term540 y x z).
Proof. exact (TRANS (@lem1576790 y z x) (@lem1576811 y x z)). Qed.
Lemma lem1576814 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576853 (y : real) (x : real) (z : real) : (term465 x y z) = (term386 y x z).
Proof. exact (@lem1576814 y x z term48). Qed.
Lemma lem1576854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576855 (y : real) (x : real) (z : real) : (term469 x y z) = (term473 y x z).
Proof. exact (MK_COMB (@lem1576854) (@lem1576853 y x z)). Qed.
Lemma lem1576856 (y : real) (x : real) (z : real) : (term537 y x z) = (term537 y x z).
Proof. exact (eq_refl (term537 y x z)). Qed.
Lemma lem1576859 (y : real) (x : real) (z : real) : (term538 y x z) = (term541 y x z).
Proof. exact (MK_COMB (@lem1576855 y x z) (@lem1576856 y x z)). Qed.
Lemma lem1576861 (x : real) (y : real) (z : real) : (term542 x y z) = (term536 x y z).
Proof. exact (eq_refl (term542 x y z)). Qed.
Lemma lem1576862 (x : real) (y : real) (z : real) : (term536 x y z) = (term542 x y z).
Proof. exact (SYM (@lem1576861 x y z)). Qed.
Lemma lem1576863 (x : real) (z : real) (y : real) : (term542 x y z) = (term543 x z y).
Proof. exact (@lem1483205 z (term544 y x z) y). Qed.
Lemma lem1576864 (x : real) (z : real) (y : real) : (term536 x y z) = (term543 x z y).
Proof. exact (TRANS (@lem1576862 x y z) (@lem1576863 x z y)). Qed.
Lemma lem1576865 (x : real) (z : real) (y : real) : (term545 x z y) = (term546 x z y).
Proof. exact (eq_refl (term545 x z y)). Qed.
Lemma lem1576866 (y : real) (z : real) : (term194 y z) = (term194 y z).
Proof. exact (eq_refl (term194 y z)). Qed.
Lemma lem1576867 (x : real) (z : real) (y : real) : (term547 x z y) = (term548 x z y).
Proof. exact (MK_COMB (@lem1576866 y z) (@lem1576865 x z y)). Qed.
Lemma lem1576868 (y : real) (x : real) (z : real) : (term549 y x z) = (term550 y x z).
Proof. exact (eq_refl (term549 y x z)). Qed.
Lemma lem1576869 (z : real) (y : real) : (term199 z y) = (term199 z y).
Proof. exact (eq_refl (term199 z y)). Qed.
Lemma lem1576870 (y : real) (x : real) (z : real) : (term551 y x z) = (term552 y x z).
Proof. exact (MK_COMB (@lem1576869 z y) (@lem1576868 y x z)). Qed.
Lemma lem1576871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576872 (y : real) (x : real) (z : real) : (term553 y x z) = (term554 y x z).
Proof. exact (MK_COMB (@lem1576871) (@lem1576870 y x z)). Qed.
Lemma lem1576873 (x : real) (z : real) (y : real) : (term543 x z y) = (term555 x z y).
Proof. exact (MK_COMB (@lem1576872 y x z) (@lem1576867 x z y)). Qed.
Lemma lem1576874 (x : real) (y : real) (z : real) : (term556 x y z) = (term556 x y z).
Proof. exact (eq_refl (term556 x y z)). Qed.
Lemma lem1576875 (x : real) (z : real) (y : real) : ((term536 x y z) = (term543 x z y)) = ((term536 x y z) = (term555 x z y)).
Proof. exact (MK_COMB (@lem1576874 x y z) (@lem1576873 x z y)). Qed.
Lemma lem1576876 (x : real) (z : real) (y : real) : (term536 x y z) = (term555 x z y).
Proof. exact (EQ_MP (@lem1576875 x z y) (@lem1576864 x z y)). Qed.
Lemma lem1576877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576878 (x : real) (z : real) : (term256 x z) = (term256 x z).
Proof. exact (MK_COMB (@lem1576877) (@lem1575822 x z)). Qed.
Lemma lem1576879 (x : real) (z : real) : (term193 x z) = (term268 x z).
Proof. exact (MK_COMB (@lem1576878 x z) (@lem1575898 z)). Qed.
Lemma lem1576880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576881 (y : real) (z : real) : (term256 y z) = (term256 y z).
Proof. exact (MK_COMB (@lem1576880) (@lem1575855 y z)). Qed.
Lemma lem1576882 (y : real) (x : real) (z : real) : (term316 y x z) = (term331 y x z).
Proof. exact (MK_COMB (@lem1576881 y z) (@lem1576879 x z)). Qed.
Lemma lem1576883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576884 (x : real) (z : real) : (term244 x z) = (term244 x z).
Proof. exact (MK_COMB (@lem1576883) (@lem1576590 x z)). Qed.
Lemma lem1576885 (y : real) (x : real) (z : real) : (term550 y x z) = (term557 y x z).
Proof. exact (MK_COMB (@lem1576884 x z) (@lem1576882 y x z)). Qed.
Lemma lem1576886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576887 (y : real) (z : real) : (term199 z y) = (term244 y z).
Proof. exact (MK_COMB (@lem1576886) (@lem1576557 y z)). Qed.
Lemma lem1576888 (y : real) (x : real) (z : real) : (term552 y x z) = (term558 y x z).
Proof. exact (MK_COMB (@lem1576887 y z) (@lem1576885 y x z)). Qed.
Lemma lem1576889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576890 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1576889) (@lem1575422 x y)). Qed.
Lemma lem1576891 (x : real) (y : real) (z : real) : (term385 x z y) = (term559 x y z).
Proof. exact (MK_COMB (@lem1576890 x y) (@lem1576088 y z)). Qed.
Lemma lem1576892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576893 (y : real) : (term241 y) = term242.
Proof. exact (MK_COMB (@lem1576892) (@lem1575389 y)). Qed.
Lemma lem1576894 (x : real) (y : real) (z : real) : (term387 x z y) = (term560 x y z).
Proof. exact (MK_COMB (@lem1576893 y) (@lem1576891 x y z)). Qed.
Lemma lem1576895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576896 (x : real) (y : real) : (term244 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1576895) (@lem1576654 x y)). Qed.
Lemma lem1576897 (x : real) (y : real) (z : real) : (term546 x z y) = (term561 x y z).
Proof. exact (MK_COMB (@lem1576896 x y) (@lem1576894 x y z)). Qed.
Lemma lem1576898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576899 (y : real) (z : real) : (term194 y z) = (term257 y z).
Proof. exact (MK_COMB (@lem1576898) (@lem1576621 y z)). Qed.
Lemma lem1576900 (x : real) (y : real) (z : real) : (term548 x z y) = (term562 x y z).
Proof. exact (MK_COMB (@lem1576899 y z) (@lem1576897 x y z)). Qed.
Lemma lem1576901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576902 (y : real) (x : real) (z : real) : (term554 y x z) = (term563 y x z).
Proof. exact (MK_COMB (@lem1576901) (@lem1576888 y x z)). Qed.
Lemma lem1576903 (x : real) (y : real) (z : real) : (term555 x z y) = (term564 x y z).
Proof. exact (MK_COMB (@lem1576902 y x z) (@lem1576900 x y z)). Qed.
Lemma lem1576915 (x : real) (y : real) (z : real) : (term536 x y z) = (term564 x y z).
Proof. exact (TRANS (@lem1576876 x z y) (@lem1576903 x y z)). Qed.
Lemma lem1576916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1576917 (x : real) (y : real) (z : real) : (term539 x y z) = (term565 x y z).
Proof. exact (MK_COMB (@lem1576916) (@lem1576915 x y z)). Qed.
Lemma lem1576918 (y : real) (x : real) (z : real) : (term540 y x z) = (term566 y x z).
Proof. exact (MK_COMB (@lem1576917 x y z) (@lem1576859 y x z)). Qed.
Lemma lem1576919 (y : real) (x : real) (z : real) : (term521 x y z) = (term566 y x z).
Proof. exact (TRANS (@lem1576812 y x z) (@lem1576918 y x z)). Qed.
Lemma lem1576920 (y : real) (x : real) (z : real) : (term105 y x z) = (term566 y x z).
Proof. exact (TRANS (@lem1576774 x y z) (@lem1576919 y x z)). Qed.
Lemma lem1576922 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576923 (x : real) (y : real) (z : real) : (term101 y x z) = (term509 x y z).
Proof. exact (@lem1576922 x (term7 y x z) (real_max y z) term48). Qed.
Lemma lem1576936 (y : real) (x : real) (z : real) : (term510 x y z) = (term511 y x z).
Proof. exact (@lem1483488 (term29 y z) (term7 y x z)). Qed.
Lemma lem1576937 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576938 (y : real) (x : real) (z : real) : (term512 x y z) = (term513 y x z).
Proof. exact (MK_COMB (@lem1576937) (@lem1576936 y x z)). Qed.
Lemma lem1576939 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576940 (y : real) (x : real) (z : real) : (term514 x y z) = (term515 y x z).
Proof. exact (MK_COMB (@lem1576938 y x z) (@lem1576939)). Qed.
Lemma lem1576953 (y : real) (x : real) (z : real) : (term418 y z x) = (term419 y x z).
Proof. exact (@lem1483488 (term114 x) (term7 y x z)). Qed.
Lemma lem1576954 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576955 (y : real) (x : real) (z : real) : (term420 y z x) = (term421 y x z).
Proof. exact (MK_COMB (@lem1576954) (@lem1576953 y x z)). Qed.
Lemma lem1576956 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576957 (y : real) (x : real) (z : real) : (term422 y z x) = (term423 y x z).
Proof. exact (MK_COMB (@lem1576955 y x z) (@lem1576956)). Qed.
Lemma lem1576958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1576959 (y : real) (x : real) (z : real) : (term516 y z x) = (term517 y x z).
Proof. exact (MK_COMB (@lem1576958) (@lem1576957 y x z)). Qed.
Lemma lem1576960 (y : real) (x : real) (z : real) : (term509 x y z) = (term518 y x z).
Proof. exact (MK_COMB (@lem1576959 y x z) (@lem1576940 y x z)). Qed.
Lemma lem1576961 (y : real) (x : real) (z : real) : (term101 y x z) = (term518 y x z).
Proof. exact (TRANS (@lem1576923 x y z) (@lem1576960 y x z)). Qed.
Lemma lem1576963 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1576964 (y : real) (x : real) (z : real) : (term515 y x z) = (term519 y x z).
Proof. exact (@lem1576963 y (term7 y x z) z term48). Qed.
Lemma lem1576977 (y : real) (x : real) (z : real) : (term402 y x z) = (term403 y x z).
Proof. exact (@lem1483488 (term114 z) (term7 y x z)). Qed.
Lemma lem1576978 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576979 (y : real) (x : real) (z : real) : (term404 y x z) = (term405 y x z).
Proof. exact (MK_COMB (@lem1576978) (@lem1576977 y x z)). Qed.
Lemma lem1576980 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576981 (y : real) (x : real) (z : real) : (term406 y x z) = (term407 y x z).
Proof. exact (MK_COMB (@lem1576979 y x z) (@lem1576980)). Qed.
Lemma lem1576994 (y : real) (x : real) (z : real) : (term424 x z y) = (term425 y x z).
Proof. exact (@lem1483488 (term114 y) (term7 y x z)). Qed.
Lemma lem1576995 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1576996 (y : real) (x : real) (z : real) : (term426 x z y) = (term427 y x z).
Proof. exact (MK_COMB (@lem1576995) (@lem1576994 y x z)). Qed.
Lemma lem1576997 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1576998 (y : real) (x : real) (z : real) : (term428 x z y) = (term429 y x z).
Proof. exact (MK_COMB (@lem1576996 y x z) (@lem1576997)). Qed.
Lemma lem1576999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577000 (y : real) (x : real) (z : real) : (term430 x z y) = (term431 y x z).
Proof. exact (MK_COMB (@lem1576999) (@lem1576998 y x z)). Qed.
Lemma lem1577001 (y : real) (x : real) (z : real) : (term519 y x z) = (term520 y x z).
Proof. exact (MK_COMB (@lem1577000 y x z) (@lem1576981 y x z)). Qed.
Lemma lem1577002 (y : real) (x : real) (z : real) : (term515 y x z) = (term520 y x z).
Proof. exact (TRANS (@lem1576964 y x z) (@lem1577001 y x z)). Qed.
Lemma lem1577003 (y : real) (x : real) (z : real) : (term517 y x z) = (term517 y x z).
Proof. exact (eq_refl (term517 y x z)). Qed.
Lemma lem1577004 (y : real) (x : real) (z : real) : (term518 y x z) = (term521 y x z).
Proof. exact (MK_COMB (@lem1577003 y x z) (@lem1577002 y x z)). Qed.
Lemma lem1577005 (y : real) (x : real) (z : real) : (term101 y x z) = (term521 y x z).
Proof. exact (TRANS (@lem1576961 y x z) (@lem1577004 y x z)). Qed.
Lemma lem1577006 (y : real) (x : real) (z : real) : (term522 y x z) = (term521 y x z).
Proof. exact (eq_refl (term522 y x z)). Qed.
Lemma lem1577007 (y : real) (x : real) (z : real) : (term521 y x z) = (term522 y x z).
Proof. exact (SYM (@lem1577006 y x z)). Qed.
Lemma lem1577008 (x : real) (z : real) (y : real) : (term522 y x z) = (term523 x z y).
Proof. exact (@lem1483205 (real_max x z) (term309 x y z) y). Qed.
Lemma lem1577009 (x : real) (z : real) (y : real) : (term521 y x z) = (term523 x z y).
Proof. exact (TRANS (@lem1577007 y x z) (@lem1577008 x z y)). Qed.
Lemma lem1577010 (x : real) (z : real) (y : real) : (term524 x z y) = (term381 x z y).
Proof. exact (eq_refl (term524 x z y)). Qed.
Lemma lem1577011 (y : real) (x : real) (z : real) : (term440 y x z) = (term440 y x z).
Proof. exact (eq_refl (term440 y x z)). Qed.
Lemma lem1577012 (x : real) (z : real) (y : real) : (term525 x z y) = (term526 x z y).
Proof. exact (MK_COMB (@lem1577011 y x z) (@lem1577010 x z y)). Qed.
Lemma lem1577013 (y : real) (x : real) (z : real) : (term527 y x z) = (term528 y x z).
Proof. exact (eq_refl (term527 y x z)). Qed.
Lemma lem1577014 (x : real) (z : real) (y : real) : (term445 x z y) = (term445 x z y).
Proof. exact (eq_refl (term445 x z y)). Qed.
Lemma lem1577015 (y : real) (x : real) (z : real) : (term529 y x z) = (term530 y x z).
Proof. exact (MK_COMB (@lem1577014 x z y) (@lem1577013 y x z)). Qed.
Lemma lem1577016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577017 (y : real) (x : real) (z : real) : (term531 y x z) = (term532 y x z).
Proof. exact (MK_COMB (@lem1577016) (@lem1577015 y x z)). Qed.
Lemma lem1577018 (x : real) (z : real) (y : real) : (term523 x z y) = (term533 x z y).
Proof. exact (MK_COMB (@lem1577017 y x z) (@lem1577012 x z y)). Qed.
Lemma lem1577019 (y : real) (x : real) (z : real) : (term534 y x z) = (term534 y x z).
Proof. exact (eq_refl (term534 y x z)). Qed.
Lemma lem1577020 (x : real) (z : real) (y : real) : ((term521 y x z) = (term523 x z y)) = ((term521 y x z) = (term533 x z y)).
Proof. exact (MK_COMB (@lem1577019 y x z) (@lem1577018 x z y)). Qed.
Lemma lem1577021 (x : real) (z : real) (y : real) : (term521 y x z) = (term533 x z y).
Proof. exact (EQ_MP (@lem1577020 x z y) (@lem1577009 x z y)). Qed.
Lemma lem1577022 (x : real) (z : real) (y : real) : (term452 x z y) = (term453 x z y).
Proof. exact (@lem1483527 (real_max x z) y). Qed.
Lemma lem1577028 (x : real) (z : real) (y : real) : (term336 x z y) = (term337 x z y).
Proof. exact (@lem1483519 (real_max x z) y). Qed.
Lemma lem1577033 (y : real) (x : real) (z : real) : (term337 x z y) = (term338 y x z).
Proof. exact (@lem1483488 (term114 y) (real_max x z)). Qed.
Lemma lem1577035 (y : real) (x : real) (z : real) : (term336 x z y) = (term338 y x z).
Proof. exact (TRANS (@lem1577028 x z y) (@lem1577033 y x z)). Qed.
Lemma lem1577036 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577037 (y : real) (x : real) (z : real) : (term454 x z y) = (term455 y x z).
Proof. exact (MK_COMB (@lem1577036) (@lem1577035 y x z)). Qed.
Lemma lem1577038 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577039 (y : real) (x : real) (z : real) : (term453 x z y) = (term456 y x z).
Proof. exact (MK_COMB (@lem1577037 y x z) (@lem1577038)). Qed.
Lemma lem1577040 (y : real) (x : real) (z : real) : (term452 x z y) = (term456 y x z).
Proof. exact (TRANS (@lem1577022 x z y) (@lem1577039 y x z)). Qed.
Lemma lem1577041 (x : real) (z : real) : (term179 x z) = (term342 x z).
Proof. exact (@lem1483525 (term175 x z) term48). Qed.
Lemma lem1577059 (x : real) (z : real) : (term343 x z) = (term344 x z).
Proof. exact (@lem1483519 (term175 x z) term48). Qed.
Lemma lem1577061 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577062 : term227 = term48.
Proof. exact (@lem1577061 term36). Qed.
Lemma lem1577063 (x : real) (z : real) : (term345 x z) = (term345 x z).
Proof. exact (eq_refl (term345 x z)). Qed.
Lemma lem1577064 (x : real) (z : real) : (term344 x z) = (term346 x z).
Proof. exact (MK_COMB (@lem1577063 x z) (@lem1577062)). Qed.
Lemma lem1577065 (x : real) (z : real) : (term346 x z) = (term175 x z).
Proof. exact (@lem1483450 (term175 x z)). Qed.
Lemma lem1577066 (x : real) (z : real) : (term344 x z) = (term175 x z).
Proof. exact (TRANS (@lem1577064 x z) (@lem1577065 x z)). Qed.
Lemma lem1577068 (x : real) (z : real) : (term343 x z) = (term175 x z).
Proof. exact (TRANS (@lem1577059 x z) (@lem1577066 x z)). Qed.
Lemma lem1577069 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577070 (x : real) (z : real) : (term347 x z) = (term177 x z).
Proof. exact (MK_COMB (@lem1577069) (@lem1577068 x z)). Qed.
Lemma lem1577071 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577072 (x : real) (z : real) : (term342 x z) = (term179 x z).
Proof. exact (MK_COMB (@lem1577070 x z) (@lem1577071)). Qed.
Lemma lem1577073 (x : real) (z : real) : (term179 x z) = (term179 x z).
Proof. exact (TRANS (@lem1577041 x z) (@lem1577072 x z)). Qed.
Lemma lem1577074 (y : real) (x : real) (z : real) : (term341 y x z) = (term354 y x z).
Proof. exact (@lem1483525 (term338 y x z) term48). Qed.
Lemma lem1577092 (y : real) (x : real) (z : real) : (term355 y x z) = (term356 y x z).
Proof. exact (@lem1483519 (term338 y x z) term48). Qed.
Lemma lem1577094 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577095 : term227 = term48.
Proof. exact (@lem1577094 term36). Qed.
Lemma lem1577096 (y : real) (x : real) (z : real) : (term357 y x z) = (term357 y x z).
Proof. exact (eq_refl (term357 y x z)). Qed.
Lemma lem1577097 (y : real) (x : real) (z : real) : (term356 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1577096 y x z) (@lem1577095)). Qed.
Lemma lem1577098 (y : real) (x : real) (z : real) : (term358 y x z) = (term338 y x z).
Proof. exact (@lem1483450 (term338 y x z)). Qed.
Lemma lem1577099 (y : real) (x : real) (z : real) : (term356 y x z) = (term338 y x z).
Proof. exact (TRANS (@lem1577097 y x z) (@lem1577098 y x z)). Qed.
Lemma lem1577101 (y : real) (x : real) (z : real) : (term355 y x z) = (term338 y x z).
Proof. exact (TRANS (@lem1577092 y x z) (@lem1577099 y x z)). Qed.
Lemma lem1577102 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577103 (y : real) (x : real) (z : real) : (term359 y x z) = (term340 y x z).
Proof. exact (MK_COMB (@lem1577102) (@lem1577101 y x z)). Qed.
Lemma lem1577104 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577105 (y : real) (x : real) (z : real) : (term354 y x z) = (term341 y x z).
Proof. exact (MK_COMB (@lem1577103 y x z) (@lem1577104)). Qed.
Lemma lem1577106 (y : real) (x : real) (z : real) : (term341 y x z) = (term341 y x z).
Proof. exact (TRANS (@lem1577074 y x z) (@lem1577105 y x z)). Qed.
Lemma lem1577107 (x : real) (z : real) : (term185 x z) = (term348 x z).
Proof. exact (@lem1483525 (term181 x z) term48). Qed.
Lemma lem1577125 (x : real) (z : real) : (term349 x z) = (term350 x z).
Proof. exact (@lem1483519 (term181 x z) term48). Qed.
Lemma lem1577127 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577128 : term227 = term48.
Proof. exact (@lem1577127 term36). Qed.
Lemma lem1577129 (x : real) (z : real) : (term351 x z) = (term351 x z).
Proof. exact (eq_refl (term351 x z)). Qed.
Lemma lem1577130 (x : real) (z : real) : (term350 x z) = (term352 x z).
Proof. exact (MK_COMB (@lem1577129 x z) (@lem1577128)). Qed.
Lemma lem1577131 (x : real) (z : real) : (term352 x z) = (term181 x z).
Proof. exact (@lem1483450 (term181 x z)). Qed.
Lemma lem1577132 (x : real) (z : real) : (term350 x z) = (term181 x z).
Proof. exact (TRANS (@lem1577130 x z) (@lem1577131 x z)). Qed.
Lemma lem1577134 (x : real) (z : real) : (term349 x z) = (term181 x z).
Proof. exact (TRANS (@lem1577125 x z) (@lem1577132 x z)). Qed.
Lemma lem1577135 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577136 (x : real) (z : real) : (term353 x z) = (term183 x z).
Proof. exact (MK_COMB (@lem1577135) (@lem1577134 x z)). Qed.
Lemma lem1577137 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577138 (x : real) (z : real) : (term348 x z) = (term185 x z).
Proof. exact (MK_COMB (@lem1577136 x z) (@lem1577137)). Qed.
Lemma lem1577139 (x : real) (z : real) : (term185 x z) = (term185 x z).
Proof. exact (TRANS (@lem1577107 x z) (@lem1577138 x z)). Qed.
Lemma lem1577140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577141 (y : real) (x : real) (z : real) : (term362 y x z) = (term362 y x z).
Proof. exact (MK_COMB (@lem1577140) (@lem1577106 y x z)). Qed.
Lemma lem1577142 (y : real) (x : real) (z : real) : (term535 y x z) = (term535 y x z).
Proof. exact (MK_COMB (@lem1577141 y x z) (@lem1577139 x z)). Qed.
Lemma lem1577143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577144 (x : real) (z : real) : (term361 x z) = (term361 x z).
Proof. exact (MK_COMB (@lem1577143) (@lem1577073 x z)). Qed.
Lemma lem1577145 (y : real) (x : real) (z : real) : (term528 y x z) = (term528 y x z).
Proof. exact (MK_COMB (@lem1577144 x z) (@lem1577142 y x z)). Qed.
Lemma lem1577146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577147 (y : real) (x : real) (z : real) : (term445 x z y) = (term459 y x z).
Proof. exact (MK_COMB (@lem1577146) (@lem1577040 y x z)). Qed.
Lemma lem1577148 (y : real) (x : real) (z : real) : (term530 y x z) = (term536 y x z).
Proof. exact (MK_COMB (@lem1577147 y x z) (@lem1577145 y x z)). Qed.
Lemma lem1577149 (y : real) (x : real) (z : real) : (term461 y x z) = (term462 y x z).
Proof. exact (@lem1483525 y (real_max x z)). Qed.
Lemma lem1577162 (y : real) (x : real) (z : real) : (term326 y x z) = (term327 y x z).
Proof. exact (@lem1483519 y (real_max x z)). Qed.
Lemma lem1577163 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577164 (y : real) (x : real) (z : real) : (term463 y x z) = (term464 y x z).
Proof. exact (MK_COMB (@lem1577163) (@lem1577162 y x z)). Qed.
Lemma lem1577165 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577166 (y : real) (x : real) (z : real) : (term462 y x z) = (term465 y x z).
Proof. exact (MK_COMB (@lem1577164 y x z) (@lem1577165)). Qed.
Lemma lem1577167 (y : real) (x : real) (z : real) : (term461 y x z) = (term465 y x z).
Proof. exact (TRANS (@lem1577149 y x z) (@lem1577166 y x z)). Qed.
Lemma lem1577168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577169 (y : real) : (term241 y) = term242.
Proof. exact (MK_COMB (@lem1577168) (@lem1575389 y)). Qed.
Lemma lem1577170 (y : real) (z : real) : (term198 z y) = (term265 y z).
Proof. exact (MK_COMB (@lem1577169 y) (@lem1576088 y z)). Qed.
Lemma lem1577171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577172 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1577171) (@lem1575422 x y)). Qed.
Lemma lem1577173 (x : real) (y : real) (z : real) : (term381 x z y) = (term382 x y z).
Proof. exact (MK_COMB (@lem1577172 x y) (@lem1577170 y z)). Qed.
Lemma lem1577174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577175 (y : real) (x : real) (z : real) : (term440 y x z) = (term469 y x z).
Proof. exact (MK_COMB (@lem1577174) (@lem1577167 y x z)). Qed.
Lemma lem1577176 (x : real) (y : real) (z : real) : (term526 x z y) = (term567 x y z).
Proof. exact (MK_COMB (@lem1577175 y x z) (@lem1577173 x y z)). Qed.
Lemma lem1577177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577178 (y : real) (x : real) (z : real) : (term532 y x z) = (term539 y x z).
Proof. exact (MK_COMB (@lem1577177) (@lem1577148 y x z)). Qed.
Lemma lem1577179 (x : real) (y : real) (z : real) : (term533 x z y) = (term568 x y z).
Proof. exact (MK_COMB (@lem1577178 y x z) (@lem1577176 x y z)). Qed.
Lemma lem1577180 (x : real) (y : real) (z : real) : (term521 y x z) = (term568 x y z).
Proof. exact (TRANS (@lem1577021 x z y) (@lem1577179 x y z)). Qed.
Lemma lem1577182 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1577183 (x : real) (y : real) (z : real) : (term465 y x z) = (term386 x y z).
Proof. exact (@lem1577182 x y z term48). Qed.
Lemma lem1577200 (y : real) (z : real) : (term249 y z) = (term249 y z).
Proof. exact (eq_refl (term249 y z)). Qed.
Lemma lem1577213 (x : real) (y : real) : (term207 y x) = (term208 x y).
Proof. exact (@lem1483488 (term114 x) y). Qed.
Lemma lem1577214 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577215 (x : real) (y : real) : (term248 y x) = (term240 x y).
Proof. exact (MK_COMB (@lem1577214) (@lem1577213 x y)). Qed.
Lemma lem1577216 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577217 (x : real) (y : real) : (term249 y x) = (term233 x y).
Proof. exact (MK_COMB (@lem1577215 x y) (@lem1577216)). Qed.
Lemma lem1577218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577219 (x : real) (y : real) : (term257 y x) = (term256 x y).
Proof. exact (MK_COMB (@lem1577218) (@lem1577217 x y)). Qed.
Lemma lem1577220 (x : real) (y : real) (z : real) : (term386 x y z) = (term559 x y z).
Proof. exact (MK_COMB (@lem1577219 x y) (@lem1577200 y z)). Qed.
Lemma lem1577221 (x : real) (y : real) (z : real) : (term465 y x z) = (term559 x y z).
Proof. exact (TRANS (@lem1577183 x y z) (@lem1577220 x y z)). Qed.
Lemma lem1577222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577223 (x : real) (y : real) (z : real) : (term469 y x z) = (term569 x y z).
Proof. exact (MK_COMB (@lem1577222) (@lem1577221 x y z)). Qed.
Lemma lem1577224 (x : real) (y : real) (z : real) : (term382 x y z) = (term382 x y z).
Proof. exact (eq_refl (term382 x y z)). Qed.
Lemma lem1577227 (x : real) (y : real) (z : real) : (term567 x y z) = (term570 x y z).
Proof. exact (MK_COMB (@lem1577223 x y z) (@lem1577224 x y z)). Qed.
Lemma lem1577229 (y : real) (x : real) (z : real) : (term542 y x z) = (term536 y x z).
Proof. exact (eq_refl (term542 y x z)). Qed.
Lemma lem1577230 (y : real) (x : real) (z : real) : (term536 y x z) = (term542 y x z).
Proof. exact (SYM (@lem1577229 y x z)). Qed.
Lemma lem1577231 (y : real) (z : real) (x : real) : (term542 y x z) = (term543 y z x).
Proof. exact (@lem1483205 z (term544 x y z) x). Qed.
Lemma lem1577232 (y : real) (z : real) (x : real) : (term536 y x z) = (term543 y z x).
Proof. exact (TRANS (@lem1577230 y x z) (@lem1577231 y z x)). Qed.
Lemma lem1577233 (y : real) (z : real) (x : real) : (term545 y z x) = (term546 y z x).
Proof. exact (eq_refl (term545 y z x)). Qed.
Lemma lem1577234 (x : real) (z : real) : (term194 x z) = (term194 x z).
Proof. exact (eq_refl (term194 x z)). Qed.
Lemma lem1577235 (y : real) (z : real) (x : real) : (term547 y z x) = (term548 y z x).
Proof. exact (MK_COMB (@lem1577234 x z) (@lem1577233 y z x)). Qed.
Lemma lem1577236 (x : real) (y : real) (z : real) : (term549 x y z) = (term550 x y z).
Proof. exact (eq_refl (term549 x y z)). Qed.
Lemma lem1577237 (z : real) (x : real) : (term199 z x) = (term199 z x).
Proof. exact (eq_refl (term199 z x)). Qed.
Lemma lem1577238 (x : real) (y : real) (z : real) : (term551 x y z) = (term552 x y z).
Proof. exact (MK_COMB (@lem1577237 z x) (@lem1577236 x y z)). Qed.
Lemma lem1577239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577240 (x : real) (y : real) (z : real) : (term553 x y z) = (term554 x y z).
Proof. exact (MK_COMB (@lem1577239) (@lem1577238 x y z)). Qed.
Lemma lem1577241 (y : real) (z : real) (x : real) : (term543 y z x) = (term555 y z x).
Proof. exact (MK_COMB (@lem1577240 x y z) (@lem1577235 y z x)). Qed.
Lemma lem1577242 (y : real) (x : real) (z : real) : (term556 y x z) = (term556 y x z).
Proof. exact (eq_refl (term556 y x z)). Qed.
Lemma lem1577243 (y : real) (z : real) (x : real) : ((term536 y x z) = (term543 y z x)) = ((term536 y x z) = (term555 y z x)).
Proof. exact (MK_COMB (@lem1577242 y x z) (@lem1577241 y z x)). Qed.
Lemma lem1577244 (y : real) (z : real) (x : real) : (term536 y x z) = (term555 y z x).
Proof. exact (EQ_MP (@lem1577243 y z x) (@lem1577232 y z x)). Qed.
Lemma lem1577245 (z : real) (x : real) : (real_ge z x) = (term206 z x).
Proof. exact (@lem1483527 z x). Qed.
Lemma lem1577251 (z : real) (x : real) : (real_sub z x) = (term207 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1577256 (x : real) (z : real) : (term207 z x) = (term208 x z).
Proof. exact (@lem1483488 (term114 x) z). Qed.
Lemma lem1577258 (x : real) (z : real) : (real_sub z x) = (term208 x z).
Proof. exact (TRANS (@lem1577251 z x) (@lem1577256 x z)). Qed.
Lemma lem1577259 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577260 (x : real) (z : real) : (term209 z x) = (term210 x z).
Proof. exact (MK_COMB (@lem1577259) (@lem1577258 x z)). Qed.
Lemma lem1577261 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577262 (x : real) (z : real) : (term206 z x) = (term211 x z).
Proof. exact (MK_COMB (@lem1577260 x z) (@lem1577261)). Qed.
Lemma lem1577263 (x : real) (z : real) : (real_ge z x) = (term211 x z).
Proof. exact (TRANS (@lem1577245 z x) (@lem1577262 x z)). Qed.
Lemma lem1577264 (y : real) (z : real) : (term211 y z) = (term490 y z).
Proof. exact (@lem1483527 (term208 y z) term48). Qed.
Lemma lem1577282 (y : real) (z : real) : (term235 y z) = (term236 y z).
Proof. exact (@lem1483519 (term208 y z) term48). Qed.
Lemma lem1577284 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577285 : term227 = term48.
Proof. exact (@lem1577284 term36). Qed.
Lemma lem1577286 (y : real) (z : real) : (term237 y z) = (term237 y z).
Proof. exact (eq_refl (term237 y z)). Qed.
Lemma lem1577287 (y : real) (z : real) : (term236 y z) = (term238 y z).
Proof. exact (MK_COMB (@lem1577286 y z) (@lem1577285)). Qed.
Lemma lem1577288 (y : real) (z : real) : (term238 y z) = (term208 y z).
Proof. exact (@lem1483450 (term208 y z)). Qed.
Lemma lem1577289 (y : real) (z : real) : (term236 y z) = (term208 y z).
Proof. exact (TRANS (@lem1577287 y z) (@lem1577288 y z)). Qed.
Lemma lem1577291 (y : real) (z : real) : (term235 y z) = (term208 y z).
Proof. exact (TRANS (@lem1577282 y z) (@lem1577289 y z)). Qed.
Lemma lem1577292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577293 (y : real) (z : real) : (term491 y z) = (term210 y z).
Proof. exact (MK_COMB (@lem1577292) (@lem1577291 y z)). Qed.
Lemma lem1577294 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577295 (y : real) (z : real) : (term490 y z) = (term211 y z).
Proof. exact (MK_COMB (@lem1577293 y z) (@lem1577294)). Qed.
Lemma lem1577296 (y : real) (z : real) : (term211 y z) = (term211 y z).
Proof. exact (TRANS (@lem1577264 y z) (@lem1577295 y z)). Qed.
Lemma lem1577297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577298 (y : real) (z : real) : (term256 y z) = (term256 y z).
Proof. exact (MK_COMB (@lem1577297) (@lem1575855 y z)). Qed.
Lemma lem1577299 (y : real) (z : real) : (term193 y z) = (term268 y z).
Proof. exact (MK_COMB (@lem1577298 y z) (@lem1575898 z)). Qed.
Lemma lem1577300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577301 (x : real) (z : real) : (term256 x z) = (term256 x z).
Proof. exact (MK_COMB (@lem1577300) (@lem1575822 x z)). Qed.
Lemma lem1577302 (x : real) (y : real) (z : real) : (term316 x y z) = (term331 x y z).
Proof. exact (MK_COMB (@lem1577301 x z) (@lem1577299 y z)). Qed.
Lemma lem1577303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577304 (y : real) (z : real) : (term244 y z) = (term244 y z).
Proof. exact (MK_COMB (@lem1577303) (@lem1577296 y z)). Qed.
Lemma lem1577305 (x : real) (y : real) (z : real) : (term550 x y z) = (term557 x y z).
Proof. exact (MK_COMB (@lem1577304 y z) (@lem1577302 x y z)). Qed.
Lemma lem1577306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577307 (x : real) (z : real) : (term199 z x) = (term244 x z).
Proof. exact (MK_COMB (@lem1577306) (@lem1577263 x z)). Qed.
Lemma lem1577308 (x : real) (y : real) (z : real) : (term552 x y z) = (term558 x y z).
Proof. exact (MK_COMB (@lem1577307 x z) (@lem1577305 x y z)). Qed.
Lemma lem1577309 (x : real) (z : real) : (real_gt x z) = (term246 x z).
Proof. exact (@lem1483525 x z). Qed.
Lemma lem1577322 (x : real) (z : real) : (real_sub x z) = (term207 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1577323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577324 (x : real) (z : real) : (term247 x z) = (term248 x z).
Proof. exact (MK_COMB (@lem1577323) (@lem1577322 x z)). Qed.
Lemma lem1577325 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577326 (x : real) (z : real) : (term246 x z) = (term249 x z).
Proof. exact (MK_COMB (@lem1577324 x z) (@lem1577325)). Qed.
Lemma lem1577327 (x : real) (z : real) : (real_gt x z) = (term249 x z).
Proof. exact (TRANS (@lem1577309 x z) (@lem1577326 x z)). Qed.
Lemma lem1577328 (y : real) (x : real) : (term211 y x) = (term490 y x).
Proof. exact (@lem1483527 (term208 y x) term48). Qed.
Lemma lem1577329 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577342 (x : real) (y : real) : (term208 y x) = (term207 x y).
Proof. exact (@lem1483488 x (term114 y)). Qed.
Lemma lem1577343 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1577344 (x : real) (y : real) : (term250 y x) = (term251 x y).
Proof. exact (MK_COMB (@lem1577343) (@lem1577342 x y)). Qed.
Lemma lem1577345 (x : real) (y : real) : (term235 y x) = (term252 x y).
Proof. exact (MK_COMB (@lem1577344 x y) (@lem1577329)). Qed.
Lemma lem1577346 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (@lem1483519 (term207 x y) term48). Qed.
Lemma lem1577348 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577349 : term227 = term48.
Proof. exact (@lem1577348 term36). Qed.
Lemma lem1577350 (x : real) (y : real) : (term254 x y) = (term254 x y).
Proof. exact (eq_refl (term254 x y)). Qed.
Lemma lem1577351 (x : real) (y : real) : (term253 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1577350 x y) (@lem1577349)). Qed.
Lemma lem1577352 (x : real) (y : real) : (term255 x y) = (term207 x y).
Proof. exact (@lem1483450 (term207 x y)). Qed.
Lemma lem1577353 (x : real) (y : real) : (term253 x y) = (term207 x y).
Proof. exact (TRANS (@lem1577351 x y) (@lem1577352 x y)). Qed.
Lemma lem1577354 (x : real) (y : real) : (term252 x y) = (term207 x y).
Proof. exact (TRANS (@lem1577346 x y) (@lem1577353 x y)). Qed.
Lemma lem1577355 (x : real) (y : real) : (term235 y x) = (term207 x y).
Proof. exact (TRANS (@lem1577345 x y) (@lem1577354 x y)). Qed.
Lemma lem1577356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577357 (x : real) (y : real) : (term491 y x) = (term263 x y).
Proof. exact (MK_COMB (@lem1577356) (@lem1577355 x y)). Qed.
Lemma lem1577358 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577359 (x : real) (y : real) : (term490 y x) = (term264 x y).
Proof. exact (MK_COMB (@lem1577357 x y) (@lem1577358)). Qed.
Lemma lem1577360 (x : real) (y : real) : (term211 y x) = (term264 x y).
Proof. exact (TRANS (@lem1577328 y x) (@lem1577359 x y)). Qed.
Lemma lem1577361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577362 (x : real) (y : real) : (term256 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1577361) (@lem1575480 x y)). Qed.
Lemma lem1577363 (y : real) (x : real) (z : real) : (term385 y z x) = (term386 y x z).
Proof. exact (MK_COMB (@lem1577362 x y) (@lem1576133 x z)). Qed.
Lemma lem1577364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577365 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1577364) (@lem1575523 x)). Qed.
Lemma lem1577366 (y : real) (x : real) (z : real) : (term387 y z x) = (term388 y x z).
Proof. exact (MK_COMB (@lem1577365 x) (@lem1577363 y x z)). Qed.
Lemma lem1577367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577368 (x : real) (y : real) : (term244 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem1577367) (@lem1577360 x y)). Qed.
Lemma lem1577369 (y : real) (x : real) (z : real) : (term546 y z x) = (term571 y x z).
Proof. exact (MK_COMB (@lem1577368 x y) (@lem1577366 y x z)). Qed.
Lemma lem1577370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577371 (x : real) (z : real) : (term194 x z) = (term257 x z).
Proof. exact (MK_COMB (@lem1577370) (@lem1577327 x z)). Qed.
Lemma lem1577372 (y : real) (x : real) (z : real) : (term548 y z x) = (term572 y x z).
Proof. exact (MK_COMB (@lem1577371 x z) (@lem1577369 y x z)). Qed.
Lemma lem1577373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577374 (x : real) (y : real) (z : real) : (term554 x y z) = (term563 x y z).
Proof. exact (MK_COMB (@lem1577373) (@lem1577308 x y z)). Qed.
Lemma lem1577375 (y : real) (x : real) (z : real) : (term555 y z x) = (term573 y x z).
Proof. exact (MK_COMB (@lem1577374 x y z) (@lem1577372 y x z)). Qed.
Lemma lem1577387 (y : real) (x : real) (z : real) : (term536 y x z) = (term573 y x z).
Proof. exact (TRANS (@lem1577244 y z x) (@lem1577375 y x z)). Qed.
Lemma lem1577388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577389 (y : real) (x : real) (z : real) : (term539 y x z) = (term574 y x z).
Proof. exact (MK_COMB (@lem1577388) (@lem1577387 y x z)). Qed.
Lemma lem1577390 (x : real) (y : real) (z : real) : (term568 x y z) = (term575 x y z).
Proof. exact (MK_COMB (@lem1577389 y x z) (@lem1577227 x y z)). Qed.
Lemma lem1577391 (x : real) (y : real) (z : real) : (term521 y x z) = (term575 x y z).
Proof. exact (TRANS (@lem1577180 x y z) (@lem1577390 x y z)). Qed.
Lemma lem1577392 (x : real) (y : real) (z : real) : (term101 y x z) = (term575 x y z).
Proof. exact (TRANS (@lem1577005 y x z) (@lem1577391 x y z)). Qed.
Lemma lem1577393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577394 (y : real) (x : real) (z : real) : (term107 y x z) = (term576 y x z).
Proof. exact (MK_COMB (@lem1577393) (@lem1576920 y x z)). Qed.
Lemma lem1577395 (x : real) (y : real) (z : real) : (term108 y x z) = (term577 x y z).
Proof. exact (MK_COMB (@lem1577394 y x z) (@lem1577392 x y z)). Qed.
Lemma lem1577397 (x : real) : (term578 x) = (term133 x).
Proof. exact (eq_refl (term578 x)). Qed.
Lemma lem1577398 (x : real) : (term133 x) = (term578 x).
Proof. exact (SYM (@lem1577397 x)). Qed.
Lemma lem1577399 (x : real) : (term578 x) = (term579 x).
Proof. exact (@lem1483205 x (term580 x) x). Qed.
Lemma lem1577400 (x : real) : (term133 x) = (term579 x).
Proof. exact (TRANS (@lem1577398 x) (@lem1577399 x)). Qed.
Lemma lem1577401 (x : real) : (term581 x) = (term212 x).
Proof. exact (eq_refl (term581 x)). Qed.
Lemma lem1577402 (x : real) : (term582 x) = (term582 x).
Proof. exact (eq_refl (term582 x)). Qed.
Lemma lem1577403 (x : real) : (term583 x) = (term584 x).
Proof. exact (MK_COMB (@lem1577402 x) (@lem1577401 x)). Qed.
Lemma lem1577404 (x : real) : (term581 x) = (term212 x).
Proof. exact (eq_refl (term581 x)). Qed.
Lemma lem1577405 (x : real) : (term585 x) = (term585 x).
Proof. exact (eq_refl (term585 x)). Qed.
Lemma lem1577406 (x : real) : (term586 x) = (term587 x).
Proof. exact (MK_COMB (@lem1577405 x) (@lem1577404 x)). Qed.
Lemma lem1577407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577408 (x : real) : (term588 x) = (term589 x).
Proof. exact (MK_COMB (@lem1577407) (@lem1577406 x)). Qed.
Lemma lem1577409 (x : real) : (term579 x) = (term590 x).
Proof. exact (MK_COMB (@lem1577408 x) (@lem1577403 x)). Qed.
Lemma lem1577410 (x : real) : (term591 x) = (term591 x).
Proof. exact (eq_refl (term591 x)). Qed.
Lemma lem1577411 (x : real) : ((term133 x) = (term579 x)) = ((term133 x) = (term590 x)).
Proof. exact (MK_COMB (@lem1577410 x) (@lem1577409 x)). Qed.
Lemma lem1577412 (x : real) : (term133 x) = (term590 x).
Proof. exact (EQ_MP (@lem1577411 x) (@lem1577400 x)). Qed.
Lemma lem1577413 (x : real) : (real_ge x x) = (term592 x).
Proof. exact (@lem1483527 x x). Qed.
Lemma lem1577419 (x : real) : (real_sub x x) = (term593 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1577423 (x : real) : (term593 x) = (term215 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1577425 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577426 : term217 = term48.
Proof. exact (@lem1577425 term36). Qed.
Lemma lem1577427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577428 : term218 = term219.
Proof. exact (MK_COMB (@lem1577427) (@lem1577426)). Qed.
Lemma lem1577429 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577430 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577428) (@lem1577429 x)). Qed.
Lemma lem1577431 (x : real) : (term593 x) = (term220 x).
Proof. exact (TRANS (@lem1577423 x) (@lem1577430 x)). Qed.
Lemma lem1577432 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577434 (x : real) : (term593 x) = term48.
Proof. exact (TRANS (@lem1577431 x) (@lem1577432 x)). Qed.
Lemma lem1577436 (x : real) : (real_sub x x) = term48.
Proof. exact (TRANS (@lem1577419 x) (@lem1577434 x)). Qed.
Lemma lem1577437 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577438 (x : real) : (term594 x) = term595.
Proof. exact (MK_COMB (@lem1577437) (@lem1577436 x)). Qed.
Lemma lem1577439 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577440 (x : real) : (term592 x) = term596.
Proof. exact (MK_COMB (@lem1577438 x) (@lem1577439)). Qed.
Lemma lem1577441 (x : real) : (real_ge x x) = term596.
Proof. exact (TRANS (@lem1577413 x) (@lem1577440 x)). Qed.
Lemma lem1577442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577443 (x : real) : (term585 x) = term597.
Proof. exact (MK_COMB (@lem1577442) (@lem1577441 x)). Qed.
Lemma lem1577444 (x : real) : (term587 x) = term598.
Proof. exact (MK_COMB (@lem1577443 x) (@lem1575523 x)). Qed.
Lemma lem1577445 (x : real) : (real_gt x x) = (term599 x).
Proof. exact (@lem1483525 x x). Qed.
Lemma lem1577451 (x : real) : (real_sub x x) = (term593 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1577455 (x : real) : (term593 x) = (term215 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1577457 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577458 : term217 = term48.
Proof. exact (@lem1577457 term36). Qed.
Lemma lem1577459 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577460 : term218 = term219.
Proof. exact (MK_COMB (@lem1577459) (@lem1577458)). Qed.
Lemma lem1577461 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577462 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577460) (@lem1577461 x)). Qed.
Lemma lem1577463 (x : real) : (term593 x) = (term220 x).
Proof. exact (TRANS (@lem1577455 x) (@lem1577462 x)). Qed.
Lemma lem1577464 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577466 (x : real) : (term593 x) = term48.
Proof. exact (TRANS (@lem1577463 x) (@lem1577464 x)). Qed.
Lemma lem1577468 (x : real) : (real_sub x x) = term48.
Proof. exact (TRANS (@lem1577451 x) (@lem1577466 x)). Qed.
Lemma lem1577469 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577470 (x : real) : (term600 x) = term231.
Proof. exact (MK_COMB (@lem1577469) (@lem1577468 x)). Qed.
Lemma lem1577471 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577472 (x : real) : (term599 x) = term232.
Proof. exact (MK_COMB (@lem1577470 x) (@lem1577471)). Qed.
Lemma lem1577473 (x : real) : (real_gt x x) = term232.
Proof. exact (TRANS (@lem1577445 x) (@lem1577472 x)). Qed.
Lemma lem1577474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577475 (x : real) : (term582 x) = term242.
Proof. exact (MK_COMB (@lem1577474) (@lem1577473 x)). Qed.
Lemma lem1577476 (x : real) : (term584 x) = term601.
Proof. exact (MK_COMB (@lem1577475 x) (@lem1575523 x)). Qed.
Lemma lem1577477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577478 (x : real) : (term589 x) = term602.
Proof. exact (MK_COMB (@lem1577477) (@lem1577444 x)). Qed.
Lemma lem1577479 (x : real) : (term590 x) = term603.
Proof. exact (MK_COMB (@lem1577478 x) (@lem1577476 x)). Qed.
Lemma lem1577491 (x : real) : (term133 x) = term603.
Proof. exact (TRANS (@lem1577412 x) (@lem1577479 x)). Qed.
Lemma lem1577493 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1577494 (x : real) : (term129 x) = (term604 x).
Proof. exact (@lem1577493 x x x term48). Qed.
Lemma lem1577506 (x : real) : (term593 x) = (term215 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1577508 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577509 : term217 = term48.
Proof. exact (@lem1577508 term36). Qed.
Lemma lem1577510 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577511 : term218 = term219.
Proof. exact (MK_COMB (@lem1577510) (@lem1577509)). Qed.
Lemma lem1577512 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577513 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577511) (@lem1577512 x)). Qed.
Lemma lem1577514 (x : real) : (term593 x) = (term220 x).
Proof. exact (TRANS (@lem1577506 x) (@lem1577513 x)). Qed.
Lemma lem1577515 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577517 (x : real) : (term593 x) = term48.
Proof. exact (TRANS (@lem1577514 x) (@lem1577515 x)). Qed.
Lemma lem1577518 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577519 (x : real) : (term605 x) = term231.
Proof. exact (MK_COMB (@lem1577518) (@lem1577517 x)). Qed.
Lemma lem1577520 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577521 (x : real) : (term606 x) = term232.
Proof. exact (MK_COMB (@lem1577519 x) (@lem1577520)). Qed.
Lemma lem1577533 (x : real) : (term593 x) = (term215 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1577535 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577536 : term217 = term48.
Proof. exact (@lem1577535 term36). Qed.
Lemma lem1577537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577538 : term218 = term219.
Proof. exact (MK_COMB (@lem1577537) (@lem1577536)). Qed.
Lemma lem1577539 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577540 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577538) (@lem1577539 x)). Qed.
Lemma lem1577541 (x : real) : (term593 x) = (term220 x).
Proof. exact (TRANS (@lem1577533 x) (@lem1577540 x)). Qed.
Lemma lem1577542 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577544 (x : real) : (term593 x) = term48.
Proof. exact (TRANS (@lem1577541 x) (@lem1577542 x)). Qed.
Lemma lem1577545 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577546 (x : real) : (term605 x) = term231.
Proof. exact (MK_COMB (@lem1577545) (@lem1577544 x)). Qed.
Lemma lem1577547 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577548 (x : real) : (term606 x) = term232.
Proof. exact (MK_COMB (@lem1577546 x) (@lem1577547)). Qed.
Lemma lem1577549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577550 (x : real) : (term607 x) = term242.
Proof. exact (MK_COMB (@lem1577549) (@lem1577548 x)). Qed.
Lemma lem1577551 (x : real) : (term604 x) = term601.
Proof. exact (MK_COMB (@lem1577550 x) (@lem1577521 x)). Qed.
Lemma lem1577554 (x : real) : (term129 x) = term601.
Proof. exact (TRANS (@lem1577494 x) (@lem1577551 x)). Qed.
Lemma lem1577555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577556 (x : real) : (term135 x) = term608.
Proof. exact (MK_COMB (@lem1577555) (@lem1577491 x)). Qed.
Lemma lem1577557 (x : real) : (term136 x) = term609.
Proof. exact (MK_COMB (@lem1577556 x) (@lem1577554 x)). Qed.
Lemma lem1577559 (x : real) (a : real) (y : real) (r : real) : (term262 x y a r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1577560 (x : real) (y : real) : (term158 x y) = (term610 x y).
Proof. exact (@lem1577559 x (term2 x y) y term48). Qed.
Lemma lem1577573 (x : real) (y : real) : (term611 x y) = (term612 x y).
Proof. exact (@lem1483488 (term114 y) (term2 x y)). Qed.
Lemma lem1577574 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577575 (x : real) (y : real) : (term613 x y) = (term614 x y).
Proof. exact (MK_COMB (@lem1577574) (@lem1577573 x y)). Qed.
Lemma lem1577576 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577577 (x : real) (y : real) : (term615 x y) = (term616 x y).
Proof. exact (MK_COMB (@lem1577575 x y) (@lem1577576)). Qed.
Lemma lem1577590 (x : real) (y : real) : (term617 y x) = (term618 x y).
Proof. exact (@lem1483488 (term114 x) (term2 x y)). Qed.
Lemma lem1577591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577592 (x : real) (y : real) : (term619 y x) = (term620 x y).
Proof. exact (MK_COMB (@lem1577591) (@lem1577590 x y)). Qed.
Lemma lem1577593 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577594 (x : real) (y : real) : (term621 y x) = (term622 x y).
Proof. exact (MK_COMB (@lem1577592 x y) (@lem1577593)). Qed.
Lemma lem1577595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577596 (x : real) (y : real) : (term623 y x) = (term624 x y).
Proof. exact (MK_COMB (@lem1577595) (@lem1577594 x y)). Qed.
Lemma lem1577597 (x : real) (y : real) : (term610 x y) = (term625 x y).
Proof. exact (MK_COMB (@lem1577596 x y) (@lem1577577 x y)). Qed.
Lemma lem1577598 (x : real) (y : real) : (term158 x y) = (term625 x y).
Proof. exact (TRANS (@lem1577560 x y) (@lem1577597 x y)). Qed.
Lemma lem1577599 (x : real) (y : real) : (term626 x y) = (term625 x y).
Proof. exact (eq_refl (term626 x y)). Qed.
Lemma lem1577600 (x : real) (y : real) : (term625 x y) = (term626 x y).
Proof. exact (SYM (@lem1577599 x y)). Qed.
Lemma lem1577601 (y : real) (x : real) : (term626 x y) = (term627 y x).
Proof. exact (@lem1483205 (real_max x y) (term191 x y) x). Qed.
Lemma lem1577602 (y : real) (x : real) : (term625 x y) = (term627 y x).
Proof. exact (TRANS (@lem1577600 x y) (@lem1577601 y x)). Qed.
Lemma lem1577603 (y : real) (x : real) : (term197 y x) = (term198 y x).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1577604 (x : real) (y : real) : (term628 x y) = (term628 x y).
Proof. exact (eq_refl (term628 x y)). Qed.
Lemma lem1577605 (y : real) (x : real) : (term629 y x) = (term630 y x).
Proof. exact (MK_COMB (@lem1577604 x y) (@lem1577603 y x)). Qed.
Lemma lem1577606 (x : real) (y : real) : (term631 x y) = (term632 x y).
Proof. exact (eq_refl (term631 x y)). Qed.
Lemma lem1577607 (y : real) (x : real) : (term633 y x) = (term633 y x).
Proof. exact (eq_refl (term633 y x)). Qed.
Lemma lem1577608 (x : real) (y : real) : (term634 x y) = (term635 x y).
Proof. exact (MK_COMB (@lem1577607 y x) (@lem1577606 x y)). Qed.
Lemma lem1577609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577610 (x : real) (y : real) : (term636 x y) = (term637 x y).
Proof. exact (MK_COMB (@lem1577609) (@lem1577608 x y)). Qed.
Lemma lem1577611 (y : real) (x : real) : (term627 y x) = (term638 y x).
Proof. exact (MK_COMB (@lem1577610 x y) (@lem1577605 y x)). Qed.
Lemma lem1577612 (x : real) (y : real) : (term639 x y) = (term639 x y).
Proof. exact (eq_refl (term639 x y)). Qed.
Lemma lem1577613 (y : real) (x : real) : ((term625 x y) = (term627 y x)) = ((term625 x y) = (term638 y x)).
Proof. exact (MK_COMB (@lem1577612 x y) (@lem1577611 y x)). Qed.
Lemma lem1577614 (y : real) (x : real) : (term625 x y) = (term638 y x).
Proof. exact (EQ_MP (@lem1577613 y x) (@lem1577602 y x)). Qed.
Lemma lem1577615 (y : real) (x : real) : (term640 y x) = (term641 y x).
Proof. exact (@lem1483527 (real_max x y) x). Qed.
Lemma lem1577621 (y : real) (x : real) : (term642 y x) = (term174 y x).
Proof. exact (@lem1483519 (real_max x y) x). Qed.
Lemma lem1577626 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 (term114 x) (real_max x y)). Qed.
Lemma lem1577628 (x : real) (y : real) : (term642 y x) = (term175 x y).
Proof. exact (TRANS (@lem1577621 y x) (@lem1577626 x y)). Qed.
Lemma lem1577629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577630 (x : real) (y : real) : (term643 y x) = (term644 x y).
Proof. exact (MK_COMB (@lem1577629) (@lem1577628 x y)). Qed.
Lemma lem1577631 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577632 (x : real) (y : real) : (term641 y x) = (term645 x y).
Proof. exact (MK_COMB (@lem1577630 x y) (@lem1577631)). Qed.
Lemma lem1577633 (x : real) (y : real) : (term640 y x) = (term645 x y).
Proof. exact (TRANS (@lem1577615 y x) (@lem1577632 x y)). Qed.
Lemma lem1577634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577635 (x : real) (y : real) : (term361 x y) = (term361 x y).
Proof. exact (MK_COMB (@lem1577634) (@lem1575959 x y)). Qed.
Lemma lem1577636 (x : real) (y : real) : (term632 x y) = (term632 x y).
Proof. exact (MK_COMB (@lem1577635 x y) (@lem1575992 x y)). Qed.
Lemma lem1577637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577638 (x : real) (y : real) : (term633 y x) = (term646 x y).
Proof. exact (MK_COMB (@lem1577637) (@lem1577633 x y)). Qed.
Lemma lem1577639 (x : real) (y : real) : (term635 x y) = (term647 x y).
Proof. exact (MK_COMB (@lem1577638 x y) (@lem1577636 x y)). Qed.
Lemma lem1577640 (x : real) (y : real) : (term648 x y) = (term649 x y).
Proof. exact (@lem1483525 x (real_max x y)). Qed.
Lemma lem1577653 (x : real) (y : real) : (term650 x y) = (term651 x y).
Proof. exact (@lem1483519 x (real_max x y)). Qed.
Lemma lem1577654 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577655 (x : real) (y : real) : (term652 x y) = (term653 x y).
Proof. exact (MK_COMB (@lem1577654) (@lem1577653 x y)). Qed.
Lemma lem1577656 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577657 (x : real) (y : real) : (term649 x y) = (term654 x y).
Proof. exact (MK_COMB (@lem1577655 x y) (@lem1577656)). Qed.
Lemma lem1577658 (x : real) (y : real) : (term648 x y) = (term654 x y).
Proof. exact (TRANS (@lem1577640 x y) (@lem1577657 x y)). Qed.
Lemma lem1577659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577660 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1577659) (@lem1575523 x)). Qed.
Lemma lem1577661 (x : real) (y : real) : (term198 y x) = (term265 x y).
Proof. exact (MK_COMB (@lem1577660 x) (@lem1575480 x y)). Qed.
Lemma lem1577662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577663 (x : real) (y : real) : (term628 x y) = (term655 x y).
Proof. exact (MK_COMB (@lem1577662) (@lem1577658 x y)). Qed.
Lemma lem1577664 (x : real) (y : real) : (term630 y x) = (term656 x y).
Proof. exact (MK_COMB (@lem1577663 x y) (@lem1577661 x y)). Qed.
Lemma lem1577665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577666 (x : real) (y : real) : (term637 x y) = (term657 x y).
Proof. exact (MK_COMB (@lem1577665) (@lem1577639 x y)). Qed.
Lemma lem1577667 (x : real) (y : real) : (term638 y x) = (term658 x y).
Proof. exact (MK_COMB (@lem1577666 x y) (@lem1577664 x y)). Qed.
Lemma lem1577668 (x : real) (y : real) : (term625 x y) = (term658 x y).
Proof. exact (TRANS (@lem1577614 y x) (@lem1577667 x y)). Qed.
Lemma lem1577670 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1577671 (x : real) (y : real) : (term654 x y) = (term659 x y).
Proof. exact (@lem1577670 x x y term48). Qed.
Lemma lem1577688 (x : real) (y : real) : (term249 x y) = (term249 x y).
Proof. exact (eq_refl (term249 x y)). Qed.
Lemma lem1577700 (x : real) : (term593 x) = (term215 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1577702 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577703 : term217 = term48.
Proof. exact (@lem1577702 term36). Qed.
Lemma lem1577704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577705 : term218 = term219.
Proof. exact (MK_COMB (@lem1577704) (@lem1577703)). Qed.
Lemma lem1577706 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577707 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577705) (@lem1577706 x)). Qed.
Lemma lem1577708 (x : real) : (term593 x) = (term220 x).
Proof. exact (TRANS (@lem1577700 x) (@lem1577707 x)). Qed.
Lemma lem1577709 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577711 (x : real) : (term593 x) = term48.
Proof. exact (TRANS (@lem1577708 x) (@lem1577709 x)). Qed.
Lemma lem1577712 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577713 (x : real) : (term605 x) = term231.
Proof. exact (MK_COMB (@lem1577712) (@lem1577711 x)). Qed.
Lemma lem1577714 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577715 (x : real) : (term606 x) = term232.
Proof. exact (MK_COMB (@lem1577713 x) (@lem1577714)). Qed.
Lemma lem1577716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577717 (x : real) : (term607 x) = term242.
Proof. exact (MK_COMB (@lem1577716) (@lem1577715 x)). Qed.
Lemma lem1577718 (x : real) (y : real) : (term659 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem1577717 x) (@lem1577688 x y)). Qed.
Lemma lem1577719 (x : real) (y : real) : (term654 x y) = (term265 x y).
Proof. exact (TRANS (@lem1577671 x y) (@lem1577718 x y)). Qed.
Lemma lem1577720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577721 (x : real) (y : real) : (term655 x y) = (term467 x y).
Proof. exact (MK_COMB (@lem1577720) (@lem1577719 x y)). Qed.
Lemma lem1577722 (x : real) (y : real) : (term265 x y) = (term265 x y).
Proof. exact (eq_refl (term265 x y)). Qed.
Lemma lem1577725 (x : real) (y : real) : (term656 x y) = (term660 x y).
Proof. exact (MK_COMB (@lem1577721 x y) (@lem1577722 x y)). Qed.
Lemma lem1577727 (x : real) (y : real) : (term661 x y) = (term647 x y).
Proof. exact (eq_refl (term661 x y)). Qed.
Lemma lem1577728 (x : real) (y : real) : (term647 x y) = (term661 x y).
Proof. exact (SYM (@lem1577727 x y)). Qed.
Lemma lem1577729 (y : real) (x : real) : (term661 x y) = (term662 y x).
Proof. exact (@lem1483205 y (term663 x y) x). Qed.
Lemma lem1577730 (y : real) (x : real) : (term647 x y) = (term662 y x).
Proof. exact (TRANS (@lem1577728 x y) (@lem1577729 y x)). Qed.
Lemma lem1577731 (y : real) (x : real) : (term664 y x) = (term665 y x).
Proof. exact (eq_refl (term664 y x)). Qed.
Lemma lem1577732 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1577733 (y : real) (x : real) : (term666 y x) = (term667 y x).
Proof. exact (MK_COMB (@lem1577732 x y) (@lem1577731 y x)). Qed.
Lemma lem1577734 (x : real) (y : real) : (term668 x y) = (term669 x y).
Proof. exact (eq_refl (term668 x y)). Qed.
Lemma lem1577735 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1577736 (x : real) (y : real) : (term670 x y) = (term671 x y).
Proof. exact (MK_COMB (@lem1577735 y x) (@lem1577734 x y)). Qed.
Lemma lem1577737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577738 (x : real) (y : real) : (term672 x y) = (term673 x y).
Proof. exact (MK_COMB (@lem1577737) (@lem1577736 x y)). Qed.
Lemma lem1577739 (y : real) (x : real) : (term662 y x) = (term674 y x).
Proof. exact (MK_COMB (@lem1577738 x y) (@lem1577733 y x)). Qed.
Lemma lem1577740 (x : real) (y : real) : (term675 x y) = (term675 x y).
Proof. exact (eq_refl (term675 x y)). Qed.
Lemma lem1577741 (y : real) (x : real) : ((term647 x y) = (term662 y x)) = ((term647 x y) = (term674 y x)).
Proof. exact (MK_COMB (@lem1577740 x y) (@lem1577739 y x)). Qed.
Lemma lem1577742 (y : real) (x : real) : (term647 x y) = (term674 y x).
Proof. exact (EQ_MP (@lem1577741 y x) (@lem1577730 y x)). Qed.
Lemma lem1577743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577744 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1577743) (@lem1575422 x y)). Qed.
Lemma lem1577745 (x : real) (y : real) : (term193 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1577744 x y) (@lem1575389 y)). Qed.
Lemma lem1577746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577747 (x : real) (y : real) : (term244 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1577746) (@lem1576654 x y)). Qed.
Lemma lem1577748 (x : real) (y : real) : (term669 x y) = (term676 x y).
Proof. exact (MK_COMB (@lem1577747 x y) (@lem1577745 x y)). Qed.
Lemma lem1577749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577750 (x : real) (y : real) : (term199 y x) = (term244 x y).
Proof. exact (MK_COMB (@lem1577749) (@lem1575346 x y)). Qed.
Lemma lem1577751 (x : real) (y : real) : (term671 x y) = (term677 x y).
Proof. exact (MK_COMB (@lem1577750 x y) (@lem1577748 x y)). Qed.
Lemma lem1577752 (x : real) : (term678 x) = (term679 x).
Proof. exact (@lem1483527 (term214 x) term48). Qed.
Lemma lem1577753 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577765 (x : real) : (term214 x) = (term215 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1577767 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577768 : term217 = term48.
Proof. exact (@lem1577767 term36). Qed.
Lemma lem1577769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577770 : term218 = term219.
Proof. exact (MK_COMB (@lem1577769) (@lem1577768)). Qed.
Lemma lem1577771 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1577772 (x : real) : (term215 x) = (term220 x).
Proof. exact (MK_COMB (@lem1577770) (@lem1577771 x)). Qed.
Lemma lem1577773 (x : real) : (term214 x) = (term220 x).
Proof. exact (TRANS (@lem1577765 x) (@lem1577772 x)). Qed.
Lemma lem1577774 (x : real) : (term220 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1577776 (x : real) : (term214 x) = term48.
Proof. exact (TRANS (@lem1577773 x) (@lem1577774 x)). Qed.
Lemma lem1577777 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1577778 (x : real) : (term221 x) = term222.
Proof. exact (MK_COMB (@lem1577777) (@lem1577776 x)). Qed.
Lemma lem1577779 (x : real) : (term223 x) = term224.
Proof. exact (MK_COMB (@lem1577778 x) (@lem1577753)). Qed.
Lemma lem1577780 : term224 = term225.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1577782 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577783 : term227 = term48.
Proof. exact (@lem1577782 term36). Qed.
Lemma lem1577784 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem1577785 : term225 = term229.
Proof. exact (MK_COMB (@lem1577784) (@lem1577783)). Qed.
Lemma lem1577786 : term229 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1577787 : term225 = term48.
Proof. exact (TRANS (@lem1577785) (@lem1577786)). Qed.
Lemma lem1577788 : term224 = term48.
Proof. exact (TRANS (@lem1577780) (@lem1577787)). Qed.
Lemma lem1577789 (x : real) : (term223 x) = term48.
Proof. exact (TRANS (@lem1577779 x) (@lem1577788)). Qed.
Lemma lem1577790 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1577791 (x : real) : (term680 x) = term595.
Proof. exact (MK_COMB (@lem1577790) (@lem1577789 x)). Qed.
Lemma lem1577792 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577793 (x : real) : (term679 x) = term596.
Proof. exact (MK_COMB (@lem1577791 x) (@lem1577792)). Qed.
Lemma lem1577794 (x : real) : (term678 x) = term596.
Proof. exact (TRANS (@lem1577752 x) (@lem1577793 x)). Qed.
Lemma lem1577795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577796 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1577795) (@lem1575523 x)). Qed.
Lemma lem1577797 (x : real) (y : real) : (term198 y x) = (term265 x y).
Proof. exact (MK_COMB (@lem1577796 x) (@lem1575480 x y)). Qed.
Lemma lem1577798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577799 (x : real) : (term681 x) = term597.
Proof. exact (MK_COMB (@lem1577798) (@lem1577794 x)). Qed.
Lemma lem1577800 (x : real) (y : real) : (term665 y x) = (term682 x y).
Proof. exact (MK_COMB (@lem1577799 x) (@lem1577797 x y)). Qed.
Lemma lem1577801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577802 (x : real) (y : real) : (term194 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1577801) (@lem1575447 x y)). Qed.
Lemma lem1577803 (x : real) (y : real) : (term667 y x) = (term683 x y).
Proof. exact (MK_COMB (@lem1577802 x y) (@lem1577800 x y)). Qed.
Lemma lem1577804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577805 (x : real) (y : real) : (term673 x y) = (term684 x y).
Proof. exact (MK_COMB (@lem1577804) (@lem1577751 x y)). Qed.
Lemma lem1577806 (x : real) (y : real) : (term674 y x) = (term685 x y).
Proof. exact (MK_COMB (@lem1577805 x y) (@lem1577803 x y)). Qed.
Lemma lem1577818 (x : real) (y : real) : (term647 x y) = (term685 x y).
Proof. exact (TRANS (@lem1577742 y x) (@lem1577806 x y)). Qed.
Lemma lem1577819 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577820 (x : real) (y : real) : (term657 x y) = (term686 x y).
Proof. exact (MK_COMB (@lem1577819) (@lem1577818 x y)). Qed.
Lemma lem1577821 (x : real) (y : real) : (term658 x y) = (term687 x y).
Proof. exact (MK_COMB (@lem1577820 x y) (@lem1577725 x y)). Qed.
Lemma lem1577822 (x : real) (y : real) : (term625 x y) = (term687 x y).
Proof. exact (TRANS (@lem1577668 x y) (@lem1577821 x y)). Qed.
Lemma lem1577823 (x : real) (y : real) : (term158 x y) = (term687 x y).
Proof. exact (TRANS (@lem1577598 x y) (@lem1577822 x y)). Qed.
Lemma lem1577825 (x : real) (a : real) (y : real) (r : real) : (term171 a x y r) = (term172 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1577826 (x : real) (y : real) : (term154 x y) = (term688 x y).
Proof. exact (@lem1577825 x (real_max x y) (real_max x y) term48). Qed.
Lemma lem1577838 (x : real) (y : real) : (term689 x y) = (term690 x y).
Proof. exact (@lem1483442 term28 (real_max x y)). Qed.
Lemma lem1577840 (m : nat) : (term216 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1577841 : term217 = term48.
Proof. exact (@lem1577840 term36). Qed.
Lemma lem1577842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1577843 : term218 = term219.
Proof. exact (MK_COMB (@lem1577842) (@lem1577841)). Qed.
Lemma lem1577844 (x : real) (y : real) : (real_max x y) = (real_max x y).
Proof. exact (eq_refl (real_max x y)). Qed.
Lemma lem1577845 (x : real) (y : real) : (term690 x y) = (term691 x y).
Proof. exact (MK_COMB (@lem1577843) (@lem1577844 x y)). Qed.
Lemma lem1577846 (x : real) (y : real) : (term689 x y) = (term691 x y).
Proof. exact (TRANS (@lem1577838 x y) (@lem1577845 x y)). Qed.
Lemma lem1577847 (x : real) (y : real) : (term691 x y) = term48.
Proof. exact (@lem1483446 (real_max x y)). Qed.
Lemma lem1577849 (x : real) (y : real) : (term689 x y) = term48.
Proof. exact (TRANS (@lem1577846 x y) (@lem1577847 x y)). Qed.
Lemma lem1577850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577851 (x : real) (y : real) : (term692 x y) = term231.
Proof. exact (MK_COMB (@lem1577850) (@lem1577849 x y)). Qed.
Lemma lem1577852 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577853 (x : real) (y : real) : (term693 x y) = term232.
Proof. exact (MK_COMB (@lem1577851 x y) (@lem1577852)). Qed.
Lemma lem1577866 (x : real) (y : real) : (term174 y x) = (term175 x y).
Proof. exact (@lem1483488 (term114 x) (real_max x y)). Qed.
Lemma lem1577867 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577868 (x : real) (y : real) : (term176 y x) = (term177 x y).
Proof. exact (MK_COMB (@lem1577867) (@lem1577866 x y)). Qed.
Lemma lem1577869 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577870 (x : real) (y : real) : (term178 y x) = (term179 x y).
Proof. exact (MK_COMB (@lem1577868 x y) (@lem1577869)). Qed.
Lemma lem1577871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577872 (x : real) (y : real) : (term694 y x) = (term361 x y).
Proof. exact (MK_COMB (@lem1577871) (@lem1577870 x y)). Qed.
Lemma lem1577873 (x : real) (y : real) : (term688 x y) = (term695 x y).
Proof. exact (MK_COMB (@lem1577872 x y) (@lem1577853 x y)). Qed.
Lemma lem1577874 (x : real) (y : real) : (term154 x y) = (term695 x y).
Proof. exact (TRANS (@lem1577826 x y) (@lem1577873 x y)). Qed.
Lemma lem1577875 (x : real) (y : real) : (term696 x y) = (term695 x y).
Proof. exact (eq_refl (term696 x y)). Qed.
Lemma lem1577876 (x : real) (y : real) : (term695 x y) = (term696 x y).
Proof. exact (SYM (@lem1577875 x y)). Qed.
Lemma lem1577877 (y : real) (x : real) : (term696 x y) = (term697 y x).
Proof. exact (@lem1483205 y (term698 x) x). Qed.
Lemma lem1577878 (y : real) (x : real) : (term695 x y) = (term697 y x).
Proof. exact (TRANS (@lem1577876 x y) (@lem1577877 y x)). Qed.
Lemma lem1577879 (x : real) : (term699 x) = (term700 x).
Proof. exact (eq_refl (term699 x)). Qed.
Lemma lem1577880 (x : real) (y : real) : (term194 x y) = (term194 x y).
Proof. exact (eq_refl (term194 x y)). Qed.
Lemma lem1577881 (y : real) (x : real) : (term701 y x) = (term702 y x).
Proof. exact (MK_COMB (@lem1577880 x y) (@lem1577879 x)). Qed.
Lemma lem1577882 (x : real) (y : real) : (term703 x y) = (term268 x y).
Proof. exact (eq_refl (term703 x y)). Qed.
Lemma lem1577883 (y : real) (x : real) : (term199 y x) = (term199 y x).
Proof. exact (eq_refl (term199 y x)). Qed.
Lemma lem1577884 (x : real) (y : real) : (term704 x y) = (term705 x y).
Proof. exact (MK_COMB (@lem1577883 y x) (@lem1577882 x y)). Qed.
Lemma lem1577885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577886 (x : real) (y : real) : (term706 x y) = (term707 x y).
Proof. exact (MK_COMB (@lem1577885) (@lem1577884 x y)). Qed.
Lemma lem1577887 (y : real) (x : real) : (term697 y x) = (term708 y x).
Proof. exact (MK_COMB (@lem1577886 x y) (@lem1577881 y x)). Qed.
Lemma lem1577888 (x : real) (y : real) : (term709 x y) = (term709 x y).
Proof. exact (eq_refl (term709 x y)). Qed.
Lemma lem1577889 (y : real) (x : real) : ((term695 x y) = (term697 y x)) = ((term695 x y) = (term708 y x)).
Proof. exact (MK_COMB (@lem1577888 x y) (@lem1577887 y x)). Qed.
Lemma lem1577890 (y : real) (x : real) : (term695 x y) = (term708 y x).
Proof. exact (EQ_MP (@lem1577889 y x) (@lem1577878 y x)). Qed.
Lemma lem1577891 : term232 = term710.
Proof. exact (@lem1483525 term48 term48). Qed.
Lemma lem1577897 : term224 = term225.
Proof. exact (@lem1483519 term48 term48). Qed.
Lemma lem1577899 (x : nat) : (term226 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1577900 : term227 = term48.
Proof. exact (@lem1577899 term36). Qed.
Lemma lem1577901 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem1577902 : term225 = term229.
Proof. exact (MK_COMB (@lem1577901) (@lem1577900)). Qed.
Lemma lem1577903 : term229 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1577904 : term225 = term48.
Proof. exact (TRANS (@lem1577902) (@lem1577903)). Qed.
Lemma lem1577906 : term224 = term48.
Proof. exact (TRANS (@lem1577897) (@lem1577904)). Qed.
Lemma lem1577907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1577908 : term711 = term231.
Proof. exact (MK_COMB (@lem1577907) (@lem1577906)). Qed.
Lemma lem1577909 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1577910 : term710 = term232.
Proof. exact (MK_COMB (@lem1577908) (@lem1577909)). Qed.
Lemma lem1577911 : term232 = term232.
Proof. exact (TRANS (@lem1577891) (@lem1577910)). Qed.
Lemma lem1577912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577913 (x : real) (y : real) : (term256 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1577912) (@lem1575422 x y)). Qed.
Lemma lem1577914 (x : real) (y : real) : (term268 x y) = (term268 x y).
Proof. exact (MK_COMB (@lem1577913 x y) (@lem1577911)). Qed.
Lemma lem1577915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577916 (x : real) (y : real) : (term199 y x) = (term244 x y).
Proof. exact (MK_COMB (@lem1577915) (@lem1575346 x y)). Qed.
Lemma lem1577917 (x : real) (y : real) : (term705 x y) = (term676 x y).
Proof. exact (MK_COMB (@lem1577916 x y) (@lem1577914 x y)). Qed.
Lemma lem1577918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577919 (x : real) : (term241 x) = term242.
Proof. exact (MK_COMB (@lem1577918) (@lem1575523 x)). Qed.
Lemma lem1577920 (x : real) : (term700 x) = term601.
Proof. exact (MK_COMB (@lem1577919 x) (@lem1577911)). Qed.
Lemma lem1577921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1577922 (x : real) (y : real) : (term194 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem1577921) (@lem1575447 x y)). Qed.
Lemma lem1577923 (x : real) (y : real) : (term702 y x) = (term712 x y).
Proof. exact (MK_COMB (@lem1577922 x y) (@lem1577920 x)). Qed.
Lemma lem1577924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577925 (x : real) (y : real) : (term707 x y) = (term713 x y).
Proof. exact (MK_COMB (@lem1577924) (@lem1577917 x y)). Qed.
Lemma lem1577926 (x : real) (y : real) : (term708 y x) = (term714 x y).
Proof. exact (MK_COMB (@lem1577925 x y) (@lem1577923 x y)). Qed.
Lemma lem1577937 (x : real) (y : real) : (term695 x y) = (term714 x y).
Proof. exact (TRANS (@lem1577890 y x) (@lem1577926 x y)). Qed.
Lemma lem1577938 (x : real) (y : real) : (term154 x y) = (term714 x y).
Proof. exact (TRANS (@lem1577874 x y) (@lem1577937 x y)). Qed.
Lemma lem1577939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577940 (x : real) (y : real) : (term160 x y) = (term715 x y).
Proof. exact (MK_COMB (@lem1577939) (@lem1577823 x y)). Qed.
Lemma lem1577941 (x : real) (y : real) : (term161 x y) = (term716 x y).
Proof. exact (MK_COMB (@lem1577940 x y) (@lem1577938 x y)). Qed.
Lemma lem1577942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577943 (x : real) : (term163 x) = term717.
Proof. exact (MK_COMB (@lem1577942) (@lem1577557 x)). Qed.
Lemma lem1577944 (x : real) (y : real) : (term164 x y) = (term718 x y).
Proof. exact (MK_COMB (@lem1577943 x) (@lem1577941 x y)). Qed.
Lemma lem1577945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577946 (x : real) (y : real) (z : real) : (term165 y x z) = (term719 x y z).
Proof. exact (MK_COMB (@lem1577945) (@lem1577395 x y z)). Qed.
Lemma lem1577947 (z : real) (x : real) (y : real) : (term166 z x y) = (term720 z x y).
Proof. exact (MK_COMB (@lem1577946 x y z) (@lem1577944 x y)). Qed.
Lemma lem1577948 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577949 (y : real) (x : real) (z : real) : (term167 x y z) = (term721 y x z).
Proof. exact (MK_COMB (@lem1577948) (@lem1576689 y x z)). Qed.
Lemma lem1577950 (z : real) (x : real) (y : real) : (term168 z x y) = (term722 z x y).
Proof. exact (MK_COMB (@lem1577949 y x z) (@lem1577947 z x y)). Qed.
Lemma lem1577951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1577952 (x : real) (y : real) : (term169 y x) = (term723 x y).
Proof. exact (MK_COMB (@lem1577951) (@lem1575669 x y)). Qed.
Lemma lem1577953 (z : real) (x : real) (y : real) : (term170 z x y) = (term724 z x y).
Proof. exact (MK_COMB (@lem1577952 x y) (@lem1577950 z x y)). Qed.
Lemma lem1577954 (z : real) (x : real) (y : real) (h1 : term724 z x y) : term724 z x y.
Proof. exact (h1). Qed.
Lemma lem1577955 (x : real) (y : real) (h1 : term273 x y) : term273 x y.
Proof. exact (h1). Qed.
Lemma lem1577956 (x : real) (y : real) (h1 : term261 x y) : term261 x y.
Proof. exact (h1). Qed.
Lemma lem1577957 (x : real) (y : real) (h1 : term245 x y) : term245 x y.
Proof. exact (h1). Qed.
Lemma lem1577958 (x : real) (y : real) (h1 : term245 x y) : term243 x y.
Proof. exact (proj2 (@lem1577957 x y h1)). Qed.
Lemma lem1577961 (x : real) (y : real) (h1 : term245 x y) : term232.
Proof. exact (proj1 (@lem1577958 x y h1)). Qed.
Lemma lem1577963 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1577964 : term232 = term726.
Proof. exact (@lem1577963 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1577965 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1577966 : term232 = False.
Proof. exact (TRANS (@lem1577964) (@lem1577965)). Qed.
Lemma lem1577967 (x : real) (y : real) (h1 : term245 x y) : False.
Proof. exact (EQ_MP (@lem1577966) (@lem1577961 x y h1)). Qed.
Lemma lem1577968 (x : real) (y : real) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1577969 (x : real) (y : real) (h1 : term259 x y) : term258 x y.
Proof. exact (proj2 (@lem1577968 x y h1)). Qed.
Lemma lem1577971 (x : real) (y : real) (h1 : term259 x y) : term232.
Proof. exact (proj2 (@lem1577969 x y h1)). Qed.
Lemma lem1577974 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1577975 : term232 = term726.
Proof. exact (@lem1577974 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1577976 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1577977 : term232 = False.
Proof. exact (TRANS (@lem1577975) (@lem1577976)). Qed.
Lemma lem1577978 (x : real) (y : real) (h1 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1577977) (@lem1577971 x y h1)). Qed.
Lemma lem1577979 (x : real) (y : real) (h1 : term261 x y) : False.
Proof. exact (or_elim (@lem1577956 x y h1) (fun h0 : term245 x y => @lem1577967 x y h0) (fun h0 : term259 x y => @lem1577978 x y h0)). Qed.
Lemma lem1577980 (x : real) (y : real) (h1 : term271 x y) : term271 x y.
Proof. exact (h1). Qed.
Lemma lem1577981 (x : real) (y : real) (h1 : term267 x y) : term267 x y.
Proof. exact (h1). Qed.
Lemma lem1577982 (x : real) (y : real) (h1 : term267 x y) : term265 x y.
Proof. exact (proj2 (@lem1577981 x y h1)). Qed.
Lemma lem1577985 (x : real) (y : real) (h1 : term267 x y) : term232.
Proof. exact (proj1 (@lem1577982 x y h1)). Qed.
Lemma lem1577987 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1577988 : term232 = term726.
Proof. exact (@lem1577987 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1577989 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1577990 : term232 = False.
Proof. exact (TRANS (@lem1577988) (@lem1577989)). Qed.
Lemma lem1577991 (x : real) (y : real) (h1 : term267 x y) : False.
Proof. exact (EQ_MP (@lem1577990) (@lem1577985 x y h1)). Qed.
Lemma lem1577992 (x : real) (y : real) (h1 : term269 x y) : term269 x y.
Proof. exact (h1). Qed.
Lemma lem1577993 (x : real) (y : real) (h1 : term269 x y) : term268 x y.
Proof. exact (proj2 (@lem1577992 x y h1)). Qed.
Lemma lem1577995 (x : real) (y : real) (h1 : term269 x y) : term232.
Proof. exact (proj2 (@lem1577993 x y h1)). Qed.
Lemma lem1577998 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1577999 : term232 = term726.
Proof. exact (@lem1577998 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578000 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578001 : term232 = False.
Proof. exact (TRANS (@lem1577999) (@lem1578000)). Qed.
Lemma lem1578002 (x : real) (y : real) (h1 : term269 x y) : False.
Proof. exact (EQ_MP (@lem1578001) (@lem1577995 x y h1)). Qed.
Lemma lem1578003 (x : real) (y : real) (h1 : term271 x y) : False.
Proof. exact (or_elim (@lem1577980 x y h1) (fun h0 : term267 x y => @lem1577991 x y h0) (fun h0 : term269 x y => @lem1578002 x y h0)). Qed.
Lemma lem1578004 (x : real) (y : real) (h1 : term273 x y) : False.
Proof. exact (or_elim (@lem1577955 x y h1) (fun h0 : term261 x y => @lem1577979 x y h0) (fun h0 : term271 x y => @lem1578003 x y h0)). Qed.
Lemma lem1578005 (z : real) (x : real) (y : real) (h1 : term722 z x y) : term722 z x y.
Proof. exact (h1). Qed.
Lemma lem1578006 (y : real) (x : real) (z : real) (h1 : term508 y x z) : term508 y x z.
Proof. exact (h1). Qed.
Lemma lem1578007 (y : real) (x : real) (z : real) (h1 : term400 y x z) : term400 y x z.
Proof. exact (h1). Qed.
Lemma lem1578008 (x : real) (y : real) (z : real) (h1 : term398 x y z) : term398 x y z.
Proof. exact (h1). Qed.
Lemma lem1578009 (x : real) (y : real) (z : real) (h1 : term398 x y z) : term331 x y z.
Proof. exact (proj2 (@lem1578008 x y z h1)). Qed.
Lemma lem1578013 (x : real) (y : real) (z : real) (h1 : term398 x y z) : term268 y z.
Proof. exact (proj2 (@lem1578009 x y z h1)). Qed.
Lemma lem1578015 (x : real) (y : real) (z : real) (h1 : term398 x y z) : term232.
Proof. exact (proj2 (@lem1578013 x y z h1)). Qed.
Lemma lem1578018 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578019 : term232 = term726.
Proof. exact (@lem1578018 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578020 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578021 : term232 = False.
Proof. exact (TRANS (@lem1578019) (@lem1578020)). Qed.
Lemma lem1578022 (x : real) (y : real) (z : real) (h1 : term398 x y z) : False.
Proof. exact (EQ_MP (@lem1578021) (@lem1578015 x y z h1)). Qed.
Lemma lem1578023 (y : real) (x : real) (z : real) (h1 : term392 y x z) : term392 y x z.
Proof. exact (h1). Qed.
Lemma lem1578024 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term384 x y z.
Proof. exact (h1). Qed.
Lemma lem1578025 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term383 x y z.
Proof. exact (proj2 (@lem1578024 x y z h1)). Qed.
Lemma lem1578027 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term382 x y z.
Proof. exact (proj2 (@lem1578025 x y z h1)). Qed.
Lemma lem1578029 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term265 y z.
Proof. exact (proj2 (@lem1578027 x y z h1)). Qed.
Lemma lem1578032 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term232.
Proof. exact (proj1 (@lem1578029 x y z h1)). Qed.
Lemma lem1578034 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578035 : term232 = term726.
Proof. exact (@lem1578034 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578036 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578037 : term232 = False.
Proof. exact (TRANS (@lem1578035) (@lem1578036)). Qed.
Lemma lem1578038 (x : real) (y : real) (z : real) (h1 : term384 x y z) : False.
Proof. exact (EQ_MP (@lem1578037) (@lem1578032 x y z h1)). Qed.
Lemma lem1578039 (y : real) (x : real) (z : real) (h1 : term390 y x z) : term390 y x z.
Proof. exact (h1). Qed.
Lemma lem1578040 (y : real) (x : real) (z : real) (h1 : term390 y x z) : term389 y x z.
Proof. exact (proj2 (@lem1578039 y x z h1)). Qed.
Lemma lem1578042 (y : real) (x : real) (z : real) (h1 : term390 y x z) : term388 y x z.
Proof. exact (proj2 (@lem1578040 y x z h1)). Qed.
Lemma lem1578045 (y : real) (x : real) (z : real) (h1 : term390 y x z) : term232.
Proof. exact (proj1 (@lem1578042 y x z h1)). Qed.
Lemma lem1578049 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578050 : term232 = term726.
Proof. exact (@lem1578049 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578051 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578052 : term232 = False.
Proof. exact (TRANS (@lem1578050) (@lem1578051)). Qed.
Lemma lem1578053 (y : real) (x : real) (z : real) (h1 : term390 y x z) : False.
Proof. exact (EQ_MP (@lem1578052) (@lem1578045 y x z h1)). Qed.
Lemma lem1578054 (y : real) (x : real) (z : real) (h1 : term392 y x z) : False.
Proof. exact (or_elim (@lem1578023 y x z h1) (fun h0 : term384 x y z => @lem1578038 x y z h0) (fun h0 : term390 y x z => @lem1578053 y x z h0)). Qed.
Lemma lem1578055 (y : real) (x : real) (z : real) (h1 : term400 y x z) : False.
Proof. exact (or_elim (@lem1578007 y x z h1) (fun h0 : term398 x y z => @lem1578022 x y z h0) (fun h0 : term392 y x z => @lem1578054 y x z h0)). Qed.
Lemma lem1578056 (y : real) (x : real) (z : real) (h1 : term506 y x z) : term506 y x z.
Proof. exact (h1). Qed.
Lemma lem1578057 (x : real) (y : real) (z : real) (h1 : term504 x y z) : term504 x y z.
Proof. exact (h1). Qed.
Lemma lem1578058 (x : real) (y : real) (z : real) (h1 : term496 x y z) : term496 x y z.
Proof. exact (h1). Qed.
Lemma lem1578059 (x : real) (y : real) (z : real) (h1 : term496 x y z) : term495 x y z.
Proof. exact (proj2 (@lem1578058 x y z h1)). Qed.
Lemma lem1578061 (x : real) (y : real) (z : real) (h1 : term496 x y z) : term494 x y z.
Proof. exact (proj2 (@lem1578059 x y z h1)). Qed.
Lemma lem1578063 (x : real) (y : real) (z : real) (h1 : term496 x y z) : term232.
Proof. exact (proj2 (@lem1578061 x y z h1)). Qed.
Lemma lem1578068 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578069 : term232 = term726.
Proof. exact (@lem1578068 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578070 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578071 : term232 = False.
Proof. exact (TRANS (@lem1578069) (@lem1578070)). Qed.
Lemma lem1578072 (x : real) (y : real) (z : real) (h1 : term496 x y z) : False.
Proof. exact (EQ_MP (@lem1578071) (@lem1578063 x y z h1)). Qed.
Lemma lem1578073 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term502 x y z.
Proof. exact (h1). Qed.
Lemma lem1578074 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term501 x y z.
Proof. exact (proj2 (@lem1578073 x y z h1)). Qed.
Lemma lem1578076 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term500 x y z.
Proof. exact (proj2 (@lem1578074 x y z h1)). Qed.
Lemma lem1578079 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term268 x y.
Proof. exact (proj1 (@lem1578076 x y z h1)). Qed.
Lemma lem1578080 (x : real) (y : real) (z : real) (h1 : term502 x y z) : term232.
Proof. exact (proj2 (@lem1578079 x y z h1)). Qed.
Lemma lem1578083 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578084 : term232 = term726.
Proof. exact (@lem1578083 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578085 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578086 : term232 = False.
Proof. exact (TRANS (@lem1578084) (@lem1578085)). Qed.
Lemma lem1578087 (x : real) (y : real) (z : real) (h1 : term502 x y z) : False.
Proof. exact (EQ_MP (@lem1578086) (@lem1578080 x y z h1)). Qed.
Lemma lem1578088 (x : real) (y : real) (z : real) (h1 : term504 x y z) : False.
Proof. exact (or_elim (@lem1578057 x y z h1) (fun h0 : term496 x y z => @lem1578072 x y z h0) (fun h0 : term502 x y z => @lem1578087 x y z h0)). Qed.
Lemma lem1578089 (y : real) (x : real) (z : real) (h1 : term474 y x z) : term474 y x z.
Proof. exact (h1). Qed.
Lemma lem1578090 (y : real) (x : real) (z : real) (h1 : term474 y x z) : term468 y x z.
Proof. exact (proj2 (@lem1578089 y x z h1)). Qed.
Lemma lem1578095 (y : real) (x : real) (z : real) (h1 : term474 y x z) : term265 x y.
Proof. exact (proj1 (@lem1578090 y x z h1)). Qed.
Lemma lem1578097 (y : real) (x : real) (z : real) (h1 : term474 y x z) : term232.
Proof. exact (proj1 (@lem1578095 y x z h1)). Qed.
Lemma lem1578099 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578100 : term232 = term726.
Proof. exact (@lem1578099 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578101 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578102 : term232 = False.
Proof. exact (TRANS (@lem1578100) (@lem1578101)). Qed.
Lemma lem1578103 (y : real) (x : real) (z : real) (h1 : term474 y x z) : False.
Proof. exact (EQ_MP (@lem1578102) (@lem1578097 y x z h1)). Qed.
Lemma lem1578104 (y : real) (x : real) (z : real) (h1 : term506 y x z) : False.
Proof. exact (or_elim (@lem1578056 y x z h1) (fun h0 : term504 x y z => @lem1578088 x y z h0) (fun h0 : term474 y x z => @lem1578103 y x z h0)). Qed.
Lemma lem1578105 (y : real) (x : real) (z : real) (h1 : term508 y x z) : False.
Proof. exact (or_elim (@lem1578006 y x z h1) (fun h0 : term400 y x z => @lem1578055 y x z h0) (fun h0 : term506 y x z => @lem1578104 y x z h0)). Qed.
Lemma lem1578106 (z : real) (x : real) (y : real) (h1 : term720 z x y) : term720 z x y.
Proof. exact (h1). Qed.
Lemma lem1578107 (x : real) (y : real) (z : real) (h1 : term577 x y z) : term577 x y z.
Proof. exact (h1). Qed.
Lemma lem1578108 (y : real) (x : real) (z : real) (h1 : term566 y x z) : term566 y x z.
Proof. exact (h1). Qed.
Lemma lem1578109 (x : real) (y : real) (z : real) (h1 : term564 x y z) : term564 x y z.
Proof. exact (h1). Qed.
Lemma lem1578110 (y : real) (x : real) (z : real) (h1 : term558 y x z) : term558 y x z.
Proof. exact (h1). Qed.
Lemma lem1578111 (y : real) (x : real) (z : real) (h1 : term558 y x z) : term557 y x z.
Proof. exact (proj2 (@lem1578110 y x z h1)). Qed.
Lemma lem1578113 (y : real) (x : real) (z : real) (h1 : term558 y x z) : term331 y x z.
Proof. exact (proj2 (@lem1578111 y x z h1)). Qed.
Lemma lem1578115 (y : real) (x : real) (z : real) (h1 : term558 y x z) : term268 x z.
Proof. exact (proj2 (@lem1578113 y x z h1)). Qed.
Lemma lem1578117 (y : real) (x : real) (z : real) (h1 : term558 y x z) : term232.
Proof. exact (proj2 (@lem1578115 y x z h1)). Qed.
Lemma lem1578120 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578121 : term232 = term726.
Proof. exact (@lem1578120 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578122 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578123 : term232 = False.
Proof. exact (TRANS (@lem1578121) (@lem1578122)). Qed.
Lemma lem1578124 (y : real) (x : real) (z : real) (h1 : term558 y x z) : False.
Proof. exact (EQ_MP (@lem1578123) (@lem1578117 y x z h1)). Qed.
Lemma lem1578125 (x : real) (y : real) (z : real) (h1 : term562 x y z) : term562 x y z.
Proof. exact (h1). Qed.
Lemma lem1578126 (x : real) (y : real) (z : real) (h1 : term562 x y z) : term561 x y z.
Proof. exact (proj2 (@lem1578125 x y z h1)). Qed.
Lemma lem1578128 (x : real) (y : real) (z : real) (h1 : term562 x y z) : term560 x y z.
Proof. exact (proj2 (@lem1578126 x y z h1)). Qed.
Lemma lem1578131 (x : real) (y : real) (z : real) (h1 : term562 x y z) : term232.
Proof. exact (proj1 (@lem1578128 x y z h1)). Qed.
Lemma lem1578135 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578136 : term232 = term726.
Proof. exact (@lem1578135 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578137 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578138 : term232 = False.
Proof. exact (TRANS (@lem1578136) (@lem1578137)). Qed.
Lemma lem1578139 (x : real) (y : real) (z : real) (h1 : term562 x y z) : False.
Proof. exact (EQ_MP (@lem1578138) (@lem1578131 x y z h1)). Qed.
Lemma lem1578140 (x : real) (y : real) (z : real) (h1 : term564 x y z) : False.
Proof. exact (or_elim (@lem1578109 x y z h1) (fun h0 : term558 y x z => @lem1578124 y x z h0) (fun h0 : term562 x y z => @lem1578139 x y z h0)). Qed.
Lemma lem1578141 (y : real) (x : real) (z : real) (h1 : term541 y x z) : term541 y x z.
Proof. exact (h1). Qed.
Lemma lem1578142 (y : real) (x : real) (z : real) (h1 : term541 y x z) : term537 y x z.
Proof. exact (proj2 (@lem1578141 y x z h1)). Qed.
Lemma lem1578146 (y : real) (x : real) (z : real) (h1 : term541 y x z) : term265 x z.
Proof. exact (proj2 (@lem1578142 y x z h1)). Qed.
Lemma lem1578149 (y : real) (x : real) (z : real) (h1 : term541 y x z) : term232.
Proof. exact (proj1 (@lem1578146 y x z h1)). Qed.
Lemma lem1578151 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578152 : term232 = term726.
Proof. exact (@lem1578151 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578153 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578154 : term232 = False.
Proof. exact (TRANS (@lem1578152) (@lem1578153)). Qed.
Lemma lem1578155 (y : real) (x : real) (z : real) (h1 : term541 y x z) : False.
Proof. exact (EQ_MP (@lem1578154) (@lem1578149 y x z h1)). Qed.
Lemma lem1578156 (y : real) (x : real) (z : real) (h1 : term566 y x z) : False.
Proof. exact (or_elim (@lem1578108 y x z h1) (fun h0 : term564 x y z => @lem1578140 x y z h0) (fun h0 : term541 y x z => @lem1578155 y x z h0)). Qed.
Lemma lem1578157 (x : real) (y : real) (z : real) (h1 : term575 x y z) : term575 x y z.
Proof. exact (h1). Qed.
Lemma lem1578158 (y : real) (x : real) (z : real) (h1 : term573 y x z) : term573 y x z.
Proof. exact (h1). Qed.
Lemma lem1578159 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term558 x y z.
Proof. exact (h1). Qed.
Lemma lem1578160 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term557 x y z.
Proof. exact (proj2 (@lem1578159 x y z h1)). Qed.
Lemma lem1578162 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term331 x y z.
Proof. exact (proj2 (@lem1578160 x y z h1)). Qed.
Lemma lem1578164 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term268 y z.
Proof. exact (proj2 (@lem1578162 x y z h1)). Qed.
Lemma lem1578166 (x : real) (y : real) (z : real) (h1 : term558 x y z) : term232.
Proof. exact (proj2 (@lem1578164 x y z h1)). Qed.
Lemma lem1578169 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578170 : term232 = term726.
Proof. exact (@lem1578169 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578171 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578172 : term232 = False.
Proof. exact (TRANS (@lem1578170) (@lem1578171)). Qed.
Lemma lem1578173 (x : real) (y : real) (z : real) (h1 : term558 x y z) : False.
Proof. exact (EQ_MP (@lem1578172) (@lem1578166 x y z h1)). Qed.
Lemma lem1578174 (y : real) (x : real) (z : real) (h1 : term572 y x z) : term572 y x z.
Proof. exact (h1). Qed.
Lemma lem1578175 (y : real) (x : real) (z : real) (h1 : term572 y x z) : term571 y x z.
Proof. exact (proj2 (@lem1578174 y x z h1)). Qed.
Lemma lem1578177 (y : real) (x : real) (z : real) (h1 : term572 y x z) : term388 y x z.
Proof. exact (proj2 (@lem1578175 y x z h1)). Qed.
Lemma lem1578180 (y : real) (x : real) (z : real) (h1 : term572 y x z) : term232.
Proof. exact (proj1 (@lem1578177 y x z h1)). Qed.
Lemma lem1578184 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578185 : term232 = term726.
Proof. exact (@lem1578184 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578186 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578187 : term232 = False.
Proof. exact (TRANS (@lem1578185) (@lem1578186)). Qed.
Lemma lem1578188 (y : real) (x : real) (z : real) (h1 : term572 y x z) : False.
Proof. exact (EQ_MP (@lem1578187) (@lem1578180 y x z h1)). Qed.
Lemma lem1578189 (y : real) (x : real) (z : real) (h1 : term573 y x z) : False.
Proof. exact (or_elim (@lem1578158 y x z h1) (fun h0 : term558 x y z => @lem1578173 x y z h0) (fun h0 : term572 y x z => @lem1578188 y x z h0)). Qed.
Lemma lem1578190 (x : real) (y : real) (z : real) (h1 : term570 x y z) : term570 x y z.
Proof. exact (h1). Qed.
Lemma lem1578191 (x : real) (y : real) (z : real) (h1 : term570 x y z) : term382 x y z.
Proof. exact (proj2 (@lem1578190 x y z h1)). Qed.
Lemma lem1578195 (x : real) (y : real) (z : real) (h1 : term570 x y z) : term265 y z.
Proof. exact (proj2 (@lem1578191 x y z h1)). Qed.
Lemma lem1578198 (x : real) (y : real) (z : real) (h1 : term570 x y z) : term232.
Proof. exact (proj1 (@lem1578195 x y z h1)). Qed.
Lemma lem1578200 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578201 : term232 = term726.
Proof. exact (@lem1578200 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578202 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578203 : term232 = False.
Proof. exact (TRANS (@lem1578201) (@lem1578202)). Qed.
Lemma lem1578204 (x : real) (y : real) (z : real) (h1 : term570 x y z) : False.
Proof. exact (EQ_MP (@lem1578203) (@lem1578198 x y z h1)). Qed.
Lemma lem1578205 (x : real) (y : real) (z : real) (h1 : term575 x y z) : False.
Proof. exact (or_elim (@lem1578157 x y z h1) (fun h0 : term573 y x z => @lem1578189 y x z h0) (fun h0 : term570 x y z => @lem1578204 x y z h0)). Qed.
Lemma lem1578206 (x : real) (y : real) (z : real) (h1 : term577 x y z) : False.
Proof. exact (or_elim (@lem1578107 x y z h1) (fun h0 : term566 y x z => @lem1578156 y x z h0) (fun h0 : term575 x y z => @lem1578205 x y z h0)). Qed.
Lemma lem1578207 (x : real) (y : real) (h1 : term718 x y) : term718 x y.
Proof. exact (h1). Qed.
Lemma lem1578208 (h1 : term609) : term609.
Proof. exact (h1). Qed.
Lemma lem1578209 (h1 : term603) : term603.
Proof. exact (h1). Qed.
Lemma lem1578210 (h1 : term598) : term598.
Proof. exact (h1). Qed.
Lemma lem1578211 (h1 : term598) : term232.
Proof. exact (proj2 (@lem1578210 h1)). Qed.
Lemma lem1578214 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578215 : term232 = term726.
Proof. exact (@lem1578214 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578216 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578217 : term232 = False.
Proof. exact (TRANS (@lem1578215) (@lem1578216)). Qed.
Lemma lem1578218 (h1 : term598) : False.
Proof. exact (EQ_MP (@lem1578217) (@lem1578211 h1)). Qed.
Lemma lem1578219 (h1 : term601) : term601.
Proof. exact (h1). Qed.
Lemma lem1578220 (h1 : term601) : term232.
Proof. exact (proj2 (@lem1578219 h1)). Qed.
Lemma lem1578223 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578224 : term232 = term726.
Proof. exact (@lem1578223 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578225 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578226 : term232 = False.
Proof. exact (TRANS (@lem1578224) (@lem1578225)). Qed.
Lemma lem1578227 (h1 : term601) : False.
Proof. exact (EQ_MP (@lem1578226) (@lem1578220 h1)). Qed.
Lemma lem1578228 (h1 : term603) : False.
Proof. exact (or_elim (@lem1578209 h1) (fun h0 : term598 => @lem1578218 h0) (fun h0 : term601 => @lem1578227 h0)). Qed.
Lemma lem1578229 (h1 : term601) : term601.
Proof. exact (h1). Qed.
Lemma lem1578230 (h1 : term601) : term232.
Proof. exact (proj2 (@lem1578229 h1)). Qed.
Lemma lem1578233 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578234 : term232 = term726.
Proof. exact (@lem1578233 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578235 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578236 : term232 = False.
Proof. exact (TRANS (@lem1578234) (@lem1578235)). Qed.
Lemma lem1578237 (h1 : term601) : False.
Proof. exact (EQ_MP (@lem1578236) (@lem1578230 h1)). Qed.
Lemma lem1578238 (h1 : term609) : False.
Proof. exact (or_elim (@lem1578208 h1) (fun h0 : term603 => @lem1578228 h0) (fun h0 : term601 => @lem1578237 h0)). Qed.
Lemma lem1578239 (x : real) (y : real) (h1 : term716 x y) : term716 x y.
Proof. exact (h1). Qed.
Lemma lem1578240 (x : real) (y : real) (h1 : term687 x y) : term687 x y.
Proof. exact (h1). Qed.
Lemma lem1578241 (x : real) (y : real) (h1 : term685 x y) : term685 x y.
Proof. exact (h1). Qed.
Lemma lem1578242 (x : real) (y : real) (h1 : term677 x y) : term677 x y.
Proof. exact (h1). Qed.
Lemma lem1578243 (x : real) (y : real) (h1 : term677 x y) : term676 x y.
Proof. exact (proj2 (@lem1578242 x y h1)). Qed.
Lemma lem1578245 (x : real) (y : real) (h1 : term677 x y) : term268 x y.
Proof. exact (proj2 (@lem1578243 x y h1)). Qed.
Lemma lem1578247 (x : real) (y : real) (h1 : term677 x y) : term232.
Proof. exact (proj2 (@lem1578245 x y h1)). Qed.
Lemma lem1578250 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578251 : term232 = term726.
Proof. exact (@lem1578250 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578252 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578253 : term232 = False.
Proof. exact (TRANS (@lem1578251) (@lem1578252)). Qed.
Lemma lem1578254 (x : real) (y : real) (h1 : term677 x y) : False.
Proof. exact (EQ_MP (@lem1578253) (@lem1578247 x y h1)). Qed.
Lemma lem1578255 (x : real) (y : real) (h1 : term683 x y) : term683 x y.
Proof. exact (h1). Qed.
Lemma lem1578256 (x : real) (y : real) (h1 : term683 x y) : term682 x y.
Proof. exact (proj2 (@lem1578255 x y h1)). Qed.
Lemma lem1578258 (x : real) (y : real) (h1 : term683 x y) : term265 x y.
Proof. exact (proj2 (@lem1578256 x y h1)). Qed.
Lemma lem1578261 (x : real) (y : real) (h1 : term683 x y) : term232.
Proof. exact (proj1 (@lem1578258 x y h1)). Qed.
Lemma lem1578263 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578264 : term232 = term726.
Proof. exact (@lem1578263 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578265 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578266 : term232 = False.
Proof. exact (TRANS (@lem1578264) (@lem1578265)). Qed.
Lemma lem1578267 (x : real) (y : real) (h1 : term683 x y) : False.
Proof. exact (EQ_MP (@lem1578266) (@lem1578261 x y h1)). Qed.
Lemma lem1578268 (x : real) (y : real) (h1 : term685 x y) : False.
Proof. exact (or_elim (@lem1578241 x y h1) (fun h0 : term677 x y => @lem1578254 x y h0) (fun h0 : term683 x y => @lem1578267 x y h0)). Qed.
Lemma lem1578269 (x : real) (y : real) (h1 : term660 x y) : term660 x y.
Proof. exact (h1). Qed.
Lemma lem1578270 (x : real) (y : real) (h1 : term660 x y) : term265 x y.
Proof. exact (proj2 (@lem1578269 x y h1)). Qed.
Lemma lem1578275 (x : real) (y : real) (h1 : term660 x y) : term232.
Proof. exact (proj1 (@lem1578270 x y h1)). Qed.
Lemma lem1578277 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578278 : term232 = term726.
Proof. exact (@lem1578277 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578279 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578280 : term232 = False.
Proof. exact (TRANS (@lem1578278) (@lem1578279)). Qed.
Lemma lem1578281 (x : real) (y : real) (h1 : term660 x y) : False.
Proof. exact (EQ_MP (@lem1578280) (@lem1578275 x y h1)). Qed.
Lemma lem1578282 (x : real) (y : real) (h1 : term687 x y) : False.
Proof. exact (or_elim (@lem1578240 x y h1) (fun h0 : term685 x y => @lem1578268 x y h0) (fun h0 : term660 x y => @lem1578281 x y h0)). Qed.
Lemma lem1578283 (x : real) (y : real) (h1 : term714 x y) : term714 x y.
Proof. exact (h1). Qed.
Lemma lem1578284 (x : real) (y : real) (h1 : term676 x y) : term676 x y.
Proof. exact (h1). Qed.
Lemma lem1578285 (x : real) (y : real) (h1 : term676 x y) : term268 x y.
Proof. exact (proj2 (@lem1578284 x y h1)). Qed.
Lemma lem1578287 (x : real) (y : real) (h1 : term676 x y) : term232.
Proof. exact (proj2 (@lem1578285 x y h1)). Qed.
Lemma lem1578290 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578291 : term232 = term726.
Proof. exact (@lem1578290 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578292 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578293 : term232 = False.
Proof. exact (TRANS (@lem1578291) (@lem1578292)). Qed.
Lemma lem1578294 (x : real) (y : real) (h1 : term676 x y) : False.
Proof. exact (EQ_MP (@lem1578293) (@lem1578287 x y h1)). Qed.
Lemma lem1578295 (x : real) (y : real) (h1 : term712 x y) : term712 x y.
Proof. exact (h1). Qed.
Lemma lem1578296 (x : real) (y : real) (h1 : term712 x y) : term601.
Proof. exact (proj2 (@lem1578295 x y h1)). Qed.
Lemma lem1578298 (x : real) (y : real) (h1 : term712 x y) : term232.
Proof. exact (proj2 (@lem1578296 x y h1)). Qed.
Lemma lem1578301 (n : nat) (m : nat) : (term725 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1578302 : term232 = term726.
Proof. exact (@lem1578301 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1578303 : term726 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1578304 : term232 = False.
Proof. exact (TRANS (@lem1578302) (@lem1578303)). Qed.
Lemma lem1578305 (x : real) (y : real) (h1 : term712 x y) : False.
Proof. exact (EQ_MP (@lem1578304) (@lem1578298 x y h1)). Qed.
Lemma lem1578306 (x : real) (y : real) (h1 : term714 x y) : False.
Proof. exact (or_elim (@lem1578283 x y h1) (fun h0 : term676 x y => @lem1578294 x y h0) (fun h0 : term712 x y => @lem1578305 x y h0)). Qed.
Lemma lem1578307 (x : real) (y : real) (h1 : term716 x y) : False.
Proof. exact (or_elim (@lem1578239 x y h1) (fun h0 : term687 x y => @lem1578282 x y h0) (fun h0 : term714 x y => @lem1578306 x y h0)). Qed.
Lemma lem1578308 (x : real) (y : real) (h1 : term718 x y) : False.
Proof. exact (or_elim (@lem1578207 x y h1) (fun h0 : term609 => @lem1578238 h0) (fun h0 : term716 x y => @lem1578307 x y h0)). Qed.
Lemma lem1578309 (z : real) (x : real) (y : real) (h1 : term720 z x y) : False.
Proof. exact (or_elim (@lem1578106 z x y h1) (fun h0 : term577 x y z => @lem1578206 x y z h0) (fun h0 : term718 x y => @lem1578308 x y h0)). Qed.
Lemma lem1578310 (z : real) (x : real) (y : real) (h1 : term722 z x y) : False.
Proof. exact (or_elim (@lem1578005 z x y h1) (fun h0 : term508 y x z => @lem1578105 y x z h0) (fun h0 : term720 z x y => @lem1578309 z x y h0)). Qed.
Lemma lem1578311 (z : real) (x : real) (y : real) (h1 : term724 z x y) : False.
Proof. exact (or_elim (@lem1577954 z x y h1) (fun h0 : term273 x y => @lem1578004 x y h0) (fun h0 : term722 z x y => @lem1578310 z x y h0)). Qed.
Lemma lem1578312 (z : real) (x : real) (y : real) (h1 : term170 z x y) : term170 z x y.
Proof. exact (h1). Qed.
Lemma lem1578313 (z : real) (x : real) (y : real) (h1 : term170 z x y) : term724 z x y.
Proof. exact (EQ_MP (@lem1577953 z x y) (@lem1578312 z x y h1)). Qed.
Lemma lem1578314 (z : real) (x : real) (y : real) (h1 : term170 z x y) : (term724 z x y) = False.
Proof. exact (prop_ext (fun h2 : term724 z x y => @lem1578311 z x y h2) (fun h2 : False => @lem1578313 z x y h1)). Qed.
Lemma lem1578315 (z : real) (x : real) (y : real) (h1 : term170 z x y) : False.
Proof. exact (EQ_MP (@lem1578314 z x y h1) (@lem1578313 z x y h1)). Qed.
Lemma lem1578316 (z : real) (x : real) (y : real) (h1 : term18 z x y) : term18 z x y.
Proof. exact (h1). Qed.
Lemma lem1578317 (z : real) (x : real) (y : real) (h1 : term18 z x y) : term170 z x y.
Proof. exact (EQ_MP (@lem1575270 z x y) (@lem1578316 z x y h1)). Qed.
Lemma lem1578318 (z : real) (x : real) (y : real) (h1 : term18 z x y) : (term170 z x y) = False.
Proof. exact (prop_ext (fun h2 : term170 z x y => @lem1578315 z x y h2) (fun h2 : False => @lem1578317 z x y h1)). Qed.
Lemma lem1578319 (z : real) (x : real) (y : real) (h1 : term18 z x y) : False.
Proof. exact (EQ_MP (@lem1578318 z x y h1) (@lem1578317 z x y h1)). Qed.
Lemma lem1578320 (z : real) (x : real) (y : real) : term727 z x y.
Proof. exact (fun h0 : term18 z x y => @lem1578319 z x y h0). Qed.
Lemma lem1578321 (z : real) (x : real) (y : real) : term728 z x y.
Proof. exact (@lem1386578 (term729 z x y)). Qed.
Lemma lem1578322 (z : real) (x : real) (y : real) : term729 z x y.
Proof. exact (@lem1578321 z x y (@lem1578320 z x y)). Qed.

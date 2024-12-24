Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_EQ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1507896 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 ((real_neg x) = y) (x = (real_neg y))). Qed.
Lemma lem1507897 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1507898 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1507897 (term6 x)). Qed.
Lemma lem1507899 (x : real) (y : real) : (term7 x y) = (((real_neg x) = y) = (x = (real_neg y))).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1507900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1507901 (x : real) (y : real) : (term8 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1507900) (@lem1507899 x y)). Qed.
Lemma lem1507902 (x : real) (y : real) : (term8 x y) = (term1 x y).
Proof. exact (TRANS (@lem1507901 x y) (@lem1507896 x y)). Qed.
Lemma lem1507903 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1507902 x y)). Qed.
Lemma lem1507904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507905 (x : real) : (term5 x) = (term11 x).
Proof. exact (MK_COMB (@lem1507904) (@lem1507903 x)). Qed.
Lemma lem1507906 (x : real) : (term4 x) = (term11 x).
Proof. exact (TRANS (@lem1507898 x) (@lem1507905 x)). Qed.
Lemma lem1507907 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1507908 : term12 = term13.
Proof. exact (@lem1507907 term14). Qed.
Lemma lem1507909 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1507910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1507911 (x : real) : (term17 x) = (term4 x).
Proof. exact (MK_COMB (@lem1507910) (@lem1507909 x)). Qed.
Lemma lem1507912 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1507911 x) (@lem1507906 x)). Qed.
Lemma lem1507913 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1507912 x)). Qed.
Lemma lem1507914 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507915 : term13 = term20.
Proof. exact (MK_COMB (@lem1507914) (@lem1507913)). Qed.
Lemma lem1507917 : term12 = term20.
Proof. exact (TRANS (@lem1507908) (@lem1507915)). Qed.
Lemma lem1507934 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1507935 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1507934 x y)). Qed.
Lemma lem1507936 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507937 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1507936) (@lem1507935 x)). Qed.
Lemma lem1507938 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1507937 x)). Qed.
Lemma lem1507939 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507940 : term20 = term20.
Proof. exact (MK_COMB (@lem1507939) (@lem1507938)). Qed.
Lemma lem1507941 : term12 = term20.
Proof. exact (TRANS (@lem1507917) (@lem1507940)). Qed.
Lemma lem1507942 (x : real) (y : real) : ((real_neg x) = y) = ((term21 x y) = term22).
Proof. exact (@lem1483529 (real_neg x) y). Qed.
Lemma lem1507943 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1507950 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1507951 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1507952 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1507951) (@lem1507950 x)). Qed.
Lemma lem1507953 (x : real) (y : real) : (term21 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1507952 x) (@lem1507943 y)). Qed.
Lemma lem1507960 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (term23 x) y). Qed.
Lemma lem1507961 (x : real) (y : real) : (term21 x y) = (term27 x y).
Proof. exact (TRANS (@lem1507953 x y) (@lem1507960 x y)). Qed.
Lemma lem1507962 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507963 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1507962) (@lem1507961 x y)). Qed.
Lemma lem1507964 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1507965 (x : real) (y : real) : ((term21 x y) = term22) = ((term27 x y) = term22).
Proof. exact (MK_COMB (@lem1507963 x y) (@lem1507964)). Qed.
Lemma lem1507966 (x : real) (y : real) : ((real_neg x) = y) = ((term27 x y) = term22).
Proof. exact (TRANS (@lem1507942 x y) (@lem1507965 x y)). Qed.
Lemma lem1507967 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483554 x (real_neg y)). Qed.
Lemma lem1507974 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1507977 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1507978 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1507977 x) (@lem1507974 y)). Qed.
Lemma lem1507979 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483519 x (term23 y)). Qed.
Lemma lem1507980 (y : real) : (term35 y) = (term36 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1507982 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1507983 : term40 = term41.
Proof. exact (@lem1507982 term42 term42). Qed.
Lemma lem1507984 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1507985 : term44 = term42.
Proof. exact (EQ_MP (@lem1507984) (@lem940073)). Qed.
Lemma lem1507986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1507987 : term41 = term45.
Proof. exact (MK_COMB (@lem1507986) (@lem1507985)). Qed.
Lemma lem1507988 : term40 = term45.
Proof. exact (TRANS (@lem1507983) (@lem1507987)). Qed.
Lemma lem1507989 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507990 : term46 = term47.
Proof. exact (MK_COMB (@lem1507989) (@lem1507988)). Qed.
Lemma lem1507991 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1507992 (y : real) : (term36 y) = (term48 y).
Proof. exact (MK_COMB (@lem1507990) (@lem1507991 y)). Qed.
Lemma lem1507993 (y : real) : (term35 y) = (term48 y).
Proof. exact (TRANS (@lem1507980 y) (@lem1507992 y)). Qed.
Lemma lem1507994 (y : real) : (term48 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1507995 (y : real) : (term35 y) = y.
Proof. exact (TRANS (@lem1507993 y) (@lem1507994 y)). Qed.
Lemma lem1507996 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1507999 (x : real) (y : real) : (term34 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1507996 x) (@lem1507995 y)). Qed.
Lemma lem1508000 (x : real) (y : real) : (term33 x y) = (real_add x y).
Proof. exact (TRANS (@lem1507979 x y) (@lem1507999 x y)). Qed.
Lemma lem1508001 (x : real) (y : real) : (term32 x y) = (real_add x y).
Proof. exact (TRANS (@lem1507978 x y) (@lem1508000 x y)). Qed.
Lemma lem1508002 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1508003 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1508002) (@lem1508001 x y)). Qed.
Lemma lem1508004 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1508011 (x : real) (y : real) : (term51 x y) = (term27 x y).
Proof. exact (@lem1483508 x term37 y). Qed.
Lemma lem1508012 (x : real) (y : real) : (term50 x y) = (term27 x y).
Proof. exact (TRANS (@lem1508004 x y) (@lem1508011 x y)). Qed.
Lemma lem1508013 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1508014 (x : real) (y : real) : ((term49 x y) = (term50 x y)) = ((term49 x y) = (term27 x y)).
Proof. exact (MK_COMB (@lem1508013 x y) (@lem1508012 x y)). Qed.
Lemma lem1508015 (x : real) (y : real) : (term49 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1508014 x y) (@lem1508003 x y)). Qed.
Lemma lem1508016 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508017 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1508016) (@lem1508015 x y)). Qed.
Lemma lem1508018 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508019 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1508017 x y) (@lem1508018)). Qed.
Lemma lem1508020 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508021 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1508020) (@lem1508001 x y)). Qed.
Lemma lem1508022 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508023 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1508021 x y) (@lem1508022)). Qed.
Lemma lem1508024 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508025 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1508024) (@lem1508023 x y)). Qed.
Lemma lem1508026 (x : real) (y : real) : (term31 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1508025 x y) (@lem1508019 x y)). Qed.
Lemma lem1508027 (x : real) (y : real) : (term30 x y) = (term63 x y).
Proof. exact (TRANS (@lem1507967 x y) (@lem1508026 x y)). Qed.
Lemma lem1508028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1508029 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1508028) (@lem1507966 x y)). Qed.
Lemma lem1508030 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1508029 x y) (@lem1508027 x y)). Qed.
Lemma lem1508031 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (@lem1483554 (real_neg x) y). Qed.
Lemma lem1508032 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508039 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1508040 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1508041 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1508040) (@lem1508039 x)). Qed.
Lemma lem1508042 (x : real) (y : real) : (term21 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1508041 x) (@lem1508032 y)). Qed.
Lemma lem1508049 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (term23 x) y). Qed.
Lemma lem1508050 (x : real) (y : real) : (term21 x y) = (term27 x y).
Proof. exact (TRANS (@lem1508042 x y) (@lem1508049 x y)). Qed.
Lemma lem1508051 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1508052 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1508051) (@lem1508050 x y)). Qed.
Lemma lem1508053 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (@lem1483512 (term27 x y)). Qed.
Lemma lem1508054 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483508 (term23 x) term37 (term23 y)). Qed.
Lemma lem1508055 (y : real) : (term35 y) = (term36 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1508057 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508058 : term40 = term41.
Proof. exact (@lem1508057 term42 term42). Qed.
Lemma lem1508059 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508060 : term44 = term42.
Proof. exact (EQ_MP (@lem1508059) (@lem940073)). Qed.
Lemma lem1508061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508062 : term41 = term45.
Proof. exact (MK_COMB (@lem1508061) (@lem1508060)). Qed.
Lemma lem1508063 : term40 = term45.
Proof. exact (TRANS (@lem1508058) (@lem1508062)). Qed.
Lemma lem1508064 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508065 : term46 = term47.
Proof. exact (MK_COMB (@lem1508064) (@lem1508063)). Qed.
Lemma lem1508066 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508067 (y : real) : (term36 y) = (term48 y).
Proof. exact (MK_COMB (@lem1508065) (@lem1508066 y)). Qed.
Lemma lem1508068 (y : real) : (term35 y) = (term48 y).
Proof. exact (TRANS (@lem1508055 y) (@lem1508067 y)). Qed.
Lemma lem1508069 (y : real) : (term48 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1508070 (y : real) : (term35 y) = y.
Proof. exact (TRANS (@lem1508068 y) (@lem1508069 y)). Qed.
Lemma lem1508071 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483476 term37 term37 x). Qed.
Lemma lem1508073 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508074 : term40 = term41.
Proof. exact (@lem1508073 term42 term42). Qed.
Lemma lem1508075 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508076 : term44 = term42.
Proof. exact (EQ_MP (@lem1508075) (@lem940073)). Qed.
Lemma lem1508077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508078 : term41 = term45.
Proof. exact (MK_COMB (@lem1508077) (@lem1508076)). Qed.
Lemma lem1508079 : term40 = term45.
Proof. exact (TRANS (@lem1508074) (@lem1508078)). Qed.
Lemma lem1508080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508081 : term46 = term47.
Proof. exact (MK_COMB (@lem1508080) (@lem1508079)). Qed.
Lemma lem1508082 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508083 (x : real) : (term36 x) = (term48 x).
Proof. exact (MK_COMB (@lem1508081) (@lem1508082 x)). Qed.
Lemma lem1508084 (x : real) : (term35 x) = (term48 x).
Proof. exact (TRANS (@lem1508071 x) (@lem1508083 x)). Qed.
Lemma lem1508085 (x : real) : (term48 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1508086 (x : real) : (term35 x) = x.
Proof. exact (TRANS (@lem1508084 x) (@lem1508085 x)). Qed.
Lemma lem1508087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508088 (x : real) : (term74 x) = (real_add x).
Proof. exact (MK_COMB (@lem1508087) (@lem1508086 x)). Qed.
Lemma lem1508089 (x : real) (y : real) : (term73 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1508088 x) (@lem1508070 y)). Qed.
Lemma lem1508090 (x : real) (y : real) : (term72 x y) = (real_add x y).
Proof. exact (TRANS (@lem1508054 x y) (@lem1508089 x y)). Qed.
Lemma lem1508091 (x : real) (y : real) : (term71 x y) = (real_add x y).
Proof. exact (TRANS (@lem1508053 x y) (@lem1508090 x y)). Qed.
Lemma lem1508092 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1508093 (x : real) (y : real) : ((term70 x y) = (term71 x y)) = ((term70 x y) = (real_add x y)).
Proof. exact (MK_COMB (@lem1508092 x y) (@lem1508091 x y)). Qed.
Lemma lem1508094 (x : real) (y : real) : (term70 x y) = (real_add x y).
Proof. exact (EQ_MP (@lem1508093 x y) (@lem1508052 x y)). Qed.
Lemma lem1508095 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508096 (x : real) (y : real) : (term76 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1508095) (@lem1508094 x y)). Qed.
Lemma lem1508097 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508098 (x : real) (y : real) : (term77 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1508096 x y) (@lem1508097)). Qed.
Lemma lem1508099 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508100 (x : real) (y : real) : (term78 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1508099) (@lem1508050 x y)). Qed.
Lemma lem1508101 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508102 (x : real) (y : real) : (term79 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1508100 x y) (@lem1508101)). Qed.
Lemma lem1508103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508104 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1508103) (@lem1508102 x y)). Qed.
Lemma lem1508105 (x : real) (y : real) : (term69 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1508104 x y) (@lem1508098 x y)). Qed.
Lemma lem1508106 (x : real) (y : real) : (term68 x y) = (term82 x y).
Proof. exact (TRANS (@lem1508031 x y) (@lem1508105 x y)). Qed.
Lemma lem1508107 (x : real) (y : real) : (x = (real_neg y)) = ((term32 x y) = term22).
Proof. exact (@lem1483529 x (real_neg y)). Qed.
Lemma lem1508114 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1508117 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1508118 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1508117 x) (@lem1508114 y)). Qed.
Lemma lem1508119 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483519 x (term23 y)). Qed.
Lemma lem1508120 (y : real) : (term35 y) = (term36 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1508122 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508123 : term40 = term41.
Proof. exact (@lem1508122 term42 term42). Qed.
Lemma lem1508124 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508125 : term44 = term42.
Proof. exact (EQ_MP (@lem1508124) (@lem940073)). Qed.
Lemma lem1508126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508127 : term41 = term45.
Proof. exact (MK_COMB (@lem1508126) (@lem1508125)). Qed.
Lemma lem1508128 : term40 = term45.
Proof. exact (TRANS (@lem1508123) (@lem1508127)). Qed.
Lemma lem1508129 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508130 : term46 = term47.
Proof. exact (MK_COMB (@lem1508129) (@lem1508128)). Qed.
Lemma lem1508131 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508132 (y : real) : (term36 y) = (term48 y).
Proof. exact (MK_COMB (@lem1508130) (@lem1508131 y)). Qed.
Lemma lem1508133 (y : real) : (term35 y) = (term48 y).
Proof. exact (TRANS (@lem1508120 y) (@lem1508132 y)). Qed.
Lemma lem1508134 (y : real) : (term48 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1508135 (y : real) : (term35 y) = y.
Proof. exact (TRANS (@lem1508133 y) (@lem1508134 y)). Qed.
Lemma lem1508136 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1508139 (x : real) (y : real) : (term34 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1508136 x) (@lem1508135 y)). Qed.
Lemma lem1508140 (x : real) (y : real) : (term33 x y) = (real_add x y).
Proof. exact (TRANS (@lem1508119 x y) (@lem1508139 x y)). Qed.
Lemma lem1508141 (x : real) (y : real) : (term32 x y) = (real_add x y).
Proof. exact (TRANS (@lem1508118 x y) (@lem1508140 x y)). Qed.
Lemma lem1508142 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1508143 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1508142) (@lem1508141 x y)). Qed.
Lemma lem1508144 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508145 (x : real) (y : real) : ((term32 x y) = term22) = ((real_add x y) = term22).
Proof. exact (MK_COMB (@lem1508143 x y) (@lem1508144)). Qed.
Lemma lem1508146 (x : real) (y : real) : (x = (real_neg y)) = ((real_add x y) = term22).
Proof. exact (TRANS (@lem1508107 x y) (@lem1508145 x y)). Qed.
Lemma lem1508147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1508148 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1508147) (@lem1508106 x y)). Qed.
Lemma lem1508149 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1508148 x y) (@lem1508146 x y)). Qed.
Lemma lem1508150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508151 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1508150) (@lem1508030 x y)). Qed.
Lemma lem1508152 (x : real) (y : real) : (term1 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1508151 x y) (@lem1508149 x y)). Qed.
Lemma lem1508153 (x : real) : (term10 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1508152 x y)). Qed.
Lemma lem1508154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508155 (x : real) : (term11 x) = (term93 x).
Proof. exact (MK_COMB (@lem1508154) (@lem1508153 x)). Qed.
Lemma lem1508156 : term19 = term94.
Proof. exact (fun_ext (fun x : real => @lem1508155 x)). Qed.
Lemma lem1508157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508158 : term20 = term95.
Proof. exact (MK_COMB (@lem1508157) (@lem1508156)). Qed.
Lemma lem1508159 : term12 = term95.
Proof. exact (TRANS (@lem1507941) (@lem1508158)). Qed.
Lemma lem1508165 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1508166 (P : real -> Prop) (Q : real -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem1508165 real P Q). Qed.
Lemma lem1508167 (x : real) : (term100 x) = (term101 x).
Proof. exact (@lem1508166 (term102 x) (term103 x)). Qed.
Lemma lem1508168 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1508169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508170 (x : real) (y : real) : (term105 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1508169) (@lem1508168 x y)). Qed.
Lemma lem1508171 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1508172 (x : real) (y : real) : (term107 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1508170 x y) (@lem1508171 x y)). Qed.
Lemma lem1508173 (x : real) : (term108 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1508172 x y)). Qed.
Lemma lem1508174 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508175 (x : real) : (term100 x) = (term93 x).
Proof. exact (MK_COMB (@lem1508174) (@lem1508173 x)). Qed.
Lemma lem1508176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1508177 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1508176) (@lem1508175 x)). Qed.
Lemma lem1508178 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1508179 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1508178 x y)). Qed.
Lemma lem1508180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508181 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1508180) (@lem1508179 x)). Qed.
Lemma lem1508182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508183 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1508182) (@lem1508181 x)). Qed.
Lemma lem1508184 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1508185 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1508184 x y)). Qed.
Lemma lem1508186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508187 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1508186) (@lem1508185 x)). Qed.
Lemma lem1508188 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1508183 x) (@lem1508187 x)). Qed.
Lemma lem1508189 (x : real) : ((term100 x) = (term101 x)) = ((term93 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1508177 x) (@lem1508188 x)). Qed.
Lemma lem1508190 (x : real) : (term93 x) = (term119 x).
Proof. exact (EQ_MP (@lem1508189 x) (@lem1508167 x)). Qed.
Lemma lem1508287 : term94 = term120.
Proof. exact (fun_ext (fun x : real => @lem1508190 x)). Qed.
Lemma lem1508288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508289 : term95 = term121.
Proof. exact (MK_COMB (@lem1508288) (@lem1508287)). Qed.
Lemma lem1508291 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1508292 (P : real -> Prop) (Q : real -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem1508291 real P Q). Qed.
Lemma lem1508293 : term122 = term123.
Proof. exact (@lem1508292 term124 term125). Qed.
Lemma lem1508294 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1508295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508296 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1508295) (@lem1508294 x)). Qed.
Lemma lem1508297 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1508298 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1508296 x) (@lem1508297 x)). Qed.
Lemma lem1508299 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1508298 x)). Qed.
Lemma lem1508300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508301 : term122 = term121.
Proof. exact (MK_COMB (@lem1508300) (@lem1508299)). Qed.
Lemma lem1508302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1508303 : term131 = term132.
Proof. exact (MK_COMB (@lem1508302) (@lem1508301)). Qed.
Lemma lem1508304 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1508305 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1508304 x)). Qed.
Lemma lem1508306 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508307 : term134 = term135.
Proof. exact (MK_COMB (@lem1508306) (@lem1508305)). Qed.
Lemma lem1508308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508309 : term136 = term137.
Proof. exact (MK_COMB (@lem1508308) (@lem1508307)). Qed.
Lemma lem1508310 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1508311 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1508310 x)). Qed.
Lemma lem1508312 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508313 : term139 = term140.
Proof. exact (MK_COMB (@lem1508312) (@lem1508311)). Qed.
Lemma lem1508314 : term123 = term141.
Proof. exact (MK_COMB (@lem1508309) (@lem1508313)). Qed.
Lemma lem1508315 : (term122 = term123) = (term121 = term141).
Proof. exact (MK_COMB (@lem1508303) (@lem1508314)). Qed.
Lemma lem1508316 : term121 = term141.
Proof. exact (EQ_MP (@lem1508315) (@lem1508293)). Qed.
Lemma lem1508421 : term95 = term141.
Proof. exact (TRANS (@lem1508289) (@lem1508316)). Qed.
Lemma lem1508423 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term96 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1508424 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term98 P Q).
Proof. exact (@lem1508423 real P Q). Qed.
Lemma lem1508425 : term123 = term122.
Proof. exact (@lem1508424 term124 term125). Qed.
Lemma lem1508426 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1508427 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1508426 x)). Qed.
Lemma lem1508428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508429 : term134 = term135.
Proof. exact (MK_COMB (@lem1508428) (@lem1508427)). Qed.
Lemma lem1508430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508431 : term136 = term137.
Proof. exact (MK_COMB (@lem1508430) (@lem1508429)). Qed.
Lemma lem1508432 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1508433 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1508432 x)). Qed.
Lemma lem1508434 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508435 : term139 = term140.
Proof. exact (MK_COMB (@lem1508434) (@lem1508433)). Qed.
Lemma lem1508436 : term123 = term141.
Proof. exact (MK_COMB (@lem1508431) (@lem1508435)). Qed.
Lemma lem1508437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1508438 : term142 = term143.
Proof. exact (MK_COMB (@lem1508437) (@lem1508436)). Qed.
Lemma lem1508439 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1508440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508441 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1508440) (@lem1508439 x)). Qed.
Lemma lem1508442 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1508443 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1508441 x) (@lem1508442 x)). Qed.
Lemma lem1508444 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1508443 x)). Qed.
Lemma lem1508445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508446 : term122 = term121.
Proof. exact (MK_COMB (@lem1508445) (@lem1508444)). Qed.
Lemma lem1508447 : (term123 = term122) = (term141 = term121).
Proof. exact (MK_COMB (@lem1508438) (@lem1508446)). Qed.
Lemma lem1508448 : term141 = term121.
Proof. exact (EQ_MP (@lem1508447) (@lem1508425)). Qed.
Lemma lem1508450 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term96 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1508451 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term98 P Q).
Proof. exact (@lem1508450 real P Q). Qed.
Lemma lem1508452 (x : real) : (term101 x) = (term100 x).
Proof. exact (@lem1508451 (term102 x) (term103 x)). Qed.
Lemma lem1508453 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1508454 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1508453 x y)). Qed.
Lemma lem1508455 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508456 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1508455) (@lem1508454 x)). Qed.
Lemma lem1508457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508458 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1508457) (@lem1508456 x)). Qed.
Lemma lem1508459 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1508460 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1508459 x y)). Qed.
Lemma lem1508461 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508462 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1508461) (@lem1508460 x)). Qed.
Lemma lem1508463 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1508458 x) (@lem1508462 x)). Qed.
Lemma lem1508464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1508465 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1508464) (@lem1508463 x)). Qed.
Lemma lem1508466 (x : real) (y : real) : (term104 x y) = (term67 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1508467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508468 (x : real) (y : real) : (term105 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1508467) (@lem1508466 x y)). Qed.
Lemma lem1508469 (x : real) (y : real) : (term106 x y) = (term88 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1508470 (x : real) (y : real) : (term107 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1508468 x y) (@lem1508469 x y)). Qed.
Lemma lem1508471 (x : real) : (term108 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1508470 x y)). Qed.
Lemma lem1508472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508473 (x : real) : (term100 x) = (term93 x).
Proof. exact (MK_COMB (@lem1508472) (@lem1508471 x)). Qed.
Lemma lem1508474 (x : real) : ((term101 x) = (term100 x)) = ((term119 x) = (term93 x)).
Proof. exact (MK_COMB (@lem1508465 x) (@lem1508473 x)). Qed.
Lemma lem1508475 (x : real) : (term119 x) = (term93 x).
Proof. exact (EQ_MP (@lem1508474 x) (@lem1508452 x)). Qed.
Lemma lem1508476 : term120 = term94.
Proof. exact (fun_ext (fun x : real => @lem1508475 x)). Qed.
Lemma lem1508477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508478 : term121 = term95.
Proof. exact (MK_COMB (@lem1508477) (@lem1508476)). Qed.
Lemma lem1508479 : term141 = term95.
Proof. exact (TRANS (@lem1508448) (@lem1508478)). Qed.
Lemma lem1508480 : term95 = term95.
Proof. exact (TRANS (@lem1508421) (@lem1508479)). Qed.
Lemma lem1508483 : term12 = term95.
Proof. exact (TRANS (@lem1508159) (@lem1508480)). Qed.
Lemma lem1508500 (x : real) (y : real) : (term88 x y) = (term146 x y).
Proof. exact (@lem19367 (term56 x y) (term60 x y) ((real_add x y) = term22)). Qed.
Lemma lem1508517 (x : real) (y : real) : (term67 x y) = (term147 x y).
Proof. exact (@lem19158 (term60 x y) ((term27 x y) = term22) (term56 x y)). Qed.
Lemma lem1508518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1508519 (x : real) (y : real) : (term90 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1508518) (@lem1508517 x y)). Qed.
Lemma lem1508520 (x : real) (y : real) : (term91 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1508519 x y) (@lem1508500 x y)). Qed.
Lemma lem1508521 (x : real) : (term92 x) = (term150 x).
Proof. exact (fun_ext (fun y : real => @lem1508520 x y)). Qed.
Lemma lem1508522 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508523 (x : real) : (term93 x) = (term151 x).
Proof. exact (MK_COMB (@lem1508522) (@lem1508521 x)). Qed.
Lemma lem1508524 : term94 = term152.
Proof. exact (fun_ext (fun x : real => @lem1508523 x)). Qed.
Lemma lem1508525 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1508526 : term95 = term153.
Proof. exact (MK_COMB (@lem1508525) (@lem1508524)). Qed.
Lemma lem1508527 : term12 = term153.
Proof. exact (TRANS (@lem1508483) (@lem1508526)). Qed.
Lemma lem1508549 (x : real) (y : real) (h1 : term149 x y) : term149 x y.
Proof. exact (h1). Qed.
Lemma lem1508550 (x : real) (y : real) (h1 : term147 x y) : term147 x y.
Proof. exact (h1). Qed.
Lemma lem1508551 (x : real) (y : real) (h1 : term154 x y) : term154 x y.
Proof. exact (h1). Qed.
Lemma lem1508552 (x : real) (y : real) (h1 : term154 x y) : term60 x y.
Proof. exact (proj2 (@lem1508551 x y h1)). Qed.
Lemma lem1508553 (x : real) (y : real) (h1 : term154 x y) : (term27 x y) = term22.
Proof. exact (proj1 (@lem1508551 x y h1)). Qed.
Lemma lem1508555 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508556 : term156 = term157.
Proof. exact (@lem1508555 (NUMERAL 0) term42). Qed.
Lemma lem1508557 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1508558 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1508559 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1508558 h1) (fun h1 : term157 = True => @lem1508557)). Qed.
Lemma lem1508560 : term157 = True.
Proof. exact (EQ_MP (@lem1508559) (@lem1508557)). Qed.
Lemma lem1508561 : term156 = True.
Proof. exact (TRANS (@lem1508556) (@lem1508560)). Qed.
Lemma lem1508562 : True = term156.
Proof. exact (SYM (@lem1508561)). Qed.
Lemma lem1508563 : term156.
Proof. exact (EQ_MP (@lem1508562) (@lem0)). Qed.
Lemma lem1508564 (x : real) (y : real) (h1 : term154 x y) : term159 x y.
Proof. exact (conj (@lem1508563) (@lem1508552 x y h1)). Qed.
Lemma lem1508566 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1508567 (x : real) (y : real) : term161 x y.
Proof. exact (@lem1508566 term45 (real_add x y)). Qed.
Lemma lem1508568 (x : real) (y : real) (h1 : term154 x y) : term162 x y.
Proof. exact (@lem1508567 x y (@lem1508564 x y h1)). Qed.
Lemma lem1508569 (x : real) (y : real) : (term163 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1508570 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508571 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1508570) (@lem1508569 x y)). Qed.
Lemma lem1508572 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508573 (x : real) (y : real) : (term162 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1508571 x y) (@lem1508572)). Qed.
Lemma lem1508574 (x : real) (y : real) (h1 : term154 x y) : term60 x y.
Proof. exact (EQ_MP (@lem1508573 x y) (@lem1508568 x y h1)). Qed.
Lemma lem1508576 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1508577 (x : real) (y : real) : term166 x y.
Proof. exact (@lem1508576 (term27 x y)). Qed.
Lemma lem1508578 (x : real) (y : real) (h1 : term154 x y) : term167 x y.
Proof. exact (@lem1508577 x y (@lem1508553 x y h1)). Qed.
Lemma lem1508579 (x : real) (y : real) (h1 : term154 x y) : term168 x y.
Proof. exact (@lem1508578 x y h1 term45). Qed.
Lemma lem1508580 (x : real) (y : real) : (term168 x y) = ((term169 x y) = term22).
Proof. exact (eq_refl (term168 x y)). Qed.
Lemma lem1508581 (x : real) (y : real) (h1 : term154 x y) : (term169 x y) = term22.
Proof. exact (EQ_MP (@lem1508580 x y) (@lem1508579 x y h1)). Qed.
Lemma lem1508582 (x : real) (y : real) : (term169 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1508583 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1508584 (x : real) (y : real) : (term170 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1508583) (@lem1508582 x y)). Qed.
Lemma lem1508585 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508586 (x : real) (y : real) : ((term169 x y) = term22) = ((term27 x y) = term22).
Proof. exact (MK_COMB (@lem1508584 x y) (@lem1508585)). Qed.
Lemma lem1508587 (x : real) (y : real) (h1 : term154 x y) : (term27 x y) = term22.
Proof. exact (EQ_MP (@lem1508586 x y) (@lem1508581 x y h1)). Qed.
Lemma lem1508588 (x : real) (y : real) (h1 : term154 x y) : term154 x y.
Proof. exact (conj (@lem1508587 x y h1) (@lem1508574 x y h1)). Qed.
Lemma lem1508590 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1508591 (x : real) (y : real) : term172 x y.
Proof. exact (@lem1508590 (term27 x y) (real_add x y)). Qed.
Lemma lem1508592 (x : real) (y : real) (h1 : term154 x y) : term173 x y.
Proof. exact (@lem1508591 x y (@lem1508588 x y h1)). Qed.
Lemma lem1508593 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483480 (term23 x) x (term23 y) y). Qed.
Lemma lem1508594 (x : real) : (term176 x) = (term177 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1508596 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508597 : term179 = term22.
Proof. exact (@lem1508596 term42). Qed.
Lemma lem1508598 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508599 : term180 = term181.
Proof. exact (MK_COMB (@lem1508598) (@lem1508597)). Qed.
Lemma lem1508600 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508601 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1508599) (@lem1508600 x)). Qed.
Lemma lem1508602 (x : real) : (term176 x) = (term182 x).
Proof. exact (TRANS (@lem1508594 x) (@lem1508601 x)). Qed.
Lemma lem1508603 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1508604 (x : real) : (term176 x) = term22.
Proof. exact (TRANS (@lem1508602 x) (@lem1508603 x)). Qed.
Lemma lem1508605 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508606 (x : real) : (term183 x) = term184.
Proof. exact (MK_COMB (@lem1508605) (@lem1508604 x)). Qed.
Lemma lem1508607 (y : real) : (term176 y) = (term177 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1508609 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508610 : term179 = term22.
Proof. exact (@lem1508609 term42). Qed.
Lemma lem1508611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508612 : term180 = term181.
Proof. exact (MK_COMB (@lem1508611) (@lem1508610)). Qed.
Lemma lem1508613 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508614 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1508612) (@lem1508613 y)). Qed.
Lemma lem1508615 (y : real) : (term176 y) = (term182 y).
Proof. exact (TRANS (@lem1508607 y) (@lem1508614 y)). Qed.
Lemma lem1508616 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1508617 (y : real) : (term176 y) = term22.
Proof. exact (TRANS (@lem1508615 y) (@lem1508616 y)). Qed.
Lemma lem1508618 (x : real) (y : real) : (term175 x y) = term185.
Proof. exact (MK_COMB (@lem1508606 x) (@lem1508617 y)). Qed.
Lemma lem1508619 (x : real) (y : real) : (term174 x y) = term185.
Proof. exact (TRANS (@lem1508593 x y) (@lem1508618 x y)). Qed.
Lemma lem1508620 : term185 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1508621 (x : real) (y : real) : (term174 x y) = term22.
Proof. exact (TRANS (@lem1508619 x y) (@lem1508620)). Qed.
Lemma lem1508622 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508623 (x : real) (y : real) : (term186 x y) = term187.
Proof. exact (MK_COMB (@lem1508622) (@lem1508621 x y)). Qed.
Lemma lem1508624 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508625 (x : real) (y : real) : (term173 x y) = term188.
Proof. exact (MK_COMB (@lem1508623 x y) (@lem1508624)). Qed.
Lemma lem1508626 (x : real) (y : real) (h1 : term154 x y) : term188.
Proof. exact (EQ_MP (@lem1508625 x y) (@lem1508592 x y h1)). Qed.
Lemma lem1508628 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508629 : term188 = term189.
Proof. exact (@lem1508628 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1508630 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1508631 : term188 = False.
Proof. exact (TRANS (@lem1508629) (@lem1508630)). Qed.
Lemma lem1508632 (x : real) (y : real) (h1 : term154 x y) : False.
Proof. exact (EQ_MP (@lem1508631) (@lem1508626 x y h1)). Qed.
Lemma lem1508633 (x : real) (y : real) (h1 : term190 x y) : term190 x y.
Proof. exact (h1). Qed.
Lemma lem1508634 (x : real) (y : real) (h1 : term190 x y) : term56 x y.
Proof. exact (proj2 (@lem1508633 x y h1)). Qed.
Lemma lem1508635 (x : real) (y : real) (h1 : term190 x y) : (term27 x y) = term22.
Proof. exact (proj1 (@lem1508633 x y h1)). Qed.
Lemma lem1508637 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508638 : term156 = term157.
Proof. exact (@lem1508637 (NUMERAL 0) term42). Qed.
Lemma lem1508639 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1508640 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1508641 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1508640 h1) (fun h1 : term157 = True => @lem1508639)). Qed.
Lemma lem1508642 : term157 = True.
Proof. exact (EQ_MP (@lem1508641) (@lem1508639)). Qed.
Lemma lem1508643 : term156 = True.
Proof. exact (TRANS (@lem1508638) (@lem1508642)). Qed.
Lemma lem1508644 : True = term156.
Proof. exact (SYM (@lem1508643)). Qed.
Lemma lem1508645 : term156.
Proof. exact (EQ_MP (@lem1508644) (@lem0)). Qed.
Lemma lem1508646 (x : real) (y : real) (h1 : term190 x y) : term191 x y.
Proof. exact (conj (@lem1508645) (@lem1508634 x y h1)). Qed.
Lemma lem1508648 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1508649 (x : real) (y : real) : term192 x y.
Proof. exact (@lem1508648 term45 (term27 x y)). Qed.
Lemma lem1508650 (x : real) (y : real) (h1 : term190 x y) : term193 x y.
Proof. exact (@lem1508649 x y (@lem1508646 x y h1)). Qed.
Lemma lem1508651 (x : real) (y : real) : (term169 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1508652 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508653 (x : real) (y : real) : (term194 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1508652) (@lem1508651 x y)). Qed.
Lemma lem1508654 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508655 (x : real) (y : real) : (term193 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1508653 x y) (@lem1508654)). Qed.
Lemma lem1508656 (x : real) (y : real) (h1 : term190 x y) : term56 x y.
Proof. exact (EQ_MP (@lem1508655 x y) (@lem1508650 x y h1)). Qed.
Lemma lem1508658 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1508659 (x : real) (y : real) : term166 x y.
Proof. exact (@lem1508658 (term27 x y)). Qed.
Lemma lem1508660 (x : real) (y : real) (h1 : term190 x y) : term167 x y.
Proof. exact (@lem1508659 x y (@lem1508635 x y h1)). Qed.
Lemma lem1508661 (x : real) (y : real) (h1 : term190 x y) : term195 x y.
Proof. exact (@lem1508660 x y h1 term37). Qed.
Lemma lem1508662 (x : real) (y : real) : (term195 x y) = ((term72 x y) = term22).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1508663 (x : real) (y : real) (h1 : term190 x y) : (term72 x y) = term22.
Proof. exact (EQ_MP (@lem1508662 x y) (@lem1508661 x y h1)). Qed.
Lemma lem1508664 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483508 (term23 x) term37 (term23 y)). Qed.
Lemma lem1508665 (y : real) : (term35 y) = (term36 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1508667 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508668 : term40 = term41.
Proof. exact (@lem1508667 term42 term42). Qed.
Lemma lem1508669 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508670 : term44 = term42.
Proof. exact (EQ_MP (@lem1508669) (@lem940073)). Qed.
Lemma lem1508671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508672 : term41 = term45.
Proof. exact (MK_COMB (@lem1508671) (@lem1508670)). Qed.
Lemma lem1508673 : term40 = term45.
Proof. exact (TRANS (@lem1508668) (@lem1508672)). Qed.
Lemma lem1508674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508675 : term46 = term47.
Proof. exact (MK_COMB (@lem1508674) (@lem1508673)). Qed.
Lemma lem1508676 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508677 (y : real) : (term36 y) = (term48 y).
Proof. exact (MK_COMB (@lem1508675) (@lem1508676 y)). Qed.
Lemma lem1508678 (y : real) : (term35 y) = (term48 y).
Proof. exact (TRANS (@lem1508665 y) (@lem1508677 y)). Qed.
Lemma lem1508679 (y : real) : (term48 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1508680 (y : real) : (term35 y) = y.
Proof. exact (TRANS (@lem1508678 y) (@lem1508679 y)). Qed.
Lemma lem1508681 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483476 term37 term37 x). Qed.
Lemma lem1508683 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1508684 : term40 = term41.
Proof. exact (@lem1508683 term42 term42). Qed.
Lemma lem1508685 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1508686 : term44 = term42.
Proof. exact (EQ_MP (@lem1508685) (@lem940073)). Qed.
Lemma lem1508687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1508688 : term41 = term45.
Proof. exact (MK_COMB (@lem1508687) (@lem1508686)). Qed.
Lemma lem1508689 : term40 = term45.
Proof. exact (TRANS (@lem1508684) (@lem1508688)). Qed.
Lemma lem1508690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508691 : term46 = term47.
Proof. exact (MK_COMB (@lem1508690) (@lem1508689)). Qed.
Lemma lem1508692 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508693 (x : real) : (term36 x) = (term48 x).
Proof. exact (MK_COMB (@lem1508691) (@lem1508692 x)). Qed.
Lemma lem1508694 (x : real) : (term35 x) = (term48 x).
Proof. exact (TRANS (@lem1508681 x) (@lem1508693 x)). Qed.
Lemma lem1508695 (x : real) : (term48 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1508696 (x : real) : (term35 x) = x.
Proof. exact (TRANS (@lem1508694 x) (@lem1508695 x)). Qed.
Lemma lem1508697 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508698 (x : real) : (term74 x) = (real_add x).
Proof. exact (MK_COMB (@lem1508697) (@lem1508696 x)). Qed.
Lemma lem1508699 (x : real) (y : real) : (term73 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1508698 x) (@lem1508680 y)). Qed.
Lemma lem1508700 (x : real) (y : real) : (term72 x y) = (real_add x y).
Proof. exact (TRANS (@lem1508664 x y) (@lem1508699 x y)). Qed.
Lemma lem1508701 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1508702 (x : real) (y : real) : (term196 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1508701) (@lem1508700 x y)). Qed.
Lemma lem1508703 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508704 (x : real) (y : real) : ((term72 x y) = term22) = ((real_add x y) = term22).
Proof. exact (MK_COMB (@lem1508702 x y) (@lem1508703)). Qed.
Lemma lem1508705 (x : real) (y : real) (h1 : term190 x y) : (real_add x y) = term22.
Proof. exact (EQ_MP (@lem1508704 x y) (@lem1508663 x y h1)). Qed.
Lemma lem1508706 (x : real) (y : real) (h1 : term190 x y) : term197 x y.
Proof. exact (conj (@lem1508705 x y h1) (@lem1508656 x y h1)). Qed.
Lemma lem1508708 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1508709 (x : real) (y : real) : term198 x y.
Proof. exact (@lem1508708 (real_add x y) (term27 x y)). Qed.
Lemma lem1508710 (x : real) (y : real) (h1 : term190 x y) : term199 x y.
Proof. exact (@lem1508709 x y (@lem1508706 x y h1)). Qed.
Lemma lem1508711 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (@lem1483480 x (term23 x) y (term23 y)). Qed.
Lemma lem1508712 (x : real) : (term202 x) = (term177 x).
Proof. exact (@lem1483442 term37 x). Qed.
Lemma lem1508714 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508715 : term179 = term22.
Proof. exact (@lem1508714 term42). Qed.
Lemma lem1508716 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508717 : term180 = term181.
Proof. exact (MK_COMB (@lem1508716) (@lem1508715)). Qed.
Lemma lem1508718 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508719 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1508717) (@lem1508718 x)). Qed.
Lemma lem1508720 (x : real) : (term202 x) = (term182 x).
Proof. exact (TRANS (@lem1508712 x) (@lem1508719 x)). Qed.
Lemma lem1508721 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1508722 (x : real) : (term202 x) = term22.
Proof. exact (TRANS (@lem1508720 x) (@lem1508721 x)). Qed.
Lemma lem1508723 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508724 (x : real) : (term203 x) = term184.
Proof. exact (MK_COMB (@lem1508723) (@lem1508722 x)). Qed.
Lemma lem1508725 (y : real) : (term202 y) = (term177 y).
Proof. exact (@lem1483442 term37 y). Qed.
Lemma lem1508727 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508728 : term179 = term22.
Proof. exact (@lem1508727 term42). Qed.
Lemma lem1508729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508730 : term180 = term181.
Proof. exact (MK_COMB (@lem1508729) (@lem1508728)). Qed.
Lemma lem1508731 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508732 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1508730) (@lem1508731 y)). Qed.
Lemma lem1508733 (y : real) : (term202 y) = (term182 y).
Proof. exact (TRANS (@lem1508725 y) (@lem1508732 y)). Qed.
Lemma lem1508734 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1508735 (y : real) : (term202 y) = term22.
Proof. exact (TRANS (@lem1508733 y) (@lem1508734 y)). Qed.
Lemma lem1508736 (x : real) (y : real) : (term201 x y) = term185.
Proof. exact (MK_COMB (@lem1508724 x) (@lem1508735 y)). Qed.
Lemma lem1508737 (x : real) (y : real) : (term200 x y) = term185.
Proof. exact (TRANS (@lem1508711 x y) (@lem1508736 x y)). Qed.
Lemma lem1508738 : term185 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1508739 (x : real) (y : real) : (term200 x y) = term22.
Proof. exact (TRANS (@lem1508737 x y) (@lem1508738)). Qed.
Lemma lem1508740 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508741 (x : real) (y : real) : (term204 x y) = term187.
Proof. exact (MK_COMB (@lem1508740) (@lem1508739 x y)). Qed.
Lemma lem1508742 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508743 (x : real) (y : real) : (term199 x y) = term188.
Proof. exact (MK_COMB (@lem1508741 x y) (@lem1508742)). Qed.
Lemma lem1508744 (x : real) (y : real) (h1 : term190 x y) : term188.
Proof. exact (EQ_MP (@lem1508743 x y) (@lem1508710 x y h1)). Qed.
Lemma lem1508746 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508747 : term188 = term189.
Proof. exact (@lem1508746 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1508748 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1508749 : term188 = False.
Proof. exact (TRANS (@lem1508747) (@lem1508748)). Qed.
Lemma lem1508750 (x : real) (y : real) (h1 : term190 x y) : False.
Proof. exact (EQ_MP (@lem1508749) (@lem1508744 x y h1)). Qed.
Lemma lem1508751 (x : real) (y : real) (h1 : term147 x y) : False.
Proof. exact (or_elim (@lem1508550 x y h1) (fun h0 : term154 x y => @lem1508632 x y h0) (fun h0 : term190 x y => @lem1508750 x y h0)). Qed.
Lemma lem1508752 (x : real) (y : real) (h1 : term146 x y) : term146 x y.
Proof. exact (h1). Qed.
Lemma lem1508753 (x : real) (y : real) (h1 : term205 x y) : term205 x y.
Proof. exact (h1). Qed.
Lemma lem1508754 (x : real) (y : real) (h1 : term205 x y) : (real_add x y) = term22.
Proof. exact (proj2 (@lem1508753 x y h1)). Qed.
Lemma lem1508755 (x : real) (y : real) (h1 : term205 x y) : term56 x y.
Proof. exact (proj1 (@lem1508753 x y h1)). Qed.
Lemma lem1508757 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508758 : term156 = term157.
Proof. exact (@lem1508757 (NUMERAL 0) term42). Qed.
Lemma lem1508759 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1508760 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1508761 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1508760 h1) (fun h1 : term157 = True => @lem1508759)). Qed.
Lemma lem1508762 : term157 = True.
Proof. exact (EQ_MP (@lem1508761) (@lem1508759)). Qed.
Lemma lem1508763 : term156 = True.
Proof. exact (TRANS (@lem1508758) (@lem1508762)). Qed.
Lemma lem1508764 : True = term156.
Proof. exact (SYM (@lem1508763)). Qed.
Lemma lem1508765 : term156.
Proof. exact (EQ_MP (@lem1508764) (@lem0)). Qed.
Lemma lem1508766 (x : real) (y : real) (h1 : term205 x y) : term191 x y.
Proof. exact (conj (@lem1508765) (@lem1508755 x y h1)). Qed.
Lemma lem1508768 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1508769 (x : real) (y : real) : term192 x y.
Proof. exact (@lem1508768 term45 (term27 x y)). Qed.
Lemma lem1508770 (x : real) (y : real) (h1 : term205 x y) : term193 x y.
Proof. exact (@lem1508769 x y (@lem1508766 x y h1)). Qed.
Lemma lem1508771 (x : real) (y : real) : (term169 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1508772 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508773 (x : real) (y : real) : (term194 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1508772) (@lem1508771 x y)). Qed.
Lemma lem1508774 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508775 (x : real) (y : real) : (term193 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1508773 x y) (@lem1508774)). Qed.
Lemma lem1508776 (x : real) (y : real) (h1 : term205 x y) : term56 x y.
Proof. exact (EQ_MP (@lem1508775 x y) (@lem1508770 x y h1)). Qed.
Lemma lem1508778 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1508779 (x : real) (y : real) : term206 x y.
Proof. exact (@lem1508778 (real_add x y)). Qed.
Lemma lem1508780 (x : real) (y : real) (h1 : term205 x y) : term207 x y.
Proof. exact (@lem1508779 x y (@lem1508754 x y h1)). Qed.
Lemma lem1508781 (x : real) (y : real) (h1 : term205 x y) : term208 x y.
Proof. exact (@lem1508780 x y h1 term45). Qed.
Lemma lem1508782 (x : real) (y : real) : (term208 x y) = ((term163 x y) = term22).
Proof. exact (eq_refl (term208 x y)). Qed.
Lemma lem1508783 (x : real) (y : real) (h1 : term205 x y) : (term163 x y) = term22.
Proof. exact (EQ_MP (@lem1508782 x y) (@lem1508781 x y h1)). Qed.
Lemma lem1508784 (x : real) (y : real) : (term163 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1508785 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1508786 (x : real) (y : real) : (term209 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1508785) (@lem1508784 x y)). Qed.
Lemma lem1508787 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508788 (x : real) (y : real) : ((term163 x y) = term22) = ((real_add x y) = term22).
Proof. exact (MK_COMB (@lem1508786 x y) (@lem1508787)). Qed.
Lemma lem1508789 (x : real) (y : real) (h1 : term205 x y) : (real_add x y) = term22.
Proof. exact (EQ_MP (@lem1508788 x y) (@lem1508783 x y h1)). Qed.
Lemma lem1508790 (x : real) (y : real) (h1 : term205 x y) : term197 x y.
Proof. exact (conj (@lem1508789 x y h1) (@lem1508776 x y h1)). Qed.
Lemma lem1508792 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1508793 (x : real) (y : real) : term198 x y.
Proof. exact (@lem1508792 (real_add x y) (term27 x y)). Qed.
Lemma lem1508794 (x : real) (y : real) (h1 : term205 x y) : term199 x y.
Proof. exact (@lem1508793 x y (@lem1508790 x y h1)). Qed.
Lemma lem1508795 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (@lem1483480 x (term23 x) y (term23 y)). Qed.
Lemma lem1508796 (x : real) : (term202 x) = (term177 x).
Proof. exact (@lem1483442 term37 x). Qed.
Lemma lem1508798 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508799 : term179 = term22.
Proof. exact (@lem1508798 term42). Qed.
Lemma lem1508800 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508801 : term180 = term181.
Proof. exact (MK_COMB (@lem1508800) (@lem1508799)). Qed.
Lemma lem1508802 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508803 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1508801) (@lem1508802 x)). Qed.
Lemma lem1508804 (x : real) : (term202 x) = (term182 x).
Proof. exact (TRANS (@lem1508796 x) (@lem1508803 x)). Qed.
Lemma lem1508805 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1508806 (x : real) : (term202 x) = term22.
Proof. exact (TRANS (@lem1508804 x) (@lem1508805 x)). Qed.
Lemma lem1508807 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508808 (x : real) : (term203 x) = term184.
Proof. exact (MK_COMB (@lem1508807) (@lem1508806 x)). Qed.
Lemma lem1508809 (y : real) : (term202 y) = (term177 y).
Proof. exact (@lem1483442 term37 y). Qed.
Lemma lem1508811 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508812 : term179 = term22.
Proof. exact (@lem1508811 term42). Qed.
Lemma lem1508813 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508814 : term180 = term181.
Proof. exact (MK_COMB (@lem1508813) (@lem1508812)). Qed.
Lemma lem1508815 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508816 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1508814) (@lem1508815 y)). Qed.
Lemma lem1508817 (y : real) : (term202 y) = (term182 y).
Proof. exact (TRANS (@lem1508809 y) (@lem1508816 y)). Qed.
Lemma lem1508818 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1508819 (y : real) : (term202 y) = term22.
Proof. exact (TRANS (@lem1508817 y) (@lem1508818 y)). Qed.
Lemma lem1508820 (x : real) (y : real) : (term201 x y) = term185.
Proof. exact (MK_COMB (@lem1508808 x) (@lem1508819 y)). Qed.
Lemma lem1508821 (x : real) (y : real) : (term200 x y) = term185.
Proof. exact (TRANS (@lem1508795 x y) (@lem1508820 x y)). Qed.
Lemma lem1508822 : term185 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1508823 (x : real) (y : real) : (term200 x y) = term22.
Proof. exact (TRANS (@lem1508821 x y) (@lem1508822)). Qed.
Lemma lem1508824 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508825 (x : real) (y : real) : (term204 x y) = term187.
Proof. exact (MK_COMB (@lem1508824) (@lem1508823 x y)). Qed.
Lemma lem1508826 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508827 (x : real) (y : real) : (term199 x y) = term188.
Proof. exact (MK_COMB (@lem1508825 x y) (@lem1508826)). Qed.
Lemma lem1508828 (x : real) (y : real) (h1 : term205 x y) : term188.
Proof. exact (EQ_MP (@lem1508827 x y) (@lem1508794 x y h1)). Qed.
Lemma lem1508830 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508831 : term188 = term189.
Proof. exact (@lem1508830 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1508832 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1508833 : term188 = False.
Proof. exact (TRANS (@lem1508831) (@lem1508832)). Qed.
Lemma lem1508834 (x : real) (y : real) (h1 : term205 x y) : False.
Proof. exact (EQ_MP (@lem1508833) (@lem1508828 x y h1)). Qed.
Lemma lem1508835 (x : real) (y : real) (h1 : term210 x y) : term210 x y.
Proof. exact (h1). Qed.
Lemma lem1508836 (x : real) (y : real) (h1 : term210 x y) : (real_add x y) = term22.
Proof. exact (proj2 (@lem1508835 x y h1)). Qed.
Lemma lem1508837 (x : real) (y : real) (h1 : term210 x y) : term60 x y.
Proof. exact (proj1 (@lem1508835 x y h1)). Qed.
Lemma lem1508839 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508840 : term156 = term157.
Proof. exact (@lem1508839 (NUMERAL 0) term42). Qed.
Lemma lem1508841 : term158 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1508842 (h1 : term158 = (BIT1 0)) : term157 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1508843 : (term158 = (BIT1 0)) = (term157 = True).
Proof. exact (prop_ext (fun h1 : term158 = (BIT1 0) => @lem1508842 h1) (fun h1 : term157 = True => @lem1508841)). Qed.
Lemma lem1508844 : term157 = True.
Proof. exact (EQ_MP (@lem1508843) (@lem1508841)). Qed.
Lemma lem1508845 : term156 = True.
Proof. exact (TRANS (@lem1508840) (@lem1508844)). Qed.
Lemma lem1508846 : True = term156.
Proof. exact (SYM (@lem1508845)). Qed.
Lemma lem1508847 : term156.
Proof. exact (EQ_MP (@lem1508846) (@lem0)). Qed.
Lemma lem1508848 (x : real) (y : real) (h1 : term210 x y) : term159 x y.
Proof. exact (conj (@lem1508847) (@lem1508837 x y h1)). Qed.
Lemma lem1508850 (x : real) (y : real) : term160 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1508851 (x : real) (y : real) : term161 x y.
Proof. exact (@lem1508850 term45 (real_add x y)). Qed.
Lemma lem1508852 (x : real) (y : real) (h1 : term210 x y) : term162 x y.
Proof. exact (@lem1508851 x y (@lem1508848 x y h1)). Qed.
Lemma lem1508853 (x : real) (y : real) : (term163 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1508854 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508855 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1508854) (@lem1508853 x y)). Qed.
Lemma lem1508856 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508857 (x : real) (y : real) : (term162 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1508855 x y) (@lem1508856)). Qed.
Lemma lem1508858 (x : real) (y : real) (h1 : term210 x y) : term60 x y.
Proof. exact (EQ_MP (@lem1508857 x y) (@lem1508852 x y h1)). Qed.
Lemma lem1508860 (y : real) : term165 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1508861 (x : real) (y : real) : term206 x y.
Proof. exact (@lem1508860 (real_add x y)). Qed.
Lemma lem1508862 (x : real) (y : real) (h1 : term210 x y) : term207 x y.
Proof. exact (@lem1508861 x y (@lem1508836 x y h1)). Qed.
Lemma lem1508863 (x : real) (y : real) (h1 : term210 x y) : term211 x y.
Proof. exact (@lem1508862 x y h1 term37). Qed.
Lemma lem1508864 (x : real) (y : real) : (term211 x y) = ((term51 x y) = term22).
Proof. exact (eq_refl (term211 x y)). Qed.
Lemma lem1508865 (x : real) (y : real) (h1 : term210 x y) : (term51 x y) = term22.
Proof. exact (EQ_MP (@lem1508864 x y) (@lem1508863 x y h1)). Qed.
Lemma lem1508872 (x : real) (y : real) : (term51 x y) = (term27 x y).
Proof. exact (@lem1483508 x term37 y). Qed.
Lemma lem1508873 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1508874 (x : real) (y : real) : (term212 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1508873) (@lem1508872 x y)). Qed.
Lemma lem1508875 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508876 (x : real) (y : real) : ((term51 x y) = term22) = ((term27 x y) = term22).
Proof. exact (MK_COMB (@lem1508874 x y) (@lem1508875)). Qed.
Lemma lem1508877 (x : real) (y : real) (h1 : term210 x y) : (term27 x y) = term22.
Proof. exact (EQ_MP (@lem1508876 x y) (@lem1508865 x y h1)). Qed.
Lemma lem1508878 (x : real) (y : real) (h1 : term210 x y) : term154 x y.
Proof. exact (conj (@lem1508877 x y h1) (@lem1508858 x y h1)). Qed.
Lemma lem1508880 (x : real) (y : real) : term171 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1508881 (x : real) (y : real) : term172 x y.
Proof. exact (@lem1508880 (term27 x y) (real_add x y)). Qed.
Lemma lem1508882 (x : real) (y : real) (h1 : term210 x y) : term173 x y.
Proof. exact (@lem1508881 x y (@lem1508878 x y h1)). Qed.
Lemma lem1508883 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483480 (term23 x) x (term23 y) y). Qed.
Lemma lem1508884 (x : real) : (term176 x) = (term177 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1508886 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508887 : term179 = term22.
Proof. exact (@lem1508886 term42). Qed.
Lemma lem1508888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508889 : term180 = term181.
Proof. exact (MK_COMB (@lem1508888) (@lem1508887)). Qed.
Lemma lem1508890 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1508891 (x : real) : (term177 x) = (term182 x).
Proof. exact (MK_COMB (@lem1508889) (@lem1508890 x)). Qed.
Lemma lem1508892 (x : real) : (term176 x) = (term182 x).
Proof. exact (TRANS (@lem1508884 x) (@lem1508891 x)). Qed.
Lemma lem1508893 (x : real) : (term182 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1508894 (x : real) : (term176 x) = term22.
Proof. exact (TRANS (@lem1508892 x) (@lem1508893 x)). Qed.
Lemma lem1508895 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1508896 (x : real) : (term183 x) = term184.
Proof. exact (MK_COMB (@lem1508895) (@lem1508894 x)). Qed.
Lemma lem1508897 (y : real) : (term176 y) = (term177 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1508899 (m : nat) : (term178 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1508900 : term179 = term22.
Proof. exact (@lem1508899 term42). Qed.
Lemma lem1508901 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1508902 : term180 = term181.
Proof. exact (MK_COMB (@lem1508901) (@lem1508900)). Qed.
Lemma lem1508903 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1508904 (y : real) : (term177 y) = (term182 y).
Proof. exact (MK_COMB (@lem1508902) (@lem1508903 y)). Qed.
Lemma lem1508905 (y : real) : (term176 y) = (term182 y).
Proof. exact (TRANS (@lem1508897 y) (@lem1508904 y)). Qed.
Lemma lem1508906 (y : real) : (term182 y) = term22.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1508907 (y : real) : (term176 y) = term22.
Proof. exact (TRANS (@lem1508905 y) (@lem1508906 y)). Qed.
Lemma lem1508908 (x : real) (y : real) : (term175 x y) = term185.
Proof. exact (MK_COMB (@lem1508896 x) (@lem1508907 y)). Qed.
Lemma lem1508909 (x : real) (y : real) : (term174 x y) = term185.
Proof. exact (TRANS (@lem1508883 x y) (@lem1508908 x y)). Qed.
Lemma lem1508910 : term185 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1508911 (x : real) (y : real) : (term174 x y) = term22.
Proof. exact (TRANS (@lem1508909 x y) (@lem1508910)). Qed.
Lemma lem1508912 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1508913 (x : real) (y : real) : (term186 x y) = term187.
Proof. exact (MK_COMB (@lem1508912) (@lem1508911 x y)). Qed.
Lemma lem1508914 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1508915 (x : real) (y : real) : (term173 x y) = term188.
Proof. exact (MK_COMB (@lem1508913 x y) (@lem1508914)). Qed.
Lemma lem1508916 (x : real) (y : real) (h1 : term210 x y) : term188.
Proof. exact (EQ_MP (@lem1508915 x y) (@lem1508882 x y h1)). Qed.
Lemma lem1508918 (n : nat) (m : nat) : (term155 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1508919 : term188 = term189.
Proof. exact (@lem1508918 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1508920 : term189 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1508921 : term188 = False.
Proof. exact (TRANS (@lem1508919) (@lem1508920)). Qed.
Lemma lem1508922 (x : real) (y : real) (h1 : term210 x y) : False.
Proof. exact (EQ_MP (@lem1508921) (@lem1508916 x y h1)). Qed.
Lemma lem1508923 (x : real) (y : real) (h1 : term146 x y) : False.
Proof. exact (or_elim (@lem1508752 x y h1) (fun h0 : term205 x y => @lem1508834 x y h0) (fun h0 : term210 x y => @lem1508922 x y h0)). Qed.
Lemma lem1508924 (x : real) (y : real) (h1 : term149 x y) : False.
Proof. exact (or_elim (@lem1508549 x y h1) (fun h0 : term147 x y => @lem1508751 x y h0) (fun h0 : term146 x y => @lem1508923 x y h0)). Qed.
Lemma lem1508926 (x : real) (y : real) (h1 : term149 x y) : term149 x y.
Proof. exact (h1). Qed.
Lemma lem1508927 (x : real) (y : real) (h1 : term149 x y) : (term149 x y) = False.
Proof. exact (prop_ext (fun h2 : term149 x y => @lem1508924 x y h1) (fun h2 : False => @lem1508926 x y h1)). Qed.
Lemma lem1508928 (x : real) (y : real) (h1 : term149 x y) : False.
Proof. exact (EQ_MP (@lem1508927 x y h1) (@lem1508926 x y h1)). Qed.
Lemma lem1508929 (x : real) (h1 : term151 x) : term151 x.
Proof. exact (h1). Qed.
Lemma lem1508930 (x : real) (h1 : term151 x) : False.
Proof. exact (ex_elim (@lem1508929 x h1) (fun y : real => fun h0 : term150 x y => @lem1508928 x y h0)). Qed.
Lemma lem1508931 (h1 : term153) : term153.
Proof. exact (h1). Qed.
Lemma lem1508932 (h1 : term153) : False.
Proof. exact (ex_elim (@lem1508931 h1) (fun x : real => fun h0 : term152 x => @lem1508930 x h0)). Qed.
Lemma lem1508933 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1508934 (h1 : term12) : term153.
Proof. exact (EQ_MP (@lem1508527) (@lem1508933 h1)). Qed.
Lemma lem1508935 (h1 : term12) : term153 = False.
Proof. exact (prop_ext (fun h2 : term153 => @lem1508932 h2) (fun h2 : False => @lem1508934 h1)). Qed.
Lemma lem1508936 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1508935 h1) (@lem1508934 h1)). Qed.
Lemma lem1508937 : term213.
Proof. exact (fun h0 : term12 => @lem1508936 h0). Qed.
Lemma lem1508938 : term214.
Proof. exact (@lem1386578 term215). Qed.
Lemma lem1508939 : term215.
Proof. exact (@lem1508938 (@lem1508937)). Qed.

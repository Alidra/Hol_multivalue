Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_SYM_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482709_spec.
Require Import thm1482710_spec.
Require Import thm1483205_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
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
Lemma lem1557946 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557947 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1557946 (term4 x)). Qed.
Lemma lem1557948 (y : real) (x : real) : (term5 x y) = ((real_max x y) = (real_max y x)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1557949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557951 (y : real) (x : real) : (term6 x y) = (term7 y x).
Proof. exact (MK_COMB (@lem1557949) (@lem1557948 y x)). Qed.
Lemma lem1557952 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1557951 y x)). Qed.
Lemma lem1557953 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557954 (x : real) : (term3 x) = (term10 x).
Proof. exact (MK_COMB (@lem1557953) (@lem1557952 x)). Qed.
Lemma lem1557955 (x : real) : (term2 x) = (term10 x).
Proof. exact (TRANS (@lem1557947 x) (@lem1557954 x)). Qed.
Lemma lem1557956 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557957 : term11 = term12.
Proof. exact (@lem1557956 term13). Qed.
Lemma lem1557958 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1557959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557960 (x : real) : (term16 x) = (term2 x).
Proof. exact (MK_COMB (@lem1557959) (@lem1557958 x)). Qed.
Lemma lem1557961 (x : real) : (term16 x) = (term10 x).
Proof. exact (TRANS (@lem1557960 x) (@lem1557955 x)). Qed.
Lemma lem1557962 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1557961 x)). Qed.
Lemma lem1557963 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557964 : term12 = term19.
Proof. exact (MK_COMB (@lem1557963) (@lem1557962)). Qed.
Lemma lem1557966 : term11 = term19.
Proof. exact (TRANS (@lem1557957) (@lem1557964)). Qed.
Lemma lem1557969 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1557970 (x : real) : (term9 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1557969 y x)). Qed.
Lemma lem1557971 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557972 (x : real) : (term10 x) = (term10 x).
Proof. exact (MK_COMB (@lem1557971) (@lem1557970 x)). Qed.
Lemma lem1557973 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1557972 x)). Qed.
Lemma lem1557974 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557975 : term19 = term19.
Proof. exact (MK_COMB (@lem1557974) (@lem1557973)). Qed.
Lemma lem1557976 : term11 = term19.
Proof. exact (TRANS (@lem1557966) (@lem1557975)). Qed.
Lemma lem1557977 (y : real) (x : real) : (term7 y x) = (term20 y x).
Proof. exact (@lem1483554 (real_max x y) (real_max y x)). Qed.
Lemma lem1557990 (y : real) (x : real) : (term21 y x) = (term22 y x).
Proof. exact (@lem1483519 (real_max x y) (real_max y x)). Qed.
Lemma lem1557991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1557992 (y : real) (x : real) : (term23 y x) = (term24 y x).
Proof. exact (MK_COMB (@lem1557991) (@lem1557990 y x)). Qed.
Lemma lem1557993 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (@lem1483512 (term22 y x)). Qed.
Lemma lem1557994 (y : real) (x : real) : (term25 y x) = (term26 y x).
Proof. exact (@lem1483508 (real_max x y) term27 (term28 y x)). Qed.
Lemma lem1557995 (y : real) (x : real) : (term29 y x) = (term30 y x).
Proof. exact (@lem1483476 term27 term27 (real_max y x)). Qed.
Lemma lem1557997 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1557998 : term33 = term34.
Proof. exact (@lem1557997 term35 term35). Qed.
Lemma lem1557999 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1558000 : term37 = term35.
Proof. exact (EQ_MP (@lem1557999) (@lem940073)). Qed.
Lemma lem1558001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1558002 : term34 = term38.
Proof. exact (MK_COMB (@lem1558001) (@lem1558000)). Qed.
Lemma lem1558003 : term33 = term38.
Proof. exact (TRANS (@lem1557998) (@lem1558002)). Qed.
Lemma lem1558004 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1558005 : term39 = term40.
Proof. exact (MK_COMB (@lem1558004) (@lem1558003)). Qed.
Lemma lem1558006 (y : real) (x : real) : (real_max y x) = (real_max y x).
Proof. exact (eq_refl (real_max y x)). Qed.
Lemma lem1558007 (y : real) (x : real) : (term30 y x) = (term41 y x).
Proof. exact (MK_COMB (@lem1558005) (@lem1558006 y x)). Qed.
Lemma lem1558008 (y : real) (x : real) : (term29 y x) = (term41 y x).
Proof. exact (TRANS (@lem1557995 y x) (@lem1558007 y x)). Qed.
Lemma lem1558009 (y : real) (x : real) : (term41 y x) = (real_max y x).
Proof. exact (@lem1483436 (real_max y x)). Qed.
Lemma lem1558010 (y : real) (x : real) : (term29 y x) = (real_max y x).
Proof. exact (TRANS (@lem1558008 y x) (@lem1558009 y x)). Qed.
Lemma lem1558013 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1558014 (y : real) (x : real) : (term26 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem1558013 x y) (@lem1558010 y x)). Qed.
Lemma lem1558015 (y : real) (x : real) : (term25 y x) = (term43 y x).
Proof. exact (TRANS (@lem1557994 y x) (@lem1558014 y x)). Qed.
Lemma lem1558016 (y : real) (x : real) : (term24 y x) = (term43 y x).
Proof. exact (TRANS (@lem1557993 y x) (@lem1558015 y x)). Qed.
Lemma lem1558017 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (eq_refl (term44 y x)). Qed.
Lemma lem1558018 (y : real) (x : real) : ((term23 y x) = (term24 y x)) = ((term23 y x) = (term43 y x)).
Proof. exact (MK_COMB (@lem1558017 y x) (@lem1558016 y x)). Qed.
Lemma lem1558019 (y : real) (x : real) : (term23 y x) = (term43 y x).
Proof. exact (EQ_MP (@lem1558018 y x) (@lem1557992 y x)). Qed.
Lemma lem1558020 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558021 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1558020) (@lem1558019 y x)). Qed.
Lemma lem1558022 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558023 (y : real) (x : real) : (term48 y x) = (term49 y x).
Proof. exact (MK_COMB (@lem1558021 y x) (@lem1558022)). Qed.
Lemma lem1558024 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558025 (y : real) (x : real) : (term50 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1558024) (@lem1557990 y x)). Qed.
Lemma lem1558026 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558027 (y : real) (x : real) : (term52 y x) = (term53 y x).
Proof. exact (MK_COMB (@lem1558025 y x) (@lem1558026)). Qed.
Lemma lem1558028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558029 (y : real) (x : real) : (term54 y x) = (term55 y x).
Proof. exact (MK_COMB (@lem1558028) (@lem1558027 y x)). Qed.
Lemma lem1558030 (y : real) (x : real) : (term20 y x) = (term56 y x).
Proof. exact (MK_COMB (@lem1558029 y x) (@lem1558023 y x)). Qed.
Lemma lem1558031 (y : real) (x : real) : (term7 y x) = (term56 y x).
Proof. exact (TRANS (@lem1557977 y x) (@lem1558030 y x)). Qed.
Lemma lem1558032 (x : real) : (term9 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558031 y x)). Qed.
Lemma lem1558033 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558034 (x : real) : (term10 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558033) (@lem1558032 x)). Qed.
Lemma lem1558035 : term18 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558034 x)). Qed.
Lemma lem1558036 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558037 : term19 = term60.
Proof. exact (MK_COMB (@lem1558036) (@lem1558035)). Qed.
Lemma lem1558038 : term11 = term60.
Proof. exact (TRANS (@lem1557976) (@lem1558037)). Qed.
Lemma lem1558044 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1558045 (P : real -> Prop) (Q : real -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem1558044 real P Q). Qed.
Lemma lem1558046 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1558045 (term67 x) (term68 x)). Qed.
Lemma lem1558047 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558049 (y : real) (x : real) : (term70 x y) = (term55 y x).
Proof. exact (MK_COMB (@lem1558048) (@lem1558047 y x)). Qed.
Lemma lem1558050 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558051 (y : real) (x : real) : (term72 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1558049 y x) (@lem1558050 y x)). Qed.
Lemma lem1558052 (x : real) : (term73 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558051 y x)). Qed.
Lemma lem1558053 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558054 (x : real) : (term65 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558053) (@lem1558052 x)). Qed.
Lemma lem1558055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558056 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1558055) (@lem1558054 x)). Qed.
Lemma lem1558057 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558058 (x : real) : (term76 x) = (term67 x).
Proof. exact (fun_ext (fun y : real => @lem1558057 y x)). Qed.
Lemma lem1558059 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558060 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1558059) (@lem1558058 x)). Qed.
Lemma lem1558061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558062 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558061) (@lem1558060 x)). Qed.
Lemma lem1558063 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558064 (x : real) : (term81 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1558063 y x)). Qed.
Lemma lem1558065 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558066 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1558065) (@lem1558064 x)). Qed.
Lemma lem1558067 (x : real) : (term66 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558062 x) (@lem1558066 x)). Qed.
Lemma lem1558068 (x : real) : ((term65 x) = (term66 x)) = ((term58 x) = (term84 x)).
Proof. exact (MK_COMB (@lem1558056 x) (@lem1558067 x)). Qed.
Lemma lem1558069 (x : real) : (term58 x) = (term84 x).
Proof. exact (EQ_MP (@lem1558068 x) (@lem1558046 x)). Qed.
Lemma lem1558078 : term59 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558069 x)). Qed.
Lemma lem1558079 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558080 : term60 = term86.
Proof. exact (MK_COMB (@lem1558079) (@lem1558078)). Qed.
Lemma lem1558082 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term61 A P Q) = (term62 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1558083 (P : real -> Prop) (Q : real -> Prop) : (term63 P Q) = (term64 P Q).
Proof. exact (@lem1558082 real P Q). Qed.
Lemma lem1558084 : term87 = term88.
Proof. exact (@lem1558083 term89 term90). Qed.
Lemma lem1558085 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558087 (x : real) : (term92 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558086) (@lem1558085 x)). Qed.
Lemma lem1558088 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558089 (x : real) : (term94 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558087 x) (@lem1558088 x)). Qed.
Lemma lem1558090 : term95 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558089 x)). Qed.
Lemma lem1558091 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558092 : term87 = term86.
Proof. exact (MK_COMB (@lem1558091) (@lem1558090)). Qed.
Lemma lem1558093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558094 : term96 = term97.
Proof. exact (MK_COMB (@lem1558093) (@lem1558092)). Qed.
Lemma lem1558095 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558096 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1558095 x)). Qed.
Lemma lem1558097 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558098 : term99 = term100.
Proof. exact (MK_COMB (@lem1558097) (@lem1558096)). Qed.
Lemma lem1558099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558100 : term101 = term102.
Proof. exact (MK_COMB (@lem1558099) (@lem1558098)). Qed.
Lemma lem1558101 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558102 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1558101 x)). Qed.
Lemma lem1558103 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558104 : term104 = term105.
Proof. exact (MK_COMB (@lem1558103) (@lem1558102)). Qed.
Lemma lem1558105 : term88 = term106.
Proof. exact (MK_COMB (@lem1558100) (@lem1558104)). Qed.
Lemma lem1558106 : (term87 = term88) = (term86 = term106).
Proof. exact (MK_COMB (@lem1558094) (@lem1558105)). Qed.
Lemma lem1558107 : term86 = term106.
Proof. exact (EQ_MP (@lem1558106) (@lem1558084)). Qed.
Lemma lem1558124 : term60 = term106.
Proof. exact (TRANS (@lem1558080) (@lem1558107)). Qed.
Lemma lem1558126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1558127 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term63 P Q).
Proof. exact (@lem1558126 real P Q). Qed.
Lemma lem1558128 : term88 = term87.
Proof. exact (@lem1558127 term89 term90). Qed.
Lemma lem1558129 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558130 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1558129 x)). Qed.
Lemma lem1558131 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558132 : term99 = term100.
Proof. exact (MK_COMB (@lem1558131) (@lem1558130)). Qed.
Lemma lem1558133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558134 : term101 = term102.
Proof. exact (MK_COMB (@lem1558133) (@lem1558132)). Qed.
Lemma lem1558135 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558136 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1558135 x)). Qed.
Lemma lem1558137 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558138 : term104 = term105.
Proof. exact (MK_COMB (@lem1558137) (@lem1558136)). Qed.
Lemma lem1558139 : term88 = term106.
Proof. exact (MK_COMB (@lem1558134) (@lem1558138)). Qed.
Lemma lem1558140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558141 : term107 = term108.
Proof. exact (MK_COMB (@lem1558140) (@lem1558139)). Qed.
Lemma lem1558142 (x : real) : (term91 x) = (term78 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1558143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558144 (x : real) : (term92 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558143) (@lem1558142 x)). Qed.
Lemma lem1558145 (x : real) : (term93 x) = (term83 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1558146 (x : real) : (term94 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558144 x) (@lem1558145 x)). Qed.
Lemma lem1558147 : term95 = term85.
Proof. exact (fun_ext (fun x : real => @lem1558146 x)). Qed.
Lemma lem1558148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558149 : term87 = term86.
Proof. exact (MK_COMB (@lem1558148) (@lem1558147)). Qed.
Lemma lem1558150 : (term88 = term87) = (term106 = term86).
Proof. exact (MK_COMB (@lem1558141) (@lem1558149)). Qed.
Lemma lem1558151 : term106 = term86.
Proof. exact (EQ_MP (@lem1558150) (@lem1558128)). Qed.
Lemma lem1558153 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term62 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1558154 (P : real -> Prop) (Q : real -> Prop) : (term64 P Q) = (term63 P Q).
Proof. exact (@lem1558153 real P Q). Qed.
Lemma lem1558155 (x : real) : (term66 x) = (term65 x).
Proof. exact (@lem1558154 (term67 x) (term68 x)). Qed.
Lemma lem1558156 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558157 (x : real) : (term76 x) = (term67 x).
Proof. exact (fun_ext (fun y : real => @lem1558156 y x)). Qed.
Lemma lem1558158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558159 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1558158) (@lem1558157 x)). Qed.
Lemma lem1558160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558161 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1558160) (@lem1558159 x)). Qed.
Lemma lem1558162 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558163 (x : real) : (term81 x) = (term68 x).
Proof. exact (fun_ext (fun y : real => @lem1558162 y x)). Qed.
Lemma lem1558164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558165 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1558164) (@lem1558163 x)). Qed.
Lemma lem1558166 (x : real) : (term66 x) = (term84 x).
Proof. exact (MK_COMB (@lem1558161 x) (@lem1558165 x)). Qed.
Lemma lem1558167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1558168 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1558167) (@lem1558166 x)). Qed.
Lemma lem1558169 (y : real) (x : real) : (term69 x y) = (term53 y x).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1558170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558171 (y : real) (x : real) : (term70 x y) = (term55 y x).
Proof. exact (MK_COMB (@lem1558170) (@lem1558169 y x)). Qed.
Lemma lem1558172 (y : real) (x : real) : (term71 x y) = (term49 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1558173 (y : real) (x : real) : (term72 x y) = (term56 y x).
Proof. exact (MK_COMB (@lem1558171 y x) (@lem1558172 y x)). Qed.
Lemma lem1558174 (x : real) : (term73 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558173 y x)). Qed.
Lemma lem1558175 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558176 (x : real) : (term65 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558175) (@lem1558174 x)). Qed.
Lemma lem1558177 (x : real) : ((term66 x) = (term65 x)) = ((term84 x) = (term58 x)).
Proof. exact (MK_COMB (@lem1558168 x) (@lem1558176 x)). Qed.
Lemma lem1558178 (x : real) : (term84 x) = (term58 x).
Proof. exact (EQ_MP (@lem1558177 x) (@lem1558155 x)). Qed.
Lemma lem1558179 : term85 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558178 x)). Qed.
Lemma lem1558180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558181 : term86 = term60.
Proof. exact (MK_COMB (@lem1558180) (@lem1558179)). Qed.
Lemma lem1558182 : term106 = term60.
Proof. exact (TRANS (@lem1558151) (@lem1558181)). Qed.
Lemma lem1558183 : term60 = term60.
Proof. exact (TRANS (@lem1558124) (@lem1558182)). Qed.
Lemma lem1558186 : term11 = term60.
Proof. exact (TRANS (@lem1558038) (@lem1558183)). Qed.
Lemma lem1558191 (y : real) (x : real) : (term56 y x) = (term56 y x).
Proof. exact (eq_refl (term56 y x)). Qed.
Lemma lem1558192 (x : real) : (term57 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1558191 y x)). Qed.
Lemma lem1558193 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558194 (x : real) : (term58 x) = (term58 x).
Proof. exact (MK_COMB (@lem1558193) (@lem1558192 x)). Qed.
Lemma lem1558195 : term59 = term59.
Proof. exact (fun_ext (fun x : real => @lem1558194 x)). Qed.
Lemma lem1558196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1558197 : term60 = term60.
Proof. exact (MK_COMB (@lem1558196) (@lem1558195)). Qed.
Lemma lem1558198 : term11 = term60.
Proof. exact (TRANS (@lem1558186) (@lem1558197)). Qed.
Lemma lem1558200 (x : real) (a : real) (y : real) (r : real) : (term111 a x y r) = (term112 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1558201 (y : real) (x : real) : (term53 y x) = (term113 y x).
Proof. exact (@lem1558200 y (real_max x y) x term47). Qed.
Lemma lem1558214 (x : real) (y : real) : (term114 y x) = (term115 x y).
Proof. exact (@lem1483488 (term116 x) (real_max x y)). Qed.
Lemma lem1558215 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558216 (x : real) (y : real) : (term117 y x) = (term118 x y).
Proof. exact (MK_COMB (@lem1558215) (@lem1558214 x y)). Qed.
Lemma lem1558217 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558218 (x : real) (y : real) : (term119 y x) = (term120 x y).
Proof. exact (MK_COMB (@lem1558216 x y) (@lem1558217)). Qed.
Lemma lem1558231 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (@lem1483488 (term116 y) (real_max x y)). Qed.
Lemma lem1558232 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558233 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1558232) (@lem1558231 x y)). Qed.
Lemma lem1558234 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558235 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1558233 x y) (@lem1558234)). Qed.
Lemma lem1558236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558237 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1558236) (@lem1558235 x y)). Qed.
Lemma lem1558238 (x : real) (y : real) : (term113 y x) = (term129 x y).
Proof. exact (MK_COMB (@lem1558237 x y) (@lem1558218 x y)). Qed.
Lemma lem1558239 (x : real) (y : real) : (term53 y x) = (term129 x y).
Proof. exact (TRANS (@lem1558201 y x) (@lem1558238 x y)). Qed.
Lemma lem1558240 (x : real) (y : real) : (term130 x y) = (term129 x y).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem1558241 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (SYM (@lem1558240 x y)). Qed.
Lemma lem1558242 (y : real) (x : real) : (term130 x y) = (term131 y x).
Proof. exact (@lem1483205 y (term132 y x) x). Qed.
Lemma lem1558243 (y : real) (x : real) : (term129 x y) = (term131 y x).
Proof. exact (TRANS (@lem1558241 x y) (@lem1558242 y x)). Qed.
Lemma lem1558244 (y : real) (x : real) : (term133 y x) = (term134 y x).
Proof. exact (eq_refl (term133 y x)). Qed.
Lemma lem1558245 (x : real) (y : real) : (term135 x y) = (term135 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1558246 (y : real) (x : real) : (term136 y x) = (term137 y x).
Proof. exact (MK_COMB (@lem1558245 x y) (@lem1558244 y x)). Qed.
Lemma lem1558247 (x : real) (y : real) : (term138 x y) = (term139 x y).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1558248 (y : real) (x : real) : (term140 y x) = (term140 y x).
Proof. exact (eq_refl (term140 y x)). Qed.
Lemma lem1558249 (x : real) (y : real) : (term141 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem1558248 y x) (@lem1558247 x y)). Qed.
Lemma lem1558250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558251 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (MK_COMB (@lem1558250) (@lem1558249 x y)). Qed.
Lemma lem1558252 (y : real) (x : real) : (term131 y x) = (term145 y x).
Proof. exact (MK_COMB (@lem1558251 x y) (@lem1558246 y x)). Qed.
Lemma lem1558253 (x : real) (y : real) : (term146 x y) = (term146 x y).
Proof. exact (eq_refl (term146 x y)). Qed.
Lemma lem1558254 (y : real) (x : real) : ((term129 x y) = (term131 y x)) = ((term129 x y) = (term145 y x)).
Proof. exact (MK_COMB (@lem1558253 x y) (@lem1558252 y x)). Qed.
Lemma lem1558255 (y : real) (x : real) : (term129 x y) = (term145 y x).
Proof. exact (EQ_MP (@lem1558254 y x) (@lem1558243 y x)). Qed.
Lemma lem1558256 (y : real) (x : real) : (real_ge y x) = (term147 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1558262 (y : real) (x : real) : (real_sub y x) = (term148 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1558267 (x : real) (y : real) : (term148 y x) = (term149 x y).
Proof. exact (@lem1483488 (term116 x) y). Qed.
Lemma lem1558269 (x : real) (y : real) : (real_sub y x) = (term149 x y).
Proof. exact (TRANS (@lem1558262 y x) (@lem1558267 x y)). Qed.
Lemma lem1558270 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1558271 (x : real) (y : real) : (term150 y x) = (term151 x y).
Proof. exact (MK_COMB (@lem1558270) (@lem1558269 x y)). Qed.
Lemma lem1558272 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558273 (x : real) (y : real) : (term147 y x) = (term152 x y).
Proof. exact (MK_COMB (@lem1558271 x y) (@lem1558272)). Qed.
Lemma lem1558274 (x : real) (y : real) : (real_ge y x) = (term152 x y).
Proof. exact (TRANS (@lem1558256 y x) (@lem1558273 x y)). Qed.
Lemma lem1558275 (y : real) : (term153 y) = (term154 y).
Proof. exact (@lem1483525 (term155 y) term47). Qed.
Lemma lem1558276 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558288 (y : real) : (term155 y) = (term156 y).
Proof. exact (@lem1483440 term27 y). Qed.
Lemma lem1558290 (m : nat) : (term157 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1558291 : term158 = term47.
Proof. exact (@lem1558290 term35). Qed.
Lemma lem1558292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1558293 : term159 = term160.
Proof. exact (MK_COMB (@lem1558292) (@lem1558291)). Qed.
Lemma lem1558294 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1558295 (y : real) : (term156 y) = (term161 y).
Proof. exact (MK_COMB (@lem1558293) (@lem1558294 y)). Qed.
Lemma lem1558296 (y : real) : (term155 y) = (term161 y).
Proof. exact (TRANS (@lem1558288 y) (@lem1558295 y)). Qed.
Lemma lem1558297 (y : real) : (term161 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1558299 (y : real) : (term155 y) = term47.
Proof. exact (TRANS (@lem1558296 y) (@lem1558297 y)). Qed.
Lemma lem1558300 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1558301 (y : real) : (term162 y) = term163.
Proof. exact (MK_COMB (@lem1558300) (@lem1558299 y)). Qed.
Lemma lem1558302 (y : real) : (term164 y) = term165.
Proof. exact (MK_COMB (@lem1558301 y) (@lem1558276)). Qed.
Lemma lem1558303 : term165 = term166.
Proof. exact (@lem1483519 term47 term47). Qed.
Lemma lem1558305 (x : nat) : (term167 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1558306 : term168 = term47.
Proof. exact (@lem1558305 term35). Qed.
Lemma lem1558307 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1558308 : term166 = term170.
Proof. exact (MK_COMB (@lem1558307) (@lem1558306)). Qed.
Lemma lem1558309 : term170 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1558310 : term166 = term47.
Proof. exact (TRANS (@lem1558308) (@lem1558309)). Qed.
Lemma lem1558311 : term165 = term47.
Proof. exact (TRANS (@lem1558303) (@lem1558310)). Qed.
Lemma lem1558312 (y : real) : (term164 y) = term47.
Proof. exact (TRANS (@lem1558302 y) (@lem1558311)). Qed.
Lemma lem1558313 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558314 (y : real) : (term171 y) = term172.
Proof. exact (MK_COMB (@lem1558313) (@lem1558312 y)). Qed.
Lemma lem1558315 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558316 (y : real) : (term154 y) = term173.
Proof. exact (MK_COMB (@lem1558314 y) (@lem1558315)). Qed.
Lemma lem1558317 (y : real) : (term153 y) = term173.
Proof. exact (TRANS (@lem1558275 y) (@lem1558316 y)). Qed.
Lemma lem1558318 (x : real) (y : real) : (term174 x y) = (term175 x y).
Proof. exact (@lem1483525 (term149 x y) term47). Qed.
Lemma lem1558336 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (@lem1483519 (term149 x y) term47). Qed.
Lemma lem1558338 (x : nat) : (term167 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1558339 : term168 = term47.
Proof. exact (@lem1558338 term35). Qed.
Lemma lem1558340 (x : real) (y : real) : (term178 x y) = (term178 x y).
Proof. exact (eq_refl (term178 x y)). Qed.
Lemma lem1558341 (x : real) (y : real) : (term177 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1558340 x y) (@lem1558339)). Qed.
Lemma lem1558342 (x : real) (y : real) : (term179 x y) = (term149 x y).
Proof. exact (@lem1483450 (term149 x y)). Qed.
Lemma lem1558343 (x : real) (y : real) : (term177 x y) = (term149 x y).
Proof. exact (TRANS (@lem1558341 x y) (@lem1558342 x y)). Qed.
Lemma lem1558345 (x : real) (y : real) : (term176 x y) = (term149 x y).
Proof. exact (TRANS (@lem1558336 x y) (@lem1558343 x y)). Qed.
Lemma lem1558346 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558347 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1558346) (@lem1558345 x y)). Qed.
Lemma lem1558348 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558349 (x : real) (y : real) : (term175 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1558347 x y) (@lem1558348)). Qed.
Lemma lem1558350 (x : real) (y : real) : (term174 x y) = (term174 x y).
Proof. exact (TRANS (@lem1558318 x y) (@lem1558349 x y)). Qed.
Lemma lem1558351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558352 (y : real) : (term182 y) = term183.
Proof. exact (MK_COMB (@lem1558351) (@lem1558317 y)). Qed.
Lemma lem1558353 (x : real) (y : real) : (term139 x y) = (term184 x y).
Proof. exact (MK_COMB (@lem1558352 y) (@lem1558350 x y)). Qed.
Lemma lem1558354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558355 (x : real) (y : real) : (term140 y x) = (term185 x y).
Proof. exact (MK_COMB (@lem1558354) (@lem1558274 x y)). Qed.
Lemma lem1558356 (x : real) (y : real) : (term142 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1558355 x y) (@lem1558353 x y)). Qed.
Lemma lem1558357 (x : real) (y : real) : (real_gt x y) = (term187 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1558370 (x : real) (y : real) : (real_sub x y) = (term148 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1558371 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558372 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem1558371) (@lem1558370 x y)). Qed.
Lemma lem1558373 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558374 (x : real) (y : real) : (term187 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1558372 x y) (@lem1558373)). Qed.
Lemma lem1558375 (x : real) (y : real) : (real_gt x y) = (term190 x y).
Proof. exact (TRANS (@lem1558357 x y) (@lem1558374 x y)). Qed.
Lemma lem1558376 (y : real) (x : real) : (term174 y x) = (term175 y x).
Proof. exact (@lem1483525 (term149 y x) term47). Qed.
Lemma lem1558377 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558390 (x : real) (y : real) : (term149 y x) = (term148 x y).
Proof. exact (@lem1483488 x (term116 y)). Qed.
Lemma lem1558391 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1558392 (x : real) (y : real) : (term191 y x) = (term192 x y).
Proof. exact (MK_COMB (@lem1558391) (@lem1558390 x y)). Qed.
Lemma lem1558393 (x : real) (y : real) : (term176 y x) = (term193 x y).
Proof. exact (MK_COMB (@lem1558392 x y) (@lem1558377)). Qed.
Lemma lem1558394 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (@lem1483519 (term148 x y) term47). Qed.
Lemma lem1558396 (x : nat) : (term167 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1558397 : term168 = term47.
Proof. exact (@lem1558396 term35). Qed.
Lemma lem1558398 (x : real) (y : real) : (term195 x y) = (term195 x y).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1558399 (x : real) (y : real) : (term194 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1558398 x y) (@lem1558397)). Qed.
Lemma lem1558400 (x : real) (y : real) : (term196 x y) = (term148 x y).
Proof. exact (@lem1483450 (term148 x y)). Qed.
Lemma lem1558401 (x : real) (y : real) : (term194 x y) = (term148 x y).
Proof. exact (TRANS (@lem1558399 x y) (@lem1558400 x y)). Qed.
Lemma lem1558402 (x : real) (y : real) : (term193 x y) = (term148 x y).
Proof. exact (TRANS (@lem1558394 x y) (@lem1558401 x y)). Qed.
Lemma lem1558403 (x : real) (y : real) : (term176 y x) = (term148 x y).
Proof. exact (TRANS (@lem1558393 x y) (@lem1558402 x y)). Qed.
Lemma lem1558404 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558405 (x : real) (y : real) : (term180 y x) = (term189 x y).
Proof. exact (MK_COMB (@lem1558404) (@lem1558403 x y)). Qed.
Lemma lem1558406 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558407 (x : real) (y : real) : (term175 y x) = (term190 x y).
Proof. exact (MK_COMB (@lem1558405 x y) (@lem1558406)). Qed.
Lemma lem1558408 (x : real) (y : real) : (term174 y x) = (term190 x y).
Proof. exact (TRANS (@lem1558376 y x) (@lem1558407 x y)). Qed.
Lemma lem1558409 (x : real) : (term153 x) = (term154 x).
Proof. exact (@lem1483525 (term155 x) term47). Qed.
Lemma lem1558410 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558422 (x : real) : (term155 x) = (term156 x).
Proof. exact (@lem1483440 term27 x). Qed.
Lemma lem1558424 (m : nat) : (term157 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1558425 : term158 = term47.
Proof. exact (@lem1558424 term35). Qed.
Lemma lem1558426 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1558427 : term159 = term160.
Proof. exact (MK_COMB (@lem1558426) (@lem1558425)). Qed.
Lemma lem1558428 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1558429 (x : real) : (term156 x) = (term161 x).
Proof. exact (MK_COMB (@lem1558427) (@lem1558428 x)). Qed.
Lemma lem1558430 (x : real) : (term155 x) = (term161 x).
Proof. exact (TRANS (@lem1558422 x) (@lem1558429 x)). Qed.
Lemma lem1558431 (x : real) : (term161 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1558433 (x : real) : (term155 x) = term47.
Proof. exact (TRANS (@lem1558430 x) (@lem1558431 x)). Qed.
Lemma lem1558434 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1558435 (x : real) : (term162 x) = term163.
Proof. exact (MK_COMB (@lem1558434) (@lem1558433 x)). Qed.
Lemma lem1558436 (x : real) : (term164 x) = term165.
Proof. exact (MK_COMB (@lem1558435 x) (@lem1558410)). Qed.
Lemma lem1558437 : term165 = term166.
Proof. exact (@lem1483519 term47 term47). Qed.
Lemma lem1558439 (x : nat) : (term167 x) = term47.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1558440 : term168 = term47.
Proof. exact (@lem1558439 term35). Qed.
Lemma lem1558441 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1558442 : term166 = term170.
Proof. exact (MK_COMB (@lem1558441) (@lem1558440)). Qed.
Lemma lem1558443 : term170 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1558444 : term166 = term47.
Proof. exact (TRANS (@lem1558442) (@lem1558443)). Qed.
Lemma lem1558445 : term165 = term47.
Proof. exact (TRANS (@lem1558437) (@lem1558444)). Qed.
Lemma lem1558446 (x : real) : (term164 x) = term47.
Proof. exact (TRANS (@lem1558436 x) (@lem1558445)). Qed.
Lemma lem1558447 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558448 (x : real) : (term171 x) = term172.
Proof. exact (MK_COMB (@lem1558447) (@lem1558446 x)). Qed.
Lemma lem1558449 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558450 (x : real) : (term154 x) = term173.
Proof. exact (MK_COMB (@lem1558448 x) (@lem1558449)). Qed.
Lemma lem1558451 (x : real) : (term153 x) = term173.
Proof. exact (TRANS (@lem1558409 x) (@lem1558450 x)). Qed.
Lemma lem1558452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558453 (x : real) (y : real) : (term197 y x) = (term198 x y).
Proof. exact (MK_COMB (@lem1558452) (@lem1558408 x y)). Qed.
Lemma lem1558454 (x : real) (y : real) : (term134 y x) = (term199 x y).
Proof. exact (MK_COMB (@lem1558453 x y) (@lem1558451 x)). Qed.
Lemma lem1558455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558456 (x : real) (y : real) : (term135 x y) = (term198 x y).
Proof. exact (MK_COMB (@lem1558455) (@lem1558375 x y)). Qed.
Lemma lem1558457 (x : real) (y : real) : (term137 y x) = (term200 x y).
Proof. exact (MK_COMB (@lem1558456 x y) (@lem1558454 x y)). Qed.
Lemma lem1558458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558459 (x : real) (y : real) : (term144 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1558458) (@lem1558356 x y)). Qed.
Lemma lem1558460 (x : real) (y : real) : (term145 y x) = (term202 x y).
Proof. exact (MK_COMB (@lem1558459 x y) (@lem1558457 x y)). Qed.
Lemma lem1558471 (x : real) (y : real) : (term129 x y) = (term202 x y).
Proof. exact (TRANS (@lem1558255 y x) (@lem1558460 x y)). Qed.
Lemma lem1558472 (x : real) (y : real) : (term53 y x) = (term202 x y).
Proof. exact (TRANS (@lem1558239 x y) (@lem1558471 x y)). Qed.
Lemma lem1558474 (x : real) (a : real) (y : real) (r : real) : (term203 x y a r) = (term112 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1558475 (x : real) (y : real) : (term49 y x) = (term113 x y).
Proof. exact (@lem1558474 x (real_max y x) y term47). Qed.
Lemma lem1558488 (y : real) (x : real) : (term114 x y) = (term115 y x).
Proof. exact (@lem1483488 (term116 y) (real_max y x)). Qed.
Lemma lem1558489 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558490 (y : real) (x : real) : (term117 x y) = (term118 y x).
Proof. exact (MK_COMB (@lem1558489) (@lem1558488 y x)). Qed.
Lemma lem1558491 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558492 (y : real) (x : real) : (term119 x y) = (term120 y x).
Proof. exact (MK_COMB (@lem1558490 y x) (@lem1558491)). Qed.
Lemma lem1558505 (y : real) (x : real) : (term121 y x) = (term122 y x).
Proof. exact (@lem1483488 (term116 x) (real_max y x)). Qed.
Lemma lem1558506 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558507 (y : real) (x : real) : (term123 y x) = (term124 y x).
Proof. exact (MK_COMB (@lem1558506) (@lem1558505 y x)). Qed.
Lemma lem1558508 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558509 (y : real) (x : real) : (term125 y x) = (term126 y x).
Proof. exact (MK_COMB (@lem1558507 y x) (@lem1558508)). Qed.
Lemma lem1558510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558511 (y : real) (x : real) : (term127 y x) = (term128 y x).
Proof. exact (MK_COMB (@lem1558510) (@lem1558509 y x)). Qed.
Lemma lem1558512 (y : real) (x : real) : (term113 x y) = (term129 y x).
Proof. exact (MK_COMB (@lem1558511 y x) (@lem1558492 y x)). Qed.
Lemma lem1558513 (y : real) (x : real) : (term49 y x) = (term129 y x).
Proof. exact (TRANS (@lem1558475 x y) (@lem1558512 y x)). Qed.
Lemma lem1558514 (y : real) (x : real) : (term130 y x) = (term129 y x).
Proof. exact (eq_refl (term130 y x)). Qed.
Lemma lem1558515 (y : real) (x : real) : (term129 y x) = (term130 y x).
Proof. exact (SYM (@lem1558514 y x)). Qed.
Lemma lem1558516 (x : real) (y : real) : (term130 y x) = (term131 x y).
Proof. exact (@lem1483205 x (term132 x y) y). Qed.
Lemma lem1558517 (x : real) (y : real) : (term129 y x) = (term131 x y).
Proof. exact (TRANS (@lem1558515 y x) (@lem1558516 x y)). Qed.
Lemma lem1558518 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1558519 (y : real) (x : real) : (term135 y x) = (term135 y x).
Proof. exact (eq_refl (term135 y x)). Qed.
Lemma lem1558520 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (MK_COMB (@lem1558519 y x) (@lem1558518 x y)). Qed.
Lemma lem1558521 (y : real) (x : real) : (term138 y x) = (term139 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem1558522 (x : real) (y : real) : (term140 x y) = (term140 x y).
Proof. exact (eq_refl (term140 x y)). Qed.
Lemma lem1558523 (y : real) (x : real) : (term141 y x) = (term142 y x).
Proof. exact (MK_COMB (@lem1558522 x y) (@lem1558521 y x)). Qed.
Lemma lem1558524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558525 (y : real) (x : real) : (term143 y x) = (term144 y x).
Proof. exact (MK_COMB (@lem1558524) (@lem1558523 y x)). Qed.
Lemma lem1558526 (x : real) (y : real) : (term131 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1558525 y x) (@lem1558520 x y)). Qed.
Lemma lem1558527 (y : real) (x : real) : (term146 y x) = (term146 y x).
Proof. exact (eq_refl (term146 y x)). Qed.
Lemma lem1558528 (x : real) (y : real) : ((term129 y x) = (term131 x y)) = ((term129 y x) = (term145 x y)).
Proof. exact (MK_COMB (@lem1558527 y x) (@lem1558526 x y)). Qed.
Lemma lem1558529 (x : real) (y : real) : (term129 y x) = (term145 x y).
Proof. exact (EQ_MP (@lem1558528 x y) (@lem1558517 x y)). Qed.
Lemma lem1558530 (x : real) (y : real) : (real_ge x y) = (term147 x y).
Proof. exact (@lem1483527 x y). Qed.
Lemma lem1558543 (x : real) (y : real) : (real_sub x y) = (term148 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1558544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1558545 (x : real) (y : real) : (term150 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1558544) (@lem1558543 x y)). Qed.
Lemma lem1558546 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558547 (x : real) (y : real) : (term147 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1558545 x y) (@lem1558546)). Qed.
Lemma lem1558548 (x : real) (y : real) : (real_ge x y) = (term205 x y).
Proof. exact (TRANS (@lem1558530 x y) (@lem1558547 x y)). Qed.
Lemma lem1558549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558550 (x : real) : (term182 x) = term183.
Proof. exact (MK_COMB (@lem1558549) (@lem1558451 x)). Qed.
Lemma lem1558551 (x : real) (y : real) : (term139 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem1558550 x) (@lem1558408 x y)). Qed.
Lemma lem1558552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558553 (x : real) (y : real) : (term140 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1558552) (@lem1558548 x y)). Qed.
Lemma lem1558554 (x : real) (y : real) : (term142 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1558553 x y) (@lem1558551 x y)). Qed.
Lemma lem1558555 (y : real) (x : real) : (real_gt y x) = (term187 y x).
Proof. exact (@lem1483525 y x). Qed.
Lemma lem1558561 (y : real) (x : real) : (real_sub y x) = (term148 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1558566 (x : real) (y : real) : (term148 y x) = (term149 x y).
Proof. exact (@lem1483488 (term116 x) y). Qed.
Lemma lem1558568 (x : real) (y : real) : (real_sub y x) = (term149 x y).
Proof. exact (TRANS (@lem1558561 y x) (@lem1558566 x y)). Qed.
Lemma lem1558569 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1558570 (x : real) (y : real) : (term188 y x) = (term181 x y).
Proof. exact (MK_COMB (@lem1558569) (@lem1558568 x y)). Qed.
Lemma lem1558571 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1558572 (x : real) (y : real) : (term187 y x) = (term174 x y).
Proof. exact (MK_COMB (@lem1558570 x y) (@lem1558571)). Qed.
Lemma lem1558573 (x : real) (y : real) : (real_gt y x) = (term174 x y).
Proof. exact (TRANS (@lem1558555 y x) (@lem1558572 x y)). Qed.
Lemma lem1558574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558575 (x : real) (y : real) : (term197 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1558574) (@lem1558350 x y)). Qed.
Lemma lem1558576 (x : real) (y : real) : (term134 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1558575 x y) (@lem1558317 y)). Qed.
Lemma lem1558577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1558578 (x : real) (y : real) : (term135 y x) = (term197 x y).
Proof. exact (MK_COMB (@lem1558577) (@lem1558573 x y)). Qed.
Lemma lem1558579 (x : real) (y : real) : (term137 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1558578 x y) (@lem1558576 x y)). Qed.
Lemma lem1558580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558581 (x : real) (y : real) : (term144 y x) = (term211 x y).
Proof. exact (MK_COMB (@lem1558580) (@lem1558554 x y)). Qed.
Lemma lem1558582 (x : real) (y : real) : (term145 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem1558581 x y) (@lem1558579 x y)). Qed.
Lemma lem1558593 (x : real) (y : real) : (term129 y x) = (term212 x y).
Proof. exact (TRANS (@lem1558529 x y) (@lem1558582 x y)). Qed.
Lemma lem1558594 (x : real) (y : real) : (term49 y x) = (term212 x y).
Proof. exact (TRANS (@lem1558513 y x) (@lem1558593 x y)). Qed.
Lemma lem1558595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1558596 (x : real) (y : real) : (term55 y x) = (term213 x y).
Proof. exact (MK_COMB (@lem1558595) (@lem1558472 x y)). Qed.
Lemma lem1558597 (x : real) (y : real) : (term56 y x) = (term214 x y).
Proof. exact (MK_COMB (@lem1558596 x y) (@lem1558594 x y)). Qed.
Lemma lem1558598 (x : real) (y : real) (h1 : term214 x y) : term214 x y.
Proof. exact (h1). Qed.
Lemma lem1558599 (x : real) (y : real) (h1 : term202 x y) : term202 x y.
Proof. exact (h1). Qed.
Lemma lem1558600 (x : real) (y : real) (h1 : term186 x y) : term186 x y.
Proof. exact (h1). Qed.
Lemma lem1558601 (x : real) (y : real) (h1 : term186 x y) : term184 x y.
Proof. exact (proj2 (@lem1558600 x y h1)). Qed.
Lemma lem1558604 (x : real) (y : real) (h1 : term186 x y) : term173.
Proof. exact (proj1 (@lem1558601 x y h1)). Qed.
Lemma lem1558606 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1558607 : term173 = term216.
Proof. exact (@lem1558606 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1558608 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1558609 : term173 = False.
Proof. exact (TRANS (@lem1558607) (@lem1558608)). Qed.
Lemma lem1558610 (x : real) (y : real) (h1 : term186 x y) : False.
Proof. exact (EQ_MP (@lem1558609) (@lem1558604 x y h1)). Qed.
Lemma lem1558611 (x : real) (y : real) (h1 : term200 x y) : term200 x y.
Proof. exact (h1). Qed.
Lemma lem1558612 (x : real) (y : real) (h1 : term200 x y) : term199 x y.
Proof. exact (proj2 (@lem1558611 x y h1)). Qed.
Lemma lem1558614 (x : real) (y : real) (h1 : term200 x y) : term173.
Proof. exact (proj2 (@lem1558612 x y h1)). Qed.
Lemma lem1558617 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1558618 : term173 = term216.
Proof. exact (@lem1558617 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1558619 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1558620 : term173 = False.
Proof. exact (TRANS (@lem1558618) (@lem1558619)). Qed.
Lemma lem1558621 (x : real) (y : real) (h1 : term200 x y) : False.
Proof. exact (EQ_MP (@lem1558620) (@lem1558614 x y h1)). Qed.
Lemma lem1558622 (x : real) (y : real) (h1 : term202 x y) : False.
Proof. exact (or_elim (@lem1558599 x y h1) (fun h0 : term186 x y => @lem1558610 x y h0) (fun h0 : term200 x y => @lem1558621 x y h0)). Qed.
Lemma lem1558623 (x : real) (y : real) (h1 : term212 x y) : term212 x y.
Proof. exact (h1). Qed.
Lemma lem1558624 (x : real) (y : real) (h1 : term208 x y) : term208 x y.
Proof. exact (h1). Qed.
Lemma lem1558625 (x : real) (y : real) (h1 : term208 x y) : term206 x y.
Proof. exact (proj2 (@lem1558624 x y h1)). Qed.
Lemma lem1558628 (x : real) (y : real) (h1 : term208 x y) : term173.
Proof. exact (proj1 (@lem1558625 x y h1)). Qed.
Lemma lem1558630 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1558631 : term173 = term216.
Proof. exact (@lem1558630 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1558632 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1558633 : term173 = False.
Proof. exact (TRANS (@lem1558631) (@lem1558632)). Qed.
Lemma lem1558634 (x : real) (y : real) (h1 : term208 x y) : False.
Proof. exact (EQ_MP (@lem1558633) (@lem1558628 x y h1)). Qed.
Lemma lem1558635 (x : real) (y : real) (h1 : term210 x y) : term210 x y.
Proof. exact (h1). Qed.
Lemma lem1558636 (x : real) (y : real) (h1 : term210 x y) : term209 x y.
Proof. exact (proj2 (@lem1558635 x y h1)). Qed.
Lemma lem1558638 (x : real) (y : real) (h1 : term210 x y) : term173.
Proof. exact (proj2 (@lem1558636 x y h1)). Qed.
Lemma lem1558641 (n : nat) (m : nat) : (term215 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1558642 : term173 = term216.
Proof. exact (@lem1558641 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1558643 : term216 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1558644 : term173 = False.
Proof. exact (TRANS (@lem1558642) (@lem1558643)). Qed.
Lemma lem1558645 (x : real) (y : real) (h1 : term210 x y) : False.
Proof. exact (EQ_MP (@lem1558644) (@lem1558638 x y h1)). Qed.
Lemma lem1558646 (x : real) (y : real) (h1 : term212 x y) : False.
Proof. exact (or_elim (@lem1558623 x y h1) (fun h0 : term208 x y => @lem1558634 x y h0) (fun h0 : term210 x y => @lem1558645 x y h0)). Qed.
Lemma lem1558647 (x : real) (y : real) (h1 : term214 x y) : False.
Proof. exact (or_elim (@lem1558598 x y h1) (fun h0 : term202 x y => @lem1558622 x y h0) (fun h0 : term212 x y => @lem1558646 x y h0)). Qed.
Lemma lem1558648 (y : real) (x : real) (h1 : term56 y x) : term56 y x.
Proof. exact (h1). Qed.
Lemma lem1558649 (y : real) (x : real) (h1 : term56 y x) : term214 x y.
Proof. exact (EQ_MP (@lem1558597 x y) (@lem1558648 y x h1)). Qed.
Lemma lem1558650 (y : real) (x : real) (h1 : term56 y x) : (term214 x y) = False.
Proof. exact (prop_ext (fun h2 : term214 x y => @lem1558647 x y h2) (fun h2 : False => @lem1558649 y x h1)). Qed.
Lemma lem1558651 (y : real) (x : real) (h1 : term56 y x) : False.
Proof. exact (EQ_MP (@lem1558650 y x h1) (@lem1558649 y x h1)). Qed.
Lemma lem1558652 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1558653 (x : real) (h1 : term58 x) : False.
Proof. exact (ex_elim (@lem1558652 x h1) (fun y : real => fun h0 : term57 x y => @lem1558651 y x h0)). Qed.
Lemma lem1558654 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem1558655 (h1 : term60) : False.
Proof. exact (ex_elim (@lem1558654 h1) (fun x : real => fun h0 : term59 x => @lem1558653 x h0)). Qed.
Lemma lem1558656 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1558657 (h1 : term11) : term60.
Proof. exact (EQ_MP (@lem1558198) (@lem1558656 h1)). Qed.
Lemma lem1558658 (h1 : term11) : term60 = False.
Proof. exact (prop_ext (fun h2 : term60 => @lem1558655 h2) (fun h2 : False => @lem1558657 h1)). Qed.
Lemma lem1558659 (h1 : term11) : False.
Proof. exact (EQ_MP (@lem1558658 h1) (@lem1558657 h1)). Qed.
Lemma lem1558660 : term217.
Proof. exact (fun h0 : term11 => @lem1558659 h0). Qed.
Lemma lem1558661 : term218.
Proof. exact (@lem1386578 term219). Qed.
Lemma lem1558662 : term219.
Proof. exact (@lem1558661 (@lem1558660)). Qed.

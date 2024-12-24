Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_EQ_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
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
Lemma lem1506955 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 ((real_neg x) = term2) (x = term2)). Qed.
Lemma lem1506956 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1506957 : term5 = term6.
Proof. exact (@lem1506956 term7). Qed.
Lemma lem1506958 (x : real) : (term8 x) = (((real_neg x) = term2) = (x = term2)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1506959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1506960 (x : real) : (term9 x) = (term0 x).
Proof. exact (MK_COMB (@lem1506959) (@lem1506958 x)). Qed.
Lemma lem1506961 (x : real) : (term9 x) = (term1 x).
Proof. exact (TRANS (@lem1506960 x) (@lem1506955 x)). Qed.
Lemma lem1506962 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1506961 x)). Qed.
Lemma lem1506963 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506964 : term6 = term12.
Proof. exact (MK_COMB (@lem1506963) (@lem1506962)). Qed.
Lemma lem1506966 : term5 = term12.
Proof. exact (TRANS (@lem1506957) (@lem1506964)). Qed.
Lemma lem1506983 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1506984 : term11 = term11.
Proof. exact (fun_ext (fun x : real => @lem1506983 x)). Qed.
Lemma lem1506985 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506986 : term12 = term12.
Proof. exact (MK_COMB (@lem1506985) (@lem1506984)). Qed.
Lemma lem1506987 : term5 = term12.
Proof. exact (TRANS (@lem1506966) (@lem1506986)). Qed.
Lemma lem1506988 (x : real) : ((real_neg x) = term2) = ((term13 x) = term2).
Proof. exact (@lem1483529 (real_neg x) term2). Qed.
Lemma lem1506989 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1506996 (x : real) : (real_neg x) = (term14 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1506997 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1506998 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1506997) (@lem1506996 x)). Qed.
Lemma lem1506999 (x : real) : (term13 x) = (term17 x).
Proof. exact (MK_COMB (@lem1506998 x) (@lem1506989)). Qed.
Lemma lem1507000 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem1483519 (term14 x) term2). Qed.
Lemma lem1507002 (x : nat) : (term19 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1507003 : term20 = term2.
Proof. exact (@lem1507002 term21). Qed.
Lemma lem1507004 (x : real) : (term22 x) = (term22 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1507005 (x : real) : (term18 x) = (term23 x).
Proof. exact (MK_COMB (@lem1507004 x) (@lem1507003)). Qed.
Lemma lem1507006 (x : real) : (term23 x) = (term14 x).
Proof. exact (@lem1483450 (term14 x)). Qed.
Lemma lem1507007 (x : real) : (term18 x) = (term14 x).
Proof. exact (TRANS (@lem1507005 x) (@lem1507006 x)). Qed.
Lemma lem1507008 (x : real) : (term17 x) = (term14 x).
Proof. exact (TRANS (@lem1507000 x) (@lem1507007 x)). Qed.
Lemma lem1507009 (x : real) : (term13 x) = (term14 x).
Proof. exact (TRANS (@lem1506999 x) (@lem1507008 x)). Qed.
Lemma lem1507010 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507011 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1507010) (@lem1507009 x)). Qed.
Lemma lem1507012 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507013 (x : real) : ((term13 x) = term2) = ((term14 x) = term2).
Proof. exact (MK_COMB (@lem1507011 x) (@lem1507012)). Qed.
Lemma lem1507014 (x : real) : ((real_neg x) = term2) = ((term14 x) = term2).
Proof. exact (TRANS (@lem1506988 x) (@lem1507013 x)). Qed.
Lemma lem1507015 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483554 x term2). Qed.
Lemma lem1507021 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1507023 (x : nat) : (term19 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1507024 : term20 = term2.
Proof. exact (@lem1507023 term21). Qed.
Lemma lem1507025 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1507026 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1507025 x) (@lem1507024)). Qed.
Lemma lem1507027 (x : real) : (term30 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1507028 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1507026 x) (@lem1507027 x)). Qed.
Lemma lem1507030 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1507021 x) (@lem1507028 x)). Qed.
Lemma lem1507031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1507032 (x : real) : (term31 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1507031) (@lem1507030 x)). Qed.
Lemma lem1507035 (x : real) : (real_neg x) = (term14 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1507036 (x : real) : (term32 x) = (term32 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1507037 (x : real) : ((term31 x) = (real_neg x)) = ((term31 x) = (term14 x)).
Proof. exact (MK_COMB (@lem1507036 x) (@lem1507035 x)). Qed.
Lemma lem1507038 (x : real) : (term31 x) = (term14 x).
Proof. exact (EQ_MP (@lem1507037 x) (@lem1507032 x)). Qed.
Lemma lem1507039 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507040 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1507039) (@lem1507038 x)). Qed.
Lemma lem1507041 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507042 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1507040 x) (@lem1507041)). Qed.
Lemma lem1507043 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507044 (x : real) : (term37 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1507043) (@lem1507030 x)). Qed.
Lemma lem1507045 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507046 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1507044 x) (@lem1507045)). Qed.
Lemma lem1507047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507048 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1507047) (@lem1507046 x)). Qed.
Lemma lem1507049 (x : real) : (term27 x) = (term42 x).
Proof. exact (MK_COMB (@lem1507048 x) (@lem1507042 x)). Qed.
Lemma lem1507050 (x : real) : (term26 x) = (term42 x).
Proof. exact (TRANS (@lem1507015 x) (@lem1507049 x)). Qed.
Lemma lem1507051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1507052 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1507051) (@lem1507014 x)). Qed.
Lemma lem1507053 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1507052 x) (@lem1507050 x)). Qed.
Lemma lem1507054 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1483554 (real_neg x) term2). Qed.
Lemma lem1507055 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507062 (x : real) : (real_neg x) = (term14 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1507063 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1507064 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1507063) (@lem1507062 x)). Qed.
Lemma lem1507065 (x : real) : (term13 x) = (term17 x).
Proof. exact (MK_COMB (@lem1507064 x) (@lem1507055)). Qed.
Lemma lem1507066 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem1483519 (term14 x) term2). Qed.
Lemma lem1507068 (x : nat) : (term19 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1507069 : term20 = term2.
Proof. exact (@lem1507068 term21). Qed.
Lemma lem1507070 (x : real) : (term22 x) = (term22 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1507071 (x : real) : (term18 x) = (term23 x).
Proof. exact (MK_COMB (@lem1507070 x) (@lem1507069)). Qed.
Lemma lem1507072 (x : real) : (term23 x) = (term14 x).
Proof. exact (@lem1483450 (term14 x)). Qed.
Lemma lem1507073 (x : real) : (term18 x) = (term14 x).
Proof. exact (TRANS (@lem1507071 x) (@lem1507072 x)). Qed.
Lemma lem1507074 (x : real) : (term17 x) = (term14 x).
Proof. exact (TRANS (@lem1507066 x) (@lem1507073 x)). Qed.
Lemma lem1507075 (x : real) : (term13 x) = (term14 x).
Proof. exact (TRANS (@lem1507065 x) (@lem1507074 x)). Qed.
Lemma lem1507076 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1507077 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1507076) (@lem1507075 x)). Qed.
Lemma lem1507078 (x : real) : (term50 x) = (term51 x).
Proof. exact (@lem1483512 (term14 x)). Qed.
Lemma lem1507079 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem1483476 term53 term53 x). Qed.
Lemma lem1507081 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1507082 : term56 = term57.
Proof. exact (@lem1507081 term21 term21). Qed.
Lemma lem1507083 : (term58 = (BIT1 0)) = (term59 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1507084 : term59 = term21.
Proof. exact (EQ_MP (@lem1507083) (@lem940073)). Qed.
Lemma lem1507085 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1507086 : term57 = term60.
Proof. exact (MK_COMB (@lem1507085) (@lem1507084)). Qed.
Lemma lem1507087 : term56 = term60.
Proof. exact (TRANS (@lem1507082) (@lem1507086)). Qed.
Lemma lem1507088 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507089 : term61 = term62.
Proof. exact (MK_COMB (@lem1507088) (@lem1507087)). Qed.
Lemma lem1507090 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507091 (x : real) : (term52 x) = (term63 x).
Proof. exact (MK_COMB (@lem1507089) (@lem1507090 x)). Qed.
Lemma lem1507092 (x : real) : (term51 x) = (term63 x).
Proof. exact (TRANS (@lem1507079 x) (@lem1507091 x)). Qed.
Lemma lem1507093 (x : real) : (term63 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1507094 (x : real) : (term51 x) = x.
Proof. exact (TRANS (@lem1507092 x) (@lem1507093 x)). Qed.
Lemma lem1507095 (x : real) : (term50 x) = x.
Proof. exact (TRANS (@lem1507078 x) (@lem1507094 x)). Qed.
Lemma lem1507096 (x : real) : (term64 x) = (term64 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1507097 (x : real) : ((term49 x) = (term50 x)) = ((term49 x) = x).
Proof. exact (MK_COMB (@lem1507096 x) (@lem1507095 x)). Qed.
Lemma lem1507098 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem1507097 x) (@lem1507077 x)). Qed.
Lemma lem1507099 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507100 (x : real) : (term65 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1507099) (@lem1507098 x)). Qed.
Lemma lem1507101 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507102 (x : real) : (term66 x) = (term39 x).
Proof. exact (MK_COMB (@lem1507100 x) (@lem1507101)). Qed.
Lemma lem1507103 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507104 (x : real) : (term67 x) = (term34 x).
Proof. exact (MK_COMB (@lem1507103) (@lem1507075 x)). Qed.
Lemma lem1507105 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507106 (x : real) : (term68 x) = (term36 x).
Proof. exact (MK_COMB (@lem1507104 x) (@lem1507105)). Qed.
Lemma lem1507107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507108 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1507107) (@lem1507106 x)). Qed.
Lemma lem1507109 (x : real) : (term48 x) = (term71 x).
Proof. exact (MK_COMB (@lem1507108 x) (@lem1507102 x)). Qed.
Lemma lem1507110 (x : real) : (term47 x) = (term71 x).
Proof. exact (TRANS (@lem1507054 x) (@lem1507109 x)). Qed.
Lemma lem1507111 (x : real) : (x = term2) = ((term28 x) = term2).
Proof. exact (@lem1483529 x term2). Qed.
Lemma lem1507117 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1507119 (x : nat) : (term19 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1507120 : term20 = term2.
Proof. exact (@lem1507119 term21). Qed.
Lemma lem1507121 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1507122 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1507121 x) (@lem1507120)). Qed.
Lemma lem1507123 (x : real) : (term30 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1507124 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1507122 x) (@lem1507123 x)). Qed.
Lemma lem1507126 (x : real) : (term28 x) = x.
Proof. exact (TRANS (@lem1507117 x) (@lem1507124 x)). Qed.
Lemma lem1507127 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507128 (x : real) : (term72 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1507127) (@lem1507126 x)). Qed.
Lemma lem1507129 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507130 (x : real) : ((term28 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1507128 x) (@lem1507129)). Qed.
Lemma lem1507131 (x : real) : (x = term2) = (x = term2).
Proof. exact (TRANS (@lem1507111 x) (@lem1507130 x)). Qed.
Lemma lem1507132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1507133 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1507132) (@lem1507110 x)). Qed.
Lemma lem1507134 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1507133 x) (@lem1507131 x)). Qed.
Lemma lem1507135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507136 (x : real) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem1507135) (@lem1507053 x)). Qed.
Lemma lem1507137 (x : real) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1507136 x) (@lem1507134 x)). Qed.
Lemma lem1507138 : term11 = term80.
Proof. exact (fun_ext (fun x : real => @lem1507137 x)). Qed.
Lemma lem1507139 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507140 : term12 = term81.
Proof. exact (MK_COMB (@lem1507139) (@lem1507138)). Qed.
Lemma lem1507141 : term5 = term81.
Proof. exact (TRANS (@lem1506987) (@lem1507140)). Qed.
Lemma lem1507143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term82 A P Q) = (term83 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1507144 (P : real -> Prop) (Q : real -> Prop) : (term84 P Q) = (term85 P Q).
Proof. exact (@lem1507143 real P Q). Qed.
Lemma lem1507145 : term86 = term87.
Proof. exact (@lem1507144 term88 term89). Qed.
Lemma lem1507146 (x : real) : (term90 x) = (term46 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1507147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507148 (x : real) : (term91 x) = (term78 x).
Proof. exact (MK_COMB (@lem1507147) (@lem1507146 x)). Qed.
Lemma lem1507149 (x : real) : (term92 x) = (term76 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1507150 (x : real) : (term93 x) = (term79 x).
Proof. exact (MK_COMB (@lem1507148 x) (@lem1507149 x)). Qed.
Lemma lem1507151 : term94 = term80.
Proof. exact (fun_ext (fun x : real => @lem1507150 x)). Qed.
Lemma lem1507152 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507153 : term86 = term81.
Proof. exact (MK_COMB (@lem1507152) (@lem1507151)). Qed.
Lemma lem1507154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1507155 : term95 = term96.
Proof. exact (MK_COMB (@lem1507154) (@lem1507153)). Qed.
Lemma lem1507156 (x : real) : (term90 x) = (term46 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1507157 : term97 = term88.
Proof. exact (fun_ext (fun x : real => @lem1507156 x)). Qed.
Lemma lem1507158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507159 : term98 = term99.
Proof. exact (MK_COMB (@lem1507158) (@lem1507157)). Qed.
Lemma lem1507160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507161 : term100 = term101.
Proof. exact (MK_COMB (@lem1507160) (@lem1507159)). Qed.
Lemma lem1507162 (x : real) : (term92 x) = (term76 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1507163 : term102 = term89.
Proof. exact (fun_ext (fun x : real => @lem1507162 x)). Qed.
Lemma lem1507164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507165 : term103 = term104.
Proof. exact (MK_COMB (@lem1507164) (@lem1507163)). Qed.
Lemma lem1507166 : term87 = term105.
Proof. exact (MK_COMB (@lem1507161) (@lem1507165)). Qed.
Lemma lem1507167 : (term86 = term87) = (term81 = term105).
Proof. exact (MK_COMB (@lem1507155) (@lem1507166)). Qed.
Lemma lem1507168 : term81 = term105.
Proof. exact (EQ_MP (@lem1507167) (@lem1507145)). Qed.
Lemma lem1507266 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1507267 (P : real -> Prop) (Q : real -> Prop) : (term85 P Q) = (term84 P Q).
Proof. exact (@lem1507266 real P Q). Qed.
Lemma lem1507268 : term87 = term86.
Proof. exact (@lem1507267 term88 term89). Qed.
Lemma lem1507269 (x : real) : (term90 x) = (term46 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1507270 : term97 = term88.
Proof. exact (fun_ext (fun x : real => @lem1507269 x)). Qed.
Lemma lem1507271 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507272 : term98 = term99.
Proof. exact (MK_COMB (@lem1507271) (@lem1507270)). Qed.
Lemma lem1507273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507274 : term100 = term101.
Proof. exact (MK_COMB (@lem1507273) (@lem1507272)). Qed.
Lemma lem1507275 (x : real) : (term92 x) = (term76 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1507276 : term102 = term89.
Proof. exact (fun_ext (fun x : real => @lem1507275 x)). Qed.
Lemma lem1507277 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507278 : term103 = term104.
Proof. exact (MK_COMB (@lem1507277) (@lem1507276)). Qed.
Lemma lem1507279 : term87 = term105.
Proof. exact (MK_COMB (@lem1507274) (@lem1507278)). Qed.
Lemma lem1507280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1507281 : term106 = term107.
Proof. exact (MK_COMB (@lem1507280) (@lem1507279)). Qed.
Lemma lem1507282 (x : real) : (term90 x) = (term46 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1507283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507284 (x : real) : (term91 x) = (term78 x).
Proof. exact (MK_COMB (@lem1507283) (@lem1507282 x)). Qed.
Lemma lem1507285 (x : real) : (term92 x) = (term76 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1507286 (x : real) : (term93 x) = (term79 x).
Proof. exact (MK_COMB (@lem1507284 x) (@lem1507285 x)). Qed.
Lemma lem1507287 : term94 = term80.
Proof. exact (fun_ext (fun x : real => @lem1507286 x)). Qed.
Lemma lem1507288 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507289 : term86 = term81.
Proof. exact (MK_COMB (@lem1507288) (@lem1507287)). Qed.
Lemma lem1507290 : (term87 = term86) = (term105 = term81).
Proof. exact (MK_COMB (@lem1507281) (@lem1507289)). Qed.
Lemma lem1507291 : term105 = term81.
Proof. exact (EQ_MP (@lem1507290) (@lem1507268)). Qed.
Lemma lem1507292 : term81 = term81.
Proof. exact (TRANS (@lem1507168) (@lem1507291)). Qed.
Lemma lem1507295 : term5 = term81.
Proof. exact (TRANS (@lem1507141) (@lem1507292)). Qed.
Lemma lem1507312 (x : real) : (term76 x) = (term108 x).
Proof. exact (@lem19367 (term36 x) (term39 x) (x = term2)). Qed.
Lemma lem1507329 (x : real) : (term46 x) = (term109 x).
Proof. exact (@lem19158 (term39 x) ((term14 x) = term2) (term36 x)). Qed.
Lemma lem1507330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1507331 (x : real) : (term78 x) = (term110 x).
Proof. exact (MK_COMB (@lem1507330) (@lem1507329 x)). Qed.
Lemma lem1507332 (x : real) : (term79 x) = (term111 x).
Proof. exact (MK_COMB (@lem1507331 x) (@lem1507312 x)). Qed.
Lemma lem1507333 : term80 = term112.
Proof. exact (fun_ext (fun x : real => @lem1507332 x)). Qed.
Lemma lem1507334 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1507335 : term81 = term113.
Proof. exact (MK_COMB (@lem1507334) (@lem1507333)). Qed.
Lemma lem1507336 : term5 = term113.
Proof. exact (TRANS (@lem1507295) (@lem1507335)). Qed.
Lemma lem1507358 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (h1). Qed.
Lemma lem1507359 (x : real) (h1 : term109 x) : term109 x.
Proof. exact (h1). Qed.
Lemma lem1507360 (x : real) (h1 : term114 x) : term114 x.
Proof. exact (h1). Qed.
Lemma lem1507361 (x : real) (h1 : term114 x) : term39 x.
Proof. exact (proj2 (@lem1507360 x h1)). Qed.
Lemma lem1507362 (x : real) (h1 : term114 x) : (term14 x) = term2.
Proof. exact (proj1 (@lem1507360 x h1)). Qed.
Lemma lem1507364 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507365 : term116 = term117.
Proof. exact (@lem1507364 (NUMERAL 0) term21). Qed.
Lemma lem1507366 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1507367 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1507368 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem1507367 h1) (fun h1 : term117 = True => @lem1507366)). Qed.
Lemma lem1507369 : term117 = True.
Proof. exact (EQ_MP (@lem1507368) (@lem1507366)). Qed.
Lemma lem1507370 : term116 = True.
Proof. exact (TRANS (@lem1507365) (@lem1507369)). Qed.
Lemma lem1507371 : True = term116.
Proof. exact (SYM (@lem1507370)). Qed.
Lemma lem1507372 : term116.
Proof. exact (EQ_MP (@lem1507371) (@lem0)). Qed.
Lemma lem1507373 (x : real) (h1 : term114 x) : term119 x.
Proof. exact (conj (@lem1507372) (@lem1507361 x h1)). Qed.
Lemma lem1507375 (x : real) (y : real) : term120 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1507376 (x : real) : term121 x.
Proof. exact (@lem1507375 term60 x). Qed.
Lemma lem1507377 (x : real) (h1 : term114 x) : term122 x.
Proof. exact (@lem1507376 x (@lem1507373 x h1)). Qed.
Lemma lem1507378 (x : real) : (term63 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1507379 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507380 (x : real) : (term123 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1507379) (@lem1507378 x)). Qed.
Lemma lem1507381 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507382 (x : real) : (term122 x) = (term39 x).
Proof. exact (MK_COMB (@lem1507380 x) (@lem1507381)). Qed.
Lemma lem1507383 (x : real) (h1 : term114 x) : term39 x.
Proof. exact (EQ_MP (@lem1507382 x) (@lem1507377 x h1)). Qed.
Lemma lem1507385 (y : real) : term124 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1507386 (x : real) : term125 x.
Proof. exact (@lem1507385 (term14 x)). Qed.
Lemma lem1507387 (x : real) (h1 : term114 x) : term126 x.
Proof. exact (@lem1507386 x (@lem1507362 x h1)). Qed.
Lemma lem1507388 (x : real) (h1 : term114 x) : term127 x.
Proof. exact (@lem1507387 x h1 term60). Qed.
Lemma lem1507389 (x : real) : (term127 x) = ((term128 x) = term2).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1507390 (x : real) (h1 : term114 x) : (term128 x) = term2.
Proof. exact (EQ_MP (@lem1507389 x) (@lem1507388 x h1)). Qed.
Lemma lem1507391 (x : real) : (term128 x) = (term14 x).
Proof. exact (@lem1483460 (term14 x)). Qed.
Lemma lem1507392 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507393 (x : real) : (term129 x) = (term25 x).
Proof. exact (MK_COMB (@lem1507392) (@lem1507391 x)). Qed.
Lemma lem1507394 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507395 (x : real) : ((term128 x) = term2) = ((term14 x) = term2).
Proof. exact (MK_COMB (@lem1507393 x) (@lem1507394)). Qed.
Lemma lem1507396 (x : real) (h1 : term114 x) : (term14 x) = term2.
Proof. exact (EQ_MP (@lem1507395 x) (@lem1507390 x h1)). Qed.
Lemma lem1507397 (x : real) (h1 : term114 x) : term114 x.
Proof. exact (conj (@lem1507396 x h1) (@lem1507383 x h1)). Qed.
Lemma lem1507399 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1507400 (x : real) : term131 x.
Proof. exact (@lem1507399 (term14 x) x). Qed.
Lemma lem1507401 (x : real) (h1 : term114 x) : term132 x.
Proof. exact (@lem1507400 x (@lem1507397 x h1)). Qed.
Lemma lem1507402 (x : real) : (term133 x) = (term134 x).
Proof. exact (@lem1483440 term53 x). Qed.
Lemma lem1507404 (m : nat) : (term135 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507405 : term136 = term2.
Proof. exact (@lem1507404 term21). Qed.
Lemma lem1507406 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507407 : term137 = term138.
Proof. exact (MK_COMB (@lem1507406) (@lem1507405)). Qed.
Lemma lem1507408 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507409 (x : real) : (term134 x) = (term139 x).
Proof. exact (MK_COMB (@lem1507407) (@lem1507408 x)). Qed.
Lemma lem1507410 (x : real) : (term133 x) = (term139 x).
Proof. exact (TRANS (@lem1507402 x) (@lem1507409 x)). Qed.
Lemma lem1507411 (x : real) : (term139 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1507412 (x : real) : (term133 x) = term2.
Proof. exact (TRANS (@lem1507410 x) (@lem1507411 x)). Qed.
Lemma lem1507413 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507414 (x : real) : (term140 x) = term141.
Proof. exact (MK_COMB (@lem1507413) (@lem1507412 x)). Qed.
Lemma lem1507415 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507416 (x : real) : (term132 x) = term142.
Proof. exact (MK_COMB (@lem1507414 x) (@lem1507415)). Qed.
Lemma lem1507417 (x : real) (h1 : term114 x) : term142.
Proof. exact (EQ_MP (@lem1507416 x) (@lem1507401 x h1)). Qed.
Lemma lem1507419 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507420 : term142 = term143.
Proof. exact (@lem1507419 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507421 : term143 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507422 : term142 = False.
Proof. exact (TRANS (@lem1507420) (@lem1507421)). Qed.
Lemma lem1507423 (x : real) (h1 : term114 x) : False.
Proof. exact (EQ_MP (@lem1507422) (@lem1507417 x h1)). Qed.
Lemma lem1507424 (x : real) (h1 : term144 x) : term144 x.
Proof. exact (h1). Qed.
Lemma lem1507425 (x : real) (h1 : term144 x) : term36 x.
Proof. exact (proj2 (@lem1507424 x h1)). Qed.
Lemma lem1507426 (x : real) (h1 : term144 x) : (term14 x) = term2.
Proof. exact (proj1 (@lem1507424 x h1)). Qed.
Lemma lem1507428 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507429 : term116 = term117.
Proof. exact (@lem1507428 (NUMERAL 0) term21). Qed.
Lemma lem1507430 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1507431 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1507432 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem1507431 h1) (fun h1 : term117 = True => @lem1507430)). Qed.
Lemma lem1507433 : term117 = True.
Proof. exact (EQ_MP (@lem1507432) (@lem1507430)). Qed.
Lemma lem1507434 : term116 = True.
Proof. exact (TRANS (@lem1507429) (@lem1507433)). Qed.
Lemma lem1507435 : True = term116.
Proof. exact (SYM (@lem1507434)). Qed.
Lemma lem1507436 : term116.
Proof. exact (EQ_MP (@lem1507435) (@lem0)). Qed.
Lemma lem1507437 (x : real) (h1 : term144 x) : term145 x.
Proof. exact (conj (@lem1507436) (@lem1507425 x h1)). Qed.
Lemma lem1507439 (x : real) (y : real) : term120 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1507440 (x : real) : term146 x.
Proof. exact (@lem1507439 term60 (term14 x)). Qed.
Lemma lem1507441 (x : real) (h1 : term144 x) : term147 x.
Proof. exact (@lem1507440 x (@lem1507437 x h1)). Qed.
Lemma lem1507442 (x : real) : (term128 x) = (term14 x).
Proof. exact (@lem1483460 (term14 x)). Qed.
Lemma lem1507443 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507444 (x : real) : (term148 x) = (term34 x).
Proof. exact (MK_COMB (@lem1507443) (@lem1507442 x)). Qed.
Lemma lem1507445 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507446 (x : real) : (term147 x) = (term36 x).
Proof. exact (MK_COMB (@lem1507444 x) (@lem1507445)). Qed.
Lemma lem1507447 (x : real) (h1 : term144 x) : term36 x.
Proof. exact (EQ_MP (@lem1507446 x) (@lem1507441 x h1)). Qed.
Lemma lem1507449 (y : real) : term124 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1507450 (x : real) : term125 x.
Proof. exact (@lem1507449 (term14 x)). Qed.
Lemma lem1507451 (x : real) (h1 : term144 x) : term126 x.
Proof. exact (@lem1507450 x (@lem1507426 x h1)). Qed.
Lemma lem1507452 (x : real) (h1 : term144 x) : term149 x.
Proof. exact (@lem1507451 x h1 term53). Qed.
Lemma lem1507453 (x : real) : (term149 x) = ((term51 x) = term2).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1507454 (x : real) (h1 : term144 x) : (term51 x) = term2.
Proof. exact (EQ_MP (@lem1507453 x) (@lem1507452 x h1)). Qed.
Lemma lem1507455 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem1483476 term53 term53 x). Qed.
Lemma lem1507457 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1507458 : term56 = term57.
Proof. exact (@lem1507457 term21 term21). Qed.
Lemma lem1507459 : (term58 = (BIT1 0)) = (term59 = term21).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1507460 : term59 = term21.
Proof. exact (EQ_MP (@lem1507459) (@lem940073)). Qed.
Lemma lem1507461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1507462 : term57 = term60.
Proof. exact (MK_COMB (@lem1507461) (@lem1507460)). Qed.
Lemma lem1507463 : term56 = term60.
Proof. exact (TRANS (@lem1507458) (@lem1507462)). Qed.
Lemma lem1507464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507465 : term61 = term62.
Proof. exact (MK_COMB (@lem1507464) (@lem1507463)). Qed.
Lemma lem1507466 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507467 (x : real) : (term52 x) = (term63 x).
Proof. exact (MK_COMB (@lem1507465) (@lem1507466 x)). Qed.
Lemma lem1507468 (x : real) : (term51 x) = (term63 x).
Proof. exact (TRANS (@lem1507455 x) (@lem1507467 x)). Qed.
Lemma lem1507469 (x : real) : (term63 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1507470 (x : real) : (term51 x) = x.
Proof. exact (TRANS (@lem1507468 x) (@lem1507469 x)). Qed.
Lemma lem1507471 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507472 (x : real) : (term150 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1507471) (@lem1507470 x)). Qed.
Lemma lem1507473 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507474 (x : real) : ((term51 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1507472 x) (@lem1507473)). Qed.
Lemma lem1507475 (x : real) (h1 : term144 x) : x = term2.
Proof. exact (EQ_MP (@lem1507474 x) (@lem1507454 x h1)). Qed.
Lemma lem1507476 (x : real) (h1 : term144 x) : term151 x.
Proof. exact (conj (@lem1507475 x h1) (@lem1507447 x h1)). Qed.
Lemma lem1507478 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1507479 (x : real) : term152 x.
Proof. exact (@lem1507478 x (term14 x)). Qed.
Lemma lem1507480 (x : real) (h1 : term144 x) : term153 x.
Proof. exact (@lem1507479 x (@lem1507476 x h1)). Qed.
Lemma lem1507481 (x : real) : (term154 x) = (term134 x).
Proof. exact (@lem1483442 term53 x). Qed.
Lemma lem1507483 (m : nat) : (term135 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507484 : term136 = term2.
Proof. exact (@lem1507483 term21). Qed.
Lemma lem1507485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507486 : term137 = term138.
Proof. exact (MK_COMB (@lem1507485) (@lem1507484)). Qed.
Lemma lem1507487 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507488 (x : real) : (term134 x) = (term139 x).
Proof. exact (MK_COMB (@lem1507486) (@lem1507487 x)). Qed.
Lemma lem1507489 (x : real) : (term154 x) = (term139 x).
Proof. exact (TRANS (@lem1507481 x) (@lem1507488 x)). Qed.
Lemma lem1507490 (x : real) : (term139 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1507491 (x : real) : (term154 x) = term2.
Proof. exact (TRANS (@lem1507489 x) (@lem1507490 x)). Qed.
Lemma lem1507492 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507493 (x : real) : (term155 x) = term141.
Proof. exact (MK_COMB (@lem1507492) (@lem1507491 x)). Qed.
Lemma lem1507494 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507495 (x : real) : (term153 x) = term142.
Proof. exact (MK_COMB (@lem1507493 x) (@lem1507494)). Qed.
Lemma lem1507496 (x : real) (h1 : term144 x) : term142.
Proof. exact (EQ_MP (@lem1507495 x) (@lem1507480 x h1)). Qed.
Lemma lem1507498 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507499 : term142 = term143.
Proof. exact (@lem1507498 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507500 : term143 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507501 : term142 = False.
Proof. exact (TRANS (@lem1507499) (@lem1507500)). Qed.
Lemma lem1507502 (x : real) (h1 : term144 x) : False.
Proof. exact (EQ_MP (@lem1507501) (@lem1507496 x h1)). Qed.
Lemma lem1507503 (x : real) (h1 : term109 x) : False.
Proof. exact (or_elim (@lem1507359 x h1) (fun h0 : term114 x => @lem1507423 x h0) (fun h0 : term144 x => @lem1507502 x h0)). Qed.
Lemma lem1507504 (x : real) (h1 : term108 x) : term108 x.
Proof. exact (h1). Qed.
Lemma lem1507505 (x : real) (h1 : term156 x) : term156 x.
Proof. exact (h1). Qed.
Lemma lem1507506 (x : real) (h1 : term156 x) : x = term2.
Proof. exact (proj2 (@lem1507505 x h1)). Qed.
Lemma lem1507507 (x : real) (h1 : term156 x) : term36 x.
Proof. exact (proj1 (@lem1507505 x h1)). Qed.
Lemma lem1507509 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507510 : term116 = term117.
Proof. exact (@lem1507509 (NUMERAL 0) term21). Qed.
Lemma lem1507511 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1507512 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1507513 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem1507512 h1) (fun h1 : term117 = True => @lem1507511)). Qed.
Lemma lem1507514 : term117 = True.
Proof. exact (EQ_MP (@lem1507513) (@lem1507511)). Qed.
Lemma lem1507515 : term116 = True.
Proof. exact (TRANS (@lem1507510) (@lem1507514)). Qed.
Lemma lem1507516 : True = term116.
Proof. exact (SYM (@lem1507515)). Qed.
Lemma lem1507517 : term116.
Proof. exact (EQ_MP (@lem1507516) (@lem0)). Qed.
Lemma lem1507518 (x : real) (h1 : term156 x) : term145 x.
Proof. exact (conj (@lem1507517) (@lem1507507 x h1)). Qed.
Lemma lem1507520 (x : real) (y : real) : term120 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1507521 (x : real) : term146 x.
Proof. exact (@lem1507520 term60 (term14 x)). Qed.
Lemma lem1507522 (x : real) (h1 : term156 x) : term147 x.
Proof. exact (@lem1507521 x (@lem1507518 x h1)). Qed.
Lemma lem1507523 (x : real) : (term128 x) = (term14 x).
Proof. exact (@lem1483460 (term14 x)). Qed.
Lemma lem1507524 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507525 (x : real) : (term148 x) = (term34 x).
Proof. exact (MK_COMB (@lem1507524) (@lem1507523 x)). Qed.
Lemma lem1507526 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507527 (x : real) : (term147 x) = (term36 x).
Proof. exact (MK_COMB (@lem1507525 x) (@lem1507526)). Qed.
Lemma lem1507528 (x : real) (h1 : term156 x) : term36 x.
Proof. exact (EQ_MP (@lem1507527 x) (@lem1507522 x h1)). Qed.
Lemma lem1507530 (y : real) : term124 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1507531 (x : real) : term124 x.
Proof. exact (@lem1507530 x). Qed.
Lemma lem1507532 (x : real) (h1 : term156 x) : term157 x.
Proof. exact (@lem1507531 x (@lem1507506 x h1)). Qed.
Lemma lem1507533 (x : real) (h1 : term156 x) : term158 x.
Proof. exact (@lem1507532 x h1 term60). Qed.
Lemma lem1507534 (x : real) : (term158 x) = ((term63 x) = term2).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1507535 (x : real) (h1 : term156 x) : (term63 x) = term2.
Proof. exact (EQ_MP (@lem1507534 x) (@lem1507533 x h1)). Qed.
Lemma lem1507536 (x : real) : (term63 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1507537 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1507538 (x : real) : (term159 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1507537) (@lem1507536 x)). Qed.
Lemma lem1507539 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507540 (x : real) : ((term63 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1507538 x) (@lem1507539)). Qed.
Lemma lem1507541 (x : real) (h1 : term156 x) : x = term2.
Proof. exact (EQ_MP (@lem1507540 x) (@lem1507535 x h1)). Qed.
Lemma lem1507542 (x : real) (h1 : term156 x) : term151 x.
Proof. exact (conj (@lem1507541 x h1) (@lem1507528 x h1)). Qed.
Lemma lem1507544 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1507545 (x : real) : term152 x.
Proof. exact (@lem1507544 x (term14 x)). Qed.
Lemma lem1507546 (x : real) (h1 : term156 x) : term153 x.
Proof. exact (@lem1507545 x (@lem1507542 x h1)). Qed.
Lemma lem1507547 (x : real) : (term154 x) = (term134 x).
Proof. exact (@lem1483442 term53 x). Qed.
Lemma lem1507549 (m : nat) : (term135 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507550 : term136 = term2.
Proof. exact (@lem1507549 term21). Qed.
Lemma lem1507551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507552 : term137 = term138.
Proof. exact (MK_COMB (@lem1507551) (@lem1507550)). Qed.
Lemma lem1507553 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507554 (x : real) : (term134 x) = (term139 x).
Proof. exact (MK_COMB (@lem1507552) (@lem1507553 x)). Qed.
Lemma lem1507555 (x : real) : (term154 x) = (term139 x).
Proof. exact (TRANS (@lem1507547 x) (@lem1507554 x)). Qed.
Lemma lem1507556 (x : real) : (term139 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1507557 (x : real) : (term154 x) = term2.
Proof. exact (TRANS (@lem1507555 x) (@lem1507556 x)). Qed.
Lemma lem1507558 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507559 (x : real) : (term155 x) = term141.
Proof. exact (MK_COMB (@lem1507558) (@lem1507557 x)). Qed.
Lemma lem1507560 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507561 (x : real) : (term153 x) = term142.
Proof. exact (MK_COMB (@lem1507559 x) (@lem1507560)). Qed.
Lemma lem1507562 (x : real) (h1 : term156 x) : term142.
Proof. exact (EQ_MP (@lem1507561 x) (@lem1507546 x h1)). Qed.
Lemma lem1507564 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507565 : term142 = term143.
Proof. exact (@lem1507564 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507566 : term143 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507567 : term142 = False.
Proof. exact (TRANS (@lem1507565) (@lem1507566)). Qed.
Lemma lem1507568 (x : real) (h1 : term156 x) : False.
Proof. exact (EQ_MP (@lem1507567) (@lem1507562 x h1)). Qed.
Lemma lem1507569 (x : real) (h1 : term160 x) : term160 x.
Proof. exact (h1). Qed.
Lemma lem1507570 (x : real) (h1 : term160 x) : x = term2.
Proof. exact (proj2 (@lem1507569 x h1)). Qed.
Lemma lem1507571 (x : real) (h1 : term160 x) : term39 x.
Proof. exact (proj1 (@lem1507569 x h1)). Qed.
Lemma lem1507573 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507574 : term116 = term117.
Proof. exact (@lem1507573 (NUMERAL 0) term21). Qed.
Lemma lem1507575 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1507576 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1507577 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem1507576 h1) (fun h1 : term117 = True => @lem1507575)). Qed.
Lemma lem1507578 : term117 = True.
Proof. exact (EQ_MP (@lem1507577) (@lem1507575)). Qed.
Lemma lem1507579 : term116 = True.
Proof. exact (TRANS (@lem1507574) (@lem1507578)). Qed.
Lemma lem1507580 : True = term116.
Proof. exact (SYM (@lem1507579)). Qed.
Lemma lem1507581 : term116.
Proof. exact (EQ_MP (@lem1507580) (@lem0)). Qed.
Lemma lem1507582 (x : real) (h1 : term160 x) : term119 x.
Proof. exact (conj (@lem1507581) (@lem1507571 x h1)). Qed.
Lemma lem1507584 (x : real) (y : real) : term120 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1507585 (x : real) : term121 x.
Proof. exact (@lem1507584 term60 x). Qed.
Lemma lem1507586 (x : real) (h1 : term160 x) : term122 x.
Proof. exact (@lem1507585 x (@lem1507582 x h1)). Qed.
Lemma lem1507587 (x : real) : (term63 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1507588 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507589 (x : real) : (term123 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1507588) (@lem1507587 x)). Qed.
Lemma lem1507590 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507591 (x : real) : (term122 x) = (term39 x).
Proof. exact (MK_COMB (@lem1507589 x) (@lem1507590)). Qed.
Lemma lem1507592 (x : real) (h1 : term160 x) : term39 x.
Proof. exact (EQ_MP (@lem1507591 x) (@lem1507586 x h1)). Qed.
Lemma lem1507594 (y : real) : term124 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1507595 (x : real) : term124 x.
Proof. exact (@lem1507594 x). Qed.
Lemma lem1507596 (x : real) (h1 : term160 x) : term157 x.
Proof. exact (@lem1507595 x (@lem1507570 x h1)). Qed.
Lemma lem1507597 (x : real) (h1 : term160 x) : term161 x.
Proof. exact (@lem1507596 x h1 term53). Qed.
Lemma lem1507598 (x : real) : (term161 x) = ((term14 x) = term2).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1507605 (x : real) (h1 : term160 x) : (term14 x) = term2.
Proof. exact (EQ_MP (@lem1507598 x) (@lem1507597 x h1)). Qed.
Lemma lem1507606 (x : real) (h1 : term160 x) : term114 x.
Proof. exact (conj (@lem1507605 x h1) (@lem1507592 x h1)). Qed.
Lemma lem1507608 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1507609 (x : real) : term131 x.
Proof. exact (@lem1507608 (term14 x) x). Qed.
Lemma lem1507610 (x : real) (h1 : term160 x) : term132 x.
Proof. exact (@lem1507609 x (@lem1507606 x h1)). Qed.
Lemma lem1507611 (x : real) : (term133 x) = (term134 x).
Proof. exact (@lem1483440 term53 x). Qed.
Lemma lem1507613 (m : nat) : (term135 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1507614 : term136 = term2.
Proof. exact (@lem1507613 term21). Qed.
Lemma lem1507615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1507616 : term137 = term138.
Proof. exact (MK_COMB (@lem1507615) (@lem1507614)). Qed.
Lemma lem1507617 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1507618 (x : real) : (term134 x) = (term139 x).
Proof. exact (MK_COMB (@lem1507616) (@lem1507617 x)). Qed.
Lemma lem1507619 (x : real) : (term133 x) = (term139 x).
Proof. exact (TRANS (@lem1507611 x) (@lem1507618 x)). Qed.
Lemma lem1507620 (x : real) : (term139 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1507621 (x : real) : (term133 x) = term2.
Proof. exact (TRANS (@lem1507619 x) (@lem1507620 x)). Qed.
Lemma lem1507622 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1507623 (x : real) : (term140 x) = term141.
Proof. exact (MK_COMB (@lem1507622) (@lem1507621 x)). Qed.
Lemma lem1507624 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1507625 (x : real) : (term132 x) = term142.
Proof. exact (MK_COMB (@lem1507623 x) (@lem1507624)). Qed.
Lemma lem1507626 (x : real) (h1 : term160 x) : term142.
Proof. exact (EQ_MP (@lem1507625 x) (@lem1507610 x h1)). Qed.
Lemma lem1507628 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1507629 : term142 = term143.
Proof. exact (@lem1507628 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1507630 : term143 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1507631 : term142 = False.
Proof. exact (TRANS (@lem1507629) (@lem1507630)). Qed.
Lemma lem1507632 (x : real) (h1 : term160 x) : False.
Proof. exact (EQ_MP (@lem1507631) (@lem1507626 x h1)). Qed.
Lemma lem1507633 (x : real) (h1 : term108 x) : False.
Proof. exact (or_elim (@lem1507504 x h1) (fun h0 : term156 x => @lem1507568 x h0) (fun h0 : term160 x => @lem1507632 x h0)). Qed.
Lemma lem1507634 (x : real) (h1 : term111 x) : False.
Proof. exact (or_elim (@lem1507358 x h1) (fun h0 : term109 x => @lem1507503 x h0) (fun h0 : term108 x => @lem1507633 x h0)). Qed.
Lemma lem1507636 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (h1). Qed.
Lemma lem1507637 (x : real) (h1 : term111 x) : (term111 x) = False.
Proof. exact (prop_ext (fun h2 : term111 x => @lem1507634 x h1) (fun h2 : False => @lem1507636 x h1)). Qed.
Lemma lem1507638 (x : real) (h1 : term111 x) : False.
Proof. exact (EQ_MP (@lem1507637 x h1) (@lem1507636 x h1)). Qed.
Lemma lem1507639 (h1 : term113) : term113.
Proof. exact (h1). Qed.
Lemma lem1507640 (h1 : term113) : False.
Proof. exact (ex_elim (@lem1507639 h1) (fun x : real => fun h0 : term112 x => @lem1507638 x h0)). Qed.
Lemma lem1507641 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1507642 (h1 : term5) : term113.
Proof. exact (EQ_MP (@lem1507336) (@lem1507641 h1)). Qed.
Lemma lem1507643 (h1 : term5) : term113 = False.
Proof. exact (prop_ext (fun h2 : term113 => @lem1507640 h2) (fun h2 : False => @lem1507642 h1)). Qed.
Lemma lem1507644 (h1 : term5) : False.
Proof. exact (EQ_MP (@lem1507643 h1) (@lem1507642 h1)). Qed.
Lemma lem1507645 : term162.
Proof. exact (fun h0 : term5 => @lem1507644 h0). Qed.
Lemma lem1507646 : term163.
Proof. exact (@lem1386578 term164). Qed.
Lemma lem1507647 : term164.
Proof. exact (@lem1507646 (@lem1507645)). Qed.

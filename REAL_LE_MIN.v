Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_MIN_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482698_spec.
Require Import thm1483429_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1560928 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17045 (real_le z x) (real_le z y)). Qed.
Lemma lem1560934 (x : real) (z : real) (y : real) : (term2 x z y) = (term2 x z y).
Proof. exact (eq_refl (term2 x z y)). Qed.
Lemma lem1560936 (z : real) (x : real) (y : real) : (term3 z x y) = (term3 z x y).
Proof. exact (eq_refl (term3 z x y)). Qed.
Lemma lem1560937 (x : real) (z : real) (y : real) : (term4 x z y) = (term5 x z y).
Proof. exact (MK_COMB (@lem1560936 z x y) (@lem1560928 x z y)). Qed.
Lemma lem1560938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560939 (x : real) (z : real) (y : real) : (term6 x z y) = (term7 x z y).
Proof. exact (MK_COMB (@lem1560938) (@lem1560937 x z y)). Qed.
Lemma lem1560940 (x : real) (z : real) (y : real) : (term8 x z y) = (term9 x z y).
Proof. exact (MK_COMB (@lem1560939 x z y) (@lem1560934 x z y)). Qed.
Lemma lem1560941 (x : real) (z : real) (y : real) : (term10 x z y) = (term8 x z y).
Proof. exact (@lem17646 (term11 z x y) (term12 x z y)). Qed.
Lemma lem1560942 (x : real) (z : real) (y : real) : (term10 x z y) = (term9 x z y).
Proof. exact (TRANS (@lem1560941 x z y) (@lem1560940 x z y)). Qed.
Lemma lem1560943 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1560944 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1560943 (term17 x y)). Qed.
Lemma lem1560945 (x : real) (z : real) (y : real) : (term18 x y z) = ((term11 z x y) = (term12 x z y)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1560946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1560947 (x : real) (z : real) (y : real) : (term19 x y z) = (term10 x z y).
Proof. exact (MK_COMB (@lem1560946) (@lem1560945 x z y)). Qed.
Lemma lem1560948 (x : real) (z : real) (y : real) : (term19 x y z) = (term9 x z y).
Proof. exact (TRANS (@lem1560947 x z y) (@lem1560942 x z y)). Qed.
Lemma lem1560949 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1560948 x z y)). Qed.
Lemma lem1560950 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560951 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1560950) (@lem1560949 x y)). Qed.
Lemma lem1560952 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1560944 x y) (@lem1560951 x y)). Qed.
Lemma lem1560953 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1560954 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1560953 (term25 x)). Qed.
Lemma lem1560955 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1560956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1560957 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1560956) (@lem1560955 x y)). Qed.
Lemma lem1560958 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1560957 x y) (@lem1560952 x y)). Qed.
Lemma lem1560959 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1560958 x y)). Qed.
Lemma lem1560960 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560961 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1560960) (@lem1560959 x)). Qed.
Lemma lem1560962 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1560954 x) (@lem1560961 x)). Qed.
Lemma lem1560963 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1560964 : term32 = term33.
Proof. exact (@lem1560963 term34). Qed.
Lemma lem1560965 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1560966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1560967 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1560966) (@lem1560965 x)). Qed.
Lemma lem1560968 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1560967 x) (@lem1560962 x)). Qed.
Lemma lem1560969 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1560968 x)). Qed.
Lemma lem1560970 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560971 : term33 = term40.
Proof. exact (MK_COMB (@lem1560970) (@lem1560969)). Qed.
Lemma lem1560973 : term32 = term40.
Proof. exact (TRANS (@lem1560964) (@lem1560971)). Qed.
Lemma lem1561000 (x : real) (z : real) (y : real) : (term9 x z y) = (term9 x z y).
Proof. exact (eq_refl (term9 x z y)). Qed.
Lemma lem1561001 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1561000 x z y)). Qed.
Lemma lem1561002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561003 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1561002) (@lem1561001 x y)). Qed.
Lemma lem1561004 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1561003 x y)). Qed.
Lemma lem1561005 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561006 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1561005) (@lem1561004 x)). Qed.
Lemma lem1561007 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1561006 x)). Qed.
Lemma lem1561008 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561009 : term40 = term40.
Proof. exact (MK_COMB (@lem1561008) (@lem1561007)). Qed.
Lemma lem1561010 : term32 = term40.
Proof. exact (TRANS (@lem1560973) (@lem1561009)). Qed.
Lemma lem1561011 (x : real) (y : real) (z : real) : (term11 z x y) = (term41 x y z).
Proof. exact (@lem1483523 (real_min x y) z). Qed.
Lemma lem1561017 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1561022 (z : real) (x : real) (y : real) : (term43 x y z) = (term44 z x y).
Proof. exact (@lem1483488 (term45 z) (real_min x y)). Qed.
Lemma lem1561024 (z : real) (x : real) (y : real) : (term42 x y z) = (term44 z x y).
Proof. exact (TRANS (@lem1561017 x y z) (@lem1561022 z x y)). Qed.
Lemma lem1561025 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561026 (z : real) (x : real) (y : real) : (term46 x y z) = (term47 z x y).
Proof. exact (MK_COMB (@lem1561025) (@lem1561024 z x y)). Qed.
Lemma lem1561027 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561028 (z : real) (x : real) (y : real) : (term41 x y z) = (term49 z x y).
Proof. exact (MK_COMB (@lem1561026 z x y) (@lem1561027)). Qed.
Lemma lem1561029 (z : real) (x : real) (y : real) : (term11 z x y) = (term49 z x y).
Proof. exact (TRANS (@lem1561011 x y z) (@lem1561028 z x y)). Qed.
Lemma lem1561030 (z : real) (x : real) : (term50 z x) = (term51 z x).
Proof. exact (@lem1483533 z x). Qed.
Lemma lem1561036 (z : real) (x : real) : (real_sub z x) = (term52 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1561041 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1561043 (x : real) (z : real) : (real_sub z x) = (term53 x z).
Proof. exact (TRANS (@lem1561036 z x) (@lem1561041 x z)). Qed.
Lemma lem1561044 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561045 (x : real) (z : real) : (term54 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1561044) (@lem1561043 x z)). Qed.
Lemma lem1561046 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561047 (x : real) (z : real) : (term51 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1561045 x z) (@lem1561046)). Qed.
Lemma lem1561048 (x : real) (z : real) : (term50 z x) = (term56 x z).
Proof. exact (TRANS (@lem1561030 z x) (@lem1561047 x z)). Qed.
Lemma lem1561049 (z : real) (y : real) : (term50 z y) = (term51 z y).
Proof. exact (@lem1483533 z y). Qed.
Lemma lem1561055 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1561060 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1561062 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1561055 z y) (@lem1561060 y z)). Qed.
Lemma lem1561063 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561064 (y : real) (z : real) : (term54 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1561063) (@lem1561062 y z)). Qed.
Lemma lem1561065 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561066 (y : real) (z : real) : (term51 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1561064 y z) (@lem1561065)). Qed.
Lemma lem1561067 (y : real) (z : real) : (term50 z y) = (term56 y z).
Proof. exact (TRANS (@lem1561049 z y) (@lem1561066 y z)). Qed.
Lemma lem1561068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561069 (x : real) (z : real) : (term57 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1561068) (@lem1561048 x z)). Qed.
Lemma lem1561070 (x : real) (y : real) (z : real) : (term1 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1561069 x z) (@lem1561067 y z)). Qed.
Lemma lem1561071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561072 (z : real) (x : real) (y : real) : (term3 z x y) = (term60 z x y).
Proof. exact (MK_COMB (@lem1561071) (@lem1561029 z x y)). Qed.
Lemma lem1561073 (x : real) (y : real) (z : real) : (term5 x z y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1561072 z x y) (@lem1561070 x y z)). Qed.
Lemma lem1561074 (z : real) (x : real) (y : real) : (term62 z x y) = (term63 z x y).
Proof. exact (@lem1483533 z (real_min x y)). Qed.
Lemma lem1561087 (z : real) (x : real) (y : real) : (term64 z x y) = (term65 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1561088 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561089 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1561088) (@lem1561087 z x y)). Qed.
Lemma lem1561090 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561091 (z : real) (x : real) (y : real) : (term63 z x y) = (term68 z x y).
Proof. exact (MK_COMB (@lem1561089 z x y) (@lem1561090)). Qed.
Lemma lem1561092 (z : real) (x : real) (y : real) : (term62 z x y) = (term68 z x y).
Proof. exact (TRANS (@lem1561074 z x y) (@lem1561091 z x y)). Qed.
Lemma lem1561093 (x : real) (z : real) : (real_le z x) = (term69 x z).
Proof. exact (@lem1483523 x z). Qed.
Lemma lem1561106 (x : real) (z : real) : (real_sub x z) = (term52 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1561107 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561108 (x : real) (z : real) : (term70 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1561107) (@lem1561106 x z)). Qed.
Lemma lem1561109 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561110 (x : real) (z : real) : (term69 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1561108 x z) (@lem1561109)). Qed.
Lemma lem1561111 (x : real) (z : real) : (real_le z x) = (term72 x z).
Proof. exact (TRANS (@lem1561093 x z) (@lem1561110 x z)). Qed.
Lemma lem1561112 (y : real) (z : real) : (real_le z y) = (term69 y z).
Proof. exact (@lem1483523 y z). Qed.
Lemma lem1561125 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1561126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561127 (y : real) (z : real) : (term70 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1561126) (@lem1561125 y z)). Qed.
Lemma lem1561128 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561129 (y : real) (z : real) : (term69 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1561127 y z) (@lem1561128)). Qed.
Lemma lem1561130 (y : real) (z : real) : (real_le z y) = (term72 y z).
Proof. exact (TRANS (@lem1561112 y z) (@lem1561129 y z)). Qed.
Lemma lem1561131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561132 (x : real) (z : real) : (term73 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1561131) (@lem1561111 x z)). Qed.
Lemma lem1561133 (x : real) (y : real) (z : real) : (term12 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1561132 x z) (@lem1561130 y z)). Qed.
Lemma lem1561134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561135 (z : real) (x : real) (y : real) : (term76 z x y) = (term77 z x y).
Proof. exact (MK_COMB (@lem1561134) (@lem1561092 z x y)). Qed.
Lemma lem1561136 (x : real) (y : real) (z : real) : (term2 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1561135 z x y) (@lem1561133 x y z)). Qed.
Lemma lem1561137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561138 (x : real) (y : real) (z : real) : (term7 x z y) = (term79 x y z).
Proof. exact (MK_COMB (@lem1561137) (@lem1561073 x y z)). Qed.
Lemma lem1561139 (x : real) (y : real) (z : real) : (term9 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1561138 x y z) (@lem1561136 x y z)). Qed.
Lemma lem1561140 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1561139 x y z)). Qed.
Lemma lem1561141 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561142 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1561141) (@lem1561140 x y)). Qed.
Lemma lem1561143 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1561142 x y)). Qed.
Lemma lem1561144 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561145 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1561144) (@lem1561143 x)). Qed.
Lemma lem1561146 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1561145 x)). Qed.
Lemma lem1561147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561148 : term40 = term86.
Proof. exact (MK_COMB (@lem1561147) (@lem1561146)). Qed.
Lemma lem1561149 : term32 = term86.
Proof. exact (TRANS (@lem1561010) (@lem1561148)). Qed.
Lemma lem1561159 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1561160 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1561159 real P Q). Qed.
Lemma lem1561161 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1561160 (term93 x y) (term94 x y)). Qed.
Lemma lem1561162 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1561163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561164 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1561163) (@lem1561162 x y z)). Qed.
Lemma lem1561165 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1561166 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1561164 x y z) (@lem1561165 x y z)). Qed.
Lemma lem1561167 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1561166 x y z)). Qed.
Lemma lem1561168 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561169 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1561168) (@lem1561167 x y)). Qed.
Lemma lem1561170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561171 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1561170) (@lem1561169 x y)). Qed.
Lemma lem1561172 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1561173 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1561172 x y z)). Qed.
Lemma lem1561174 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561175 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1561174) (@lem1561173 x y)). Qed.
Lemma lem1561176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561177 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1561176) (@lem1561175 x y)). Qed.
Lemma lem1561178 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1561179 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1561178 x y z)). Qed.
Lemma lem1561180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561181 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1561180) (@lem1561179 x y)). Qed.
Lemma lem1561182 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1561177 x y) (@lem1561181 x y)). Qed.
Lemma lem1561183 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1561171 x y) (@lem1561182 x y)). Qed.
Lemma lem1561184 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1561183 x y) (@lem1561161 x y)). Qed.
Lemma lem1561281 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1561184 x y)). Qed.
Lemma lem1561282 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561283 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1561282) (@lem1561281 x)). Qed.
Lemma lem1561285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1561286 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1561285 real P Q). Qed.
Lemma lem1561287 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1561286 (term115 x) (term116 x)). Qed.
Lemma lem1561288 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1561289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561290 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1561289) (@lem1561288 x y)). Qed.
Lemma lem1561291 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1561292 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1561290 x y) (@lem1561291 x y)). Qed.
Lemma lem1561293 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1561292 x y)). Qed.
Lemma lem1561294 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561295 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1561294) (@lem1561293 x)). Qed.
Lemma lem1561296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561297 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1561296) (@lem1561295 x)). Qed.
Lemma lem1561298 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1561299 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1561298 x y)). Qed.
Lemma lem1561300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561301 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1561300) (@lem1561299 x)). Qed.
Lemma lem1561302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561303 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1561302) (@lem1561301 x)). Qed.
Lemma lem1561304 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1561305 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1561304 x y)). Qed.
Lemma lem1561306 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561307 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1561306) (@lem1561305 x)). Qed.
Lemma lem1561308 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1561303 x) (@lem1561307 x)). Qed.
Lemma lem1561309 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1561297 x) (@lem1561308 x)). Qed.
Lemma lem1561310 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1561309 x) (@lem1561287 x)). Qed.
Lemma lem1561415 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1561283 x) (@lem1561310 x)). Qed.
Lemma lem1561416 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1561415 x)). Qed.
Lemma lem1561417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561418 : term86 = term134.
Proof. exact (MK_COMB (@lem1561417) (@lem1561416)). Qed.
Lemma lem1561420 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1561421 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1561420 real P Q). Qed.
Lemma lem1561422 : term135 = term136.
Proof. exact (@lem1561421 term137 term138). Qed.
Lemma lem1561423 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1561424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561425 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1561424) (@lem1561423 x)). Qed.
Lemma lem1561426 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1561427 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1561425 x) (@lem1561426 x)). Qed.
Lemma lem1561428 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1561427 x)). Qed.
Lemma lem1561429 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561430 : term135 = term134.
Proof. exact (MK_COMB (@lem1561429) (@lem1561428)). Qed.
Lemma lem1561431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561432 : term144 = term145.
Proof. exact (MK_COMB (@lem1561431) (@lem1561430)). Qed.
Lemma lem1561433 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1561434 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1561433 x)). Qed.
Lemma lem1561435 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561436 : term147 = term148.
Proof. exact (MK_COMB (@lem1561435) (@lem1561434)). Qed.
Lemma lem1561437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561438 : term149 = term150.
Proof. exact (MK_COMB (@lem1561437) (@lem1561436)). Qed.
Lemma lem1561439 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1561440 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1561439 x)). Qed.
Lemma lem1561441 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561442 : term152 = term153.
Proof. exact (MK_COMB (@lem1561441) (@lem1561440)). Qed.
Lemma lem1561443 : term136 = term154.
Proof. exact (MK_COMB (@lem1561438) (@lem1561442)). Qed.
Lemma lem1561444 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1561432) (@lem1561443)). Qed.
Lemma lem1561445 : term134 = term154.
Proof. exact (EQ_MP (@lem1561444) (@lem1561422)). Qed.
Lemma lem1561558 : term86 = term154.
Proof. exact (TRANS (@lem1561418) (@lem1561445)). Qed.
Lemma lem1561560 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1561561 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1561560 real P Q). Qed.
Lemma lem1561562 : term136 = term135.
Proof. exact (@lem1561561 term137 term138). Qed.
Lemma lem1561563 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1561564 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1561563 x)). Qed.
Lemma lem1561565 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561566 : term147 = term148.
Proof. exact (MK_COMB (@lem1561565) (@lem1561564)). Qed.
Lemma lem1561567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561568 : term149 = term150.
Proof. exact (MK_COMB (@lem1561567) (@lem1561566)). Qed.
Lemma lem1561569 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1561570 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1561569 x)). Qed.
Lemma lem1561571 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561572 : term152 = term153.
Proof. exact (MK_COMB (@lem1561571) (@lem1561570)). Qed.
Lemma lem1561573 : term136 = term154.
Proof. exact (MK_COMB (@lem1561568) (@lem1561572)). Qed.
Lemma lem1561574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561575 : term155 = term156.
Proof. exact (MK_COMB (@lem1561574) (@lem1561573)). Qed.
Lemma lem1561576 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1561577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561578 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1561577) (@lem1561576 x)). Qed.
Lemma lem1561579 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1561580 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1561578 x) (@lem1561579 x)). Qed.
Lemma lem1561581 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1561580 x)). Qed.
Lemma lem1561582 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561583 : term135 = term134.
Proof. exact (MK_COMB (@lem1561582) (@lem1561581)). Qed.
Lemma lem1561584 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1561575) (@lem1561583)). Qed.
Lemma lem1561585 : term154 = term134.
Proof. exact (EQ_MP (@lem1561584) (@lem1561562)). Qed.
Lemma lem1561587 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1561588 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1561587 real P Q). Qed.
Lemma lem1561589 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1561588 (term115 x) (term116 x)). Qed.
Lemma lem1561590 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1561591 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1561590 x y)). Qed.
Lemma lem1561592 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561593 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1561592) (@lem1561591 x)). Qed.
Lemma lem1561594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561595 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1561594) (@lem1561593 x)). Qed.
Lemma lem1561596 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1561597 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1561596 x y)). Qed.
Lemma lem1561598 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561599 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1561598) (@lem1561597 x)). Qed.
Lemma lem1561600 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1561595 x) (@lem1561599 x)). Qed.
Lemma lem1561601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561602 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1561601) (@lem1561600 x)). Qed.
Lemma lem1561603 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1561604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561605 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1561604) (@lem1561603 x y)). Qed.
Lemma lem1561606 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1561607 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1561605 x y) (@lem1561606 x y)). Qed.
Lemma lem1561608 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1561607 x y)). Qed.
Lemma lem1561609 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561610 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1561609) (@lem1561608 x)). Qed.
Lemma lem1561611 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1561602 x) (@lem1561610 x)). Qed.
Lemma lem1561612 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1561611 x) (@lem1561589 x)). Qed.
Lemma lem1561614 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1561615 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1561614 real P Q). Qed.
Lemma lem1561616 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1561615 (term93 x y) (term94 x y)). Qed.
Lemma lem1561617 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1561618 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1561617 x y z)). Qed.
Lemma lem1561619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561620 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1561619) (@lem1561618 x y)). Qed.
Lemma lem1561621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561622 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1561621) (@lem1561620 x y)). Qed.
Lemma lem1561623 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1561624 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1561623 x y z)). Qed.
Lemma lem1561625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561626 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1561625) (@lem1561624 x y)). Qed.
Lemma lem1561627 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1561622 x y) (@lem1561626 x y)). Qed.
Lemma lem1561628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1561629 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1561628) (@lem1561627 x y)). Qed.
Lemma lem1561630 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1561631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561632 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1561631) (@lem1561630 x y z)). Qed.
Lemma lem1561633 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1561634 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1561632 x y z) (@lem1561633 x y z)). Qed.
Lemma lem1561635 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1561634 x y z)). Qed.
Lemma lem1561636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561637 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1561636) (@lem1561635 x y)). Qed.
Lemma lem1561638 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1561629 x y) (@lem1561637 x y)). Qed.
Lemma lem1561639 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1561638 x y) (@lem1561616 x y)). Qed.
Lemma lem1561640 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1561639 x y)). Qed.
Lemma lem1561641 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561642 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1561641) (@lem1561640 x)). Qed.
Lemma lem1561643 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1561612 x) (@lem1561642 x)). Qed.
Lemma lem1561644 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1561643 x)). Qed.
Lemma lem1561645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561646 : term134 = term86.
Proof. exact (MK_COMB (@lem1561645) (@lem1561644)). Qed.
Lemma lem1561647 : term154 = term86.
Proof. exact (TRANS (@lem1561585) (@lem1561646)). Qed.
Lemma lem1561648 : term86 = term86.
Proof. exact (TRANS (@lem1561558) (@lem1561647)). Qed.
Lemma lem1561651 : term32 = term86.
Proof. exact (TRANS (@lem1561149) (@lem1561648)). Qed.
Lemma lem1561664 (x : real) (y : real) (z : real) : (term78 x y z) = (term78 x y z).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1561681 (x : real) (y : real) (z : real) : (term61 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term56 x z) (term49 z x y) (term56 y z)). Qed.
Lemma lem1561682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561683 (x : real) (y : real) (z : real) : (term79 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1561682) (@lem1561681 x y z)). Qed.
Lemma lem1561684 (x : real) (y : real) (z : real) : (term80 x y z) = (term163 x y z).
Proof. exact (MK_COMB (@lem1561683 x y z) (@lem1561664 x y z)). Qed.
Lemma lem1561685 (x : real) (y : real) : (term81 x y) = (term164 x y).
Proof. exact (fun_ext (fun z : real => @lem1561684 x y z)). Qed.
Lemma lem1561686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561687 (x : real) (y : real) : (term82 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1561686) (@lem1561685 x y)). Qed.
Lemma lem1561688 (x : real) : (term83 x) = (term166 x).
Proof. exact (fun_ext (fun y : real => @lem1561687 x y)). Qed.
Lemma lem1561689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561690 (x : real) : (term84 x) = (term167 x).
Proof. exact (MK_COMB (@lem1561689) (@lem1561688 x)). Qed.
Lemma lem1561691 : term85 = term168.
Proof. exact (fun_ext (fun x : real => @lem1561690 x)). Qed.
Lemma lem1561692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1561693 : term86 = term169.
Proof. exact (MK_COMB (@lem1561692) (@lem1561691)). Qed.
Lemma lem1561694 : term32 = term169.
Proof. exact (TRANS (@lem1561651) (@lem1561693)). Qed.
Lemma lem1561696 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1561697 (x : real) (z : real) (y : real) : (term49 z x y) = (term172 x z y).
Proof. exact (@lem1561696 x (term45 z) y term48). Qed.
Lemma lem1561710 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1561711 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561712 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1561711) (@lem1561710 y z)). Qed.
Lemma lem1561713 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561714 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1561712 y z) (@lem1561713)). Qed.
Lemma lem1561727 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1561728 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561729 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1561728) (@lem1561727 x z)). Qed.
Lemma lem1561730 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561731 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1561729 x z) (@lem1561730)). Qed.
Lemma lem1561732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561733 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1561732) (@lem1561731 x z)). Qed.
Lemma lem1561734 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1561733 x z) (@lem1561714 y z)). Qed.
Lemma lem1561735 (x : real) (y : real) (z : real) : (term49 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1561697 x z y) (@lem1561734 x y z)). Qed.
Lemma lem1561736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561737 (x : real) (y : real) (z : real) : (term60 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1561736) (@lem1561735 x y z)). Qed.
Lemma lem1561738 (x : real) (z : real) : (term56 x z) = (term56 x z).
Proof. exact (eq_refl (term56 x z)). Qed.
Lemma lem1561741 (y : real) (x : real) (z : real) : (term177 y x z) = (term178 y x z).
Proof. exact (MK_COMB (@lem1561737 x y z) (@lem1561738 x z)). Qed.
Lemma lem1561743 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1561744 (x : real) (z : real) (y : real) : (term49 z x y) = (term172 x z y).
Proof. exact (@lem1561743 x (term45 z) y term48). Qed.
Lemma lem1561757 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1561758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561759 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1561758) (@lem1561757 y z)). Qed.
Lemma lem1561760 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561761 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1561759 y z) (@lem1561760)). Qed.
Lemma lem1561774 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1561775 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561776 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1561775) (@lem1561774 x z)). Qed.
Lemma lem1561777 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561778 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1561776 x z) (@lem1561777)). Qed.
Lemma lem1561779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561780 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1561779) (@lem1561778 x z)). Qed.
Lemma lem1561781 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1561780 x z) (@lem1561761 y z)). Qed.
Lemma lem1561782 (x : real) (y : real) (z : real) : (term49 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1561744 x z y) (@lem1561781 x y z)). Qed.
Lemma lem1561783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561784 (x : real) (y : real) (z : real) : (term60 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1561783) (@lem1561782 x y z)). Qed.
Lemma lem1561785 (y : real) (z : real) : (term56 y z) = (term56 y z).
Proof. exact (eq_refl (term56 y z)). Qed.
Lemma lem1561788 (x : real) (y : real) (z : real) : (term179 x y z) = (term180 x y z).
Proof. exact (MK_COMB (@lem1561784 x y z) (@lem1561785 y z)). Qed.
Lemma lem1561789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561790 (y : real) (x : real) (z : real) : (term181 y x z) = (term182 y x z).
Proof. exact (MK_COMB (@lem1561789) (@lem1561741 y x z)). Qed.
Lemma lem1561791 (x : real) (y : real) (z : real) : (term161 x y z) = (term183 x y z).
Proof. exact (MK_COMB (@lem1561790 y x z) (@lem1561788 x y z)). Qed.
Lemma lem1561793 (x : real) (y : real) (z : real) : (term184 z x y) = (term78 x y z).
Proof. exact (eq_refl (term184 z x y)). Qed.
Lemma lem1561794 (z : real) (x : real) (y : real) : (term78 x y z) = (term184 z x y).
Proof. exact (SYM (@lem1561793 x y z)). Qed.
Lemma lem1561795 (x : real) (z : real) (y : real) : (term184 z x y) = (term185 x z y).
Proof. exact (@lem1483429 x (term186 x y z) y). Qed.
Lemma lem1561796 (x : real) (z : real) (y : real) : (term78 x y z) = (term185 x z y).
Proof. exact (TRANS (@lem1561794 z x y) (@lem1561795 x z y)). Qed.
Lemma lem1561797 (x : real) (y : real) (z : real) : (term187 x z y) = (term188 x y z).
Proof. exact (eq_refl (term187 x z y)). Qed.
Lemma lem1561798 (x : real) (y : real) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1561799 (x : real) (y : real) (z : real) : (term190 x z y) = (term191 x y z).
Proof. exact (MK_COMB (@lem1561798 x y) (@lem1561797 x y z)). Qed.
Lemma lem1561800 (x : real) (y : real) (z : real) : (term192 y z x) = (term193 x y z).
Proof. exact (eq_refl (term192 y z x)). Qed.
Lemma lem1561801 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1561802 (x : real) (y : real) (z : real) : (term195 y z x) = (term196 x y z).
Proof. exact (MK_COMB (@lem1561801 y x) (@lem1561800 x y z)). Qed.
Lemma lem1561803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561804 (x : real) (y : real) (z : real) : (term197 y z x) = (term198 x y z).
Proof. exact (MK_COMB (@lem1561803) (@lem1561802 x y z)). Qed.
Lemma lem1561805 (x : real) (y : real) (z : real) : (term185 x z y) = (term199 x y z).
Proof. exact (MK_COMB (@lem1561804 x y z) (@lem1561799 x y z)). Qed.
Lemma lem1561806 (x : real) (y : real) (z : real) : (term200 x y z) = (term200 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1561807 (x : real) (y : real) (z : real) : ((term78 x y z) = (term185 x z y)) = ((term78 x y z) = (term199 x y z)).
Proof. exact (MK_COMB (@lem1561806 x y z) (@lem1561805 x y z)). Qed.
Lemma lem1561808 (x : real) (y : real) (z : real) : (term78 x y z) = (term199 x y z).
Proof. exact (EQ_MP (@lem1561807 x y z) (@lem1561796 x z y)). Qed.
Lemma lem1561809 (y : real) (x : real) : (real_ge y x) = (term69 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1561815 (y : real) (x : real) : (real_sub y x) = (term52 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1561820 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (@lem1483488 (term45 x) y). Qed.
Lemma lem1561822 (x : real) (y : real) : (real_sub y x) = (term53 x y).
Proof. exact (TRANS (@lem1561815 y x) (@lem1561820 x y)). Qed.
Lemma lem1561823 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561824 (x : real) (y : real) : (term70 y x) = (term173 x y).
Proof. exact (MK_COMB (@lem1561823) (@lem1561822 x y)). Qed.
Lemma lem1561825 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561826 (x : real) (y : real) : (term69 y x) = (term174 x y).
Proof. exact (MK_COMB (@lem1561824 x y) (@lem1561825)). Qed.
Lemma lem1561827 (x : real) (y : real) : (real_ge y x) = (term174 x y).
Proof. exact (TRANS (@lem1561809 y x) (@lem1561826 x y)). Qed.
Lemma lem1561828 (z : real) (x : real) : (term201 z x) = (term202 z x).
Proof. exact (@lem1483525 (term52 z x) term48). Qed.
Lemma lem1561829 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561842 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1561843 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1561844 (x : real) (z : real) : (term203 z x) = (term204 x z).
Proof. exact (MK_COMB (@lem1561843) (@lem1561842 x z)). Qed.
Lemma lem1561845 (x : real) (z : real) : (term205 z x) = (term206 x z).
Proof. exact (MK_COMB (@lem1561844 x z) (@lem1561829)). Qed.
Lemma lem1561846 (x : real) (z : real) : (term206 x z) = (term207 x z).
Proof. exact (@lem1483519 (term53 x z) term48). Qed.
Lemma lem1561848 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1561849 : term209 = term48.
Proof. exact (@lem1561848 term210). Qed.
Lemma lem1561850 (x : real) (z : real) : (term211 x z) = (term211 x z).
Proof. exact (eq_refl (term211 x z)). Qed.
Lemma lem1561851 (x : real) (z : real) : (term207 x z) = (term212 x z).
Proof. exact (MK_COMB (@lem1561850 x z) (@lem1561849)). Qed.
Lemma lem1561852 (x : real) (z : real) : (term212 x z) = (term53 x z).
Proof. exact (@lem1483450 (term53 x z)). Qed.
Lemma lem1561853 (x : real) (z : real) : (term207 x z) = (term53 x z).
Proof. exact (TRANS (@lem1561851 x z) (@lem1561852 x z)). Qed.
Lemma lem1561854 (x : real) (z : real) : (term206 x z) = (term53 x z).
Proof. exact (TRANS (@lem1561846 x z) (@lem1561853 x z)). Qed.
Lemma lem1561855 (x : real) (z : real) : (term205 z x) = (term53 x z).
Proof. exact (TRANS (@lem1561845 x z) (@lem1561854 x z)). Qed.
Lemma lem1561856 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561857 (x : real) (z : real) : (term213 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1561856) (@lem1561855 x z)). Qed.
Lemma lem1561858 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561859 (x : real) (z : real) : (term202 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1561857 x z) (@lem1561858)). Qed.
Lemma lem1561860 (x : real) (z : real) : (term201 z x) = (term56 x z).
Proof. exact (TRANS (@lem1561828 z x) (@lem1561859 x z)). Qed.
Lemma lem1561861 (x : real) (z : real) : (term72 x z) = (term214 x z).
Proof. exact (@lem1483527 (term52 x z) term48). Qed.
Lemma lem1561879 (x : real) (z : real) : (term205 x z) = (term215 x z).
Proof. exact (@lem1483519 (term52 x z) term48). Qed.
Lemma lem1561881 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1561882 : term209 = term48.
Proof. exact (@lem1561881 term210). Qed.
Lemma lem1561883 (x : real) (z : real) : (term216 x z) = (term216 x z).
Proof. exact (eq_refl (term216 x z)). Qed.
Lemma lem1561884 (x : real) (z : real) : (term215 x z) = (term217 x z).
Proof. exact (MK_COMB (@lem1561883 x z) (@lem1561882)). Qed.
Lemma lem1561885 (x : real) (z : real) : (term217 x z) = (term52 x z).
Proof. exact (@lem1483450 (term52 x z)). Qed.
Lemma lem1561886 (x : real) (z : real) : (term215 x z) = (term52 x z).
Proof. exact (TRANS (@lem1561884 x z) (@lem1561885 x z)). Qed.
Lemma lem1561888 (x : real) (z : real) : (term205 x z) = (term52 x z).
Proof. exact (TRANS (@lem1561879 x z) (@lem1561886 x z)). Qed.
Lemma lem1561889 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561890 (x : real) (z : real) : (term218 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1561889) (@lem1561888 x z)). Qed.
Lemma lem1561891 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561892 (x : real) (z : real) : (term214 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1561890 x z) (@lem1561891)). Qed.
Lemma lem1561893 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (TRANS (@lem1561861 x z) (@lem1561892 x z)). Qed.
Lemma lem1561894 (y : real) (z : real) : (term72 y z) = (term214 y z).
Proof. exact (@lem1483527 (term52 y z) term48). Qed.
Lemma lem1561912 (y : real) (z : real) : (term205 y z) = (term215 y z).
Proof. exact (@lem1483519 (term52 y z) term48). Qed.
Lemma lem1561914 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1561915 : term209 = term48.
Proof. exact (@lem1561914 term210). Qed.
Lemma lem1561916 (y : real) (z : real) : (term216 y z) = (term216 y z).
Proof. exact (eq_refl (term216 y z)). Qed.
Lemma lem1561917 (y : real) (z : real) : (term215 y z) = (term217 y z).
Proof. exact (MK_COMB (@lem1561916 y z) (@lem1561915)). Qed.
Lemma lem1561918 (y : real) (z : real) : (term217 y z) = (term52 y z).
Proof. exact (@lem1483450 (term52 y z)). Qed.
Lemma lem1561919 (y : real) (z : real) : (term215 y z) = (term52 y z).
Proof. exact (TRANS (@lem1561917 y z) (@lem1561918 y z)). Qed.
Lemma lem1561921 (y : real) (z : real) : (term205 y z) = (term52 y z).
Proof. exact (TRANS (@lem1561912 y z) (@lem1561919 y z)). Qed.
Lemma lem1561922 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1561923 (y : real) (z : real) : (term218 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1561922) (@lem1561921 y z)). Qed.
Lemma lem1561924 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561925 (y : real) (z : real) : (term214 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1561923 y z) (@lem1561924)). Qed.
Lemma lem1561926 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (TRANS (@lem1561894 y z) (@lem1561925 y z)). Qed.
Lemma lem1561927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561928 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1561927) (@lem1561893 x z)). Qed.
Lemma lem1561929 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1561928 x z) (@lem1561926 y z)). Qed.
Lemma lem1561930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561931 (x : real) (z : real) : (term219 z x) = (term220 x z).
Proof. exact (MK_COMB (@lem1561930) (@lem1561860 x z)). Qed.
Lemma lem1561932 (x : real) (y : real) (z : real) : (term193 x y z) = (term221 x y z).
Proof. exact (MK_COMB (@lem1561931 x z) (@lem1561929 x y z)). Qed.
Lemma lem1561933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561934 (x : real) (y : real) : (term194 y x) = (term175 x y).
Proof. exact (MK_COMB (@lem1561933) (@lem1561827 x y)). Qed.
Lemma lem1561935 (x : real) (y : real) (z : real) : (term196 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1561934 x y) (@lem1561932 x y z)). Qed.
Lemma lem1561936 (x : real) (y : real) : (real_gt x y) = (term51 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1561949 (x : real) (y : real) : (real_sub x y) = (term52 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1561950 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561951 (x : real) (y : real) : (term54 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1561950) (@lem1561949 x y)). Qed.
Lemma lem1561952 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561953 (x : real) (y : real) : (term51 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1561951 x y) (@lem1561952)). Qed.
Lemma lem1561954 (x : real) (y : real) : (real_gt x y) = (term201 x y).
Proof. exact (TRANS (@lem1561936 x y) (@lem1561953 x y)). Qed.
Lemma lem1561955 (z : real) (y : real) : (term201 z y) = (term202 z y).
Proof. exact (@lem1483525 (term52 z y) term48). Qed.
Lemma lem1561956 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561969 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1561970 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1561971 (y : real) (z : real) : (term203 z y) = (term204 y z).
Proof. exact (MK_COMB (@lem1561970) (@lem1561969 y z)). Qed.
Lemma lem1561972 (y : real) (z : real) : (term205 z y) = (term206 y z).
Proof. exact (MK_COMB (@lem1561971 y z) (@lem1561956)). Qed.
Lemma lem1561973 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483519 (term53 y z) term48). Qed.
Lemma lem1561975 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1561976 : term209 = term48.
Proof. exact (@lem1561975 term210). Qed.
Lemma lem1561977 (y : real) (z : real) : (term211 y z) = (term211 y z).
Proof. exact (eq_refl (term211 y z)). Qed.
Lemma lem1561978 (y : real) (z : real) : (term207 y z) = (term212 y z).
Proof. exact (MK_COMB (@lem1561977 y z) (@lem1561976)). Qed.
Lemma lem1561979 (y : real) (z : real) : (term212 y z) = (term53 y z).
Proof. exact (@lem1483450 (term53 y z)). Qed.
Lemma lem1561980 (y : real) (z : real) : (term207 y z) = (term53 y z).
Proof. exact (TRANS (@lem1561978 y z) (@lem1561979 y z)). Qed.
Lemma lem1561981 (y : real) (z : real) : (term206 y z) = (term53 y z).
Proof. exact (TRANS (@lem1561973 y z) (@lem1561980 y z)). Qed.
Lemma lem1561982 (y : real) (z : real) : (term205 z y) = (term53 y z).
Proof. exact (TRANS (@lem1561972 y z) (@lem1561981 y z)). Qed.
Lemma lem1561983 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1561984 (y : real) (z : real) : (term213 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1561983) (@lem1561982 y z)). Qed.
Lemma lem1561985 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1561986 (y : real) (z : real) : (term202 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1561984 y z) (@lem1561985)). Qed.
Lemma lem1561987 (y : real) (z : real) : (term201 z y) = (term56 y z).
Proof. exact (TRANS (@lem1561955 z y) (@lem1561986 y z)). Qed.
Lemma lem1561988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561989 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1561988) (@lem1561893 x z)). Qed.
Lemma lem1561990 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1561989 x z) (@lem1561926 y z)). Qed.
Lemma lem1561991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561992 (y : real) (z : real) : (term219 z y) = (term220 y z).
Proof. exact (MK_COMB (@lem1561991) (@lem1561987 y z)). Qed.
Lemma lem1561993 (x : real) (y : real) (z : real) : (term188 x y z) = (term224 x y z).
Proof. exact (MK_COMB (@lem1561992 y z) (@lem1561990 x y z)). Qed.
Lemma lem1561994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1561995 (x : real) (y : real) : (term189 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1561994) (@lem1561954 x y)). Qed.
Lemma lem1561996 (x : real) (y : real) (z : real) : (term191 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1561995 x y) (@lem1561993 x y z)). Qed.
Lemma lem1561997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1561998 (x : real) (y : real) (z : real) : (term198 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1561997) (@lem1561935 x y z)). Qed.
Lemma lem1561999 (x : real) (y : real) (z : real) : (term199 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1561998 x y z) (@lem1561996 x y z)). Qed.
Lemma lem1562011 (x : real) (y : real) (z : real) : (term78 x y z) = (term227 x y z).
Proof. exact (TRANS (@lem1561808 x y z) (@lem1561999 x y z)). Qed.
Lemma lem1562012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562013 (x : real) (y : real) (z : real) : (term162 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1562012) (@lem1561791 x y z)). Qed.
Lemma lem1562014 (x : real) (y : real) (z : real) : (term163 x y z) = (term229 x y z).
Proof. exact (MK_COMB (@lem1562013 x y z) (@lem1562011 x y z)). Qed.
Lemma lem1562015 (x : real) (y : real) (z : real) (h1 : term229 x y z) : term229 x y z.
Proof. exact (h1). Qed.
Lemma lem1562016 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1562017 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term178 y x z.
Proof. exact (h1). Qed.
Lemma lem1562018 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term56 x z.
Proof. exact (proj2 (@lem1562017 y x z h1)). Qed.
Lemma lem1562019 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term75 x y z.
Proof. exact (proj1 (@lem1562017 y x z h1)). Qed.
Lemma lem1562021 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (proj1 (@lem1562019 y x z h1)). Qed.
Lemma lem1562023 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562024 : term231 = term232.
Proof. exact (@lem1562023 (NUMERAL 0) term210). Qed.
Lemma lem1562025 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562026 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562027 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562026 h1) (fun h1 : term232 = True => @lem1562025)). Qed.
Lemma lem1562028 : term232 = True.
Proof. exact (EQ_MP (@lem1562027) (@lem1562025)). Qed.
Lemma lem1562029 : term231 = True.
Proof. exact (TRANS (@lem1562024) (@lem1562028)). Qed.
Lemma lem1562030 : True = term231.
Proof. exact (SYM (@lem1562029)). Qed.
Lemma lem1562031 : term231.
Proof. exact (EQ_MP (@lem1562030) (@lem0)). Qed.
Lemma lem1562032 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term234 x z.
Proof. exact (conj (@lem1562031) (@lem1562021 y x z h1)). Qed.
Lemma lem1562034 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1562035 (x : real) (z : real) : term236 x z.
Proof. exact (@lem1562034 term237 (term52 x z)). Qed.
Lemma lem1562036 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term238 x z.
Proof. exact (@lem1562035 x z (@lem1562032 y x z h1)). Qed.
Lemma lem1562037 (x : real) (z : real) : (term239 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1562038 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562039 (x : real) (z : real) : (term240 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1562038) (@lem1562037 x z)). Qed.
Lemma lem1562040 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562041 (x : real) (z : real) : (term238 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1562039 x z) (@lem1562040)). Qed.
Lemma lem1562042 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1562041 x z) (@lem1562036 y x z h1)). Qed.
Lemma lem1562044 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562045 : term231 = term232.
Proof. exact (@lem1562044 (NUMERAL 0) term210). Qed.
Lemma lem1562046 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562047 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562048 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562047 h1) (fun h1 : term232 = True => @lem1562046)). Qed.
Lemma lem1562049 : term232 = True.
Proof. exact (EQ_MP (@lem1562048) (@lem1562046)). Qed.
Lemma lem1562050 : term231 = True.
Proof. exact (TRANS (@lem1562045) (@lem1562049)). Qed.
Lemma lem1562051 : True = term231.
Proof. exact (SYM (@lem1562050)). Qed.
Lemma lem1562052 : term231.
Proof. exact (EQ_MP (@lem1562051) (@lem0)). Qed.
Lemma lem1562053 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term241 x z.
Proof. exact (conj (@lem1562052) (@lem1562018 y x z h1)). Qed.
Lemma lem1562055 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1562056 (x : real) (z : real) : term243 x z.
Proof. exact (@lem1562055 term237 (term53 x z)). Qed.
Lemma lem1562057 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term244 x z.
Proof. exact (@lem1562056 x z (@lem1562053 y x z h1)). Qed.
Lemma lem1562058 (x : real) (z : real) : (term245 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1562059 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562060 (x : real) (z : real) : (term246 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1562059) (@lem1562058 x z)). Qed.
Lemma lem1562061 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562062 (x : real) (z : real) : (term244 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1562060 x z) (@lem1562061)). Qed.
Lemma lem1562063 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term56 x z.
Proof. exact (EQ_MP (@lem1562062 x z) (@lem1562057 y x z h1)). Qed.
Lemma lem1562064 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term247 x z.
Proof. exact (conj (@lem1562063 y x z h1) (@lem1562042 y x z h1)). Qed.
Lemma lem1562066 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1562067 (x : real) (z : real) : term249 x z.
Proof. exact (@lem1562066 (term53 x z) (term52 x z)). Qed.
Lemma lem1562068 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term250 x z.
Proof. exact (@lem1562067 x z (@lem1562064 y x z h1)). Qed.
Lemma lem1562069 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483480 (term45 x) x z (term45 z)). Qed.
Lemma lem1562070 (x : real) : (term253 x) = (term254 x).
Proof. exact (@lem1483440 term255 x). Qed.
Lemma lem1562072 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562073 : term257 = term48.
Proof. exact (@lem1562072 term210). Qed.
Lemma lem1562074 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562075 : term258 = term259.
Proof. exact (MK_COMB (@lem1562074) (@lem1562073)). Qed.
Lemma lem1562076 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1562077 (x : real) : (term254 x) = (term260 x).
Proof. exact (MK_COMB (@lem1562075) (@lem1562076 x)). Qed.
Lemma lem1562078 (x : real) : (term253 x) = (term260 x).
Proof. exact (TRANS (@lem1562070 x) (@lem1562077 x)). Qed.
Lemma lem1562079 (x : real) : (term260 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1562080 (x : real) : (term253 x) = term48.
Proof. exact (TRANS (@lem1562078 x) (@lem1562079 x)). Qed.
Lemma lem1562081 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1562082 (x : real) : (term261 x) = term262.
Proof. exact (MK_COMB (@lem1562081) (@lem1562080 x)). Qed.
Lemma lem1562083 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1562085 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562086 : term257 = term48.
Proof. exact (@lem1562085 term210). Qed.
Lemma lem1562087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562088 : term258 = term259.
Proof. exact (MK_COMB (@lem1562087) (@lem1562086)). Qed.
Lemma lem1562089 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1562090 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1562088) (@lem1562089 z)). Qed.
Lemma lem1562091 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1562083 z) (@lem1562090 z)). Qed.
Lemma lem1562092 (z : real) : (term260 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1562093 (z : real) : (term263 z) = term48.
Proof. exact (TRANS (@lem1562091 z) (@lem1562092 z)). Qed.
Lemma lem1562094 (x : real) (z : real) : (term252 x z) = term264.
Proof. exact (MK_COMB (@lem1562082 x) (@lem1562093 z)). Qed.
Lemma lem1562095 (x : real) (z : real) : (term251 x z) = term264.
Proof. exact (TRANS (@lem1562069 x z) (@lem1562094 x z)). Qed.
Lemma lem1562096 : term264 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1562097 (x : real) (z : real) : (term251 x z) = term48.
Proof. exact (TRANS (@lem1562095 x z) (@lem1562096)). Qed.
Lemma lem1562098 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562099 (x : real) (z : real) : (term265 x z) = term266.
Proof. exact (MK_COMB (@lem1562098) (@lem1562097 x z)). Qed.
Lemma lem1562100 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562101 (x : real) (z : real) : (term250 x z) = term267.
Proof. exact (MK_COMB (@lem1562099 x z) (@lem1562100)). Qed.
Lemma lem1562102 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term267.
Proof. exact (EQ_MP (@lem1562101 x z) (@lem1562068 y x z h1)). Qed.
Lemma lem1562104 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562105 : term267 = term268.
Proof. exact (@lem1562104 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1562106 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1562107 : term267 = False.
Proof. exact (TRANS (@lem1562105) (@lem1562106)). Qed.
Lemma lem1562108 (y : real) (x : real) (z : real) (h1 : term178 y x z) : False.
Proof. exact (EQ_MP (@lem1562107) (@lem1562102 y x z h1)). Qed.
Lemma lem1562109 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term180 x y z.
Proof. exact (h1). Qed.
Lemma lem1562110 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term56 y z.
Proof. exact (proj2 (@lem1562109 x y z h1)). Qed.
Lemma lem1562111 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term75 x y z.
Proof. exact (proj1 (@lem1562109 x y z h1)). Qed.
Lemma lem1562112 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (proj2 (@lem1562111 x y z h1)). Qed.
Lemma lem1562115 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562116 : term231 = term232.
Proof. exact (@lem1562115 (NUMERAL 0) term210). Qed.
Lemma lem1562117 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562118 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562119 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562118 h1) (fun h1 : term232 = True => @lem1562117)). Qed.
Lemma lem1562120 : term232 = True.
Proof. exact (EQ_MP (@lem1562119) (@lem1562117)). Qed.
Lemma lem1562121 : term231 = True.
Proof. exact (TRANS (@lem1562116) (@lem1562120)). Qed.
Lemma lem1562122 : True = term231.
Proof. exact (SYM (@lem1562121)). Qed.
Lemma lem1562123 : term231.
Proof. exact (EQ_MP (@lem1562122) (@lem0)). Qed.
Lemma lem1562124 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term234 y z.
Proof. exact (conj (@lem1562123) (@lem1562112 x y z h1)). Qed.
Lemma lem1562126 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1562127 (y : real) (z : real) : term236 y z.
Proof. exact (@lem1562126 term237 (term52 y z)). Qed.
Lemma lem1562128 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term238 y z.
Proof. exact (@lem1562127 y z (@lem1562124 x y z h1)). Qed.
Lemma lem1562129 (y : real) (z : real) : (term239 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1562130 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562131 (y : real) (z : real) : (term240 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1562130) (@lem1562129 y z)). Qed.
Lemma lem1562132 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562133 (y : real) (z : real) : (term238 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1562131 y z) (@lem1562132)). Qed.
Lemma lem1562134 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1562133 y z) (@lem1562128 x y z h1)). Qed.
Lemma lem1562136 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562137 : term231 = term232.
Proof. exact (@lem1562136 (NUMERAL 0) term210). Qed.
Lemma lem1562138 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562139 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562140 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562139 h1) (fun h1 : term232 = True => @lem1562138)). Qed.
Lemma lem1562141 : term232 = True.
Proof. exact (EQ_MP (@lem1562140) (@lem1562138)). Qed.
Lemma lem1562142 : term231 = True.
Proof. exact (TRANS (@lem1562137) (@lem1562141)). Qed.
Lemma lem1562143 : True = term231.
Proof. exact (SYM (@lem1562142)). Qed.
Lemma lem1562144 : term231.
Proof. exact (EQ_MP (@lem1562143) (@lem0)). Qed.
Lemma lem1562145 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term241 y z.
Proof. exact (conj (@lem1562144) (@lem1562110 x y z h1)). Qed.
Lemma lem1562147 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1562148 (y : real) (z : real) : term243 y z.
Proof. exact (@lem1562147 term237 (term53 y z)). Qed.
Lemma lem1562149 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term244 y z.
Proof. exact (@lem1562148 y z (@lem1562145 x y z h1)). Qed.
Lemma lem1562150 (y : real) (z : real) : (term245 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1562151 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562152 (y : real) (z : real) : (term246 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1562151) (@lem1562150 y z)). Qed.
Lemma lem1562153 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562154 (y : real) (z : real) : (term244 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1562152 y z) (@lem1562153)). Qed.
Lemma lem1562155 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1562154 y z) (@lem1562149 x y z h1)). Qed.
Lemma lem1562156 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term247 y z.
Proof. exact (conj (@lem1562155 x y z h1) (@lem1562134 x y z h1)). Qed.
Lemma lem1562158 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1562159 (y : real) (z : real) : term249 y z.
Proof. exact (@lem1562158 (term53 y z) (term52 y z)). Qed.
Lemma lem1562160 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term250 y z.
Proof. exact (@lem1562159 y z (@lem1562156 x y z h1)). Qed.
Lemma lem1562161 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483480 (term45 y) y z (term45 z)). Qed.
Lemma lem1562162 (y : real) : (term253 y) = (term254 y).
Proof. exact (@lem1483440 term255 y). Qed.
Lemma lem1562164 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562165 : term257 = term48.
Proof. exact (@lem1562164 term210). Qed.
Lemma lem1562166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562167 : term258 = term259.
Proof. exact (MK_COMB (@lem1562166) (@lem1562165)). Qed.
Lemma lem1562168 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1562169 (y : real) : (term254 y) = (term260 y).
Proof. exact (MK_COMB (@lem1562167) (@lem1562168 y)). Qed.
Lemma lem1562170 (y : real) : (term253 y) = (term260 y).
Proof. exact (TRANS (@lem1562162 y) (@lem1562169 y)). Qed.
Lemma lem1562171 (y : real) : (term260 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1562172 (y : real) : (term253 y) = term48.
Proof. exact (TRANS (@lem1562170 y) (@lem1562171 y)). Qed.
Lemma lem1562173 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1562174 (y : real) : (term261 y) = term262.
Proof. exact (MK_COMB (@lem1562173) (@lem1562172 y)). Qed.
Lemma lem1562175 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1562177 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562178 : term257 = term48.
Proof. exact (@lem1562177 term210). Qed.
Lemma lem1562179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562180 : term258 = term259.
Proof. exact (MK_COMB (@lem1562179) (@lem1562178)). Qed.
Lemma lem1562181 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1562182 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1562180) (@lem1562181 z)). Qed.
Lemma lem1562183 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1562175 z) (@lem1562182 z)). Qed.
Lemma lem1562184 (z : real) : (term260 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1562185 (z : real) : (term263 z) = term48.
Proof. exact (TRANS (@lem1562183 z) (@lem1562184 z)). Qed.
Lemma lem1562186 (y : real) (z : real) : (term252 y z) = term264.
Proof. exact (MK_COMB (@lem1562174 y) (@lem1562185 z)). Qed.
Lemma lem1562187 (y : real) (z : real) : (term251 y z) = term264.
Proof. exact (TRANS (@lem1562161 y z) (@lem1562186 y z)). Qed.
Lemma lem1562188 : term264 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1562189 (y : real) (z : real) : (term251 y z) = term48.
Proof. exact (TRANS (@lem1562187 y z) (@lem1562188)). Qed.
Lemma lem1562190 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562191 (y : real) (z : real) : (term265 y z) = term266.
Proof. exact (MK_COMB (@lem1562190) (@lem1562189 y z)). Qed.
Lemma lem1562192 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562193 (y : real) (z : real) : (term250 y z) = term267.
Proof. exact (MK_COMB (@lem1562191 y z) (@lem1562192)). Qed.
Lemma lem1562194 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term267.
Proof. exact (EQ_MP (@lem1562193 y z) (@lem1562160 x y z h1)). Qed.
Lemma lem1562196 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562197 : term267 = term268.
Proof. exact (@lem1562196 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1562198 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1562199 : term267 = False.
Proof. exact (TRANS (@lem1562197) (@lem1562198)). Qed.
Lemma lem1562200 (x : real) (y : real) (z : real) (h1 : term180 x y z) : False.
Proof. exact (EQ_MP (@lem1562199) (@lem1562194 x y z h1)). Qed.
Lemma lem1562201 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1562016 x y z h1) (fun h0 : term178 y x z => @lem1562108 y x z h0) (fun h0 : term180 x y z => @lem1562200 x y z h0)). Qed.
Lemma lem1562202 (x : real) (y : real) (z : real) (h1 : term227 x y z) : term227 x y z.
Proof. exact (h1). Qed.
Lemma lem1562203 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1562204 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term221 x y z.
Proof. exact (proj2 (@lem1562203 x y z h1)). Qed.
Lemma lem1562206 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1562204 x y z h1)). Qed.
Lemma lem1562207 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 x z.
Proof. exact (proj1 (@lem1562204 x y z h1)). Qed.
Lemma lem1562209 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 x z.
Proof. exact (proj1 (@lem1562206 x y z h1)). Qed.
Lemma lem1562211 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562212 : term231 = term232.
Proof. exact (@lem1562211 (NUMERAL 0) term210). Qed.
Lemma lem1562213 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562214 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562215 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562214 h1) (fun h1 : term232 = True => @lem1562213)). Qed.
Lemma lem1562216 : term232 = True.
Proof. exact (EQ_MP (@lem1562215) (@lem1562213)). Qed.
Lemma lem1562217 : term231 = True.
Proof. exact (TRANS (@lem1562212) (@lem1562216)). Qed.
Lemma lem1562218 : True = term231.
Proof. exact (SYM (@lem1562217)). Qed.
Lemma lem1562219 : term231.
Proof. exact (EQ_MP (@lem1562218) (@lem0)). Qed.
Lemma lem1562220 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term234 x z.
Proof. exact (conj (@lem1562219) (@lem1562209 x y z h1)). Qed.
Lemma lem1562222 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1562223 (x : real) (z : real) : term236 x z.
Proof. exact (@lem1562222 term237 (term52 x z)). Qed.
Lemma lem1562224 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term238 x z.
Proof. exact (@lem1562223 x z (@lem1562220 x y z h1)). Qed.
Lemma lem1562225 (x : real) (z : real) : (term239 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1562226 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562227 (x : real) (z : real) : (term240 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1562226) (@lem1562225 x z)). Qed.
Lemma lem1562228 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562229 (x : real) (z : real) : (term238 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1562227 x z) (@lem1562228)). Qed.
Lemma lem1562230 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1562229 x z) (@lem1562224 x y z h1)). Qed.
Lemma lem1562232 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562233 : term231 = term232.
Proof. exact (@lem1562232 (NUMERAL 0) term210). Qed.
Lemma lem1562234 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562235 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562236 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562235 h1) (fun h1 : term232 = True => @lem1562234)). Qed.
Lemma lem1562237 : term232 = True.
Proof. exact (EQ_MP (@lem1562236) (@lem1562234)). Qed.
Lemma lem1562238 : term231 = True.
Proof. exact (TRANS (@lem1562233) (@lem1562237)). Qed.
Lemma lem1562239 : True = term231.
Proof. exact (SYM (@lem1562238)). Qed.
Lemma lem1562240 : term231.
Proof. exact (EQ_MP (@lem1562239) (@lem0)). Qed.
Lemma lem1562241 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term241 x z.
Proof. exact (conj (@lem1562240) (@lem1562207 x y z h1)). Qed.
Lemma lem1562243 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1562244 (x : real) (z : real) : term243 x z.
Proof. exact (@lem1562243 term237 (term53 x z)). Qed.
Lemma lem1562245 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term244 x z.
Proof. exact (@lem1562244 x z (@lem1562241 x y z h1)). Qed.
Lemma lem1562246 (x : real) (z : real) : (term245 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1562247 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562248 (x : real) (z : real) : (term246 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1562247) (@lem1562246 x z)). Qed.
Lemma lem1562249 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562250 (x : real) (z : real) : (term244 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1562248 x z) (@lem1562249)). Qed.
Lemma lem1562251 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 x z.
Proof. exact (EQ_MP (@lem1562250 x z) (@lem1562245 x y z h1)). Qed.
Lemma lem1562252 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term247 x z.
Proof. exact (conj (@lem1562251 x y z h1) (@lem1562230 x y z h1)). Qed.
Lemma lem1562254 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1562255 (x : real) (z : real) : term249 x z.
Proof. exact (@lem1562254 (term53 x z) (term52 x z)). Qed.
Lemma lem1562256 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term250 x z.
Proof. exact (@lem1562255 x z (@lem1562252 x y z h1)). Qed.
Lemma lem1562257 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483480 (term45 x) x z (term45 z)). Qed.
Lemma lem1562258 (x : real) : (term253 x) = (term254 x).
Proof. exact (@lem1483440 term255 x). Qed.
Lemma lem1562260 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562261 : term257 = term48.
Proof. exact (@lem1562260 term210). Qed.
Lemma lem1562262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562263 : term258 = term259.
Proof. exact (MK_COMB (@lem1562262) (@lem1562261)). Qed.
Lemma lem1562264 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1562265 (x : real) : (term254 x) = (term260 x).
Proof. exact (MK_COMB (@lem1562263) (@lem1562264 x)). Qed.
Lemma lem1562266 (x : real) : (term253 x) = (term260 x).
Proof. exact (TRANS (@lem1562258 x) (@lem1562265 x)). Qed.
Lemma lem1562267 (x : real) : (term260 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1562268 (x : real) : (term253 x) = term48.
Proof. exact (TRANS (@lem1562266 x) (@lem1562267 x)). Qed.
Lemma lem1562269 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1562270 (x : real) : (term261 x) = term262.
Proof. exact (MK_COMB (@lem1562269) (@lem1562268 x)). Qed.
Lemma lem1562271 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1562273 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562274 : term257 = term48.
Proof. exact (@lem1562273 term210). Qed.
Lemma lem1562275 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562276 : term258 = term259.
Proof. exact (MK_COMB (@lem1562275) (@lem1562274)). Qed.
Lemma lem1562277 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1562278 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1562276) (@lem1562277 z)). Qed.
Lemma lem1562279 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1562271 z) (@lem1562278 z)). Qed.
Lemma lem1562280 (z : real) : (term260 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1562281 (z : real) : (term263 z) = term48.
Proof. exact (TRANS (@lem1562279 z) (@lem1562280 z)). Qed.
Lemma lem1562282 (x : real) (z : real) : (term252 x z) = term264.
Proof. exact (MK_COMB (@lem1562270 x) (@lem1562281 z)). Qed.
Lemma lem1562283 (x : real) (z : real) : (term251 x z) = term264.
Proof. exact (TRANS (@lem1562257 x z) (@lem1562282 x z)). Qed.
Lemma lem1562284 : term264 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1562285 (x : real) (z : real) : (term251 x z) = term48.
Proof. exact (TRANS (@lem1562283 x z) (@lem1562284)). Qed.
Lemma lem1562286 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562287 (x : real) (z : real) : (term265 x z) = term266.
Proof. exact (MK_COMB (@lem1562286) (@lem1562285 x z)). Qed.
Lemma lem1562288 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562289 (x : real) (z : real) : (term250 x z) = term267.
Proof. exact (MK_COMB (@lem1562287 x z) (@lem1562288)). Qed.
Lemma lem1562290 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term267.
Proof. exact (EQ_MP (@lem1562289 x z) (@lem1562256 x y z h1)). Qed.
Lemma lem1562292 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562293 : term267 = term268.
Proof. exact (@lem1562292 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1562294 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1562295 : term267 = False.
Proof. exact (TRANS (@lem1562293) (@lem1562294)). Qed.
Lemma lem1562296 (x : real) (y : real) (z : real) (h1 : term222 x y z) : False.
Proof. exact (EQ_MP (@lem1562295) (@lem1562290 x y z h1)). Qed.
Lemma lem1562297 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term225 x y z.
Proof. exact (h1). Qed.
Lemma lem1562298 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term224 x y z.
Proof. exact (proj2 (@lem1562297 x y z h1)). Qed.
Lemma lem1562300 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1562298 x y z h1)). Qed.
Lemma lem1562301 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term56 y z.
Proof. exact (proj1 (@lem1562298 x y z h1)). Qed.
Lemma lem1562302 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term72 y z.
Proof. exact (proj2 (@lem1562300 x y z h1)). Qed.
Lemma lem1562305 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562306 : term231 = term232.
Proof. exact (@lem1562305 (NUMERAL 0) term210). Qed.
Lemma lem1562307 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562308 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562309 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562308 h1) (fun h1 : term232 = True => @lem1562307)). Qed.
Lemma lem1562310 : term232 = True.
Proof. exact (EQ_MP (@lem1562309) (@lem1562307)). Qed.
Lemma lem1562311 : term231 = True.
Proof. exact (TRANS (@lem1562306) (@lem1562310)). Qed.
Lemma lem1562312 : True = term231.
Proof. exact (SYM (@lem1562311)). Qed.
Lemma lem1562313 : term231.
Proof. exact (EQ_MP (@lem1562312) (@lem0)). Qed.
Lemma lem1562314 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term234 y z.
Proof. exact (conj (@lem1562313) (@lem1562302 x y z h1)). Qed.
Lemma lem1562316 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1562317 (y : real) (z : real) : term236 y z.
Proof. exact (@lem1562316 term237 (term52 y z)). Qed.
Lemma lem1562318 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term238 y z.
Proof. exact (@lem1562317 y z (@lem1562314 x y z h1)). Qed.
Lemma lem1562319 (y : real) (z : real) : (term239 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1562320 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562321 (y : real) (z : real) : (term240 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1562320) (@lem1562319 y z)). Qed.
Lemma lem1562322 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562323 (y : real) (z : real) : (term238 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1562321 y z) (@lem1562322)). Qed.
Lemma lem1562324 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1562323 y z) (@lem1562318 x y z h1)). Qed.
Lemma lem1562326 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562327 : term231 = term232.
Proof. exact (@lem1562326 (NUMERAL 0) term210). Qed.
Lemma lem1562328 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1562329 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1562330 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1562329 h1) (fun h1 : term232 = True => @lem1562328)). Qed.
Lemma lem1562331 : term232 = True.
Proof. exact (EQ_MP (@lem1562330) (@lem1562328)). Qed.
Lemma lem1562332 : term231 = True.
Proof. exact (TRANS (@lem1562327) (@lem1562331)). Qed.
Lemma lem1562333 : True = term231.
Proof. exact (SYM (@lem1562332)). Qed.
Lemma lem1562334 : term231.
Proof. exact (EQ_MP (@lem1562333) (@lem0)). Qed.
Lemma lem1562335 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term241 y z.
Proof. exact (conj (@lem1562334) (@lem1562301 x y z h1)). Qed.
Lemma lem1562337 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1562338 (y : real) (z : real) : term243 y z.
Proof. exact (@lem1562337 term237 (term53 y z)). Qed.
Lemma lem1562339 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term244 y z.
Proof. exact (@lem1562338 y z (@lem1562335 x y z h1)). Qed.
Lemma lem1562340 (y : real) (z : real) : (term245 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1562341 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562342 (y : real) (z : real) : (term246 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1562341) (@lem1562340 y z)). Qed.
Lemma lem1562343 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562344 (y : real) (z : real) : (term244 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1562342 y z) (@lem1562343)). Qed.
Lemma lem1562345 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1562344 y z) (@lem1562339 x y z h1)). Qed.
Lemma lem1562346 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term247 y z.
Proof. exact (conj (@lem1562345 x y z h1) (@lem1562324 x y z h1)). Qed.
Lemma lem1562348 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1562349 (y : real) (z : real) : term249 y z.
Proof. exact (@lem1562348 (term53 y z) (term52 y z)). Qed.
Lemma lem1562350 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term250 y z.
Proof. exact (@lem1562349 y z (@lem1562346 x y z h1)). Qed.
Lemma lem1562351 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483480 (term45 y) y z (term45 z)). Qed.
Lemma lem1562352 (y : real) : (term253 y) = (term254 y).
Proof. exact (@lem1483440 term255 y). Qed.
Lemma lem1562354 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562355 : term257 = term48.
Proof. exact (@lem1562354 term210). Qed.
Lemma lem1562356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562357 : term258 = term259.
Proof. exact (MK_COMB (@lem1562356) (@lem1562355)). Qed.
Lemma lem1562358 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1562359 (y : real) : (term254 y) = (term260 y).
Proof. exact (MK_COMB (@lem1562357) (@lem1562358 y)). Qed.
Lemma lem1562360 (y : real) : (term253 y) = (term260 y).
Proof. exact (TRANS (@lem1562352 y) (@lem1562359 y)). Qed.
Lemma lem1562361 (y : real) : (term260 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1562362 (y : real) : (term253 y) = term48.
Proof. exact (TRANS (@lem1562360 y) (@lem1562361 y)). Qed.
Lemma lem1562363 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1562364 (y : real) : (term261 y) = term262.
Proof. exact (MK_COMB (@lem1562363) (@lem1562362 y)). Qed.
Lemma lem1562365 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1562367 (m : nat) : (term256 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1562368 : term257 = term48.
Proof. exact (@lem1562367 term210). Qed.
Lemma lem1562369 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1562370 : term258 = term259.
Proof. exact (MK_COMB (@lem1562369) (@lem1562368)). Qed.
Lemma lem1562371 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1562372 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1562370) (@lem1562371 z)). Qed.
Lemma lem1562373 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1562365 z) (@lem1562372 z)). Qed.
Lemma lem1562374 (z : real) : (term260 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1562375 (z : real) : (term263 z) = term48.
Proof. exact (TRANS (@lem1562373 z) (@lem1562374 z)). Qed.
Lemma lem1562376 (y : real) (z : real) : (term252 y z) = term264.
Proof. exact (MK_COMB (@lem1562364 y) (@lem1562375 z)). Qed.
Lemma lem1562377 (y : real) (z : real) : (term251 y z) = term264.
Proof. exact (TRANS (@lem1562351 y z) (@lem1562376 y z)). Qed.
Lemma lem1562378 : term264 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1562379 (y : real) (z : real) : (term251 y z) = term48.
Proof. exact (TRANS (@lem1562377 y z) (@lem1562378)). Qed.
Lemma lem1562380 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562381 (y : real) (z : real) : (term265 y z) = term266.
Proof. exact (MK_COMB (@lem1562380) (@lem1562379 y z)). Qed.
Lemma lem1562382 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562383 (y : real) (z : real) : (term250 y z) = term267.
Proof. exact (MK_COMB (@lem1562381 y z) (@lem1562382)). Qed.
Lemma lem1562384 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term267.
Proof. exact (EQ_MP (@lem1562383 y z) (@lem1562350 x y z h1)). Qed.
Lemma lem1562386 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1562387 : term267 = term268.
Proof. exact (@lem1562386 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1562388 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1562389 : term267 = False.
Proof. exact (TRANS (@lem1562387) (@lem1562388)). Qed.
Lemma lem1562390 (x : real) (y : real) (z : real) (h1 : term225 x y z) : False.
Proof. exact (EQ_MP (@lem1562389) (@lem1562384 x y z h1)). Qed.
Lemma lem1562391 (x : real) (y : real) (z : real) (h1 : term227 x y z) : False.
Proof. exact (or_elim (@lem1562202 x y z h1) (fun h0 : term222 x y z => @lem1562296 x y z h0) (fun h0 : term225 x y z => @lem1562390 x y z h0)). Qed.
Lemma lem1562392 (x : real) (y : real) (z : real) (h1 : term229 x y z) : False.
Proof. exact (or_elim (@lem1562015 x y z h1) (fun h0 : term183 x y z => @lem1562201 x y z h0) (fun h0 : term227 x y z => @lem1562391 x y z h0)). Qed.
Lemma lem1562393 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term163 x y z.
Proof. exact (h1). Qed.
Lemma lem1562394 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term229 x y z.
Proof. exact (EQ_MP (@lem1562014 x y z) (@lem1562393 x y z h1)). Qed.
Lemma lem1562395 (x : real) (y : real) (z : real) (h1 : term163 x y z) : (term229 x y z) = False.
Proof. exact (prop_ext (fun h2 : term229 x y z => @lem1562392 x y z h2) (fun h2 : False => @lem1562394 x y z h1)). Qed.
Lemma lem1562396 (x : real) (y : real) (z : real) (h1 : term163 x y z) : False.
Proof. exact (EQ_MP (@lem1562395 x y z h1) (@lem1562394 x y z h1)). Qed.
Lemma lem1562397 (x : real) (y : real) (h1 : term165 x y) : term165 x y.
Proof. exact (h1). Qed.
Lemma lem1562398 (x : real) (y : real) (h1 : term165 x y) : False.
Proof. exact (ex_elim (@lem1562397 x y h1) (fun z : real => fun h0 : term164 x y z => @lem1562396 x y z h0)). Qed.
Lemma lem1562399 (x : real) (h1 : term167 x) : term167 x.
Proof. exact (h1). Qed.
Lemma lem1562400 (x : real) (h1 : term167 x) : False.
Proof. exact (ex_elim (@lem1562399 x h1) (fun y : real => fun h0 : term166 x y => @lem1562398 x y h0)). Qed.
Lemma lem1562401 (h1 : term169) : term169.
Proof. exact (h1). Qed.
Lemma lem1562402 (h1 : term169) : False.
Proof. exact (ex_elim (@lem1562401 h1) (fun x : real => fun h0 : term168 x => @lem1562400 x h0)). Qed.
Lemma lem1562403 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1562404 (h1 : term32) : term169.
Proof. exact (EQ_MP (@lem1561694) (@lem1562403 h1)). Qed.
Lemma lem1562405 (h1 : term32) : term169 = False.
Proof. exact (prop_ext (fun h2 : term169 => @lem1562402 h2) (fun h2 : False => @lem1562404 h1)). Qed.
Lemma lem1562406 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1562405 h1) (@lem1562404 h1)). Qed.
Lemma lem1562407 : term269.
Proof. exact (fun h0 : term32 => @lem1562406 h0). Qed.
Lemma lem1562408 : term270.
Proof. exact (@lem1386578 term271). Qed.
Lemma lem1562409 : term271.
Proof. exact (@lem1562408 (@lem1562407)). Qed.

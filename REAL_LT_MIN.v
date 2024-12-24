Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_MIN_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482716_spec.
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
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
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
Lemma lem1563946 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17045 (real_lt z x) (real_lt z y)). Qed.
Lemma lem1563952 (x : real) (z : real) (y : real) : (term2 x z y) = (term2 x z y).
Proof. exact (eq_refl (term2 x z y)). Qed.
Lemma lem1563954 (z : real) (x : real) (y : real) : (term3 z x y) = (term3 z x y).
Proof. exact (eq_refl (term3 z x y)). Qed.
Lemma lem1563955 (x : real) (z : real) (y : real) : (term4 x z y) = (term5 x z y).
Proof. exact (MK_COMB (@lem1563954 z x y) (@lem1563946 x z y)). Qed.
Lemma lem1563956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563957 (x : real) (z : real) (y : real) : (term6 x z y) = (term7 x z y).
Proof. exact (MK_COMB (@lem1563956) (@lem1563955 x z y)). Qed.
Lemma lem1563958 (x : real) (z : real) (y : real) : (term8 x z y) = (term9 x z y).
Proof. exact (MK_COMB (@lem1563957 x z y) (@lem1563952 x z y)). Qed.
Lemma lem1563959 (x : real) (z : real) (y : real) : (term10 x z y) = (term8 x z y).
Proof. exact (@lem17646 (term11 z x y) (term12 x z y)). Qed.
Lemma lem1563960 (x : real) (z : real) (y : real) : (term10 x z y) = (term9 x z y).
Proof. exact (TRANS (@lem1563959 x z y) (@lem1563958 x z y)). Qed.
Lemma lem1563961 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1563962 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1563961 (term17 x y)). Qed.
Lemma lem1563963 (x : real) (z : real) (y : real) : (term18 x y z) = ((term11 z x y) = (term12 x z y)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1563964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1563965 (x : real) (z : real) (y : real) : (term19 x y z) = (term10 x z y).
Proof. exact (MK_COMB (@lem1563964) (@lem1563963 x z y)). Qed.
Lemma lem1563966 (x : real) (z : real) (y : real) : (term19 x y z) = (term9 x z y).
Proof. exact (TRANS (@lem1563965 x z y) (@lem1563960 x z y)). Qed.
Lemma lem1563967 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1563966 x z y)). Qed.
Lemma lem1563968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563969 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1563968) (@lem1563967 x y)). Qed.
Lemma lem1563970 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1563962 x y) (@lem1563969 x y)). Qed.
Lemma lem1563971 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1563972 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1563971 (term25 x)). Qed.
Lemma lem1563973 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1563974 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1563975 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1563974) (@lem1563973 x y)). Qed.
Lemma lem1563976 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1563975 x y) (@lem1563970 x y)). Qed.
Lemma lem1563977 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1563976 x y)). Qed.
Lemma lem1563978 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563979 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1563978) (@lem1563977 x)). Qed.
Lemma lem1563980 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1563972 x) (@lem1563979 x)). Qed.
Lemma lem1563981 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1563982 : term32 = term33.
Proof. exact (@lem1563981 term34). Qed.
Lemma lem1563983 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1563984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1563985 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1563984) (@lem1563983 x)). Qed.
Lemma lem1563986 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1563985 x) (@lem1563980 x)). Qed.
Lemma lem1563987 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1563986 x)). Qed.
Lemma lem1563988 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563989 : term33 = term40.
Proof. exact (MK_COMB (@lem1563988) (@lem1563987)). Qed.
Lemma lem1563991 : term32 = term40.
Proof. exact (TRANS (@lem1563982) (@lem1563989)). Qed.
Lemma lem1564018 (x : real) (z : real) (y : real) : (term9 x z y) = (term9 x z y).
Proof. exact (eq_refl (term9 x z y)). Qed.
Lemma lem1564019 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1564018 x z y)). Qed.
Lemma lem1564020 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564021 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1564020) (@lem1564019 x y)). Qed.
Lemma lem1564022 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1564021 x y)). Qed.
Lemma lem1564023 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564024 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1564023) (@lem1564022 x)). Qed.
Lemma lem1564025 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1564024 x)). Qed.
Lemma lem1564026 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564027 : term40 = term40.
Proof. exact (MK_COMB (@lem1564026) (@lem1564025)). Qed.
Lemma lem1564028 : term32 = term40.
Proof. exact (TRANS (@lem1563991) (@lem1564027)). Qed.
Lemma lem1564029 (x : real) (y : real) (z : real) : (term11 z x y) = (term41 x y z).
Proof. exact (@lem1483521 (real_min x y) z). Qed.
Lemma lem1564035 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1564040 (z : real) (x : real) (y : real) : (term43 x y z) = (term44 z x y).
Proof. exact (@lem1483488 (term45 z) (real_min x y)). Qed.
Lemma lem1564042 (z : real) (x : real) (y : real) : (term42 x y z) = (term44 z x y).
Proof. exact (TRANS (@lem1564035 x y z) (@lem1564040 z x y)). Qed.
Lemma lem1564043 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564044 (z : real) (x : real) (y : real) : (term46 x y z) = (term47 z x y).
Proof. exact (MK_COMB (@lem1564043) (@lem1564042 z x y)). Qed.
Lemma lem1564045 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564046 (z : real) (x : real) (y : real) : (term41 x y z) = (term49 z x y).
Proof. exact (MK_COMB (@lem1564044 z x y) (@lem1564045)). Qed.
Lemma lem1564047 (z : real) (x : real) (y : real) : (term11 z x y) = (term49 z x y).
Proof. exact (TRANS (@lem1564029 x y z) (@lem1564046 z x y)). Qed.
Lemma lem1564048 (z : real) (x : real) : (term50 z x) = (term51 z x).
Proof. exact (@lem1483531 z x). Qed.
Lemma lem1564054 (z : real) (x : real) : (real_sub z x) = (term52 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1564059 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1564061 (x : real) (z : real) : (real_sub z x) = (term53 x z).
Proof. exact (TRANS (@lem1564054 z x) (@lem1564059 x z)). Qed.
Lemma lem1564062 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1564063 (x : real) (z : real) : (term54 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1564062) (@lem1564061 x z)). Qed.
Lemma lem1564064 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564065 (x : real) (z : real) : (term51 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1564063 x z) (@lem1564064)). Qed.
Lemma lem1564066 (x : real) (z : real) : (term50 z x) = (term56 x z).
Proof. exact (TRANS (@lem1564048 z x) (@lem1564065 x z)). Qed.
Lemma lem1564067 (z : real) (y : real) : (term50 z y) = (term51 z y).
Proof. exact (@lem1483531 z y). Qed.
Lemma lem1564073 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1564078 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1564080 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1564073 z y) (@lem1564078 y z)). Qed.
Lemma lem1564081 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1564082 (y : real) (z : real) : (term54 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1564081) (@lem1564080 y z)). Qed.
Lemma lem1564083 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564084 (y : real) (z : real) : (term51 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1564082 y z) (@lem1564083)). Qed.
Lemma lem1564085 (y : real) (z : real) : (term50 z y) = (term56 y z).
Proof. exact (TRANS (@lem1564067 z y) (@lem1564084 y z)). Qed.
Lemma lem1564086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564087 (x : real) (z : real) : (term57 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1564086) (@lem1564066 x z)). Qed.
Lemma lem1564088 (x : real) (y : real) (z : real) : (term1 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1564087 x z) (@lem1564085 y z)). Qed.
Lemma lem1564089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564090 (z : real) (x : real) (y : real) : (term3 z x y) = (term60 z x y).
Proof. exact (MK_COMB (@lem1564089) (@lem1564047 z x y)). Qed.
Lemma lem1564091 (x : real) (y : real) (z : real) : (term5 x z y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1564090 z x y) (@lem1564088 x y z)). Qed.
Lemma lem1564092 (z : real) (x : real) (y : real) : (term62 z x y) = (term63 z x y).
Proof. exact (@lem1483531 z (real_min x y)). Qed.
Lemma lem1564105 (z : real) (x : real) (y : real) : (term64 z x y) = (term65 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1564106 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1564107 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1564106) (@lem1564105 z x y)). Qed.
Lemma lem1564108 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564109 (z : real) (x : real) (y : real) : (term63 z x y) = (term68 z x y).
Proof. exact (MK_COMB (@lem1564107 z x y) (@lem1564108)). Qed.
Lemma lem1564110 (z : real) (x : real) (y : real) : (term62 z x y) = (term68 z x y).
Proof. exact (TRANS (@lem1564092 z x y) (@lem1564109 z x y)). Qed.
Lemma lem1564111 (x : real) (z : real) : (real_lt z x) = (term69 x z).
Proof. exact (@lem1483521 x z). Qed.
Lemma lem1564124 (x : real) (z : real) : (real_sub x z) = (term52 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1564125 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564126 (x : real) (z : real) : (term70 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1564125) (@lem1564124 x z)). Qed.
Lemma lem1564127 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564128 (x : real) (z : real) : (term69 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1564126 x z) (@lem1564127)). Qed.
Lemma lem1564129 (x : real) (z : real) : (real_lt z x) = (term72 x z).
Proof. exact (TRANS (@lem1564111 x z) (@lem1564128 x z)). Qed.
Lemma lem1564130 (y : real) (z : real) : (real_lt z y) = (term69 y z).
Proof. exact (@lem1483521 y z). Qed.
Lemma lem1564143 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1564144 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564145 (y : real) (z : real) : (term70 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1564144) (@lem1564143 y z)). Qed.
Lemma lem1564146 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564147 (y : real) (z : real) : (term69 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1564145 y z) (@lem1564146)). Qed.
Lemma lem1564148 (y : real) (z : real) : (real_lt z y) = (term72 y z).
Proof. exact (TRANS (@lem1564130 y z) (@lem1564147 y z)). Qed.
Lemma lem1564149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564150 (x : real) (z : real) : (term73 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1564149) (@lem1564129 x z)). Qed.
Lemma lem1564151 (x : real) (y : real) (z : real) : (term12 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1564150 x z) (@lem1564148 y z)). Qed.
Lemma lem1564152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564153 (z : real) (x : real) (y : real) : (term76 z x y) = (term77 z x y).
Proof. exact (MK_COMB (@lem1564152) (@lem1564110 z x y)). Qed.
Lemma lem1564154 (x : real) (y : real) (z : real) : (term2 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1564153 z x y) (@lem1564151 x y z)). Qed.
Lemma lem1564155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564156 (x : real) (y : real) (z : real) : (term7 x z y) = (term79 x y z).
Proof. exact (MK_COMB (@lem1564155) (@lem1564091 x y z)). Qed.
Lemma lem1564157 (x : real) (y : real) (z : real) : (term9 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1564156 x y z) (@lem1564154 x y z)). Qed.
Lemma lem1564158 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1564157 x y z)). Qed.
Lemma lem1564159 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564160 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1564159) (@lem1564158 x y)). Qed.
Lemma lem1564161 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1564160 x y)). Qed.
Lemma lem1564162 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564163 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1564162) (@lem1564161 x)). Qed.
Lemma lem1564164 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1564163 x)). Qed.
Lemma lem1564165 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564166 : term40 = term86.
Proof. exact (MK_COMB (@lem1564165) (@lem1564164)). Qed.
Lemma lem1564167 : term32 = term86.
Proof. exact (TRANS (@lem1564028) (@lem1564166)). Qed.
Lemma lem1564177 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1564178 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1564177 real P Q). Qed.
Lemma lem1564179 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1564178 (term93 x y) (term94 x y)). Qed.
Lemma lem1564180 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1564181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564182 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1564181) (@lem1564180 x y z)). Qed.
Lemma lem1564183 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1564184 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1564182 x y z) (@lem1564183 x y z)). Qed.
Lemma lem1564185 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1564184 x y z)). Qed.
Lemma lem1564186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564187 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1564186) (@lem1564185 x y)). Qed.
Lemma lem1564188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564189 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1564188) (@lem1564187 x y)). Qed.
Lemma lem1564190 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1564191 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1564190 x y z)). Qed.
Lemma lem1564192 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564193 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1564192) (@lem1564191 x y)). Qed.
Lemma lem1564194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564195 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1564194) (@lem1564193 x y)). Qed.
Lemma lem1564196 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1564197 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1564196 x y z)). Qed.
Lemma lem1564198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564199 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1564198) (@lem1564197 x y)). Qed.
Lemma lem1564200 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1564195 x y) (@lem1564199 x y)). Qed.
Lemma lem1564201 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1564189 x y) (@lem1564200 x y)). Qed.
Lemma lem1564202 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1564201 x y) (@lem1564179 x y)). Qed.
Lemma lem1564299 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1564202 x y)). Qed.
Lemma lem1564300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564301 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1564300) (@lem1564299 x)). Qed.
Lemma lem1564303 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1564304 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1564303 real P Q). Qed.
Lemma lem1564305 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1564304 (term115 x) (term116 x)). Qed.
Lemma lem1564306 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1564307 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564308 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1564307) (@lem1564306 x y)). Qed.
Lemma lem1564309 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1564310 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1564308 x y) (@lem1564309 x y)). Qed.
Lemma lem1564311 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1564310 x y)). Qed.
Lemma lem1564312 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564313 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1564312) (@lem1564311 x)). Qed.
Lemma lem1564314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564315 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1564314) (@lem1564313 x)). Qed.
Lemma lem1564316 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1564317 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1564316 x y)). Qed.
Lemma lem1564318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564319 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1564318) (@lem1564317 x)). Qed.
Lemma lem1564320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564321 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1564320) (@lem1564319 x)). Qed.
Lemma lem1564322 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1564323 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1564322 x y)). Qed.
Lemma lem1564324 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564325 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1564324) (@lem1564323 x)). Qed.
Lemma lem1564326 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1564321 x) (@lem1564325 x)). Qed.
Lemma lem1564327 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1564315 x) (@lem1564326 x)). Qed.
Lemma lem1564328 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1564327 x) (@lem1564305 x)). Qed.
Lemma lem1564433 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1564301 x) (@lem1564328 x)). Qed.
Lemma lem1564434 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1564433 x)). Qed.
Lemma lem1564435 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564436 : term86 = term134.
Proof. exact (MK_COMB (@lem1564435) (@lem1564434)). Qed.
Lemma lem1564438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1564439 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1564438 real P Q). Qed.
Lemma lem1564440 : term135 = term136.
Proof. exact (@lem1564439 term137 term138). Qed.
Lemma lem1564441 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1564442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564443 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1564442) (@lem1564441 x)). Qed.
Lemma lem1564444 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1564445 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1564443 x) (@lem1564444 x)). Qed.
Lemma lem1564446 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1564445 x)). Qed.
Lemma lem1564447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564448 : term135 = term134.
Proof. exact (MK_COMB (@lem1564447) (@lem1564446)). Qed.
Lemma lem1564449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564450 : term144 = term145.
Proof. exact (MK_COMB (@lem1564449) (@lem1564448)). Qed.
Lemma lem1564451 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1564452 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1564451 x)). Qed.
Lemma lem1564453 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564454 : term147 = term148.
Proof. exact (MK_COMB (@lem1564453) (@lem1564452)). Qed.
Lemma lem1564455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564456 : term149 = term150.
Proof. exact (MK_COMB (@lem1564455) (@lem1564454)). Qed.
Lemma lem1564457 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1564458 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1564457 x)). Qed.
Lemma lem1564459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564460 : term152 = term153.
Proof. exact (MK_COMB (@lem1564459) (@lem1564458)). Qed.
Lemma lem1564461 : term136 = term154.
Proof. exact (MK_COMB (@lem1564456) (@lem1564460)). Qed.
Lemma lem1564462 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1564450) (@lem1564461)). Qed.
Lemma lem1564463 : term134 = term154.
Proof. exact (EQ_MP (@lem1564462) (@lem1564440)). Qed.
Lemma lem1564576 : term86 = term154.
Proof. exact (TRANS (@lem1564436) (@lem1564463)). Qed.
Lemma lem1564578 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1564579 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1564578 real P Q). Qed.
Lemma lem1564580 : term136 = term135.
Proof. exact (@lem1564579 term137 term138). Qed.
Lemma lem1564581 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1564582 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1564581 x)). Qed.
Lemma lem1564583 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564584 : term147 = term148.
Proof. exact (MK_COMB (@lem1564583) (@lem1564582)). Qed.
Lemma lem1564585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564586 : term149 = term150.
Proof. exact (MK_COMB (@lem1564585) (@lem1564584)). Qed.
Lemma lem1564587 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1564588 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1564587 x)). Qed.
Lemma lem1564589 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564590 : term152 = term153.
Proof. exact (MK_COMB (@lem1564589) (@lem1564588)). Qed.
Lemma lem1564591 : term136 = term154.
Proof. exact (MK_COMB (@lem1564586) (@lem1564590)). Qed.
Lemma lem1564592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564593 : term155 = term156.
Proof. exact (MK_COMB (@lem1564592) (@lem1564591)). Qed.
Lemma lem1564594 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1564595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564596 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1564595) (@lem1564594 x)). Qed.
Lemma lem1564597 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1564598 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1564596 x) (@lem1564597 x)). Qed.
Lemma lem1564599 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1564598 x)). Qed.
Lemma lem1564600 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564601 : term135 = term134.
Proof. exact (MK_COMB (@lem1564600) (@lem1564599)). Qed.
Lemma lem1564602 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1564593) (@lem1564601)). Qed.
Lemma lem1564603 : term154 = term134.
Proof. exact (EQ_MP (@lem1564602) (@lem1564580)). Qed.
Lemma lem1564605 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1564606 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1564605 real P Q). Qed.
Lemma lem1564607 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1564606 (term115 x) (term116 x)). Qed.
Lemma lem1564608 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1564609 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1564608 x y)). Qed.
Lemma lem1564610 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564611 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1564610) (@lem1564609 x)). Qed.
Lemma lem1564612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564613 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1564612) (@lem1564611 x)). Qed.
Lemma lem1564614 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1564615 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1564614 x y)). Qed.
Lemma lem1564616 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564617 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1564616) (@lem1564615 x)). Qed.
Lemma lem1564618 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1564613 x) (@lem1564617 x)). Qed.
Lemma lem1564619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564620 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1564619) (@lem1564618 x)). Qed.
Lemma lem1564621 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1564622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564623 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1564622) (@lem1564621 x y)). Qed.
Lemma lem1564624 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1564625 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1564623 x y) (@lem1564624 x y)). Qed.
Lemma lem1564626 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1564625 x y)). Qed.
Lemma lem1564627 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564628 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1564627) (@lem1564626 x)). Qed.
Lemma lem1564629 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1564620 x) (@lem1564628 x)). Qed.
Lemma lem1564630 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1564629 x) (@lem1564607 x)). Qed.
Lemma lem1564632 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1564633 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1564632 real P Q). Qed.
Lemma lem1564634 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1564633 (term93 x y) (term94 x y)). Qed.
Lemma lem1564635 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1564636 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1564635 x y z)). Qed.
Lemma lem1564637 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564638 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1564637) (@lem1564636 x y)). Qed.
Lemma lem1564639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564640 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1564639) (@lem1564638 x y)). Qed.
Lemma lem1564641 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1564642 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1564641 x y z)). Qed.
Lemma lem1564643 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564644 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1564643) (@lem1564642 x y)). Qed.
Lemma lem1564645 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1564640 x y) (@lem1564644 x y)). Qed.
Lemma lem1564646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1564647 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1564646) (@lem1564645 x y)). Qed.
Lemma lem1564648 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1564649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564650 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1564649) (@lem1564648 x y z)). Qed.
Lemma lem1564651 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1564652 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1564650 x y z) (@lem1564651 x y z)). Qed.
Lemma lem1564653 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1564652 x y z)). Qed.
Lemma lem1564654 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564655 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1564654) (@lem1564653 x y)). Qed.
Lemma lem1564656 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1564647 x y) (@lem1564655 x y)). Qed.
Lemma lem1564657 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1564656 x y) (@lem1564634 x y)). Qed.
Lemma lem1564658 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1564657 x y)). Qed.
Lemma lem1564659 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564660 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1564659) (@lem1564658 x)). Qed.
Lemma lem1564661 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1564630 x) (@lem1564660 x)). Qed.
Lemma lem1564662 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1564661 x)). Qed.
Lemma lem1564663 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564664 : term134 = term86.
Proof. exact (MK_COMB (@lem1564663) (@lem1564662)). Qed.
Lemma lem1564665 : term154 = term86.
Proof. exact (TRANS (@lem1564603) (@lem1564664)). Qed.
Lemma lem1564666 : term86 = term86.
Proof. exact (TRANS (@lem1564576) (@lem1564665)). Qed.
Lemma lem1564669 : term32 = term86.
Proof. exact (TRANS (@lem1564167) (@lem1564666)). Qed.
Lemma lem1564682 (x : real) (y : real) (z : real) : (term78 x y z) = (term78 x y z).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1564699 (x : real) (y : real) (z : real) : (term61 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term56 x z) (term49 z x y) (term56 y z)). Qed.
Lemma lem1564700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564701 (x : real) (y : real) (z : real) : (term79 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1564700) (@lem1564699 x y z)). Qed.
Lemma lem1564702 (x : real) (y : real) (z : real) : (term80 x y z) = (term163 x y z).
Proof. exact (MK_COMB (@lem1564701 x y z) (@lem1564682 x y z)). Qed.
Lemma lem1564703 (x : real) (y : real) : (term81 x y) = (term164 x y).
Proof. exact (fun_ext (fun z : real => @lem1564702 x y z)). Qed.
Lemma lem1564704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564705 (x : real) (y : real) : (term82 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1564704) (@lem1564703 x y)). Qed.
Lemma lem1564706 (x : real) : (term83 x) = (term166 x).
Proof. exact (fun_ext (fun y : real => @lem1564705 x y)). Qed.
Lemma lem1564707 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564708 (x : real) : (term84 x) = (term167 x).
Proof. exact (MK_COMB (@lem1564707) (@lem1564706 x)). Qed.
Lemma lem1564709 : term85 = term168.
Proof. exact (fun_ext (fun x : real => @lem1564708 x)). Qed.
Lemma lem1564710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1564711 : term86 = term169.
Proof. exact (MK_COMB (@lem1564710) (@lem1564709)). Qed.
Lemma lem1564712 : term32 = term169.
Proof. exact (TRANS (@lem1564669) (@lem1564711)). Qed.
Lemma lem1564714 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1564715 (x : real) (z : real) (y : real) : (term49 z x y) = (term172 x z y).
Proof. exact (@lem1564714 x (term45 z) y term48). Qed.
Lemma lem1564728 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1564729 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564730 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1564729) (@lem1564728 y z)). Qed.
Lemma lem1564731 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564732 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1564730 y z) (@lem1564731)). Qed.
Lemma lem1564745 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1564746 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564747 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1564746) (@lem1564745 x z)). Qed.
Lemma lem1564748 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564749 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1564747 x z) (@lem1564748)). Qed.
Lemma lem1564750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564751 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1564750) (@lem1564749 x z)). Qed.
Lemma lem1564752 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1564751 x z) (@lem1564732 y z)). Qed.
Lemma lem1564753 (x : real) (y : real) (z : real) : (term49 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1564715 x z y) (@lem1564752 x y z)). Qed.
Lemma lem1564754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564755 (x : real) (y : real) (z : real) : (term60 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1564754) (@lem1564753 x y z)). Qed.
Lemma lem1564756 (x : real) (z : real) : (term56 x z) = (term56 x z).
Proof. exact (eq_refl (term56 x z)). Qed.
Lemma lem1564759 (y : real) (x : real) (z : real) : (term177 y x z) = (term178 y x z).
Proof. exact (MK_COMB (@lem1564755 x y z) (@lem1564756 x z)). Qed.
Lemma lem1564761 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1564762 (x : real) (z : real) (y : real) : (term49 z x y) = (term172 x z y).
Proof. exact (@lem1564761 x (term45 z) y term48). Qed.
Lemma lem1564775 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1564776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564777 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1564776) (@lem1564775 y z)). Qed.
Lemma lem1564778 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564779 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1564777 y z) (@lem1564778)). Qed.
Lemma lem1564792 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1564793 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564794 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1564793) (@lem1564792 x z)). Qed.
Lemma lem1564795 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564796 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1564794 x z) (@lem1564795)). Qed.
Lemma lem1564797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564798 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1564797) (@lem1564796 x z)). Qed.
Lemma lem1564799 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1564798 x z) (@lem1564779 y z)). Qed.
Lemma lem1564800 (x : real) (y : real) (z : real) : (term49 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1564762 x z y) (@lem1564799 x y z)). Qed.
Lemma lem1564801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564802 (x : real) (y : real) (z : real) : (term60 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1564801) (@lem1564800 x y z)). Qed.
Lemma lem1564803 (y : real) (z : real) : (term56 y z) = (term56 y z).
Proof. exact (eq_refl (term56 y z)). Qed.
Lemma lem1564806 (x : real) (y : real) (z : real) : (term179 x y z) = (term180 x y z).
Proof. exact (MK_COMB (@lem1564802 x y z) (@lem1564803 y z)). Qed.
Lemma lem1564807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564808 (y : real) (x : real) (z : real) : (term181 y x z) = (term182 y x z).
Proof. exact (MK_COMB (@lem1564807) (@lem1564759 y x z)). Qed.
Lemma lem1564809 (x : real) (y : real) (z : real) : (term161 x y z) = (term183 x y z).
Proof. exact (MK_COMB (@lem1564808 y x z) (@lem1564806 x y z)). Qed.
Lemma lem1564811 (x : real) (y : real) (z : real) : (term184 z x y) = (term78 x y z).
Proof. exact (eq_refl (term184 z x y)). Qed.
Lemma lem1564812 (z : real) (x : real) (y : real) : (term78 x y z) = (term184 z x y).
Proof. exact (SYM (@lem1564811 x y z)). Qed.
Lemma lem1564813 (x : real) (z : real) (y : real) : (term184 z x y) = (term185 x z y).
Proof. exact (@lem1483429 x (term186 x y z) y). Qed.
Lemma lem1564814 (x : real) (z : real) (y : real) : (term78 x y z) = (term185 x z y).
Proof. exact (TRANS (@lem1564812 z x y) (@lem1564813 x z y)). Qed.
Lemma lem1564815 (x : real) (y : real) (z : real) : (term187 x z y) = (term188 x y z).
Proof. exact (eq_refl (term187 x z y)). Qed.
Lemma lem1564816 (x : real) (y : real) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1564817 (x : real) (y : real) (z : real) : (term190 x z y) = (term191 x y z).
Proof. exact (MK_COMB (@lem1564816 x y) (@lem1564815 x y z)). Qed.
Lemma lem1564818 (x : real) (y : real) (z : real) : (term192 y z x) = (term193 x y z).
Proof. exact (eq_refl (term192 y z x)). Qed.
Lemma lem1564819 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1564820 (x : real) (y : real) (z : real) : (term195 y z x) = (term196 x y z).
Proof. exact (MK_COMB (@lem1564819 y x) (@lem1564818 x y z)). Qed.
Lemma lem1564821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1564822 (x : real) (y : real) (z : real) : (term197 y z x) = (term198 x y z).
Proof. exact (MK_COMB (@lem1564821) (@lem1564820 x y z)). Qed.
Lemma lem1564823 (x : real) (y : real) (z : real) : (term185 x z y) = (term199 x y z).
Proof. exact (MK_COMB (@lem1564822 x y z) (@lem1564817 x y z)). Qed.
Lemma lem1564824 (x : real) (y : real) (z : real) : (term200 x y z) = (term200 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1564825 (x : real) (y : real) (z : real) : ((term78 x y z) = (term185 x z y)) = ((term78 x y z) = (term199 x y z)).
Proof. exact (MK_COMB (@lem1564824 x y z) (@lem1564823 x y z)). Qed.
Lemma lem1564826 (x : real) (y : real) (z : real) : (term78 x y z) = (term199 x y z).
Proof. exact (EQ_MP (@lem1564825 x y z) (@lem1564814 x z y)). Qed.
Lemma lem1564827 (y : real) (x : real) : (real_ge y x) = (term51 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1564833 (y : real) (x : real) : (real_sub y x) = (term52 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1564838 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (@lem1483488 (term45 x) y). Qed.
Lemma lem1564840 (x : real) (y : real) : (real_sub y x) = (term53 x y).
Proof. exact (TRANS (@lem1564833 y x) (@lem1564838 x y)). Qed.
Lemma lem1564841 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1564842 (x : real) (y : real) : (term54 y x) = (term55 x y).
Proof. exact (MK_COMB (@lem1564841) (@lem1564840 x y)). Qed.
Lemma lem1564843 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564844 (x : real) (y : real) : (term51 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1564842 x y) (@lem1564843)). Qed.
Lemma lem1564845 (x : real) (y : real) : (real_ge y x) = (term56 x y).
Proof. exact (TRANS (@lem1564827 y x) (@lem1564844 x y)). Qed.
Lemma lem1564846 (z : real) (x : real) : (term201 z x) = (term202 z x).
Proof. exact (@lem1483527 (term52 z x) term48). Qed.
Lemma lem1564847 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564860 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1564861 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1564862 (x : real) (z : real) : (term203 z x) = (term204 x z).
Proof. exact (MK_COMB (@lem1564861) (@lem1564860 x z)). Qed.
Lemma lem1564863 (x : real) (z : real) : (term205 z x) = (term206 x z).
Proof. exact (MK_COMB (@lem1564862 x z) (@lem1564847)). Qed.
Lemma lem1564864 (x : real) (z : real) : (term206 x z) = (term207 x z).
Proof. exact (@lem1483519 (term53 x z) term48). Qed.
Lemma lem1564866 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1564867 : term209 = term48.
Proof. exact (@lem1564866 term210). Qed.
Lemma lem1564868 (x : real) (z : real) : (term211 x z) = (term211 x z).
Proof. exact (eq_refl (term211 x z)). Qed.
Lemma lem1564869 (x : real) (z : real) : (term207 x z) = (term212 x z).
Proof. exact (MK_COMB (@lem1564868 x z) (@lem1564867)). Qed.
Lemma lem1564870 (x : real) (z : real) : (term212 x z) = (term53 x z).
Proof. exact (@lem1483450 (term53 x z)). Qed.
Lemma lem1564871 (x : real) (z : real) : (term207 x z) = (term53 x z).
Proof. exact (TRANS (@lem1564869 x z) (@lem1564870 x z)). Qed.
Lemma lem1564872 (x : real) (z : real) : (term206 x z) = (term53 x z).
Proof. exact (TRANS (@lem1564864 x z) (@lem1564871 x z)). Qed.
Lemma lem1564873 (x : real) (z : real) : (term205 z x) = (term53 x z).
Proof. exact (TRANS (@lem1564863 x z) (@lem1564872 x z)). Qed.
Lemma lem1564874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1564875 (x : real) (z : real) : (term213 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1564874) (@lem1564873 x z)). Qed.
Lemma lem1564876 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564877 (x : real) (z : real) : (term202 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1564875 x z) (@lem1564876)). Qed.
Lemma lem1564878 (x : real) (z : real) : (term201 z x) = (term56 x z).
Proof. exact (TRANS (@lem1564846 z x) (@lem1564877 x z)). Qed.
Lemma lem1564879 (x : real) (z : real) : (term72 x z) = (term214 x z).
Proof. exact (@lem1483525 (term52 x z) term48). Qed.
Lemma lem1564897 (x : real) (z : real) : (term205 x z) = (term215 x z).
Proof. exact (@lem1483519 (term52 x z) term48). Qed.
Lemma lem1564899 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1564900 : term209 = term48.
Proof. exact (@lem1564899 term210). Qed.
Lemma lem1564901 (x : real) (z : real) : (term216 x z) = (term216 x z).
Proof. exact (eq_refl (term216 x z)). Qed.
Lemma lem1564902 (x : real) (z : real) : (term215 x z) = (term217 x z).
Proof. exact (MK_COMB (@lem1564901 x z) (@lem1564900)). Qed.
Lemma lem1564903 (x : real) (z : real) : (term217 x z) = (term52 x z).
Proof. exact (@lem1483450 (term52 x z)). Qed.
Lemma lem1564904 (x : real) (z : real) : (term215 x z) = (term52 x z).
Proof. exact (TRANS (@lem1564902 x z) (@lem1564903 x z)). Qed.
Lemma lem1564906 (x : real) (z : real) : (term205 x z) = (term52 x z).
Proof. exact (TRANS (@lem1564897 x z) (@lem1564904 x z)). Qed.
Lemma lem1564907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564908 (x : real) (z : real) : (term218 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1564907) (@lem1564906 x z)). Qed.
Lemma lem1564909 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564910 (x : real) (z : real) : (term214 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1564908 x z) (@lem1564909)). Qed.
Lemma lem1564911 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (TRANS (@lem1564879 x z) (@lem1564910 x z)). Qed.
Lemma lem1564912 (y : real) (z : real) : (term72 y z) = (term214 y z).
Proof. exact (@lem1483525 (term52 y z) term48). Qed.
Lemma lem1564930 (y : real) (z : real) : (term205 y z) = (term215 y z).
Proof. exact (@lem1483519 (term52 y z) term48). Qed.
Lemma lem1564932 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1564933 : term209 = term48.
Proof. exact (@lem1564932 term210). Qed.
Lemma lem1564934 (y : real) (z : real) : (term216 y z) = (term216 y z).
Proof. exact (eq_refl (term216 y z)). Qed.
Lemma lem1564935 (y : real) (z : real) : (term215 y z) = (term217 y z).
Proof. exact (MK_COMB (@lem1564934 y z) (@lem1564933)). Qed.
Lemma lem1564936 (y : real) (z : real) : (term217 y z) = (term52 y z).
Proof. exact (@lem1483450 (term52 y z)). Qed.
Lemma lem1564937 (y : real) (z : real) : (term215 y z) = (term52 y z).
Proof. exact (TRANS (@lem1564935 y z) (@lem1564936 y z)). Qed.
Lemma lem1564939 (y : real) (z : real) : (term205 y z) = (term52 y z).
Proof. exact (TRANS (@lem1564930 y z) (@lem1564937 y z)). Qed.
Lemma lem1564940 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564941 (y : real) (z : real) : (term218 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1564940) (@lem1564939 y z)). Qed.
Lemma lem1564942 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564943 (y : real) (z : real) : (term214 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1564941 y z) (@lem1564942)). Qed.
Lemma lem1564944 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (TRANS (@lem1564912 y z) (@lem1564943 y z)). Qed.
Lemma lem1564945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564946 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1564945) (@lem1564911 x z)). Qed.
Lemma lem1564947 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1564946 x z) (@lem1564944 y z)). Qed.
Lemma lem1564948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564949 (x : real) (z : real) : (term219 z x) = (term220 x z).
Proof. exact (MK_COMB (@lem1564948) (@lem1564878 x z)). Qed.
Lemma lem1564950 (x : real) (y : real) (z : real) : (term193 x y z) = (term221 x y z).
Proof. exact (MK_COMB (@lem1564949 x z) (@lem1564947 x y z)). Qed.
Lemma lem1564951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1564952 (x : real) (y : real) : (term194 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem1564951) (@lem1564845 x y)). Qed.
Lemma lem1564953 (x : real) (y : real) (z : real) : (term196 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1564952 x y) (@lem1564950 x y z)). Qed.
Lemma lem1564954 (x : real) (y : real) : (real_gt x y) = (term69 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1564967 (x : real) (y : real) : (real_sub x y) = (term52 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1564968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1564969 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1564968) (@lem1564967 x y)). Qed.
Lemma lem1564970 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564971 (x : real) (y : real) : (term69 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1564969 x y) (@lem1564970)). Qed.
Lemma lem1564972 (x : real) (y : real) : (real_gt x y) = (term72 x y).
Proof. exact (TRANS (@lem1564954 x y) (@lem1564971 x y)). Qed.
Lemma lem1564973 (z : real) (y : real) : (term201 z y) = (term202 z y).
Proof. exact (@lem1483527 (term52 z y) term48). Qed.
Lemma lem1564974 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1564987 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1564988 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1564989 (y : real) (z : real) : (term203 z y) = (term204 y z).
Proof. exact (MK_COMB (@lem1564988) (@lem1564987 y z)). Qed.
Lemma lem1564990 (y : real) (z : real) : (term205 z y) = (term206 y z).
Proof. exact (MK_COMB (@lem1564989 y z) (@lem1564974)). Qed.
Lemma lem1564991 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483519 (term53 y z) term48). Qed.
Lemma lem1564993 (x : nat) : (term208 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1564994 : term209 = term48.
Proof. exact (@lem1564993 term210). Qed.
Lemma lem1564995 (y : real) (z : real) : (term211 y z) = (term211 y z).
Proof. exact (eq_refl (term211 y z)). Qed.
Lemma lem1564996 (y : real) (z : real) : (term207 y z) = (term212 y z).
Proof. exact (MK_COMB (@lem1564995 y z) (@lem1564994)). Qed.
Lemma lem1564997 (y : real) (z : real) : (term212 y z) = (term53 y z).
Proof. exact (@lem1483450 (term53 y z)). Qed.
Lemma lem1564998 (y : real) (z : real) : (term207 y z) = (term53 y z).
Proof. exact (TRANS (@lem1564996 y z) (@lem1564997 y z)). Qed.
Lemma lem1564999 (y : real) (z : real) : (term206 y z) = (term53 y z).
Proof. exact (TRANS (@lem1564991 y z) (@lem1564998 y z)). Qed.
Lemma lem1565000 (y : real) (z : real) : (term205 z y) = (term53 y z).
Proof. exact (TRANS (@lem1564990 y z) (@lem1564999 y z)). Qed.
Lemma lem1565001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565002 (y : real) (z : real) : (term213 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1565001) (@lem1565000 y z)). Qed.
Lemma lem1565003 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565004 (y : real) (z : real) : (term202 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1565002 y z) (@lem1565003)). Qed.
Lemma lem1565005 (y : real) (z : real) : (term201 z y) = (term56 y z).
Proof. exact (TRANS (@lem1564973 z y) (@lem1565004 y z)). Qed.
Lemma lem1565006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565007 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1565006) (@lem1564911 x z)). Qed.
Lemma lem1565008 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1565007 x z) (@lem1564944 y z)). Qed.
Lemma lem1565009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565010 (y : real) (z : real) : (term219 z y) = (term220 y z).
Proof. exact (MK_COMB (@lem1565009) (@lem1565005 y z)). Qed.
Lemma lem1565011 (x : real) (y : real) (z : real) : (term188 x y z) = (term223 x y z).
Proof. exact (MK_COMB (@lem1565010 y z) (@lem1565008 x y z)). Qed.
Lemma lem1565012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565013 (x : real) (y : real) : (term189 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1565012) (@lem1564972 x y)). Qed.
Lemma lem1565014 (x : real) (y : real) (z : real) : (term191 x y z) = (term224 x y z).
Proof. exact (MK_COMB (@lem1565013 x y) (@lem1565011 x y z)). Qed.
Lemma lem1565015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565016 (x : real) (y : real) (z : real) : (term198 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1565015) (@lem1564953 x y z)). Qed.
Lemma lem1565017 (x : real) (y : real) (z : real) : (term199 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1565016 x y z) (@lem1565014 x y z)). Qed.
Lemma lem1565029 (x : real) (y : real) (z : real) : (term78 x y z) = (term226 x y z).
Proof. exact (TRANS (@lem1564826 x y z) (@lem1565017 x y z)). Qed.
Lemma lem1565030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565031 (x : real) (y : real) (z : real) : (term162 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1565030) (@lem1564809 x y z)). Qed.
Lemma lem1565032 (x : real) (y : real) (z : real) : (term163 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1565031 x y z) (@lem1565029 x y z)). Qed.
Lemma lem1565033 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term228 x y z.
Proof. exact (h1). Qed.
Lemma lem1565034 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1565035 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term178 y x z.
Proof. exact (h1). Qed.
Lemma lem1565036 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term56 x z.
Proof. exact (proj2 (@lem1565035 y x z h1)). Qed.
Lemma lem1565037 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term75 x y z.
Proof. exact (proj1 (@lem1565035 y x z h1)). Qed.
Lemma lem1565039 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (proj1 (@lem1565037 y x z h1)). Qed.
Lemma lem1565041 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565042 : term230 = term231.
Proof. exact (@lem1565041 (NUMERAL 0) term210). Qed.
Lemma lem1565043 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565044 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565045 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565044 h1) (fun h1 : term231 = True => @lem1565043)). Qed.
Lemma lem1565046 : term231 = True.
Proof. exact (EQ_MP (@lem1565045) (@lem1565043)). Qed.
Lemma lem1565047 : term230 = True.
Proof. exact (TRANS (@lem1565042) (@lem1565046)). Qed.
Lemma lem1565048 : True = term230.
Proof. exact (SYM (@lem1565047)). Qed.
Lemma lem1565049 : term230.
Proof. exact (EQ_MP (@lem1565048) (@lem0)). Qed.
Lemma lem1565050 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term233 x z.
Proof. exact (conj (@lem1565049) (@lem1565036 y x z h1)). Qed.
Lemma lem1565052 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1565053 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1565052 term236 (term53 x z)). Qed.
Lemma lem1565054 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term237 x z.
Proof. exact (@lem1565053 x z (@lem1565050 y x z h1)). Qed.
Lemma lem1565055 (x : real) (z : real) : (term238 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1565056 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565057 (x : real) (z : real) : (term239 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1565056) (@lem1565055 x z)). Qed.
Lemma lem1565058 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565059 (x : real) (z : real) : (term237 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1565057 x z) (@lem1565058)). Qed.
Lemma lem1565060 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term56 x z.
Proof. exact (EQ_MP (@lem1565059 x z) (@lem1565054 y x z h1)). Qed.
Lemma lem1565062 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565063 : term230 = term231.
Proof. exact (@lem1565062 (NUMERAL 0) term210). Qed.
Lemma lem1565064 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565065 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565066 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565065 h1) (fun h1 : term231 = True => @lem1565064)). Qed.
Lemma lem1565067 : term231 = True.
Proof. exact (EQ_MP (@lem1565066) (@lem1565064)). Qed.
Lemma lem1565068 : term230 = True.
Proof. exact (TRANS (@lem1565063) (@lem1565067)). Qed.
Lemma lem1565069 : True = term230.
Proof. exact (SYM (@lem1565068)). Qed.
Lemma lem1565070 : term230.
Proof. exact (EQ_MP (@lem1565069) (@lem0)). Qed.
Lemma lem1565071 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term240 x z.
Proof. exact (conj (@lem1565070) (@lem1565039 y x z h1)). Qed.
Lemma lem1565073 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1565074 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1565073 term236 (term52 x z)). Qed.
Lemma lem1565075 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term243 x z.
Proof. exact (@lem1565074 x z (@lem1565071 y x z h1)). Qed.
Lemma lem1565076 (x : real) (z : real) : (term244 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1565077 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565078 (x : real) (z : real) : (term245 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1565077) (@lem1565076 x z)). Qed.
Lemma lem1565079 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565080 (x : real) (z : real) : (term243 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1565078 x z) (@lem1565079)). Qed.
Lemma lem1565081 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1565080 x z) (@lem1565075 y x z h1)). Qed.
Lemma lem1565082 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term246 x z.
Proof. exact (conj (@lem1565081 y x z h1) (@lem1565060 y x z h1)). Qed.
Lemma lem1565084 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1565085 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1565084 (term52 x z) (term53 x z)). Qed.
Lemma lem1565086 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term249 x z.
Proof. exact (@lem1565085 x z (@lem1565082 y x z h1)). Qed.
Lemma lem1565087 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 x (term45 x) (term45 z) z). Qed.
Lemma lem1565088 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483442 term254 x). Qed.
Lemma lem1565090 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565091 : term256 = term48.
Proof. exact (@lem1565090 term210). Qed.
Lemma lem1565092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565093 : term257 = term258.
Proof. exact (MK_COMB (@lem1565092) (@lem1565091)). Qed.
Lemma lem1565094 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1565095 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1565093) (@lem1565094 x)). Qed.
Lemma lem1565096 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1565088 x) (@lem1565095 x)). Qed.
Lemma lem1565097 (x : real) : (term259 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1565098 (x : real) : (term252 x) = term48.
Proof. exact (TRANS (@lem1565096 x) (@lem1565097 x)). Qed.
Lemma lem1565099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1565100 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1565099) (@lem1565098 x)). Qed.
Lemma lem1565101 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1565103 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565104 : term256 = term48.
Proof. exact (@lem1565103 term210). Qed.
Lemma lem1565105 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565106 : term257 = term258.
Proof. exact (MK_COMB (@lem1565105) (@lem1565104)). Qed.
Lemma lem1565107 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1565108 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1565106) (@lem1565107 z)). Qed.
Lemma lem1565109 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1565101 z) (@lem1565108 z)). Qed.
Lemma lem1565110 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1565111 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1565109 z) (@lem1565110 z)). Qed.
Lemma lem1565112 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1565100 x) (@lem1565111 z)). Qed.
Lemma lem1565113 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1565087 x z) (@lem1565112 x z)). Qed.
Lemma lem1565114 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1565115 (x : real) (z : real) : (term250 x z) = term48.
Proof. exact (TRANS (@lem1565113 x z) (@lem1565114)). Qed.
Lemma lem1565116 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565117 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1565116) (@lem1565115 x z)). Qed.
Lemma lem1565118 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565119 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1565117 x z) (@lem1565118)). Qed.
Lemma lem1565120 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term266.
Proof. exact (EQ_MP (@lem1565119 x z) (@lem1565086 y x z h1)). Qed.
Lemma lem1565122 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565123 : term266 = term267.
Proof. exact (@lem1565122 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1565124 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1565125 : term266 = False.
Proof. exact (TRANS (@lem1565123) (@lem1565124)). Qed.
Lemma lem1565126 (y : real) (x : real) (z : real) (h1 : term178 y x z) : False.
Proof. exact (EQ_MP (@lem1565125) (@lem1565120 y x z h1)). Qed.
Lemma lem1565127 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term180 x y z.
Proof. exact (h1). Qed.
Lemma lem1565128 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term56 y z.
Proof. exact (proj2 (@lem1565127 x y z h1)). Qed.
Lemma lem1565129 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term75 x y z.
Proof. exact (proj1 (@lem1565127 x y z h1)). Qed.
Lemma lem1565130 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (proj2 (@lem1565129 x y z h1)). Qed.
Lemma lem1565133 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565134 : term230 = term231.
Proof. exact (@lem1565133 (NUMERAL 0) term210). Qed.
Lemma lem1565135 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565136 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565137 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565136 h1) (fun h1 : term231 = True => @lem1565135)). Qed.
Lemma lem1565138 : term231 = True.
Proof. exact (EQ_MP (@lem1565137) (@lem1565135)). Qed.
Lemma lem1565139 : term230 = True.
Proof. exact (TRANS (@lem1565134) (@lem1565138)). Qed.
Lemma lem1565140 : True = term230.
Proof. exact (SYM (@lem1565139)). Qed.
Lemma lem1565141 : term230.
Proof. exact (EQ_MP (@lem1565140) (@lem0)). Qed.
Lemma lem1565142 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term233 y z.
Proof. exact (conj (@lem1565141) (@lem1565128 x y z h1)). Qed.
Lemma lem1565144 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1565145 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1565144 term236 (term53 y z)). Qed.
Lemma lem1565146 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term237 y z.
Proof. exact (@lem1565145 y z (@lem1565142 x y z h1)). Qed.
Lemma lem1565147 (y : real) (z : real) : (term238 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1565148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565149 (y : real) (z : real) : (term239 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1565148) (@lem1565147 y z)). Qed.
Lemma lem1565150 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565151 (y : real) (z : real) : (term237 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1565149 y z) (@lem1565150)). Qed.
Lemma lem1565152 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1565151 y z) (@lem1565146 x y z h1)). Qed.
Lemma lem1565154 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565155 : term230 = term231.
Proof. exact (@lem1565154 (NUMERAL 0) term210). Qed.
Lemma lem1565156 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565157 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565158 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565157 h1) (fun h1 : term231 = True => @lem1565156)). Qed.
Lemma lem1565159 : term231 = True.
Proof. exact (EQ_MP (@lem1565158) (@lem1565156)). Qed.
Lemma lem1565160 : term230 = True.
Proof. exact (TRANS (@lem1565155) (@lem1565159)). Qed.
Lemma lem1565161 : True = term230.
Proof. exact (SYM (@lem1565160)). Qed.
Lemma lem1565162 : term230.
Proof. exact (EQ_MP (@lem1565161) (@lem0)). Qed.
Lemma lem1565163 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term240 y z.
Proof. exact (conj (@lem1565162) (@lem1565130 x y z h1)). Qed.
Lemma lem1565165 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1565166 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1565165 term236 (term52 y z)). Qed.
Lemma lem1565167 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term243 y z.
Proof. exact (@lem1565166 y z (@lem1565163 x y z h1)). Qed.
Lemma lem1565168 (y : real) (z : real) : (term244 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1565169 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565170 (y : real) (z : real) : (term245 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1565169) (@lem1565168 y z)). Qed.
Lemma lem1565171 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565172 (y : real) (z : real) : (term243 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1565170 y z) (@lem1565171)). Qed.
Lemma lem1565173 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1565172 y z) (@lem1565167 x y z h1)). Qed.
Lemma lem1565174 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term246 y z.
Proof. exact (conj (@lem1565173 x y z h1) (@lem1565152 x y z h1)). Qed.
Lemma lem1565176 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1565177 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1565176 (term52 y z) (term53 y z)). Qed.
Lemma lem1565178 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term249 y z.
Proof. exact (@lem1565177 y z (@lem1565174 x y z h1)). Qed.
Lemma lem1565179 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1565180 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483442 term254 y). Qed.
Lemma lem1565182 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565183 : term256 = term48.
Proof. exact (@lem1565182 term210). Qed.
Lemma lem1565184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565185 : term257 = term258.
Proof. exact (MK_COMB (@lem1565184) (@lem1565183)). Qed.
Lemma lem1565186 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1565187 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1565185) (@lem1565186 y)). Qed.
Lemma lem1565188 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1565180 y) (@lem1565187 y)). Qed.
Lemma lem1565189 (y : real) : (term259 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1565190 (y : real) : (term252 y) = term48.
Proof. exact (TRANS (@lem1565188 y) (@lem1565189 y)). Qed.
Lemma lem1565191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1565192 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1565191) (@lem1565190 y)). Qed.
Lemma lem1565193 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1565195 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565196 : term256 = term48.
Proof. exact (@lem1565195 term210). Qed.
Lemma lem1565197 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565198 : term257 = term258.
Proof. exact (MK_COMB (@lem1565197) (@lem1565196)). Qed.
Lemma lem1565199 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1565200 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1565198) (@lem1565199 z)). Qed.
Lemma lem1565201 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1565193 z) (@lem1565200 z)). Qed.
Lemma lem1565202 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1565203 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1565201 z) (@lem1565202 z)). Qed.
Lemma lem1565204 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1565192 y) (@lem1565203 z)). Qed.
Lemma lem1565205 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1565179 y z) (@lem1565204 y z)). Qed.
Lemma lem1565206 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1565207 (y : real) (z : real) : (term250 y z) = term48.
Proof. exact (TRANS (@lem1565205 y z) (@lem1565206)). Qed.
Lemma lem1565208 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565209 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1565208) (@lem1565207 y z)). Qed.
Lemma lem1565210 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565211 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1565209 y z) (@lem1565210)). Qed.
Lemma lem1565212 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term266.
Proof. exact (EQ_MP (@lem1565211 y z) (@lem1565178 x y z h1)). Qed.
Lemma lem1565214 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565215 : term266 = term267.
Proof. exact (@lem1565214 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1565216 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1565217 : term266 = False.
Proof. exact (TRANS (@lem1565215) (@lem1565216)). Qed.
Lemma lem1565218 (x : real) (y : real) (z : real) (h1 : term180 x y z) : False.
Proof. exact (EQ_MP (@lem1565217) (@lem1565212 x y z h1)). Qed.
Lemma lem1565219 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1565034 x y z h1) (fun h0 : term178 y x z => @lem1565126 y x z h0) (fun h0 : term180 x y z => @lem1565218 x y z h0)). Qed.
Lemma lem1565220 (x : real) (y : real) (z : real) (h1 : term226 x y z) : term226 x y z.
Proof. exact (h1). Qed.
Lemma lem1565221 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1565222 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term221 x y z.
Proof. exact (proj2 (@lem1565221 x y z h1)). Qed.
Lemma lem1565224 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1565222 x y z h1)). Qed.
Lemma lem1565225 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 x z.
Proof. exact (proj1 (@lem1565222 x y z h1)). Qed.
Lemma lem1565227 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 x z.
Proof. exact (proj1 (@lem1565224 x y z h1)). Qed.
Lemma lem1565229 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565230 : term230 = term231.
Proof. exact (@lem1565229 (NUMERAL 0) term210). Qed.
Lemma lem1565231 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565232 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565233 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565232 h1) (fun h1 : term231 = True => @lem1565231)). Qed.
Lemma lem1565234 : term231 = True.
Proof. exact (EQ_MP (@lem1565233) (@lem1565231)). Qed.
Lemma lem1565235 : term230 = True.
Proof. exact (TRANS (@lem1565230) (@lem1565234)). Qed.
Lemma lem1565236 : True = term230.
Proof. exact (SYM (@lem1565235)). Qed.
Lemma lem1565237 : term230.
Proof. exact (EQ_MP (@lem1565236) (@lem0)). Qed.
Lemma lem1565238 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term233 x z.
Proof. exact (conj (@lem1565237) (@lem1565225 x y z h1)). Qed.
Lemma lem1565240 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1565241 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1565240 term236 (term53 x z)). Qed.
Lemma lem1565242 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term237 x z.
Proof. exact (@lem1565241 x z (@lem1565238 x y z h1)). Qed.
Lemma lem1565243 (x : real) (z : real) : (term238 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1565244 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565245 (x : real) (z : real) : (term239 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1565244) (@lem1565243 x z)). Qed.
Lemma lem1565246 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565247 (x : real) (z : real) : (term237 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1565245 x z) (@lem1565246)). Qed.
Lemma lem1565248 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 x z.
Proof. exact (EQ_MP (@lem1565247 x z) (@lem1565242 x y z h1)). Qed.
Lemma lem1565250 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565251 : term230 = term231.
Proof. exact (@lem1565250 (NUMERAL 0) term210). Qed.
Lemma lem1565252 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565253 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565254 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565253 h1) (fun h1 : term231 = True => @lem1565252)). Qed.
Lemma lem1565255 : term231 = True.
Proof. exact (EQ_MP (@lem1565254) (@lem1565252)). Qed.
Lemma lem1565256 : term230 = True.
Proof. exact (TRANS (@lem1565251) (@lem1565255)). Qed.
Lemma lem1565257 : True = term230.
Proof. exact (SYM (@lem1565256)). Qed.
Lemma lem1565258 : term230.
Proof. exact (EQ_MP (@lem1565257) (@lem0)). Qed.
Lemma lem1565259 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term240 x z.
Proof. exact (conj (@lem1565258) (@lem1565227 x y z h1)). Qed.
Lemma lem1565261 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1565262 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1565261 term236 (term52 x z)). Qed.
Lemma lem1565263 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term243 x z.
Proof. exact (@lem1565262 x z (@lem1565259 x y z h1)). Qed.
Lemma lem1565264 (x : real) (z : real) : (term244 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1565265 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565266 (x : real) (z : real) : (term245 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1565265) (@lem1565264 x z)). Qed.
Lemma lem1565267 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565268 (x : real) (z : real) : (term243 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1565266 x z) (@lem1565267)). Qed.
Lemma lem1565269 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1565268 x z) (@lem1565263 x y z h1)). Qed.
Lemma lem1565270 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term246 x z.
Proof. exact (conj (@lem1565269 x y z h1) (@lem1565248 x y z h1)). Qed.
Lemma lem1565272 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1565273 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1565272 (term52 x z) (term53 x z)). Qed.
Lemma lem1565274 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term249 x z.
Proof. exact (@lem1565273 x z (@lem1565270 x y z h1)). Qed.
Lemma lem1565275 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 x (term45 x) (term45 z) z). Qed.
Lemma lem1565276 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483442 term254 x). Qed.
Lemma lem1565278 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565279 : term256 = term48.
Proof. exact (@lem1565278 term210). Qed.
Lemma lem1565280 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565281 : term257 = term258.
Proof. exact (MK_COMB (@lem1565280) (@lem1565279)). Qed.
Lemma lem1565282 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1565283 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1565281) (@lem1565282 x)). Qed.
Lemma lem1565284 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1565276 x) (@lem1565283 x)). Qed.
Lemma lem1565285 (x : real) : (term259 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1565286 (x : real) : (term252 x) = term48.
Proof. exact (TRANS (@lem1565284 x) (@lem1565285 x)). Qed.
Lemma lem1565287 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1565288 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1565287) (@lem1565286 x)). Qed.
Lemma lem1565289 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1565291 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565292 : term256 = term48.
Proof. exact (@lem1565291 term210). Qed.
Lemma lem1565293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565294 : term257 = term258.
Proof. exact (MK_COMB (@lem1565293) (@lem1565292)). Qed.
Lemma lem1565295 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1565296 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1565294) (@lem1565295 z)). Qed.
Lemma lem1565297 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1565289 z) (@lem1565296 z)). Qed.
Lemma lem1565298 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1565299 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1565297 z) (@lem1565298 z)). Qed.
Lemma lem1565300 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1565288 x) (@lem1565299 z)). Qed.
Lemma lem1565301 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1565275 x z) (@lem1565300 x z)). Qed.
Lemma lem1565302 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1565303 (x : real) (z : real) : (term250 x z) = term48.
Proof. exact (TRANS (@lem1565301 x z) (@lem1565302)). Qed.
Lemma lem1565304 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565305 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1565304) (@lem1565303 x z)). Qed.
Lemma lem1565306 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565307 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1565305 x z) (@lem1565306)). Qed.
Lemma lem1565308 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term266.
Proof. exact (EQ_MP (@lem1565307 x z) (@lem1565274 x y z h1)). Qed.
Lemma lem1565310 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565311 : term266 = term267.
Proof. exact (@lem1565310 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1565312 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1565313 : term266 = False.
Proof. exact (TRANS (@lem1565311) (@lem1565312)). Qed.
Lemma lem1565314 (x : real) (y : real) (z : real) (h1 : term222 x y z) : False.
Proof. exact (EQ_MP (@lem1565313) (@lem1565308 x y z h1)). Qed.
Lemma lem1565315 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term224 x y z.
Proof. exact (h1). Qed.
Lemma lem1565316 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term223 x y z.
Proof. exact (proj2 (@lem1565315 x y z h1)). Qed.
Lemma lem1565318 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1565316 x y z h1)). Qed.
Lemma lem1565319 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term56 y z.
Proof. exact (proj1 (@lem1565316 x y z h1)). Qed.
Lemma lem1565320 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term72 y z.
Proof. exact (proj2 (@lem1565318 x y z h1)). Qed.
Lemma lem1565323 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565324 : term230 = term231.
Proof. exact (@lem1565323 (NUMERAL 0) term210). Qed.
Lemma lem1565325 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565326 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565327 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565326 h1) (fun h1 : term231 = True => @lem1565325)). Qed.
Lemma lem1565328 : term231 = True.
Proof. exact (EQ_MP (@lem1565327) (@lem1565325)). Qed.
Lemma lem1565329 : term230 = True.
Proof. exact (TRANS (@lem1565324) (@lem1565328)). Qed.
Lemma lem1565330 : True = term230.
Proof. exact (SYM (@lem1565329)). Qed.
Lemma lem1565331 : term230.
Proof. exact (EQ_MP (@lem1565330) (@lem0)). Qed.
Lemma lem1565332 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term233 y z.
Proof. exact (conj (@lem1565331) (@lem1565319 x y z h1)). Qed.
Lemma lem1565334 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1565335 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1565334 term236 (term53 y z)). Qed.
Lemma lem1565336 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term237 y z.
Proof. exact (@lem1565335 y z (@lem1565332 x y z h1)). Qed.
Lemma lem1565337 (y : real) (z : real) : (term238 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1565338 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565339 (y : real) (z : real) : (term239 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1565338) (@lem1565337 y z)). Qed.
Lemma lem1565340 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565341 (y : real) (z : real) : (term237 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1565339 y z) (@lem1565340)). Qed.
Lemma lem1565342 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1565341 y z) (@lem1565336 x y z h1)). Qed.
Lemma lem1565344 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565345 : term230 = term231.
Proof. exact (@lem1565344 (NUMERAL 0) term210). Qed.
Lemma lem1565346 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1565347 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1565348 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1565347 h1) (fun h1 : term231 = True => @lem1565346)). Qed.
Lemma lem1565349 : term231 = True.
Proof. exact (EQ_MP (@lem1565348) (@lem1565346)). Qed.
Lemma lem1565350 : term230 = True.
Proof. exact (TRANS (@lem1565345) (@lem1565349)). Qed.
Lemma lem1565351 : True = term230.
Proof. exact (SYM (@lem1565350)). Qed.
Lemma lem1565352 : term230.
Proof. exact (EQ_MP (@lem1565351) (@lem0)). Qed.
Lemma lem1565353 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term240 y z.
Proof. exact (conj (@lem1565352) (@lem1565320 x y z h1)). Qed.
Lemma lem1565355 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1565356 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1565355 term236 (term52 y z)). Qed.
Lemma lem1565357 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term243 y z.
Proof. exact (@lem1565356 y z (@lem1565353 x y z h1)). Qed.
Lemma lem1565358 (y : real) (z : real) : (term244 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1565359 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565360 (y : real) (z : real) : (term245 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1565359) (@lem1565358 y z)). Qed.
Lemma lem1565361 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565362 (y : real) (z : real) : (term243 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1565360 y z) (@lem1565361)). Qed.
Lemma lem1565363 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1565362 y z) (@lem1565357 x y z h1)). Qed.
Lemma lem1565364 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term246 y z.
Proof. exact (conj (@lem1565363 x y z h1) (@lem1565342 x y z h1)). Qed.
Lemma lem1565366 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1565367 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1565366 (term52 y z) (term53 y z)). Qed.
Lemma lem1565368 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term249 y z.
Proof. exact (@lem1565367 y z (@lem1565364 x y z h1)). Qed.
Lemma lem1565369 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1565370 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483442 term254 y). Qed.
Lemma lem1565372 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565373 : term256 = term48.
Proof. exact (@lem1565372 term210). Qed.
Lemma lem1565374 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565375 : term257 = term258.
Proof. exact (MK_COMB (@lem1565374) (@lem1565373)). Qed.
Lemma lem1565376 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1565377 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1565375) (@lem1565376 y)). Qed.
Lemma lem1565378 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1565370 y) (@lem1565377 y)). Qed.
Lemma lem1565379 (y : real) : (term259 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1565380 (y : real) : (term252 y) = term48.
Proof. exact (TRANS (@lem1565378 y) (@lem1565379 y)). Qed.
Lemma lem1565381 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1565382 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1565381) (@lem1565380 y)). Qed.
Lemma lem1565383 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1565385 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1565386 : term256 = term48.
Proof. exact (@lem1565385 term210). Qed.
Lemma lem1565387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1565388 : term257 = term258.
Proof. exact (MK_COMB (@lem1565387) (@lem1565386)). Qed.
Lemma lem1565389 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1565390 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1565388) (@lem1565389 z)). Qed.
Lemma lem1565391 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1565383 z) (@lem1565390 z)). Qed.
Lemma lem1565392 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1565393 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1565391 z) (@lem1565392 z)). Qed.
Lemma lem1565394 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1565382 y) (@lem1565393 z)). Qed.
Lemma lem1565395 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1565369 y z) (@lem1565394 y z)). Qed.
Lemma lem1565396 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1565397 (y : real) (z : real) : (term250 y z) = term48.
Proof. exact (TRANS (@lem1565395 y z) (@lem1565396)). Qed.
Lemma lem1565398 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565399 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1565398) (@lem1565397 y z)). Qed.
Lemma lem1565400 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1565401 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1565399 y z) (@lem1565400)). Qed.
Lemma lem1565402 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term266.
Proof. exact (EQ_MP (@lem1565401 y z) (@lem1565368 x y z h1)). Qed.
Lemma lem1565404 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1565405 : term266 = term267.
Proof. exact (@lem1565404 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1565406 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1565407 : term266 = False.
Proof. exact (TRANS (@lem1565405) (@lem1565406)). Qed.
Lemma lem1565408 (x : real) (y : real) (z : real) (h1 : term224 x y z) : False.
Proof. exact (EQ_MP (@lem1565407) (@lem1565402 x y z h1)). Qed.
Lemma lem1565409 (x : real) (y : real) (z : real) (h1 : term226 x y z) : False.
Proof. exact (or_elim (@lem1565220 x y z h1) (fun h0 : term222 x y z => @lem1565314 x y z h0) (fun h0 : term224 x y z => @lem1565408 x y z h0)). Qed.
Lemma lem1565410 (x : real) (y : real) (z : real) (h1 : term228 x y z) : False.
Proof. exact (or_elim (@lem1565033 x y z h1) (fun h0 : term183 x y z => @lem1565219 x y z h0) (fun h0 : term226 x y z => @lem1565409 x y z h0)). Qed.
Lemma lem1565411 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term163 x y z.
Proof. exact (h1). Qed.
Lemma lem1565412 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term228 x y z.
Proof. exact (EQ_MP (@lem1565032 x y z) (@lem1565411 x y z h1)). Qed.
Lemma lem1565413 (x : real) (y : real) (z : real) (h1 : term163 x y z) : (term228 x y z) = False.
Proof. exact (prop_ext (fun h2 : term228 x y z => @lem1565410 x y z h2) (fun h2 : False => @lem1565412 x y z h1)). Qed.
Lemma lem1565414 (x : real) (y : real) (z : real) (h1 : term163 x y z) : False.
Proof. exact (EQ_MP (@lem1565413 x y z h1) (@lem1565412 x y z h1)). Qed.
Lemma lem1565415 (x : real) (y : real) (h1 : term165 x y) : term165 x y.
Proof. exact (h1). Qed.
Lemma lem1565416 (x : real) (y : real) (h1 : term165 x y) : False.
Proof. exact (ex_elim (@lem1565415 x y h1) (fun z : real => fun h0 : term164 x y z => @lem1565414 x y z h0)). Qed.
Lemma lem1565417 (x : real) (h1 : term167 x) : term167 x.
Proof. exact (h1). Qed.
Lemma lem1565418 (x : real) (h1 : term167 x) : False.
Proof. exact (ex_elim (@lem1565417 x h1) (fun y : real => fun h0 : term166 x y => @lem1565416 x y h0)). Qed.
Lemma lem1565419 (h1 : term169) : term169.
Proof. exact (h1). Qed.
Lemma lem1565420 (h1 : term169) : False.
Proof. exact (ex_elim (@lem1565419 h1) (fun x : real => fun h0 : term168 x => @lem1565418 x h0)). Qed.
Lemma lem1565421 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1565422 (h1 : term32) : term169.
Proof. exact (EQ_MP (@lem1564712) (@lem1565421 h1)). Qed.
Lemma lem1565423 (h1 : term32) : term169 = False.
Proof. exact (prop_ext (fun h2 : term169 => @lem1565420 h2) (fun h2 : False => @lem1565422 h1)). Qed.
Lemma lem1565424 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1565423 h1) (@lem1565422 h1)). Qed.
Lemma lem1565425 : term268.
Proof. exact (fun h0 : term32 => @lem1565424 h0). Qed.
Lemma lem1565426 : term269.
Proof. exact (@lem1386578 term270). Qed.
Lemma lem1565427 : term270.
Proof. exact (@lem1565426 (@lem1565425)). Qed.

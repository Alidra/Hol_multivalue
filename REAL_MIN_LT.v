Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_LT_term_abbrevs.
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
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1569982 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17160 (real_lt x z) (real_lt y z)). Qed.
Lemma lem1569988 (x : real) (y : real) (z : real) : (term2 x y z) = (term2 x y z).
Proof. exact (eq_refl (term2 x y z)). Qed.
Lemma lem1569990 (x : real) (y : real) (z : real) : (term3 x y z) = (term3 x y z).
Proof. exact (eq_refl (term3 x y z)). Qed.
Lemma lem1569991 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (MK_COMB (@lem1569990 x y z) (@lem1569982 x y z)). Qed.
Lemma lem1569992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569993 (x : real) (y : real) (z : real) : (term6 x y z) = (term7 x y z).
Proof. exact (MK_COMB (@lem1569992) (@lem1569991 x y z)). Qed.
Lemma lem1569994 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1569993 x y z) (@lem1569988 x y z)). Qed.
Lemma lem1569995 (x : real) (y : real) (z : real) : (term10 x y z) = (term8 x y z).
Proof. exact (@lem17646 (term11 x y z) (term12 x y z)). Qed.
Lemma lem1569996 (x : real) (y : real) (z : real) : (term10 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1569995 x y z) (@lem1569994 x y z)). Qed.
Lemma lem1569997 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1569998 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1569997 (term17 x y)). Qed.
Lemma lem1569999 (x : real) (y : real) (z : real) : (term18 x y z) = ((term11 x y z) = (term12 x y z)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1570000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1570001 (x : real) (y : real) (z : real) : (term19 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1570000) (@lem1569999 x y z)). Qed.
Lemma lem1570002 (x : real) (y : real) (z : real) : (term19 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1570001 x y z) (@lem1569996 x y z)). Qed.
Lemma lem1570003 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1570002 x y z)). Qed.
Lemma lem1570004 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570005 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1570004) (@lem1570003 x y)). Qed.
Lemma lem1570006 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1569998 x y) (@lem1570005 x y)). Qed.
Lemma lem1570007 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1570008 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1570007 (term25 x)). Qed.
Lemma lem1570009 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1570010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1570011 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1570010) (@lem1570009 x y)). Qed.
Lemma lem1570012 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1570011 x y) (@lem1570006 x y)). Qed.
Lemma lem1570013 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1570012 x y)). Qed.
Lemma lem1570014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570015 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1570014) (@lem1570013 x)). Qed.
Lemma lem1570016 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1570008 x) (@lem1570015 x)). Qed.
Lemma lem1570017 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1570018 : term32 = term33.
Proof. exact (@lem1570017 term34). Qed.
Lemma lem1570019 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1570020 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1570021 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1570020) (@lem1570019 x)). Qed.
Lemma lem1570022 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1570021 x) (@lem1570016 x)). Qed.
Lemma lem1570023 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1570022 x)). Qed.
Lemma lem1570024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570025 : term33 = term40.
Proof. exact (MK_COMB (@lem1570024) (@lem1570023)). Qed.
Lemma lem1570027 : term32 = term40.
Proof. exact (TRANS (@lem1570018) (@lem1570025)). Qed.
Lemma lem1570054 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1570055 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1570054 x y z)). Qed.
Lemma lem1570056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570057 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1570056) (@lem1570055 x y)). Qed.
Lemma lem1570058 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1570057 x y)). Qed.
Lemma lem1570059 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570060 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1570059) (@lem1570058 x)). Qed.
Lemma lem1570061 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1570060 x)). Qed.
Lemma lem1570062 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570063 : term40 = term40.
Proof. exact (MK_COMB (@lem1570062) (@lem1570061)). Qed.
Lemma lem1570064 : term32 = term40.
Proof. exact (TRANS (@lem1570027) (@lem1570063)). Qed.
Lemma lem1570065 (z : real) (x : real) (y : real) : (term11 x y z) = (term41 z x y).
Proof. exact (@lem1483521 z (real_min x y)). Qed.
Lemma lem1570078 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1570079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570080 (z : real) (x : real) (y : real) : (term44 z x y) = (term45 z x y).
Proof. exact (MK_COMB (@lem1570079) (@lem1570078 z x y)). Qed.
Lemma lem1570081 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570082 (z : real) (x : real) (y : real) : (term41 z x y) = (term47 z x y).
Proof. exact (MK_COMB (@lem1570080 z x y) (@lem1570081)). Qed.
Lemma lem1570083 (z : real) (x : real) (y : real) : (term11 x y z) = (term47 z x y).
Proof. exact (TRANS (@lem1570065 z x y) (@lem1570082 z x y)). Qed.
Lemma lem1570084 (x : real) (z : real) : (term48 x z) = (term49 x z).
Proof. exact (@lem1483531 x z). Qed.
Lemma lem1570097 (x : real) (z : real) : (real_sub x z) = (term50 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1570098 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570099 (x : real) (z : real) : (term51 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1570098) (@lem1570097 x z)). Qed.
Lemma lem1570100 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570101 (x : real) (z : real) : (term49 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1570099 x z) (@lem1570100)). Qed.
Lemma lem1570102 (x : real) (z : real) : (term48 x z) = (term53 x z).
Proof. exact (TRANS (@lem1570084 x z) (@lem1570101 x z)). Qed.
Lemma lem1570103 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483531 y z). Qed.
Lemma lem1570116 (y : real) (z : real) : (real_sub y z) = (term50 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1570117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570118 (y : real) (z : real) : (term51 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1570117) (@lem1570116 y z)). Qed.
Lemma lem1570119 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570120 (y : real) (z : real) : (term49 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1570118 y z) (@lem1570119)). Qed.
Lemma lem1570121 (y : real) (z : real) : (term48 y z) = (term53 y z).
Proof. exact (TRANS (@lem1570103 y z) (@lem1570120 y z)). Qed.
Lemma lem1570122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570123 (x : real) (z : real) : (term54 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1570122) (@lem1570102 x z)). Qed.
Lemma lem1570124 (x : real) (y : real) (z : real) : (term1 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1570123 x z) (@lem1570121 y z)). Qed.
Lemma lem1570125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570126 (z : real) (x : real) (y : real) : (term3 x y z) = (term57 z x y).
Proof. exact (MK_COMB (@lem1570125) (@lem1570083 z x y)). Qed.
Lemma lem1570127 (x : real) (y : real) (z : real) : (term5 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem1570126 z x y) (@lem1570124 x y z)). Qed.
Lemma lem1570128 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483531 (real_min x y) z). Qed.
Lemma lem1570134 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1570139 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (@lem1483488 (term64 z) (real_min x y)). Qed.
Lemma lem1570141 (z : real) (x : real) (y : real) : (term61 x y z) = (term63 z x y).
Proof. exact (TRANS (@lem1570134 x y z) (@lem1570139 z x y)). Qed.
Lemma lem1570142 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570143 (z : real) (x : real) (y : real) : (term65 x y z) = (term66 z x y).
Proof. exact (MK_COMB (@lem1570142) (@lem1570141 z x y)). Qed.
Lemma lem1570144 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570145 (z : real) (x : real) (y : real) : (term60 x y z) = (term67 z x y).
Proof. exact (MK_COMB (@lem1570143 z x y) (@lem1570144)). Qed.
Lemma lem1570146 (z : real) (x : real) (y : real) : (term59 x y z) = (term67 z x y).
Proof. exact (TRANS (@lem1570128 x y z) (@lem1570145 z x y)). Qed.
Lemma lem1570147 (z : real) (x : real) : (real_lt x z) = (term68 z x).
Proof. exact (@lem1483521 z x). Qed.
Lemma lem1570153 (z : real) (x : real) : (real_sub z x) = (term50 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1570158 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1570160 (x : real) (z : real) : (real_sub z x) = (term69 x z).
Proof. exact (TRANS (@lem1570153 z x) (@lem1570158 x z)). Qed.
Lemma lem1570161 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570162 (x : real) (z : real) : (term70 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1570161) (@lem1570160 x z)). Qed.
Lemma lem1570163 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570164 (x : real) (z : real) : (term68 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1570162 x z) (@lem1570163)). Qed.
Lemma lem1570165 (x : real) (z : real) : (real_lt x z) = (term72 x z).
Proof. exact (TRANS (@lem1570147 z x) (@lem1570164 x z)). Qed.
Lemma lem1570166 (z : real) (y : real) : (real_lt y z) = (term68 z y).
Proof. exact (@lem1483521 z y). Qed.
Lemma lem1570172 (z : real) (y : real) : (real_sub z y) = (term50 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1570177 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1570179 (y : real) (z : real) : (real_sub z y) = (term69 y z).
Proof. exact (TRANS (@lem1570172 z y) (@lem1570177 y z)). Qed.
Lemma lem1570180 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570181 (y : real) (z : real) : (term70 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1570180) (@lem1570179 y z)). Qed.
Lemma lem1570182 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570183 (y : real) (z : real) : (term68 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1570181 y z) (@lem1570182)). Qed.
Lemma lem1570184 (y : real) (z : real) : (real_lt y z) = (term72 y z).
Proof. exact (TRANS (@lem1570166 z y) (@lem1570183 y z)). Qed.
Lemma lem1570185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570186 (x : real) (z : real) : (term73 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1570185) (@lem1570165 x z)). Qed.
Lemma lem1570187 (x : real) (y : real) (z : real) : (term12 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1570186 x z) (@lem1570184 y z)). Qed.
Lemma lem1570188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570189 (z : real) (x : real) (y : real) : (term76 x y z) = (term77 z x y).
Proof. exact (MK_COMB (@lem1570188) (@lem1570146 z x y)). Qed.
Lemma lem1570190 (x : real) (y : real) (z : real) : (term2 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1570189 z x y) (@lem1570187 x y z)). Qed.
Lemma lem1570191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570192 (x : real) (y : real) (z : real) : (term7 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1570191) (@lem1570127 x y z)). Qed.
Lemma lem1570193 (x : real) (y : real) (z : real) : (term9 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1570192 x y z) (@lem1570190 x y z)). Qed.
Lemma lem1570194 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1570193 x y z)). Qed.
Lemma lem1570195 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570196 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1570195) (@lem1570194 x y)). Qed.
Lemma lem1570197 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1570196 x y)). Qed.
Lemma lem1570198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570199 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1570198) (@lem1570197 x)). Qed.
Lemma lem1570200 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1570199 x)). Qed.
Lemma lem1570201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570202 : term40 = term86.
Proof. exact (MK_COMB (@lem1570201) (@lem1570200)). Qed.
Lemma lem1570203 : term32 = term86.
Proof. exact (TRANS (@lem1570064) (@lem1570202)). Qed.
Lemma lem1570213 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1570214 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1570213 real P Q). Qed.
Lemma lem1570215 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1570214 (term93 x y) (term94 x y)). Qed.
Lemma lem1570216 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1570217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570218 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1570217) (@lem1570216 x y z)). Qed.
Lemma lem1570219 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1570220 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1570218 x y z) (@lem1570219 x y z)). Qed.
Lemma lem1570221 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1570220 x y z)). Qed.
Lemma lem1570222 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570223 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1570222) (@lem1570221 x y)). Qed.
Lemma lem1570224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570225 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1570224) (@lem1570223 x y)). Qed.
Lemma lem1570226 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1570227 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1570226 x y z)). Qed.
Lemma lem1570228 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570229 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1570228) (@lem1570227 x y)). Qed.
Lemma lem1570230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570231 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1570230) (@lem1570229 x y)). Qed.
Lemma lem1570232 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1570233 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1570232 x y z)). Qed.
Lemma lem1570234 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570235 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1570234) (@lem1570233 x y)). Qed.
Lemma lem1570236 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1570231 x y) (@lem1570235 x y)). Qed.
Lemma lem1570237 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1570225 x y) (@lem1570236 x y)). Qed.
Lemma lem1570238 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1570237 x y) (@lem1570215 x y)). Qed.
Lemma lem1570335 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1570238 x y)). Qed.
Lemma lem1570336 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570337 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1570336) (@lem1570335 x)). Qed.
Lemma lem1570339 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1570340 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1570339 real P Q). Qed.
Lemma lem1570341 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1570340 (term115 x) (term116 x)). Qed.
Lemma lem1570342 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1570343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570344 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1570343) (@lem1570342 x y)). Qed.
Lemma lem1570345 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1570346 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1570344 x y) (@lem1570345 x y)). Qed.
Lemma lem1570347 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1570346 x y)). Qed.
Lemma lem1570348 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570349 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1570348) (@lem1570347 x)). Qed.
Lemma lem1570350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570351 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1570350) (@lem1570349 x)). Qed.
Lemma lem1570352 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1570353 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1570352 x y)). Qed.
Lemma lem1570354 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570355 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1570354) (@lem1570353 x)). Qed.
Lemma lem1570356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570357 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1570356) (@lem1570355 x)). Qed.
Lemma lem1570358 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1570359 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1570358 x y)). Qed.
Lemma lem1570360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570361 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1570360) (@lem1570359 x)). Qed.
Lemma lem1570362 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1570357 x) (@lem1570361 x)). Qed.
Lemma lem1570363 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1570351 x) (@lem1570362 x)). Qed.
Lemma lem1570364 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1570363 x) (@lem1570341 x)). Qed.
Lemma lem1570469 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1570337 x) (@lem1570364 x)). Qed.
Lemma lem1570470 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1570469 x)). Qed.
Lemma lem1570471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570472 : term86 = term134.
Proof. exact (MK_COMB (@lem1570471) (@lem1570470)). Qed.
Lemma lem1570474 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1570475 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1570474 real P Q). Qed.
Lemma lem1570476 : term135 = term136.
Proof. exact (@lem1570475 term137 term138). Qed.
Lemma lem1570477 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1570478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570479 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1570478) (@lem1570477 x)). Qed.
Lemma lem1570480 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1570481 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1570479 x) (@lem1570480 x)). Qed.
Lemma lem1570482 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1570481 x)). Qed.
Lemma lem1570483 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570484 : term135 = term134.
Proof. exact (MK_COMB (@lem1570483) (@lem1570482)). Qed.
Lemma lem1570485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570486 : term144 = term145.
Proof. exact (MK_COMB (@lem1570485) (@lem1570484)). Qed.
Lemma lem1570487 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1570488 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1570487 x)). Qed.
Lemma lem1570489 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570490 : term147 = term148.
Proof. exact (MK_COMB (@lem1570489) (@lem1570488)). Qed.
Lemma lem1570491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570492 : term149 = term150.
Proof. exact (MK_COMB (@lem1570491) (@lem1570490)). Qed.
Lemma lem1570493 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1570494 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1570493 x)). Qed.
Lemma lem1570495 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570496 : term152 = term153.
Proof. exact (MK_COMB (@lem1570495) (@lem1570494)). Qed.
Lemma lem1570497 : term136 = term154.
Proof. exact (MK_COMB (@lem1570492) (@lem1570496)). Qed.
Lemma lem1570498 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1570486) (@lem1570497)). Qed.
Lemma lem1570499 : term134 = term154.
Proof. exact (EQ_MP (@lem1570498) (@lem1570476)). Qed.
Lemma lem1570612 : term86 = term154.
Proof. exact (TRANS (@lem1570472) (@lem1570499)). Qed.
Lemma lem1570614 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1570615 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1570614 real P Q). Qed.
Lemma lem1570616 : term136 = term135.
Proof. exact (@lem1570615 term137 term138). Qed.
Lemma lem1570617 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1570618 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1570617 x)). Qed.
Lemma lem1570619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570620 : term147 = term148.
Proof. exact (MK_COMB (@lem1570619) (@lem1570618)). Qed.
Lemma lem1570621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570622 : term149 = term150.
Proof. exact (MK_COMB (@lem1570621) (@lem1570620)). Qed.
Lemma lem1570623 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1570624 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1570623 x)). Qed.
Lemma lem1570625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570626 : term152 = term153.
Proof. exact (MK_COMB (@lem1570625) (@lem1570624)). Qed.
Lemma lem1570627 : term136 = term154.
Proof. exact (MK_COMB (@lem1570622) (@lem1570626)). Qed.
Lemma lem1570628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570629 : term155 = term156.
Proof. exact (MK_COMB (@lem1570628) (@lem1570627)). Qed.
Lemma lem1570630 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1570631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570632 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1570631) (@lem1570630 x)). Qed.
Lemma lem1570633 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1570634 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1570632 x) (@lem1570633 x)). Qed.
Lemma lem1570635 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1570634 x)). Qed.
Lemma lem1570636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570637 : term135 = term134.
Proof. exact (MK_COMB (@lem1570636) (@lem1570635)). Qed.
Lemma lem1570638 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1570629) (@lem1570637)). Qed.
Lemma lem1570639 : term154 = term134.
Proof. exact (EQ_MP (@lem1570638) (@lem1570616)). Qed.
Lemma lem1570641 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1570642 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1570641 real P Q). Qed.
Lemma lem1570643 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1570642 (term115 x) (term116 x)). Qed.
Lemma lem1570644 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1570645 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1570644 x y)). Qed.
Lemma lem1570646 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570647 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1570646) (@lem1570645 x)). Qed.
Lemma lem1570648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570649 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1570648) (@lem1570647 x)). Qed.
Lemma lem1570650 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1570651 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1570650 x y)). Qed.
Lemma lem1570652 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570653 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1570652) (@lem1570651 x)). Qed.
Lemma lem1570654 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1570649 x) (@lem1570653 x)). Qed.
Lemma lem1570655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570656 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1570655) (@lem1570654 x)). Qed.
Lemma lem1570657 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1570658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570659 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1570658) (@lem1570657 x y)). Qed.
Lemma lem1570660 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1570661 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1570659 x y) (@lem1570660 x y)). Qed.
Lemma lem1570662 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1570661 x y)). Qed.
Lemma lem1570663 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570664 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1570663) (@lem1570662 x)). Qed.
Lemma lem1570665 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1570656 x) (@lem1570664 x)). Qed.
Lemma lem1570666 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1570665 x) (@lem1570643 x)). Qed.
Lemma lem1570668 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1570669 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1570668 real P Q). Qed.
Lemma lem1570670 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1570669 (term93 x y) (term94 x y)). Qed.
Lemma lem1570671 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1570672 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1570671 x y z)). Qed.
Lemma lem1570673 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570674 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1570673) (@lem1570672 x y)). Qed.
Lemma lem1570675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570676 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1570675) (@lem1570674 x y)). Qed.
Lemma lem1570677 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1570678 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1570677 x y z)). Qed.
Lemma lem1570679 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570680 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1570679) (@lem1570678 x y)). Qed.
Lemma lem1570681 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1570676 x y) (@lem1570680 x y)). Qed.
Lemma lem1570682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1570683 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1570682) (@lem1570681 x y)). Qed.
Lemma lem1570684 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1570685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570686 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1570685) (@lem1570684 x y z)). Qed.
Lemma lem1570687 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1570688 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1570686 x y z) (@lem1570687 x y z)). Qed.
Lemma lem1570689 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1570688 x y z)). Qed.
Lemma lem1570690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570691 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1570690) (@lem1570689 x y)). Qed.
Lemma lem1570692 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1570683 x y) (@lem1570691 x y)). Qed.
Lemma lem1570693 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1570692 x y) (@lem1570670 x y)). Qed.
Lemma lem1570694 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1570693 x y)). Qed.
Lemma lem1570695 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570696 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1570695) (@lem1570694 x)). Qed.
Lemma lem1570697 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1570666 x) (@lem1570696 x)). Qed.
Lemma lem1570698 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1570697 x)). Qed.
Lemma lem1570699 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570700 : term134 = term86.
Proof. exact (MK_COMB (@lem1570699) (@lem1570698)). Qed.
Lemma lem1570701 : term154 = term86.
Proof. exact (TRANS (@lem1570639) (@lem1570700)). Qed.
Lemma lem1570702 : term86 = term86.
Proof. exact (TRANS (@lem1570612) (@lem1570701)). Qed.
Lemma lem1570705 : term32 = term86.
Proof. exact (TRANS (@lem1570203) (@lem1570702)). Qed.
Lemma lem1570722 (x : real) (y : real) (z : real) : (term78 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term72 x z) (term67 z x y) (term72 y z)). Qed.
Lemma lem1570737 (x : real) (y : real) (z : real) : (term79 x y z) = (term79 x y z).
Proof. exact (eq_refl (term79 x y z)). Qed.
Lemma lem1570738 (x : real) (y : real) (z : real) : (term80 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1570737 x y z) (@lem1570722 x y z)). Qed.
Lemma lem1570739 (x : real) (y : real) : (term81 x y) = (term163 x y).
Proof. exact (fun_ext (fun z : real => @lem1570738 x y z)). Qed.
Lemma lem1570740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570741 (x : real) (y : real) : (term82 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1570740) (@lem1570739 x y)). Qed.
Lemma lem1570742 (x : real) : (term83 x) = (term165 x).
Proof. exact (fun_ext (fun y : real => @lem1570741 x y)). Qed.
Lemma lem1570743 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570744 (x : real) : (term84 x) = (term166 x).
Proof. exact (MK_COMB (@lem1570743) (@lem1570742 x)). Qed.
Lemma lem1570745 : term85 = term167.
Proof. exact (fun_ext (fun x : real => @lem1570744 x)). Qed.
Lemma lem1570746 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1570747 : term86 = term168.
Proof. exact (MK_COMB (@lem1570746) (@lem1570745)). Qed.
Lemma lem1570748 : term32 = term168.
Proof. exact (TRANS (@lem1570705) (@lem1570747)). Qed.
Lemma lem1570750 (x : real) (y : real) (z : real) : (term169 z x y) = (term58 x y z).
Proof. exact (eq_refl (term169 z x y)). Qed.
Lemma lem1570751 (z : real) (x : real) (y : real) : (term58 x y z) = (term169 z x y).
Proof. exact (SYM (@lem1570750 x y z)). Qed.
Lemma lem1570752 (x : real) (z : real) (y : real) : (term169 z x y) = (term170 x z y).
Proof. exact (@lem1483429 x (term171 x y z) y). Qed.
Lemma lem1570753 (x : real) (z : real) (y : real) : (term58 x y z) = (term170 x z y).
Proof. exact (TRANS (@lem1570751 z x y) (@lem1570752 x z y)). Qed.
Lemma lem1570754 (x : real) (y : real) (z : real) : (term172 x z y) = (term173 x y z).
Proof. exact (eq_refl (term172 x z y)). Qed.
Lemma lem1570755 (x : real) (y : real) : (term174 x y) = (term174 x y).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1570756 (x : real) (y : real) (z : real) : (term175 x z y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1570755 x y) (@lem1570754 x y z)). Qed.
Lemma lem1570757 (x : real) (y : real) (z : real) : (term177 y z x) = (term178 x y z).
Proof. exact (eq_refl (term177 y z x)). Qed.
Lemma lem1570758 (y : real) (x : real) : (term179 y x) = (term179 y x).
Proof. exact (eq_refl (term179 y x)). Qed.
Lemma lem1570759 (x : real) (y : real) (z : real) : (term180 y z x) = (term181 x y z).
Proof. exact (MK_COMB (@lem1570758 y x) (@lem1570757 x y z)). Qed.
Lemma lem1570760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570761 (x : real) (y : real) (z : real) : (term182 y z x) = (term183 x y z).
Proof. exact (MK_COMB (@lem1570760) (@lem1570759 x y z)). Qed.
Lemma lem1570762 (x : real) (y : real) (z : real) : (term170 x z y) = (term184 x y z).
Proof. exact (MK_COMB (@lem1570761 x y z) (@lem1570756 x y z)). Qed.
Lemma lem1570763 (x : real) (y : real) (z : real) : (term185 x y z) = (term185 x y z).
Proof. exact (eq_refl (term185 x y z)). Qed.
Lemma lem1570764 (x : real) (y : real) (z : real) : ((term58 x y z) = (term170 x z y)) = ((term58 x y z) = (term184 x y z)).
Proof. exact (MK_COMB (@lem1570763 x y z) (@lem1570762 x y z)). Qed.
Lemma lem1570765 (x : real) (y : real) (z : real) : (term58 x y z) = (term184 x y z).
Proof. exact (EQ_MP (@lem1570764 x y z) (@lem1570753 x z y)). Qed.
Lemma lem1570766 (y : real) (x : real) : (real_ge y x) = (term49 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1570772 (y : real) (x : real) : (real_sub y x) = (term50 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1570777 (x : real) (y : real) : (term50 y x) = (term69 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1570779 (x : real) (y : real) : (real_sub y x) = (term69 x y).
Proof. exact (TRANS (@lem1570772 y x) (@lem1570777 x y)). Qed.
Lemma lem1570780 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570781 (x : real) (y : real) : (term51 y x) = (term186 x y).
Proof. exact (MK_COMB (@lem1570780) (@lem1570779 x y)). Qed.
Lemma lem1570782 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570783 (x : real) (y : real) : (term49 y x) = (term187 x y).
Proof. exact (MK_COMB (@lem1570781 x y) (@lem1570782)). Qed.
Lemma lem1570784 (x : real) (y : real) : (real_ge y x) = (term187 x y).
Proof. exact (TRANS (@lem1570766 y x) (@lem1570783 x y)). Qed.
Lemma lem1570785 (z : real) (x : real) : (term188 z x) = (term189 z x).
Proof. exact (@lem1483525 (term50 z x) term46). Qed.
Lemma lem1570786 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570799 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1570800 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1570801 (x : real) (z : real) : (term190 z x) = (term191 x z).
Proof. exact (MK_COMB (@lem1570800) (@lem1570799 x z)). Qed.
Lemma lem1570802 (x : real) (z : real) : (term192 z x) = (term193 x z).
Proof. exact (MK_COMB (@lem1570801 x z) (@lem1570786)). Qed.
Lemma lem1570803 (x : real) (z : real) : (term193 x z) = (term194 x z).
Proof. exact (@lem1483519 (term69 x z) term46). Qed.
Lemma lem1570805 (x : nat) : (term195 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1570806 : term196 = term46.
Proof. exact (@lem1570805 term197). Qed.
Lemma lem1570807 (x : real) (z : real) : (term198 x z) = (term198 x z).
Proof. exact (eq_refl (term198 x z)). Qed.
Lemma lem1570808 (x : real) (z : real) : (term194 x z) = (term199 x z).
Proof. exact (MK_COMB (@lem1570807 x z) (@lem1570806)). Qed.
Lemma lem1570809 (x : real) (z : real) : (term199 x z) = (term69 x z).
Proof. exact (@lem1483450 (term69 x z)). Qed.
Lemma lem1570810 (x : real) (z : real) : (term194 x z) = (term69 x z).
Proof. exact (TRANS (@lem1570808 x z) (@lem1570809 x z)). Qed.
Lemma lem1570811 (x : real) (z : real) : (term193 x z) = (term69 x z).
Proof. exact (TRANS (@lem1570803 x z) (@lem1570810 x z)). Qed.
Lemma lem1570812 (x : real) (z : real) : (term192 z x) = (term69 x z).
Proof. exact (TRANS (@lem1570802 x z) (@lem1570811 x z)). Qed.
Lemma lem1570813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570814 (x : real) (z : real) : (term200 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1570813) (@lem1570812 x z)). Qed.
Lemma lem1570815 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570816 (x : real) (z : real) : (term189 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1570814 x z) (@lem1570815)). Qed.
Lemma lem1570817 (x : real) (z : real) : (term188 z x) = (term72 x z).
Proof. exact (TRANS (@lem1570785 z x) (@lem1570816 x z)). Qed.
Lemma lem1570818 (x : real) (z : real) : (term53 x z) = (term201 x z).
Proof. exact (@lem1483527 (term50 x z) term46). Qed.
Lemma lem1570836 (x : real) (z : real) : (term192 x z) = (term202 x z).
Proof. exact (@lem1483519 (term50 x z) term46). Qed.
Lemma lem1570838 (x : nat) : (term195 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1570839 : term196 = term46.
Proof. exact (@lem1570838 term197). Qed.
Lemma lem1570840 (x : real) (z : real) : (term203 x z) = (term203 x z).
Proof. exact (eq_refl (term203 x z)). Qed.
Lemma lem1570841 (x : real) (z : real) : (term202 x z) = (term204 x z).
Proof. exact (MK_COMB (@lem1570840 x z) (@lem1570839)). Qed.
Lemma lem1570842 (x : real) (z : real) : (term204 x z) = (term50 x z).
Proof. exact (@lem1483450 (term50 x z)). Qed.
Lemma lem1570843 (x : real) (z : real) : (term202 x z) = (term50 x z).
Proof. exact (TRANS (@lem1570841 x z) (@lem1570842 x z)). Qed.
Lemma lem1570845 (x : real) (z : real) : (term192 x z) = (term50 x z).
Proof. exact (TRANS (@lem1570836 x z) (@lem1570843 x z)). Qed.
Lemma lem1570846 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570847 (x : real) (z : real) : (term205 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1570846) (@lem1570845 x z)). Qed.
Lemma lem1570848 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570849 (x : real) (z : real) : (term201 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1570847 x z) (@lem1570848)). Qed.
Lemma lem1570850 (x : real) (z : real) : (term53 x z) = (term53 x z).
Proof. exact (TRANS (@lem1570818 x z) (@lem1570849 x z)). Qed.
Lemma lem1570851 (y : real) (z : real) : (term53 y z) = (term201 y z).
Proof. exact (@lem1483527 (term50 y z) term46). Qed.
Lemma lem1570869 (y : real) (z : real) : (term192 y z) = (term202 y z).
Proof. exact (@lem1483519 (term50 y z) term46). Qed.
Lemma lem1570871 (x : nat) : (term195 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1570872 : term196 = term46.
Proof. exact (@lem1570871 term197). Qed.
Lemma lem1570873 (y : real) (z : real) : (term203 y z) = (term203 y z).
Proof. exact (eq_refl (term203 y z)). Qed.
Lemma lem1570874 (y : real) (z : real) : (term202 y z) = (term204 y z).
Proof. exact (MK_COMB (@lem1570873 y z) (@lem1570872)). Qed.
Lemma lem1570875 (y : real) (z : real) : (term204 y z) = (term50 y z).
Proof. exact (@lem1483450 (term50 y z)). Qed.
Lemma lem1570876 (y : real) (z : real) : (term202 y z) = (term50 y z).
Proof. exact (TRANS (@lem1570874 y z) (@lem1570875 y z)). Qed.
Lemma lem1570878 (y : real) (z : real) : (term192 y z) = (term50 y z).
Proof. exact (TRANS (@lem1570869 y z) (@lem1570876 y z)). Qed.
Lemma lem1570879 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570880 (y : real) (z : real) : (term205 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1570879) (@lem1570878 y z)). Qed.
Lemma lem1570881 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570882 (y : real) (z : real) : (term201 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1570880 y z) (@lem1570881)). Qed.
Lemma lem1570883 (y : real) (z : real) : (term53 y z) = (term53 y z).
Proof. exact (TRANS (@lem1570851 y z) (@lem1570882 y z)). Qed.
Lemma lem1570884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570885 (x : real) (z : real) : (term55 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1570884) (@lem1570850 x z)). Qed.
Lemma lem1570886 (x : real) (y : real) (z : real) : (term56 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1570885 x z) (@lem1570883 y z)). Qed.
Lemma lem1570887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570888 (x : real) (z : real) : (term206 z x) = (term207 x z).
Proof. exact (MK_COMB (@lem1570887) (@lem1570817 x z)). Qed.
Lemma lem1570889 (x : real) (y : real) (z : real) : (term178 x y z) = (term208 x y z).
Proof. exact (MK_COMB (@lem1570888 x z) (@lem1570886 x y z)). Qed.
Lemma lem1570890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570891 (x : real) (y : real) : (term179 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem1570890) (@lem1570784 x y)). Qed.
Lemma lem1570892 (x : real) (y : real) (z : real) : (term181 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem1570891 x y) (@lem1570889 x y z)). Qed.
Lemma lem1570893 (x : real) (y : real) : (real_gt x y) = (term68 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1570906 (x : real) (y : real) : (real_sub x y) = (term50 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1570907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570908 (x : real) (y : real) : (term70 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1570907) (@lem1570906 x y)). Qed.
Lemma lem1570909 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570910 (x : real) (y : real) : (term68 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1570908 x y) (@lem1570909)). Qed.
Lemma lem1570911 (x : real) (y : real) : (real_gt x y) = (term188 x y).
Proof. exact (TRANS (@lem1570893 x y) (@lem1570910 x y)). Qed.
Lemma lem1570912 (z : real) (y : real) : (term188 z y) = (term189 z y).
Proof. exact (@lem1483525 (term50 z y) term46). Qed.
Lemma lem1570913 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570926 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1570927 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1570928 (y : real) (z : real) : (term190 z y) = (term191 y z).
Proof. exact (MK_COMB (@lem1570927) (@lem1570926 y z)). Qed.
Lemma lem1570929 (y : real) (z : real) : (term192 z y) = (term193 y z).
Proof. exact (MK_COMB (@lem1570928 y z) (@lem1570913)). Qed.
Lemma lem1570930 (y : real) (z : real) : (term193 y z) = (term194 y z).
Proof. exact (@lem1483519 (term69 y z) term46). Qed.
Lemma lem1570932 (x : nat) : (term195 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1570933 : term196 = term46.
Proof. exact (@lem1570932 term197). Qed.
Lemma lem1570934 (y : real) (z : real) : (term198 y z) = (term198 y z).
Proof. exact (eq_refl (term198 y z)). Qed.
Lemma lem1570935 (y : real) (z : real) : (term194 y z) = (term199 y z).
Proof. exact (MK_COMB (@lem1570934 y z) (@lem1570933)). Qed.
Lemma lem1570936 (y : real) (z : real) : (term199 y z) = (term69 y z).
Proof. exact (@lem1483450 (term69 y z)). Qed.
Lemma lem1570937 (y : real) (z : real) : (term194 y z) = (term69 y z).
Proof. exact (TRANS (@lem1570935 y z) (@lem1570936 y z)). Qed.
Lemma lem1570938 (y : real) (z : real) : (term193 y z) = (term69 y z).
Proof. exact (TRANS (@lem1570930 y z) (@lem1570937 y z)). Qed.
Lemma lem1570939 (y : real) (z : real) : (term192 z y) = (term69 y z).
Proof. exact (TRANS (@lem1570929 y z) (@lem1570938 y z)). Qed.
Lemma lem1570940 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1570941 (y : real) (z : real) : (term200 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1570940) (@lem1570939 y z)). Qed.
Lemma lem1570942 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570943 (y : real) (z : real) : (term189 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1570941 y z) (@lem1570942)). Qed.
Lemma lem1570944 (y : real) (z : real) : (term188 z y) = (term72 y z).
Proof. exact (TRANS (@lem1570912 z y) (@lem1570943 y z)). Qed.
Lemma lem1570945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570946 (x : real) (z : real) : (term55 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1570945) (@lem1570850 x z)). Qed.
Lemma lem1570947 (x : real) (y : real) (z : real) : (term56 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1570946 x z) (@lem1570883 y z)). Qed.
Lemma lem1570948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570949 (y : real) (z : real) : (term206 z y) = (term207 y z).
Proof. exact (MK_COMB (@lem1570948) (@lem1570944 y z)). Qed.
Lemma lem1570950 (x : real) (y : real) (z : real) : (term173 x y z) = (term212 x y z).
Proof. exact (MK_COMB (@lem1570949 y z) (@lem1570947 x y z)). Qed.
Lemma lem1570951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1570952 (x : real) (y : real) : (term174 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1570951) (@lem1570911 x y)). Qed.
Lemma lem1570953 (x : real) (y : real) (z : real) : (term176 x y z) = (term213 x y z).
Proof. exact (MK_COMB (@lem1570952 x y) (@lem1570950 x y z)). Qed.
Lemma lem1570954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1570955 (x : real) (y : real) (z : real) : (term183 x y z) = (term214 x y z).
Proof. exact (MK_COMB (@lem1570954) (@lem1570892 x y z)). Qed.
Lemma lem1570956 (x : real) (y : real) (z : real) : (term184 x y z) = (term215 x y z).
Proof. exact (MK_COMB (@lem1570955 x y z) (@lem1570953 x y z)). Qed.
Lemma lem1570968 (x : real) (y : real) (z : real) : (term58 x y z) = (term215 x y z).
Proof. exact (TRANS (@lem1570765 x y z) (@lem1570956 x y z)). Qed.
Lemma lem1570970 (x : real) (a : real) (y : real) (r : real) : (term216 a x y r) = (term217 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1570971 (x : real) (z : real) (y : real) : (term67 z x y) = (term218 x z y).
Proof. exact (@lem1570970 x (term64 z) y term46). Qed.
Lemma lem1570984 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1570985 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1570986 (y : real) (z : real) : (term186 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1570985) (@lem1570984 y z)). Qed.
Lemma lem1570987 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1570988 (y : real) (z : real) : (term187 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1570986 y z) (@lem1570987)). Qed.
Lemma lem1571001 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1571002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571003 (x : real) (z : real) : (term186 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1571002) (@lem1571001 x z)). Qed.
Lemma lem1571004 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571005 (x : real) (z : real) : (term187 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1571003 x z) (@lem1571004)). Qed.
Lemma lem1571006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571007 (x : real) (z : real) : (term209 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1571006) (@lem1571005 x z)). Qed.
Lemma lem1571008 (x : real) (y : real) (z : real) : (term218 x z y) = (term56 x y z).
Proof. exact (MK_COMB (@lem1571007 x z) (@lem1570988 y z)). Qed.
Lemma lem1571009 (x : real) (y : real) (z : real) : (term67 z x y) = (term56 x y z).
Proof. exact (TRANS (@lem1570971 x z y) (@lem1571008 x y z)). Qed.
Lemma lem1571010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571011 (x : real) (y : real) (z : real) : (term77 z x y) = (term219 x y z).
Proof. exact (MK_COMB (@lem1571010) (@lem1571009 x y z)). Qed.
Lemma lem1571012 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (eq_refl (term72 x z)). Qed.
Lemma lem1571015 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem1571011 x y z) (@lem1571012 x z)). Qed.
Lemma lem1571017 (x : real) (a : real) (y : real) (r : real) : (term216 a x y r) = (term217 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem1571018 (x : real) (z : real) (y : real) : (term67 z x y) = (term218 x z y).
Proof. exact (@lem1571017 x (term64 z) y term46). Qed.
Lemma lem1571031 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1571032 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571033 (y : real) (z : real) : (term186 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1571032) (@lem1571031 y z)). Qed.
Lemma lem1571034 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571035 (y : real) (z : real) : (term187 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1571033 y z) (@lem1571034)). Qed.
Lemma lem1571048 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1571049 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571050 (x : real) (z : real) : (term186 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1571049) (@lem1571048 x z)). Qed.
Lemma lem1571051 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571052 (x : real) (z : real) : (term187 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1571050 x z) (@lem1571051)). Qed.
Lemma lem1571053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571054 (x : real) (z : real) : (term209 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1571053) (@lem1571052 x z)). Qed.
Lemma lem1571055 (x : real) (y : real) (z : real) : (term218 x z y) = (term56 x y z).
Proof. exact (MK_COMB (@lem1571054 x z) (@lem1571035 y z)). Qed.
Lemma lem1571056 (x : real) (y : real) (z : real) : (term67 z x y) = (term56 x y z).
Proof. exact (TRANS (@lem1571018 x z y) (@lem1571055 x y z)). Qed.
Lemma lem1571057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571058 (x : real) (y : real) (z : real) : (term77 z x y) = (term219 x y z).
Proof. exact (MK_COMB (@lem1571057) (@lem1571056 x y z)). Qed.
Lemma lem1571059 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (eq_refl (term72 y z)). Qed.
Lemma lem1571062 (x : real) (y : real) (z : real) : (term222 x y z) = (term223 x y z).
Proof. exact (MK_COMB (@lem1571058 x y z) (@lem1571059 y z)). Qed.
Lemma lem1571063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571064 (y : real) (x : real) (z : real) : (term224 y x z) = (term225 y x z).
Proof. exact (MK_COMB (@lem1571063) (@lem1571015 y x z)). Qed.
Lemma lem1571065 (x : real) (y : real) (z : real) : (term161 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1571064 y x z) (@lem1571062 x y z)). Qed.
Lemma lem1571066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571067 (x : real) (y : real) (z : real) : (term79 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1571066) (@lem1570968 x y z)). Qed.
Lemma lem1571068 (x : real) (y : real) (z : real) : (term162 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1571067 x y z) (@lem1571065 x y z)). Qed.
Lemma lem1571069 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term228 x y z.
Proof. exact (h1). Qed.
Lemma lem1571070 (x : real) (y : real) (z : real) (h1 : term215 x y z) : term215 x y z.
Proof. exact (h1). Qed.
Lemma lem1571071 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term210 x y z.
Proof. exact (h1). Qed.
Lemma lem1571072 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term208 x y z.
Proof. exact (proj2 (@lem1571071 x y z h1)). Qed.
Lemma lem1571074 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term56 x y z.
Proof. exact (proj2 (@lem1571072 x y z h1)). Qed.
Lemma lem1571075 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term72 x z.
Proof. exact (proj1 (@lem1571072 x y z h1)). Qed.
Lemma lem1571077 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term53 x z.
Proof. exact (proj1 (@lem1571074 x y z h1)). Qed.
Lemma lem1571079 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571080 : term230 = term231.
Proof. exact (@lem1571079 (NUMERAL 0) term197). Qed.
Lemma lem1571081 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571082 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571083 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571082 h1) (fun h1 : term231 = True => @lem1571081)). Qed.
Lemma lem1571084 : term231 = True.
Proof. exact (EQ_MP (@lem1571083) (@lem1571081)). Qed.
Lemma lem1571085 : term230 = True.
Proof. exact (TRANS (@lem1571080) (@lem1571084)). Qed.
Lemma lem1571086 : True = term230.
Proof. exact (SYM (@lem1571085)). Qed.
Lemma lem1571087 : term230.
Proof. exact (EQ_MP (@lem1571086) (@lem0)). Qed.
Lemma lem1571088 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term233 x z.
Proof. exact (conj (@lem1571087) (@lem1571077 x y z h1)). Qed.
Lemma lem1571090 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1571091 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1571090 term236 (term50 x z)). Qed.
Lemma lem1571092 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term237 x z.
Proof. exact (@lem1571091 x z (@lem1571088 x y z h1)). Qed.
Lemma lem1571093 (x : real) (z : real) : (term238 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1571094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571095 (x : real) (z : real) : (term239 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1571094) (@lem1571093 x z)). Qed.
Lemma lem1571096 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571097 (x : real) (z : real) : (term237 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1571095 x z) (@lem1571096)). Qed.
Lemma lem1571098 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term53 x z.
Proof. exact (EQ_MP (@lem1571097 x z) (@lem1571092 x y z h1)). Qed.
Lemma lem1571100 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571101 : term230 = term231.
Proof. exact (@lem1571100 (NUMERAL 0) term197). Qed.
Lemma lem1571102 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571103 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571104 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571103 h1) (fun h1 : term231 = True => @lem1571102)). Qed.
Lemma lem1571105 : term231 = True.
Proof. exact (EQ_MP (@lem1571104) (@lem1571102)). Qed.
Lemma lem1571106 : term230 = True.
Proof. exact (TRANS (@lem1571101) (@lem1571105)). Qed.
Lemma lem1571107 : True = term230.
Proof. exact (SYM (@lem1571106)). Qed.
Lemma lem1571108 : term230.
Proof. exact (EQ_MP (@lem1571107) (@lem0)). Qed.
Lemma lem1571109 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term240 x z.
Proof. exact (conj (@lem1571108) (@lem1571075 x y z h1)). Qed.
Lemma lem1571111 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1571112 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1571111 term236 (term69 x z)). Qed.
Lemma lem1571113 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term243 x z.
Proof. exact (@lem1571112 x z (@lem1571109 x y z h1)). Qed.
Lemma lem1571114 (x : real) (z : real) : (term244 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1571115 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571116 (x : real) (z : real) : (term245 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1571115) (@lem1571114 x z)). Qed.
Lemma lem1571117 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571118 (x : real) (z : real) : (term243 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1571116 x z) (@lem1571117)). Qed.
Lemma lem1571119 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1571118 x z) (@lem1571113 x y z h1)). Qed.
Lemma lem1571120 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term246 x z.
Proof. exact (conj (@lem1571119 x y z h1) (@lem1571098 x y z h1)). Qed.
Lemma lem1571122 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1571123 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1571122 (term69 x z) (term50 x z)). Qed.
Lemma lem1571124 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term249 x z.
Proof. exact (@lem1571123 x z (@lem1571120 x y z h1)). Qed.
Lemma lem1571125 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 (term64 x) x z (term64 z)). Qed.
Lemma lem1571126 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483440 term254 x). Qed.
Lemma lem1571128 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571129 : term256 = term46.
Proof. exact (@lem1571128 term197). Qed.
Lemma lem1571130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571131 : term257 = term258.
Proof. exact (MK_COMB (@lem1571130) (@lem1571129)). Qed.
Lemma lem1571132 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1571133 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1571131) (@lem1571132 x)). Qed.
Lemma lem1571134 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1571126 x) (@lem1571133 x)). Qed.
Lemma lem1571135 (x : real) : (term259 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1571136 (x : real) : (term252 x) = term46.
Proof. exact (TRANS (@lem1571134 x) (@lem1571135 x)). Qed.
Lemma lem1571137 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1571138 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1571137) (@lem1571136 x)). Qed.
Lemma lem1571139 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1571141 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571142 : term256 = term46.
Proof. exact (@lem1571141 term197). Qed.
Lemma lem1571143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571144 : term257 = term258.
Proof. exact (MK_COMB (@lem1571143) (@lem1571142)). Qed.
Lemma lem1571145 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1571146 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1571144) (@lem1571145 z)). Qed.
Lemma lem1571147 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1571139 z) (@lem1571146 z)). Qed.
Lemma lem1571148 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1571149 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1571147 z) (@lem1571148 z)). Qed.
Lemma lem1571150 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1571138 x) (@lem1571149 z)). Qed.
Lemma lem1571151 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1571125 x z) (@lem1571150 x z)). Qed.
Lemma lem1571152 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1571153 (x : real) (z : real) : (term250 x z) = term46.
Proof. exact (TRANS (@lem1571151 x z) (@lem1571152)). Qed.
Lemma lem1571154 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571155 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1571154) (@lem1571153 x z)). Qed.
Lemma lem1571156 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571157 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1571155 x z) (@lem1571156)). Qed.
Lemma lem1571158 (x : real) (y : real) (z : real) (h1 : term210 x y z) : term266.
Proof. exact (EQ_MP (@lem1571157 x z) (@lem1571124 x y z h1)). Qed.
Lemma lem1571160 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571161 : term266 = term267.
Proof. exact (@lem1571160 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1571162 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1571163 : term266 = False.
Proof. exact (TRANS (@lem1571161) (@lem1571162)). Qed.
Lemma lem1571164 (x : real) (y : real) (z : real) (h1 : term210 x y z) : False.
Proof. exact (EQ_MP (@lem1571163) (@lem1571158 x y z h1)). Qed.
Lemma lem1571165 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term213 x y z.
Proof. exact (h1). Qed.
Lemma lem1571166 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term212 x y z.
Proof. exact (proj2 (@lem1571165 x y z h1)). Qed.
Lemma lem1571168 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term56 x y z.
Proof. exact (proj2 (@lem1571166 x y z h1)). Qed.
Lemma lem1571169 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term72 y z.
Proof. exact (proj1 (@lem1571166 x y z h1)). Qed.
Lemma lem1571170 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term53 y z.
Proof. exact (proj2 (@lem1571168 x y z h1)). Qed.
Lemma lem1571173 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571174 : term230 = term231.
Proof. exact (@lem1571173 (NUMERAL 0) term197). Qed.
Lemma lem1571175 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571176 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571177 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571176 h1) (fun h1 : term231 = True => @lem1571175)). Qed.
Lemma lem1571178 : term231 = True.
Proof. exact (EQ_MP (@lem1571177) (@lem1571175)). Qed.
Lemma lem1571179 : term230 = True.
Proof. exact (TRANS (@lem1571174) (@lem1571178)). Qed.
Lemma lem1571180 : True = term230.
Proof. exact (SYM (@lem1571179)). Qed.
Lemma lem1571181 : term230.
Proof. exact (EQ_MP (@lem1571180) (@lem0)). Qed.
Lemma lem1571182 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term233 y z.
Proof. exact (conj (@lem1571181) (@lem1571170 x y z h1)). Qed.
Lemma lem1571184 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1571185 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1571184 term236 (term50 y z)). Qed.
Lemma lem1571186 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term237 y z.
Proof. exact (@lem1571185 y z (@lem1571182 x y z h1)). Qed.
Lemma lem1571187 (y : real) (z : real) : (term238 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1571188 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571189 (y : real) (z : real) : (term239 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1571188) (@lem1571187 y z)). Qed.
Lemma lem1571190 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571191 (y : real) (z : real) : (term237 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1571189 y z) (@lem1571190)). Qed.
Lemma lem1571192 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1571191 y z) (@lem1571186 x y z h1)). Qed.
Lemma lem1571194 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571195 : term230 = term231.
Proof. exact (@lem1571194 (NUMERAL 0) term197). Qed.
Lemma lem1571196 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571197 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571198 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571197 h1) (fun h1 : term231 = True => @lem1571196)). Qed.
Lemma lem1571199 : term231 = True.
Proof. exact (EQ_MP (@lem1571198) (@lem1571196)). Qed.
Lemma lem1571200 : term230 = True.
Proof. exact (TRANS (@lem1571195) (@lem1571199)). Qed.
Lemma lem1571201 : True = term230.
Proof. exact (SYM (@lem1571200)). Qed.
Lemma lem1571202 : term230.
Proof. exact (EQ_MP (@lem1571201) (@lem0)). Qed.
Lemma lem1571203 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term240 y z.
Proof. exact (conj (@lem1571202) (@lem1571169 x y z h1)). Qed.
Lemma lem1571205 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1571206 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1571205 term236 (term69 y z)). Qed.
Lemma lem1571207 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term243 y z.
Proof. exact (@lem1571206 y z (@lem1571203 x y z h1)). Qed.
Lemma lem1571208 (y : real) (z : real) : (term244 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1571209 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571210 (y : real) (z : real) : (term245 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1571209) (@lem1571208 y z)). Qed.
Lemma lem1571211 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571212 (y : real) (z : real) : (term243 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1571210 y z) (@lem1571211)). Qed.
Lemma lem1571213 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1571212 y z) (@lem1571207 x y z h1)). Qed.
Lemma lem1571214 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term246 y z.
Proof. exact (conj (@lem1571213 x y z h1) (@lem1571192 x y z h1)). Qed.
Lemma lem1571216 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1571217 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1571216 (term69 y z) (term50 y z)). Qed.
Lemma lem1571218 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term249 y z.
Proof. exact (@lem1571217 y z (@lem1571214 x y z h1)). Qed.
Lemma lem1571219 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 (term64 y) y z (term64 z)). Qed.
Lemma lem1571220 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483440 term254 y). Qed.
Lemma lem1571222 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571223 : term256 = term46.
Proof. exact (@lem1571222 term197). Qed.
Lemma lem1571224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571225 : term257 = term258.
Proof. exact (MK_COMB (@lem1571224) (@lem1571223)). Qed.
Lemma lem1571226 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1571227 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1571225) (@lem1571226 y)). Qed.
Lemma lem1571228 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1571220 y) (@lem1571227 y)). Qed.
Lemma lem1571229 (y : real) : (term259 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1571230 (y : real) : (term252 y) = term46.
Proof. exact (TRANS (@lem1571228 y) (@lem1571229 y)). Qed.
Lemma lem1571231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1571232 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1571231) (@lem1571230 y)). Qed.
Lemma lem1571233 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1571235 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571236 : term256 = term46.
Proof. exact (@lem1571235 term197). Qed.
Lemma lem1571237 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571238 : term257 = term258.
Proof. exact (MK_COMB (@lem1571237) (@lem1571236)). Qed.
Lemma lem1571239 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1571240 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1571238) (@lem1571239 z)). Qed.
Lemma lem1571241 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1571233 z) (@lem1571240 z)). Qed.
Lemma lem1571242 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1571243 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1571241 z) (@lem1571242 z)). Qed.
Lemma lem1571244 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1571232 y) (@lem1571243 z)). Qed.
Lemma lem1571245 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1571219 y z) (@lem1571244 y z)). Qed.
Lemma lem1571246 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1571247 (y : real) (z : real) : (term250 y z) = term46.
Proof. exact (TRANS (@lem1571245 y z) (@lem1571246)). Qed.
Lemma lem1571248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571249 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1571248) (@lem1571247 y z)). Qed.
Lemma lem1571250 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571251 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1571249 y z) (@lem1571250)). Qed.
Lemma lem1571252 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term266.
Proof. exact (EQ_MP (@lem1571251 y z) (@lem1571218 x y z h1)). Qed.
Lemma lem1571254 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571255 : term266 = term267.
Proof. exact (@lem1571254 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1571256 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1571257 : term266 = False.
Proof. exact (TRANS (@lem1571255) (@lem1571256)). Qed.
Lemma lem1571258 (x : real) (y : real) (z : real) (h1 : term213 x y z) : False.
Proof. exact (EQ_MP (@lem1571257) (@lem1571252 x y z h1)). Qed.
Lemma lem1571259 (x : real) (y : real) (z : real) (h1 : term215 x y z) : False.
Proof. exact (or_elim (@lem1571070 x y z h1) (fun h0 : term210 x y z => @lem1571164 x y z h0) (fun h0 : term213 x y z => @lem1571258 x y z h0)). Qed.
Lemma lem1571260 (x : real) (y : real) (z : real) (h1 : term226 x y z) : term226 x y z.
Proof. exact (h1). Qed.
Lemma lem1571261 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term221 y x z.
Proof. exact (h1). Qed.
Lemma lem1571262 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term72 x z.
Proof. exact (proj2 (@lem1571261 y x z h1)). Qed.
Lemma lem1571263 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term56 x y z.
Proof. exact (proj1 (@lem1571261 y x z h1)). Qed.
Lemma lem1571265 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term53 x z.
Proof. exact (proj1 (@lem1571263 y x z h1)). Qed.
Lemma lem1571267 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571268 : term230 = term231.
Proof. exact (@lem1571267 (NUMERAL 0) term197). Qed.
Lemma lem1571269 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571270 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571271 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571270 h1) (fun h1 : term231 = True => @lem1571269)). Qed.
Lemma lem1571272 : term231 = True.
Proof. exact (EQ_MP (@lem1571271) (@lem1571269)). Qed.
Lemma lem1571273 : term230 = True.
Proof. exact (TRANS (@lem1571268) (@lem1571272)). Qed.
Lemma lem1571274 : True = term230.
Proof. exact (SYM (@lem1571273)). Qed.
Lemma lem1571275 : term230.
Proof. exact (EQ_MP (@lem1571274) (@lem0)). Qed.
Lemma lem1571276 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term233 x z.
Proof. exact (conj (@lem1571275) (@lem1571265 y x z h1)). Qed.
Lemma lem1571278 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1571279 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1571278 term236 (term50 x z)). Qed.
Lemma lem1571280 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term237 x z.
Proof. exact (@lem1571279 x z (@lem1571276 y x z h1)). Qed.
Lemma lem1571281 (x : real) (z : real) : (term238 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1571282 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571283 (x : real) (z : real) : (term239 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1571282) (@lem1571281 x z)). Qed.
Lemma lem1571284 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571285 (x : real) (z : real) : (term237 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1571283 x z) (@lem1571284)). Qed.
Lemma lem1571286 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term53 x z.
Proof. exact (EQ_MP (@lem1571285 x z) (@lem1571280 y x z h1)). Qed.
Lemma lem1571288 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571289 : term230 = term231.
Proof. exact (@lem1571288 (NUMERAL 0) term197). Qed.
Lemma lem1571290 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571291 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571292 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571291 h1) (fun h1 : term231 = True => @lem1571290)). Qed.
Lemma lem1571293 : term231 = True.
Proof. exact (EQ_MP (@lem1571292) (@lem1571290)). Qed.
Lemma lem1571294 : term230 = True.
Proof. exact (TRANS (@lem1571289) (@lem1571293)). Qed.
Lemma lem1571295 : True = term230.
Proof. exact (SYM (@lem1571294)). Qed.
Lemma lem1571296 : term230.
Proof. exact (EQ_MP (@lem1571295) (@lem0)). Qed.
Lemma lem1571297 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term240 x z.
Proof. exact (conj (@lem1571296) (@lem1571262 y x z h1)). Qed.
Lemma lem1571299 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1571300 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1571299 term236 (term69 x z)). Qed.
Lemma lem1571301 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term243 x z.
Proof. exact (@lem1571300 x z (@lem1571297 y x z h1)). Qed.
Lemma lem1571302 (x : real) (z : real) : (term244 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1571303 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571304 (x : real) (z : real) : (term245 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1571303) (@lem1571302 x z)). Qed.
Lemma lem1571305 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571306 (x : real) (z : real) : (term243 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1571304 x z) (@lem1571305)). Qed.
Lemma lem1571307 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1571306 x z) (@lem1571301 y x z h1)). Qed.
Lemma lem1571308 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term246 x z.
Proof. exact (conj (@lem1571307 y x z h1) (@lem1571286 y x z h1)). Qed.
Lemma lem1571310 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1571311 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1571310 (term69 x z) (term50 x z)). Qed.
Lemma lem1571312 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term249 x z.
Proof. exact (@lem1571311 x z (@lem1571308 y x z h1)). Qed.
Lemma lem1571313 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 (term64 x) x z (term64 z)). Qed.
Lemma lem1571314 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483440 term254 x). Qed.
Lemma lem1571316 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571317 : term256 = term46.
Proof. exact (@lem1571316 term197). Qed.
Lemma lem1571318 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571319 : term257 = term258.
Proof. exact (MK_COMB (@lem1571318) (@lem1571317)). Qed.
Lemma lem1571320 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1571321 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1571319) (@lem1571320 x)). Qed.
Lemma lem1571322 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1571314 x) (@lem1571321 x)). Qed.
Lemma lem1571323 (x : real) : (term259 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1571324 (x : real) : (term252 x) = term46.
Proof. exact (TRANS (@lem1571322 x) (@lem1571323 x)). Qed.
Lemma lem1571325 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1571326 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1571325) (@lem1571324 x)). Qed.
Lemma lem1571327 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1571329 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571330 : term256 = term46.
Proof. exact (@lem1571329 term197). Qed.
Lemma lem1571331 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571332 : term257 = term258.
Proof. exact (MK_COMB (@lem1571331) (@lem1571330)). Qed.
Lemma lem1571333 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1571334 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1571332) (@lem1571333 z)). Qed.
Lemma lem1571335 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1571327 z) (@lem1571334 z)). Qed.
Lemma lem1571336 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1571337 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1571335 z) (@lem1571336 z)). Qed.
Lemma lem1571338 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1571326 x) (@lem1571337 z)). Qed.
Lemma lem1571339 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1571313 x z) (@lem1571338 x z)). Qed.
Lemma lem1571340 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1571341 (x : real) (z : real) : (term250 x z) = term46.
Proof. exact (TRANS (@lem1571339 x z) (@lem1571340)). Qed.
Lemma lem1571342 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571343 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1571342) (@lem1571341 x z)). Qed.
Lemma lem1571344 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571345 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1571343 x z) (@lem1571344)). Qed.
Lemma lem1571346 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term266.
Proof. exact (EQ_MP (@lem1571345 x z) (@lem1571312 y x z h1)). Qed.
Lemma lem1571348 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571349 : term266 = term267.
Proof. exact (@lem1571348 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1571350 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1571351 : term266 = False.
Proof. exact (TRANS (@lem1571349) (@lem1571350)). Qed.
Lemma lem1571352 (y : real) (x : real) (z : real) (h1 : term221 y x z) : False.
Proof. exact (EQ_MP (@lem1571351) (@lem1571346 y x z h1)). Qed.
Lemma lem1571353 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term223 x y z.
Proof. exact (h1). Qed.
Lemma lem1571354 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (proj2 (@lem1571353 x y z h1)). Qed.
Lemma lem1571355 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term56 x y z.
Proof. exact (proj1 (@lem1571353 x y z h1)). Qed.
Lemma lem1571356 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term53 y z.
Proof. exact (proj2 (@lem1571355 x y z h1)). Qed.
Lemma lem1571359 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571360 : term230 = term231.
Proof. exact (@lem1571359 (NUMERAL 0) term197). Qed.
Lemma lem1571361 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571362 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571363 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571362 h1) (fun h1 : term231 = True => @lem1571361)). Qed.
Lemma lem1571364 : term231 = True.
Proof. exact (EQ_MP (@lem1571363) (@lem1571361)). Qed.
Lemma lem1571365 : term230 = True.
Proof. exact (TRANS (@lem1571360) (@lem1571364)). Qed.
Lemma lem1571366 : True = term230.
Proof. exact (SYM (@lem1571365)). Qed.
Lemma lem1571367 : term230.
Proof. exact (EQ_MP (@lem1571366) (@lem0)). Qed.
Lemma lem1571368 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term233 y z.
Proof. exact (conj (@lem1571367) (@lem1571356 x y z h1)). Qed.
Lemma lem1571370 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1571371 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1571370 term236 (term50 y z)). Qed.
Lemma lem1571372 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term237 y z.
Proof. exact (@lem1571371 y z (@lem1571368 x y z h1)). Qed.
Lemma lem1571373 (y : real) (z : real) : (term238 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1571374 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571375 (y : real) (z : real) : (term239 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1571374) (@lem1571373 y z)). Qed.
Lemma lem1571376 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571377 (y : real) (z : real) : (term237 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1571375 y z) (@lem1571376)). Qed.
Lemma lem1571378 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1571377 y z) (@lem1571372 x y z h1)). Qed.
Lemma lem1571380 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571381 : term230 = term231.
Proof. exact (@lem1571380 (NUMERAL 0) term197). Qed.
Lemma lem1571382 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1571383 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1571384 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1571383 h1) (fun h1 : term231 = True => @lem1571382)). Qed.
Lemma lem1571385 : term231 = True.
Proof. exact (EQ_MP (@lem1571384) (@lem1571382)). Qed.
Lemma lem1571386 : term230 = True.
Proof. exact (TRANS (@lem1571381) (@lem1571385)). Qed.
Lemma lem1571387 : True = term230.
Proof. exact (SYM (@lem1571386)). Qed.
Lemma lem1571388 : term230.
Proof. exact (EQ_MP (@lem1571387) (@lem0)). Qed.
Lemma lem1571389 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term240 y z.
Proof. exact (conj (@lem1571388) (@lem1571354 x y z h1)). Qed.
Lemma lem1571391 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1571392 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1571391 term236 (term69 y z)). Qed.
Lemma lem1571393 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term243 y z.
Proof. exact (@lem1571392 y z (@lem1571389 x y z h1)). Qed.
Lemma lem1571394 (y : real) (z : real) : (term244 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1571395 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571396 (y : real) (z : real) : (term245 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1571395) (@lem1571394 y z)). Qed.
Lemma lem1571397 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571398 (y : real) (z : real) : (term243 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1571396 y z) (@lem1571397)). Qed.
Lemma lem1571399 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1571398 y z) (@lem1571393 x y z h1)). Qed.
Lemma lem1571400 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term246 y z.
Proof. exact (conj (@lem1571399 x y z h1) (@lem1571378 x y z h1)). Qed.
Lemma lem1571402 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1571403 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1571402 (term69 y z) (term50 y z)). Qed.
Lemma lem1571404 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term249 y z.
Proof. exact (@lem1571403 y z (@lem1571400 x y z h1)). Qed.
Lemma lem1571405 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 (term64 y) y z (term64 z)). Qed.
Lemma lem1571406 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483440 term254 y). Qed.
Lemma lem1571408 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571409 : term256 = term46.
Proof. exact (@lem1571408 term197). Qed.
Lemma lem1571410 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571411 : term257 = term258.
Proof. exact (MK_COMB (@lem1571410) (@lem1571409)). Qed.
Lemma lem1571412 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1571413 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1571411) (@lem1571412 y)). Qed.
Lemma lem1571414 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1571406 y) (@lem1571413 y)). Qed.
Lemma lem1571415 (y : real) : (term259 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1571416 (y : real) : (term252 y) = term46.
Proof. exact (TRANS (@lem1571414 y) (@lem1571415 y)). Qed.
Lemma lem1571417 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1571418 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1571417) (@lem1571416 y)). Qed.
Lemma lem1571419 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1571421 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1571422 : term256 = term46.
Proof. exact (@lem1571421 term197). Qed.
Lemma lem1571423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571424 : term257 = term258.
Proof. exact (MK_COMB (@lem1571423) (@lem1571422)). Qed.
Lemma lem1571425 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1571426 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1571424) (@lem1571425 z)). Qed.
Lemma lem1571427 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1571419 z) (@lem1571426 z)). Qed.
Lemma lem1571428 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1571429 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1571427 z) (@lem1571428 z)). Qed.
Lemma lem1571430 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1571418 y) (@lem1571429 z)). Qed.
Lemma lem1571431 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1571405 y z) (@lem1571430 y z)). Qed.
Lemma lem1571432 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1571433 (y : real) (z : real) : (term250 y z) = term46.
Proof. exact (TRANS (@lem1571431 y z) (@lem1571432)). Qed.
Lemma lem1571434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571435 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1571434) (@lem1571433 y z)). Qed.
Lemma lem1571436 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1571437 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1571435 y z) (@lem1571436)). Qed.
Lemma lem1571438 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term266.
Proof. exact (EQ_MP (@lem1571437 y z) (@lem1571404 x y z h1)). Qed.
Lemma lem1571440 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1571441 : term266 = term267.
Proof. exact (@lem1571440 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1571442 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1571443 : term266 = False.
Proof. exact (TRANS (@lem1571441) (@lem1571442)). Qed.
Lemma lem1571444 (x : real) (y : real) (z : real) (h1 : term223 x y z) : False.
Proof. exact (EQ_MP (@lem1571443) (@lem1571438 x y z h1)). Qed.
Lemma lem1571445 (x : real) (y : real) (z : real) (h1 : term226 x y z) : False.
Proof. exact (or_elim (@lem1571260 x y z h1) (fun h0 : term221 y x z => @lem1571352 y x z h0) (fun h0 : term223 x y z => @lem1571444 x y z h0)). Qed.
Lemma lem1571446 (x : real) (y : real) (z : real) (h1 : term228 x y z) : False.
Proof. exact (or_elim (@lem1571069 x y z h1) (fun h0 : term215 x y z => @lem1571259 x y z h0) (fun h0 : term226 x y z => @lem1571445 x y z h0)). Qed.
Lemma lem1571447 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term162 x y z.
Proof. exact (h1). Qed.
Lemma lem1571448 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term228 x y z.
Proof. exact (EQ_MP (@lem1571068 x y z) (@lem1571447 x y z h1)). Qed.
Lemma lem1571449 (x : real) (y : real) (z : real) (h1 : term162 x y z) : (term228 x y z) = False.
Proof. exact (prop_ext (fun h2 : term228 x y z => @lem1571446 x y z h2) (fun h2 : False => @lem1571448 x y z h1)). Qed.
Lemma lem1571450 (x : real) (y : real) (z : real) (h1 : term162 x y z) : False.
Proof. exact (EQ_MP (@lem1571449 x y z h1) (@lem1571448 x y z h1)). Qed.
Lemma lem1571451 (x : real) (y : real) (h1 : term164 x y) : term164 x y.
Proof. exact (h1). Qed.
Lemma lem1571452 (x : real) (y : real) (h1 : term164 x y) : False.
Proof. exact (ex_elim (@lem1571451 x y h1) (fun z : real => fun h0 : term163 x y z => @lem1571450 x y z h0)). Qed.
Lemma lem1571453 (x : real) (h1 : term166 x) : term166 x.
Proof. exact (h1). Qed.
Lemma lem1571454 (x : real) (h1 : term166 x) : False.
Proof. exact (ex_elim (@lem1571453 x h1) (fun y : real => fun h0 : term165 x y => @lem1571452 x y h0)). Qed.
Lemma lem1571455 (h1 : term168) : term168.
Proof. exact (h1). Qed.
Lemma lem1571456 (h1 : term168) : False.
Proof. exact (ex_elim (@lem1571455 h1) (fun x : real => fun h0 : term167 x => @lem1571454 x h0)). Qed.
Lemma lem1571457 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1571458 (h1 : term32) : term168.
Proof. exact (EQ_MP (@lem1570748) (@lem1571457 h1)). Qed.
Lemma lem1571459 (h1 : term32) : term168 = False.
Proof. exact (prop_ext (fun h2 : term168 => @lem1571456 h2) (fun h2 : False => @lem1571458 h1)). Qed.
Lemma lem1571460 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1571459 h1) (@lem1571458 h1)). Qed.
Lemma lem1571461 : term268.
Proof. exact (fun h0 : term32 => @lem1571460 h0). Qed.
Lemma lem1571462 : term269.
Proof. exact (@lem1386578 term270). Qed.
Lemma lem1571463 : term270.
Proof. exact (@lem1571462 (@lem1571461)). Qed.

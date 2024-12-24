Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADD_SUB_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1512119 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17646 (term2 x y z) (term3 x z y)). Qed.
Lemma lem1512120 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1512121 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1512120 (term8 x y)). Qed.
Lemma lem1512122 (x : real) (z : real) (y : real) : (term9 x y z) = ((term2 x y z) = (term3 x z y)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1512123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1512124 (x : real) (z : real) (y : real) : (term10 x y z) = (term0 x z y).
Proof. exact (MK_COMB (@lem1512123) (@lem1512122 x z y)). Qed.
Lemma lem1512125 (x : real) (z : real) (y : real) : (term10 x y z) = (term1 x z y).
Proof. exact (TRANS (@lem1512124 x z y) (@lem1512119 x z y)). Qed.
Lemma lem1512126 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1512125 x z y)). Qed.
Lemma lem1512127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512128 (x : real) (y : real) : (term7 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1512127) (@lem1512126 x y)). Qed.
Lemma lem1512129 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (TRANS (@lem1512121 x y) (@lem1512128 x y)). Qed.
Lemma lem1512130 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1512131 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1512130 (term16 x)). Qed.
Lemma lem1512132 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1512133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1512134 (x : real) (y : real) : (term19 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1512133) (@lem1512132 x y)). Qed.
Lemma lem1512135 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1512134 x y) (@lem1512129 x y)). Qed.
Lemma lem1512136 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1512135 x y)). Qed.
Lemma lem1512137 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512138 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1512137) (@lem1512136 x)). Qed.
Lemma lem1512139 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1512131 x) (@lem1512138 x)). Qed.
Lemma lem1512140 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1512141 : term23 = term24.
Proof. exact (@lem1512140 term25). Qed.
Lemma lem1512142 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1512143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1512144 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1512143) (@lem1512142 x)). Qed.
Lemma lem1512145 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1512144 x) (@lem1512139 x)). Qed.
Lemma lem1512146 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1512145 x)). Qed.
Lemma lem1512147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512148 : term24 = term31.
Proof. exact (MK_COMB (@lem1512147) (@lem1512146)). Qed.
Lemma lem1512150 : term23 = term31.
Proof. exact (TRANS (@lem1512141) (@lem1512148)). Qed.
Lemma lem1512167 (x : real) (z : real) (y : real) : (term1 x z y) = (term1 x z y).
Proof. exact (eq_refl (term1 x z y)). Qed.
Lemma lem1512168 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1512167 x z y)). Qed.
Lemma lem1512169 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512170 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1512169) (@lem1512168 x y)). Qed.
Lemma lem1512171 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1512170 x y)). Qed.
Lemma lem1512172 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512173 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1512172) (@lem1512171 x)). Qed.
Lemma lem1512174 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1512173 x)). Qed.
Lemma lem1512175 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512176 : term31 = term31.
Proof. exact (MK_COMB (@lem1512175) (@lem1512174)). Qed.
Lemma lem1512177 : term23 = term31.
Proof. exact (TRANS (@lem1512150) (@lem1512176)). Qed.
Lemma lem1512178 (z : real) (x : real) (y : real) : (term2 x y z) = (term32 z x y).
Proof. exact (@lem1483521 z (real_add x y)). Qed.
Lemma lem1512190 (z : real) (x : real) (y : real) : (term33 z x y) = (term34 z x y).
Proof. exact (@lem1483519 z (real_add x y)). Qed.
Lemma lem1512197 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483508 x term37 y). Qed.
Lemma lem1512198 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1512199 (z : real) (x : real) (y : real) : (term34 z x y) = (term38 z x y).
Proof. exact (MK_COMB (@lem1512198 z) (@lem1512197 x y)). Qed.
Lemma lem1512200 (x : real) (z : real) (y : real) : (term38 z x y) = (term39 x z y).
Proof. exact (@lem1483484 (term40 x) z (term40 y)). Qed.
Lemma lem1512201 (y : real) (z : real) : (term41 z y) = (term42 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1512202 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1512203 (x : real) (y : real) (z : real) : (term39 x z y) = (term44 x y z).
Proof. exact (MK_COMB (@lem1512202 x) (@lem1512201 y z)). Qed.
Lemma lem1512204 (x : real) (y : real) (z : real) : (term38 z x y) = (term44 x y z).
Proof. exact (TRANS (@lem1512200 x z y) (@lem1512203 x y z)). Qed.
Lemma lem1512205 (x : real) (y : real) (z : real) : (term34 z x y) = (term44 x y z).
Proof. exact (TRANS (@lem1512199 z x y) (@lem1512204 x y z)). Qed.
Lemma lem1512207 (x : real) (y : real) (z : real) : (term33 z x y) = (term44 x y z).
Proof. exact (TRANS (@lem1512190 z x y) (@lem1512205 x y z)). Qed.
Lemma lem1512208 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1512209 (x : real) (y : real) (z : real) : (term45 z x y) = (term46 x y z).
Proof. exact (MK_COMB (@lem1512208) (@lem1512207 x y z)). Qed.
Lemma lem1512210 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512211 (x : real) (y : real) (z : real) : (term32 z x y) = (term48 x y z).
Proof. exact (MK_COMB (@lem1512209 x y z) (@lem1512210)). Qed.
Lemma lem1512212 (x : real) (y : real) (z : real) : (term2 x y z) = (term48 x y z).
Proof. exact (TRANS (@lem1512178 z x y) (@lem1512211 x y z)). Qed.
Lemma lem1512213 (x : real) (z : real) (y : real) : (term49 x z y) = (term50 x z y).
Proof. exact (@lem1483531 x (real_sub z y)). Qed.
Lemma lem1512219 (z : real) (y : real) : (real_sub z y) = (term41 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1512224 (y : real) (z : real) : (term41 z y) = (term42 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1512226 (y : real) (z : real) : (real_sub z y) = (term42 y z).
Proof. exact (TRANS (@lem1512219 z y) (@lem1512224 y z)). Qed.
Lemma lem1512229 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1512230 (x : real) (y : real) (z : real) : (term51 x z y) = (term52 x y z).
Proof. exact (MK_COMB (@lem1512229 x) (@lem1512226 y z)). Qed.
Lemma lem1512231 (x : real) (y : real) (z : real) : (term52 x y z) = (term53 x y z).
Proof. exact (@lem1483519 x (term42 y z)). Qed.
Lemma lem1512232 (y : real) (z : real) : (term54 y z) = (term55 y z).
Proof. exact (@lem1483508 (term40 y) term37 z). Qed.
Lemma lem1512233 (z : real) : (term40 z) = (term40 z).
Proof. exact (eq_refl (term40 z)). Qed.
Lemma lem1512234 (y : real) : (term56 y) = (term57 y).
Proof. exact (@lem1483476 term37 term37 y). Qed.
Lemma lem1512236 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1512237 : term60 = term61.
Proof. exact (@lem1512236 term62 term62). Qed.
Lemma lem1512238 : (term63 = (BIT1 0)) = (term64 = term62).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1512239 : term64 = term62.
Proof. exact (EQ_MP (@lem1512238) (@lem940073)). Qed.
Lemma lem1512240 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1512241 : term61 = term65.
Proof. exact (MK_COMB (@lem1512240) (@lem1512239)). Qed.
Lemma lem1512242 : term60 = term65.
Proof. exact (TRANS (@lem1512237) (@lem1512241)). Qed.
Lemma lem1512243 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1512244 : term66 = term67.
Proof. exact (MK_COMB (@lem1512243) (@lem1512242)). Qed.
Lemma lem1512245 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1512246 (y : real) : (term57 y) = (term68 y).
Proof. exact (MK_COMB (@lem1512244) (@lem1512245 y)). Qed.
Lemma lem1512247 (y : real) : (term56 y) = (term68 y).
Proof. exact (TRANS (@lem1512234 y) (@lem1512246 y)). Qed.
Lemma lem1512248 (y : real) : (term68 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1512249 (y : real) : (term56 y) = y.
Proof. exact (TRANS (@lem1512247 y) (@lem1512248 y)). Qed.
Lemma lem1512250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1512251 (y : real) : (term69 y) = (real_add y).
Proof. exact (MK_COMB (@lem1512250) (@lem1512249 y)). Qed.
Lemma lem1512252 (y : real) (z : real) : (term55 y z) = (term41 y z).
Proof. exact (MK_COMB (@lem1512251 y) (@lem1512233 z)). Qed.
Lemma lem1512253 (y : real) (z : real) : (term54 y z) = (term41 y z).
Proof. exact (TRANS (@lem1512232 y z) (@lem1512252 y z)). Qed.
Lemma lem1512254 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1512257 (x : real) (y : real) (z : real) : (term53 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1512254 x) (@lem1512253 y z)). Qed.
Lemma lem1512258 (x : real) (y : real) (z : real) : (term52 x y z) = (term70 x y z).
Proof. exact (TRANS (@lem1512231 x y z) (@lem1512257 x y z)). Qed.
Lemma lem1512259 (x : real) (y : real) (z : real) : (term51 x z y) = (term70 x y z).
Proof. exact (TRANS (@lem1512230 x y z) (@lem1512258 x y z)). Qed.
Lemma lem1512260 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1512261 (x : real) (y : real) (z : real) : (term71 x z y) = (term72 x y z).
Proof. exact (MK_COMB (@lem1512260) (@lem1512259 x y z)). Qed.
Lemma lem1512262 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512263 (x : real) (y : real) (z : real) : (term50 x z y) = (term73 x y z).
Proof. exact (MK_COMB (@lem1512261 x y z) (@lem1512262)). Qed.
Lemma lem1512264 (x : real) (y : real) (z : real) : (term49 x z y) = (term73 x y z).
Proof. exact (TRANS (@lem1512213 x z y) (@lem1512263 x y z)). Qed.
Lemma lem1512265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1512266 (x : real) (y : real) (z : real) : (term74 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1512265) (@lem1512212 x y z)). Qed.
Lemma lem1512267 (x : real) (y : real) (z : real) : (term76 x z y) = (term77 x y z).
Proof. exact (MK_COMB (@lem1512266 x y z) (@lem1512264 x y z)). Qed.
Lemma lem1512268 (x : real) (y : real) (z : real) : (term78 x y z) = (term79 x y z).
Proof. exact (@lem1483531 (real_add x y) z). Qed.
Lemma lem1512280 (x : real) (y : real) (z : real) : (term80 x y z) = (term81 x y z).
Proof. exact (@lem1483519 (real_add x y) z). Qed.
Lemma lem1512289 (x : real) (y : real) (z : real) : (term81 x y z) = (term70 x y z).
Proof. exact (@lem1483482 x y (term40 z)). Qed.
Lemma lem1512291 (x : real) (y : real) (z : real) : (term80 x y z) = (term70 x y z).
Proof. exact (TRANS (@lem1512280 x y z) (@lem1512289 x y z)). Qed.
Lemma lem1512292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1512293 (x : real) (y : real) (z : real) : (term82 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1512292) (@lem1512291 x y z)). Qed.
Lemma lem1512294 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512295 (x : real) (y : real) (z : real) : (term79 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1512293 x y z) (@lem1512294)). Qed.
Lemma lem1512296 (x : real) (y : real) (z : real) : (term78 x y z) = (term73 x y z).
Proof. exact (TRANS (@lem1512268 x y z) (@lem1512295 x y z)). Qed.
Lemma lem1512297 (z : real) (y : real) (x : real) : (term3 x z y) = (term83 z y x).
Proof. exact (@lem1483521 (real_sub z y) x). Qed.
Lemma lem1512298 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1512304 (z : real) (y : real) : (real_sub z y) = (term41 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1512309 (y : real) (z : real) : (term41 z y) = (term42 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1512311 (y : real) (z : real) : (real_sub z y) = (term42 y z).
Proof. exact (TRANS (@lem1512304 z y) (@lem1512309 y z)). Qed.
Lemma lem1512312 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1512313 (y : real) (z : real) : (term84 z y) = (term85 y z).
Proof. exact (MK_COMB (@lem1512312) (@lem1512311 y z)). Qed.
Lemma lem1512314 (y : real) (z : real) (x : real) : (term86 z y x) = (term87 y z x).
Proof. exact (MK_COMB (@lem1512313 y z) (@lem1512298 x)). Qed.
Lemma lem1512315 (y : real) (z : real) (x : real) : (term87 y z x) = (term88 y z x).
Proof. exact (@lem1483519 (term42 y z) x). Qed.
Lemma lem1512320 (x : real) (y : real) (z : real) : (term88 y z x) = (term44 x y z).
Proof. exact (@lem1483488 (term40 x) (term42 y z)). Qed.
Lemma lem1512321 (x : real) (y : real) (z : real) : (term87 y z x) = (term44 x y z).
Proof. exact (TRANS (@lem1512315 y z x) (@lem1512320 x y z)). Qed.
Lemma lem1512322 (x : real) (y : real) (z : real) : (term86 z y x) = (term44 x y z).
Proof. exact (TRANS (@lem1512314 y z x) (@lem1512321 x y z)). Qed.
Lemma lem1512323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1512324 (x : real) (y : real) (z : real) : (term89 z y x) = (term46 x y z).
Proof. exact (MK_COMB (@lem1512323) (@lem1512322 x y z)). Qed.
Lemma lem1512325 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512326 (x : real) (y : real) (z : real) : (term83 z y x) = (term48 x y z).
Proof. exact (MK_COMB (@lem1512324 x y z) (@lem1512325)). Qed.
Lemma lem1512327 (x : real) (y : real) (z : real) : (term3 x z y) = (term48 x y z).
Proof. exact (TRANS (@lem1512297 z y x) (@lem1512326 x y z)). Qed.
Lemma lem1512328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1512329 (x : real) (y : real) (z : real) : (term90 x y z) = (term91 x y z).
Proof. exact (MK_COMB (@lem1512328) (@lem1512296 x y z)). Qed.
Lemma lem1512330 (x : real) (y : real) (z : real) : (term92 x z y) = (term93 x y z).
Proof. exact (MK_COMB (@lem1512329 x y z) (@lem1512327 x y z)). Qed.
Lemma lem1512331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512332 (x : real) (y : real) (z : real) : (term94 x z y) = (term95 x y z).
Proof. exact (MK_COMB (@lem1512331) (@lem1512267 x y z)). Qed.
Lemma lem1512333 (x : real) (y : real) (z : real) : (term1 x z y) = (term96 x y z).
Proof. exact (MK_COMB (@lem1512332 x y z) (@lem1512330 x y z)). Qed.
Lemma lem1512334 (x : real) (y : real) : (term12 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1512333 x y z)). Qed.
Lemma lem1512335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512336 (x : real) (y : real) : (term13 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1512335) (@lem1512334 x y)). Qed.
Lemma lem1512337 (x : real) : (term21 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1512336 x y)). Qed.
Lemma lem1512338 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512339 (x : real) : (term22 x) = (term100 x).
Proof. exact (MK_COMB (@lem1512338) (@lem1512337 x)). Qed.
Lemma lem1512340 : term30 = term101.
Proof. exact (fun_ext (fun x : real => @lem1512339 x)). Qed.
Lemma lem1512341 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512342 : term31 = term102.
Proof. exact (MK_COMB (@lem1512341) (@lem1512340)). Qed.
Lemma lem1512343 : term23 = term102.
Proof. exact (TRANS (@lem1512177) (@lem1512342)). Qed.
Lemma lem1512353 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1512354 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1512353 real P Q). Qed.
Lemma lem1512355 (x : real) (y : real) : (term107 x y) = (term108 x y).
Proof. exact (@lem1512354 (term109 x y) (term110 x y)). Qed.
Lemma lem1512356 (x : real) (y : real) (z : real) : (term111 x y z) = (term77 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1512357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512358 (x : real) (y : real) (z : real) : (term112 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1512357) (@lem1512356 x y z)). Qed.
Lemma lem1512359 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1512360 (x : real) (y : real) (z : real) : (term114 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1512358 x y z) (@lem1512359 x y z)). Qed.
Lemma lem1512361 (x : real) (y : real) : (term115 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1512360 x y z)). Qed.
Lemma lem1512362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512363 (x : real) (y : real) : (term107 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1512362) (@lem1512361 x y)). Qed.
Lemma lem1512364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512365 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1512364) (@lem1512363 x y)). Qed.
Lemma lem1512366 (x : real) (y : real) (z : real) : (term111 x y z) = (term77 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1512367 (x : real) (y : real) : (term118 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1512366 x y z)). Qed.
Lemma lem1512368 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512369 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1512368) (@lem1512367 x y)). Qed.
Lemma lem1512370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512371 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1512370) (@lem1512369 x y)). Qed.
Lemma lem1512372 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1512373 (x : real) (y : real) : (term123 x y) = (term110 x y).
Proof. exact (fun_ext (fun z : real => @lem1512372 x y z)). Qed.
Lemma lem1512374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512375 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1512374) (@lem1512373 x y)). Qed.
Lemma lem1512376 (x : real) (y : real) : (term108 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1512371 x y) (@lem1512375 x y)). Qed.
Lemma lem1512377 (x : real) (y : real) : ((term107 x y) = (term108 x y)) = ((term98 x y) = (term126 x y)).
Proof. exact (MK_COMB (@lem1512365 x y) (@lem1512376 x y)). Qed.
Lemma lem1512378 (x : real) (y : real) : (term98 x y) = (term126 x y).
Proof. exact (EQ_MP (@lem1512377 x y) (@lem1512355 x y)). Qed.
Lemma lem1512475 (x : real) : (term99 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1512378 x y)). Qed.
Lemma lem1512476 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512477 (x : real) : (term100 x) = (term128 x).
Proof. exact (MK_COMB (@lem1512476) (@lem1512475 x)). Qed.
Lemma lem1512479 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1512480 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1512479 real P Q). Qed.
Lemma lem1512481 (x : real) : (term129 x) = (term130 x).
Proof. exact (@lem1512480 (term131 x) (term132 x)). Qed.
Lemma lem1512482 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1512483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512484 (x : real) (y : real) : (term134 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1512483) (@lem1512482 x y)). Qed.
Lemma lem1512485 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1512486 (x : real) (y : real) : (term136 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1512484 x y) (@lem1512485 x y)). Qed.
Lemma lem1512487 (x : real) : (term137 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1512486 x y)). Qed.
Lemma lem1512488 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512489 (x : real) : (term129 x) = (term128 x).
Proof. exact (MK_COMB (@lem1512488) (@lem1512487 x)). Qed.
Lemma lem1512490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512491 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1512490) (@lem1512489 x)). Qed.
Lemma lem1512492 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1512493 (x : real) : (term140 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1512492 x y)). Qed.
Lemma lem1512494 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512495 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1512494) (@lem1512493 x)). Qed.
Lemma lem1512496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512497 (x : real) : (term143 x) = (term144 x).
Proof. exact (MK_COMB (@lem1512496) (@lem1512495 x)). Qed.
Lemma lem1512498 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1512499 (x : real) : (term145 x) = (term132 x).
Proof. exact (fun_ext (fun y : real => @lem1512498 x y)). Qed.
Lemma lem1512500 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512501 (x : real) : (term146 x) = (term147 x).
Proof. exact (MK_COMB (@lem1512500) (@lem1512499 x)). Qed.
Lemma lem1512502 (x : real) : (term130 x) = (term148 x).
Proof. exact (MK_COMB (@lem1512497 x) (@lem1512501 x)). Qed.
Lemma lem1512503 (x : real) : ((term129 x) = (term130 x)) = ((term128 x) = (term148 x)).
Proof. exact (MK_COMB (@lem1512491 x) (@lem1512502 x)). Qed.
Lemma lem1512504 (x : real) : (term128 x) = (term148 x).
Proof. exact (EQ_MP (@lem1512503 x) (@lem1512481 x)). Qed.
Lemma lem1512609 (x : real) : (term100 x) = (term148 x).
Proof. exact (TRANS (@lem1512477 x) (@lem1512504 x)). Qed.
Lemma lem1512610 : term101 = term149.
Proof. exact (fun_ext (fun x : real => @lem1512609 x)). Qed.
Lemma lem1512611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512612 : term102 = term150.
Proof. exact (MK_COMB (@lem1512611) (@lem1512610)). Qed.
Lemma lem1512614 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1512615 (P : real -> Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1512614 real P Q). Qed.
Lemma lem1512616 : term151 = term152.
Proof. exact (@lem1512615 term153 term154). Qed.
Lemma lem1512617 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1512618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512619 (x : real) : (term156 x) = (term144 x).
Proof. exact (MK_COMB (@lem1512618) (@lem1512617 x)). Qed.
Lemma lem1512620 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1512621 (x : real) : (term158 x) = (term148 x).
Proof. exact (MK_COMB (@lem1512619 x) (@lem1512620 x)). Qed.
Lemma lem1512622 : term159 = term149.
Proof. exact (fun_ext (fun x : real => @lem1512621 x)). Qed.
Lemma lem1512623 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512624 : term151 = term150.
Proof. exact (MK_COMB (@lem1512623) (@lem1512622)). Qed.
Lemma lem1512625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512626 : term160 = term161.
Proof. exact (MK_COMB (@lem1512625) (@lem1512624)). Qed.
Lemma lem1512627 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1512628 : term162 = term153.
Proof. exact (fun_ext (fun x : real => @lem1512627 x)). Qed.
Lemma lem1512629 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512630 : term163 = term164.
Proof. exact (MK_COMB (@lem1512629) (@lem1512628)). Qed.
Lemma lem1512631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512632 : term165 = term166.
Proof. exact (MK_COMB (@lem1512631) (@lem1512630)). Qed.
Lemma lem1512633 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1512634 : term167 = term154.
Proof. exact (fun_ext (fun x : real => @lem1512633 x)). Qed.
Lemma lem1512635 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512636 : term168 = term169.
Proof. exact (MK_COMB (@lem1512635) (@lem1512634)). Qed.
Lemma lem1512637 : term152 = term170.
Proof. exact (MK_COMB (@lem1512632) (@lem1512636)). Qed.
Lemma lem1512638 : (term151 = term152) = (term150 = term170).
Proof. exact (MK_COMB (@lem1512626) (@lem1512637)). Qed.
Lemma lem1512639 : term150 = term170.
Proof. exact (EQ_MP (@lem1512638) (@lem1512616)). Qed.
Lemma lem1512752 : term102 = term170.
Proof. exact (TRANS (@lem1512612) (@lem1512639)). Qed.
Lemma lem1512754 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1512755 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1512754 real P Q). Qed.
Lemma lem1512756 : term152 = term151.
Proof. exact (@lem1512755 term153 term154). Qed.
Lemma lem1512757 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1512758 : term162 = term153.
Proof. exact (fun_ext (fun x : real => @lem1512757 x)). Qed.
Lemma lem1512759 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512760 : term163 = term164.
Proof. exact (MK_COMB (@lem1512759) (@lem1512758)). Qed.
Lemma lem1512761 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512762 : term165 = term166.
Proof. exact (MK_COMB (@lem1512761) (@lem1512760)). Qed.
Lemma lem1512763 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1512764 : term167 = term154.
Proof. exact (fun_ext (fun x : real => @lem1512763 x)). Qed.
Lemma lem1512765 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512766 : term168 = term169.
Proof. exact (MK_COMB (@lem1512765) (@lem1512764)). Qed.
Lemma lem1512767 : term152 = term170.
Proof. exact (MK_COMB (@lem1512762) (@lem1512766)). Qed.
Lemma lem1512768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512769 : term171 = term172.
Proof. exact (MK_COMB (@lem1512768) (@lem1512767)). Qed.
Lemma lem1512770 (x : real) : (term155 x) = (term142 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1512771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512772 (x : real) : (term156 x) = (term144 x).
Proof. exact (MK_COMB (@lem1512771) (@lem1512770 x)). Qed.
Lemma lem1512773 (x : real) : (term157 x) = (term147 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1512774 (x : real) : (term158 x) = (term148 x).
Proof. exact (MK_COMB (@lem1512772 x) (@lem1512773 x)). Qed.
Lemma lem1512775 : term159 = term149.
Proof. exact (fun_ext (fun x : real => @lem1512774 x)). Qed.
Lemma lem1512776 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512777 : term151 = term150.
Proof. exact (MK_COMB (@lem1512776) (@lem1512775)). Qed.
Lemma lem1512778 : (term152 = term151) = (term170 = term150).
Proof. exact (MK_COMB (@lem1512769) (@lem1512777)). Qed.
Lemma lem1512779 : term170 = term150.
Proof. exact (EQ_MP (@lem1512778) (@lem1512756)). Qed.
Lemma lem1512781 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1512782 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1512781 real P Q). Qed.
Lemma lem1512783 (x : real) : (term130 x) = (term129 x).
Proof. exact (@lem1512782 (term131 x) (term132 x)). Qed.
Lemma lem1512784 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1512785 (x : real) : (term140 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1512784 x y)). Qed.
Lemma lem1512786 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512787 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1512786) (@lem1512785 x)). Qed.
Lemma lem1512788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512789 (x : real) : (term143 x) = (term144 x).
Proof. exact (MK_COMB (@lem1512788) (@lem1512787 x)). Qed.
Lemma lem1512790 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1512791 (x : real) : (term145 x) = (term132 x).
Proof. exact (fun_ext (fun y : real => @lem1512790 x y)). Qed.
Lemma lem1512792 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512793 (x : real) : (term146 x) = (term147 x).
Proof. exact (MK_COMB (@lem1512792) (@lem1512791 x)). Qed.
Lemma lem1512794 (x : real) : (term130 x) = (term148 x).
Proof. exact (MK_COMB (@lem1512789 x) (@lem1512793 x)). Qed.
Lemma lem1512795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512796 (x : real) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem1512795) (@lem1512794 x)). Qed.
Lemma lem1512797 (x : real) (y : real) : (term133 x y) = (term120 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1512798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512799 (x : real) (y : real) : (term134 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1512798) (@lem1512797 x y)). Qed.
Lemma lem1512800 (x : real) (y : real) : (term135 x y) = (term125 x y).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem1512801 (x : real) (y : real) : (term136 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1512799 x y) (@lem1512800 x y)). Qed.
Lemma lem1512802 (x : real) : (term137 x) = (term127 x).
Proof. exact (fun_ext (fun y : real => @lem1512801 x y)). Qed.
Lemma lem1512803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512804 (x : real) : (term129 x) = (term128 x).
Proof. exact (MK_COMB (@lem1512803) (@lem1512802 x)). Qed.
Lemma lem1512805 (x : real) : ((term130 x) = (term129 x)) = ((term148 x) = (term128 x)).
Proof. exact (MK_COMB (@lem1512796 x) (@lem1512804 x)). Qed.
Lemma lem1512806 (x : real) : (term148 x) = (term128 x).
Proof. exact (EQ_MP (@lem1512805 x) (@lem1512783 x)). Qed.
Lemma lem1512808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1512809 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem1512808 real P Q). Qed.
Lemma lem1512810 (x : real) (y : real) : (term108 x y) = (term107 x y).
Proof. exact (@lem1512809 (term109 x y) (term110 x y)). Qed.
Lemma lem1512811 (x : real) (y : real) (z : real) : (term111 x y z) = (term77 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1512812 (x : real) (y : real) : (term118 x y) = (term109 x y).
Proof. exact (fun_ext (fun z : real => @lem1512811 x y z)). Qed.
Lemma lem1512813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512814 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1512813) (@lem1512812 x y)). Qed.
Lemma lem1512815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512816 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (MK_COMB (@lem1512815) (@lem1512814 x y)). Qed.
Lemma lem1512817 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1512818 (x : real) (y : real) : (term123 x y) = (term110 x y).
Proof. exact (fun_ext (fun z : real => @lem1512817 x y z)). Qed.
Lemma lem1512819 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512820 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1512819) (@lem1512818 x y)). Qed.
Lemma lem1512821 (x : real) (y : real) : (term108 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1512816 x y) (@lem1512820 x y)). Qed.
Lemma lem1512822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1512823 (x : real) (y : real) : (term175 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1512822) (@lem1512821 x y)). Qed.
Lemma lem1512824 (x : real) (y : real) (z : real) : (term111 x y z) = (term77 x y z).
Proof. exact (eq_refl (term111 x y z)). Qed.
Lemma lem1512825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1512826 (x : real) (y : real) (z : real) : (term112 x y z) = (term95 x y z).
Proof. exact (MK_COMB (@lem1512825) (@lem1512824 x y z)). Qed.
Lemma lem1512827 (x : real) (y : real) (z : real) : (term113 x y z) = (term93 x y z).
Proof. exact (eq_refl (term113 x y z)). Qed.
Lemma lem1512828 (x : real) (y : real) (z : real) : (term114 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1512826 x y z) (@lem1512827 x y z)). Qed.
Lemma lem1512829 (x : real) (y : real) : (term115 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1512828 x y z)). Qed.
Lemma lem1512830 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512831 (x : real) (y : real) : (term107 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1512830) (@lem1512829 x y)). Qed.
Lemma lem1512832 (x : real) (y : real) : ((term108 x y) = (term107 x y)) = ((term126 x y) = (term98 x y)).
Proof. exact (MK_COMB (@lem1512823 x y) (@lem1512831 x y)). Qed.
Lemma lem1512833 (x : real) (y : real) : (term126 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem1512832 x y) (@lem1512810 x y)). Qed.
Lemma lem1512834 (x : real) : (term127 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1512833 x y)). Qed.
Lemma lem1512835 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512836 (x : real) : (term128 x) = (term100 x).
Proof. exact (MK_COMB (@lem1512835) (@lem1512834 x)). Qed.
Lemma lem1512837 (x : real) : (term148 x) = (term100 x).
Proof. exact (TRANS (@lem1512806 x) (@lem1512836 x)). Qed.
Lemma lem1512838 : term149 = term101.
Proof. exact (fun_ext (fun x : real => @lem1512837 x)). Qed.
Lemma lem1512839 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512840 : term150 = term102.
Proof. exact (MK_COMB (@lem1512839) (@lem1512838)). Qed.
Lemma lem1512841 : term170 = term102.
Proof. exact (TRANS (@lem1512779) (@lem1512840)). Qed.
Lemma lem1512842 : term102 = term102.
Proof. exact (TRANS (@lem1512752) (@lem1512841)). Qed.
Lemma lem1512845 : term23 = term102.
Proof. exact (TRANS (@lem1512343) (@lem1512842)). Qed.
Lemma lem1512862 (x : real) (y : real) (z : real) : (term96 x y z) = (term96 x y z).
Proof. exact (eq_refl (term96 x y z)). Qed.
Lemma lem1512863 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1512862 x y z)). Qed.
Lemma lem1512864 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512865 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1512864) (@lem1512863 x y)). Qed.
Lemma lem1512866 (x : real) : (term99 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem1512865 x y)). Qed.
Lemma lem1512867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512868 (x : real) : (term100 x) = (term100 x).
Proof. exact (MK_COMB (@lem1512867) (@lem1512866 x)). Qed.
Lemma lem1512869 : term101 = term101.
Proof. exact (fun_ext (fun x : real => @lem1512868 x)). Qed.
Lemma lem1512870 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1512871 : term102 = term102.
Proof. exact (MK_COMB (@lem1512870) (@lem1512869)). Qed.
Lemma lem1512872 : term23 = term102.
Proof. exact (TRANS (@lem1512845) (@lem1512871)). Qed.
Lemma lem1512882 (x : real) (y : real) (z : real) (h1 : term96 x y z) : term96 x y z.
Proof. exact (h1). Qed.
Lemma lem1512883 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term77 x y z.
Proof. exact (h1). Qed.
Lemma lem1512884 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term73 x y z.
Proof. exact (proj2 (@lem1512883 x y z h1)). Qed.
Lemma lem1512885 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term48 x y z.
Proof. exact (proj1 (@lem1512883 x y z h1)). Qed.
Lemma lem1512887 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512888 : term178 = term179.
Proof. exact (@lem1512887 (NUMERAL 0) term62). Qed.
Lemma lem1512889 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1512890 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1512891 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1512890 h1) (fun h1 : term179 = True => @lem1512889)). Qed.
Lemma lem1512892 : term179 = True.
Proof. exact (EQ_MP (@lem1512891) (@lem1512889)). Qed.
Lemma lem1512893 : term178 = True.
Proof. exact (TRANS (@lem1512888) (@lem1512892)). Qed.
Lemma lem1512894 : True = term178.
Proof. exact (SYM (@lem1512893)). Qed.
Lemma lem1512895 : term178.
Proof. exact (EQ_MP (@lem1512894) (@lem0)). Qed.
Lemma lem1512896 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term181 x y z.
Proof. exact (conj (@lem1512895) (@lem1512884 x y z h1)). Qed.
Lemma lem1512898 (x : real) (y : real) : term182 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1512899 (x : real) (y : real) (z : real) : term183 x y z.
Proof. exact (@lem1512898 term65 (term70 x y z)). Qed.
Lemma lem1512900 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term184 x y z.
Proof. exact (@lem1512899 x y z (@lem1512896 x y z h1)). Qed.
Lemma lem1512901 (x : real) (y : real) (z : real) : (term185 x y z) = (term70 x y z).
Proof. exact (@lem1483460 (term70 x y z)). Qed.
Lemma lem1512902 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1512903 (x : real) (y : real) (z : real) : (term186 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1512902) (@lem1512901 x y z)). Qed.
Lemma lem1512904 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512905 (x : real) (y : real) (z : real) : (term184 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1512903 x y z) (@lem1512904)). Qed.
Lemma lem1512906 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term73 x y z.
Proof. exact (EQ_MP (@lem1512905 x y z) (@lem1512900 x y z h1)). Qed.
Lemma lem1512908 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512909 : term178 = term179.
Proof. exact (@lem1512908 (NUMERAL 0) term62). Qed.
Lemma lem1512910 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1512911 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1512912 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1512911 h1) (fun h1 : term179 = True => @lem1512910)). Qed.
Lemma lem1512913 : term179 = True.
Proof. exact (EQ_MP (@lem1512912) (@lem1512910)). Qed.
Lemma lem1512914 : term178 = True.
Proof. exact (TRANS (@lem1512909) (@lem1512913)). Qed.
Lemma lem1512915 : True = term178.
Proof. exact (SYM (@lem1512914)). Qed.
Lemma lem1512916 : term178.
Proof. exact (EQ_MP (@lem1512915) (@lem0)). Qed.
Lemma lem1512917 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term187 x y z.
Proof. exact (conj (@lem1512916) (@lem1512885 x y z h1)). Qed.
Lemma lem1512919 (x : real) (y : real) : term188 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1512920 (x : real) (y : real) (z : real) : term189 x y z.
Proof. exact (@lem1512919 term65 (term44 x y z)). Qed.
Lemma lem1512921 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term190 x y z.
Proof. exact (@lem1512920 x y z (@lem1512917 x y z h1)). Qed.
Lemma lem1512922 (x : real) (y : real) (z : real) : (term191 x y z) = (term44 x y z).
Proof. exact (@lem1483460 (term44 x y z)). Qed.
Lemma lem1512923 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1512924 (x : real) (y : real) (z : real) : (term192 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1512923) (@lem1512922 x y z)). Qed.
Lemma lem1512925 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512926 (x : real) (y : real) (z : real) : (term190 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem1512924 x y z) (@lem1512925)). Qed.
Lemma lem1512927 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term48 x y z.
Proof. exact (EQ_MP (@lem1512926 x y z) (@lem1512921 x y z h1)). Qed.
Lemma lem1512928 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term77 x y z.
Proof. exact (conj (@lem1512927 x y z h1) (@lem1512906 x y z h1)). Qed.
Lemma lem1512930 (x : real) (y : real) : term193 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1512931 (x : real) (y : real) (z : real) : term194 x y z.
Proof. exact (@lem1512930 (term44 x y z) (term70 x y z)). Qed.
Lemma lem1512932 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term195 x y z.
Proof. exact (@lem1512931 x y z (@lem1512928 x y z h1)). Qed.
Lemma lem1512933 (x : real) (y : real) (z : real) : (term196 x y z) = (term197 x y z).
Proof. exact (@lem1483480 (term40 x) x (term42 y z) (term41 y z)). Qed.
Lemma lem1512934 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1512936 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1512937 : term201 = term47.
Proof. exact (@lem1512936 term62). Qed.
Lemma lem1512938 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1512939 : term202 = term203.
Proof. exact (MK_COMB (@lem1512938) (@lem1512937)). Qed.
Lemma lem1512940 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1512941 (x : real) : (term199 x) = (term204 x).
Proof. exact (MK_COMB (@lem1512939) (@lem1512940 x)). Qed.
Lemma lem1512942 (x : real) : (term198 x) = (term204 x).
Proof. exact (TRANS (@lem1512934 x) (@lem1512941 x)). Qed.
Lemma lem1512943 (x : real) : (term204 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1512944 (x : real) : (term198 x) = term47.
Proof. exact (TRANS (@lem1512942 x) (@lem1512943 x)). Qed.
Lemma lem1512945 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1512946 (x : real) : (term205 x) = term206.
Proof. exact (MK_COMB (@lem1512945) (@lem1512944 x)). Qed.
Lemma lem1512947 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1512948 (y : real) : (term198 y) = (term199 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1512950 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1512951 : term201 = term47.
Proof. exact (@lem1512950 term62). Qed.
Lemma lem1512952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1512953 : term202 = term203.
Proof. exact (MK_COMB (@lem1512952) (@lem1512951)). Qed.
Lemma lem1512954 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1512955 (y : real) : (term199 y) = (term204 y).
Proof. exact (MK_COMB (@lem1512953) (@lem1512954 y)). Qed.
Lemma lem1512956 (y : real) : (term198 y) = (term204 y).
Proof. exact (TRANS (@lem1512948 y) (@lem1512955 y)). Qed.
Lemma lem1512957 (y : real) : (term204 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1512958 (y : real) : (term198 y) = term47.
Proof. exact (TRANS (@lem1512956 y) (@lem1512957 y)). Qed.
Lemma lem1512959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1512960 (y : real) : (term205 y) = term206.
Proof. exact (MK_COMB (@lem1512959) (@lem1512958 y)). Qed.
Lemma lem1512961 (z : real) : (term209 z) = (term199 z).
Proof. exact (@lem1483442 term37 z). Qed.
Lemma lem1512963 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1512964 : term201 = term47.
Proof. exact (@lem1512963 term62). Qed.
Lemma lem1512965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1512966 : term202 = term203.
Proof. exact (MK_COMB (@lem1512965) (@lem1512964)). Qed.
Lemma lem1512967 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1512968 (z : real) : (term199 z) = (term204 z).
Proof. exact (MK_COMB (@lem1512966) (@lem1512967 z)). Qed.
Lemma lem1512969 (z : real) : (term209 z) = (term204 z).
Proof. exact (TRANS (@lem1512961 z) (@lem1512968 z)). Qed.
Lemma lem1512970 (z : real) : (term204 z) = term47.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1512971 (z : real) : (term209 z) = term47.
Proof. exact (TRANS (@lem1512969 z) (@lem1512970 z)). Qed.
Lemma lem1512972 (y : real) (z : real) : (term208 y z) = term210.
Proof. exact (MK_COMB (@lem1512960 y) (@lem1512971 z)). Qed.
Lemma lem1512973 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (TRANS (@lem1512947 y z) (@lem1512972 y z)). Qed.
Lemma lem1512974 : term210 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1512975 (y : real) (z : real) : (term207 y z) = term47.
Proof. exact (TRANS (@lem1512973 y z) (@lem1512974)). Qed.
Lemma lem1512976 (x : real) (y : real) (z : real) : (term197 x y z) = term210.
Proof. exact (MK_COMB (@lem1512946 x) (@lem1512975 y z)). Qed.
Lemma lem1512977 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (TRANS (@lem1512933 x y z) (@lem1512976 x y z)). Qed.
Lemma lem1512978 : term210 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1512979 (x : real) (y : real) (z : real) : (term196 x y z) = term47.
Proof. exact (TRANS (@lem1512977 x y z) (@lem1512978)). Qed.
Lemma lem1512980 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1512981 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1512980) (@lem1512979 x y z)). Qed.
Lemma lem1512982 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1512983 (x : real) (y : real) (z : real) : (term195 x y z) = term213.
Proof. exact (MK_COMB (@lem1512981 x y z) (@lem1512982)). Qed.
Lemma lem1512984 (x : real) (y : real) (z : real) (h1 : term77 x y z) : term213.
Proof. exact (EQ_MP (@lem1512983 x y z) (@lem1512932 x y z h1)). Qed.
Lemma lem1512986 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512987 : term213 = term214.
Proof. exact (@lem1512986 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1512988 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1512989 : term213 = False.
Proof. exact (TRANS (@lem1512987) (@lem1512988)). Qed.
Lemma lem1512990 (x : real) (y : real) (z : real) (h1 : term77 x y z) : False.
Proof. exact (EQ_MP (@lem1512989) (@lem1512984 x y z h1)). Qed.
Lemma lem1512991 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term93 x y z.
Proof. exact (h1). Qed.
Lemma lem1512992 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term48 x y z.
Proof. exact (proj2 (@lem1512991 x y z h1)). Qed.
Lemma lem1512993 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term73 x y z.
Proof. exact (proj1 (@lem1512991 x y z h1)). Qed.
Lemma lem1512995 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1512996 : term178 = term179.
Proof. exact (@lem1512995 (NUMERAL 0) term62). Qed.
Lemma lem1512997 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1512998 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1512999 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1512998 h1) (fun h1 : term179 = True => @lem1512997)). Qed.
Lemma lem1513000 : term179 = True.
Proof. exact (EQ_MP (@lem1512999) (@lem1512997)). Qed.
Lemma lem1513001 : term178 = True.
Proof. exact (TRANS (@lem1512996) (@lem1513000)). Qed.
Lemma lem1513002 : True = term178.
Proof. exact (SYM (@lem1513001)). Qed.
Lemma lem1513003 : term178.
Proof. exact (EQ_MP (@lem1513002) (@lem0)). Qed.
Lemma lem1513004 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term181 x y z.
Proof. exact (conj (@lem1513003) (@lem1512993 x y z h1)). Qed.
Lemma lem1513006 (x : real) (y : real) : term182 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1513007 (x : real) (y : real) (z : real) : term183 x y z.
Proof. exact (@lem1513006 term65 (term70 x y z)). Qed.
Lemma lem1513008 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term184 x y z.
Proof. exact (@lem1513007 x y z (@lem1513004 x y z h1)). Qed.
Lemma lem1513009 (x : real) (y : real) (z : real) : (term185 x y z) = (term70 x y z).
Proof. exact (@lem1483460 (term70 x y z)). Qed.
Lemma lem1513010 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1513011 (x : real) (y : real) (z : real) : (term186 x y z) = (term72 x y z).
Proof. exact (MK_COMB (@lem1513010) (@lem1513009 x y z)). Qed.
Lemma lem1513012 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1513013 (x : real) (y : real) (z : real) : (term184 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1513011 x y z) (@lem1513012)). Qed.
Lemma lem1513014 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term73 x y z.
Proof. exact (EQ_MP (@lem1513013 x y z) (@lem1513008 x y z h1)). Qed.
Lemma lem1513016 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1513017 : term178 = term179.
Proof. exact (@lem1513016 (NUMERAL 0) term62). Qed.
Lemma lem1513018 : term180 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1513019 (h1 : term180 = (BIT1 0)) : term179 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1513020 : (term180 = (BIT1 0)) = (term179 = True).
Proof. exact (prop_ext (fun h1 : term180 = (BIT1 0) => @lem1513019 h1) (fun h1 : term179 = True => @lem1513018)). Qed.
Lemma lem1513021 : term179 = True.
Proof. exact (EQ_MP (@lem1513020) (@lem1513018)). Qed.
Lemma lem1513022 : term178 = True.
Proof. exact (TRANS (@lem1513017) (@lem1513021)). Qed.
Lemma lem1513023 : True = term178.
Proof. exact (SYM (@lem1513022)). Qed.
Lemma lem1513024 : term178.
Proof. exact (EQ_MP (@lem1513023) (@lem0)). Qed.
Lemma lem1513025 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term187 x y z.
Proof. exact (conj (@lem1513024) (@lem1512992 x y z h1)). Qed.
Lemma lem1513027 (x : real) (y : real) : term188 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1513028 (x : real) (y : real) (z : real) : term189 x y z.
Proof. exact (@lem1513027 term65 (term44 x y z)). Qed.
Lemma lem1513029 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term190 x y z.
Proof. exact (@lem1513028 x y z (@lem1513025 x y z h1)). Qed.
Lemma lem1513030 (x : real) (y : real) (z : real) : (term191 x y z) = (term44 x y z).
Proof. exact (@lem1483460 (term44 x y z)). Qed.
Lemma lem1513031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1513032 (x : real) (y : real) (z : real) : (term192 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1513031) (@lem1513030 x y z)). Qed.
Lemma lem1513033 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1513034 (x : real) (y : real) (z : real) : (term190 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem1513032 x y z) (@lem1513033)). Qed.
Lemma lem1513035 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term48 x y z.
Proof. exact (EQ_MP (@lem1513034 x y z) (@lem1513029 x y z h1)). Qed.
Lemma lem1513036 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term77 x y z.
Proof. exact (conj (@lem1513035 x y z h1) (@lem1513014 x y z h1)). Qed.
Lemma lem1513038 (x : real) (y : real) : term193 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1513039 (x : real) (y : real) (z : real) : term194 x y z.
Proof. exact (@lem1513038 (term44 x y z) (term70 x y z)). Qed.
Lemma lem1513040 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term195 x y z.
Proof. exact (@lem1513039 x y z (@lem1513036 x y z h1)). Qed.
Lemma lem1513041 (x : real) (y : real) (z : real) : (term196 x y z) = (term197 x y z).
Proof. exact (@lem1483480 (term40 x) x (term42 y z) (term41 y z)). Qed.
Lemma lem1513042 (x : real) : (term198 x) = (term199 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1513044 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513045 : term201 = term47.
Proof. exact (@lem1513044 term62). Qed.
Lemma lem1513046 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513047 : term202 = term203.
Proof. exact (MK_COMB (@lem1513046) (@lem1513045)). Qed.
Lemma lem1513048 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1513049 (x : real) : (term199 x) = (term204 x).
Proof. exact (MK_COMB (@lem1513047) (@lem1513048 x)). Qed.
Lemma lem1513050 (x : real) : (term198 x) = (term204 x).
Proof. exact (TRANS (@lem1513042 x) (@lem1513049 x)). Qed.
Lemma lem1513051 (x : real) : (term204 x) = term47.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1513052 (x : real) : (term198 x) = term47.
Proof. exact (TRANS (@lem1513050 x) (@lem1513051 x)). Qed.
Lemma lem1513053 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1513054 (x : real) : (term205 x) = term206.
Proof. exact (MK_COMB (@lem1513053) (@lem1513052 x)). Qed.
Lemma lem1513055 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1513056 (y : real) : (term198 y) = (term199 y).
Proof. exact (@lem1483440 term37 y). Qed.
Lemma lem1513058 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513059 : term201 = term47.
Proof. exact (@lem1513058 term62). Qed.
Lemma lem1513060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513061 : term202 = term203.
Proof. exact (MK_COMB (@lem1513060) (@lem1513059)). Qed.
Lemma lem1513062 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1513063 (y : real) : (term199 y) = (term204 y).
Proof. exact (MK_COMB (@lem1513061) (@lem1513062 y)). Qed.
Lemma lem1513064 (y : real) : (term198 y) = (term204 y).
Proof. exact (TRANS (@lem1513056 y) (@lem1513063 y)). Qed.
Lemma lem1513065 (y : real) : (term204 y) = term47.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1513066 (y : real) : (term198 y) = term47.
Proof. exact (TRANS (@lem1513064 y) (@lem1513065 y)). Qed.
Lemma lem1513067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1513068 (y : real) : (term205 y) = term206.
Proof. exact (MK_COMB (@lem1513067) (@lem1513066 y)). Qed.
Lemma lem1513069 (z : real) : (term209 z) = (term199 z).
Proof. exact (@lem1483442 term37 z). Qed.
Lemma lem1513071 (m : nat) : (term200 m) = term47.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1513072 : term201 = term47.
Proof. exact (@lem1513071 term62). Qed.
Lemma lem1513073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1513074 : term202 = term203.
Proof. exact (MK_COMB (@lem1513073) (@lem1513072)). Qed.
Lemma lem1513075 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1513076 (z : real) : (term199 z) = (term204 z).
Proof. exact (MK_COMB (@lem1513074) (@lem1513075 z)). Qed.
Lemma lem1513077 (z : real) : (term209 z) = (term204 z).
Proof. exact (TRANS (@lem1513069 z) (@lem1513076 z)). Qed.
Lemma lem1513078 (z : real) : (term204 z) = term47.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1513079 (z : real) : (term209 z) = term47.
Proof. exact (TRANS (@lem1513077 z) (@lem1513078 z)). Qed.
Lemma lem1513080 (y : real) (z : real) : (term208 y z) = term210.
Proof. exact (MK_COMB (@lem1513068 y) (@lem1513079 z)). Qed.
Lemma lem1513081 (y : real) (z : real) : (term207 y z) = term210.
Proof. exact (TRANS (@lem1513055 y z) (@lem1513080 y z)). Qed.
Lemma lem1513082 : term210 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1513083 (y : real) (z : real) : (term207 y z) = term47.
Proof. exact (TRANS (@lem1513081 y z) (@lem1513082)). Qed.
Lemma lem1513084 (x : real) (y : real) (z : real) : (term197 x y z) = term210.
Proof. exact (MK_COMB (@lem1513054 x) (@lem1513083 y z)). Qed.
Lemma lem1513085 (x : real) (y : real) (z : real) : (term196 x y z) = term210.
Proof. exact (TRANS (@lem1513041 x y z) (@lem1513084 x y z)). Qed.
Lemma lem1513086 : term210 = term47.
Proof. exact (@lem1483448 term47). Qed.
Lemma lem1513087 (x : real) (y : real) (z : real) : (term196 x y z) = term47.
Proof. exact (TRANS (@lem1513085 x y z) (@lem1513086)). Qed.
Lemma lem1513088 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1513089 (x : real) (y : real) (z : real) : (term211 x y z) = term212.
Proof. exact (MK_COMB (@lem1513088) (@lem1513087 x y z)). Qed.
Lemma lem1513090 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1513091 (x : real) (y : real) (z : real) : (term195 x y z) = term213.
Proof. exact (MK_COMB (@lem1513089 x y z) (@lem1513090)). Qed.
Lemma lem1513092 (x : real) (y : real) (z : real) (h1 : term93 x y z) : term213.
Proof. exact (EQ_MP (@lem1513091 x y z) (@lem1513040 x y z h1)). Qed.
Lemma lem1513094 (n : nat) (m : nat) : (term177 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1513095 : term213 = term214.
Proof. exact (@lem1513094 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1513096 : term214 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1513097 : term213 = False.
Proof. exact (TRANS (@lem1513095) (@lem1513096)). Qed.
Lemma lem1513098 (x : real) (y : real) (z : real) (h1 : term93 x y z) : False.
Proof. exact (EQ_MP (@lem1513097) (@lem1513092 x y z h1)). Qed.
Lemma lem1513099 (x : real) (y : real) (z : real) (h1 : term96 x y z) : False.
Proof. exact (or_elim (@lem1512882 x y z h1) (fun h0 : term77 x y z => @lem1512990 x y z h0) (fun h0 : term93 x y z => @lem1513098 x y z h0)). Qed.
Lemma lem1513101 (x : real) (y : real) (z : real) (h1 : term96 x y z) : term96 x y z.
Proof. exact (h1). Qed.
Lemma lem1513102 (x : real) (y : real) (z : real) (h1 : term96 x y z) : (term96 x y z) = False.
Proof. exact (prop_ext (fun h2 : term96 x y z => @lem1513099 x y z h1) (fun h2 : False => @lem1513101 x y z h1)). Qed.
Lemma lem1513103 (x : real) (y : real) (z : real) (h1 : term96 x y z) : False.
Proof. exact (EQ_MP (@lem1513102 x y z h1) (@lem1513101 x y z h1)). Qed.
Lemma lem1513104 (x : real) (y : real) (h1 : term98 x y) : term98 x y.
Proof. exact (h1). Qed.
Lemma lem1513105 (x : real) (y : real) (h1 : term98 x y) : False.
Proof. exact (ex_elim (@lem1513104 x y h1) (fun z : real => fun h0 : term97 x y z => @lem1513103 x y z h0)). Qed.
Lemma lem1513106 (x : real) (h1 : term100 x) : term100 x.
Proof. exact (h1). Qed.
Lemma lem1513107 (x : real) (h1 : term100 x) : False.
Proof. exact (ex_elim (@lem1513106 x h1) (fun y : real => fun h0 : term99 x y => @lem1513105 x y h0)). Qed.
Lemma lem1513108 (h1 : term102) : term102.
Proof. exact (h1). Qed.
Lemma lem1513109 (h1 : term102) : False.
Proof. exact (ex_elim (@lem1513108 h1) (fun x : real => fun h0 : term101 x => @lem1513107 x h0)). Qed.
Lemma lem1513110 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1513111 (h1 : term23) : term102.
Proof. exact (EQ_MP (@lem1512872) (@lem1513110 h1)). Qed.
Lemma lem1513112 (h1 : term23) : term102 = False.
Proof. exact (prop_ext (fun h2 : term102 => @lem1513109 h2) (fun h2 : False => @lem1513111 h1)). Qed.
Lemma lem1513113 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1513112 h1) (@lem1513111 h1)). Qed.
Lemma lem1513114 : term215.
Proof. exact (fun h0 : term23 => @lem1513113 h0). Qed.
Lemma lem1513115 : term216.
Proof. exact (@lem1386578 term217). Qed.
Lemma lem1513116 : term217.
Proof. exact (@lem1513115 (@lem1513114)). Qed.

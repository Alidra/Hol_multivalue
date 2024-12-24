Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NOT_EQ_term_abbrevs.
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
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
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
Lemma lem1494179 (x : real) (y : real) : (term0 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1494188 (y : real) (x : real) : (term1 y x) = (term2 y x).
Proof. exact (@lem17160 (real_lt x y) (real_lt y x)). Qed.
Lemma lem1494191 (y : real) (x : real) : (term3 y x) = (term3 y x).
Proof. exact (eq_refl (term3 y x)). Qed.
Lemma lem1494192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1494193 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1494192) (@lem1494179 x y)). Qed.
Lemma lem1494194 (y : real) (x : real) : (term6 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem1494193 x y) (@lem1494191 y x)). Qed.
Lemma lem1494196 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1494197 (y : real) (x : real) : (term9 y x) = (term10 y x).
Proof. exact (MK_COMB (@lem1494196 x y) (@lem1494188 y x)). Qed.
Lemma lem1494198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494199 (y : real) (x : real) : (term11 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1494198) (@lem1494197 y x)). Qed.
Lemma lem1494200 (y : real) (x : real) : (term13 y x) = (term14 y x).
Proof. exact (MK_COMB (@lem1494199 y x) (@lem1494194 y x)). Qed.
Lemma lem1494201 (y : real) (x : real) : (term15 y x) = (term13 y x).
Proof. exact (@lem17646 (term16 x y) (term3 y x)). Qed.
Lemma lem1494202 (y : real) (x : real) : (term15 y x) = (term14 y x).
Proof. exact (TRANS (@lem1494201 y x) (@lem1494200 y x)). Qed.
Lemma lem1494203 (P : real -> Prop) : (term17 P) = (term18 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1494204 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1494203 (term21 x)). Qed.
Lemma lem1494205 (y : real) (x : real) : (term22 x y) = ((term16 x y) = (term3 y x)).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1494206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1494207 (y : real) (x : real) : (term23 x y) = (term15 y x).
Proof. exact (MK_COMB (@lem1494206) (@lem1494205 y x)). Qed.
Lemma lem1494208 (y : real) (x : real) : (term23 x y) = (term14 y x).
Proof. exact (TRANS (@lem1494207 y x) (@lem1494202 y x)). Qed.
Lemma lem1494209 (x : real) : (term24 x) = (term25 x).
Proof. exact (fun_ext (fun y : real => @lem1494208 y x)). Qed.
Lemma lem1494210 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494211 (x : real) : (term20 x) = (term26 x).
Proof. exact (MK_COMB (@lem1494210) (@lem1494209 x)). Qed.
Lemma lem1494212 (x : real) : (term19 x) = (term26 x).
Proof. exact (TRANS (@lem1494204 x) (@lem1494211 x)). Qed.
Lemma lem1494213 (P : real -> Prop) : (term17 P) = (term18 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1494214 : term27 = term28.
Proof. exact (@lem1494213 term29). Qed.
Lemma lem1494215 (x : real) : (term30 x) = (term31 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1494216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1494217 (x : real) : (term32 x) = (term19 x).
Proof. exact (MK_COMB (@lem1494216) (@lem1494215 x)). Qed.
Lemma lem1494218 (x : real) : (term32 x) = (term26 x).
Proof. exact (TRANS (@lem1494217 x) (@lem1494212 x)). Qed.
Lemma lem1494219 : term33 = term34.
Proof. exact (fun_ext (fun x : real => @lem1494218 x)). Qed.
Lemma lem1494220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494221 : term28 = term35.
Proof. exact (MK_COMB (@lem1494220) (@lem1494219)). Qed.
Lemma lem1494223 : term27 = term35.
Proof. exact (TRANS (@lem1494214) (@lem1494221)). Qed.
Lemma lem1494250 (y : real) (x : real) : (term14 y x) = (term14 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1494251 (x : real) : (term25 x) = (term25 x).
Proof. exact (fun_ext (fun y : real => @lem1494250 y x)). Qed.
Lemma lem1494252 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494253 (x : real) : (term26 x) = (term26 x).
Proof. exact (MK_COMB (@lem1494252) (@lem1494251 x)). Qed.
Lemma lem1494254 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1494253 x)). Qed.
Lemma lem1494255 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494256 : term35 = term35.
Proof. exact (MK_COMB (@lem1494255) (@lem1494254)). Qed.
Lemma lem1494257 : term27 = term35.
Proof. exact (TRANS (@lem1494223) (@lem1494256)). Qed.
Lemma lem1494258 (x : real) (y : real) : (term16 x y) = (term36 x y).
Proof. exact (@lem1483554 x y). Qed.
Lemma lem1494271 (x : real) (y : real) : (real_sub x y) = (term37 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1494272 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1494273 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1494272) (@lem1494271 x y)). Qed.
Lemma lem1494274 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (@lem1483512 (term37 x y)). Qed.
Lemma lem1494275 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem1483508 x term42 (term43 y)). Qed.
Lemma lem1494276 (y : real) : (term44 y) = (term45 y).
Proof. exact (@lem1483476 term42 term42 y). Qed.
Lemma lem1494278 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1494279 : term48 = term49.
Proof. exact (@lem1494278 term50 term50). Qed.
Lemma lem1494280 : (term51 = (BIT1 0)) = (term52 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1494281 : term52 = term50.
Proof. exact (EQ_MP (@lem1494280) (@lem940073)). Qed.
Lemma lem1494282 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1494283 : term49 = term53.
Proof. exact (MK_COMB (@lem1494282) (@lem1494281)). Qed.
Lemma lem1494284 : term48 = term53.
Proof. exact (TRANS (@lem1494279) (@lem1494283)). Qed.
Lemma lem1494285 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494286 : term54 = term55.
Proof. exact (MK_COMB (@lem1494285) (@lem1494284)). Qed.
Lemma lem1494287 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1494288 (y : real) : (term45 y) = (term56 y).
Proof. exact (MK_COMB (@lem1494286) (@lem1494287 y)). Qed.
Lemma lem1494289 (y : real) : (term44 y) = (term56 y).
Proof. exact (TRANS (@lem1494276 y) (@lem1494288 y)). Qed.
Lemma lem1494290 (y : real) : (term56 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1494291 (y : real) : (term44 y) = y.
Proof. exact (TRANS (@lem1494289 y) (@lem1494290 y)). Qed.
Lemma lem1494294 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1494295 (x : real) (y : real) : (term41 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1494294 x) (@lem1494291 y)). Qed.
Lemma lem1494296 (x : real) (y : real) : (term40 x y) = (term58 x y).
Proof. exact (TRANS (@lem1494275 x y) (@lem1494295 x y)). Qed.
Lemma lem1494297 (x : real) (y : real) : (term39 x y) = (term58 x y).
Proof. exact (TRANS (@lem1494274 x y) (@lem1494296 x y)). Qed.
Lemma lem1494298 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1494299 (x : real) (y : real) : ((term38 x y) = (term39 x y)) = ((term38 x y) = (term58 x y)).
Proof. exact (MK_COMB (@lem1494298 x y) (@lem1494297 x y)). Qed.
Lemma lem1494300 (x : real) (y : real) : (term38 x y) = (term58 x y).
Proof. exact (EQ_MP (@lem1494299 x y) (@lem1494273 x y)). Qed.
Lemma lem1494301 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494302 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1494301) (@lem1494300 x y)). Qed.
Lemma lem1494303 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494304 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1494302 x y) (@lem1494303)). Qed.
Lemma lem1494305 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494306 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1494305) (@lem1494271 x y)). Qed.
Lemma lem1494307 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494308 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1494306 x y) (@lem1494307)). Qed.
Lemma lem1494309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494310 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1494309) (@lem1494308 x y)). Qed.
Lemma lem1494311 (x : real) (y : real) : (term36 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1494310 x y) (@lem1494304 x y)). Qed.
Lemma lem1494312 (x : real) (y : real) : (term16 x y) = (term71 x y).
Proof. exact (TRANS (@lem1494258 x y) (@lem1494311 x y)). Qed.
Lemma lem1494313 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (@lem1483531 x y). Qed.
Lemma lem1494326 (x : real) (y : real) : (real_sub x y) = (term37 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1494327 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1494328 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1494327) (@lem1494326 x y)). Qed.
Lemma lem1494329 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494330 (x : real) (y : real) : (term73 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1494328 x y) (@lem1494329)). Qed.
Lemma lem1494331 (x : real) (y : real) : (term72 x y) = (term76 x y).
Proof. exact (TRANS (@lem1494313 x y) (@lem1494330 x y)). Qed.
Lemma lem1494332 (y : real) (x : real) : (term72 y x) = (term73 y x).
Proof. exact (@lem1483531 y x). Qed.
Lemma lem1494338 (y : real) (x : real) : (real_sub y x) = (term37 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1494343 (x : real) (y : real) : (term37 y x) = (term58 x y).
Proof. exact (@lem1483488 (term43 x) y). Qed.
Lemma lem1494345 (x : real) (y : real) : (real_sub y x) = (term58 x y).
Proof. exact (TRANS (@lem1494338 y x) (@lem1494343 x y)). Qed.
Lemma lem1494346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1494347 (x : real) (y : real) : (term74 y x) = (term77 x y).
Proof. exact (MK_COMB (@lem1494346) (@lem1494345 x y)). Qed.
Lemma lem1494348 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494349 (x : real) (y : real) : (term73 y x) = (term78 x y).
Proof. exact (MK_COMB (@lem1494347 x y) (@lem1494348)). Qed.
Lemma lem1494350 (x : real) (y : real) : (term72 y x) = (term78 x y).
Proof. exact (TRANS (@lem1494332 y x) (@lem1494349 x y)). Qed.
Lemma lem1494351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1494352 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1494351) (@lem1494331 x y)). Qed.
Lemma lem1494353 (x : real) (y : real) : (term2 y x) = (term81 x y).
Proof. exact (MK_COMB (@lem1494352 x y) (@lem1494350 x y)). Qed.
Lemma lem1494354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1494355 (x : real) (y : real) : (term8 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1494354) (@lem1494312 x y)). Qed.
Lemma lem1494356 (x : real) (y : real) : (term10 y x) = (term83 x y).
Proof. exact (MK_COMB (@lem1494355 x y) (@lem1494353 x y)). Qed.
Lemma lem1494357 (x : real) (y : real) : (x = y) = ((real_sub x y) = term62).
Proof. exact (@lem1483529 x y). Qed.
Lemma lem1494370 (x : real) (y : real) : (real_sub x y) = (term37 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1494371 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1494372 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1494371) (@lem1494370 x y)). Qed.
Lemma lem1494373 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494374 (x : real) (y : real) : ((real_sub x y) = term62) = ((term37 x y) = term62).
Proof. exact (MK_COMB (@lem1494372 x y) (@lem1494373)). Qed.
Lemma lem1494375 (x : real) (y : real) : (x = y) = ((term37 x y) = term62).
Proof. exact (TRANS (@lem1494357 x y) (@lem1494374 x y)). Qed.
Lemma lem1494376 (y : real) (x : real) : (real_lt x y) = (term67 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1494382 (y : real) (x : real) : (real_sub y x) = (term37 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1494387 (x : real) (y : real) : (term37 y x) = (term58 x y).
Proof. exact (@lem1483488 (term43 x) y). Qed.
Lemma lem1494389 (x : real) (y : real) : (real_sub y x) = (term58 x y).
Proof. exact (TRANS (@lem1494382 y x) (@lem1494387 x y)). Qed.
Lemma lem1494390 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494391 (x : real) (y : real) : (term65 y x) = (term61 x y).
Proof. exact (MK_COMB (@lem1494390) (@lem1494389 x y)). Qed.
Lemma lem1494392 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494393 (x : real) (y : real) : (term67 y x) = (term64 x y).
Proof. exact (MK_COMB (@lem1494391 x y) (@lem1494392)). Qed.
Lemma lem1494394 (x : real) (y : real) : (real_lt x y) = (term64 x y).
Proof. exact (TRANS (@lem1494376 y x) (@lem1494393 x y)). Qed.
Lemma lem1494395 (x : real) (y : real) : (real_lt y x) = (term67 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1494408 (x : real) (y : real) : (real_sub x y) = (term37 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1494409 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494410 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1494409) (@lem1494408 x y)). Qed.
Lemma lem1494411 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494412 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1494410 x y) (@lem1494411)). Qed.
Lemma lem1494413 (x : real) (y : real) : (real_lt y x) = (term68 x y).
Proof. exact (TRANS (@lem1494395 x y) (@lem1494412 x y)). Qed.
Lemma lem1494414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494415 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1494414) (@lem1494394 x y)). Qed.
Lemma lem1494416 (x : real) (y : real) : (term3 y x) = (term88 x y).
Proof. exact (MK_COMB (@lem1494415 x y) (@lem1494413 x y)). Qed.
Lemma lem1494417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1494418 (x : real) (y : real) : (term5 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1494417) (@lem1494375 x y)). Qed.
Lemma lem1494419 (x : real) (y : real) : (term7 y x) = (term90 x y).
Proof. exact (MK_COMB (@lem1494418 x y) (@lem1494416 x y)). Qed.
Lemma lem1494420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494421 (x : real) (y : real) : (term12 y x) = (term91 x y).
Proof. exact (MK_COMB (@lem1494420) (@lem1494356 x y)). Qed.
Lemma lem1494422 (x : real) (y : real) : (term14 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem1494421 x y) (@lem1494419 x y)). Qed.
Lemma lem1494423 (x : real) : (term25 x) = (term93 x).
Proof. exact (fun_ext (fun y : real => @lem1494422 x y)). Qed.
Lemma lem1494424 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494425 (x : real) : (term26 x) = (term94 x).
Proof. exact (MK_COMB (@lem1494424) (@lem1494423 x)). Qed.
Lemma lem1494426 : term34 = term95.
Proof. exact (fun_ext (fun x : real => @lem1494425 x)). Qed.
Lemma lem1494427 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494428 : term35 = term96.
Proof. exact (MK_COMB (@lem1494427) (@lem1494426)). Qed.
Lemma lem1494429 : term27 = term96.
Proof. exact (TRANS (@lem1494257) (@lem1494428)). Qed.
Lemma lem1494435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1494436 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1494435 real P Q). Qed.
Lemma lem1494437 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1494436 (term103 x) (term104 x)). Qed.
Lemma lem1494438 (x : real) (y : real) : (term105 x y) = (term83 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1494439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494440 (x : real) (y : real) : (term106 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1494439) (@lem1494438 x y)). Qed.
Lemma lem1494441 (x : real) (y : real) : (term107 x y) = (term90 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1494442 (x : real) (y : real) : (term108 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1494440 x y) (@lem1494441 x y)). Qed.
Lemma lem1494443 (x : real) : (term109 x) = (term93 x).
Proof. exact (fun_ext (fun y : real => @lem1494442 x y)). Qed.
Lemma lem1494444 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494445 (x : real) : (term101 x) = (term94 x).
Proof. exact (MK_COMB (@lem1494444) (@lem1494443 x)). Qed.
Lemma lem1494446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1494447 (x : real) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1494446) (@lem1494445 x)). Qed.
Lemma lem1494448 (x : real) (y : real) : (term105 x y) = (term83 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1494449 (x : real) : (term112 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1494448 x y)). Qed.
Lemma lem1494450 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494451 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1494450) (@lem1494449 x)). Qed.
Lemma lem1494452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494453 (x : real) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem1494452) (@lem1494451 x)). Qed.
Lemma lem1494454 (x : real) (y : real) : (term107 x y) = (term90 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1494455 (x : real) : (term117 x) = (term104 x).
Proof. exact (fun_ext (fun y : real => @lem1494454 x y)). Qed.
Lemma lem1494456 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494457 (x : real) : (term118 x) = (term119 x).
Proof. exact (MK_COMB (@lem1494456) (@lem1494455 x)). Qed.
Lemma lem1494458 (x : real) : (term102 x) = (term120 x).
Proof. exact (MK_COMB (@lem1494453 x) (@lem1494457 x)). Qed.
Lemma lem1494459 (x : real) : ((term101 x) = (term102 x)) = ((term94 x) = (term120 x)).
Proof. exact (MK_COMB (@lem1494447 x) (@lem1494458 x)). Qed.
Lemma lem1494460 (x : real) : (term94 x) = (term120 x).
Proof. exact (EQ_MP (@lem1494459 x) (@lem1494437 x)). Qed.
Lemma lem1494557 : term95 = term121.
Proof. exact (fun_ext (fun x : real => @lem1494460 x)). Qed.
Lemma lem1494558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494559 : term96 = term122.
Proof. exact (MK_COMB (@lem1494558) (@lem1494557)). Qed.
Lemma lem1494561 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1494562 (P : real -> Prop) (Q : real -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1494561 real P Q). Qed.
Lemma lem1494563 : term123 = term124.
Proof. exact (@lem1494562 term125 term126). Qed.
Lemma lem1494564 (x : real) : (term127 x) = (term114 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1494565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494566 (x : real) : (term128 x) = (term116 x).
Proof. exact (MK_COMB (@lem1494565) (@lem1494564 x)). Qed.
Lemma lem1494567 (x : real) : (term129 x) = (term119 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1494568 (x : real) : (term130 x) = (term120 x).
Proof. exact (MK_COMB (@lem1494566 x) (@lem1494567 x)). Qed.
Lemma lem1494569 : term131 = term121.
Proof. exact (fun_ext (fun x : real => @lem1494568 x)). Qed.
Lemma lem1494570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494571 : term123 = term122.
Proof. exact (MK_COMB (@lem1494570) (@lem1494569)). Qed.
Lemma lem1494572 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1494573 : term132 = term133.
Proof. exact (MK_COMB (@lem1494572) (@lem1494571)). Qed.
Lemma lem1494574 (x : real) : (term127 x) = (term114 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1494575 : term134 = term125.
Proof. exact (fun_ext (fun x : real => @lem1494574 x)). Qed.
Lemma lem1494576 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494577 : term135 = term136.
Proof. exact (MK_COMB (@lem1494576) (@lem1494575)). Qed.
Lemma lem1494578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494579 : term137 = term138.
Proof. exact (MK_COMB (@lem1494578) (@lem1494577)). Qed.
Lemma lem1494580 (x : real) : (term129 x) = (term119 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1494581 : term139 = term126.
Proof. exact (fun_ext (fun x : real => @lem1494580 x)). Qed.
Lemma lem1494582 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494583 : term140 = term141.
Proof. exact (MK_COMB (@lem1494582) (@lem1494581)). Qed.
Lemma lem1494584 : term124 = term142.
Proof. exact (MK_COMB (@lem1494579) (@lem1494583)). Qed.
Lemma lem1494585 : (term123 = term124) = (term122 = term142).
Proof. exact (MK_COMB (@lem1494573) (@lem1494584)). Qed.
Lemma lem1494586 : term122 = term142.
Proof. exact (EQ_MP (@lem1494585) (@lem1494563)). Qed.
Lemma lem1494691 : term96 = term142.
Proof. exact (TRANS (@lem1494559) (@lem1494586)). Qed.
Lemma lem1494693 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1494694 (P : real -> Prop) (Q : real -> Prop) : (term100 P Q) = (term99 P Q).
Proof. exact (@lem1494693 real P Q). Qed.
Lemma lem1494695 : term124 = term123.
Proof. exact (@lem1494694 term125 term126). Qed.
Lemma lem1494696 (x : real) : (term127 x) = (term114 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1494697 : term134 = term125.
Proof. exact (fun_ext (fun x : real => @lem1494696 x)). Qed.
Lemma lem1494698 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494699 : term135 = term136.
Proof. exact (MK_COMB (@lem1494698) (@lem1494697)). Qed.
Lemma lem1494700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494701 : term137 = term138.
Proof. exact (MK_COMB (@lem1494700) (@lem1494699)). Qed.
Lemma lem1494702 (x : real) : (term129 x) = (term119 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1494703 : term139 = term126.
Proof. exact (fun_ext (fun x : real => @lem1494702 x)). Qed.
Lemma lem1494704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494705 : term140 = term141.
Proof. exact (MK_COMB (@lem1494704) (@lem1494703)). Qed.
Lemma lem1494706 : term124 = term142.
Proof. exact (MK_COMB (@lem1494701) (@lem1494705)). Qed.
Lemma lem1494707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1494708 : term143 = term144.
Proof. exact (MK_COMB (@lem1494707) (@lem1494706)). Qed.
Lemma lem1494709 (x : real) : (term127 x) = (term114 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1494710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494711 (x : real) : (term128 x) = (term116 x).
Proof. exact (MK_COMB (@lem1494710) (@lem1494709 x)). Qed.
Lemma lem1494712 (x : real) : (term129 x) = (term119 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1494713 (x : real) : (term130 x) = (term120 x).
Proof. exact (MK_COMB (@lem1494711 x) (@lem1494712 x)). Qed.
Lemma lem1494714 : term131 = term121.
Proof. exact (fun_ext (fun x : real => @lem1494713 x)). Qed.
Lemma lem1494715 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494716 : term123 = term122.
Proof. exact (MK_COMB (@lem1494715) (@lem1494714)). Qed.
Lemma lem1494717 : (term124 = term123) = (term142 = term122).
Proof. exact (MK_COMB (@lem1494708) (@lem1494716)). Qed.
Lemma lem1494718 : term142 = term122.
Proof. exact (EQ_MP (@lem1494717) (@lem1494695)). Qed.
Lemma lem1494720 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1494721 (P : real -> Prop) (Q : real -> Prop) : (term100 P Q) = (term99 P Q).
Proof. exact (@lem1494720 real P Q). Qed.
Lemma lem1494722 (x : real) : (term102 x) = (term101 x).
Proof. exact (@lem1494721 (term103 x) (term104 x)). Qed.
Lemma lem1494723 (x : real) (y : real) : (term105 x y) = (term83 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1494724 (x : real) : (term112 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1494723 x y)). Qed.
Lemma lem1494725 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494726 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1494725) (@lem1494724 x)). Qed.
Lemma lem1494727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494728 (x : real) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem1494727) (@lem1494726 x)). Qed.
Lemma lem1494729 (x : real) (y : real) : (term107 x y) = (term90 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1494730 (x : real) : (term117 x) = (term104 x).
Proof. exact (fun_ext (fun y : real => @lem1494729 x y)). Qed.
Lemma lem1494731 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494732 (x : real) : (term118 x) = (term119 x).
Proof. exact (MK_COMB (@lem1494731) (@lem1494730 x)). Qed.
Lemma lem1494733 (x : real) : (term102 x) = (term120 x).
Proof. exact (MK_COMB (@lem1494728 x) (@lem1494732 x)). Qed.
Lemma lem1494734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1494735 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1494734) (@lem1494733 x)). Qed.
Lemma lem1494736 (x : real) (y : real) : (term105 x y) = (term83 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1494737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494738 (x : real) (y : real) : (term106 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1494737) (@lem1494736 x y)). Qed.
Lemma lem1494739 (x : real) (y : real) : (term107 x y) = (term90 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1494740 (x : real) (y : real) : (term108 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1494738 x y) (@lem1494739 x y)). Qed.
Lemma lem1494741 (x : real) : (term109 x) = (term93 x).
Proof. exact (fun_ext (fun y : real => @lem1494740 x y)). Qed.
Lemma lem1494742 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494743 (x : real) : (term101 x) = (term94 x).
Proof. exact (MK_COMB (@lem1494742) (@lem1494741 x)). Qed.
Lemma lem1494744 (x : real) : ((term102 x) = (term101 x)) = ((term120 x) = (term94 x)).
Proof. exact (MK_COMB (@lem1494735 x) (@lem1494743 x)). Qed.
Lemma lem1494745 (x : real) : (term120 x) = (term94 x).
Proof. exact (EQ_MP (@lem1494744 x) (@lem1494722 x)). Qed.
Lemma lem1494746 : term121 = term95.
Proof. exact (fun_ext (fun x : real => @lem1494745 x)). Qed.
Lemma lem1494747 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494748 : term122 = term96.
Proof. exact (MK_COMB (@lem1494747) (@lem1494746)). Qed.
Lemma lem1494749 : term142 = term96.
Proof. exact (TRANS (@lem1494718) (@lem1494748)). Qed.
Lemma lem1494750 : term96 = term96.
Proof. exact (TRANS (@lem1494691) (@lem1494749)). Qed.
Lemma lem1494753 : term27 = term96.
Proof. exact (TRANS (@lem1494429) (@lem1494750)). Qed.
Lemma lem1494770 (x : real) (y : real) : (term90 x y) = (term147 x y).
Proof. exact (@lem19158 (term64 x y) ((term37 x y) = term62) (term68 x y)). Qed.
Lemma lem1494793 (x : real) (y : real) : (term83 x y) = (term148 x y).
Proof. exact (@lem19367 (term68 x y) (term64 x y) (term81 x y)). Qed.
Lemma lem1494794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1494795 (x : real) (y : real) : (term91 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1494794) (@lem1494793 x y)). Qed.
Lemma lem1494796 (x : real) (y : real) : (term92 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1494795 x y) (@lem1494770 x y)). Qed.
Lemma lem1494797 (x : real) : (term93 x) = (term151 x).
Proof. exact (fun_ext (fun y : real => @lem1494796 x y)). Qed.
Lemma lem1494798 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494799 (x : real) : (term94 x) = (term152 x).
Proof. exact (MK_COMB (@lem1494798) (@lem1494797 x)). Qed.
Lemma lem1494800 : term95 = term153.
Proof. exact (fun_ext (fun x : real => @lem1494799 x)). Qed.
Lemma lem1494801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494802 : term96 = term154.
Proof. exact (MK_COMB (@lem1494801) (@lem1494800)). Qed.
Lemma lem1494803 : term27 = term154.
Proof. exact (TRANS (@lem1494753) (@lem1494802)). Qed.
Lemma lem1494825 (x : real) (y : real) (h1 : term150 x y) : term150 x y.
Proof. exact (h1). Qed.
Lemma lem1494826 (x : real) (y : real) (h1 : term148 x y) : term148 x y.
Proof. exact (h1). Qed.
Lemma lem1494827 (x : real) (y : real) (h1 : term155 x y) : term155 x y.
Proof. exact (h1). Qed.
Lemma lem1494828 (x : real) (y : real) (h1 : term155 x y) : term81 x y.
Proof. exact (proj2 (@lem1494827 x y h1)). Qed.
Lemma lem1494829 (x : real) (y : real) (h1 : term155 x y) : term68 x y.
Proof. exact (proj1 (@lem1494827 x y h1)). Qed.
Lemma lem1494830 (x : real) (y : real) (h1 : term155 x y) : term78 x y.
Proof. exact (proj2 (@lem1494828 x y h1)). Qed.
Lemma lem1494833 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494834 : term157 = term158.
Proof. exact (@lem1494833 (NUMERAL 0) term50). Qed.
Lemma lem1494835 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494836 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494837 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1494836 h1) (fun h1 : term158 = True => @lem1494835)). Qed.
Lemma lem1494838 : term158 = True.
Proof. exact (EQ_MP (@lem1494837) (@lem1494835)). Qed.
Lemma lem1494839 : term157 = True.
Proof. exact (TRANS (@lem1494834) (@lem1494838)). Qed.
Lemma lem1494840 : True = term157.
Proof. exact (SYM (@lem1494839)). Qed.
Lemma lem1494841 : term157.
Proof. exact (EQ_MP (@lem1494840) (@lem0)). Qed.
Lemma lem1494842 (x : real) (y : real) (h1 : term155 x y) : term160 x y.
Proof. exact (conj (@lem1494841) (@lem1494830 x y h1)). Qed.
Lemma lem1494844 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1494845 (x : real) (y : real) : term162 x y.
Proof. exact (@lem1494844 term53 (term58 x y)). Qed.
Lemma lem1494846 (x : real) (y : real) (h1 : term155 x y) : term163 x y.
Proof. exact (@lem1494845 x y (@lem1494842 x y h1)). Qed.
Lemma lem1494847 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (@lem1483460 (term58 x y)). Qed.
Lemma lem1494848 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1494849 (x : real) (y : real) : (term165 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1494848) (@lem1494847 x y)). Qed.
Lemma lem1494850 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494851 (x : real) (y : real) : (term163 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1494849 x y) (@lem1494850)). Qed.
Lemma lem1494852 (x : real) (y : real) (h1 : term155 x y) : term78 x y.
Proof. exact (EQ_MP (@lem1494851 x y) (@lem1494846 x y h1)). Qed.
Lemma lem1494854 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494855 : term157 = term158.
Proof. exact (@lem1494854 (NUMERAL 0) term50). Qed.
Lemma lem1494856 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494857 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494858 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1494857 h1) (fun h1 : term158 = True => @lem1494856)). Qed.
Lemma lem1494859 : term158 = True.
Proof. exact (EQ_MP (@lem1494858) (@lem1494856)). Qed.
Lemma lem1494860 : term157 = True.
Proof. exact (TRANS (@lem1494855) (@lem1494859)). Qed.
Lemma lem1494861 : True = term157.
Proof. exact (SYM (@lem1494860)). Qed.
Lemma lem1494862 : term157.
Proof. exact (EQ_MP (@lem1494861) (@lem0)). Qed.
Lemma lem1494863 (x : real) (y : real) (h1 : term155 x y) : term166 x y.
Proof. exact (conj (@lem1494862) (@lem1494829 x y h1)). Qed.
Lemma lem1494865 (x : real) (y : real) : term167 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1494866 (x : real) (y : real) : term168 x y.
Proof. exact (@lem1494865 term53 (term37 x y)). Qed.
Lemma lem1494867 (x : real) (y : real) (h1 : term155 x y) : term169 x y.
Proof. exact (@lem1494866 x y (@lem1494863 x y h1)). Qed.
Lemma lem1494868 (x : real) (y : real) : (term170 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1494869 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494870 (x : real) (y : real) : (term171 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1494869) (@lem1494868 x y)). Qed.
Lemma lem1494871 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494872 (x : real) (y : real) : (term169 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1494870 x y) (@lem1494871)). Qed.
Lemma lem1494873 (x : real) (y : real) (h1 : term155 x y) : term68 x y.
Proof. exact (EQ_MP (@lem1494872 x y) (@lem1494867 x y h1)). Qed.
Lemma lem1494874 (x : real) (y : real) (h1 : term155 x y) : term172 x y.
Proof. exact (conj (@lem1494873 x y h1) (@lem1494852 x y h1)). Qed.
Lemma lem1494876 (x : real) (y : real) : term173 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1494877 (x : real) (y : real) : term174 x y.
Proof. exact (@lem1494876 (term37 x y) (term58 x y)). Qed.
Lemma lem1494878 (x : real) (y : real) (h1 : term155 x y) : term175 x y.
Proof. exact (@lem1494877 x y (@lem1494874 x y h1)). Qed.
Lemma lem1494879 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (@lem1483480 x (term43 x) (term43 y) y). Qed.
Lemma lem1494880 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem1483442 term42 x). Qed.
Lemma lem1494882 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494883 : term181 = term62.
Proof. exact (@lem1494882 term50). Qed.
Lemma lem1494884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494885 : term182 = term183.
Proof. exact (MK_COMB (@lem1494884) (@lem1494883)). Qed.
Lemma lem1494886 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1494887 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1494885) (@lem1494886 x)). Qed.
Lemma lem1494888 (x : real) : (term178 x) = (term184 x).
Proof. exact (TRANS (@lem1494880 x) (@lem1494887 x)). Qed.
Lemma lem1494889 (x : real) : (term184 x) = term62.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1494890 (x : real) : (term178 x) = term62.
Proof. exact (TRANS (@lem1494888 x) (@lem1494889 x)). Qed.
Lemma lem1494891 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1494892 (x : real) : (term185 x) = term186.
Proof. exact (MK_COMB (@lem1494891) (@lem1494890 x)). Qed.
Lemma lem1494893 (y : real) : (term187 y) = (term179 y).
Proof. exact (@lem1483440 term42 y). Qed.
Lemma lem1494895 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494896 : term181 = term62.
Proof. exact (@lem1494895 term50). Qed.
Lemma lem1494897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494898 : term182 = term183.
Proof. exact (MK_COMB (@lem1494897) (@lem1494896)). Qed.
Lemma lem1494899 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1494900 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1494898) (@lem1494899 y)). Qed.
Lemma lem1494901 (y : real) : (term187 y) = (term184 y).
Proof. exact (TRANS (@lem1494893 y) (@lem1494900 y)). Qed.
Lemma lem1494902 (y : real) : (term184 y) = term62.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1494903 (y : real) : (term187 y) = term62.
Proof. exact (TRANS (@lem1494901 y) (@lem1494902 y)). Qed.
Lemma lem1494904 (x : real) (y : real) : (term177 x y) = term188.
Proof. exact (MK_COMB (@lem1494892 x) (@lem1494903 y)). Qed.
Lemma lem1494905 (x : real) (y : real) : (term176 x y) = term188.
Proof. exact (TRANS (@lem1494879 x y) (@lem1494904 x y)). Qed.
Lemma lem1494906 : term188 = term62.
Proof. exact (@lem1483448 term62). Qed.
Lemma lem1494907 (x : real) (y : real) : (term176 x y) = term62.
Proof. exact (TRANS (@lem1494905 x y) (@lem1494906)). Qed.
Lemma lem1494908 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494909 (x : real) (y : real) : (term189 x y) = term190.
Proof. exact (MK_COMB (@lem1494908) (@lem1494907 x y)). Qed.
Lemma lem1494910 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494911 (x : real) (y : real) : (term175 x y) = term191.
Proof. exact (MK_COMB (@lem1494909 x y) (@lem1494910)). Qed.
Lemma lem1494912 (x : real) (y : real) (h1 : term155 x y) : term191.
Proof. exact (EQ_MP (@lem1494911 x y) (@lem1494878 x y h1)). Qed.
Lemma lem1494914 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494915 : term191 = term192.
Proof. exact (@lem1494914 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1494916 : term192 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1494917 : term191 = False.
Proof. exact (TRANS (@lem1494915) (@lem1494916)). Qed.
Lemma lem1494918 (x : real) (y : real) (h1 : term155 x y) : False.
Proof. exact (EQ_MP (@lem1494917) (@lem1494912 x y h1)). Qed.
Lemma lem1494919 (x : real) (y : real) (h1 : term193 x y) : term193 x y.
Proof. exact (h1). Qed.
Lemma lem1494920 (x : real) (y : real) (h1 : term193 x y) : term81 x y.
Proof. exact (proj2 (@lem1494919 x y h1)). Qed.
Lemma lem1494921 (x : real) (y : real) (h1 : term193 x y) : term64 x y.
Proof. exact (proj1 (@lem1494919 x y h1)). Qed.
Lemma lem1494923 (x : real) (y : real) (h1 : term193 x y) : term76 x y.
Proof. exact (proj1 (@lem1494920 x y h1)). Qed.
Lemma lem1494925 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494926 : term157 = term158.
Proof. exact (@lem1494925 (NUMERAL 0) term50). Qed.
Lemma lem1494927 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494928 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494929 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1494928 h1) (fun h1 : term158 = True => @lem1494927)). Qed.
Lemma lem1494930 : term158 = True.
Proof. exact (EQ_MP (@lem1494929) (@lem1494927)). Qed.
Lemma lem1494931 : term157 = True.
Proof. exact (TRANS (@lem1494926) (@lem1494930)). Qed.
Lemma lem1494932 : True = term157.
Proof. exact (SYM (@lem1494931)). Qed.
Lemma lem1494933 : term157.
Proof. exact (EQ_MP (@lem1494932) (@lem0)). Qed.
Lemma lem1494934 (x : real) (y : real) (h1 : term193 x y) : term194 x y.
Proof. exact (conj (@lem1494933) (@lem1494923 x y h1)). Qed.
Lemma lem1494936 (x : real) (y : real) : term161 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1494937 (x : real) (y : real) : term195 x y.
Proof. exact (@lem1494936 term53 (term37 x y)). Qed.
Lemma lem1494938 (x : real) (y : real) (h1 : term193 x y) : term196 x y.
Proof. exact (@lem1494937 x y (@lem1494934 x y h1)). Qed.
Lemma lem1494939 (x : real) (y : real) : (term170 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1494940 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1494941 (x : real) (y : real) : (term197 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1494940) (@lem1494939 x y)). Qed.
Lemma lem1494942 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494943 (x : real) (y : real) : (term196 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1494941 x y) (@lem1494942)). Qed.
Lemma lem1494944 (x : real) (y : real) (h1 : term193 x y) : term76 x y.
Proof. exact (EQ_MP (@lem1494943 x y) (@lem1494938 x y h1)). Qed.
Lemma lem1494946 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494947 : term157 = term158.
Proof. exact (@lem1494946 (NUMERAL 0) term50). Qed.
Lemma lem1494948 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494949 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494950 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1494949 h1) (fun h1 : term158 = True => @lem1494948)). Qed.
Lemma lem1494951 : term158 = True.
Proof. exact (EQ_MP (@lem1494950) (@lem1494948)). Qed.
Lemma lem1494952 : term157 = True.
Proof. exact (TRANS (@lem1494947) (@lem1494951)). Qed.
Lemma lem1494953 : True = term157.
Proof. exact (SYM (@lem1494952)). Qed.
Lemma lem1494954 : term157.
Proof. exact (EQ_MP (@lem1494953) (@lem0)). Qed.
Lemma lem1494955 (x : real) (y : real) (h1 : term193 x y) : term198 x y.
Proof. exact (conj (@lem1494954) (@lem1494921 x y h1)). Qed.
Lemma lem1494957 (x : real) (y : real) : term167 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1494958 (x : real) (y : real) : term199 x y.
Proof. exact (@lem1494957 term53 (term58 x y)). Qed.
Lemma lem1494959 (x : real) (y : real) (h1 : term193 x y) : term200 x y.
Proof. exact (@lem1494958 x y (@lem1494955 x y h1)). Qed.
Lemma lem1494960 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (@lem1483460 (term58 x y)). Qed.
Lemma lem1494961 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494962 (x : real) (y : real) : (term201 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1494961) (@lem1494960 x y)). Qed.
Lemma lem1494963 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1494964 (x : real) (y : real) : (term200 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1494962 x y) (@lem1494963)). Qed.
Lemma lem1494965 (x : real) (y : real) (h1 : term193 x y) : term64 x y.
Proof. exact (EQ_MP (@lem1494964 x y) (@lem1494959 x y h1)). Qed.
Lemma lem1494966 (x : real) (y : real) (h1 : term193 x y) : term202 x y.
Proof. exact (conj (@lem1494965 x y h1) (@lem1494944 x y h1)). Qed.
Lemma lem1494968 (x : real) (y : real) : term173 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1494969 (x : real) (y : real) : term203 x y.
Proof. exact (@lem1494968 (term58 x y) (term37 x y)). Qed.
Lemma lem1494970 (x : real) (y : real) (h1 : term193 x y) : term204 x y.
Proof. exact (@lem1494969 x y (@lem1494966 x y h1)). Qed.
Lemma lem1494971 (x : real) (y : real) : (term205 x y) = (term206 x y).
Proof. exact (@lem1483480 (term43 x) x y (term43 y)). Qed.
Lemma lem1494972 (x : real) : (term187 x) = (term179 x).
Proof. exact (@lem1483440 term42 x). Qed.
Lemma lem1494974 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494975 : term181 = term62.
Proof. exact (@lem1494974 term50). Qed.
Lemma lem1494976 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494977 : term182 = term183.
Proof. exact (MK_COMB (@lem1494976) (@lem1494975)). Qed.
Lemma lem1494978 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1494979 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1494977) (@lem1494978 x)). Qed.
Lemma lem1494980 (x : real) : (term187 x) = (term184 x).
Proof. exact (TRANS (@lem1494972 x) (@lem1494979 x)). Qed.
Lemma lem1494981 (x : real) : (term184 x) = term62.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1494982 (x : real) : (term187 x) = term62.
Proof. exact (TRANS (@lem1494980 x) (@lem1494981 x)). Qed.
Lemma lem1494983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1494984 (x : real) : (term207 x) = term186.
Proof. exact (MK_COMB (@lem1494983) (@lem1494982 x)). Qed.
Lemma lem1494985 (y : real) : (term178 y) = (term179 y).
Proof. exact (@lem1483442 term42 y). Qed.
Lemma lem1494987 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494988 : term181 = term62.
Proof. exact (@lem1494987 term50). Qed.
Lemma lem1494989 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494990 : term182 = term183.
Proof. exact (MK_COMB (@lem1494989) (@lem1494988)). Qed.
Lemma lem1494991 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1494992 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1494990) (@lem1494991 y)). Qed.
Lemma lem1494993 (y : real) : (term178 y) = (term184 y).
Proof. exact (TRANS (@lem1494985 y) (@lem1494992 y)). Qed.
Lemma lem1494994 (y : real) : (term184 y) = term62.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1494995 (y : real) : (term178 y) = term62.
Proof. exact (TRANS (@lem1494993 y) (@lem1494994 y)). Qed.
Lemma lem1494996 (x : real) (y : real) : (term206 x y) = term188.
Proof. exact (MK_COMB (@lem1494984 x) (@lem1494995 y)). Qed.
Lemma lem1494997 (x : real) (y : real) : (term205 x y) = term188.
Proof. exact (TRANS (@lem1494971 x y) (@lem1494996 x y)). Qed.
Lemma lem1494998 : term188 = term62.
Proof. exact (@lem1483448 term62). Qed.
Lemma lem1494999 (x : real) (y : real) : (term205 x y) = term62.
Proof. exact (TRANS (@lem1494997 x y) (@lem1494998)). Qed.
Lemma lem1495000 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495001 (x : real) (y : real) : (term208 x y) = term190.
Proof. exact (MK_COMB (@lem1495000) (@lem1494999 x y)). Qed.
Lemma lem1495002 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495003 (x : real) (y : real) : (term204 x y) = term191.
Proof. exact (MK_COMB (@lem1495001 x y) (@lem1495002)). Qed.
Lemma lem1495004 (x : real) (y : real) (h1 : term193 x y) : term191.
Proof. exact (EQ_MP (@lem1495003 x y) (@lem1494970 x y h1)). Qed.
Lemma lem1495006 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495007 : term191 = term192.
Proof. exact (@lem1495006 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1495008 : term192 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1495009 : term191 = False.
Proof. exact (TRANS (@lem1495007) (@lem1495008)). Qed.
Lemma lem1495010 (x : real) (y : real) (h1 : term193 x y) : False.
Proof. exact (EQ_MP (@lem1495009) (@lem1495004 x y h1)). Qed.
Lemma lem1495011 (x : real) (y : real) (h1 : term148 x y) : False.
Proof. exact (or_elim (@lem1494826 x y h1) (fun h0 : term155 x y => @lem1494918 x y h0) (fun h0 : term193 x y => @lem1495010 x y h0)). Qed.
Lemma lem1495012 (x : real) (y : real) (h1 : term147 x y) : term147 x y.
Proof. exact (h1). Qed.
Lemma lem1495013 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (h1). Qed.
Lemma lem1495014 (x : real) (y : real) (h1 : term209 x y) : term64 x y.
Proof. exact (proj2 (@lem1495013 x y h1)). Qed.
Lemma lem1495015 (x : real) (y : real) (h1 : term209 x y) : (term37 x y) = term62.
Proof. exact (proj1 (@lem1495013 x y h1)). Qed.
Lemma lem1495017 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495018 : term157 = term158.
Proof. exact (@lem1495017 (NUMERAL 0) term50). Qed.
Lemma lem1495019 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495020 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495021 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1495020 h1) (fun h1 : term158 = True => @lem1495019)). Qed.
Lemma lem1495022 : term158 = True.
Proof. exact (EQ_MP (@lem1495021) (@lem1495019)). Qed.
Lemma lem1495023 : term157 = True.
Proof. exact (TRANS (@lem1495018) (@lem1495022)). Qed.
Lemma lem1495024 : True = term157.
Proof. exact (SYM (@lem1495023)). Qed.
Lemma lem1495025 : term157.
Proof. exact (EQ_MP (@lem1495024) (@lem0)). Qed.
Lemma lem1495026 (x : real) (y : real) (h1 : term209 x y) : term198 x y.
Proof. exact (conj (@lem1495025) (@lem1495014 x y h1)). Qed.
Lemma lem1495028 (x : real) (y : real) : term167 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1495029 (x : real) (y : real) : term199 x y.
Proof. exact (@lem1495028 term53 (term58 x y)). Qed.
Lemma lem1495030 (x : real) (y : real) (h1 : term209 x y) : term200 x y.
Proof. exact (@lem1495029 x y (@lem1495026 x y h1)). Qed.
Lemma lem1495031 (x : real) (y : real) : (term164 x y) = (term58 x y).
Proof. exact (@lem1483460 (term58 x y)). Qed.
Lemma lem1495032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495033 (x : real) (y : real) : (term201 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1495032) (@lem1495031 x y)). Qed.
Lemma lem1495034 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495035 (x : real) (y : real) : (term200 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1495033 x y) (@lem1495034)). Qed.
Lemma lem1495036 (x : real) (y : real) (h1 : term209 x y) : term64 x y.
Proof. exact (EQ_MP (@lem1495035 x y) (@lem1495030 x y h1)). Qed.
Lemma lem1495038 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1495039 (x : real) (y : real) : term211 x y.
Proof. exact (@lem1495038 (term37 x y)). Qed.
Lemma lem1495040 (x : real) (y : real) (h1 : term209 x y) : term212 x y.
Proof. exact (@lem1495039 x y (@lem1495015 x y h1)). Qed.
Lemma lem1495041 (x : real) (y : real) (h1 : term209 x y) : term213 x y.
Proof. exact (@lem1495040 x y h1 term53). Qed.
Lemma lem1495042 (x : real) (y : real) : (term213 x y) = ((term170 x y) = term62).
Proof. exact (eq_refl (term213 x y)). Qed.
Lemma lem1495043 (x : real) (y : real) (h1 : term209 x y) : (term170 x y) = term62.
Proof. exact (EQ_MP (@lem1495042 x y) (@lem1495041 x y h1)). Qed.
Lemma lem1495044 (x : real) (y : real) : (term170 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1495045 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1495046 (x : real) (y : real) : (term214 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1495045) (@lem1495044 x y)). Qed.
Lemma lem1495047 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495048 (x : real) (y : real) : ((term170 x y) = term62) = ((term37 x y) = term62).
Proof. exact (MK_COMB (@lem1495046 x y) (@lem1495047)). Qed.
Lemma lem1495049 (x : real) (y : real) (h1 : term209 x y) : (term37 x y) = term62.
Proof. exact (EQ_MP (@lem1495048 x y) (@lem1495043 x y h1)). Qed.
Lemma lem1495050 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (conj (@lem1495049 x y h1) (@lem1495036 x y h1)). Qed.
Lemma lem1495052 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1495053 (x : real) (y : real) : term216 x y.
Proof. exact (@lem1495052 (term37 x y) (term58 x y)). Qed.
Lemma lem1495054 (x : real) (y : real) (h1 : term209 x y) : term175 x y.
Proof. exact (@lem1495053 x y (@lem1495050 x y h1)). Qed.
Lemma lem1495055 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (@lem1483480 x (term43 x) (term43 y) y). Qed.
Lemma lem1495056 (x : real) : (term178 x) = (term179 x).
Proof. exact (@lem1483442 term42 x). Qed.
Lemma lem1495058 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495059 : term181 = term62.
Proof. exact (@lem1495058 term50). Qed.
Lemma lem1495060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495061 : term182 = term183.
Proof. exact (MK_COMB (@lem1495060) (@lem1495059)). Qed.
Lemma lem1495062 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1495063 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1495061) (@lem1495062 x)). Qed.
Lemma lem1495064 (x : real) : (term178 x) = (term184 x).
Proof. exact (TRANS (@lem1495056 x) (@lem1495063 x)). Qed.
Lemma lem1495065 (x : real) : (term184 x) = term62.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1495066 (x : real) : (term178 x) = term62.
Proof. exact (TRANS (@lem1495064 x) (@lem1495065 x)). Qed.
Lemma lem1495067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1495068 (x : real) : (term185 x) = term186.
Proof. exact (MK_COMB (@lem1495067) (@lem1495066 x)). Qed.
Lemma lem1495069 (y : real) : (term187 y) = (term179 y).
Proof. exact (@lem1483440 term42 y). Qed.
Lemma lem1495071 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495072 : term181 = term62.
Proof. exact (@lem1495071 term50). Qed.
Lemma lem1495073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495074 : term182 = term183.
Proof. exact (MK_COMB (@lem1495073) (@lem1495072)). Qed.
Lemma lem1495075 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1495076 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1495074) (@lem1495075 y)). Qed.
Lemma lem1495077 (y : real) : (term187 y) = (term184 y).
Proof. exact (TRANS (@lem1495069 y) (@lem1495076 y)). Qed.
Lemma lem1495078 (y : real) : (term184 y) = term62.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1495079 (y : real) : (term187 y) = term62.
Proof. exact (TRANS (@lem1495077 y) (@lem1495078 y)). Qed.
Lemma lem1495080 (x : real) (y : real) : (term177 x y) = term188.
Proof. exact (MK_COMB (@lem1495068 x) (@lem1495079 y)). Qed.
Lemma lem1495081 (x : real) (y : real) : (term176 x y) = term188.
Proof. exact (TRANS (@lem1495055 x y) (@lem1495080 x y)). Qed.
Lemma lem1495082 : term188 = term62.
Proof. exact (@lem1483448 term62). Qed.
Lemma lem1495083 (x : real) (y : real) : (term176 x y) = term62.
Proof. exact (TRANS (@lem1495081 x y) (@lem1495082)). Qed.
Lemma lem1495084 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495085 (x : real) (y : real) : (term189 x y) = term190.
Proof. exact (MK_COMB (@lem1495084) (@lem1495083 x y)). Qed.
Lemma lem1495086 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495087 (x : real) (y : real) : (term175 x y) = term191.
Proof. exact (MK_COMB (@lem1495085 x y) (@lem1495086)). Qed.
Lemma lem1495088 (x : real) (y : real) (h1 : term209 x y) : term191.
Proof. exact (EQ_MP (@lem1495087 x y) (@lem1495054 x y h1)). Qed.
Lemma lem1495090 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495091 : term191 = term192.
Proof. exact (@lem1495090 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1495092 : term192 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1495093 : term191 = False.
Proof. exact (TRANS (@lem1495091) (@lem1495092)). Qed.
Lemma lem1495094 (x : real) (y : real) (h1 : term209 x y) : False.
Proof. exact (EQ_MP (@lem1495093) (@lem1495088 x y h1)). Qed.
Lemma lem1495095 (x : real) (y : real) (h1 : term217 x y) : term217 x y.
Proof. exact (h1). Qed.
Lemma lem1495096 (x : real) (y : real) (h1 : term217 x y) : term68 x y.
Proof. exact (proj2 (@lem1495095 x y h1)). Qed.
Lemma lem1495097 (x : real) (y : real) (h1 : term217 x y) : (term37 x y) = term62.
Proof. exact (proj1 (@lem1495095 x y h1)). Qed.
Lemma lem1495099 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495100 : term157 = term158.
Proof. exact (@lem1495099 (NUMERAL 0) term50). Qed.
Lemma lem1495101 : term159 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495102 (h1 : term159 = (BIT1 0)) : term158 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495103 : (term159 = (BIT1 0)) = (term158 = True).
Proof. exact (prop_ext (fun h1 : term159 = (BIT1 0) => @lem1495102 h1) (fun h1 : term158 = True => @lem1495101)). Qed.
Lemma lem1495104 : term158 = True.
Proof. exact (EQ_MP (@lem1495103) (@lem1495101)). Qed.
Lemma lem1495105 : term157 = True.
Proof. exact (TRANS (@lem1495100) (@lem1495104)). Qed.
Lemma lem1495106 : True = term157.
Proof. exact (SYM (@lem1495105)). Qed.
Lemma lem1495107 : term157.
Proof. exact (EQ_MP (@lem1495106) (@lem0)). Qed.
Lemma lem1495108 (x : real) (y : real) (h1 : term217 x y) : term166 x y.
Proof. exact (conj (@lem1495107) (@lem1495096 x y h1)). Qed.
Lemma lem1495110 (x : real) (y : real) : term167 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1495111 (x : real) (y : real) : term168 x y.
Proof. exact (@lem1495110 term53 (term37 x y)). Qed.
Lemma lem1495112 (x : real) (y : real) (h1 : term217 x y) : term169 x y.
Proof. exact (@lem1495111 x y (@lem1495108 x y h1)). Qed.
Lemma lem1495113 (x : real) (y : real) : (term170 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1495114 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495115 (x : real) (y : real) : (term171 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1495114) (@lem1495113 x y)). Qed.
Lemma lem1495116 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495117 (x : real) (y : real) : (term169 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1495115 x y) (@lem1495116)). Qed.
Lemma lem1495118 (x : real) (y : real) (h1 : term217 x y) : term68 x y.
Proof. exact (EQ_MP (@lem1495117 x y) (@lem1495112 x y h1)). Qed.
Lemma lem1495120 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1495121 (x : real) (y : real) : term211 x y.
Proof. exact (@lem1495120 (term37 x y)). Qed.
Lemma lem1495122 (x : real) (y : real) (h1 : term217 x y) : term212 x y.
Proof. exact (@lem1495121 x y (@lem1495097 x y h1)). Qed.
Lemma lem1495123 (x : real) (y : real) (h1 : term217 x y) : term218 x y.
Proof. exact (@lem1495122 x y h1 term42). Qed.
Lemma lem1495124 (x : real) (y : real) : (term218 x y) = ((term40 x y) = term62).
Proof. exact (eq_refl (term218 x y)). Qed.
Lemma lem1495125 (x : real) (y : real) (h1 : term217 x y) : (term40 x y) = term62.
Proof. exact (EQ_MP (@lem1495124 x y) (@lem1495123 x y h1)). Qed.
Lemma lem1495126 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem1483508 x term42 (term43 y)). Qed.
Lemma lem1495127 (y : real) : (term44 y) = (term45 y).
Proof. exact (@lem1483476 term42 term42 y). Qed.
Lemma lem1495129 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1495130 : term48 = term49.
Proof. exact (@lem1495129 term50 term50). Qed.
Lemma lem1495131 : (term51 = (BIT1 0)) = (term52 = term50).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1495132 : term52 = term50.
Proof. exact (EQ_MP (@lem1495131) (@lem940073)). Qed.
Lemma lem1495133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1495134 : term49 = term53.
Proof. exact (MK_COMB (@lem1495133) (@lem1495132)). Qed.
Lemma lem1495135 : term48 = term53.
Proof. exact (TRANS (@lem1495130) (@lem1495134)). Qed.
Lemma lem1495136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495137 : term54 = term55.
Proof. exact (MK_COMB (@lem1495136) (@lem1495135)). Qed.
Lemma lem1495138 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1495139 (y : real) : (term45 y) = (term56 y).
Proof. exact (MK_COMB (@lem1495137) (@lem1495138 y)). Qed.
Lemma lem1495140 (y : real) : (term44 y) = (term56 y).
Proof. exact (TRANS (@lem1495127 y) (@lem1495139 y)). Qed.
Lemma lem1495141 (y : real) : (term56 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1495142 (y : real) : (term44 y) = y.
Proof. exact (TRANS (@lem1495140 y) (@lem1495141 y)). Qed.
Lemma lem1495145 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1495146 (x : real) (y : real) : (term41 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1495145 x) (@lem1495142 y)). Qed.
Lemma lem1495147 (x : real) (y : real) : (term40 x y) = (term58 x y).
Proof. exact (TRANS (@lem1495126 x y) (@lem1495146 x y)). Qed.
Lemma lem1495148 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1495149 (x : real) (y : real) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1495148) (@lem1495147 x y)). Qed.
Lemma lem1495150 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495151 (x : real) (y : real) : ((term40 x y) = term62) = ((term58 x y) = term62).
Proof. exact (MK_COMB (@lem1495149 x y) (@lem1495150)). Qed.
Lemma lem1495152 (x : real) (y : real) (h1 : term217 x y) : (term58 x y) = term62.
Proof. exact (EQ_MP (@lem1495151 x y) (@lem1495125 x y h1)). Qed.
Lemma lem1495153 (x : real) (y : real) (h1 : term217 x y) : term221 x y.
Proof. exact (conj (@lem1495152 x y h1) (@lem1495118 x y h1)). Qed.
Lemma lem1495155 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1495156 (x : real) (y : real) : term222 x y.
Proof. exact (@lem1495155 (term58 x y) (term37 x y)). Qed.
Lemma lem1495157 (x : real) (y : real) (h1 : term217 x y) : term204 x y.
Proof. exact (@lem1495156 x y (@lem1495153 x y h1)). Qed.
Lemma lem1495158 (x : real) (y : real) : (term205 x y) = (term206 x y).
Proof. exact (@lem1483480 (term43 x) x y (term43 y)). Qed.
Lemma lem1495159 (x : real) : (term187 x) = (term179 x).
Proof. exact (@lem1483440 term42 x). Qed.
Lemma lem1495161 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495162 : term181 = term62.
Proof. exact (@lem1495161 term50). Qed.
Lemma lem1495163 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495164 : term182 = term183.
Proof. exact (MK_COMB (@lem1495163) (@lem1495162)). Qed.
Lemma lem1495165 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1495166 (x : real) : (term179 x) = (term184 x).
Proof. exact (MK_COMB (@lem1495164) (@lem1495165 x)). Qed.
Lemma lem1495167 (x : real) : (term187 x) = (term184 x).
Proof. exact (TRANS (@lem1495159 x) (@lem1495166 x)). Qed.
Lemma lem1495168 (x : real) : (term184 x) = term62.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1495169 (x : real) : (term187 x) = term62.
Proof. exact (TRANS (@lem1495167 x) (@lem1495168 x)). Qed.
Lemma lem1495170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1495171 (x : real) : (term207 x) = term186.
Proof. exact (MK_COMB (@lem1495170) (@lem1495169 x)). Qed.
Lemma lem1495172 (y : real) : (term178 y) = (term179 y).
Proof. exact (@lem1483442 term42 y). Qed.
Lemma lem1495174 (m : nat) : (term180 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495175 : term181 = term62.
Proof. exact (@lem1495174 term50). Qed.
Lemma lem1495176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495177 : term182 = term183.
Proof. exact (MK_COMB (@lem1495176) (@lem1495175)). Qed.
Lemma lem1495178 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1495179 (y : real) : (term179 y) = (term184 y).
Proof. exact (MK_COMB (@lem1495177) (@lem1495178 y)). Qed.
Lemma lem1495180 (y : real) : (term178 y) = (term184 y).
Proof. exact (TRANS (@lem1495172 y) (@lem1495179 y)). Qed.
Lemma lem1495181 (y : real) : (term184 y) = term62.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1495182 (y : real) : (term178 y) = term62.
Proof. exact (TRANS (@lem1495180 y) (@lem1495181 y)). Qed.
Lemma lem1495183 (x : real) (y : real) : (term206 x y) = term188.
Proof. exact (MK_COMB (@lem1495171 x) (@lem1495182 y)). Qed.
Lemma lem1495184 (x : real) (y : real) : (term205 x y) = term188.
Proof. exact (TRANS (@lem1495158 x y) (@lem1495183 x y)). Qed.
Lemma lem1495185 : term188 = term62.
Proof. exact (@lem1483448 term62). Qed.
Lemma lem1495186 (x : real) (y : real) : (term205 x y) = term62.
Proof. exact (TRANS (@lem1495184 x y) (@lem1495185)). Qed.
Lemma lem1495187 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495188 (x : real) (y : real) : (term208 x y) = term190.
Proof. exact (MK_COMB (@lem1495187) (@lem1495186 x y)). Qed.
Lemma lem1495189 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1495190 (x : real) (y : real) : (term204 x y) = term191.
Proof. exact (MK_COMB (@lem1495188 x y) (@lem1495189)). Qed.
Lemma lem1495191 (x : real) (y : real) (h1 : term217 x y) : term191.
Proof. exact (EQ_MP (@lem1495190 x y) (@lem1495157 x y h1)). Qed.
Lemma lem1495193 (n : nat) (m : nat) : (term156 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495194 : term191 = term192.
Proof. exact (@lem1495193 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1495195 : term192 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1495196 : term191 = False.
Proof. exact (TRANS (@lem1495194) (@lem1495195)). Qed.
Lemma lem1495197 (x : real) (y : real) (h1 : term217 x y) : False.
Proof. exact (EQ_MP (@lem1495196) (@lem1495191 x y h1)). Qed.
Lemma lem1495198 (x : real) (y : real) (h1 : term147 x y) : False.
Proof. exact (or_elim (@lem1495012 x y h1) (fun h0 : term209 x y => @lem1495094 x y h0) (fun h0 : term217 x y => @lem1495197 x y h0)). Qed.
Lemma lem1495199 (x : real) (y : real) (h1 : term150 x y) : False.
Proof. exact (or_elim (@lem1494825 x y h1) (fun h0 : term148 x y => @lem1495011 x y h0) (fun h0 : term147 x y => @lem1495198 x y h0)). Qed.
Lemma lem1495201 (x : real) (y : real) (h1 : term150 x y) : term150 x y.
Proof. exact (h1). Qed.
Lemma lem1495202 (x : real) (y : real) (h1 : term150 x y) : (term150 x y) = False.
Proof. exact (prop_ext (fun h2 : term150 x y => @lem1495199 x y h1) (fun h2 : False => @lem1495201 x y h1)). Qed.
Lemma lem1495203 (x : real) (y : real) (h1 : term150 x y) : False.
Proof. exact (EQ_MP (@lem1495202 x y h1) (@lem1495201 x y h1)). Qed.
Lemma lem1495204 (x : real) (h1 : term152 x) : term152 x.
Proof. exact (h1). Qed.
Lemma lem1495205 (x : real) (h1 : term152 x) : False.
Proof. exact (ex_elim (@lem1495204 x h1) (fun y : real => fun h0 : term151 x y => @lem1495203 x y h0)). Qed.
Lemma lem1495206 (h1 : term154) : term154.
Proof. exact (h1). Qed.
Lemma lem1495207 (h1 : term154) : False.
Proof. exact (ex_elim (@lem1495206 h1) (fun x : real => fun h0 : term153 x => @lem1495205 x h0)). Qed.
Lemma lem1495208 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1495209 (h1 : term27) : term154.
Proof. exact (EQ_MP (@lem1494803) (@lem1495208 h1)). Qed.
Lemma lem1495210 (h1 : term27) : term154 = False.
Proof. exact (prop_ext (fun h2 : term154 => @lem1495207 h2) (fun h2 : False => @lem1495209 h1)). Qed.
Lemma lem1495211 (h1 : term27) : False.
Proof. exact (EQ_MP (@lem1495210 h1) (@lem1495209 h1)). Qed.
Lemma lem1495212 : term223.
Proof. exact (fun h0 : term27 => @lem1495211 h0). Qed.
Lemma lem1495213 : term224.
Proof. exact (@lem1386578 term225). Qed.
Lemma lem1495214 : term225.
Proof. exact (@lem1495213 (@lem1495212)). Qed.

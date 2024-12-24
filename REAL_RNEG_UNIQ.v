Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_RNEG_UNIQ_term_abbrevs.
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
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
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
Lemma lem1490201 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17646 ((real_add x y) = term2) (y = (real_neg x))). Qed.
Lemma lem1490202 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1490203 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1490202 (term7 x)). Qed.
Lemma lem1490204 (y : real) (x : real) : (term8 x y) = (((real_add x y) = term2) = (y = (real_neg x))).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1490205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1490206 (y : real) (x : real) : (term9 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1490205) (@lem1490204 y x)). Qed.
Lemma lem1490207 (y : real) (x : real) : (term9 x y) = (term1 y x).
Proof. exact (TRANS (@lem1490206 y x) (@lem1490201 y x)). Qed.
Lemma lem1490208 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1490207 y x)). Qed.
Lemma lem1490209 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490210 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1490209) (@lem1490208 x)). Qed.
Lemma lem1490211 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1490203 x) (@lem1490210 x)). Qed.
Lemma lem1490212 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1490213 : term13 = term14.
Proof. exact (@lem1490212 term15). Qed.
Lemma lem1490214 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1490215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1490216 (x : real) : (term18 x) = (term5 x).
Proof. exact (MK_COMB (@lem1490215) (@lem1490214 x)). Qed.
Lemma lem1490217 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1490216 x) (@lem1490211 x)). Qed.
Lemma lem1490218 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1490217 x)). Qed.
Lemma lem1490219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490220 : term14 = term21.
Proof. exact (MK_COMB (@lem1490219) (@lem1490218)). Qed.
Lemma lem1490222 : term13 = term21.
Proof. exact (TRANS (@lem1490213) (@lem1490220)). Qed.
Lemma lem1490239 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1490240 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1490239 y x)). Qed.
Lemma lem1490241 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490242 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1490241) (@lem1490240 x)). Qed.
Lemma lem1490243 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1490242 x)). Qed.
Lemma lem1490244 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490245 : term21 = term21.
Proof. exact (MK_COMB (@lem1490244) (@lem1490243)). Qed.
Lemma lem1490246 : term13 = term21.
Proof. exact (TRANS (@lem1490222) (@lem1490245)). Qed.
Lemma lem1490247 (x : real) (y : real) : ((real_add x y) = term2) = ((term22 x y) = term2).
Proof. exact (@lem1483529 (real_add x y) term2). Qed.
Lemma lem1490259 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) term2). Qed.
Lemma lem1490261 (x : nat) : (term24 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1490262 : term25 = term2.
Proof. exact (@lem1490261 term26). Qed.
Lemma lem1490263 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1490264 (x : real) (y : real) : (term23 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1490263 x y) (@lem1490262)). Qed.
Lemma lem1490265 (x : real) (y : real) : (term28 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1490266 (x : real) (y : real) : (term23 x y) = (real_add x y).
Proof. exact (TRANS (@lem1490264 x y) (@lem1490265 x y)). Qed.
Lemma lem1490268 (x : real) (y : real) : (term22 x y) = (real_add x y).
Proof. exact (TRANS (@lem1490259 x y) (@lem1490266 x y)). Qed.
Lemma lem1490269 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490270 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1490269) (@lem1490268 x y)). Qed.
Lemma lem1490271 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490272 (x : real) (y : real) : ((term22 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1490270 x y) (@lem1490271)). Qed.
Lemma lem1490273 (x : real) (y : real) : ((real_add x y) = term2) = ((real_add x y) = term2).
Proof. exact (TRANS (@lem1490247 x y) (@lem1490272 x y)). Qed.
Lemma lem1490274 (y : real) (x : real) : (term31 y x) = (term32 y x).
Proof. exact (@lem1483554 y (real_neg x)). Qed.
Lemma lem1490281 (x : real) : (real_neg x) = (term33 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1490284 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1490285 (y : real) (x : real) : (term34 y x) = (term35 y x).
Proof. exact (MK_COMB (@lem1490284 y) (@lem1490281 x)). Qed.
Lemma lem1490286 (y : real) (x : real) : (term35 y x) = (term36 y x).
Proof. exact (@lem1483519 y (term33 x)). Qed.
Lemma lem1490287 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1490289 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1490290 : term42 = term43.
Proof. exact (@lem1490289 term26 term26). Qed.
Lemma lem1490291 : (term44 = (BIT1 0)) = (term45 = term26).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1490292 : term45 = term26.
Proof. exact (EQ_MP (@lem1490291) (@lem940073)). Qed.
Lemma lem1490293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1490294 : term43 = term46.
Proof. exact (MK_COMB (@lem1490293) (@lem1490292)). Qed.
Lemma lem1490295 : term42 = term46.
Proof. exact (TRANS (@lem1490290) (@lem1490294)). Qed.
Lemma lem1490296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490297 : term47 = term48.
Proof. exact (MK_COMB (@lem1490296) (@lem1490295)). Qed.
Lemma lem1490298 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490299 (x : real) : (term38 x) = (term49 x).
Proof. exact (MK_COMB (@lem1490297) (@lem1490298 x)). Qed.
Lemma lem1490300 (x : real) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1490287 x) (@lem1490299 x)). Qed.
Lemma lem1490301 (x : real) : (term49 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1490302 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1490300 x) (@lem1490301 x)). Qed.
Lemma lem1490303 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1490304 (y : real) (x : real) : (term36 y x) = (real_add y x).
Proof. exact (MK_COMB (@lem1490303 y) (@lem1490302 x)). Qed.
Lemma lem1490305 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1483488 x y). Qed.
Lemma lem1490306 (x : real) (y : real) : (term36 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490304 y x) (@lem1490305 x y)). Qed.
Lemma lem1490307 (x : real) (y : real) : (term35 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490286 y x) (@lem1490306 x y)). Qed.
Lemma lem1490308 (x : real) (y : real) : (term34 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490285 y x) (@lem1490307 x y)). Qed.
Lemma lem1490309 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1490310 (x : real) (y : real) : (term50 y x) = (term51 x y).
Proof. exact (MK_COMB (@lem1490309) (@lem1490308 x y)). Qed.
Lemma lem1490311 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1490318 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1490319 (x : real) (y : real) : (term51 x y) = (term53 x y).
Proof. exact (TRANS (@lem1490311 x y) (@lem1490318 x y)). Qed.
Lemma lem1490320 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (eq_refl (term54 y x)). Qed.
Lemma lem1490321 (x : real) (y : real) : ((term50 y x) = (term51 x y)) = ((term50 y x) = (term53 x y)).
Proof. exact (MK_COMB (@lem1490320 y x) (@lem1490319 x y)). Qed.
Lemma lem1490322 (x : real) (y : real) : (term50 y x) = (term53 x y).
Proof. exact (EQ_MP (@lem1490321 x y) (@lem1490310 x y)). Qed.
Lemma lem1490323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490324 (x : real) (y : real) : (term55 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1490323) (@lem1490322 x y)). Qed.
Lemma lem1490325 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490326 (x : real) (y : real) : (term57 y x) = (term58 x y).
Proof. exact (MK_COMB (@lem1490324 x y) (@lem1490325)). Qed.
Lemma lem1490327 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490328 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (MK_COMB (@lem1490327) (@lem1490308 x y)). Qed.
Lemma lem1490329 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490330 (x : real) (y : real) : (term61 y x) = (term62 x y).
Proof. exact (MK_COMB (@lem1490328 x y) (@lem1490329)). Qed.
Lemma lem1490331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490332 (x : real) (y : real) : (term63 y x) = (term64 x y).
Proof. exact (MK_COMB (@lem1490331) (@lem1490330 x y)). Qed.
Lemma lem1490333 (x : real) (y : real) : (term32 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1490332 x y) (@lem1490326 x y)). Qed.
Lemma lem1490334 (x : real) (y : real) : (term31 y x) = (term65 x y).
Proof. exact (TRANS (@lem1490274 y x) (@lem1490333 x y)). Qed.
Lemma lem1490335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1490336 (x : real) (y : real) : (term66 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1490335) (@lem1490273 x y)). Qed.
Lemma lem1490337 (x : real) (y : real) : (term67 y x) = (term68 x y).
Proof. exact (MK_COMB (@lem1490336 x y) (@lem1490334 x y)). Qed.
Lemma lem1490338 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (@lem1483554 (real_add x y) term2). Qed.
Lemma lem1490350 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) term2). Qed.
Lemma lem1490352 (x : nat) : (term24 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1490353 : term25 = term2.
Proof. exact (@lem1490352 term26). Qed.
Lemma lem1490354 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1490355 (x : real) (y : real) : (term23 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1490354 x y) (@lem1490353)). Qed.
Lemma lem1490356 (x : real) (y : real) : (term28 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1490357 (x : real) (y : real) : (term23 x y) = (real_add x y).
Proof. exact (TRANS (@lem1490355 x y) (@lem1490356 x y)). Qed.
Lemma lem1490359 (x : real) (y : real) : (term22 x y) = (real_add x y).
Proof. exact (TRANS (@lem1490350 x y) (@lem1490357 x y)). Qed.
Lemma lem1490360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1490361 (x : real) (y : real) : (term71 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1490360) (@lem1490359 x y)). Qed.
Lemma lem1490362 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1490369 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1490370 (x : real) (y : real) : (term51 x y) = (term53 x y).
Proof. exact (TRANS (@lem1490362 x y) (@lem1490369 x y)). Qed.
Lemma lem1490371 (x : real) (y : real) : (term72 x y) = (term72 x y).
Proof. exact (eq_refl (term72 x y)). Qed.
Lemma lem1490372 (x : real) (y : real) : ((term71 x y) = (term51 x y)) = ((term71 x y) = (term53 x y)).
Proof. exact (MK_COMB (@lem1490371 x y) (@lem1490370 x y)). Qed.
Lemma lem1490373 (x : real) (y : real) : (term71 x y) = (term53 x y).
Proof. exact (EQ_MP (@lem1490372 x y) (@lem1490361 x y)). Qed.
Lemma lem1490374 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490375 (x : real) (y : real) : (term73 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1490374) (@lem1490373 x y)). Qed.
Lemma lem1490376 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490377 (x : real) (y : real) : (term74 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1490375 x y) (@lem1490376)). Qed.
Lemma lem1490378 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490379 (x : real) (y : real) : (term75 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1490378) (@lem1490359 x y)). Qed.
Lemma lem1490380 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490381 (x : real) (y : real) : (term76 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1490379 x y) (@lem1490380)). Qed.
Lemma lem1490382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490383 (x : real) (y : real) : (term77 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1490382) (@lem1490381 x y)). Qed.
Lemma lem1490384 (x : real) (y : real) : (term70 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1490383 x y) (@lem1490377 x y)). Qed.
Lemma lem1490385 (x : real) (y : real) : (term69 x y) = (term65 x y).
Proof. exact (TRANS (@lem1490338 x y) (@lem1490384 x y)). Qed.
Lemma lem1490386 (y : real) (x : real) : (y = (real_neg x)) = ((term34 y x) = term2).
Proof. exact (@lem1483529 y (real_neg x)). Qed.
Lemma lem1490393 (x : real) : (real_neg x) = (term33 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1490396 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1490397 (y : real) (x : real) : (term34 y x) = (term35 y x).
Proof. exact (MK_COMB (@lem1490396 y) (@lem1490393 x)). Qed.
Lemma lem1490398 (y : real) (x : real) : (term35 y x) = (term36 y x).
Proof. exact (@lem1483519 y (term33 x)). Qed.
Lemma lem1490399 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1483476 term39 term39 x). Qed.
Lemma lem1490401 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1490402 : term42 = term43.
Proof. exact (@lem1490401 term26 term26). Qed.
Lemma lem1490403 : (term44 = (BIT1 0)) = (term45 = term26).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1490404 : term45 = term26.
Proof. exact (EQ_MP (@lem1490403) (@lem940073)). Qed.
Lemma lem1490405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1490406 : term43 = term46.
Proof. exact (MK_COMB (@lem1490405) (@lem1490404)). Qed.
Lemma lem1490407 : term42 = term46.
Proof. exact (TRANS (@lem1490402) (@lem1490406)). Qed.
Lemma lem1490408 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490409 : term47 = term48.
Proof. exact (MK_COMB (@lem1490408) (@lem1490407)). Qed.
Lemma lem1490410 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490411 (x : real) : (term38 x) = (term49 x).
Proof. exact (MK_COMB (@lem1490409) (@lem1490410 x)). Qed.
Lemma lem1490412 (x : real) : (term37 x) = (term49 x).
Proof. exact (TRANS (@lem1490399 x) (@lem1490411 x)). Qed.
Lemma lem1490413 (x : real) : (term49 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1490414 (x : real) : (term37 x) = x.
Proof. exact (TRANS (@lem1490412 x) (@lem1490413 x)). Qed.
Lemma lem1490415 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1490416 (y : real) (x : real) : (term36 y x) = (real_add y x).
Proof. exact (MK_COMB (@lem1490415 y) (@lem1490414 x)). Qed.
Lemma lem1490417 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1483488 x y). Qed.
Lemma lem1490418 (x : real) (y : real) : (term36 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490416 y x) (@lem1490417 x y)). Qed.
Lemma lem1490419 (x : real) (y : real) : (term35 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490398 y x) (@lem1490418 x y)). Qed.
Lemma lem1490420 (x : real) (y : real) : (term34 y x) = (real_add x y).
Proof. exact (TRANS (@lem1490397 y x) (@lem1490419 x y)). Qed.
Lemma lem1490421 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490422 (x : real) (y : real) : (term78 y x) = (term30 x y).
Proof. exact (MK_COMB (@lem1490421) (@lem1490420 x y)). Qed.
Lemma lem1490423 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490424 (x : real) (y : real) : ((term34 y x) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1490422 x y) (@lem1490423)). Qed.
Lemma lem1490425 (x : real) (y : real) : (y = (real_neg x)) = ((real_add x y) = term2).
Proof. exact (TRANS (@lem1490386 y x) (@lem1490424 x y)). Qed.
Lemma lem1490426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1490427 (x : real) (y : real) : (term79 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1490426) (@lem1490385 x y)). Qed.
Lemma lem1490428 (x : real) (y : real) : (term81 y x) = (term82 x y).
Proof. exact (MK_COMB (@lem1490427 x y) (@lem1490425 x y)). Qed.
Lemma lem1490429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490430 (x : real) (y : real) : (term83 y x) = (term84 x y).
Proof. exact (MK_COMB (@lem1490429) (@lem1490337 x y)). Qed.
Lemma lem1490431 (x : real) (y : real) : (term1 y x) = (term85 x y).
Proof. exact (MK_COMB (@lem1490430 x y) (@lem1490428 x y)). Qed.
Lemma lem1490432 (x : real) : (term11 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1490431 x y)). Qed.
Lemma lem1490433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490434 (x : real) : (term12 x) = (term87 x).
Proof. exact (MK_COMB (@lem1490433) (@lem1490432 x)). Qed.
Lemma lem1490435 : term20 = term88.
Proof. exact (fun_ext (fun x : real => @lem1490434 x)). Qed.
Lemma lem1490436 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490437 : term21 = term89.
Proof. exact (MK_COMB (@lem1490436) (@lem1490435)). Qed.
Lemma lem1490438 : term13 = term89.
Proof. exact (TRANS (@lem1490246) (@lem1490437)). Qed.
Lemma lem1490444 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1490445 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1490444 real P Q). Qed.
Lemma lem1490446 (x : real) : (term94 x) = (term95 x).
Proof. exact (@lem1490445 (term96 x) (term97 x)). Qed.
Lemma lem1490447 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1490448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490449 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1490448) (@lem1490447 x y)). Qed.
Lemma lem1490450 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1490451 (x : real) (y : real) : (term101 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1490449 x y) (@lem1490450 x y)). Qed.
Lemma lem1490452 (x : real) : (term102 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1490451 x y)). Qed.
Lemma lem1490453 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490454 (x : real) : (term94 x) = (term87 x).
Proof. exact (MK_COMB (@lem1490453) (@lem1490452 x)). Qed.
Lemma lem1490455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1490456 (x : real) : (term103 x) = (term104 x).
Proof. exact (MK_COMB (@lem1490455) (@lem1490454 x)). Qed.
Lemma lem1490457 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1490458 (x : real) : (term105 x) = (term96 x).
Proof. exact (fun_ext (fun y : real => @lem1490457 x y)). Qed.
Lemma lem1490459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490460 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1490459) (@lem1490458 x)). Qed.
Lemma lem1490461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490462 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1490461) (@lem1490460 x)). Qed.
Lemma lem1490463 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1490464 (x : real) : (term110 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1490463 x y)). Qed.
Lemma lem1490465 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490466 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1490465) (@lem1490464 x)). Qed.
Lemma lem1490467 (x : real) : (term95 x) = (term113 x).
Proof. exact (MK_COMB (@lem1490462 x) (@lem1490466 x)). Qed.
Lemma lem1490468 (x : real) : ((term94 x) = (term95 x)) = ((term87 x) = (term113 x)).
Proof. exact (MK_COMB (@lem1490456 x) (@lem1490467 x)). Qed.
Lemma lem1490469 (x : real) : (term87 x) = (term113 x).
Proof. exact (EQ_MP (@lem1490468 x) (@lem1490446 x)). Qed.
Lemma lem1490566 : term88 = term114.
Proof. exact (fun_ext (fun x : real => @lem1490469 x)). Qed.
Lemma lem1490567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490568 : term89 = term115.
Proof. exact (MK_COMB (@lem1490567) (@lem1490566)). Qed.
Lemma lem1490570 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1490571 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1490570 real P Q). Qed.
Lemma lem1490572 : term116 = term117.
Proof. exact (@lem1490571 term118 term119). Qed.
Lemma lem1490573 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1490574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490575 (x : real) : (term121 x) = (term109 x).
Proof. exact (MK_COMB (@lem1490574) (@lem1490573 x)). Qed.
Lemma lem1490576 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1490577 (x : real) : (term123 x) = (term113 x).
Proof. exact (MK_COMB (@lem1490575 x) (@lem1490576 x)). Qed.
Lemma lem1490578 : term124 = term114.
Proof. exact (fun_ext (fun x : real => @lem1490577 x)). Qed.
Lemma lem1490579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490580 : term116 = term115.
Proof. exact (MK_COMB (@lem1490579) (@lem1490578)). Qed.
Lemma lem1490581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1490582 : term125 = term126.
Proof. exact (MK_COMB (@lem1490581) (@lem1490580)). Qed.
Lemma lem1490583 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1490584 : term127 = term118.
Proof. exact (fun_ext (fun x : real => @lem1490583 x)). Qed.
Lemma lem1490585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490586 : term128 = term129.
Proof. exact (MK_COMB (@lem1490585) (@lem1490584)). Qed.
Lemma lem1490587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490588 : term130 = term131.
Proof. exact (MK_COMB (@lem1490587) (@lem1490586)). Qed.
Lemma lem1490589 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1490590 : term132 = term119.
Proof. exact (fun_ext (fun x : real => @lem1490589 x)). Qed.
Lemma lem1490591 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490592 : term133 = term134.
Proof. exact (MK_COMB (@lem1490591) (@lem1490590)). Qed.
Lemma lem1490593 : term117 = term135.
Proof. exact (MK_COMB (@lem1490588) (@lem1490592)). Qed.
Lemma lem1490594 : (term116 = term117) = (term115 = term135).
Proof. exact (MK_COMB (@lem1490582) (@lem1490593)). Qed.
Lemma lem1490595 : term115 = term135.
Proof. exact (EQ_MP (@lem1490594) (@lem1490572)). Qed.
Lemma lem1490700 : term89 = term135.
Proof. exact (TRANS (@lem1490568) (@lem1490595)). Qed.
Lemma lem1490702 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1490703 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1490702 real P Q). Qed.
Lemma lem1490704 : term117 = term116.
Proof. exact (@lem1490703 term118 term119). Qed.
Lemma lem1490705 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1490706 : term127 = term118.
Proof. exact (fun_ext (fun x : real => @lem1490705 x)). Qed.
Lemma lem1490707 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490708 : term128 = term129.
Proof. exact (MK_COMB (@lem1490707) (@lem1490706)). Qed.
Lemma lem1490709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490710 : term130 = term131.
Proof. exact (MK_COMB (@lem1490709) (@lem1490708)). Qed.
Lemma lem1490711 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1490712 : term132 = term119.
Proof. exact (fun_ext (fun x : real => @lem1490711 x)). Qed.
Lemma lem1490713 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490714 : term133 = term134.
Proof. exact (MK_COMB (@lem1490713) (@lem1490712)). Qed.
Lemma lem1490715 : term117 = term135.
Proof. exact (MK_COMB (@lem1490710) (@lem1490714)). Qed.
Lemma lem1490716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1490717 : term136 = term137.
Proof. exact (MK_COMB (@lem1490716) (@lem1490715)). Qed.
Lemma lem1490718 (x : real) : (term120 x) = (term107 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1490719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490720 (x : real) : (term121 x) = (term109 x).
Proof. exact (MK_COMB (@lem1490719) (@lem1490718 x)). Qed.
Lemma lem1490721 (x : real) : (term122 x) = (term112 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1490722 (x : real) : (term123 x) = (term113 x).
Proof. exact (MK_COMB (@lem1490720 x) (@lem1490721 x)). Qed.
Lemma lem1490723 : term124 = term114.
Proof. exact (fun_ext (fun x : real => @lem1490722 x)). Qed.
Lemma lem1490724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490725 : term116 = term115.
Proof. exact (MK_COMB (@lem1490724) (@lem1490723)). Qed.
Lemma lem1490726 : (term117 = term116) = (term135 = term115).
Proof. exact (MK_COMB (@lem1490717) (@lem1490725)). Qed.
Lemma lem1490727 : term135 = term115.
Proof. exact (EQ_MP (@lem1490726) (@lem1490704)). Qed.
Lemma lem1490729 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1490730 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1490729 real P Q). Qed.
Lemma lem1490731 (x : real) : (term95 x) = (term94 x).
Proof. exact (@lem1490730 (term96 x) (term97 x)). Qed.
Lemma lem1490732 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1490733 (x : real) : (term105 x) = (term96 x).
Proof. exact (fun_ext (fun y : real => @lem1490732 x y)). Qed.
Lemma lem1490734 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490735 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1490734) (@lem1490733 x)). Qed.
Lemma lem1490736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490737 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1490736) (@lem1490735 x)). Qed.
Lemma lem1490738 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1490739 (x : real) : (term110 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1490738 x y)). Qed.
Lemma lem1490740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490741 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1490740) (@lem1490739 x)). Qed.
Lemma lem1490742 (x : real) : (term95 x) = (term113 x).
Proof. exact (MK_COMB (@lem1490737 x) (@lem1490741 x)). Qed.
Lemma lem1490743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1490744 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1490743) (@lem1490742 x)). Qed.
Lemma lem1490745 (x : real) (y : real) : (term98 x y) = (term68 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1490746 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490747 (x : real) (y : real) : (term99 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1490746) (@lem1490745 x y)). Qed.
Lemma lem1490748 (x : real) (y : real) : (term100 x y) = (term82 x y).
Proof. exact (eq_refl (term100 x y)). Qed.
Lemma lem1490749 (x : real) (y : real) : (term101 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1490747 x y) (@lem1490748 x y)). Qed.
Lemma lem1490750 (x : real) : (term102 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1490749 x y)). Qed.
Lemma lem1490751 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490752 (x : real) : (term94 x) = (term87 x).
Proof. exact (MK_COMB (@lem1490751) (@lem1490750 x)). Qed.
Lemma lem1490753 (x : real) : ((term95 x) = (term94 x)) = ((term113 x) = (term87 x)).
Proof. exact (MK_COMB (@lem1490744 x) (@lem1490752 x)). Qed.
Lemma lem1490754 (x : real) : (term113 x) = (term87 x).
Proof. exact (EQ_MP (@lem1490753 x) (@lem1490731 x)). Qed.
Lemma lem1490755 : term114 = term88.
Proof. exact (fun_ext (fun x : real => @lem1490754 x)). Qed.
Lemma lem1490756 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490757 : term115 = term89.
Proof. exact (MK_COMB (@lem1490756) (@lem1490755)). Qed.
Lemma lem1490758 : term135 = term89.
Proof. exact (TRANS (@lem1490727) (@lem1490757)). Qed.
Lemma lem1490759 : term89 = term89.
Proof. exact (TRANS (@lem1490700) (@lem1490758)). Qed.
Lemma lem1490762 : term13 = term89.
Proof. exact (TRANS (@lem1490438) (@lem1490759)). Qed.
Lemma lem1490779 (x : real) (y : real) : (term82 x y) = (term140 x y).
Proof. exact (@lem19367 (term62 x y) (term58 x y) ((real_add x y) = term2)). Qed.
Lemma lem1490796 (x : real) (y : real) : (term68 x y) = (term141 x y).
Proof. exact (@lem19158 (term62 x y) ((real_add x y) = term2) (term58 x y)). Qed.
Lemma lem1490797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1490798 (x : real) (y : real) : (term84 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem1490797) (@lem1490796 x y)). Qed.
Lemma lem1490799 (x : real) (y : real) : (term85 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1490798 x y) (@lem1490779 x y)). Qed.
Lemma lem1490800 (x : real) : (term86 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1490799 x y)). Qed.
Lemma lem1490801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490802 (x : real) : (term87 x) = (term145 x).
Proof. exact (MK_COMB (@lem1490801) (@lem1490800 x)). Qed.
Lemma lem1490803 : term88 = term146.
Proof. exact (fun_ext (fun x : real => @lem1490802 x)). Qed.
Lemma lem1490804 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1490805 : term89 = term147.
Proof. exact (MK_COMB (@lem1490804) (@lem1490803)). Qed.
Lemma lem1490806 : term13 = term147.
Proof. exact (TRANS (@lem1490762) (@lem1490805)). Qed.
Lemma lem1490828 (x : real) (y : real) (h1 : term143 x y) : term143 x y.
Proof. exact (h1). Qed.
Lemma lem1490829 (x : real) (y : real) (h1 : term141 x y) : term141 x y.
Proof. exact (h1). Qed.
Lemma lem1490830 (x : real) (y : real) (h1 : term148 x y) : term148 x y.
Proof. exact (h1). Qed.
Lemma lem1490831 (x : real) (y : real) (h1 : term148 x y) : term62 x y.
Proof. exact (proj2 (@lem1490830 x y h1)). Qed.
Lemma lem1490832 (x : real) (y : real) (h1 : term148 x y) : (real_add x y) = term2.
Proof. exact (proj1 (@lem1490830 x y h1)). Qed.
Lemma lem1490834 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490835 : term150 = term151.
Proof. exact (@lem1490834 (NUMERAL 0) term26). Qed.
Lemma lem1490836 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1490837 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1490838 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1490837 h1) (fun h1 : term151 = True => @lem1490836)). Qed.
Lemma lem1490839 : term151 = True.
Proof. exact (EQ_MP (@lem1490838) (@lem1490836)). Qed.
Lemma lem1490840 : term150 = True.
Proof. exact (TRANS (@lem1490835) (@lem1490839)). Qed.
Lemma lem1490841 : True = term150.
Proof. exact (SYM (@lem1490840)). Qed.
Lemma lem1490842 : term150.
Proof. exact (EQ_MP (@lem1490841) (@lem0)). Qed.
Lemma lem1490843 (x : real) (y : real) (h1 : term148 x y) : term153 x y.
Proof. exact (conj (@lem1490842) (@lem1490831 x y h1)). Qed.
Lemma lem1490845 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1490846 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1490845 term46 (real_add x y)). Qed.
Lemma lem1490847 (x : real) (y : real) (h1 : term148 x y) : term156 x y.
Proof. exact (@lem1490846 x y (@lem1490843 x y h1)). Qed.
Lemma lem1490848 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1490849 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490850 (x : real) (y : real) : (term158 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1490849) (@lem1490848 x y)). Qed.
Lemma lem1490851 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490852 (x : real) (y : real) : (term156 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1490850 x y) (@lem1490851)). Qed.
Lemma lem1490853 (x : real) (y : real) (h1 : term148 x y) : term62 x y.
Proof. exact (EQ_MP (@lem1490852 x y) (@lem1490847 x y h1)). Qed.
Lemma lem1490855 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1490856 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1490855 (real_add x y)). Qed.
Lemma lem1490857 (x : real) (y : real) (h1 : term148 x y) : term161 x y.
Proof. exact (@lem1490856 x y (@lem1490832 x y h1)). Qed.
Lemma lem1490858 (x : real) (y : real) (h1 : term148 x y) : term162 x y.
Proof. exact (@lem1490857 x y h1 term39). Qed.
Lemma lem1490859 (x : real) (y : real) : (term162 x y) = ((term52 x y) = term2).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1490860 (x : real) (y : real) (h1 : term148 x y) : (term52 x y) = term2.
Proof. exact (EQ_MP (@lem1490859 x y) (@lem1490858 x y h1)). Qed.
Lemma lem1490867 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1490868 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490869 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1490868) (@lem1490867 x y)). Qed.
Lemma lem1490870 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490871 (x : real) (y : real) : ((term52 x y) = term2) = ((term53 x y) = term2).
Proof. exact (MK_COMB (@lem1490869 x y) (@lem1490870)). Qed.
Lemma lem1490872 (x : real) (y : real) (h1 : term148 x y) : (term53 x y) = term2.
Proof. exact (EQ_MP (@lem1490871 x y) (@lem1490860 x y h1)). Qed.
Lemma lem1490873 (x : real) (y : real) (h1 : term148 x y) : term165 x y.
Proof. exact (conj (@lem1490872 x y h1) (@lem1490853 x y h1)). Qed.
Lemma lem1490875 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1490876 (x : real) (y : real) : term167 x y.
Proof. exact (@lem1490875 (term53 x y) (real_add x y)). Qed.
Lemma lem1490877 (x : real) (y : real) (h1 : term148 x y) : term168 x y.
Proof. exact (@lem1490876 x y (@lem1490873 x y h1)). Qed.
Lemma lem1490878 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1483480 (term33 x) x (term33 y) y). Qed.
Lemma lem1490879 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1490881 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490882 : term174 = term2.
Proof. exact (@lem1490881 term26). Qed.
Lemma lem1490883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490884 : term175 = term176.
Proof. exact (MK_COMB (@lem1490883) (@lem1490882)). Qed.
Lemma lem1490885 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490886 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1490884) (@lem1490885 x)). Qed.
Lemma lem1490887 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1490879 x) (@lem1490886 x)). Qed.
Lemma lem1490888 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1490889 (x : real) : (term171 x) = term2.
Proof. exact (TRANS (@lem1490887 x) (@lem1490888 x)). Qed.
Lemma lem1490890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1490891 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1490890) (@lem1490889 x)). Qed.
Lemma lem1490892 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1490894 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490895 : term174 = term2.
Proof. exact (@lem1490894 term26). Qed.
Lemma lem1490896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490897 : term175 = term176.
Proof. exact (MK_COMB (@lem1490896) (@lem1490895)). Qed.
Lemma lem1490898 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1490899 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1490897) (@lem1490898 y)). Qed.
Lemma lem1490900 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1490892 y) (@lem1490899 y)). Qed.
Lemma lem1490901 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1490902 (y : real) : (term171 y) = term2.
Proof. exact (TRANS (@lem1490900 y) (@lem1490901 y)). Qed.
Lemma lem1490903 (x : real) (y : real) : (term170 x y) = term180.
Proof. exact (MK_COMB (@lem1490891 x) (@lem1490902 y)). Qed.
Lemma lem1490904 (x : real) (y : real) : (term169 x y) = term180.
Proof. exact (TRANS (@lem1490878 x y) (@lem1490903 x y)). Qed.
Lemma lem1490905 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1490906 (x : real) (y : real) : (term169 x y) = term2.
Proof. exact (TRANS (@lem1490904 x y) (@lem1490905)). Qed.
Lemma lem1490907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490908 (x : real) (y : real) : (term181 x y) = term182.
Proof. exact (MK_COMB (@lem1490907) (@lem1490906 x y)). Qed.
Lemma lem1490909 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490910 (x : real) (y : real) : (term168 x y) = term183.
Proof. exact (MK_COMB (@lem1490908 x y) (@lem1490909)). Qed.
Lemma lem1490911 (x : real) (y : real) (h1 : term148 x y) : term183.
Proof. exact (EQ_MP (@lem1490910 x y) (@lem1490877 x y h1)). Qed.
Lemma lem1490913 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490914 : term183 = term184.
Proof. exact (@lem1490913 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1490915 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1490916 : term183 = False.
Proof. exact (TRANS (@lem1490914) (@lem1490915)). Qed.
Lemma lem1490917 (x : real) (y : real) (h1 : term148 x y) : False.
Proof. exact (EQ_MP (@lem1490916) (@lem1490911 x y h1)). Qed.
Lemma lem1490918 (x : real) (y : real) (h1 : term185 x y) : term185 x y.
Proof. exact (h1). Qed.
Lemma lem1490919 (x : real) (y : real) (h1 : term185 x y) : term58 x y.
Proof. exact (proj2 (@lem1490918 x y h1)). Qed.
Lemma lem1490920 (x : real) (y : real) (h1 : term185 x y) : (real_add x y) = term2.
Proof. exact (proj1 (@lem1490918 x y h1)). Qed.
Lemma lem1490922 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490923 : term150 = term151.
Proof. exact (@lem1490922 (NUMERAL 0) term26). Qed.
Lemma lem1490924 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1490925 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1490926 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1490925 h1) (fun h1 : term151 = True => @lem1490924)). Qed.
Lemma lem1490927 : term151 = True.
Proof. exact (EQ_MP (@lem1490926) (@lem1490924)). Qed.
Lemma lem1490928 : term150 = True.
Proof. exact (TRANS (@lem1490923) (@lem1490927)). Qed.
Lemma lem1490929 : True = term150.
Proof. exact (SYM (@lem1490928)). Qed.
Lemma lem1490930 : term150.
Proof. exact (EQ_MP (@lem1490929) (@lem0)). Qed.
Lemma lem1490931 (x : real) (y : real) (h1 : term185 x y) : term186 x y.
Proof. exact (conj (@lem1490930) (@lem1490919 x y h1)). Qed.
Lemma lem1490933 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1490934 (x : real) (y : real) : term187 x y.
Proof. exact (@lem1490933 term46 (term53 x y)). Qed.
Lemma lem1490935 (x : real) (y : real) (h1 : term185 x y) : term188 x y.
Proof. exact (@lem1490934 x y (@lem1490931 x y h1)). Qed.
Lemma lem1490936 (x : real) (y : real) : (term189 x y) = (term53 x y).
Proof. exact (@lem1483460 (term53 x y)). Qed.
Lemma lem1490937 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490938 (x : real) (y : real) : (term190 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1490937) (@lem1490936 x y)). Qed.
Lemma lem1490939 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490940 (x : real) (y : real) : (term188 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1490938 x y) (@lem1490939)). Qed.
Lemma lem1490941 (x : real) (y : real) (h1 : term185 x y) : term58 x y.
Proof. exact (EQ_MP (@lem1490940 x y) (@lem1490935 x y h1)). Qed.
Lemma lem1490943 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1490944 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1490943 (real_add x y)). Qed.
Lemma lem1490945 (x : real) (y : real) (h1 : term185 x y) : term161 x y.
Proof. exact (@lem1490944 x y (@lem1490920 x y h1)). Qed.
Lemma lem1490946 (x : real) (y : real) (h1 : term185 x y) : term191 x y.
Proof. exact (@lem1490945 x y h1 term46). Qed.
Lemma lem1490947 (x : real) (y : real) : (term191 x y) = ((term157 x y) = term2).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1490948 (x : real) (y : real) (h1 : term185 x y) : (term157 x y) = term2.
Proof. exact (EQ_MP (@lem1490947 x y) (@lem1490946 x y h1)). Qed.
Lemma lem1490949 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1490950 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1490951 (x : real) (y : real) : (term192 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1490950) (@lem1490949 x y)). Qed.
Lemma lem1490952 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490953 (x : real) (y : real) : ((term157 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1490951 x y) (@lem1490952)). Qed.
Lemma lem1490954 (x : real) (y : real) (h1 : term185 x y) : (real_add x y) = term2.
Proof. exact (EQ_MP (@lem1490953 x y) (@lem1490948 x y h1)). Qed.
Lemma lem1490955 (x : real) (y : real) (h1 : term185 x y) : term185 x y.
Proof. exact (conj (@lem1490954 x y h1) (@lem1490941 x y h1)). Qed.
Lemma lem1490957 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1490958 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1490957 (real_add x y) (term53 x y)). Qed.
Lemma lem1490959 (x : real) (y : real) (h1 : term185 x y) : term194 x y.
Proof. exact (@lem1490958 x y (@lem1490955 x y h1)). Qed.
Lemma lem1490960 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483480 x (term33 x) y (term33 y)). Qed.
Lemma lem1490961 (x : real) : (term197 x) = (term172 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1490963 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490964 : term174 = term2.
Proof. exact (@lem1490963 term26). Qed.
Lemma lem1490965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490966 : term175 = term176.
Proof. exact (MK_COMB (@lem1490965) (@lem1490964)). Qed.
Lemma lem1490967 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1490968 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1490966) (@lem1490967 x)). Qed.
Lemma lem1490969 (x : real) : (term197 x) = (term177 x).
Proof. exact (TRANS (@lem1490961 x) (@lem1490968 x)). Qed.
Lemma lem1490970 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1490971 (x : real) : (term197 x) = term2.
Proof. exact (TRANS (@lem1490969 x) (@lem1490970 x)). Qed.
Lemma lem1490972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1490973 (x : real) : (term198 x) = term179.
Proof. exact (MK_COMB (@lem1490972) (@lem1490971 x)). Qed.
Lemma lem1490974 (y : real) : (term197 y) = (term172 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1490976 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1490977 : term174 = term2.
Proof. exact (@lem1490976 term26). Qed.
Lemma lem1490978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1490979 : term175 = term176.
Proof. exact (MK_COMB (@lem1490978) (@lem1490977)). Qed.
Lemma lem1490980 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1490981 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1490979) (@lem1490980 y)). Qed.
Lemma lem1490982 (y : real) : (term197 y) = (term177 y).
Proof. exact (TRANS (@lem1490974 y) (@lem1490981 y)). Qed.
Lemma lem1490983 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1490984 (y : real) : (term197 y) = term2.
Proof. exact (TRANS (@lem1490982 y) (@lem1490983 y)). Qed.
Lemma lem1490985 (x : real) (y : real) : (term196 x y) = term180.
Proof. exact (MK_COMB (@lem1490973 x) (@lem1490984 y)). Qed.
Lemma lem1490986 (x : real) (y : real) : (term195 x y) = term180.
Proof. exact (TRANS (@lem1490960 x y) (@lem1490985 x y)). Qed.
Lemma lem1490987 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1490988 (x : real) (y : real) : (term195 x y) = term2.
Proof. exact (TRANS (@lem1490986 x y) (@lem1490987)). Qed.
Lemma lem1490989 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1490990 (x : real) (y : real) : (term199 x y) = term182.
Proof. exact (MK_COMB (@lem1490989) (@lem1490988 x y)). Qed.
Lemma lem1490991 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1490992 (x : real) (y : real) : (term194 x y) = term183.
Proof. exact (MK_COMB (@lem1490990 x y) (@lem1490991)). Qed.
Lemma lem1490993 (x : real) (y : real) (h1 : term185 x y) : term183.
Proof. exact (EQ_MP (@lem1490992 x y) (@lem1490959 x y h1)). Qed.
Lemma lem1490995 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1490996 : term183 = term184.
Proof. exact (@lem1490995 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1490997 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1490998 : term183 = False.
Proof. exact (TRANS (@lem1490996) (@lem1490997)). Qed.
Lemma lem1490999 (x : real) (y : real) (h1 : term185 x y) : False.
Proof. exact (EQ_MP (@lem1490998) (@lem1490993 x y h1)). Qed.
Lemma lem1491000 (x : real) (y : real) (h1 : term141 x y) : False.
Proof. exact (or_elim (@lem1490829 x y h1) (fun h0 : term148 x y => @lem1490917 x y h0) (fun h0 : term185 x y => @lem1490999 x y h0)). Qed.
Lemma lem1491001 (x : real) (y : real) (h1 : term140 x y) : term140 x y.
Proof. exact (h1). Qed.
Lemma lem1491002 (x : real) (y : real) (h1 : term200 x y) : term200 x y.
Proof. exact (h1). Qed.
Lemma lem1491003 (x : real) (y : real) (h1 : term200 x y) : (real_add x y) = term2.
Proof. exact (proj2 (@lem1491002 x y h1)). Qed.
Lemma lem1491004 (x : real) (y : real) (h1 : term200 x y) : term62 x y.
Proof. exact (proj1 (@lem1491002 x y h1)). Qed.
Lemma lem1491006 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491007 : term150 = term151.
Proof. exact (@lem1491006 (NUMERAL 0) term26). Qed.
Lemma lem1491008 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1491009 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1491010 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1491009 h1) (fun h1 : term151 = True => @lem1491008)). Qed.
Lemma lem1491011 : term151 = True.
Proof. exact (EQ_MP (@lem1491010) (@lem1491008)). Qed.
Lemma lem1491012 : term150 = True.
Proof. exact (TRANS (@lem1491007) (@lem1491011)). Qed.
Lemma lem1491013 : True = term150.
Proof. exact (SYM (@lem1491012)). Qed.
Lemma lem1491014 : term150.
Proof. exact (EQ_MP (@lem1491013) (@lem0)). Qed.
Lemma lem1491015 (x : real) (y : real) (h1 : term200 x y) : term153 x y.
Proof. exact (conj (@lem1491014) (@lem1491004 x y h1)). Qed.
Lemma lem1491017 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1491018 (x : real) (y : real) : term155 x y.
Proof. exact (@lem1491017 term46 (real_add x y)). Qed.
Lemma lem1491019 (x : real) (y : real) (h1 : term200 x y) : term156 x y.
Proof. exact (@lem1491018 x y (@lem1491015 x y h1)). Qed.
Lemma lem1491020 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1491021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491022 (x : real) (y : real) : (term158 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1491021) (@lem1491020 x y)). Qed.
Lemma lem1491023 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491024 (x : real) (y : real) : (term156 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1491022 x y) (@lem1491023)). Qed.
Lemma lem1491025 (x : real) (y : real) (h1 : term200 x y) : term62 x y.
Proof. exact (EQ_MP (@lem1491024 x y) (@lem1491019 x y h1)). Qed.
Lemma lem1491027 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1491028 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1491027 (real_add x y)). Qed.
Lemma lem1491029 (x : real) (y : real) (h1 : term200 x y) : term161 x y.
Proof. exact (@lem1491028 x y (@lem1491003 x y h1)). Qed.
Lemma lem1491030 (x : real) (y : real) (h1 : term200 x y) : term162 x y.
Proof. exact (@lem1491029 x y h1 term39). Qed.
Lemma lem1491031 (x : real) (y : real) : (term162 x y) = ((term52 x y) = term2).
Proof. exact (eq_refl (term162 x y)). Qed.
Lemma lem1491032 (x : real) (y : real) (h1 : term200 x y) : (term52 x y) = term2.
Proof. exact (EQ_MP (@lem1491031 x y) (@lem1491030 x y h1)). Qed.
Lemma lem1491039 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 x term39 y). Qed.
Lemma lem1491040 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1491041 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1491040) (@lem1491039 x y)). Qed.
Lemma lem1491042 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491043 (x : real) (y : real) : ((term52 x y) = term2) = ((term53 x y) = term2).
Proof. exact (MK_COMB (@lem1491041 x y) (@lem1491042)). Qed.
Lemma lem1491044 (x : real) (y : real) (h1 : term200 x y) : (term53 x y) = term2.
Proof. exact (EQ_MP (@lem1491043 x y) (@lem1491032 x y h1)). Qed.
Lemma lem1491045 (x : real) (y : real) (h1 : term200 x y) : term165 x y.
Proof. exact (conj (@lem1491044 x y h1) (@lem1491025 x y h1)). Qed.
Lemma lem1491047 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1491048 (x : real) (y : real) : term167 x y.
Proof. exact (@lem1491047 (term53 x y) (real_add x y)). Qed.
Lemma lem1491049 (x : real) (y : real) (h1 : term200 x y) : term168 x y.
Proof. exact (@lem1491048 x y (@lem1491045 x y h1)). Qed.
Lemma lem1491050 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1483480 (term33 x) x (term33 y) y). Qed.
Lemma lem1491051 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1491053 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491054 : term174 = term2.
Proof. exact (@lem1491053 term26). Qed.
Lemma lem1491055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491056 : term175 = term176.
Proof. exact (MK_COMB (@lem1491055) (@lem1491054)). Qed.
Lemma lem1491057 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1491058 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1491056) (@lem1491057 x)). Qed.
Lemma lem1491059 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1491051 x) (@lem1491058 x)). Qed.
Lemma lem1491060 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1491061 (x : real) : (term171 x) = term2.
Proof. exact (TRANS (@lem1491059 x) (@lem1491060 x)). Qed.
Lemma lem1491062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1491063 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1491062) (@lem1491061 x)). Qed.
Lemma lem1491064 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term39 y). Qed.
Lemma lem1491066 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491067 : term174 = term2.
Proof. exact (@lem1491066 term26). Qed.
Lemma lem1491068 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491069 : term175 = term176.
Proof. exact (MK_COMB (@lem1491068) (@lem1491067)). Qed.
Lemma lem1491070 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1491071 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1491069) (@lem1491070 y)). Qed.
Lemma lem1491072 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1491064 y) (@lem1491071 y)). Qed.
Lemma lem1491073 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1491074 (y : real) : (term171 y) = term2.
Proof. exact (TRANS (@lem1491072 y) (@lem1491073 y)). Qed.
Lemma lem1491075 (x : real) (y : real) : (term170 x y) = term180.
Proof. exact (MK_COMB (@lem1491063 x) (@lem1491074 y)). Qed.
Lemma lem1491076 (x : real) (y : real) : (term169 x y) = term180.
Proof. exact (TRANS (@lem1491050 x y) (@lem1491075 x y)). Qed.
Lemma lem1491077 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1491078 (x : real) (y : real) : (term169 x y) = term2.
Proof. exact (TRANS (@lem1491076 x y) (@lem1491077)). Qed.
Lemma lem1491079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491080 (x : real) (y : real) : (term181 x y) = term182.
Proof. exact (MK_COMB (@lem1491079) (@lem1491078 x y)). Qed.
Lemma lem1491081 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491082 (x : real) (y : real) : (term168 x y) = term183.
Proof. exact (MK_COMB (@lem1491080 x y) (@lem1491081)). Qed.
Lemma lem1491083 (x : real) (y : real) (h1 : term200 x y) : term183.
Proof. exact (EQ_MP (@lem1491082 x y) (@lem1491049 x y h1)). Qed.
Lemma lem1491085 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491086 : term183 = term184.
Proof. exact (@lem1491085 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491087 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491088 : term183 = False.
Proof. exact (TRANS (@lem1491086) (@lem1491087)). Qed.
Lemma lem1491089 (x : real) (y : real) (h1 : term200 x y) : False.
Proof. exact (EQ_MP (@lem1491088) (@lem1491083 x y h1)). Qed.
Lemma lem1491090 (x : real) (y : real) (h1 : term201 x y) : term201 x y.
Proof. exact (h1). Qed.
Lemma lem1491091 (x : real) (y : real) (h1 : term201 x y) : (real_add x y) = term2.
Proof. exact (proj2 (@lem1491090 x y h1)). Qed.
Lemma lem1491092 (x : real) (y : real) (h1 : term201 x y) : term58 x y.
Proof. exact (proj1 (@lem1491090 x y h1)). Qed.
Lemma lem1491094 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491095 : term150 = term151.
Proof. exact (@lem1491094 (NUMERAL 0) term26). Qed.
Lemma lem1491096 : term152 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1491097 (h1 : term152 = (BIT1 0)) : term151 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1491098 : (term152 = (BIT1 0)) = (term151 = True).
Proof. exact (prop_ext (fun h1 : term152 = (BIT1 0) => @lem1491097 h1) (fun h1 : term151 = True => @lem1491096)). Qed.
Lemma lem1491099 : term151 = True.
Proof. exact (EQ_MP (@lem1491098) (@lem1491096)). Qed.
Lemma lem1491100 : term150 = True.
Proof. exact (TRANS (@lem1491095) (@lem1491099)). Qed.
Lemma lem1491101 : True = term150.
Proof. exact (SYM (@lem1491100)). Qed.
Lemma lem1491102 : term150.
Proof. exact (EQ_MP (@lem1491101) (@lem0)). Qed.
Lemma lem1491103 (x : real) (y : real) (h1 : term201 x y) : term186 x y.
Proof. exact (conj (@lem1491102) (@lem1491092 x y h1)). Qed.
Lemma lem1491105 (x : real) (y : real) : term154 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1491106 (x : real) (y : real) : term187 x y.
Proof. exact (@lem1491105 term46 (term53 x y)). Qed.
Lemma lem1491107 (x : real) (y : real) (h1 : term201 x y) : term188 x y.
Proof. exact (@lem1491106 x y (@lem1491103 x y h1)). Qed.
Lemma lem1491108 (x : real) (y : real) : (term189 x y) = (term53 x y).
Proof. exact (@lem1483460 (term53 x y)). Qed.
Lemma lem1491109 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491110 (x : real) (y : real) : (term190 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1491109) (@lem1491108 x y)). Qed.
Lemma lem1491111 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491112 (x : real) (y : real) : (term188 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1491110 x y) (@lem1491111)). Qed.
Lemma lem1491113 (x : real) (y : real) (h1 : term201 x y) : term58 x y.
Proof. exact (EQ_MP (@lem1491112 x y) (@lem1491107 x y h1)). Qed.
Lemma lem1491115 (y : real) : term159 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1491116 (x : real) (y : real) : term160 x y.
Proof. exact (@lem1491115 (real_add x y)). Qed.
Lemma lem1491117 (x : real) (y : real) (h1 : term201 x y) : term161 x y.
Proof. exact (@lem1491116 x y (@lem1491091 x y h1)). Qed.
Lemma lem1491118 (x : real) (y : real) (h1 : term201 x y) : term191 x y.
Proof. exact (@lem1491117 x y h1 term46). Qed.
Lemma lem1491119 (x : real) (y : real) : (term191 x y) = ((term157 x y) = term2).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1491120 (x : real) (y : real) (h1 : term201 x y) : (term157 x y) = term2.
Proof. exact (EQ_MP (@lem1491119 x y) (@lem1491118 x y h1)). Qed.
Lemma lem1491121 (x : real) (y : real) : (term157 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1491122 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1491123 (x : real) (y : real) : (term192 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1491122) (@lem1491121 x y)). Qed.
Lemma lem1491124 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491125 (x : real) (y : real) : ((term157 x y) = term2) = ((real_add x y) = term2).
Proof. exact (MK_COMB (@lem1491123 x y) (@lem1491124)). Qed.
Lemma lem1491126 (x : real) (y : real) (h1 : term201 x y) : (real_add x y) = term2.
Proof. exact (EQ_MP (@lem1491125 x y) (@lem1491120 x y h1)). Qed.
Lemma lem1491127 (x : real) (y : real) (h1 : term201 x y) : term185 x y.
Proof. exact (conj (@lem1491126 x y h1) (@lem1491113 x y h1)). Qed.
Lemma lem1491129 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1491130 (x : real) (y : real) : term193 x y.
Proof. exact (@lem1491129 (real_add x y) (term53 x y)). Qed.
Lemma lem1491131 (x : real) (y : real) (h1 : term201 x y) : term194 x y.
Proof. exact (@lem1491130 x y (@lem1491127 x y h1)). Qed.
Lemma lem1491132 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483480 x (term33 x) y (term33 y)). Qed.
Lemma lem1491133 (x : real) : (term197 x) = (term172 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1491135 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491136 : term174 = term2.
Proof. exact (@lem1491135 term26). Qed.
Lemma lem1491137 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491138 : term175 = term176.
Proof. exact (MK_COMB (@lem1491137) (@lem1491136)). Qed.
Lemma lem1491139 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1491140 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1491138) (@lem1491139 x)). Qed.
Lemma lem1491141 (x : real) : (term197 x) = (term177 x).
Proof. exact (TRANS (@lem1491133 x) (@lem1491140 x)). Qed.
Lemma lem1491142 (x : real) : (term177 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1491143 (x : real) : (term197 x) = term2.
Proof. exact (TRANS (@lem1491141 x) (@lem1491142 x)). Qed.
Lemma lem1491144 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1491145 (x : real) : (term198 x) = term179.
Proof. exact (MK_COMB (@lem1491144) (@lem1491143 x)). Qed.
Lemma lem1491146 (y : real) : (term197 y) = (term172 y).
Proof. exact (@lem1483442 term39 y). Qed.
Lemma lem1491148 (m : nat) : (term173 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491149 : term174 = term2.
Proof. exact (@lem1491148 term26). Qed.
Lemma lem1491150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1491151 : term175 = term176.
Proof. exact (MK_COMB (@lem1491150) (@lem1491149)). Qed.
Lemma lem1491152 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1491153 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1491151) (@lem1491152 y)). Qed.
Lemma lem1491154 (y : real) : (term197 y) = (term177 y).
Proof. exact (TRANS (@lem1491146 y) (@lem1491153 y)). Qed.
Lemma lem1491155 (y : real) : (term177 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1491156 (y : real) : (term197 y) = term2.
Proof. exact (TRANS (@lem1491154 y) (@lem1491155 y)). Qed.
Lemma lem1491157 (x : real) (y : real) : (term196 x y) = term180.
Proof. exact (MK_COMB (@lem1491145 x) (@lem1491156 y)). Qed.
Lemma lem1491158 (x : real) (y : real) : (term195 x y) = term180.
Proof. exact (TRANS (@lem1491132 x y) (@lem1491157 x y)). Qed.
Lemma lem1491159 : term180 = term2.
Proof. exact (@lem1483448 term2). Qed.
Lemma lem1491160 (x : real) (y : real) : (term195 x y) = term2.
Proof. exact (TRANS (@lem1491158 x y) (@lem1491159)). Qed.
Lemma lem1491161 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1491162 (x : real) (y : real) : (term199 x y) = term182.
Proof. exact (MK_COMB (@lem1491161) (@lem1491160 x y)). Qed.
Lemma lem1491163 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1491164 (x : real) (y : real) : (term194 x y) = term183.
Proof. exact (MK_COMB (@lem1491162 x y) (@lem1491163)). Qed.
Lemma lem1491165 (x : real) (y : real) (h1 : term201 x y) : term183.
Proof. exact (EQ_MP (@lem1491164 x y) (@lem1491131 x y h1)). Qed.
Lemma lem1491167 (n : nat) (m : nat) : (term149 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1491168 : term183 = term184.
Proof. exact (@lem1491167 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1491169 : term184 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1491170 : term183 = False.
Proof. exact (TRANS (@lem1491168) (@lem1491169)). Qed.
Lemma lem1491171 (x : real) (y : real) (h1 : term201 x y) : False.
Proof. exact (EQ_MP (@lem1491170) (@lem1491165 x y h1)). Qed.
Lemma lem1491172 (x : real) (y : real) (h1 : term140 x y) : False.
Proof. exact (or_elim (@lem1491001 x y h1) (fun h0 : term200 x y => @lem1491089 x y h0) (fun h0 : term201 x y => @lem1491171 x y h0)). Qed.
Lemma lem1491173 (x : real) (y : real) (h1 : term143 x y) : False.
Proof. exact (or_elim (@lem1490828 x y h1) (fun h0 : term141 x y => @lem1491000 x y h0) (fun h0 : term140 x y => @lem1491172 x y h0)). Qed.
Lemma lem1491175 (x : real) (y : real) (h1 : term143 x y) : term143 x y.
Proof. exact (h1). Qed.
Lemma lem1491176 (x : real) (y : real) (h1 : term143 x y) : (term143 x y) = False.
Proof. exact (prop_ext (fun h2 : term143 x y => @lem1491173 x y h1) (fun h2 : False => @lem1491175 x y h1)). Qed.
Lemma lem1491177 (x : real) (y : real) (h1 : term143 x y) : False.
Proof. exact (EQ_MP (@lem1491176 x y h1) (@lem1491175 x y h1)). Qed.
Lemma lem1491178 (x : real) (h1 : term145 x) : term145 x.
Proof. exact (h1). Qed.
Lemma lem1491179 (x : real) (h1 : term145 x) : False.
Proof. exact (ex_elim (@lem1491178 x h1) (fun y : real => fun h0 : term144 x y => @lem1491177 x y h0)). Qed.
Lemma lem1491180 (h1 : term147) : term147.
Proof. exact (h1). Qed.
Lemma lem1491181 (h1 : term147) : False.
Proof. exact (ex_elim (@lem1491180 h1) (fun x : real => fun h0 : term146 x => @lem1491179 x h0)). Qed.
Lemma lem1491182 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1491183 (h1 : term13) : term147.
Proof. exact (EQ_MP (@lem1490806) (@lem1491182 h1)). Qed.
Lemma lem1491184 (h1 : term13) : term147 = False.
Proof. exact (prop_ext (fun h2 : term147 => @lem1491181 h2) (fun h2 : False => @lem1491183 h1)). Qed.
Lemma lem1491185 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1491184 h1) (@lem1491183 h1)). Qed.
Lemma lem1491186 : term202.
Proof. exact (fun h0 : term13 => @lem1491185 h0). Qed.
Lemma lem1491187 : term203.
Proof. exact (@lem1386578 term204). Qed.
Lemma lem1491188 : term204.
Proof. exact (@lem1491187 (@lem1491186)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LMUL_term_abbrevs.
Require Import REAL_LT_MUL_spec.
Require Import REAL_SUB_LDISTRIB_spec.
Require Import REAL_SUB_RZERO_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
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
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1584230 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term0 x y z) = (term1 y x z).
Proof. exact (h1). Qed.
Lemma lem1584231 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term1 y x z) = (term0 x y z).
Proof. exact (SYM (@lem1584230 y x z h1)). Qed.
Lemma lem1584232 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term1 y x z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1584233 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term0 x y z) = (term1 y x z).
Proof. exact (SYM (@lem1584232 x y z h1)). Qed.
Lemma lem1584234 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 y x z)) = ((term1 y x z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 y x z) => @lem1584231 y x z h1) (fun h1 : (term1 y x z) = (term0 x y z) => @lem1584233 x y z h1)). Qed.
Lemma lem1584235 (x : real) (y : real) : (term2 y x) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1584234 x y z)). Qed.
Lemma lem1584236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584237 (x : real) (y : real) : (term4 y x) = (term5 x y).
Proof. exact (MK_COMB (@lem1584236) (@lem1584235 x y)). Qed.
Lemma lem1584238 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1584237 x y)). Qed.
Lemma lem1584239 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584240 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1584239) (@lem1584238 x)). Qed.
Lemma lem1584241 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1584240 x)). Qed.
Lemma lem1584242 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584243 : term12 = term13.
Proof. exact (MK_COMB (@lem1584242) (@lem1584241)). Qed.
Lemma lem1584244 : term13.
Proof. exact (EQ_MP (@lem1584243) (@lem1526444)). Qed.
Lemma lem1584245 (x : real) : term14 x.
Proof. exact (@lem1487565 x). Qed.
Lemma lem1584246 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1584247 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1584246 x) (@lem1584245 x)). Qed.
Lemma lem1584248 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1584247 x y). Qed.
Lemma lem1584249 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1584250 (x : real) (y : real) : term17 x y.
Proof. exact (EQ_MP (@lem1584249 x y) (@lem1584248 x y)). Qed.
Lemma lem1584251 (x : real) (y : real) : (term17 x y) = ((term17 x y) = True).
Proof. exact (@lem7 (term17 x y)). Qed.
Lemma lem1584253 (x : real) : term18 x.
Proof. exact (@lem1518006 x). Qed.
Lemma lem1584254 (x : real) : (term18 x) = ((term19 x) = x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1584256 (x : real) : term20 x.
Proof. exact (@lem1584244 x). Qed.
Lemma lem1584257 (x : real) : (term20 x) = (term9 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1584258 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1584257 x) (@lem1584256 x)). Qed.
Lemma lem1584259 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1584258 x y). Qed.
Lemma lem1584260 (x : real) (y : real) : (term21 x y) = (term5 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1584261 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1584260 x y) (@lem1584259 x y)). Qed.
Lemma lem1584262 (x : real) (y : real) (z : real) : term22 x y z.
Proof. exact (@lem1584261 x y z). Qed.
Lemma lem1584263 (x : real) (y : real) (z : real) : (term22 x y z) = ((term1 y x z) = (term0 x y z)).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1584301 (y : real) (x : real) : (term23 y x) = (term24 y x).
Proof. exact (@lem17646 (real_lt x y) (term25 y x)). Qed.
Lemma lem1584302 (y : real) (x : real) : (real_lt x y) = (term26 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1584308 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1584313 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1584315 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1584308 y x) (@lem1584313 x y)). Qed.
Lemma lem1584316 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584317 (x : real) (y : real) : (term30 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1584316) (@lem1584315 x y)). Qed.
Lemma lem1584318 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584319 (x : real) (y : real) : (term26 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1584317 x y) (@lem1584318)). Qed.
Lemma lem1584320 (x : real) (y : real) : (real_lt x y) = (term33 x y).
Proof. exact (TRANS (@lem1584302 y x) (@lem1584319 x y)). Qed.
Lemma lem1584321 (y : real) (x : real) : (term34 y x) = (term35 y x).
Proof. exact (@lem1483531 term32 (real_sub y x)). Qed.
Lemma lem1584327 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1584332 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1584334 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1584327 y x) (@lem1584332 x y)). Qed.
Lemma lem1584337 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1584338 (x : real) (y : real) : (term37 y x) = (term38 x y).
Proof. exact (MK_COMB (@lem1584337) (@lem1584334 x y)). Qed.
Lemma lem1584339 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (@lem1483519 term32 (term28 x y)). Qed.
Lemma lem1584340 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem1483508 (term29 x) term42 y). Qed.
Lemma lem1584341 (y : real) : (term29 y) = (term29 y).
Proof. exact (eq_refl (term29 y)). Qed.
Lemma lem1584342 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483476 term42 term42 x). Qed.
Lemma lem1584344 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1584345 : term47 = term48.
Proof. exact (@lem1584344 term49 term49). Qed.
Lemma lem1584346 : (term50 = (BIT1 0)) = (term51 = term49).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1584347 : term51 = term49.
Proof. exact (EQ_MP (@lem1584346) (@lem940073)). Qed.
Lemma lem1584348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1584349 : term48 = term52.
Proof. exact (MK_COMB (@lem1584348) (@lem1584347)). Qed.
Lemma lem1584350 : term47 = term52.
Proof. exact (TRANS (@lem1584345) (@lem1584349)). Qed.
Lemma lem1584351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1584352 : term53 = term54.
Proof. exact (MK_COMB (@lem1584351) (@lem1584350)). Qed.
Lemma lem1584353 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1584354 (x : real) : (term44 x) = (term55 x).
Proof. exact (MK_COMB (@lem1584352) (@lem1584353 x)). Qed.
Lemma lem1584355 (x : real) : (term43 x) = (term55 x).
Proof. exact (TRANS (@lem1584342 x) (@lem1584354 x)). Qed.
Lemma lem1584356 (x : real) : (term55 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1584357 (x : real) : (term43 x) = x.
Proof. exact (TRANS (@lem1584355 x) (@lem1584356 x)). Qed.
Lemma lem1584358 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1584359 (x : real) : (term56 x) = (real_add x).
Proof. exact (MK_COMB (@lem1584358) (@lem1584357 x)). Qed.
Lemma lem1584360 (x : real) (y : real) : (term41 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1584359 x) (@lem1584341 y)). Qed.
Lemma lem1584361 (x : real) (y : real) : (term40 x y) = (term27 x y).
Proof. exact (TRANS (@lem1584340 x y) (@lem1584360 x y)). Qed.
Lemma lem1584362 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1584363 (x : real) (y : real) : (term39 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1584362) (@lem1584361 x y)). Qed.
Lemma lem1584364 (x : real) (y : real) : (term58 x y) = (term27 x y).
Proof. exact (@lem1483448 (term27 x y)). Qed.
Lemma lem1584365 (x : real) (y : real) : (term39 x y) = (term27 x y).
Proof. exact (TRANS (@lem1584363 x y) (@lem1584364 x y)). Qed.
Lemma lem1584366 (x : real) (y : real) : (term38 x y) = (term27 x y).
Proof. exact (TRANS (@lem1584339 x y) (@lem1584365 x y)). Qed.
Lemma lem1584367 (x : real) (y : real) : (term37 y x) = (term27 x y).
Proof. exact (TRANS (@lem1584338 x y) (@lem1584366 x y)). Qed.
Lemma lem1584368 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1584369 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (MK_COMB (@lem1584368) (@lem1584367 x y)). Qed.
Lemma lem1584370 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584371 (x : real) (y : real) : (term35 y x) = (term61 x y).
Proof. exact (MK_COMB (@lem1584369 x y) (@lem1584370)). Qed.
Lemma lem1584372 (x : real) (y : real) : (term34 y x) = (term61 x y).
Proof. exact (TRANS (@lem1584321 y x) (@lem1584371 x y)). Qed.
Lemma lem1584373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584374 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1584373) (@lem1584320 x y)). Qed.
Lemma lem1584375 (x : real) (y : real) : (term64 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1584374 x y) (@lem1584372 x y)). Qed.
Lemma lem1584376 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem1483531 x y). Qed.
Lemma lem1584389 (x : real) (y : real) : (real_sub x y) = (term27 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1584390 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1584391 (x : real) (y : real) : (term68 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1584390) (@lem1584389 x y)). Qed.
Lemma lem1584392 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584393 (x : real) (y : real) : (term67 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1584391 x y) (@lem1584392)). Qed.
Lemma lem1584394 (x : real) (y : real) : (term66 x y) = (term61 x y).
Proof. exact (TRANS (@lem1584376 x y) (@lem1584393 x y)). Qed.
Lemma lem1584395 (y : real) (x : real) : (term25 y x) = (term69 y x).
Proof. exact (@lem1483521 (real_sub y x) term32). Qed.
Lemma lem1584396 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584402 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1584407 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1584409 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1584402 y x) (@lem1584407 x y)). Qed.
Lemma lem1584410 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1584411 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1584410) (@lem1584409 x y)). Qed.
Lemma lem1584412 (x : real) (y : real) : (term72 y x) = (term73 x y).
Proof. exact (MK_COMB (@lem1584411 x y) (@lem1584396)). Qed.
Lemma lem1584413 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (@lem1483519 (term28 x y) term32). Qed.
Lemma lem1584415 (x : nat) : (term75 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1584416 : term76 = term32.
Proof. exact (@lem1584415 term49). Qed.
Lemma lem1584417 (x : real) (y : real) : (term77 x y) = (term77 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1584418 (x : real) (y : real) : (term74 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1584417 x y) (@lem1584416)). Qed.
Lemma lem1584419 (x : real) (y : real) : (term78 x y) = (term28 x y).
Proof. exact (@lem1483450 (term28 x y)). Qed.
Lemma lem1584420 (x : real) (y : real) : (term74 x y) = (term28 x y).
Proof. exact (TRANS (@lem1584418 x y) (@lem1584419 x y)). Qed.
Lemma lem1584421 (x : real) (y : real) : (term73 x y) = (term28 x y).
Proof. exact (TRANS (@lem1584413 x y) (@lem1584420 x y)). Qed.
Lemma lem1584422 (x : real) (y : real) : (term72 y x) = (term28 x y).
Proof. exact (TRANS (@lem1584412 x y) (@lem1584421 x y)). Qed.
Lemma lem1584423 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584424 (x : real) (y : real) : (term79 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1584423) (@lem1584422 x y)). Qed.
Lemma lem1584425 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584426 (x : real) (y : real) : (term69 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1584424 x y) (@lem1584425)). Qed.
Lemma lem1584427 (x : real) (y : real) : (term25 y x) = (term33 x y).
Proof. exact (TRANS (@lem1584395 y x) (@lem1584426 x y)). Qed.
Lemma lem1584428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584429 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1584428) (@lem1584394 x y)). Qed.
Lemma lem1584430 (x : real) (y : real) : (term82 y x) = (term83 x y).
Proof. exact (MK_COMB (@lem1584429 x y) (@lem1584427 x y)). Qed.
Lemma lem1584431 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1584432 (x : real) (y : real) : (term84 y x) = (term85 x y).
Proof. exact (MK_COMB (@lem1584431) (@lem1584375 x y)). Qed.
Lemma lem1584433 (x : real) (y : real) : (term24 y x) = (term86 x y).
Proof. exact (MK_COMB (@lem1584432 x y) (@lem1584430 x y)). Qed.
Lemma lem1584458 (x : real) (y : real) : (term23 y x) = (term86 x y).
Proof. exact (TRANS (@lem1584301 y x) (@lem1584433 x y)). Qed.
Lemma lem1584468 (x : real) (y : real) (h1 : term86 x y) : term86 x y.
Proof. exact (h1). Qed.
Lemma lem1584469 (x : real) (y : real) (h1 : term65 x y) : term65 x y.
Proof. exact (h1). Qed.
Lemma lem1584470 (x : real) (y : real) (h1 : term65 x y) : term61 x y.
Proof. exact (proj2 (@lem1584469 x y h1)). Qed.
Lemma lem1584471 (x : real) (y : real) (h1 : term65 x y) : term33 x y.
Proof. exact (proj1 (@lem1584469 x y h1)). Qed.
Lemma lem1584473 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584474 : term88 = term89.
Proof. exact (@lem1584473 (NUMERAL 0) term49). Qed.
Lemma lem1584475 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1584476 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1584477 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1584476 h1) (fun h1 : term89 = True => @lem1584475)). Qed.
Lemma lem1584478 : term89 = True.
Proof. exact (EQ_MP (@lem1584477) (@lem1584475)). Qed.
Lemma lem1584479 : term88 = True.
Proof. exact (TRANS (@lem1584474) (@lem1584478)). Qed.
Lemma lem1584480 : True = term88.
Proof. exact (SYM (@lem1584479)). Qed.
Lemma lem1584481 : term88.
Proof. exact (EQ_MP (@lem1584480) (@lem0)). Qed.
Lemma lem1584482 (x : real) (y : real) (h1 : term65 x y) : term91 x y.
Proof. exact (conj (@lem1584481) (@lem1584470 x y h1)). Qed.
Lemma lem1584484 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1584485 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1584484 term52 (term27 x y)). Qed.
Lemma lem1584486 (x : real) (y : real) (h1 : term65 x y) : term94 x y.
Proof. exact (@lem1584485 x y (@lem1584482 x y h1)). Qed.
Lemma lem1584487 (x : real) (y : real) : (term95 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1584488 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1584489 (x : real) (y : real) : (term96 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1584488) (@lem1584487 x y)). Qed.
Lemma lem1584490 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584491 (x : real) (y : real) : (term94 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1584489 x y) (@lem1584490)). Qed.
Lemma lem1584492 (x : real) (y : real) (h1 : term65 x y) : term61 x y.
Proof. exact (EQ_MP (@lem1584491 x y) (@lem1584486 x y h1)). Qed.
Lemma lem1584494 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584495 : term88 = term89.
Proof. exact (@lem1584494 (NUMERAL 0) term49). Qed.
Lemma lem1584496 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1584497 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1584498 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1584497 h1) (fun h1 : term89 = True => @lem1584496)). Qed.
Lemma lem1584499 : term89 = True.
Proof. exact (EQ_MP (@lem1584498) (@lem1584496)). Qed.
Lemma lem1584500 : term88 = True.
Proof. exact (TRANS (@lem1584495) (@lem1584499)). Qed.
Lemma lem1584501 : True = term88.
Proof. exact (SYM (@lem1584500)). Qed.
Lemma lem1584502 : term88.
Proof. exact (EQ_MP (@lem1584501) (@lem0)). Qed.
Lemma lem1584503 (x : real) (y : real) (h1 : term65 x y) : term97 x y.
Proof. exact (conj (@lem1584502) (@lem1584471 x y h1)). Qed.
Lemma lem1584505 (x : real) (y : real) : term98 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1584506 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1584505 term52 (term28 x y)). Qed.
Lemma lem1584507 (x : real) (y : real) (h1 : term65 x y) : term100 x y.
Proof. exact (@lem1584506 x y (@lem1584503 x y h1)). Qed.
Lemma lem1584508 (x : real) (y : real) : (term101 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1584509 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584510 (x : real) (y : real) : (term102 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1584509) (@lem1584508 x y)). Qed.
Lemma lem1584511 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584512 (x : real) (y : real) : (term100 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1584510 x y) (@lem1584511)). Qed.
Lemma lem1584513 (x : real) (y : real) (h1 : term65 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1584512 x y) (@lem1584507 x y h1)). Qed.
Lemma lem1584514 (x : real) (y : real) (h1 : term65 x y) : term65 x y.
Proof. exact (conj (@lem1584513 x y h1) (@lem1584492 x y h1)). Qed.
Lemma lem1584516 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1584517 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1584516 (term28 x y) (term27 x y)). Qed.
Lemma lem1584518 (x : real) (y : real) (h1 : term65 x y) : term105 x y.
Proof. exact (@lem1584517 x y (@lem1584514 x y h1)). Qed.
Lemma lem1584519 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1483480 (term29 x) x y (term29 y)). Qed.
Lemma lem1584520 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1483440 term42 x). Qed.
Lemma lem1584522 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1584523 : term111 = term32.
Proof. exact (@lem1584522 term49). Qed.
Lemma lem1584524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1584525 : term112 = term113.
Proof. exact (MK_COMB (@lem1584524) (@lem1584523)). Qed.
Lemma lem1584526 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1584527 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1584525) (@lem1584526 x)). Qed.
Lemma lem1584528 (x : real) : (term108 x) = (term114 x).
Proof. exact (TRANS (@lem1584520 x) (@lem1584527 x)). Qed.
Lemma lem1584529 (x : real) : (term114 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1584530 (x : real) : (term108 x) = term32.
Proof. exact (TRANS (@lem1584528 x) (@lem1584529 x)). Qed.
Lemma lem1584531 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1584532 (x : real) : (term115 x) = term57.
Proof. exact (MK_COMB (@lem1584531) (@lem1584530 x)). Qed.
Lemma lem1584533 (y : real) : (term116 y) = (term109 y).
Proof. exact (@lem1483442 term42 y). Qed.
Lemma lem1584535 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1584536 : term111 = term32.
Proof. exact (@lem1584535 term49). Qed.
Lemma lem1584537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1584538 : term112 = term113.
Proof. exact (MK_COMB (@lem1584537) (@lem1584536)). Qed.
Lemma lem1584539 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1584540 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1584538) (@lem1584539 y)). Qed.
Lemma lem1584541 (y : real) : (term116 y) = (term114 y).
Proof. exact (TRANS (@lem1584533 y) (@lem1584540 y)). Qed.
Lemma lem1584542 (y : real) : (term114 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1584543 (y : real) : (term116 y) = term32.
Proof. exact (TRANS (@lem1584541 y) (@lem1584542 y)). Qed.
Lemma lem1584544 (x : real) (y : real) : (term107 x y) = term117.
Proof. exact (MK_COMB (@lem1584532 x) (@lem1584543 y)). Qed.
Lemma lem1584545 (x : real) (y : real) : (term106 x y) = term117.
Proof. exact (TRANS (@lem1584519 x y) (@lem1584544 x y)). Qed.
Lemma lem1584546 : term117 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1584547 (x : real) (y : real) : (term106 x y) = term32.
Proof. exact (TRANS (@lem1584545 x y) (@lem1584546)). Qed.
Lemma lem1584548 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584549 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1584548) (@lem1584547 x y)). Qed.
Lemma lem1584550 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584551 (x : real) (y : real) : (term105 x y) = term120.
Proof. exact (MK_COMB (@lem1584549 x y) (@lem1584550)). Qed.
Lemma lem1584552 (x : real) (y : real) (h1 : term65 x y) : term120.
Proof. exact (EQ_MP (@lem1584551 x y) (@lem1584518 x y h1)). Qed.
Lemma lem1584554 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584555 : term120 = term121.
Proof. exact (@lem1584554 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1584556 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1584557 : term120 = False.
Proof. exact (TRANS (@lem1584555) (@lem1584556)). Qed.
Lemma lem1584558 (x : real) (y : real) (h1 : term65 x y) : False.
Proof. exact (EQ_MP (@lem1584557) (@lem1584552 x y h1)). Qed.
Lemma lem1584559 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1584560 (x : real) (y : real) (h1 : term83 x y) : term33 x y.
Proof. exact (proj2 (@lem1584559 x y h1)). Qed.
Lemma lem1584561 (x : real) (y : real) (h1 : term83 x y) : term61 x y.
Proof. exact (proj1 (@lem1584559 x y h1)). Qed.
Lemma lem1584563 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584564 : term88 = term89.
Proof. exact (@lem1584563 (NUMERAL 0) term49). Qed.
Lemma lem1584565 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1584566 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1584567 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1584566 h1) (fun h1 : term89 = True => @lem1584565)). Qed.
Lemma lem1584568 : term89 = True.
Proof. exact (EQ_MP (@lem1584567) (@lem1584565)). Qed.
Lemma lem1584569 : term88 = True.
Proof. exact (TRANS (@lem1584564) (@lem1584568)). Qed.
Lemma lem1584570 : True = term88.
Proof. exact (SYM (@lem1584569)). Qed.
Lemma lem1584571 : term88.
Proof. exact (EQ_MP (@lem1584570) (@lem0)). Qed.
Lemma lem1584572 (x : real) (y : real) (h1 : term83 x y) : term91 x y.
Proof. exact (conj (@lem1584571) (@lem1584561 x y h1)). Qed.
Lemma lem1584574 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1584575 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1584574 term52 (term27 x y)). Qed.
Lemma lem1584576 (x : real) (y : real) (h1 : term83 x y) : term94 x y.
Proof. exact (@lem1584575 x y (@lem1584572 x y h1)). Qed.
Lemma lem1584577 (x : real) (y : real) : (term95 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1584578 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1584579 (x : real) (y : real) : (term96 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1584578) (@lem1584577 x y)). Qed.
Lemma lem1584580 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584581 (x : real) (y : real) : (term94 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1584579 x y) (@lem1584580)). Qed.
Lemma lem1584582 (x : real) (y : real) (h1 : term83 x y) : term61 x y.
Proof. exact (EQ_MP (@lem1584581 x y) (@lem1584576 x y h1)). Qed.
Lemma lem1584584 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584585 : term88 = term89.
Proof. exact (@lem1584584 (NUMERAL 0) term49). Qed.
Lemma lem1584586 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1584587 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1584588 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1584587 h1) (fun h1 : term89 = True => @lem1584586)). Qed.
Lemma lem1584589 : term89 = True.
Proof. exact (EQ_MP (@lem1584588) (@lem1584586)). Qed.
Lemma lem1584590 : term88 = True.
Proof. exact (TRANS (@lem1584585) (@lem1584589)). Qed.
Lemma lem1584591 : True = term88.
Proof. exact (SYM (@lem1584590)). Qed.
Lemma lem1584592 : term88.
Proof. exact (EQ_MP (@lem1584591) (@lem0)). Qed.
Lemma lem1584593 (x : real) (y : real) (h1 : term83 x y) : term97 x y.
Proof. exact (conj (@lem1584592) (@lem1584560 x y h1)). Qed.
Lemma lem1584595 (x : real) (y : real) : term98 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1584596 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1584595 term52 (term28 x y)). Qed.
Lemma lem1584597 (x : real) (y : real) (h1 : term83 x y) : term100 x y.
Proof. exact (@lem1584596 x y (@lem1584593 x y h1)). Qed.
Lemma lem1584598 (x : real) (y : real) : (term101 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1584599 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584600 (x : real) (y : real) : (term102 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1584599) (@lem1584598 x y)). Qed.
Lemma lem1584601 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584602 (x : real) (y : real) : (term100 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1584600 x y) (@lem1584601)). Qed.
Lemma lem1584603 (x : real) (y : real) (h1 : term83 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1584602 x y) (@lem1584597 x y h1)). Qed.
Lemma lem1584604 (x : real) (y : real) (h1 : term83 x y) : term65 x y.
Proof. exact (conj (@lem1584603 x y h1) (@lem1584582 x y h1)). Qed.
Lemma lem1584606 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1584607 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1584606 (term28 x y) (term27 x y)). Qed.
Lemma lem1584608 (x : real) (y : real) (h1 : term83 x y) : term105 x y.
Proof. exact (@lem1584607 x y (@lem1584604 x y h1)). Qed.
Lemma lem1584609 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1483480 (term29 x) x y (term29 y)). Qed.
Lemma lem1584610 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1483440 term42 x). Qed.
Lemma lem1584612 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1584613 : term111 = term32.
Proof. exact (@lem1584612 term49). Qed.
Lemma lem1584614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1584615 : term112 = term113.
Proof. exact (MK_COMB (@lem1584614) (@lem1584613)). Qed.
Lemma lem1584616 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1584617 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1584615) (@lem1584616 x)). Qed.
Lemma lem1584618 (x : real) : (term108 x) = (term114 x).
Proof. exact (TRANS (@lem1584610 x) (@lem1584617 x)). Qed.
Lemma lem1584619 (x : real) : (term114 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1584620 (x : real) : (term108 x) = term32.
Proof. exact (TRANS (@lem1584618 x) (@lem1584619 x)). Qed.
Lemma lem1584621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1584622 (x : real) : (term115 x) = term57.
Proof. exact (MK_COMB (@lem1584621) (@lem1584620 x)). Qed.
Lemma lem1584623 (y : real) : (term116 y) = (term109 y).
Proof. exact (@lem1483442 term42 y). Qed.
Lemma lem1584625 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1584626 : term111 = term32.
Proof. exact (@lem1584625 term49). Qed.
Lemma lem1584627 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1584628 : term112 = term113.
Proof. exact (MK_COMB (@lem1584627) (@lem1584626)). Qed.
Lemma lem1584629 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1584630 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1584628) (@lem1584629 y)). Qed.
Lemma lem1584631 (y : real) : (term116 y) = (term114 y).
Proof. exact (TRANS (@lem1584623 y) (@lem1584630 y)). Qed.
Lemma lem1584632 (y : real) : (term114 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1584633 (y : real) : (term116 y) = term32.
Proof. exact (TRANS (@lem1584631 y) (@lem1584632 y)). Qed.
Lemma lem1584634 (x : real) (y : real) : (term107 x y) = term117.
Proof. exact (MK_COMB (@lem1584622 x) (@lem1584633 y)). Qed.
Lemma lem1584635 (x : real) (y : real) : (term106 x y) = term117.
Proof. exact (TRANS (@lem1584609 x y) (@lem1584634 x y)). Qed.
Lemma lem1584636 : term117 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1584637 (x : real) (y : real) : (term106 x y) = term32.
Proof. exact (TRANS (@lem1584635 x y) (@lem1584636)). Qed.
Lemma lem1584638 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1584639 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1584638) (@lem1584637 x y)). Qed.
Lemma lem1584640 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1584641 (x : real) (y : real) : (term105 x y) = term120.
Proof. exact (MK_COMB (@lem1584639 x y) (@lem1584640)). Qed.
Lemma lem1584642 (x : real) (y : real) (h1 : term83 x y) : term120.
Proof. exact (EQ_MP (@lem1584641 x y) (@lem1584608 x y h1)). Qed.
Lemma lem1584644 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1584645 : term120 = term121.
Proof. exact (@lem1584644 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1584646 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1584647 : term120 = False.
Proof. exact (TRANS (@lem1584645) (@lem1584646)). Qed.
Lemma lem1584648 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (EQ_MP (@lem1584647) (@lem1584642 x y h1)). Qed.
Lemma lem1584649 (x : real) (y : real) (h1 : term86 x y) : False.
Proof. exact (or_elim (@lem1584468 x y h1) (fun h0 : term65 x y => @lem1584558 x y h0) (fun h0 : term83 x y => @lem1584648 x y h0)). Qed.
Lemma lem1584651 (x : real) (y : real) (h1 : term86 x y) : term86 x y.
Proof. exact (h1). Qed.
Lemma lem1584652 (x : real) (y : real) (h1 : term86 x y) : (term86 x y) = False.
Proof. exact (prop_ext (fun h2 : term86 x y => @lem1584649 x y h1) (fun h2 : False => @lem1584651 x y h1)). Qed.
Lemma lem1584653 (x : real) (y : real) (h1 : term86 x y) : False.
Proof. exact (EQ_MP (@lem1584652 x y h1) (@lem1584651 x y h1)). Qed.
Lemma lem1584654 (y : real) (x : real) (h1 : term23 y x) : term23 y x.
Proof. exact (h1). Qed.
Lemma lem1584655 (y : real) (x : real) (h1 : term23 y x) : term86 x y.
Proof. exact (EQ_MP (@lem1584458 x y) (@lem1584654 y x h1)). Qed.
Lemma lem1584656 (y : real) (x : real) (h1 : term23 y x) : (term86 x y) = False.
Proof. exact (prop_ext (fun h2 : term86 x y => @lem1584653 x y h2) (fun h2 : False => @lem1584655 y x h1)). Qed.
Lemma lem1584657 (y : real) (x : real) (h1 : term23 y x) : False.
Proof. exact (EQ_MP (@lem1584656 y x h1) (@lem1584655 y x h1)). Qed.
Lemma lem1584658 (y : real) (x : real) : term122 y x.
Proof. exact (fun h0 : term23 y x => @lem1584657 y x h0). Qed.
Lemma lem1584659 (y : real) (x : real) : term123 y x.
Proof. exact (@lem1386578 ((real_lt x y) = (term25 y x))). Qed.
Lemma lem1584678 (y : real) (x : real) : (real_lt x y) = (term25 y x).
Proof. exact (@lem1584659 y x (@lem1584658 y x)). Qed.
Lemma lem1584679 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1584678 x term32). Qed.
Lemma lem1584680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584681 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1584680) (@lem1584679 x)). Qed.
Lemma lem1584683 (y : real) (x : real) : (real_lt x y) = (term25 y x).
Proof. exact (@lem1584659 y x (@lem1584658 y x)). Qed.
Lemma lem1584684 (z : real) (y : real) : (real_lt y z) = (term25 z y).
Proof. exact (@lem1584683 z y). Qed.
Lemma lem1584685 (x : real) (z : real) (y : real) : (term128 x y z) = (term129 x z y).
Proof. exact (MK_COMB (@lem1584681 x) (@lem1584684 z y)). Qed.
Lemma lem1584686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584687 (x : real) (z : real) (y : real) : (term130 x y z) = (term131 x z y).
Proof. exact (MK_COMB (@lem1584686) (@lem1584685 x z y)). Qed.
Lemma lem1584689 (y : real) (x : real) : (real_lt x y) = (term25 y x).
Proof. exact (@lem1584659 y x (@lem1584658 y x)). Qed.
Lemma lem1584690 (z : real) (x : real) (y : real) : (term132 y x z) = (term133 z x y).
Proof. exact (@lem1584689 (real_mul x z) (real_mul x y)). Qed.
Lemma lem1584691 (z : real) (x : real) (y : real) : (term134 y x z) = (term135 z x y).
Proof. exact (MK_COMB (@lem1584687 x z y) (@lem1584690 z x y)). Qed.
Lemma lem1584692 (x : real) (y : real) : (term136 y x) = (term137 x y).
Proof. exact (fun_ext (fun z : real => @lem1584691 z x y)). Qed.
Lemma lem1584693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584694 (x : real) (y : real) : (term138 y x) = (term139 x y).
Proof. exact (MK_COMB (@lem1584693) (@lem1584692 x y)). Qed.
Lemma lem1584695 (x : real) : (term140 x) = (term141 x).
Proof. exact (fun_ext (fun y : real => @lem1584694 x y)). Qed.
Lemma lem1584696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584697 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1584696) (@lem1584695 x)). Qed.
Lemma lem1584698 : term144 = term145.
Proof. exact (fun_ext (fun x : real => @lem1584697 x)). Qed.
Lemma lem1584699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584700 : term146 = term147.
Proof. exact (MK_COMB (@lem1584699) (@lem1584698)). Qed.
Lemma lem1584701 : term147 = term146.
Proof. exact (SYM (@lem1584700)). Qed.
Lemma lem1584719 (x : real) : (term19 x) = x.
Proof. exact (EQ_MP (@lem1584254 x) (@lem1584253 x)). Qed.
Lemma lem1584720 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem1584721 (x : real) : (term125 x) = (term124 x).
Proof. exact (MK_COMB (@lem1584720) (@lem1584719 x)). Qed.
Lemma lem1584722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584723 (x : real) : (term127 x) = (term126 x).
Proof. exact (MK_COMB (@lem1584722) (@lem1584721 x)). Qed.
Lemma lem1584724 (z : real) (y : real) : (term25 z y) = (term25 z y).
Proof. exact (eq_refl (term25 z y)). Qed.
Lemma lem1584725 (x : real) (z : real) (y : real) : (term129 x z y) = (term149 x z y).
Proof. exact (MK_COMB (@lem1584723 x) (@lem1584724 z y)). Qed.
Lemma lem1584728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584729 (x : real) (z : real) (y : real) : (term131 x z y) = (term150 x z y).
Proof. exact (MK_COMB (@lem1584728) (@lem1584725 x z y)). Qed.
Lemma lem1584731 (x : real) (y : real) (z : real) : (term1 y x z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1584263 x y z) (@lem1584262 x y z)). Qed.
Lemma lem1584732 (x : real) (z : real) (y : real) : (term1 z x y) = (term0 x z y).
Proof. exact (@lem1584731 x z y). Qed.
Lemma lem1584733 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem1584734 (x : real) (z : real) (y : real) : (term133 z x y) = (term151 x z y).
Proof. exact (MK_COMB (@lem1584733) (@lem1584732 x z y)). Qed.
Lemma lem1584735 (x : real) (z : real) (y : real) : (term135 z x y) = (term152 x z y).
Proof. exact (MK_COMB (@lem1584729 x z y) (@lem1584734 x z y)). Qed.
Lemma lem1584737 (x : real) (y : real) : (term17 x y) = True.
Proof. exact (EQ_MP (@lem1584251 x y) (@lem1584250 x y)). Qed.
Lemma lem1584738 (x : real) (z : real) (y : real) : (term152 x z y) = True.
Proof. exact (@lem1584737 x (real_sub z y)). Qed.
Lemma lem1584739 (z : real) (x : real) (y : real) : (term135 z x y) = True.
Proof. exact (TRANS (@lem1584735 x z y) (@lem1584738 x z y)). Qed.
Lemma lem1584740 (x : real) (y : real) : (term137 x y) = term153.
Proof. exact (fun_ext (fun z : real => @lem1584739 z x y)). Qed.
Lemma lem1584741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584742 (x : real) (y : real) : (term139 x y) = term154.
Proof. exact (MK_COMB (@lem1584741) (@lem1584740 x y)). Qed.
Lemma lem1584744 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1584745 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1584744 real t). Qed.
Lemma lem1584746 : term154 = True.
Proof. exact (@lem1584745 True). Qed.
Lemma lem1584747 (x : real) (y : real) : (term139 x y) = True.
Proof. exact (TRANS (@lem1584742 x y) (@lem1584746)). Qed.
Lemma lem1584748 (x : real) : (term141 x) = term153.
Proof. exact (fun_ext (fun y : real => @lem1584747 x y)). Qed.
Lemma lem1584749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584750 (x : real) : (term143 x) = term154.
Proof. exact (MK_COMB (@lem1584749) (@lem1584748 x)). Qed.
Lemma lem1584752 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1584753 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1584752 real t). Qed.
Lemma lem1584754 : term154 = True.
Proof. exact (@lem1584753 True). Qed.
Lemma lem1584755 (x : real) : (term143 x) = True.
Proof. exact (TRANS (@lem1584750 x) (@lem1584754)). Qed.
Lemma lem1584756 : term145 = term153.
Proof. exact (fun_ext (fun x : real => @lem1584755 x)). Qed.
Lemma lem1584757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584758 : term147 = term154.
Proof. exact (MK_COMB (@lem1584757) (@lem1584756)). Qed.
Lemma lem1584760 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1584761 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1584760 real t). Qed.
Lemma lem1584762 : term154 = True.
Proof. exact (@lem1584761 True). Qed.
Lemma lem1584763 : term147 = True.
Proof. exact (TRANS (@lem1584758) (@lem1584762)). Qed.
Lemma lem1584764 : True = term147.
Proof. exact (SYM (@lem1584763)). Qed.
Lemma lem1584765 : term147.
Proof. exact (EQ_MP (@lem1584764) (@lem0)). Qed.
Lemma lem1584766 : term146.
Proof. exact (EQ_MP (@lem1584701) (@lem1584765)). Qed.

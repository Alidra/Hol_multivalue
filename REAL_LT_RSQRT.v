Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RSQRT_term_abbrevs.
Require Import POW_2_SQRT_ABS_spec.
Require Import SQRT_MONO_LT_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1962248 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1962249 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1962248 h1 x). Qed.
Lemma lem1962250 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1962251 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1962250 x) (@lem1962249 x h1)). Qed.
Lemma lem1962252 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1962251 x h1 y). Qed.
Lemma lem1962253 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1962254 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1962253 x y) (@lem1962252 x y h1)). Qed.
Lemma lem1962255 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1962256 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : term5 x y.
Proof. exact (@lem1962254 x y h1 (@lem1962255 x y h2)). Qed.
Lemma lem1962257 (x : real) (y : real) (h1 : real_lt x y) : term6 x y.
Proof. exact (fun h0 : term0 => @lem1962256 x y h0 h1). Qed.
Lemma lem1962258 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1962259 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : term5 x y.
Proof. exact (@lem1962257 x y h2 (@lem1962258 h1)). Qed.
Lemma lem1962260 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : real_lt x y => @lem1962259 x y h1 h0). Qed.
Lemma lem1962261 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1962260 x y h1). Qed.
Lemma lem1962262 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1962261 x h1). Qed.
Lemma lem1962263 : term7.
Proof. exact (fun h0 : term0 => @lem1962262 h0). Qed.
Lemma lem1962264 : term0.
Proof. exact (@lem1962263 (@lem1950431)). Qed.
Lemma lem1962265 (x : real) : term1 x.
Proof. exact (@lem1962264 x). Qed.
Lemma lem1962266 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1962267 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1962266 x) (@lem1962265 x)). Qed.
Lemma lem1962268 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1962267 x y). Qed.
Lemma lem1962269 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1962272 (x : real) (h1 : (term8 x) = (real_abs x)) : (term8 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1962273 (x : real) (h1 : (term8 x) = (real_abs x)) : (real_abs x) = (term8 x).
Proof. exact (SYM (@lem1962272 x h1)). Qed.
Lemma lem1962274 (x : real) (h1 : (real_abs x) = (term8 x)) : (real_abs x) = (term8 x).
Proof. exact (h1). Qed.
Lemma lem1962275 (x : real) (h1 : (real_abs x) = (term8 x)) : (term8 x) = (real_abs x).
Proof. exact (SYM (@lem1962274 x h1)). Qed.
Lemma lem1962276 (x : real) : ((term8 x) = (real_abs x)) = ((real_abs x) = (term8 x)).
Proof. exact (prop_ext (fun h1 : (term8 x) = (real_abs x) => @lem1962273 x h1) (fun h1 : (real_abs x) = (term8 x) => @lem1962275 x h1)). Qed.
Lemma lem1962277 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1962276 x)). Qed.
Lemma lem1962278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1962279 : term11 = term12.
Proof. exact (MK_COMB (@lem1962278) (@lem1962277)). Qed.
Lemma lem1962280 : term12.
Proof. exact (EQ_MP (@lem1962279) (@lem1902884)). Qed.
Lemma lem1962281 (x : real) : term13 x.
Proof. exact (@lem1962280 x). Qed.
Lemma lem1962282 (x : real) : (term13 x) = ((real_abs x) = (term8 x)).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1962304 (x : real) (a : real) : (term14 x a) = (term15 x a).
Proof. exact (@lem17362 (term16 x a) (real_lt x a)). Qed.
Lemma lem1962305 (a : real) (x : real) : (term16 x a) = (term17 a x).
Proof. exact (@lem1483521 a (real_abs x)). Qed.
Lemma lem1962318 (a : real) (x : real) : (term18 a x) = (term19 a x).
Proof. exact (@lem1483519 a (real_abs x)). Qed.
Lemma lem1962319 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1962320 (a : real) (x : real) : (term20 a x) = (term21 a x).
Proof. exact (MK_COMB (@lem1962319) (@lem1962318 a x)). Qed.
Lemma lem1962321 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962322 (a : real) (x : real) : (term17 a x) = (term23 a x).
Proof. exact (MK_COMB (@lem1962320 a x) (@lem1962321)). Qed.
Lemma lem1962323 (a : real) (x : real) : (term16 x a) = (term23 a x).
Proof. exact (TRANS (@lem1962305 a x) (@lem1962322 a x)). Qed.
Lemma lem1962324 (x : real) (a : real) : (term24 x a) = (term25 x a).
Proof. exact (@lem1483531 x a). Qed.
Lemma lem1962330 (x : real) (a : real) : (real_sub x a) = (term26 x a).
Proof. exact (@lem1483519 x a). Qed.
Lemma lem1962335 (a : real) (x : real) : (term26 x a) = (term27 a x).
Proof. exact (@lem1483488 (term28 a) x). Qed.
Lemma lem1962337 (a : real) (x : real) : (real_sub x a) = (term27 a x).
Proof. exact (TRANS (@lem1962330 x a) (@lem1962335 a x)). Qed.
Lemma lem1962338 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1962339 (a : real) (x : real) : (term29 x a) = (term30 a x).
Proof. exact (MK_COMB (@lem1962338) (@lem1962337 a x)). Qed.
Lemma lem1962340 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962341 (a : real) (x : real) : (term25 x a) = (term31 a x).
Proof. exact (MK_COMB (@lem1962339 a x) (@lem1962340)). Qed.
Lemma lem1962342 (a : real) (x : real) : (term24 x a) = (term31 a x).
Proof. exact (TRANS (@lem1962324 x a) (@lem1962341 a x)). Qed.
Lemma lem1962343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1962344 (a : real) (x : real) : (term32 x a) = (term33 a x).
Proof. exact (MK_COMB (@lem1962343) (@lem1962323 a x)). Qed.
Lemma lem1962345 (a : real) (x : real) : (term15 x a) = (term34 a x).
Proof. exact (MK_COMB (@lem1962344 a x) (@lem1962342 a x)). Qed.
Lemma lem1962360 (a : real) (x : real) : (term14 x a) = (term34 a x).
Proof. exact (TRANS (@lem1962304 x a) (@lem1962345 a x)). Qed.
Lemma lem1962362 (a : real) (x : real) (r : real) : (term35 a x r) = (term36 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1962363 (a : real) (x : real) : (term23 a x) = (term37 a x).
Proof. exact (@lem1962362 a x term22). Qed.
Lemma lem1962370 (x : real) : (term38 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1962373 (a : real) : (real_add a) = (real_add a).
Proof. exact (eq_refl (real_add a)). Qed.
Lemma lem1962376 (a : real) (x : real) : (term39 a x) = (real_add a x).
Proof. exact (MK_COMB (@lem1962373 a) (@lem1962370 x)). Qed.
Lemma lem1962377 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1962378 (a : real) (x : real) : (term40 a x) = (term41 a x).
Proof. exact (MK_COMB (@lem1962377) (@lem1962376 a x)). Qed.
Lemma lem1962379 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962380 (a : real) (x : real) : (term42 a x) = (term43 a x).
Proof. exact (MK_COMB (@lem1962378 a x) (@lem1962379)). Qed.
Lemma lem1962399 (a : real) (x : real) : (term44 a x) = (term44 a x).
Proof. exact (eq_refl (term44 a x)). Qed.
Lemma lem1962400 (a : real) (x : real) : (term37 a x) = (term45 a x).
Proof. exact (MK_COMB (@lem1962399 a x) (@lem1962380 a x)). Qed.
Lemma lem1962401 (a : real) (x : real) : (term23 a x) = (term45 a x).
Proof. exact (TRANS (@lem1962363 a x) (@lem1962400 a x)). Qed.
Lemma lem1962402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1962403 (a : real) (x : real) : (term33 a x) = (term46 a x).
Proof. exact (MK_COMB (@lem1962402) (@lem1962401 a x)). Qed.
Lemma lem1962404 (a : real) (x : real) : (term31 a x) = (term31 a x).
Proof. exact (eq_refl (term31 a x)). Qed.
Lemma lem1962407 (a : real) (x : real) : (term34 a x) = (term47 a x).
Proof. exact (MK_COMB (@lem1962403 a x) (@lem1962404 a x)). Qed.
Lemma lem1962408 (a : real) (x : real) (h1 : term47 a x) : term47 a x.
Proof. exact (h1). Qed.
Lemma lem1962409 (a : real) (x : real) (h1 : term47 a x) : term31 a x.
Proof. exact (proj2 (@lem1962408 a x h1)). Qed.
Lemma lem1962410 (a : real) (x : real) (h1 : term47 a x) : term45 a x.
Proof. exact (proj1 (@lem1962408 a x h1)). Qed.
Lemma lem1962412 (a : real) (x : real) (h1 : term47 a x) : term48 a x.
Proof. exact (proj1 (@lem1962410 a x h1)). Qed.
Lemma lem1962414 (n : nat) (m : nat) : (term49 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1962415 : term50 = term51.
Proof. exact (@lem1962414 (NUMERAL 0) term52). Qed.
Lemma lem1962416 : term53 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1962417 (h1 : term53 = (BIT1 0)) : term51 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1962418 : (term53 = (BIT1 0)) = (term51 = True).
Proof. exact (prop_ext (fun h1 : term53 = (BIT1 0) => @lem1962417 h1) (fun h1 : term51 = True => @lem1962416)). Qed.
Lemma lem1962419 : term51 = True.
Proof. exact (EQ_MP (@lem1962418) (@lem1962416)). Qed.
Lemma lem1962420 : term50 = True.
Proof. exact (TRANS (@lem1962415) (@lem1962419)). Qed.
Lemma lem1962421 : True = term50.
Proof. exact (SYM (@lem1962420)). Qed.
Lemma lem1962422 : term50.
Proof. exact (EQ_MP (@lem1962421) (@lem0)). Qed.
Lemma lem1962423 (a : real) (x : real) (h1 : term47 a x) : term54 a x.
Proof. exact (conj (@lem1962422) (@lem1962409 a x h1)). Qed.
Lemma lem1962425 (x : real) (y : real) : term55 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1962426 (a : real) (x : real) : term56 a x.
Proof. exact (@lem1962425 term57 (term27 a x)). Qed.
Lemma lem1962427 (a : real) (x : real) (h1 : term47 a x) : term58 a x.
Proof. exact (@lem1962426 a x (@lem1962423 a x h1)). Qed.
Lemma lem1962428 (a : real) (x : real) : (term59 a x) = (term27 a x).
Proof. exact (@lem1483460 (term27 a x)). Qed.
Lemma lem1962429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1962430 (a : real) (x : real) : (term60 a x) = (term30 a x).
Proof. exact (MK_COMB (@lem1962429) (@lem1962428 a x)). Qed.
Lemma lem1962431 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962432 (a : real) (x : real) : (term58 a x) = (term31 a x).
Proof. exact (MK_COMB (@lem1962430 a x) (@lem1962431)). Qed.
Lemma lem1962433 (a : real) (x : real) (h1 : term47 a x) : term31 a x.
Proof. exact (EQ_MP (@lem1962432 a x) (@lem1962427 a x h1)). Qed.
Lemma lem1962435 (n : nat) (m : nat) : (term49 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1962436 : term50 = term51.
Proof. exact (@lem1962435 (NUMERAL 0) term52). Qed.
Lemma lem1962437 : term53 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1962438 (h1 : term53 = (BIT1 0)) : term51 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1962439 : (term53 = (BIT1 0)) = (term51 = True).
Proof. exact (prop_ext (fun h1 : term53 = (BIT1 0) => @lem1962438 h1) (fun h1 : term51 = True => @lem1962437)). Qed.
Lemma lem1962440 : term51 = True.
Proof. exact (EQ_MP (@lem1962439) (@lem1962437)). Qed.
Lemma lem1962441 : term50 = True.
Proof. exact (TRANS (@lem1962436) (@lem1962440)). Qed.
Lemma lem1962442 : True = term50.
Proof. exact (SYM (@lem1962441)). Qed.
Lemma lem1962443 : term50.
Proof. exact (EQ_MP (@lem1962442) (@lem0)). Qed.
Lemma lem1962444 (a : real) (x : real) (h1 : term47 a x) : term61 a x.
Proof. exact (conj (@lem1962443) (@lem1962412 a x h1)). Qed.
Lemma lem1962446 (x : real) (y : real) : term62 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1962447 (a : real) (x : real) : term63 a x.
Proof. exact (@lem1962446 term57 (term26 a x)). Qed.
Lemma lem1962448 (a : real) (x : real) (h1 : term47 a x) : term64 a x.
Proof. exact (@lem1962447 a x (@lem1962444 a x h1)). Qed.
Lemma lem1962449 (a : real) (x : real) : (term65 a x) = (term26 a x).
Proof. exact (@lem1483460 (term26 a x)). Qed.
Lemma lem1962450 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1962451 (a : real) (x : real) : (term66 a x) = (term67 a x).
Proof. exact (MK_COMB (@lem1962450) (@lem1962449 a x)). Qed.
Lemma lem1962452 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962453 (a : real) (x : real) : (term64 a x) = (term48 a x).
Proof. exact (MK_COMB (@lem1962451 a x) (@lem1962452)). Qed.
Lemma lem1962454 (a : real) (x : real) (h1 : term47 a x) : term48 a x.
Proof. exact (EQ_MP (@lem1962453 a x) (@lem1962448 a x h1)). Qed.
Lemma lem1962455 (a : real) (x : real) (h1 : term47 a x) : term68 a x.
Proof. exact (conj (@lem1962454 a x h1) (@lem1962433 a x h1)). Qed.
Lemma lem1962457 (x : real) (y : real) : term69 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1962458 (a : real) (x : real) : term70 a x.
Proof. exact (@lem1962457 (term26 a x) (term27 a x)). Qed.
Lemma lem1962459 (a : real) (x : real) (h1 : term47 a x) : term71 a x.
Proof. exact (@lem1962458 a x (@lem1962455 a x h1)). Qed.
Lemma lem1962460 (a : real) (x : real) : (term72 a x) = (term73 a x).
Proof. exact (@lem1483480 a (term28 a) (term28 x) x). Qed.
Lemma lem1962461 (a : real) : (term74 a) = (term75 a).
Proof. exact (@lem1483442 term76 a). Qed.
Lemma lem1962463 (m : nat) : (term77 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1962464 : term78 = term22.
Proof. exact (@lem1962463 term52). Qed.
Lemma lem1962465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1962466 : term79 = term80.
Proof. exact (MK_COMB (@lem1962465) (@lem1962464)). Qed.
Lemma lem1962467 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1962468 (a : real) : (term75 a) = (term81 a).
Proof. exact (MK_COMB (@lem1962466) (@lem1962467 a)). Qed.
Lemma lem1962469 (a : real) : (term74 a) = (term81 a).
Proof. exact (TRANS (@lem1962461 a) (@lem1962468 a)). Qed.
Lemma lem1962470 (a : real) : (term81 a) = term22.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1962471 (a : real) : (term74 a) = term22.
Proof. exact (TRANS (@lem1962469 a) (@lem1962470 a)). Qed.
Lemma lem1962472 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1962473 (a : real) : (term82 a) = term83.
Proof. exact (MK_COMB (@lem1962472) (@lem1962471 a)). Qed.
Lemma lem1962474 (x : real) : (term84 x) = (term75 x).
Proof. exact (@lem1483440 term76 x). Qed.
Lemma lem1962476 (m : nat) : (term77 m) = term22.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1962477 : term78 = term22.
Proof. exact (@lem1962476 term52). Qed.
Lemma lem1962478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1962479 : term79 = term80.
Proof. exact (MK_COMB (@lem1962478) (@lem1962477)). Qed.
Lemma lem1962480 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1962481 (x : real) : (term75 x) = (term81 x).
Proof. exact (MK_COMB (@lem1962479) (@lem1962480 x)). Qed.
Lemma lem1962482 (x : real) : (term84 x) = (term81 x).
Proof. exact (TRANS (@lem1962474 x) (@lem1962481 x)). Qed.
Lemma lem1962483 (x : real) : (term81 x) = term22.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1962484 (x : real) : (term84 x) = term22.
Proof. exact (TRANS (@lem1962482 x) (@lem1962483 x)). Qed.
Lemma lem1962485 (a : real) (x : real) : (term73 a x) = term85.
Proof. exact (MK_COMB (@lem1962473 a) (@lem1962484 x)). Qed.
Lemma lem1962486 (a : real) (x : real) : (term72 a x) = term85.
Proof. exact (TRANS (@lem1962460 a x) (@lem1962485 a x)). Qed.
Lemma lem1962487 : term85 = term22.
Proof. exact (@lem1483448 term22). Qed.
Lemma lem1962488 (a : real) (x : real) : (term72 a x) = term22.
Proof. exact (TRANS (@lem1962486 a x) (@lem1962487)). Qed.
Lemma lem1962489 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1962490 (a : real) (x : real) : (term86 a x) = term87.
Proof. exact (MK_COMB (@lem1962489) (@lem1962488 a x)). Qed.
Lemma lem1962491 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1962492 (a : real) (x : real) : (term71 a x) = term88.
Proof. exact (MK_COMB (@lem1962490 a x) (@lem1962491)). Qed.
Lemma lem1962493 (a : real) (x : real) (h1 : term47 a x) : term88.
Proof. exact (EQ_MP (@lem1962492 a x) (@lem1962459 a x h1)). Qed.
Lemma lem1962495 (n : nat) (m : nat) : (term49 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1962496 : term88 = term89.
Proof. exact (@lem1962495 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1962497 : term89 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1962498 : term88 = False.
Proof. exact (TRANS (@lem1962496) (@lem1962497)). Qed.
Lemma lem1962499 (a : real) (x : real) (h1 : term47 a x) : False.
Proof. exact (EQ_MP (@lem1962498) (@lem1962493 a x h1)). Qed.
Lemma lem1962500 (a : real) (x : real) (h1 : term34 a x) : term34 a x.
Proof. exact (h1). Qed.
Lemma lem1962501 (a : real) (x : real) (h1 : term34 a x) : term47 a x.
Proof. exact (EQ_MP (@lem1962407 a x) (@lem1962500 a x h1)). Qed.
Lemma lem1962502 (a : real) (x : real) (h1 : term34 a x) : (term47 a x) = False.
Proof. exact (prop_ext (fun h2 : term47 a x => @lem1962499 a x h2) (fun h2 : False => @lem1962501 a x h1)). Qed.
Lemma lem1962503 (a : real) (x : real) (h1 : term34 a x) : False.
Proof. exact (EQ_MP (@lem1962502 a x h1) (@lem1962501 a x h1)). Qed.
Lemma lem1962504 (x : real) (a : real) (h1 : term14 x a) : term14 x a.
Proof. exact (h1). Qed.
Lemma lem1962505 (x : real) (a : real) (h1 : term14 x a) : term34 a x.
Proof. exact (EQ_MP (@lem1962360 a x) (@lem1962504 x a h1)). Qed.
Lemma lem1962506 (x : real) (a : real) (h1 : term14 x a) : (term34 a x) = False.
Proof. exact (prop_ext (fun h2 : term34 a x => @lem1962503 a x h2) (fun h2 : False => @lem1962505 x a h1)). Qed.
Lemma lem1962507 (x : real) (a : real) (h1 : term14 x a) : False.
Proof. exact (EQ_MP (@lem1962506 x a h1) (@lem1962505 x a h1)). Qed.
Lemma lem1962508 (x : real) (a : real) : term90 x a.
Proof. exact (fun h0 : term14 x a => @lem1962507 x a h0). Qed.
Lemma lem1962509 (x : real) (a : real) : term91 x a.
Proof. exact (@lem1386578 (term92 x a)). Qed.
Lemma lem1962510 (x : real) (a : real) : term92 x a.
Proof. exact (@lem1962509 x a (@lem1962508 x a)). Qed.
Lemma lem1962511 (x : real) (a : real) (h1 : term92 x a) : term92 x a.
Proof. exact (h1). Qed.
Lemma lem1962512 (x : real) (a : real) (h1 : term16 x a) : term16 x a.
Proof. exact (h1). Qed.
Lemma lem1962513 (x : real) (a : real) (h1 : term92 x a) (h2 : term16 x a) : real_lt x a.
Proof. exact (@lem1962511 x a h1 (@lem1962512 x a h2)). Qed.
Lemma lem1962514 (x : real) (a : real) (h1 : term16 x a) : term93 x a.
Proof. exact (fun h0 : term92 x a => @lem1962513 x a h0 h1). Qed.
Lemma lem1962515 (x : real) (a : real) (h1 : term92 x a) : term92 x a.
Proof. exact (h1). Qed.
Lemma lem1962516 (x : real) (a : real) (h1 : term92 x a) (h2 : term16 x a) : real_lt x a.
Proof. exact (@lem1962514 x a h2 (@lem1962515 x a h1)). Qed.
Lemma lem1962517 (x : real) (a : real) (h1 : term92 x a) : term92 x a.
Proof. exact (fun h0 : term16 x a => @lem1962516 x a h1 h0). Qed.
Lemma lem1962518 (x : real) (a : real) : term94 x a.
Proof. exact (fun h0 : term92 x a => @lem1962517 x a h0). Qed.
Lemma lem1962520 (x : real) (y : real) (h1 : term95 x y) : term95 x y.
Proof. exact (h1). Qed.
Lemma lem1962522 (x : real) (a : real) : term92 x a.
Proof. exact (@lem1962518 x a (@lem1962510 x a)). Qed.
Lemma lem1962523 (x : real) (y : real) : term96 x y.
Proof. exact (@lem1962522 x (sqrt y)). Qed.
Lemma lem1962525 (x : real) : (real_abs x) = (term8 x).
Proof. exact (EQ_MP (@lem1962282 x) (@lem1962281 x)). Qed.
Lemma lem1962526 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1962527 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem1962526) (@lem1962525 x)). Qed.
Lemma lem1962528 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (eq_refl (sqrt y)). Qed.
Lemma lem1962529 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1962527 x) (@lem1962528 y)). Qed.
Lemma lem1962530 (x : real) (y : real) : (term100 x y) = (term99 x y).
Proof. exact (SYM (@lem1962529 x y)). Qed.
Lemma lem1962532 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1962269 x y) (@lem1962268 x y)). Qed.
Lemma lem1962533 (x : real) (y : real) : term101 x y.
Proof. exact (@lem1962532 (term102 x) y). Qed.
Lemma lem1962542 (x : real) (y : real) : (term95 x y) = ((term95 x y) = True).
Proof. exact (@lem7 (term95 x y)). Qed.
Lemma lem1962545 (x : real) (y : real) (h1 : term95 x y) : (term95 x y) = True.
Proof. exact (EQ_MP (@lem1962542 x y) (@lem1962520 x y h1)). Qed.
Lemma lem1962546 (x : real) (y : real) (h1 : term95 x y) : True = (term95 x y).
Proof. exact (SYM (@lem1962545 x y h1)). Qed.
Lemma lem1962547 (x : real) (y : real) (h1 : term95 x y) : term95 x y.
Proof. exact (EQ_MP (@lem1962546 x y h1) (@lem0)). Qed.
Lemma lem1962548 (x : real) (y : real) (h1 : term95 x y) : term100 x y.
Proof. exact (@lem1962533 x y (@lem1962547 x y h1)). Qed.
Lemma lem1962549 (x : real) (y : real) (h1 : term95 x y) : term99 x y.
Proof. exact (EQ_MP (@lem1962530 x y) (@lem1962548 x y h1)). Qed.
Lemma lem1962550 (x : real) (y : real) (h1 : term95 x y) : term103 x y.
Proof. exact (@lem1962523 x y (@lem1962549 x y h1)). Qed.
Lemma lem1962551 (x : real) (y : real) (h1 : term95 x y) : (term95 x y) = (term103 x y).
Proof. exact (prop_ext (fun h2 : term95 x y => @lem1962550 x y h1) (fun h2 : term103 x y => @lem1962520 x y h1)). Qed.
Lemma lem1962552 (x : real) (y : real) (h1 : term95 x y) : term103 x y.
Proof. exact (EQ_MP (@lem1962551 x y h1) (@lem1962520 x y h1)). Qed.
Lemma lem1962553 (x : real) (y : real) : term104 x y.
Proof. exact (fun h0 : term95 x y => @lem1962552 x y h0). Qed.
Lemma lem1962558 (x : real) : term105 x.
Proof. exact (fun y : real => @lem1962553 x y). Qed.
Lemma lem1962563 : term106.
Proof. exact (fun x : real => @lem1962558 x). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_INV_term_abbrevs.
Require Import REAL_INV_NEG_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import real_sgn_spec.
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
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1734291 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1734292 (x : real) : (term2 x) = (term4 x).
Proof. exact (@lem1483521 term5 x). Qed.
Lemma lem1734298 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1483519 term5 x). Qed.
Lemma lem1734303 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem1483448 (term8 x)). Qed.
Lemma lem1734305 (x : real) : (term6 x) = (term8 x).
Proof. exact (TRANS (@lem1734298 x) (@lem1734303 x)). Qed.
Lemma lem1734306 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734307 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1734306) (@lem1734305 x)). Qed.
Lemma lem1734308 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734309 (x : real) : (term4 x) = (term11 x).
Proof. exact (MK_COMB (@lem1734307 x) (@lem1734308)). Qed.
Lemma lem1734310 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1734292 x) (@lem1734309 x)). Qed.
Lemma lem1734311 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1483531 term5 (real_neg x)). Qed.
Lemma lem1734318 (x : real) : (real_neg x) = (term8 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1734321 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1734322 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1734321) (@lem1734318 x)). Qed.
Lemma lem1734323 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1483519 term5 (term8 x)). Qed.
Lemma lem1734324 (x : real) : (term18 x) = (term19 x).
Proof. exact (@lem1483476 term20 term20 x). Qed.
Lemma lem1734326 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1734327 : term23 = term24.
Proof. exact (@lem1734326 term25 term25). Qed.
Lemma lem1734328 : (term26 = (BIT1 0)) = (term27 = term25).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1734329 : term27 = term25.
Proof. exact (EQ_MP (@lem1734328) (@lem940073)). Qed.
Lemma lem1734330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1734331 : term24 = term28.
Proof. exact (MK_COMB (@lem1734330) (@lem1734329)). Qed.
Lemma lem1734332 : term23 = term28.
Proof. exact (TRANS (@lem1734327) (@lem1734331)). Qed.
Lemma lem1734333 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734334 : term29 = term30.
Proof. exact (MK_COMB (@lem1734333) (@lem1734332)). Qed.
Lemma lem1734335 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1734336 (x : real) : (term19 x) = (term31 x).
Proof. exact (MK_COMB (@lem1734334) (@lem1734335 x)). Qed.
Lemma lem1734337 (x : real) : (term18 x) = (term31 x).
Proof. exact (TRANS (@lem1734324 x) (@lem1734336 x)). Qed.
Lemma lem1734338 (x : real) : (term31 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1734339 (x : real) : (term18 x) = x.
Proof. exact (TRANS (@lem1734337 x) (@lem1734338 x)). Qed.
Lemma lem1734340 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1734341 (x : real) : (term17 x) = (term33 x).
Proof. exact (MK_COMB (@lem1734340) (@lem1734339 x)). Qed.
Lemma lem1734342 (x : real) : (term33 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1734343 (x : real) : (term17 x) = x.
Proof. exact (TRANS (@lem1734341 x) (@lem1734342 x)). Qed.
Lemma lem1734344 (x : real) : (term16 x) = x.
Proof. exact (TRANS (@lem1734323 x) (@lem1734343 x)). Qed.
Lemma lem1734345 (x : real) : (term15 x) = x.
Proof. exact (TRANS (@lem1734322 x) (@lem1734344 x)). Qed.
Lemma lem1734346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1734347 (x : real) : (term34 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1734346) (@lem1734345 x)). Qed.
Lemma lem1734348 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734349 (x : real) : (term13 x) = (term35 x).
Proof. exact (MK_COMB (@lem1734347 x) (@lem1734348)). Qed.
Lemma lem1734350 (x : real) : (term12 x) = (term35 x).
Proof. exact (TRANS (@lem1734311 x) (@lem1734349 x)). Qed.
Lemma lem1734351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1734352 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1734351) (@lem1734310 x)). Qed.
Lemma lem1734353 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1734352 x) (@lem1734350 x)). Qed.
Lemma lem1734354 (x : real) : (term40 x) = (term41 x).
Proof. exact (@lem1483531 x term5). Qed.
Lemma lem1734360 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483519 x term5). Qed.
Lemma lem1734362 (x : nat) : (term44 x) = term5.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1734363 : term45 = term5.
Proof. exact (@lem1734362 term25). Qed.
Lemma lem1734364 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1734365 (x : real) : (term43 x) = (term46 x).
Proof. exact (MK_COMB (@lem1734364 x) (@lem1734363)). Qed.
Lemma lem1734366 (x : real) : (term46 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1734367 (x : real) : (term43 x) = x.
Proof. exact (TRANS (@lem1734365 x) (@lem1734366 x)). Qed.
Lemma lem1734369 (x : real) : (term42 x) = x.
Proof. exact (TRANS (@lem1734360 x) (@lem1734367 x)). Qed.
Lemma lem1734370 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1734371 (x : real) : (term47 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1734370) (@lem1734369 x)). Qed.
Lemma lem1734372 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734373 (x : real) : (term41 x) = (term35 x).
Proof. exact (MK_COMB (@lem1734371 x) (@lem1734372)). Qed.
Lemma lem1734374 (x : real) : (term40 x) = (term35 x).
Proof. exact (TRANS (@lem1734354 x) (@lem1734373 x)). Qed.
Lemma lem1734375 (x : real) : (term3 x) = (term48 x).
Proof. exact (@lem1483521 (real_neg x) term5). Qed.
Lemma lem1734376 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734383 (x : real) : (real_neg x) = (term8 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1734384 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1734385 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1734384) (@lem1734383 x)). Qed.
Lemma lem1734386 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1734385 x) (@lem1734376)). Qed.
Lemma lem1734387 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1483519 (term8 x) term5). Qed.
Lemma lem1734389 (x : nat) : (term44 x) = term5.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1734390 : term45 = term5.
Proof. exact (@lem1734389 term25). Qed.
Lemma lem1734391 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1734392 (x : real) : (term53 x) = (term55 x).
Proof. exact (MK_COMB (@lem1734391 x) (@lem1734390)). Qed.
Lemma lem1734393 (x : real) : (term55 x) = (term8 x).
Proof. exact (@lem1483450 (term8 x)). Qed.
Lemma lem1734394 (x : real) : (term53 x) = (term8 x).
Proof. exact (TRANS (@lem1734392 x) (@lem1734393 x)). Qed.
Lemma lem1734395 (x : real) : (term52 x) = (term8 x).
Proof. exact (TRANS (@lem1734387 x) (@lem1734394 x)). Qed.
Lemma lem1734396 (x : real) : (term51 x) = (term8 x).
Proof. exact (TRANS (@lem1734386 x) (@lem1734395 x)). Qed.
Lemma lem1734397 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734398 (x : real) : (term56 x) = (term10 x).
Proof. exact (MK_COMB (@lem1734397) (@lem1734396 x)). Qed.
Lemma lem1734399 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734400 (x : real) : (term48 x) = (term11 x).
Proof. exact (MK_COMB (@lem1734398 x) (@lem1734399)). Qed.
Lemma lem1734401 (x : real) : (term3 x) = (term11 x).
Proof. exact (TRANS (@lem1734375 x) (@lem1734400 x)). Qed.
Lemma lem1734402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1734403 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1734402) (@lem1734374 x)). Qed.
Lemma lem1734404 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1734403 x) (@lem1734401 x)). Qed.
Lemma lem1734405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734406 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1734405) (@lem1734353 x)). Qed.
Lemma lem1734407 (x : real) : (term1 x) = (term63 x).
Proof. exact (MK_COMB (@lem1734406 x) (@lem1734404 x)). Qed.
Lemma lem1734432 (x : real) : (term0 x) = (term63 x).
Proof. exact (TRANS (@lem1734291 x) (@lem1734407 x)). Qed.
Lemma lem1734442 (x : real) (h1 : term63 x) : term63 x.
Proof. exact (h1). Qed.
Lemma lem1734443 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1734444 (x : real) (h1 : term39 x) : term35 x.
Proof. exact (proj2 (@lem1734443 x h1)). Qed.
Lemma lem1734445 (x : real) (h1 : term39 x) : term11 x.
Proof. exact (proj1 (@lem1734443 x h1)). Qed.
Lemma lem1734447 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734448 : term65 = term66.
Proof. exact (@lem1734447 (NUMERAL 0) term25). Qed.
Lemma lem1734449 : term67 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1734450 (h1 : term67 = (BIT1 0)) : term66 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1734451 : (term67 = (BIT1 0)) = (term66 = True).
Proof. exact (prop_ext (fun h1 : term67 = (BIT1 0) => @lem1734450 h1) (fun h1 : term66 = True => @lem1734449)). Qed.
Lemma lem1734452 : term66 = True.
Proof. exact (EQ_MP (@lem1734451) (@lem1734449)). Qed.
Lemma lem1734453 : term65 = True.
Proof. exact (TRANS (@lem1734448) (@lem1734452)). Qed.
Lemma lem1734454 : True = term65.
Proof. exact (SYM (@lem1734453)). Qed.
Lemma lem1734455 : term65.
Proof. exact (EQ_MP (@lem1734454) (@lem0)). Qed.
Lemma lem1734456 (x : real) (h1 : term39 x) : term68 x.
Proof. exact (conj (@lem1734455) (@lem1734444 x h1)). Qed.
Lemma lem1734458 (x : real) (y : real) : term69 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1734459 (x : real) : term70 x.
Proof. exact (@lem1734458 term28 x). Qed.
Lemma lem1734460 (x : real) (h1 : term39 x) : term71 x.
Proof. exact (@lem1734459 x (@lem1734456 x h1)). Qed.
Lemma lem1734461 (x : real) : (term31 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1734462 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1734463 (x : real) : (term72 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1734462) (@lem1734461 x)). Qed.
Lemma lem1734464 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734465 (x : real) : (term71 x) = (term35 x).
Proof. exact (MK_COMB (@lem1734463 x) (@lem1734464)). Qed.
Lemma lem1734466 (x : real) (h1 : term39 x) : term35 x.
Proof. exact (EQ_MP (@lem1734465 x) (@lem1734460 x h1)). Qed.
Lemma lem1734468 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734469 : term65 = term66.
Proof. exact (@lem1734468 (NUMERAL 0) term25). Qed.
Lemma lem1734470 : term67 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1734471 (h1 : term67 = (BIT1 0)) : term66 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1734472 : (term67 = (BIT1 0)) = (term66 = True).
Proof. exact (prop_ext (fun h1 : term67 = (BIT1 0) => @lem1734471 h1) (fun h1 : term66 = True => @lem1734470)). Qed.
Lemma lem1734473 : term66 = True.
Proof. exact (EQ_MP (@lem1734472) (@lem1734470)). Qed.
Lemma lem1734474 : term65 = True.
Proof. exact (TRANS (@lem1734469) (@lem1734473)). Qed.
Lemma lem1734475 : True = term65.
Proof. exact (SYM (@lem1734474)). Qed.
Lemma lem1734476 : term65.
Proof. exact (EQ_MP (@lem1734475) (@lem0)). Qed.
Lemma lem1734477 (x : real) (h1 : term39 x) : term73 x.
Proof. exact (conj (@lem1734476) (@lem1734445 x h1)). Qed.
Lemma lem1734479 (x : real) (y : real) : term74 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1734480 (x : real) : term75 x.
Proof. exact (@lem1734479 term28 (term8 x)). Qed.
Lemma lem1734481 (x : real) (h1 : term39 x) : term76 x.
Proof. exact (@lem1734480 x (@lem1734477 x h1)). Qed.
Lemma lem1734482 (x : real) : (term77 x) = (term8 x).
Proof. exact (@lem1483460 (term8 x)). Qed.
Lemma lem1734483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734484 (x : real) : (term78 x) = (term10 x).
Proof. exact (MK_COMB (@lem1734483) (@lem1734482 x)). Qed.
Lemma lem1734485 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734486 (x : real) : (term76 x) = (term11 x).
Proof. exact (MK_COMB (@lem1734484 x) (@lem1734485)). Qed.
Lemma lem1734487 (x : real) (h1 : term39 x) : term11 x.
Proof. exact (EQ_MP (@lem1734486 x) (@lem1734481 x h1)). Qed.
Lemma lem1734488 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (conj (@lem1734487 x h1) (@lem1734466 x h1)). Qed.
Lemma lem1734490 (x : real) (y : real) : term79 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1734491 (x : real) : term80 x.
Proof. exact (@lem1734490 (term8 x) x). Qed.
Lemma lem1734492 (x : real) (h1 : term39 x) : term81 x.
Proof. exact (@lem1734491 x (@lem1734488 x h1)). Qed.
Lemma lem1734493 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem1483440 term20 x). Qed.
Lemma lem1734495 (m : nat) : (term84 m) = term5.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1734496 : term85 = term5.
Proof. exact (@lem1734495 term25). Qed.
Lemma lem1734497 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734498 : term86 = term87.
Proof. exact (MK_COMB (@lem1734497) (@lem1734496)). Qed.
Lemma lem1734499 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1734500 (x : real) : (term83 x) = (term88 x).
Proof. exact (MK_COMB (@lem1734498) (@lem1734499 x)). Qed.
Lemma lem1734501 (x : real) : (term82 x) = (term88 x).
Proof. exact (TRANS (@lem1734493 x) (@lem1734500 x)). Qed.
Lemma lem1734502 (x : real) : (term88 x) = term5.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1734503 (x : real) : (term82 x) = term5.
Proof. exact (TRANS (@lem1734501 x) (@lem1734502 x)). Qed.
Lemma lem1734504 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734505 (x : real) : (term89 x) = term90.
Proof. exact (MK_COMB (@lem1734504) (@lem1734503 x)). Qed.
Lemma lem1734506 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734507 (x : real) : (term81 x) = term91.
Proof. exact (MK_COMB (@lem1734505 x) (@lem1734506)). Qed.
Lemma lem1734508 (x : real) (h1 : term39 x) : term91.
Proof. exact (EQ_MP (@lem1734507 x) (@lem1734492 x h1)). Qed.
Lemma lem1734510 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734511 : term91 = term92.
Proof. exact (@lem1734510 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1734512 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1734513 : term91 = False.
Proof. exact (TRANS (@lem1734511) (@lem1734512)). Qed.
Lemma lem1734514 (x : real) (h1 : term39 x) : False.
Proof. exact (EQ_MP (@lem1734513) (@lem1734508 x h1)). Qed.
Lemma lem1734515 (x : real) (h1 : term60 x) : term60 x.
Proof. exact (h1). Qed.
Lemma lem1734516 (x : real) (h1 : term60 x) : term11 x.
Proof. exact (proj2 (@lem1734515 x h1)). Qed.
Lemma lem1734517 (x : real) (h1 : term60 x) : term35 x.
Proof. exact (proj1 (@lem1734515 x h1)). Qed.
Lemma lem1734519 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734520 : term65 = term66.
Proof. exact (@lem1734519 (NUMERAL 0) term25). Qed.
Lemma lem1734521 : term67 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1734522 (h1 : term67 = (BIT1 0)) : term66 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1734523 : (term67 = (BIT1 0)) = (term66 = True).
Proof. exact (prop_ext (fun h1 : term67 = (BIT1 0) => @lem1734522 h1) (fun h1 : term66 = True => @lem1734521)). Qed.
Lemma lem1734524 : term66 = True.
Proof. exact (EQ_MP (@lem1734523) (@lem1734521)). Qed.
Lemma lem1734525 : term65 = True.
Proof. exact (TRANS (@lem1734520) (@lem1734524)). Qed.
Lemma lem1734526 : True = term65.
Proof. exact (SYM (@lem1734525)). Qed.
Lemma lem1734527 : term65.
Proof. exact (EQ_MP (@lem1734526) (@lem0)). Qed.
Lemma lem1734528 (x : real) (h1 : term60 x) : term68 x.
Proof. exact (conj (@lem1734527) (@lem1734517 x h1)). Qed.
Lemma lem1734530 (x : real) (y : real) : term69 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1734531 (x : real) : term70 x.
Proof. exact (@lem1734530 term28 x). Qed.
Lemma lem1734532 (x : real) (h1 : term60 x) : term71 x.
Proof. exact (@lem1734531 x (@lem1734528 x h1)). Qed.
Lemma lem1734533 (x : real) : (term31 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1734534 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1734535 (x : real) : (term72 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1734534) (@lem1734533 x)). Qed.
Lemma lem1734536 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734537 (x : real) : (term71 x) = (term35 x).
Proof. exact (MK_COMB (@lem1734535 x) (@lem1734536)). Qed.
Lemma lem1734538 (x : real) (h1 : term60 x) : term35 x.
Proof. exact (EQ_MP (@lem1734537 x) (@lem1734532 x h1)). Qed.
Lemma lem1734540 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734541 : term65 = term66.
Proof. exact (@lem1734540 (NUMERAL 0) term25). Qed.
Lemma lem1734542 : term67 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1734543 (h1 : term67 = (BIT1 0)) : term66 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1734544 : (term67 = (BIT1 0)) = (term66 = True).
Proof. exact (prop_ext (fun h1 : term67 = (BIT1 0) => @lem1734543 h1) (fun h1 : term66 = True => @lem1734542)). Qed.
Lemma lem1734545 : term66 = True.
Proof. exact (EQ_MP (@lem1734544) (@lem1734542)). Qed.
Lemma lem1734546 : term65 = True.
Proof. exact (TRANS (@lem1734541) (@lem1734545)). Qed.
Lemma lem1734547 : True = term65.
Proof. exact (SYM (@lem1734546)). Qed.
Lemma lem1734548 : term65.
Proof. exact (EQ_MP (@lem1734547) (@lem0)). Qed.
Lemma lem1734549 (x : real) (h1 : term60 x) : term73 x.
Proof. exact (conj (@lem1734548) (@lem1734516 x h1)). Qed.
Lemma lem1734551 (x : real) (y : real) : term74 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1734552 (x : real) : term75 x.
Proof. exact (@lem1734551 term28 (term8 x)). Qed.
Lemma lem1734553 (x : real) (h1 : term60 x) : term76 x.
Proof. exact (@lem1734552 x (@lem1734549 x h1)). Qed.
Lemma lem1734554 (x : real) : (term77 x) = (term8 x).
Proof. exact (@lem1483460 (term8 x)). Qed.
Lemma lem1734555 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734556 (x : real) : (term78 x) = (term10 x).
Proof. exact (MK_COMB (@lem1734555) (@lem1734554 x)). Qed.
Lemma lem1734557 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734558 (x : real) : (term76 x) = (term11 x).
Proof. exact (MK_COMB (@lem1734556 x) (@lem1734557)). Qed.
Lemma lem1734559 (x : real) (h1 : term60 x) : term11 x.
Proof. exact (EQ_MP (@lem1734558 x) (@lem1734553 x h1)). Qed.
Lemma lem1734560 (x : real) (h1 : term60 x) : term39 x.
Proof. exact (conj (@lem1734559 x h1) (@lem1734538 x h1)). Qed.
Lemma lem1734562 (x : real) (y : real) : term79 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1734563 (x : real) : term80 x.
Proof. exact (@lem1734562 (term8 x) x). Qed.
Lemma lem1734564 (x : real) (h1 : term60 x) : term81 x.
Proof. exact (@lem1734563 x (@lem1734560 x h1)). Qed.
Lemma lem1734565 (x : real) : (term82 x) = (term83 x).
Proof. exact (@lem1483440 term20 x). Qed.
Lemma lem1734567 (m : nat) : (term84 m) = term5.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1734568 : term85 = term5.
Proof. exact (@lem1734567 term25). Qed.
Lemma lem1734569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734570 : term86 = term87.
Proof. exact (MK_COMB (@lem1734569) (@lem1734568)). Qed.
Lemma lem1734571 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1734572 (x : real) : (term83 x) = (term88 x).
Proof. exact (MK_COMB (@lem1734570) (@lem1734571 x)). Qed.
Lemma lem1734573 (x : real) : (term82 x) = (term88 x).
Proof. exact (TRANS (@lem1734565 x) (@lem1734572 x)). Qed.
Lemma lem1734574 (x : real) : (term88 x) = term5.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1734575 (x : real) : (term82 x) = term5.
Proof. exact (TRANS (@lem1734573 x) (@lem1734574 x)). Qed.
Lemma lem1734576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734577 (x : real) : (term89 x) = term90.
Proof. exact (MK_COMB (@lem1734576) (@lem1734575 x)). Qed.
Lemma lem1734578 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734579 (x : real) : (term81 x) = term91.
Proof. exact (MK_COMB (@lem1734577 x) (@lem1734578)). Qed.
Lemma lem1734580 (x : real) (h1 : term60 x) : term91.
Proof. exact (EQ_MP (@lem1734579 x) (@lem1734564 x h1)). Qed.
Lemma lem1734582 (n : nat) (m : nat) : (term64 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734583 : term91 = term92.
Proof. exact (@lem1734582 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1734584 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1734585 : term91 = False.
Proof. exact (TRANS (@lem1734583) (@lem1734584)). Qed.
Lemma lem1734586 (x : real) (h1 : term60 x) : False.
Proof. exact (EQ_MP (@lem1734585) (@lem1734580 x h1)). Qed.
Lemma lem1734587 (x : real) (h1 : term63 x) : False.
Proof. exact (or_elim (@lem1734442 x h1) (fun h0 : term39 x => @lem1734514 x h0) (fun h0 : term60 x => @lem1734586 x h0)). Qed.
Lemma lem1734589 (x : real) (h1 : term63 x) : term63 x.
Proof. exact (h1). Qed.
Lemma lem1734590 (x : real) (h1 : term63 x) : (term63 x) = False.
Proof. exact (prop_ext (fun h2 : term63 x => @lem1734587 x h1) (fun h2 : False => @lem1734589 x h1)). Qed.
Lemma lem1734591 (x : real) (h1 : term63 x) : False.
Proof. exact (EQ_MP (@lem1734590 x h1) (@lem1734589 x h1)). Qed.
Lemma lem1734592 (x : real) (h1 : term0 x) : term0 x.
Proof. exact (h1). Qed.
Lemma lem1734593 (x : real) (h1 : term0 x) : term63 x.
Proof. exact (EQ_MP (@lem1734432 x) (@lem1734592 x h1)). Qed.
Lemma lem1734594 (x : real) (h1 : term0 x) : (term63 x) = False.
Proof. exact (prop_ext (fun h2 : term63 x => @lem1734591 x h2) (fun h2 : False => @lem1734593 x h1)). Qed.
Lemma lem1734595 (x : real) (h1 : term0 x) : False.
Proof. exact (EQ_MP (@lem1734594 x h1) (@lem1734593 x h1)). Qed.
Lemma lem1734596 (x : real) : term93 x.
Proof. exact (fun h0 : term0 x => @lem1734595 x h0). Qed.
Lemma lem1734597 (x : real) : term94 x.
Proof. exact (@lem1386578 ((term2 x) = (term3 x))). Qed.
Lemma lem1734600 (x : real) (h1 : (term95 x) = (term96 x)) : (term95 x) = (term96 x).
Proof. exact (h1). Qed.
Lemma lem1734601 (x : real) (h1 : (term95 x) = (term96 x)) : (term96 x) = (term95 x).
Proof. exact (SYM (@lem1734600 x h1)). Qed.
Lemma lem1734602 (x : real) (h1 : (term96 x) = (term95 x)) : (term96 x) = (term95 x).
Proof. exact (h1). Qed.
Lemma lem1734603 (x : real) (h1 : (term96 x) = (term95 x)) : (term95 x) = (term96 x).
Proof. exact (SYM (@lem1734602 x h1)). Qed.
Lemma lem1734604 (x : real) : ((term95 x) = (term96 x)) = ((term96 x) = (term95 x)).
Proof. exact (prop_ext (fun h1 : (term95 x) = (term96 x) => @lem1734601 x h1) (fun h1 : (term96 x) = (term95 x) => @lem1734603 x h1)). Qed.
Lemma lem1734605 : term97 = term98.
Proof. exact (fun_ext (fun x : real => @lem1734604 x)). Qed.
Lemma lem1734606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734607 : term99 = term100.
Proof. exact (MK_COMB (@lem1734606) (@lem1734605)). Qed.
Lemma lem1734608 : term100.
Proof. exact (EQ_MP (@lem1734607) (@lem1590208)). Qed.
Lemma lem1734609 (x : real) : term101 x.
Proof. exact (@lem1734608 x). Qed.
Lemma lem1734610 (x : real) : (term101 x) = ((term96 x) = (term95 x)).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1734612 (x : real) : term102 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1734613 (x : real) : (term102 x) = ((term103 x) = (term104 x)).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1734615 (x : real) : term105 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1734616 (x : real) : (term105 x) = ((real_sgn x) = (term106 x)).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1734625 (x : real) : (real_sgn x) = (term106 x).
Proof. exact (EQ_MP (@lem1734616 x) (@lem1734615 x)). Qed.
Lemma lem1734626 (x : real) : (term107 x) = (term108 x).
Proof. exact (@lem1734625 (real_inv x)). Qed.
Lemma lem1734628 (x : real) : (term103 x) = (term104 x).
Proof. exact (EQ_MP (@lem1734613 x) (@lem1734612 x)). Qed.
Lemma lem1734629 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1734630 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1734629) (@lem1734628 x)). Qed.
Lemma lem1734631 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1734632 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1734630 x) (@lem1734631)). Qed.
Lemma lem1734634 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1734597 x (@lem1734596 x)). Qed.
Lemma lem1734635 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1734634 (real_inv x)). Qed.
Lemma lem1734637 (x : real) : (term96 x) = (term95 x).
Proof. exact (EQ_MP (@lem1734610 x) (@lem1734609 x)). Qed.
Lemma lem1734638 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem1734639 (x : real) : (term114 x) = (term116 x).
Proof. exact (MK_COMB (@lem1734638) (@lem1734637 x)). Qed.
Lemma lem1734641 (x : real) : (term103 x) = (term104 x).
Proof. exact (EQ_MP (@lem1734613 x) (@lem1734612 x)). Qed.
Lemma lem1734642 (x : real) : (term116 x) = (term3 x).
Proof. exact (@lem1734641 (real_neg x)). Qed.
Lemma lem1734643 (x : real) : (term114 x) = (term3 x).
Proof. exact (TRANS (@lem1734639 x) (@lem1734642 x)). Qed.
Lemma lem1734644 (x : real) : (term113 x) = (term3 x).
Proof. exact (TRANS (@lem1734635 x) (@lem1734643 x)). Qed.
Lemma lem1734645 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1734646 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1734645) (@lem1734644 x)). Qed.
Lemma lem1734647 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1734648 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1734646 x) (@lem1734647)). Qed.
Lemma lem1734649 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734650 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1734648 x) (@lem1734649)). Qed.
Lemma lem1734651 (x : real) : (term108 x) = (term123 x).
Proof. exact (MK_COMB (@lem1734632 x) (@lem1734650 x)). Qed.
Lemma lem1734652 (x : real) : (term107 x) = (term123 x).
Proof. exact (TRANS (@lem1734626 x) (@lem1734651 x)). Qed.
Lemma lem1734653 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1734654 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1734653) (@lem1734652 x)). Qed.
Lemma lem1734656 (x : real) : (real_sgn x) = (term106 x).
Proof. exact (EQ_MP (@lem1734616 x) (@lem1734615 x)). Qed.
Lemma lem1734658 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1734597 x (@lem1734596 x)). Qed.
Lemma lem1734659 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1734660 (x : real) : (term126 x) = (term118 x).
Proof. exact (MK_COMB (@lem1734659) (@lem1734658 x)). Qed.
Lemma lem1734661 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1734662 (x : real) : (term127 x) = (term120 x).
Proof. exact (MK_COMB (@lem1734660 x) (@lem1734661)). Qed.
Lemma lem1734663 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1734664 (x : real) : (term128 x) = (term122 x).
Proof. exact (MK_COMB (@lem1734662 x) (@lem1734663)). Qed.
Lemma lem1734665 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1734666 (x : real) : (term106 x) = (term123 x).
Proof. exact (MK_COMB (@lem1734665 x) (@lem1734664 x)). Qed.
Lemma lem1734667 (x : real) : (real_sgn x) = (term123 x).
Proof. exact (TRANS (@lem1734656 x) (@lem1734666 x)). Qed.
Lemma lem1734668 (x : real) : ((term107 x) = (real_sgn x)) = ((term123 x) = (term123 x)).
Proof. exact (MK_COMB (@lem1734654 x) (@lem1734667 x)). Qed.
Lemma lem1734670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1734671 (x : real) : (x = x) = True.
Proof. exact (@lem1734670 real x). Qed.
Lemma lem1734672 (x : real) : ((term123 x) = (term123 x)) = True.
Proof. exact (@lem1734671 (term123 x)). Qed.
Lemma lem1734673 (x : real) : ((term107 x) = (real_sgn x)) = True.
Proof. exact (TRANS (@lem1734668 x) (@lem1734672 x)). Qed.
Lemma lem1734674 : term129 = term130.
Proof. exact (fun_ext (fun x : real => @lem1734673 x)). Qed.
Lemma lem1734675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734676 : term131 = term132.
Proof. exact (MK_COMB (@lem1734675) (@lem1734674)). Qed.
Lemma lem1734678 {A : Type'} (t : Prop) : (term133 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1734679 (t : Prop) : (term134 t) = t.
Proof. exact (@lem1734678 real t). Qed.
Lemma lem1734680 : term132 = True.
Proof. exact (@lem1734679 True). Qed.
Lemma lem1734681 : term131 = True.
Proof. exact (TRANS (@lem1734676) (@lem1734680)). Qed.
Lemma lem1734682 : True = term131.
Proof. exact (SYM (@lem1734681)). Qed.
Lemma lem1734683 : term131.
Proof. exact (EQ_MP (@lem1734682) (@lem0)). Qed.

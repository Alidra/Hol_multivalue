Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_BOUNDS_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
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
Require Import thm1483512_spec.
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
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1552343 (x : real) (k : real) : (term0 x k) = (term1 x k).
Proof. exact (@lem17045 (term2 k x) (real_le x k)). Qed.
Lemma lem1552348 (x : real) (k : real) : (term3 x k) = (term3 x k).
Proof. exact (eq_refl (term3 x k)). Qed.
Lemma lem1552349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1552350 (x : real) (k : real) : (term4 x k) = (term5 x k).
Proof. exact (MK_COMB (@lem1552349) (@lem1552343 x k)). Qed.
Lemma lem1552351 (x : real) (k : real) : (term6 x k) = (term7 x k).
Proof. exact (MK_COMB (@lem1552350 x k) (@lem1552348 x k)). Qed.
Lemma lem1552356 (x : real) (k : real) : (term8 x k) = (term8 x k).
Proof. exact (eq_refl (term8 x k)). Qed.
Lemma lem1552357 (x : real) (k : real) : (term9 x k) = (term10 x k).
Proof. exact (MK_COMB (@lem1552356 x k) (@lem1552351 x k)). Qed.
Lemma lem1552358 (x : real) (k : real) : (term11 x k) = (term9 x k).
Proof. exact (@lem17646 (term12 x k) (term3 x k)). Qed.
Lemma lem1552359 (x : real) (k : real) : (term11 x k) = (term10 x k).
Proof. exact (TRANS (@lem1552358 x k) (@lem1552357 x k)). Qed.
Lemma lem1552360 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1552361 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1552360 (term17 x)). Qed.
Lemma lem1552362 (x : real) (k : real) : (term18 x k) = ((term12 x k) = (term3 x k)).
Proof. exact (eq_refl (term18 x k)). Qed.
Lemma lem1552363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1552364 (x : real) (k : real) : (term19 x k) = (term11 x k).
Proof. exact (MK_COMB (@lem1552363) (@lem1552362 x k)). Qed.
Lemma lem1552365 (x : real) (k : real) : (term19 x k) = (term10 x k).
Proof. exact (TRANS (@lem1552364 x k) (@lem1552359 x k)). Qed.
Lemma lem1552366 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun k : real => @lem1552365 x k)). Qed.
Lemma lem1552367 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552368 (x : real) : (term16 x) = (term22 x).
Proof. exact (MK_COMB (@lem1552367) (@lem1552366 x)). Qed.
Lemma lem1552369 (x : real) : (term15 x) = (term22 x).
Proof. exact (TRANS (@lem1552361 x) (@lem1552368 x)). Qed.
Lemma lem1552370 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1552371 : term23 = term24.
Proof. exact (@lem1552370 term25). Qed.
Lemma lem1552372 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1552373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1552374 (x : real) : (term28 x) = (term15 x).
Proof. exact (MK_COMB (@lem1552373) (@lem1552372 x)). Qed.
Lemma lem1552375 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1552374 x) (@lem1552369 x)). Qed.
Lemma lem1552376 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1552375 x)). Qed.
Lemma lem1552377 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552378 : term24 = term31.
Proof. exact (MK_COMB (@lem1552377) (@lem1552376)). Qed.
Lemma lem1552380 : term23 = term31.
Proof. exact (TRANS (@lem1552371) (@lem1552378)). Qed.
Lemma lem1552407 (x : real) (k : real) : (term10 x k) = (term10 x k).
Proof. exact (eq_refl (term10 x k)). Qed.
Lemma lem1552408 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun k : real => @lem1552407 x k)). Qed.
Lemma lem1552409 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552410 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1552409) (@lem1552408 x)). Qed.
Lemma lem1552411 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1552410 x)). Qed.
Lemma lem1552412 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552413 : term31 = term31.
Proof. exact (MK_COMB (@lem1552412) (@lem1552411)). Qed.
Lemma lem1552414 : term23 = term31.
Proof. exact (TRANS (@lem1552380) (@lem1552413)). Qed.
Lemma lem1552415 (x : real) (k : real) : (term2 k x) = (term32 x k).
Proof. exact (@lem1483523 x (real_neg k)). Qed.
Lemma lem1552422 (k : real) : (real_neg k) = (term33 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1552425 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1552426 (x : real) (k : real) : (term34 x k) = (term35 x k).
Proof. exact (MK_COMB (@lem1552425 x) (@lem1552422 k)). Qed.
Lemma lem1552427 (x : real) (k : real) : (term35 x k) = (term36 x k).
Proof. exact (@lem1483519 x (term33 k)). Qed.
Lemma lem1552428 (k : real) : (term37 k) = (term38 k).
Proof. exact (@lem1483476 term39 term39 k). Qed.
Lemma lem1552430 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1552431 : term42 = term43.
Proof. exact (@lem1552430 term44 term44). Qed.
Lemma lem1552432 : (term45 = (BIT1 0)) = (term46 = term44).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1552433 : term46 = term44.
Proof. exact (EQ_MP (@lem1552432) (@lem940073)). Qed.
Lemma lem1552434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1552435 : term43 = term47.
Proof. exact (MK_COMB (@lem1552434) (@lem1552433)). Qed.
Lemma lem1552436 : term42 = term47.
Proof. exact (TRANS (@lem1552431) (@lem1552435)). Qed.
Lemma lem1552437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1552438 : term48 = term49.
Proof. exact (MK_COMB (@lem1552437) (@lem1552436)). Qed.
Lemma lem1552439 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1552440 (k : real) : (term38 k) = (term50 k).
Proof. exact (MK_COMB (@lem1552438) (@lem1552439 k)). Qed.
Lemma lem1552441 (k : real) : (term37 k) = (term50 k).
Proof. exact (TRANS (@lem1552428 k) (@lem1552440 k)). Qed.
Lemma lem1552442 (k : real) : (term50 k) = k.
Proof. exact (@lem1483436 k). Qed.
Lemma lem1552443 (k : real) : (term37 k) = k.
Proof. exact (TRANS (@lem1552441 k) (@lem1552442 k)). Qed.
Lemma lem1552444 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1552445 (x : real) (k : real) : (term36 x k) = (real_add x k).
Proof. exact (MK_COMB (@lem1552444 x) (@lem1552443 k)). Qed.
Lemma lem1552446 (k : real) (x : real) : (real_add x k) = (real_add k x).
Proof. exact (@lem1483488 k x). Qed.
Lemma lem1552447 (k : real) (x : real) : (term36 x k) = (real_add k x).
Proof. exact (TRANS (@lem1552445 x k) (@lem1552446 k x)). Qed.
Lemma lem1552448 (k : real) (x : real) : (term35 x k) = (real_add k x).
Proof. exact (TRANS (@lem1552427 x k) (@lem1552447 k x)). Qed.
Lemma lem1552449 (k : real) (x : real) : (term34 x k) = (real_add k x).
Proof. exact (TRANS (@lem1552426 x k) (@lem1552448 k x)). Qed.
Lemma lem1552450 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552451 (k : real) (x : real) : (term51 x k) = (term52 k x).
Proof. exact (MK_COMB (@lem1552450) (@lem1552449 k x)). Qed.
Lemma lem1552452 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552453 (k : real) (x : real) : (term32 x k) = (term54 k x).
Proof. exact (MK_COMB (@lem1552451 k x) (@lem1552452)). Qed.
Lemma lem1552454 (k : real) (x : real) : (term2 k x) = (term54 k x).
Proof. exact (TRANS (@lem1552415 x k) (@lem1552453 k x)). Qed.
Lemma lem1552455 (k : real) (x : real) : (real_le x k) = (term55 k x).
Proof. exact (@lem1483523 k x). Qed.
Lemma lem1552468 (k : real) (x : real) : (real_sub k x) = (term56 k x).
Proof. exact (@lem1483519 k x). Qed.
Lemma lem1552469 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552470 (k : real) (x : real) : (term57 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1552469) (@lem1552468 k x)). Qed.
Lemma lem1552471 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552472 (k : real) (x : real) : (term55 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1552470 k x) (@lem1552471)). Qed.
Lemma lem1552473 (k : real) (x : real) : (real_le x k) = (term59 k x).
Proof. exact (TRANS (@lem1552455 k x) (@lem1552472 k x)). Qed.
Lemma lem1552474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1552475 (k : real) (x : real) : (term60 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1552474) (@lem1552454 k x)). Qed.
Lemma lem1552476 (k : real) (x : real) : (term12 x k) = (term62 k x).
Proof. exact (MK_COMB (@lem1552475 k x) (@lem1552473 k x)). Qed.
Lemma lem1552477 (x : real) (k : real) : (term63 x k) = (term64 x k).
Proof. exact (@lem1483533 (real_abs x) k). Qed.
Lemma lem1552483 (x : real) (k : real) : (term65 x k) = (term66 x k).
Proof. exact (@lem1483519 (real_abs x) k). Qed.
Lemma lem1552488 (k : real) (x : real) : (term66 x k) = (term67 k x).
Proof. exact (@lem1483488 (term33 k) (real_abs x)). Qed.
Lemma lem1552490 (k : real) (x : real) : (term65 x k) = (term67 k x).
Proof. exact (TRANS (@lem1552483 x k) (@lem1552488 k x)). Qed.
Lemma lem1552491 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552492 (k : real) (x : real) : (term68 x k) = (term69 k x).
Proof. exact (MK_COMB (@lem1552491) (@lem1552490 k x)). Qed.
Lemma lem1552493 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552494 (k : real) (x : real) : (term64 x k) = (term70 k x).
Proof. exact (MK_COMB (@lem1552492 k x) (@lem1552493)). Qed.
Lemma lem1552495 (k : real) (x : real) : (term63 x k) = (term70 k x).
Proof. exact (TRANS (@lem1552477 x k) (@lem1552494 k x)). Qed.
Lemma lem1552496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1552497 (k : real) (x : real) : (term71 x k) = (term72 k x).
Proof. exact (MK_COMB (@lem1552496) (@lem1552476 k x)). Qed.
Lemma lem1552498 (k : real) (x : real) : (term73 x k) = (term74 k x).
Proof. exact (MK_COMB (@lem1552497 k x) (@lem1552495 k x)). Qed.
Lemma lem1552499 (k : real) (x : real) : (term75 k x) = (term76 k x).
Proof. exact (@lem1483533 (real_neg k) x). Qed.
Lemma lem1552500 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1552507 (k : real) : (real_neg k) = (term33 k).
Proof. exact (@lem1483512 k). Qed.
Lemma lem1552508 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1552509 (k : real) : (term77 k) = (term78 k).
Proof. exact (MK_COMB (@lem1552508) (@lem1552507 k)). Qed.
Lemma lem1552510 (k : real) (x : real) : (term79 k x) = (term80 k x).
Proof. exact (MK_COMB (@lem1552509 k) (@lem1552500 x)). Qed.
Lemma lem1552517 (k : real) (x : real) : (term80 k x) = (term81 k x).
Proof. exact (@lem1483519 (term33 k) x). Qed.
Lemma lem1552518 (k : real) (x : real) : (term79 k x) = (term81 k x).
Proof. exact (TRANS (@lem1552510 k x) (@lem1552517 k x)). Qed.
Lemma lem1552519 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552520 (k : real) (x : real) : (term82 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1552519) (@lem1552518 k x)). Qed.
Lemma lem1552521 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552522 (k : real) (x : real) : (term76 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1552520 k x) (@lem1552521)). Qed.
Lemma lem1552523 (k : real) (x : real) : (term75 k x) = (term84 k x).
Proof. exact (TRANS (@lem1552499 k x) (@lem1552522 k x)). Qed.
Lemma lem1552524 (x : real) (k : real) : (term85 x k) = (term86 x k).
Proof. exact (@lem1483533 x k). Qed.
Lemma lem1552530 (x : real) (k : real) : (real_sub x k) = (term56 x k).
Proof. exact (@lem1483519 x k). Qed.
Lemma lem1552535 (k : real) (x : real) : (term56 x k) = (term87 k x).
Proof. exact (@lem1483488 (term33 k) x). Qed.
Lemma lem1552537 (k : real) (x : real) : (real_sub x k) = (term87 k x).
Proof. exact (TRANS (@lem1552530 x k) (@lem1552535 k x)). Qed.
Lemma lem1552538 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1552539 (k : real) (x : real) : (term88 x k) = (term89 k x).
Proof. exact (MK_COMB (@lem1552538) (@lem1552537 k x)). Qed.
Lemma lem1552540 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552541 (k : real) (x : real) : (term86 x k) = (term90 k x).
Proof. exact (MK_COMB (@lem1552539 k x) (@lem1552540)). Qed.
Lemma lem1552542 (k : real) (x : real) : (term85 x k) = (term90 k x).
Proof. exact (TRANS (@lem1552524 x k) (@lem1552541 k x)). Qed.
Lemma lem1552543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552544 (k : real) (x : real) : (term91 k x) = (term92 k x).
Proof. exact (MK_COMB (@lem1552543) (@lem1552523 k x)). Qed.
Lemma lem1552545 (k : real) (x : real) : (term1 x k) = (term93 k x).
Proof. exact (MK_COMB (@lem1552544 k x) (@lem1552542 k x)). Qed.
Lemma lem1552546 (k : real) (x : real) : (term3 x k) = (term94 k x).
Proof. exact (@lem1483523 k (real_abs x)). Qed.
Lemma lem1552559 (k : real) (x : real) : (term95 k x) = (term96 k x).
Proof. exact (@lem1483519 k (real_abs x)). Qed.
Lemma lem1552560 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552561 (k : real) (x : real) : (term97 k x) = (term98 k x).
Proof. exact (MK_COMB (@lem1552560) (@lem1552559 k x)). Qed.
Lemma lem1552562 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552563 (k : real) (x : real) : (term94 k x) = (term99 k x).
Proof. exact (MK_COMB (@lem1552561 k x) (@lem1552562)). Qed.
Lemma lem1552564 (k : real) (x : real) : (term3 x k) = (term99 k x).
Proof. exact (TRANS (@lem1552546 k x) (@lem1552563 k x)). Qed.
Lemma lem1552565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1552566 (k : real) (x : real) : (term5 x k) = (term100 k x).
Proof. exact (MK_COMB (@lem1552565) (@lem1552545 k x)). Qed.
Lemma lem1552567 (k : real) (x : real) : (term7 x k) = (term101 k x).
Proof. exact (MK_COMB (@lem1552566 k x) (@lem1552564 k x)). Qed.
Lemma lem1552568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552569 (k : real) (x : real) : (term8 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1552568) (@lem1552498 k x)). Qed.
Lemma lem1552570 (k : real) (x : real) : (term10 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1552569 k x) (@lem1552567 k x)). Qed.
Lemma lem1552571 (x : real) : (term21 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1552570 k x)). Qed.
Lemma lem1552572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552573 (x : real) : (term22 x) = (term105 x).
Proof. exact (MK_COMB (@lem1552572) (@lem1552571 x)). Qed.
Lemma lem1552574 : term30 = term106.
Proof. exact (fun_ext (fun x : real => @lem1552573 x)). Qed.
Lemma lem1552575 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552576 : term31 = term107.
Proof. exact (MK_COMB (@lem1552575) (@lem1552574)). Qed.
Lemma lem1552577 : term23 = term107.
Proof. exact (TRANS (@lem1552414) (@lem1552576)). Qed.
Lemma lem1552583 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1552584 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1552583 real P Q). Qed.
Lemma lem1552585 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem1552584 (term114 x) (term115 x)). Qed.
Lemma lem1552586 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1552587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552588 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1552587) (@lem1552586 k x)). Qed.
Lemma lem1552589 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1552590 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1552588 k x) (@lem1552589 k x)). Qed.
Lemma lem1552591 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1552590 k x)). Qed.
Lemma lem1552592 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552593 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1552592) (@lem1552591 x)). Qed.
Lemma lem1552594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1552595 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1552594) (@lem1552593 x)). Qed.
Lemma lem1552596 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1552597 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1552596 k x)). Qed.
Lemma lem1552598 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552599 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1552598) (@lem1552597 x)). Qed.
Lemma lem1552600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552601 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1552600) (@lem1552599 x)). Qed.
Lemma lem1552602 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1552603 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1552602 k x)). Qed.
Lemma lem1552604 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552605 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1552604) (@lem1552603 x)). Qed.
Lemma lem1552606 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1552601 x) (@lem1552605 x)). Qed.
Lemma lem1552607 (x : real) : ((term112 x) = (term113 x)) = ((term105 x) = (term131 x)).
Proof. exact (MK_COMB (@lem1552595 x) (@lem1552606 x)). Qed.
Lemma lem1552608 (x : real) : (term105 x) = (term131 x).
Proof. exact (EQ_MP (@lem1552607 x) (@lem1552585 x)). Qed.
Lemma lem1552705 : term106 = term132.
Proof. exact (fun_ext (fun x : real => @lem1552608 x)). Qed.
Lemma lem1552706 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552707 : term107 = term133.
Proof. exact (MK_COMB (@lem1552706) (@lem1552705)). Qed.
Lemma lem1552709 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1552710 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem1552709 real P Q). Qed.
Lemma lem1552711 : term134 = term135.
Proof. exact (@lem1552710 term136 term137). Qed.
Lemma lem1552712 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1552713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552714 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1552713) (@lem1552712 x)). Qed.
Lemma lem1552715 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1552716 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1552714 x) (@lem1552715 x)). Qed.
Lemma lem1552717 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1552716 x)). Qed.
Lemma lem1552718 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552719 : term134 = term133.
Proof. exact (MK_COMB (@lem1552718) (@lem1552717)). Qed.
Lemma lem1552720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1552721 : term143 = term144.
Proof. exact (MK_COMB (@lem1552720) (@lem1552719)). Qed.
Lemma lem1552722 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1552723 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1552722 x)). Qed.
Lemma lem1552724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552725 : term146 = term147.
Proof. exact (MK_COMB (@lem1552724) (@lem1552723)). Qed.
Lemma lem1552726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552727 : term148 = term149.
Proof. exact (MK_COMB (@lem1552726) (@lem1552725)). Qed.
Lemma lem1552728 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1552729 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1552728 x)). Qed.
Lemma lem1552730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552731 : term151 = term152.
Proof. exact (MK_COMB (@lem1552730) (@lem1552729)). Qed.
Lemma lem1552732 : term135 = term153.
Proof. exact (MK_COMB (@lem1552727) (@lem1552731)). Qed.
Lemma lem1552733 : (term134 = term135) = (term133 = term153).
Proof. exact (MK_COMB (@lem1552721) (@lem1552732)). Qed.
Lemma lem1552734 : term133 = term153.
Proof. exact (EQ_MP (@lem1552733) (@lem1552711)). Qed.
Lemma lem1552839 : term107 = term153.
Proof. exact (TRANS (@lem1552707) (@lem1552734)). Qed.
Lemma lem1552841 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1552842 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1552841 real P Q). Qed.
Lemma lem1552843 : term135 = term134.
Proof. exact (@lem1552842 term136 term137). Qed.
Lemma lem1552844 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1552845 : term145 = term136.
Proof. exact (fun_ext (fun x : real => @lem1552844 x)). Qed.
Lemma lem1552846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552847 : term146 = term147.
Proof. exact (MK_COMB (@lem1552846) (@lem1552845)). Qed.
Lemma lem1552848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552849 : term148 = term149.
Proof. exact (MK_COMB (@lem1552848) (@lem1552847)). Qed.
Lemma lem1552850 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1552851 : term150 = term137.
Proof. exact (fun_ext (fun x : real => @lem1552850 x)). Qed.
Lemma lem1552852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552853 : term151 = term152.
Proof. exact (MK_COMB (@lem1552852) (@lem1552851)). Qed.
Lemma lem1552854 : term135 = term153.
Proof. exact (MK_COMB (@lem1552849) (@lem1552853)). Qed.
Lemma lem1552855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1552856 : term154 = term155.
Proof. exact (MK_COMB (@lem1552855) (@lem1552854)). Qed.
Lemma lem1552857 (x : real) : (term138 x) = (term125 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1552858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552859 (x : real) : (term139 x) = (term127 x).
Proof. exact (MK_COMB (@lem1552858) (@lem1552857 x)). Qed.
Lemma lem1552860 (x : real) : (term140 x) = (term130 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1552861 (x : real) : (term141 x) = (term131 x).
Proof. exact (MK_COMB (@lem1552859 x) (@lem1552860 x)). Qed.
Lemma lem1552862 : term142 = term132.
Proof. exact (fun_ext (fun x : real => @lem1552861 x)). Qed.
Lemma lem1552863 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552864 : term134 = term133.
Proof. exact (MK_COMB (@lem1552863) (@lem1552862)). Qed.
Lemma lem1552865 : (term135 = term134) = (term153 = term133).
Proof. exact (MK_COMB (@lem1552856) (@lem1552864)). Qed.
Lemma lem1552866 : term153 = term133.
Proof. exact (EQ_MP (@lem1552865) (@lem1552843)). Qed.
Lemma lem1552868 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1552869 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem1552868 real P Q). Qed.
Lemma lem1552870 (x : real) : (term113 x) = (term112 x).
Proof. exact (@lem1552869 (term114 x) (term115 x)). Qed.
Lemma lem1552871 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1552872 (x : real) : (term123 x) = (term114 x).
Proof. exact (fun_ext (fun k : real => @lem1552871 k x)). Qed.
Lemma lem1552873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552874 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1552873) (@lem1552872 x)). Qed.
Lemma lem1552875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552876 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1552875) (@lem1552874 x)). Qed.
Lemma lem1552877 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1552878 (x : real) : (term128 x) = (term115 x).
Proof. exact (fun_ext (fun k : real => @lem1552877 k x)). Qed.
Lemma lem1552879 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552880 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1552879) (@lem1552878 x)). Qed.
Lemma lem1552881 (x : real) : (term113 x) = (term131 x).
Proof. exact (MK_COMB (@lem1552876 x) (@lem1552880 x)). Qed.
Lemma lem1552882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1552883 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1552882) (@lem1552881 x)). Qed.
Lemma lem1552884 (k : real) (x : real) : (term116 x k) = (term74 k x).
Proof. exact (eq_refl (term116 x k)). Qed.
Lemma lem1552885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552886 (k : real) (x : real) : (term117 x k) = (term102 k x).
Proof. exact (MK_COMB (@lem1552885) (@lem1552884 k x)). Qed.
Lemma lem1552887 (k : real) (x : real) : (term118 x k) = (term101 k x).
Proof. exact (eq_refl (term118 x k)). Qed.
Lemma lem1552888 (k : real) (x : real) : (term119 x k) = (term103 k x).
Proof. exact (MK_COMB (@lem1552886 k x) (@lem1552887 k x)). Qed.
Lemma lem1552889 (x : real) : (term120 x) = (term104 x).
Proof. exact (fun_ext (fun k : real => @lem1552888 k x)). Qed.
Lemma lem1552890 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552891 (x : real) : (term112 x) = (term105 x).
Proof. exact (MK_COMB (@lem1552890) (@lem1552889 x)). Qed.
Lemma lem1552892 (x : real) : ((term113 x) = (term112 x)) = ((term131 x) = (term105 x)).
Proof. exact (MK_COMB (@lem1552883 x) (@lem1552891 x)). Qed.
Lemma lem1552893 (x : real) : (term131 x) = (term105 x).
Proof. exact (EQ_MP (@lem1552892 x) (@lem1552870 x)). Qed.
Lemma lem1552894 : term132 = term106.
Proof. exact (fun_ext (fun x : real => @lem1552893 x)). Qed.
Lemma lem1552895 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552896 : term133 = term107.
Proof. exact (MK_COMB (@lem1552895) (@lem1552894)). Qed.
Lemma lem1552897 : term153 = term107.
Proof. exact (TRANS (@lem1552866) (@lem1552896)). Qed.
Lemma lem1552898 : term107 = term107.
Proof. exact (TRANS (@lem1552839) (@lem1552897)). Qed.
Lemma lem1552901 : term23 = term107.
Proof. exact (TRANS (@lem1552577) (@lem1552898)). Qed.
Lemma lem1552918 (k : real) (x : real) : (term101 k x) = (term158 k x).
Proof. exact (@lem19367 (term84 k x) (term90 k x) (term99 k x)). Qed.
Lemma lem1552933 (k : real) (x : real) : (term102 k x) = (term102 k x).
Proof. exact (eq_refl (term102 k x)). Qed.
Lemma lem1552934 (k : real) (x : real) : (term103 k x) = (term159 k x).
Proof. exact (MK_COMB (@lem1552933 k x) (@lem1552918 k x)). Qed.
Lemma lem1552935 (x : real) : (term104 x) = (term160 x).
Proof. exact (fun_ext (fun k : real => @lem1552934 k x)). Qed.
Lemma lem1552936 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552937 (x : real) : (term105 x) = (term161 x).
Proof. exact (MK_COMB (@lem1552936) (@lem1552935 x)). Qed.
Lemma lem1552938 : term106 = term162.
Proof. exact (fun_ext (fun x : real => @lem1552937 x)). Qed.
Lemma lem1552939 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1552940 : term107 = term163.
Proof. exact (MK_COMB (@lem1552939) (@lem1552938)). Qed.
Lemma lem1552941 : term23 = term163.
Proof. exact (TRANS (@lem1552901) (@lem1552940)). Qed.
Lemma lem1552943 (k : real) (x : real) : (term164 k x) = (term74 k x).
Proof. exact (eq_refl (term164 k x)). Qed.
Lemma lem1552944 (k : real) (x : real) : (term74 k x) = (term164 k x).
Proof. exact (SYM (@lem1552943 k x)). Qed.
Lemma lem1552945 (k : real) (x : real) : (term164 k x) = (term165 k x).
Proof. exact (@lem1482981 (term166 x k) x). Qed.
Lemma lem1552946 (k : real) (x : real) : (term74 k x) = (term165 k x).
Proof. exact (TRANS (@lem1552944 k x) (@lem1552945 k x)). Qed.
Lemma lem1552947 (k : real) (x : real) : (term167 k x) = (term168 k x).
Proof. exact (eq_refl (term167 k x)). Qed.
Lemma lem1552948 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1552949 (k : real) (x : real) : (term170 k x) = (term171 k x).
Proof. exact (MK_COMB (@lem1552948 x) (@lem1552947 k x)). Qed.
Lemma lem1552950 (k : real) (x : real) : (term172 k x) = (term173 k x).
Proof. exact (eq_refl (term172 k x)). Qed.
Lemma lem1552951 (x : real) : (term174 x) = (term174 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1552952 (k : real) (x : real) : (term175 k x) = (term176 k x).
Proof. exact (MK_COMB (@lem1552951 x) (@lem1552950 k x)). Qed.
Lemma lem1552953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1552954 (k : real) (x : real) : (term177 k x) = (term178 k x).
Proof. exact (MK_COMB (@lem1552953) (@lem1552952 k x)). Qed.
Lemma lem1552955 (k : real) (x : real) : (term165 k x) = (term179 k x).
Proof. exact (MK_COMB (@lem1552954 k x) (@lem1552949 k x)). Qed.
Lemma lem1552956 (k : real) (x : real) : (term180 k x) = (term180 k x).
Proof. exact (eq_refl (term180 k x)). Qed.
Lemma lem1552957 (k : real) (x : real) : ((term74 k x) = (term165 k x)) = ((term74 k x) = (term179 k x)).
Proof. exact (MK_COMB (@lem1552956 k x) (@lem1552955 k x)). Qed.
Lemma lem1552958 (k : real) (x : real) : (term74 k x) = (term179 k x).
Proof. exact (EQ_MP (@lem1552957 k x) (@lem1552946 k x)). Qed.
Lemma lem1552959 (x : real) : (term181 x) = (term182 x).
Proof. exact (@lem1483527 x term53). Qed.
Lemma lem1552965 (x : real) : (term183 x) = (term184 x).
Proof. exact (@lem1483519 x term53). Qed.
Lemma lem1552967 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1552968 : term186 = term53.
Proof. exact (@lem1552967 term44). Qed.
Lemma lem1552969 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1552970 (x : real) : (term184 x) = (term187 x).
Proof. exact (MK_COMB (@lem1552969 x) (@lem1552968)). Qed.
Lemma lem1552971 (x : real) : (term187 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1552972 (x : real) : (term184 x) = x.
Proof. exact (TRANS (@lem1552970 x) (@lem1552971 x)). Qed.
Lemma lem1552974 (x : real) : (term183 x) = x.
Proof. exact (TRANS (@lem1552965 x) (@lem1552972 x)). Qed.
Lemma lem1552975 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1552976 (x : real) : (term188 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1552975) (@lem1552974 x)). Qed.
Lemma lem1552977 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1552978 (x : real) : (term182 x) = (term181 x).
Proof. exact (MK_COMB (@lem1552976 x) (@lem1552977)). Qed.
Lemma lem1552979 (x : real) : (term181 x) = (term181 x).
Proof. exact (TRANS (@lem1552959 x) (@lem1552978 x)). Qed.
Lemma lem1552980 (k : real) (x : real) : (term54 k x) = (term189 k x).
Proof. exact (@lem1483527 (real_add k x) term53). Qed.
Lemma lem1552992 (k : real) (x : real) : (term190 k x) = (term191 k x).
Proof. exact (@lem1483519 (real_add k x) term53). Qed.
Lemma lem1552994 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1552995 : term186 = term53.
Proof. exact (@lem1552994 term44). Qed.
Lemma lem1552996 (k : real) (x : real) : (term192 k x) = (term192 k x).
Proof. exact (eq_refl (term192 k x)). Qed.
Lemma lem1552997 (k : real) (x : real) : (term191 k x) = (term193 k x).
Proof. exact (MK_COMB (@lem1552996 k x) (@lem1552995)). Qed.
Lemma lem1552998 (k : real) (x : real) : (term193 k x) = (real_add k x).
Proof. exact (@lem1483450 (real_add k x)). Qed.
Lemma lem1552999 (k : real) (x : real) : (term191 k x) = (real_add k x).
Proof. exact (TRANS (@lem1552997 k x) (@lem1552998 k x)). Qed.
Lemma lem1553001 (k : real) (x : real) : (term190 k x) = (real_add k x).
Proof. exact (TRANS (@lem1552992 k x) (@lem1552999 k x)). Qed.
Lemma lem1553002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553003 (k : real) (x : real) : (term194 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1553002) (@lem1553001 k x)). Qed.
Lemma lem1553004 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553005 (k : real) (x : real) : (term189 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1553003 k x) (@lem1553004)). Qed.
Lemma lem1553006 (k : real) (x : real) : (term54 k x) = (term54 k x).
Proof. exact (TRANS (@lem1552980 k x) (@lem1553005 k x)). Qed.
Lemma lem1553007 (k : real) (x : real) : (term59 k x) = (term195 k x).
Proof. exact (@lem1483527 (term56 k x) term53). Qed.
Lemma lem1553025 (k : real) (x : real) : (term196 k x) = (term197 k x).
Proof. exact (@lem1483519 (term56 k x) term53). Qed.
Lemma lem1553027 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1553028 : term186 = term53.
Proof. exact (@lem1553027 term44). Qed.
Lemma lem1553029 (k : real) (x : real) : (term198 k x) = (term198 k x).
Proof. exact (eq_refl (term198 k x)). Qed.
Lemma lem1553030 (k : real) (x : real) : (term197 k x) = (term199 k x).
Proof. exact (MK_COMB (@lem1553029 k x) (@lem1553028)). Qed.
Lemma lem1553031 (k : real) (x : real) : (term199 k x) = (term56 k x).
Proof. exact (@lem1483450 (term56 k x)). Qed.
Lemma lem1553032 (k : real) (x : real) : (term197 k x) = (term56 k x).
Proof. exact (TRANS (@lem1553030 k x) (@lem1553031 k x)). Qed.
Lemma lem1553034 (k : real) (x : real) : (term196 k x) = (term56 k x).
Proof. exact (TRANS (@lem1553025 k x) (@lem1553032 k x)). Qed.
Lemma lem1553035 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553036 (k : real) (x : real) : (term200 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1553035) (@lem1553034 k x)). Qed.
Lemma lem1553037 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553038 (k : real) (x : real) : (term195 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1553036 k x) (@lem1553037)). Qed.
Lemma lem1553039 (k : real) (x : real) : (term59 k x) = (term59 k x).
Proof. exact (TRANS (@lem1553007 k x) (@lem1553038 k x)). Qed.
Lemma lem1553040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553041 (k : real) (x : real) : (term61 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1553040) (@lem1553006 k x)). Qed.
Lemma lem1553042 (k : real) (x : real) : (term62 k x) = (term62 k x).
Proof. exact (MK_COMB (@lem1553041 k x) (@lem1553039 k x)). Qed.
Lemma lem1553043 (k : real) (x : real) : (term90 k x) = (term201 k x).
Proof. exact (@lem1483525 (term87 k x) term53). Qed.
Lemma lem1553061 (k : real) (x : real) : (term202 k x) = (term203 k x).
Proof. exact (@lem1483519 (term87 k x) term53). Qed.
Lemma lem1553063 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1553064 : term186 = term53.
Proof. exact (@lem1553063 term44). Qed.
Lemma lem1553065 (k : real) (x : real) : (term204 k x) = (term204 k x).
Proof. exact (eq_refl (term204 k x)). Qed.
Lemma lem1553066 (k : real) (x : real) : (term203 k x) = (term205 k x).
Proof. exact (MK_COMB (@lem1553065 k x) (@lem1553064)). Qed.
Lemma lem1553067 (k : real) (x : real) : (term205 k x) = (term87 k x).
Proof. exact (@lem1483450 (term87 k x)). Qed.
Lemma lem1553068 (k : real) (x : real) : (term203 k x) = (term87 k x).
Proof. exact (TRANS (@lem1553066 k x) (@lem1553067 k x)). Qed.
Lemma lem1553070 (k : real) (x : real) : (term202 k x) = (term87 k x).
Proof. exact (TRANS (@lem1553061 k x) (@lem1553068 k x)). Qed.
Lemma lem1553071 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553072 (k : real) (x : real) : (term206 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1553071) (@lem1553070 k x)). Qed.
Lemma lem1553073 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553074 (k : real) (x : real) : (term201 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1553072 k x) (@lem1553073)). Qed.
Lemma lem1553075 (k : real) (x : real) : (term90 k x) = (term90 k x).
Proof. exact (TRANS (@lem1553043 k x) (@lem1553074 k x)). Qed.
Lemma lem1553076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553077 (k : real) (x : real) : (term72 k x) = (term72 k x).
Proof. exact (MK_COMB (@lem1553076) (@lem1553042 k x)). Qed.
Lemma lem1553078 (k : real) (x : real) : (term173 k x) = (term173 k x).
Proof. exact (MK_COMB (@lem1553077 k x) (@lem1553075 k x)). Qed.
Lemma lem1553079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553080 (x : real) : (term174 x) = (term174 x).
Proof. exact (MK_COMB (@lem1553079) (@lem1552979 x)). Qed.
Lemma lem1553081 (k : real) (x : real) : (term176 k x) = (term176 k x).
Proof. exact (MK_COMB (@lem1553080 x) (@lem1553078 k x)). Qed.
Lemma lem1553082 (x : real) : (term207 x) = (term208 x).
Proof. exact (@lem1483525 term53 x). Qed.
Lemma lem1553088 (x : real) : (term209 x) = (term210 x).
Proof. exact (@lem1483519 term53 x). Qed.
Lemma lem1553093 (x : real) : (term210 x) = (term33 x).
Proof. exact (@lem1483448 (term33 x)). Qed.
Lemma lem1553095 (x : real) : (term209 x) = (term33 x).
Proof. exact (TRANS (@lem1553088 x) (@lem1553093 x)). Qed.
Lemma lem1553096 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553097 (x : real) : (term211 x) = (term212 x).
Proof. exact (MK_COMB (@lem1553096) (@lem1553095 x)). Qed.
Lemma lem1553098 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553099 (x : real) : (term208 x) = (term213 x).
Proof. exact (MK_COMB (@lem1553097 x) (@lem1553098)). Qed.
Lemma lem1553100 (x : real) : (term207 x) = (term213 x).
Proof. exact (TRANS (@lem1553082 x) (@lem1553099 x)). Qed.
Lemma lem1553101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553102 (k : real) (x : real) : (term61 k x) = (term61 k x).
Proof. exact (MK_COMB (@lem1553101) (@lem1553006 k x)). Qed.
Lemma lem1553103 (k : real) (x : real) : (term62 k x) = (term62 k x).
Proof. exact (MK_COMB (@lem1553102 k x) (@lem1553039 k x)). Qed.
Lemma lem1553104 (k : real) (x : real) : (term214 k x) = (term215 k x).
Proof. exact (@lem1483525 (term216 k x) term53). Qed.
Lemma lem1553105 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553112 (x : real) : (real_neg x) = (term33 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1553121 (k : real) : (term217 k) = (term217 k).
Proof. exact (eq_refl (term217 k)). Qed.
Lemma lem1553124 (k : real) (x : real) : (term216 k x) = (term81 k x).
Proof. exact (MK_COMB (@lem1553121 k) (@lem1553112 x)). Qed.
Lemma lem1553125 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1553126 (k : real) (x : real) : (term218 k x) = (term219 k x).
Proof. exact (MK_COMB (@lem1553125) (@lem1553124 k x)). Qed.
Lemma lem1553127 (k : real) (x : real) : (term220 k x) = (term221 k x).
Proof. exact (MK_COMB (@lem1553126 k x) (@lem1553105)). Qed.
Lemma lem1553128 (k : real) (x : real) : (term221 k x) = (term222 k x).
Proof. exact (@lem1483519 (term81 k x) term53). Qed.
Lemma lem1553130 (x : nat) : (term185 x) = term53.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1553131 : term186 = term53.
Proof. exact (@lem1553130 term44). Qed.
Lemma lem1553132 (k : real) (x : real) : (term223 k x) = (term223 k x).
Proof. exact (eq_refl (term223 k x)). Qed.
Lemma lem1553133 (k : real) (x : real) : (term222 k x) = (term224 k x).
Proof. exact (MK_COMB (@lem1553132 k x) (@lem1553131)). Qed.
Lemma lem1553134 (k : real) (x : real) : (term224 k x) = (term81 k x).
Proof. exact (@lem1483450 (term81 k x)). Qed.
Lemma lem1553135 (k : real) (x : real) : (term222 k x) = (term81 k x).
Proof. exact (TRANS (@lem1553133 k x) (@lem1553134 k x)). Qed.
Lemma lem1553136 (k : real) (x : real) : (term221 k x) = (term81 k x).
Proof. exact (TRANS (@lem1553128 k x) (@lem1553135 k x)). Qed.
Lemma lem1553137 (k : real) (x : real) : (term220 k x) = (term81 k x).
Proof. exact (TRANS (@lem1553127 k x) (@lem1553136 k x)). Qed.
Lemma lem1553138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553139 (k : real) (x : real) : (term225 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1553138) (@lem1553137 k x)). Qed.
Lemma lem1553140 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553141 (k : real) (x : real) : (term215 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1553139 k x) (@lem1553140)). Qed.
Lemma lem1553142 (k : real) (x : real) : (term214 k x) = (term84 k x).
Proof. exact (TRANS (@lem1553104 k x) (@lem1553141 k x)). Qed.
Lemma lem1553143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553144 (k : real) (x : real) : (term72 k x) = (term72 k x).
Proof. exact (MK_COMB (@lem1553143) (@lem1553103 k x)). Qed.
Lemma lem1553145 (k : real) (x : real) : (term168 k x) = (term226 k x).
Proof. exact (MK_COMB (@lem1553144 k x) (@lem1553142 k x)). Qed.
Lemma lem1553146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1553147 (x : real) : (term169 x) = (term227 x).
Proof. exact (MK_COMB (@lem1553146) (@lem1553100 x)). Qed.
Lemma lem1553148 (k : real) (x : real) : (term171 k x) = (term228 k x).
Proof. exact (MK_COMB (@lem1553147 x) (@lem1553145 k x)). Qed.
Lemma lem1553149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553150 (k : real) (x : real) : (term178 k x) = (term178 k x).
Proof. exact (MK_COMB (@lem1553149) (@lem1553081 k x)). Qed.
Lemma lem1553151 (k : real) (x : real) : (term179 k x) = (term229 k x).
Proof. exact (MK_COMB (@lem1553150 k x) (@lem1553148 k x)). Qed.
Lemma lem1553163 (k : real) (x : real) : (term74 k x) = (term229 k x).
Proof. exact (TRANS (@lem1552958 k x) (@lem1553151 k x)). Qed.
Lemma lem1553165 (a : real) (x : real) (r : real) : (term230 a x r) = (term231 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1553166 (k : real) (x : real) : (term99 k x) = (term232 k x).
Proof. exact (@lem1553165 k x term53). Qed.
Lemma lem1553173 (x : real) : (term50 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1553176 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1553179 (k : real) (x : real) : (term233 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1553176 k) (@lem1553173 x)). Qed.
Lemma lem1553180 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553181 (k : real) (x : real) : (term234 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1553180) (@lem1553179 k x)). Qed.
Lemma lem1553182 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553183 (k : real) (x : real) : (term235 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1553181 k x) (@lem1553182)). Qed.
Lemma lem1553202 (k : real) (x : real) : (term236 k x) = (term236 k x).
Proof. exact (eq_refl (term236 k x)). Qed.
Lemma lem1553203 (k : real) (x : real) : (term232 k x) = (term237 k x).
Proof. exact (MK_COMB (@lem1553202 k x) (@lem1553183 k x)). Qed.
Lemma lem1553204 (k : real) (x : real) : (term99 k x) = (term237 k x).
Proof. exact (TRANS (@lem1553166 k x) (@lem1553203 k x)). Qed.
Lemma lem1553205 (k : real) (x : real) : (term238 k x) = (term238 k x).
Proof. exact (eq_refl (term238 k x)). Qed.
Lemma lem1553208 (k : real) (x : real) : (term239 k x) = (term240 k x).
Proof. exact (MK_COMB (@lem1553205 k x) (@lem1553204 k x)). Qed.
Lemma lem1553210 (a : real) (x : real) (r : real) : (term230 a x r) = (term231 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1553211 (k : real) (x : real) : (term99 k x) = (term232 k x).
Proof. exact (@lem1553210 k x term53). Qed.
Lemma lem1553218 (x : real) : (term50 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1553221 (k : real) : (real_add k) = (real_add k).
Proof. exact (eq_refl (real_add k)). Qed.
Lemma lem1553224 (k : real) (x : real) : (term233 k x) = (real_add k x).
Proof. exact (MK_COMB (@lem1553221 k) (@lem1553218 x)). Qed.
Lemma lem1553225 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553226 (k : real) (x : real) : (term234 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1553225) (@lem1553224 k x)). Qed.
Lemma lem1553227 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553228 (k : real) (x : real) : (term235 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1553226 k x) (@lem1553227)). Qed.
Lemma lem1553247 (k : real) (x : real) : (term236 k x) = (term236 k x).
Proof. exact (eq_refl (term236 k x)). Qed.
Lemma lem1553248 (k : real) (x : real) : (term232 k x) = (term237 k x).
Proof. exact (MK_COMB (@lem1553247 k x) (@lem1553228 k x)). Qed.
Lemma lem1553249 (k : real) (x : real) : (term99 k x) = (term237 k x).
Proof. exact (TRANS (@lem1553211 k x) (@lem1553248 k x)). Qed.
Lemma lem1553250 (k : real) (x : real) : (term241 k x) = (term241 k x).
Proof. exact (eq_refl (term241 k x)). Qed.
Lemma lem1553253 (k : real) (x : real) : (term242 k x) = (term243 k x).
Proof. exact (MK_COMB (@lem1553250 k x) (@lem1553249 k x)). Qed.
Lemma lem1553254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553255 (k : real) (x : real) : (term244 k x) = (term245 k x).
Proof. exact (MK_COMB (@lem1553254) (@lem1553208 k x)). Qed.
Lemma lem1553256 (k : real) (x : real) : (term158 k x) = (term246 k x).
Proof. exact (MK_COMB (@lem1553255 k x) (@lem1553253 k x)). Qed.
Lemma lem1553257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1553258 (k : real) (x : real) : (term102 k x) = (term247 k x).
Proof. exact (MK_COMB (@lem1553257) (@lem1553163 k x)). Qed.
Lemma lem1553259 (k : real) (x : real) : (term159 k x) = (term248 k x).
Proof. exact (MK_COMB (@lem1553258 k x) (@lem1553256 k x)). Qed.
Lemma lem1553260 (k : real) (x : real) (h1 : term248 k x) : term248 k x.
Proof. exact (h1). Qed.
Lemma lem1553261 (k : real) (x : real) (h1 : term229 k x) : term229 k x.
Proof. exact (h1). Qed.
Lemma lem1553262 (k : real) (x : real) (h1 : term176 k x) : term176 k x.
Proof. exact (h1). Qed.
Lemma lem1553263 (k : real) (x : real) (h1 : term176 k x) : term173 k x.
Proof. exact (proj2 (@lem1553262 k x h1)). Qed.
Lemma lem1553265 (k : real) (x : real) (h1 : term176 k x) : term90 k x.
Proof. exact (proj2 (@lem1553263 k x h1)). Qed.
Lemma lem1553266 (k : real) (x : real) (h1 : term176 k x) : term62 k x.
Proof. exact (proj1 (@lem1553263 k x h1)). Qed.
Lemma lem1553267 (k : real) (x : real) (h1 : term176 k x) : term59 k x.
Proof. exact (proj2 (@lem1553266 k x h1)). Qed.
Lemma lem1553270 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553271 : term250 = term251.
Proof. exact (@lem1553270 (NUMERAL 0) term44). Qed.
Lemma lem1553272 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553273 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553274 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553273 h1) (fun h1 : term251 = True => @lem1553272)). Qed.
Lemma lem1553275 : term251 = True.
Proof. exact (EQ_MP (@lem1553274) (@lem1553272)). Qed.
Lemma lem1553276 : term250 = True.
Proof. exact (TRANS (@lem1553271) (@lem1553275)). Qed.
Lemma lem1553277 : True = term250.
Proof. exact (SYM (@lem1553276)). Qed.
Lemma lem1553278 : term250.
Proof. exact (EQ_MP (@lem1553277) (@lem0)). Qed.
Lemma lem1553279 (k : real) (x : real) (h1 : term176 k x) : term253 k x.
Proof. exact (conj (@lem1553278) (@lem1553267 k x h1)). Qed.
Lemma lem1553281 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1553282 (k : real) (x : real) : term255 k x.
Proof. exact (@lem1553281 term47 (term56 k x)). Qed.
Lemma lem1553283 (k : real) (x : real) (h1 : term176 k x) : term256 k x.
Proof. exact (@lem1553282 k x (@lem1553279 k x h1)). Qed.
Lemma lem1553284 (k : real) (x : real) : (term257 k x) = (term56 k x).
Proof. exact (@lem1483460 (term56 k x)). Qed.
Lemma lem1553285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553286 (k : real) (x : real) : (term258 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1553285) (@lem1553284 k x)). Qed.
Lemma lem1553287 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553288 (k : real) (x : real) : (term256 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1553286 k x) (@lem1553287)). Qed.
Lemma lem1553289 (k : real) (x : real) (h1 : term176 k x) : term59 k x.
Proof. exact (EQ_MP (@lem1553288 k x) (@lem1553283 k x h1)). Qed.
Lemma lem1553291 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553292 : term250 = term251.
Proof. exact (@lem1553291 (NUMERAL 0) term44). Qed.
Lemma lem1553293 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553294 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553295 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553294 h1) (fun h1 : term251 = True => @lem1553293)). Qed.
Lemma lem1553296 : term251 = True.
Proof. exact (EQ_MP (@lem1553295) (@lem1553293)). Qed.
Lemma lem1553297 : term250 = True.
Proof. exact (TRANS (@lem1553292) (@lem1553296)). Qed.
Lemma lem1553298 : True = term250.
Proof. exact (SYM (@lem1553297)). Qed.
Lemma lem1553299 : term250.
Proof. exact (EQ_MP (@lem1553298) (@lem0)). Qed.
Lemma lem1553300 (k : real) (x : real) (h1 : term176 k x) : term259 k x.
Proof. exact (conj (@lem1553299) (@lem1553265 k x h1)). Qed.
Lemma lem1553302 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1553303 (k : real) (x : real) : term261 k x.
Proof. exact (@lem1553302 term47 (term87 k x)). Qed.
Lemma lem1553304 (k : real) (x : real) (h1 : term176 k x) : term262 k x.
Proof. exact (@lem1553303 k x (@lem1553300 k x h1)). Qed.
Lemma lem1553305 (k : real) (x : real) : (term263 k x) = (term87 k x).
Proof. exact (@lem1483460 (term87 k x)). Qed.
Lemma lem1553306 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553307 (k : real) (x : real) : (term264 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1553306) (@lem1553305 k x)). Qed.
Lemma lem1553308 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553309 (k : real) (x : real) : (term262 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1553307 k x) (@lem1553308)). Qed.
Lemma lem1553310 (k : real) (x : real) (h1 : term176 k x) : term90 k x.
Proof. exact (EQ_MP (@lem1553309 k x) (@lem1553304 k x h1)). Qed.
Lemma lem1553311 (k : real) (x : real) (h1 : term176 k x) : term265 k x.
Proof. exact (conj (@lem1553310 k x h1) (@lem1553289 k x h1)). Qed.
Lemma lem1553313 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1553314 (k : real) (x : real) : term267 k x.
Proof. exact (@lem1553313 (term87 k x) (term56 k x)). Qed.
Lemma lem1553315 (k : real) (x : real) (h1 : term176 k x) : term268 k x.
Proof. exact (@lem1553314 k x (@lem1553311 k x h1)). Qed.
Lemma lem1553316 (k : real) (x : real) : (term269 k x) = (term270 k x).
Proof. exact (@lem1483480 (term33 k) k x (term33 x)). Qed.
Lemma lem1553317 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483440 term39 k). Qed.
Lemma lem1553319 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553320 : term274 = term53.
Proof. exact (@lem1553319 term44). Qed.
Lemma lem1553321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553322 : term275 = term276.
Proof. exact (MK_COMB (@lem1553321) (@lem1553320)). Qed.
Lemma lem1553323 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1553324 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1553322) (@lem1553323 k)). Qed.
Lemma lem1553325 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1553317 k) (@lem1553324 k)). Qed.
Lemma lem1553326 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1553327 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1553325 k) (@lem1553326 k)). Qed.
Lemma lem1553328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1553329 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1553328) (@lem1553327 k)). Qed.
Lemma lem1553330 (x : real) : (term280 x) = (term272 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1553332 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553333 : term274 = term53.
Proof. exact (@lem1553332 term44). Qed.
Lemma lem1553334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553335 : term275 = term276.
Proof. exact (MK_COMB (@lem1553334) (@lem1553333)). Qed.
Lemma lem1553336 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1553337 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1553335) (@lem1553336 x)). Qed.
Lemma lem1553338 (x : real) : (term280 x) = (term277 x).
Proof. exact (TRANS (@lem1553330 x) (@lem1553337 x)). Qed.
Lemma lem1553339 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1553340 (x : real) : (term280 x) = term53.
Proof. exact (TRANS (@lem1553338 x) (@lem1553339 x)). Qed.
Lemma lem1553341 (k : real) (x : real) : (term270 k x) = term281.
Proof. exact (MK_COMB (@lem1553329 k) (@lem1553340 x)). Qed.
Lemma lem1553342 (k : real) (x : real) : (term269 k x) = term281.
Proof. exact (TRANS (@lem1553316 k x) (@lem1553341 k x)). Qed.
Lemma lem1553343 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1553344 (k : real) (x : real) : (term269 k x) = term53.
Proof. exact (TRANS (@lem1553342 k x) (@lem1553343)). Qed.
Lemma lem1553345 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553346 (k : real) (x : real) : (term282 k x) = term283.
Proof. exact (MK_COMB (@lem1553345) (@lem1553344 k x)). Qed.
Lemma lem1553347 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553348 (k : real) (x : real) : (term268 k x) = term284.
Proof. exact (MK_COMB (@lem1553346 k x) (@lem1553347)). Qed.
Lemma lem1553349 (k : real) (x : real) (h1 : term176 k x) : term284.
Proof. exact (EQ_MP (@lem1553348 k x) (@lem1553315 k x h1)). Qed.
Lemma lem1553351 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553352 : term284 = term285.
Proof. exact (@lem1553351 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1553353 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1553354 : term284 = False.
Proof. exact (TRANS (@lem1553352) (@lem1553353)). Qed.
Lemma lem1553355 (k : real) (x : real) (h1 : term176 k x) : False.
Proof. exact (EQ_MP (@lem1553354) (@lem1553349 k x h1)). Qed.
Lemma lem1553356 (k : real) (x : real) (h1 : term228 k x) : term228 k x.
Proof. exact (h1). Qed.
Lemma lem1553357 (k : real) (x : real) (h1 : term228 k x) : term226 k x.
Proof. exact (proj2 (@lem1553356 k x h1)). Qed.
Lemma lem1553359 (k : real) (x : real) (h1 : term228 k x) : term84 k x.
Proof. exact (proj2 (@lem1553357 k x h1)). Qed.
Lemma lem1553360 (k : real) (x : real) (h1 : term228 k x) : term62 k x.
Proof. exact (proj1 (@lem1553357 k x h1)). Qed.
Lemma lem1553362 (k : real) (x : real) (h1 : term228 k x) : term54 k x.
Proof. exact (proj1 (@lem1553360 k x h1)). Qed.
Lemma lem1553364 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553365 : term250 = term251.
Proof. exact (@lem1553364 (NUMERAL 0) term44). Qed.
Lemma lem1553366 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553367 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553368 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553367 h1) (fun h1 : term251 = True => @lem1553366)). Qed.
Lemma lem1553369 : term251 = True.
Proof. exact (EQ_MP (@lem1553368) (@lem1553366)). Qed.
Lemma lem1553370 : term250 = True.
Proof. exact (TRANS (@lem1553365) (@lem1553369)). Qed.
Lemma lem1553371 : True = term250.
Proof. exact (SYM (@lem1553370)). Qed.
Lemma lem1553372 : term250.
Proof. exact (EQ_MP (@lem1553371) (@lem0)). Qed.
Lemma lem1553373 (k : real) (x : real) (h1 : term228 k x) : term286 k x.
Proof. exact (conj (@lem1553372) (@lem1553362 k x h1)). Qed.
Lemma lem1553375 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1553376 (k : real) (x : real) : term287 k x.
Proof. exact (@lem1553375 term47 (real_add k x)). Qed.
Lemma lem1553377 (k : real) (x : real) (h1 : term228 k x) : term288 k x.
Proof. exact (@lem1553376 k x (@lem1553373 k x h1)). Qed.
Lemma lem1553378 (k : real) (x : real) : (term289 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1553379 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553380 (k : real) (x : real) : (term290 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1553379) (@lem1553378 k x)). Qed.
Lemma lem1553381 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553382 (k : real) (x : real) : (term288 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1553380 k x) (@lem1553381)). Qed.
Lemma lem1553383 (k : real) (x : real) (h1 : term228 k x) : term54 k x.
Proof. exact (EQ_MP (@lem1553382 k x) (@lem1553377 k x h1)). Qed.
Lemma lem1553385 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553386 : term250 = term251.
Proof. exact (@lem1553385 (NUMERAL 0) term44). Qed.
Lemma lem1553387 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553388 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553389 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553388 h1) (fun h1 : term251 = True => @lem1553387)). Qed.
Lemma lem1553390 : term251 = True.
Proof. exact (EQ_MP (@lem1553389) (@lem1553387)). Qed.
Lemma lem1553391 : term250 = True.
Proof. exact (TRANS (@lem1553386) (@lem1553390)). Qed.
Lemma lem1553392 : True = term250.
Proof. exact (SYM (@lem1553391)). Qed.
Lemma lem1553393 : term250.
Proof. exact (EQ_MP (@lem1553392) (@lem0)). Qed.
Lemma lem1553394 (k : real) (x : real) (h1 : term228 k x) : term291 k x.
Proof. exact (conj (@lem1553393) (@lem1553359 k x h1)). Qed.
Lemma lem1553396 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1553397 (k : real) (x : real) : term292 k x.
Proof. exact (@lem1553396 term47 (term81 k x)). Qed.
Lemma lem1553398 (k : real) (x : real) (h1 : term228 k x) : term293 k x.
Proof. exact (@lem1553397 k x (@lem1553394 k x h1)). Qed.
Lemma lem1553399 (k : real) (x : real) : (term294 k x) = (term81 k x).
Proof. exact (@lem1483460 (term81 k x)). Qed.
Lemma lem1553400 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553401 (k : real) (x : real) : (term295 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1553400) (@lem1553399 k x)). Qed.
Lemma lem1553402 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553403 (k : real) (x : real) : (term293 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1553401 k x) (@lem1553402)). Qed.
Lemma lem1553404 (k : real) (x : real) (h1 : term228 k x) : term84 k x.
Proof. exact (EQ_MP (@lem1553403 k x) (@lem1553398 k x h1)). Qed.
Lemma lem1553405 (k : real) (x : real) (h1 : term228 k x) : term296 k x.
Proof. exact (conj (@lem1553404 k x h1) (@lem1553383 k x h1)). Qed.
Lemma lem1553407 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1553408 (k : real) (x : real) : term297 k x.
Proof. exact (@lem1553407 (term81 k x) (real_add k x)). Qed.
Lemma lem1553409 (k : real) (x : real) (h1 : term228 k x) : term298 k x.
Proof. exact (@lem1553408 k x (@lem1553405 k x h1)). Qed.
Lemma lem1553410 (k : real) (x : real) : (term299 k x) = (term300 k x).
Proof. exact (@lem1483480 (term33 k) k (term33 x) x). Qed.
Lemma lem1553411 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483440 term39 k). Qed.
Lemma lem1553413 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553414 : term274 = term53.
Proof. exact (@lem1553413 term44). Qed.
Lemma lem1553415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553416 : term275 = term276.
Proof. exact (MK_COMB (@lem1553415) (@lem1553414)). Qed.
Lemma lem1553417 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1553418 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1553416) (@lem1553417 k)). Qed.
Lemma lem1553419 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1553411 k) (@lem1553418 k)). Qed.
Lemma lem1553420 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1553421 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1553419 k) (@lem1553420 k)). Qed.
Lemma lem1553422 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1553423 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1553422) (@lem1553421 k)). Qed.
Lemma lem1553424 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1553426 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553427 : term274 = term53.
Proof. exact (@lem1553426 term44). Qed.
Lemma lem1553428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553429 : term275 = term276.
Proof. exact (MK_COMB (@lem1553428) (@lem1553427)). Qed.
Lemma lem1553430 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1553431 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1553429) (@lem1553430 x)). Qed.
Lemma lem1553432 (x : real) : (term271 x) = (term277 x).
Proof. exact (TRANS (@lem1553424 x) (@lem1553431 x)). Qed.
Lemma lem1553433 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1553434 (x : real) : (term271 x) = term53.
Proof. exact (TRANS (@lem1553432 x) (@lem1553433 x)). Qed.
Lemma lem1553435 (k : real) (x : real) : (term300 k x) = term281.
Proof. exact (MK_COMB (@lem1553423 k) (@lem1553434 x)). Qed.
Lemma lem1553436 (k : real) (x : real) : (term299 k x) = term281.
Proof. exact (TRANS (@lem1553410 k x) (@lem1553435 k x)). Qed.
Lemma lem1553437 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1553438 (k : real) (x : real) : (term299 k x) = term53.
Proof. exact (TRANS (@lem1553436 k x) (@lem1553437)). Qed.
Lemma lem1553439 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553440 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (MK_COMB (@lem1553439) (@lem1553438 k x)). Qed.
Lemma lem1553441 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553442 (k : real) (x : real) : (term298 k x) = term284.
Proof. exact (MK_COMB (@lem1553440 k x) (@lem1553441)). Qed.
Lemma lem1553443 (k : real) (x : real) (h1 : term228 k x) : term284.
Proof. exact (EQ_MP (@lem1553442 k x) (@lem1553409 k x h1)). Qed.
Lemma lem1553445 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553446 : term284 = term285.
Proof. exact (@lem1553445 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1553447 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1553448 : term284 = False.
Proof. exact (TRANS (@lem1553446) (@lem1553447)). Qed.
Lemma lem1553449 (k : real) (x : real) (h1 : term228 k x) : False.
Proof. exact (EQ_MP (@lem1553448) (@lem1553443 k x h1)). Qed.
Lemma lem1553450 (k : real) (x : real) (h1 : term229 k x) : False.
Proof. exact (or_elim (@lem1553261 k x h1) (fun h0 : term176 k x => @lem1553355 k x h0) (fun h0 : term228 k x => @lem1553449 k x h0)). Qed.
Lemma lem1553451 (k : real) (x : real) (h1 : term246 k x) : term246 k x.
Proof. exact (h1). Qed.
Lemma lem1553452 (k : real) (x : real) (h1 : term240 k x) : term240 k x.
Proof. exact (h1). Qed.
Lemma lem1553453 (k : real) (x : real) (h1 : term240 k x) : term237 k x.
Proof. exact (proj2 (@lem1553452 k x h1)). Qed.
Lemma lem1553454 (k : real) (x : real) (h1 : term240 k x) : term84 k x.
Proof. exact (proj1 (@lem1553452 k x h1)). Qed.
Lemma lem1553455 (k : real) (x : real) (h1 : term240 k x) : term54 k x.
Proof. exact (proj2 (@lem1553453 k x h1)). Qed.
Lemma lem1553458 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553459 : term250 = term251.
Proof. exact (@lem1553458 (NUMERAL 0) term44). Qed.
Lemma lem1553460 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553461 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553462 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553461 h1) (fun h1 : term251 = True => @lem1553460)). Qed.
Lemma lem1553463 : term251 = True.
Proof. exact (EQ_MP (@lem1553462) (@lem1553460)). Qed.
Lemma lem1553464 : term250 = True.
Proof. exact (TRANS (@lem1553459) (@lem1553463)). Qed.
Lemma lem1553465 : True = term250.
Proof. exact (SYM (@lem1553464)). Qed.
Lemma lem1553466 : term250.
Proof. exact (EQ_MP (@lem1553465) (@lem0)). Qed.
Lemma lem1553467 (k : real) (x : real) (h1 : term240 k x) : term286 k x.
Proof. exact (conj (@lem1553466) (@lem1553455 k x h1)). Qed.
Lemma lem1553469 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1553470 (k : real) (x : real) : term287 k x.
Proof. exact (@lem1553469 term47 (real_add k x)). Qed.
Lemma lem1553471 (k : real) (x : real) (h1 : term240 k x) : term288 k x.
Proof. exact (@lem1553470 k x (@lem1553467 k x h1)). Qed.
Lemma lem1553472 (k : real) (x : real) : (term289 k x) = (real_add k x).
Proof. exact (@lem1483460 (real_add k x)). Qed.
Lemma lem1553473 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553474 (k : real) (x : real) : (term290 k x) = (term52 k x).
Proof. exact (MK_COMB (@lem1553473) (@lem1553472 k x)). Qed.
Lemma lem1553475 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553476 (k : real) (x : real) : (term288 k x) = (term54 k x).
Proof. exact (MK_COMB (@lem1553474 k x) (@lem1553475)). Qed.
Lemma lem1553477 (k : real) (x : real) (h1 : term240 k x) : term54 k x.
Proof. exact (EQ_MP (@lem1553476 k x) (@lem1553471 k x h1)). Qed.
Lemma lem1553479 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553480 : term250 = term251.
Proof. exact (@lem1553479 (NUMERAL 0) term44). Qed.
Lemma lem1553481 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553482 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553483 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553482 h1) (fun h1 : term251 = True => @lem1553481)). Qed.
Lemma lem1553484 : term251 = True.
Proof. exact (EQ_MP (@lem1553483) (@lem1553481)). Qed.
Lemma lem1553485 : term250 = True.
Proof. exact (TRANS (@lem1553480) (@lem1553484)). Qed.
Lemma lem1553486 : True = term250.
Proof. exact (SYM (@lem1553485)). Qed.
Lemma lem1553487 : term250.
Proof. exact (EQ_MP (@lem1553486) (@lem0)). Qed.
Lemma lem1553488 (k : real) (x : real) (h1 : term240 k x) : term291 k x.
Proof. exact (conj (@lem1553487) (@lem1553454 k x h1)). Qed.
Lemma lem1553490 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1553491 (k : real) (x : real) : term292 k x.
Proof. exact (@lem1553490 term47 (term81 k x)). Qed.
Lemma lem1553492 (k : real) (x : real) (h1 : term240 k x) : term293 k x.
Proof. exact (@lem1553491 k x (@lem1553488 k x h1)). Qed.
Lemma lem1553493 (k : real) (x : real) : (term294 k x) = (term81 k x).
Proof. exact (@lem1483460 (term81 k x)). Qed.
Lemma lem1553494 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553495 (k : real) (x : real) : (term295 k x) = (term83 k x).
Proof. exact (MK_COMB (@lem1553494) (@lem1553493 k x)). Qed.
Lemma lem1553496 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553497 (k : real) (x : real) : (term293 k x) = (term84 k x).
Proof. exact (MK_COMB (@lem1553495 k x) (@lem1553496)). Qed.
Lemma lem1553498 (k : real) (x : real) (h1 : term240 k x) : term84 k x.
Proof. exact (EQ_MP (@lem1553497 k x) (@lem1553492 k x h1)). Qed.
Lemma lem1553499 (k : real) (x : real) (h1 : term240 k x) : term296 k x.
Proof. exact (conj (@lem1553498 k x h1) (@lem1553477 k x h1)). Qed.
Lemma lem1553501 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1553502 (k : real) (x : real) : term297 k x.
Proof. exact (@lem1553501 (term81 k x) (real_add k x)). Qed.
Lemma lem1553503 (k : real) (x : real) (h1 : term240 k x) : term298 k x.
Proof. exact (@lem1553502 k x (@lem1553499 k x h1)). Qed.
Lemma lem1553504 (k : real) (x : real) : (term299 k x) = (term300 k x).
Proof. exact (@lem1483480 (term33 k) k (term33 x) x). Qed.
Lemma lem1553505 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483440 term39 k). Qed.
Lemma lem1553507 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553508 : term274 = term53.
Proof. exact (@lem1553507 term44). Qed.
Lemma lem1553509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553510 : term275 = term276.
Proof. exact (MK_COMB (@lem1553509) (@lem1553508)). Qed.
Lemma lem1553511 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1553512 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1553510) (@lem1553511 k)). Qed.
Lemma lem1553513 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1553505 k) (@lem1553512 k)). Qed.
Lemma lem1553514 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1553515 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1553513 k) (@lem1553514 k)). Qed.
Lemma lem1553516 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1553517 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1553516) (@lem1553515 k)). Qed.
Lemma lem1553518 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1483440 term39 x). Qed.
Lemma lem1553520 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553521 : term274 = term53.
Proof. exact (@lem1553520 term44). Qed.
Lemma lem1553522 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553523 : term275 = term276.
Proof. exact (MK_COMB (@lem1553522) (@lem1553521)). Qed.
Lemma lem1553524 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1553525 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1553523) (@lem1553524 x)). Qed.
Lemma lem1553526 (x : real) : (term271 x) = (term277 x).
Proof. exact (TRANS (@lem1553518 x) (@lem1553525 x)). Qed.
Lemma lem1553527 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1553528 (x : real) : (term271 x) = term53.
Proof. exact (TRANS (@lem1553526 x) (@lem1553527 x)). Qed.
Lemma lem1553529 (k : real) (x : real) : (term300 k x) = term281.
Proof. exact (MK_COMB (@lem1553517 k) (@lem1553528 x)). Qed.
Lemma lem1553530 (k : real) (x : real) : (term299 k x) = term281.
Proof. exact (TRANS (@lem1553504 k x) (@lem1553529 k x)). Qed.
Lemma lem1553531 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1553532 (k : real) (x : real) : (term299 k x) = term53.
Proof. exact (TRANS (@lem1553530 k x) (@lem1553531)). Qed.
Lemma lem1553533 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553534 (k : real) (x : real) : (term301 k x) = term283.
Proof. exact (MK_COMB (@lem1553533) (@lem1553532 k x)). Qed.
Lemma lem1553535 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553536 (k : real) (x : real) : (term298 k x) = term284.
Proof. exact (MK_COMB (@lem1553534 k x) (@lem1553535)). Qed.
Lemma lem1553537 (k : real) (x : real) (h1 : term240 k x) : term284.
Proof. exact (EQ_MP (@lem1553536 k x) (@lem1553503 k x h1)). Qed.
Lemma lem1553539 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553540 : term284 = term285.
Proof. exact (@lem1553539 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1553541 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1553542 : term284 = False.
Proof. exact (TRANS (@lem1553540) (@lem1553541)). Qed.
Lemma lem1553543 (k : real) (x : real) (h1 : term240 k x) : False.
Proof. exact (EQ_MP (@lem1553542) (@lem1553537 k x h1)). Qed.
Lemma lem1553544 (k : real) (x : real) (h1 : term243 k x) : term243 k x.
Proof. exact (h1). Qed.
Lemma lem1553545 (k : real) (x : real) (h1 : term243 k x) : term237 k x.
Proof. exact (proj2 (@lem1553544 k x h1)). Qed.
Lemma lem1553546 (k : real) (x : real) (h1 : term243 k x) : term90 k x.
Proof. exact (proj1 (@lem1553544 k x h1)). Qed.
Lemma lem1553548 (k : real) (x : real) (h1 : term243 k x) : term59 k x.
Proof. exact (proj1 (@lem1553545 k x h1)). Qed.
Lemma lem1553550 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553551 : term250 = term251.
Proof. exact (@lem1553550 (NUMERAL 0) term44). Qed.
Lemma lem1553552 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553553 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553554 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553553 h1) (fun h1 : term251 = True => @lem1553552)). Qed.
Lemma lem1553555 : term251 = True.
Proof. exact (EQ_MP (@lem1553554) (@lem1553552)). Qed.
Lemma lem1553556 : term250 = True.
Proof. exact (TRANS (@lem1553551) (@lem1553555)). Qed.
Lemma lem1553557 : True = term250.
Proof. exact (SYM (@lem1553556)). Qed.
Lemma lem1553558 : term250.
Proof. exact (EQ_MP (@lem1553557) (@lem0)). Qed.
Lemma lem1553559 (k : real) (x : real) (h1 : term243 k x) : term253 k x.
Proof. exact (conj (@lem1553558) (@lem1553548 k x h1)). Qed.
Lemma lem1553561 (x : real) (y : real) : term254 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1553562 (k : real) (x : real) : term255 k x.
Proof. exact (@lem1553561 term47 (term56 k x)). Qed.
Lemma lem1553563 (k : real) (x : real) (h1 : term243 k x) : term256 k x.
Proof. exact (@lem1553562 k x (@lem1553559 k x h1)). Qed.
Lemma lem1553564 (k : real) (x : real) : (term257 k x) = (term56 k x).
Proof. exact (@lem1483460 (term56 k x)). Qed.
Lemma lem1553565 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1553566 (k : real) (x : real) : (term258 k x) = (term58 k x).
Proof. exact (MK_COMB (@lem1553565) (@lem1553564 k x)). Qed.
Lemma lem1553567 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553568 (k : real) (x : real) : (term256 k x) = (term59 k x).
Proof. exact (MK_COMB (@lem1553566 k x) (@lem1553567)). Qed.
Lemma lem1553569 (k : real) (x : real) (h1 : term243 k x) : term59 k x.
Proof. exact (EQ_MP (@lem1553568 k x) (@lem1553563 k x h1)). Qed.
Lemma lem1553571 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553572 : term250 = term251.
Proof. exact (@lem1553571 (NUMERAL 0) term44). Qed.
Lemma lem1553573 : term252 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1553574 (h1 : term252 = (BIT1 0)) : term251 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1553575 : (term252 = (BIT1 0)) = (term251 = True).
Proof. exact (prop_ext (fun h1 : term252 = (BIT1 0) => @lem1553574 h1) (fun h1 : term251 = True => @lem1553573)). Qed.
Lemma lem1553576 : term251 = True.
Proof. exact (EQ_MP (@lem1553575) (@lem1553573)). Qed.
Lemma lem1553577 : term250 = True.
Proof. exact (TRANS (@lem1553572) (@lem1553576)). Qed.
Lemma lem1553578 : True = term250.
Proof. exact (SYM (@lem1553577)). Qed.
Lemma lem1553579 : term250.
Proof. exact (EQ_MP (@lem1553578) (@lem0)). Qed.
Lemma lem1553580 (k : real) (x : real) (h1 : term243 k x) : term259 k x.
Proof. exact (conj (@lem1553579) (@lem1553546 k x h1)). Qed.
Lemma lem1553582 (x : real) (y : real) : term260 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1553583 (k : real) (x : real) : term261 k x.
Proof. exact (@lem1553582 term47 (term87 k x)). Qed.
Lemma lem1553584 (k : real) (x : real) (h1 : term243 k x) : term262 k x.
Proof. exact (@lem1553583 k x (@lem1553580 k x h1)). Qed.
Lemma lem1553585 (k : real) (x : real) : (term263 k x) = (term87 k x).
Proof. exact (@lem1483460 (term87 k x)). Qed.
Lemma lem1553586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553587 (k : real) (x : real) : (term264 k x) = (term89 k x).
Proof. exact (MK_COMB (@lem1553586) (@lem1553585 k x)). Qed.
Lemma lem1553588 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553589 (k : real) (x : real) : (term262 k x) = (term90 k x).
Proof. exact (MK_COMB (@lem1553587 k x) (@lem1553588)). Qed.
Lemma lem1553590 (k : real) (x : real) (h1 : term243 k x) : term90 k x.
Proof. exact (EQ_MP (@lem1553589 k x) (@lem1553584 k x h1)). Qed.
Lemma lem1553591 (k : real) (x : real) (h1 : term243 k x) : term265 k x.
Proof. exact (conj (@lem1553590 k x h1) (@lem1553569 k x h1)). Qed.
Lemma lem1553593 (x : real) (y : real) : term266 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1553594 (k : real) (x : real) : term267 k x.
Proof. exact (@lem1553593 (term87 k x) (term56 k x)). Qed.
Lemma lem1553595 (k : real) (x : real) (h1 : term243 k x) : term268 k x.
Proof. exact (@lem1553594 k x (@lem1553591 k x h1)). Qed.
Lemma lem1553596 (k : real) (x : real) : (term269 k x) = (term270 k x).
Proof. exact (@lem1483480 (term33 k) k x (term33 x)). Qed.
Lemma lem1553597 (k : real) : (term271 k) = (term272 k).
Proof. exact (@lem1483440 term39 k). Qed.
Lemma lem1553599 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553600 : term274 = term53.
Proof. exact (@lem1553599 term44). Qed.
Lemma lem1553601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553602 : term275 = term276.
Proof. exact (MK_COMB (@lem1553601) (@lem1553600)). Qed.
Lemma lem1553603 (k : real) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem1553604 (k : real) : (term272 k) = (term277 k).
Proof. exact (MK_COMB (@lem1553602) (@lem1553603 k)). Qed.
Lemma lem1553605 (k : real) : (term271 k) = (term277 k).
Proof. exact (TRANS (@lem1553597 k) (@lem1553604 k)). Qed.
Lemma lem1553606 (k : real) : (term277 k) = term53.
Proof. exact (@lem1483446 k). Qed.
Lemma lem1553607 (k : real) : (term271 k) = term53.
Proof. exact (TRANS (@lem1553605 k) (@lem1553606 k)). Qed.
Lemma lem1553608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1553609 (k : real) : (term278 k) = term279.
Proof. exact (MK_COMB (@lem1553608) (@lem1553607 k)). Qed.
Lemma lem1553610 (x : real) : (term280 x) = (term272 x).
Proof. exact (@lem1483442 term39 x). Qed.
Lemma lem1553612 (m : nat) : (term273 m) = term53.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1553613 : term274 = term53.
Proof. exact (@lem1553612 term44). Qed.
Lemma lem1553614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1553615 : term275 = term276.
Proof. exact (MK_COMB (@lem1553614) (@lem1553613)). Qed.
Lemma lem1553616 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1553617 (x : real) : (term272 x) = (term277 x).
Proof. exact (MK_COMB (@lem1553615) (@lem1553616 x)). Qed.
Lemma lem1553618 (x : real) : (term280 x) = (term277 x).
Proof. exact (TRANS (@lem1553610 x) (@lem1553617 x)). Qed.
Lemma lem1553619 (x : real) : (term277 x) = term53.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1553620 (x : real) : (term280 x) = term53.
Proof. exact (TRANS (@lem1553618 x) (@lem1553619 x)). Qed.
Lemma lem1553621 (k : real) (x : real) : (term270 k x) = term281.
Proof. exact (MK_COMB (@lem1553609 k) (@lem1553620 x)). Qed.
Lemma lem1553622 (k : real) (x : real) : (term269 k x) = term281.
Proof. exact (TRANS (@lem1553596 k x) (@lem1553621 k x)). Qed.
Lemma lem1553623 : term281 = term53.
Proof. exact (@lem1483448 term53). Qed.
Lemma lem1553624 (k : real) (x : real) : (term269 k x) = term53.
Proof. exact (TRANS (@lem1553622 k x) (@lem1553623)). Qed.
Lemma lem1553625 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1553626 (k : real) (x : real) : (term282 k x) = term283.
Proof. exact (MK_COMB (@lem1553625) (@lem1553624 k x)). Qed.
Lemma lem1553627 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1553628 (k : real) (x : real) : (term268 k x) = term284.
Proof. exact (MK_COMB (@lem1553626 k x) (@lem1553627)). Qed.
Lemma lem1553629 (k : real) (x : real) (h1 : term243 k x) : term284.
Proof. exact (EQ_MP (@lem1553628 k x) (@lem1553595 k x h1)). Qed.
Lemma lem1553631 (n : nat) (m : nat) : (term249 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1553632 : term284 = term285.
Proof. exact (@lem1553631 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1553633 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1553634 : term284 = False.
Proof. exact (TRANS (@lem1553632) (@lem1553633)). Qed.
Lemma lem1553635 (k : real) (x : real) (h1 : term243 k x) : False.
Proof. exact (EQ_MP (@lem1553634) (@lem1553629 k x h1)). Qed.
Lemma lem1553636 (k : real) (x : real) (h1 : term246 k x) : False.
Proof. exact (or_elim (@lem1553451 k x h1) (fun h0 : term240 k x => @lem1553543 k x h0) (fun h0 : term243 k x => @lem1553635 k x h0)). Qed.
Lemma lem1553637 (k : real) (x : real) (h1 : term248 k x) : False.
Proof. exact (or_elim (@lem1553260 k x h1) (fun h0 : term229 k x => @lem1553450 k x h0) (fun h0 : term246 k x => @lem1553636 k x h0)). Qed.
Lemma lem1553638 (k : real) (x : real) (h1 : term159 k x) : term159 k x.
Proof. exact (h1). Qed.
Lemma lem1553639 (k : real) (x : real) (h1 : term159 k x) : term248 k x.
Proof. exact (EQ_MP (@lem1553259 k x) (@lem1553638 k x h1)). Qed.
Lemma lem1553640 (k : real) (x : real) (h1 : term159 k x) : (term248 k x) = False.
Proof. exact (prop_ext (fun h2 : term248 k x => @lem1553637 k x h2) (fun h2 : False => @lem1553639 k x h1)). Qed.
Lemma lem1553641 (k : real) (x : real) (h1 : term159 k x) : False.
Proof. exact (EQ_MP (@lem1553640 k x h1) (@lem1553639 k x h1)). Qed.
Lemma lem1553642 (x : real) (h1 : term161 x) : term161 x.
Proof. exact (h1). Qed.
Lemma lem1553643 (x : real) (h1 : term161 x) : False.
Proof. exact (ex_elim (@lem1553642 x h1) (fun k : real => fun h0 : term160 x k => @lem1553641 k x h0)). Qed.
Lemma lem1553644 (h1 : term163) : term163.
Proof. exact (h1). Qed.
Lemma lem1553645 (h1 : term163) : False.
Proof. exact (ex_elim (@lem1553644 h1) (fun x : real => fun h0 : term162 x => @lem1553643 x h0)). Qed.
Lemma lem1553646 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1553647 (h1 : term23) : term163.
Proof. exact (EQ_MP (@lem1552941) (@lem1553646 h1)). Qed.
Lemma lem1553648 (h1 : term23) : term163 = False.
Proof. exact (prop_ext (fun h2 : term163 => @lem1553645 h2) (fun h2 : False => @lem1553647 h1)). Qed.
Lemma lem1553649 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1553648 h1) (@lem1553647 h1)). Qed.
Lemma lem1553650 : term302.
Proof. exact (fun h0 : term23 => @lem1553649 h0). Qed.
Lemma lem1553651 : term303.
Proof. exact (@lem1386578 term304). Qed.
Lemma lem1553652 : term304.
Proof. exact (@lem1553651 (@lem1553650)). Qed.

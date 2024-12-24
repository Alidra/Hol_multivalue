Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_LE_SQRT_POS_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_ABS_POS_spec.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_LE_RSQRT_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_POS_LE_spec.
Require Import SQRT_POW_2_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482703_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483454_spec.
Require Import thm1483460_spec.
Require Import thm1483472_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483498_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Lemma lem1968401 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem1483554 (term2 x y) (term3 x y)). Qed.
Lemma lem1968426 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (@lem1483519 (term5 x) (term5 y)). Qed.
Lemma lem1968433 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (eq_refl (real_add x y)). Qed.
Lemma lem1968446 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1968447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968448 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1968447) (@lem1968446 x y)). Qed.
Lemma lem1968449 (x : real) (y : real) : (term2 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1968448 x y) (@lem1968433 x y)). Qed.
Lemma lem1968450 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (@lem1483454 x (term11 y) (real_add x y)). Qed.
Lemma lem1968451 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (@lem1483508 x x y). Qed.
Lemma lem1968452 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1968453 (x : real) : (real_mul x x) = (term5 x).
Proof. exact (@lem1483498 x). Qed.
Lemma lem1968454 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1968455 (x : real) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1968454) (@lem1968453 x)). Qed.
Lemma lem1968456 (x : real) (y : real) : (term13 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1968455 x) (@lem1968452 x y)). Qed.
Lemma lem1968457 (x : real) (y : real) : (term12 x y) = (term16 x y).
Proof. exact (TRANS (@lem1968451 x y) (@lem1968456 x y)). Qed.
Lemma lem1968458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1968459 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1968458) (@lem1968457 x y)). Qed.
Lemma lem1968460 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (@lem1483508 x (term11 y) y). Qed.
Lemma lem1968461 (y : real) : (term21 y) = (term22 y).
Proof. exact (@lem1483472 term23 y y). Qed.
Lemma lem1968462 (y : real) : (real_mul y y) = (term5 y).
Proof. exact (@lem1483498 y). Qed.
Lemma lem1968463 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1968464 (y : real) : (term22 y) = (term25 y).
Proof. exact (MK_COMB (@lem1968463) (@lem1968462 y)). Qed.
Lemma lem1968465 (y : real) : (term21 y) = (term25 y).
Proof. exact (TRANS (@lem1968461 y) (@lem1968464 y)). Qed.
Lemma lem1968466 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (@lem1483472 term23 y x). Qed.
Lemma lem1968467 (x : real) (y : real) : (real_mul y x) = (real_mul x y).
Proof. exact (@lem1483474 x y). Qed.
Lemma lem1968468 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1968469 (x : real) (y : real) : (term27 y x) = (term27 x y).
Proof. exact (MK_COMB (@lem1968468) (@lem1968467 x y)). Qed.
Lemma lem1968470 (x : real) (y : real) : (term26 y x) = (term27 x y).
Proof. exact (TRANS (@lem1968466 y x) (@lem1968469 x y)). Qed.
Lemma lem1968471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1968472 (x : real) (y : real) : (term28 y x) = (term29 x y).
Proof. exact (MK_COMB (@lem1968471) (@lem1968470 x y)). Qed.
Lemma lem1968473 (x : real) (y : real) : (term20 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1968472 x y) (@lem1968465 y)). Qed.
Lemma lem1968474 (x : real) (y : real) : (term19 x y) = (term30 x y).
Proof. exact (TRANS (@lem1968460 x y) (@lem1968473 x y)). Qed.
Lemma lem1968475 (x : real) (y : real) : (term10 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1968459 x y) (@lem1968474 x y)). Qed.
Lemma lem1968476 (x : real) (y : real) : (term9 x y) = (term31 x y).
Proof. exact (TRANS (@lem1968450 x y) (@lem1968475 x y)). Qed.
Lemma lem1968477 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (@lem1483482 (term5 x) (real_mul x y) (term30 x y)). Qed.
Lemma lem1968478 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483490 (real_mul x y) (term27 x y) (term25 y)). Qed.
Lemma lem1968479 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem1483442 term23 (real_mul x y)). Qed.
Lemma lem1968481 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1968482 : term39 = term38.
Proof. exact (@lem1968481 term40). Qed.
Lemma lem1968483 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968484 : term41 = term42.
Proof. exact (MK_COMB (@lem1968483) (@lem1968482)). Qed.
Lemma lem1968485 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1968486 (x : real) (y : real) : (term36 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1968484) (@lem1968485 x y)). Qed.
Lemma lem1968487 (x : real) (y : real) : (term35 x y) = (term43 x y).
Proof. exact (TRANS (@lem1968479 x y) (@lem1968486 x y)). Qed.
Lemma lem1968488 (x : real) (y : real) : (term43 x y) = term38.
Proof. exact (@lem1483446 (real_mul x y)). Qed.
Lemma lem1968489 (x : real) (y : real) : (term35 x y) = term38.
Proof. exact (TRANS (@lem1968487 x y) (@lem1968488 x y)). Qed.
Lemma lem1968490 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1968491 (x : real) (y : real) : (term44 x y) = term45.
Proof. exact (MK_COMB (@lem1968490) (@lem1968489 x y)). Qed.
Lemma lem1968492 (y : real) : (term25 y) = (term25 y).
Proof. exact (eq_refl (term25 y)). Qed.
Lemma lem1968493 (x : real) (y : real) : (term34 x y) = (term46 y).
Proof. exact (MK_COMB (@lem1968491 x y) (@lem1968492 y)). Qed.
Lemma lem1968494 (x : real) (y : real) : (term33 x y) = (term46 y).
Proof. exact (TRANS (@lem1968478 x y) (@lem1968493 x y)). Qed.
Lemma lem1968495 (y : real) : (term46 y) = (term25 y).
Proof. exact (@lem1483448 (term25 y)). Qed.
Lemma lem1968496 (x : real) (y : real) : (term33 x y) = (term25 y).
Proof. exact (TRANS (@lem1968494 x y) (@lem1968495 y)). Qed.
Lemma lem1968497 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1968498 (x : real) (y : real) : (term32 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1968497 x) (@lem1968496 x y)). Qed.
Lemma lem1968499 (x : real) (y : real) : (term31 x y) = (term4 x y).
Proof. exact (TRANS (@lem1968477 x y) (@lem1968498 x y)). Qed.
Lemma lem1968500 (x : real) (y : real) : (term9 x y) = (term4 x y).
Proof. exact (TRANS (@lem1968476 x y) (@lem1968499 x y)). Qed.
Lemma lem1968501 (x : real) (y : real) : (term2 x y) = (term4 x y).
Proof. exact (TRANS (@lem1968449 x y) (@lem1968500 x y)). Qed.
Lemma lem1968502 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1968503 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1968502) (@lem1968501 x y)). Qed.
Lemma lem1968504 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1968503 x y) (@lem1968426 x y)). Qed.
Lemma lem1968505 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (@lem1483519 (term4 x y) (term4 x y)). Qed.
Lemma lem1968506 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483508 (term5 x) term23 (term25 y)). Qed.
Lemma lem1968507 (y : real) : (term54 y) = (term55 y).
Proof. exact (@lem1483476 term23 term23 (term5 y)). Qed.
Lemma lem1968509 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1968510 : term58 = term59.
Proof. exact (@lem1968509 term40 term40). Qed.
Lemma lem1968511 : (term60 = (BIT1 0)) = (term61 = term40).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1968512 : term61 = term40.
Proof. exact (EQ_MP (@lem1968511) (@lem940073)). Qed.
Lemma lem1968513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1968514 : term59 = term62.
Proof. exact (MK_COMB (@lem1968513) (@lem1968512)). Qed.
Lemma lem1968515 : term58 = term62.
Proof. exact (TRANS (@lem1968510) (@lem1968514)). Qed.
Lemma lem1968516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968517 : term63 = term64.
Proof. exact (MK_COMB (@lem1968516) (@lem1968515)). Qed.
Lemma lem1968518 (y : real) : (term5 y) = (term5 y).
Proof. exact (eq_refl (term5 y)). Qed.
Lemma lem1968519 (y : real) : (term55 y) = (term65 y).
Proof. exact (MK_COMB (@lem1968517) (@lem1968518 y)). Qed.
Lemma lem1968520 (y : real) : (term54 y) = (term65 y).
Proof. exact (TRANS (@lem1968507 y) (@lem1968519 y)). Qed.
Lemma lem1968521 (y : real) : (term65 y) = (term5 y).
Proof. exact (@lem1483436 (term5 y)). Qed.
Lemma lem1968522 (y : real) : (term54 y) = (term5 y).
Proof. exact (TRANS (@lem1968520 y) (@lem1968521 y)). Qed.
Lemma lem1968525 (x : real) : (term66 x) = (term66 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1968526 (x : real) (y : real) : (term53 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1968525 x) (@lem1968522 y)). Qed.
Lemma lem1968527 (x : real) (y : real) : (term52 x y) = (term67 x y).
Proof. exact (TRANS (@lem1968506 x y) (@lem1968526 x y)). Qed.
Lemma lem1968528 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1968529 (x : real) (y : real) : (term51 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1968528 x y) (@lem1968527 x y)). Qed.
Lemma lem1968530 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (@lem1483480 (term5 x) (term25 x) (term25 y) (term5 y)). Qed.
Lemma lem1968531 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem1483442 term23 (term5 x)). Qed.
Lemma lem1968533 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1968534 : term39 = term38.
Proof. exact (@lem1968533 term40). Qed.
Lemma lem1968535 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968536 : term41 = term42.
Proof. exact (MK_COMB (@lem1968535) (@lem1968534)). Qed.
Lemma lem1968537 (x : real) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1968538 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem1968536) (@lem1968537 x)). Qed.
Lemma lem1968539 (x : real) : (term71 x) = (term73 x).
Proof. exact (TRANS (@lem1968531 x) (@lem1968538 x)). Qed.
Lemma lem1968540 (x : real) : (term73 x) = term38.
Proof. exact (@lem1483446 (term5 x)). Qed.
Lemma lem1968541 (x : real) : (term71 x) = term38.
Proof. exact (TRANS (@lem1968539 x) (@lem1968540 x)). Qed.
Lemma lem1968542 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1968543 (x : real) : (term74 x) = term45.
Proof. exact (MK_COMB (@lem1968542) (@lem1968541 x)). Qed.
Lemma lem1968544 (y : real) : (term75 y) = (term72 y).
Proof. exact (@lem1483440 term23 (term5 y)). Qed.
Lemma lem1968546 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1968547 : term39 = term38.
Proof. exact (@lem1968546 term40). Qed.
Lemma lem1968548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968549 : term41 = term42.
Proof. exact (MK_COMB (@lem1968548) (@lem1968547)). Qed.
Lemma lem1968550 (y : real) : (term5 y) = (term5 y).
Proof. exact (eq_refl (term5 y)). Qed.
Lemma lem1968551 (y : real) : (term72 y) = (term73 y).
Proof. exact (MK_COMB (@lem1968549) (@lem1968550 y)). Qed.
Lemma lem1968552 (y : real) : (term75 y) = (term73 y).
Proof. exact (TRANS (@lem1968544 y) (@lem1968551 y)). Qed.
Lemma lem1968553 (y : real) : (term73 y) = term38.
Proof. exact (@lem1483446 (term5 y)). Qed.
Lemma lem1968554 (y : real) : (term75 y) = term38.
Proof. exact (TRANS (@lem1968552 y) (@lem1968553 y)). Qed.
Lemma lem1968555 (x : real) (y : real) : (term70 x y) = term76.
Proof. exact (MK_COMB (@lem1968543 x) (@lem1968554 y)). Qed.
Lemma lem1968556 (x : real) (y : real) : (term69 x y) = term76.
Proof. exact (TRANS (@lem1968530 x y) (@lem1968555 x y)). Qed.
Lemma lem1968557 : term76 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1968558 (x : real) (y : real) : (term69 x y) = term38.
Proof. exact (TRANS (@lem1968556 x y) (@lem1968557)). Qed.
Lemma lem1968559 (x : real) (y : real) : (term51 x y) = term38.
Proof. exact (TRANS (@lem1968529 x y) (@lem1968558 x y)). Qed.
Lemma lem1968560 (x : real) (y : real) : (term50 x y) = term38.
Proof. exact (TRANS (@lem1968505 x y) (@lem1968559 x y)). Qed.
Lemma lem1968561 (x : real) (y : real) : (term49 x y) = term38.
Proof. exact (TRANS (@lem1968504 x y) (@lem1968560 x y)). Qed.
Lemma lem1968562 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1968563 (x : real) (y : real) : (term77 x y) = term78.
Proof. exact (MK_COMB (@lem1968562) (@lem1968561 x y)). Qed.
Lemma lem1968564 : term78 = term79.
Proof. exact (@lem1483512 term38). Qed.
Lemma lem1968566 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968567 : term79 = term38.
Proof. exact (@lem1968566 term40). Qed.
Lemma lem1968568 : term78 = term38.
Proof. exact (TRANS (@lem1968564) (@lem1968567)). Qed.
Lemma lem1968569 (x : real) (y : real) : (term81 x y) = (term81 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem1968570 (x : real) (y : real) : ((term77 x y) = term78) = ((term77 x y) = term38).
Proof. exact (MK_COMB (@lem1968569 x y) (@lem1968568)). Qed.
Lemma lem1968571 (x : real) (y : real) : (term77 x y) = term38.
Proof. exact (EQ_MP (@lem1968570 x y) (@lem1968563 x y)). Qed.
Lemma lem1968572 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1968573 (x : real) (y : real) : (term82 x y) = term83.
Proof. exact (MK_COMB (@lem1968572) (@lem1968571 x y)). Qed.
Lemma lem1968574 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968575 (x : real) (y : real) : (term84 x y) = term85.
Proof. exact (MK_COMB (@lem1968573 x y) (@lem1968574)). Qed.
Lemma lem1968576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1968577 (x : real) (y : real) : (term86 x y) = term83.
Proof. exact (MK_COMB (@lem1968576) (@lem1968561 x y)). Qed.
Lemma lem1968578 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968579 (x : real) (y : real) : (term87 x y) = term85.
Proof. exact (MK_COMB (@lem1968577 x y) (@lem1968578)). Qed.
Lemma lem1968580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1968581 (x : real) (y : real) : (term88 x y) = term89.
Proof. exact (MK_COMB (@lem1968580) (@lem1968579 x y)). Qed.
Lemma lem1968582 (x : real) (y : real) : (term1 x y) = term90.
Proof. exact (MK_COMB (@lem1968581 x y) (@lem1968575 x y)). Qed.
Lemma lem1968596 (x : real) (y : real) : (term0 x y) = term90.
Proof. exact (TRANS (@lem1968401 x y) (@lem1968582 x y)). Qed.
Lemma lem1968606 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem1968607 (h1 : term85) : term85.
Proof. exact (h1). Qed.
Lemma lem1968609 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1968610 : term85 = term92.
Proof. exact (@lem1968609 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1968611 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1968612 : term85 = False.
Proof. exact (TRANS (@lem1968610) (@lem1968611)). Qed.
Lemma lem1968613 (h1 : term85) : False.
Proof. exact (EQ_MP (@lem1968612) (@lem1968607 h1)). Qed.
Lemma lem1968614 (h1 : term85) : term85.
Proof. exact (h1). Qed.
Lemma lem1968616 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1968617 : term85 = term92.
Proof. exact (@lem1968616 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1968618 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1968619 : term85 = False.
Proof. exact (TRANS (@lem1968617) (@lem1968618)). Qed.
Lemma lem1968620 (h1 : term85) : False.
Proof. exact (EQ_MP (@lem1968619) (@lem1968614 h1)). Qed.
Lemma lem1968621 (h1 : term90) : False.
Proof. exact (or_elim (@lem1968606 h1) (fun h0 : term85 => @lem1968613 h0) (fun h0 : term85 => @lem1968620 h0)). Qed.
Lemma lem1968623 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem1968624 (h1 : term90) : term90 = False.
Proof. exact (prop_ext (fun h2 : term90 => @lem1968621 h1) (fun h2 : False => @lem1968623 h1)). Qed.
Lemma lem1968625 (h1 : term90) : False.
Proof. exact (EQ_MP (@lem1968624 h1) (@lem1968623 h1)). Qed.
Lemma lem1968626 (x : real) (y : real) (h1 : term0 x y) : term0 x y.
Proof. exact (h1). Qed.
Lemma lem1968627 (x : real) (y : real) (h1 : term0 x y) : term90.
Proof. exact (EQ_MP (@lem1968596 x y) (@lem1968626 x y h1)). Qed.
Lemma lem1968628 (x : real) (y : real) (h1 : term0 x y) : term90 = False.
Proof. exact (prop_ext (fun h2 : term90 => @lem1968625 h2) (fun h2 : False => @lem1968627 x y h1)). Qed.
Lemma lem1968629 (x : real) (y : real) (h1 : term0 x y) : False.
Proof. exact (EQ_MP (@lem1968628 x y h1) (@lem1968627 x y h1)). Qed.
Lemma lem1968630 (x : real) (y : real) : term93 x y.
Proof. exact (fun h0 : term0 x y => @lem1968629 x y h0). Qed.
Lemma lem1968631 (x : real) (y : real) : term94 x y.
Proof. exact (@lem1386578 ((term2 x y) = (term3 x y))). Qed.
Lemma lem1968635 (x : real) (y : real) (h1 : (term95 x y) = (term96 x y)) : (term95 x y) = (term96 x y).
Proof. exact (h1). Qed.
Lemma lem1968636 (x : real) (y : real) (h1 : (term95 x y) = (term96 x y)) : (term96 x y) = (term95 x y).
Proof. exact (SYM (@lem1968635 x y h1)). Qed.
Lemma lem1968637 (x : real) (y : real) (h1 : (term96 x y) = (term95 x y)) : (term96 x y) = (term95 x y).
Proof. exact (h1). Qed.
Lemma lem1968638 (x : real) (y : real) (h1 : (term96 x y) = (term95 x y)) : (term95 x y) = (term96 x y).
Proof. exact (SYM (@lem1968637 x y h1)). Qed.
Lemma lem1968639 (x : real) (y : real) : ((term95 x y) = (term96 x y)) = ((term96 x y) = (term95 x y)).
Proof. exact (prop_ext (fun h1 : (term95 x y) = (term96 x y) => @lem1968636 x y h1) (fun h1 : (term96 x y) = (term95 x y) => @lem1968638 x y h1)). Qed.
Lemma lem1968640 (x : real) : (term97 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1968639 x y)). Qed.
Lemma lem1968641 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1968642 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem1968641) (@lem1968640 x)). Qed.
Lemma lem1968643 : term101 = term102.
Proof. exact (fun_ext (fun x : real => @lem1968642 x)). Qed.
Lemma lem1968644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1968645 : term103 = term104.
Proof. exact (MK_COMB (@lem1968644) (@lem1968643)). Qed.
Lemma lem1968646 : term104.
Proof. exact (EQ_MP (@lem1968645) (@lem1582313)). Qed.
Lemma lem1968647 (x : real) : term105 x.
Proof. exact (@lem1968646 x). Qed.
Lemma lem1968648 (x : real) : (term105 x) = (term100 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1968649 (x : real) : term100 x.
Proof. exact (EQ_MP (@lem1968648 x) (@lem1968647 x)). Qed.
Lemma lem1968650 (x : real) (y : real) : term106 x y.
Proof. exact (@lem1968649 x y). Qed.
Lemma lem1968651 (x : real) (y : real) : (term106 x y) = ((term96 x y) = (term95 x y)).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1968683 (x : real) (y : real) : (term107 x y) = (term108 x y).
Proof. exact (@lem17362 (term109 x y) (term110 x y)). Qed.
Lemma lem1968684 (x : real) : (term111 x) = (term112 x).
Proof. exact (@lem1483523 x term38). Qed.
Lemma lem1968690 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1483519 x term38). Qed.
Lemma lem1968692 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968693 : term79 = term38.
Proof. exact (@lem1968692 term40). Qed.
Lemma lem1968694 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1968695 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1968694 x) (@lem1968693)). Qed.
Lemma lem1968696 (x : real) : (term115 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1968697 (x : real) : (term114 x) = x.
Proof. exact (TRANS (@lem1968695 x) (@lem1968696 x)). Qed.
Lemma lem1968699 (x : real) : (term113 x) = x.
Proof. exact (TRANS (@lem1968690 x) (@lem1968697 x)). Qed.
Lemma lem1968700 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1968701 (x : real) : (term116 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1968700) (@lem1968699 x)). Qed.
Lemma lem1968702 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968703 (x : real) : (term112 x) = (term117 x).
Proof. exact (MK_COMB (@lem1968701 x) (@lem1968702)). Qed.
Lemma lem1968704 (x : real) : (term111 x) = (term117 x).
Proof. exact (TRANS (@lem1968684 x) (@lem1968703 x)). Qed.
Lemma lem1968705 (y : real) : (term111 y) = (term112 y).
Proof. exact (@lem1483523 y term38). Qed.
Lemma lem1968711 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483519 y term38). Qed.
Lemma lem1968713 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968714 : term79 = term38.
Proof. exact (@lem1968713 term40). Qed.
Lemma lem1968715 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1968716 (y : real) : (term114 y) = (term115 y).
Proof. exact (MK_COMB (@lem1968715 y) (@lem1968714)). Qed.
Lemma lem1968717 (y : real) : (term115 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1968718 (y : real) : (term114 y) = y.
Proof. exact (TRANS (@lem1968716 y) (@lem1968717 y)). Qed.
Lemma lem1968720 (y : real) : (term113 y) = y.
Proof. exact (TRANS (@lem1968711 y) (@lem1968718 y)). Qed.
Lemma lem1968721 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1968722 (y : real) : (term116 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1968721) (@lem1968720 y)). Qed.
Lemma lem1968723 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968724 (y : real) : (term112 y) = (term117 y).
Proof. exact (MK_COMB (@lem1968722 y) (@lem1968723)). Qed.
Lemma lem1968725 (y : real) : (term111 y) = (term117 y).
Proof. exact (TRANS (@lem1968705 y) (@lem1968724 y)). Qed.
Lemma lem1968726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968727 (x : real) : (term118 x) = (term119 x).
Proof. exact (MK_COMB (@lem1968726) (@lem1968704 x)). Qed.
Lemma lem1968728 (x : real) (y : real) : (term109 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1968727 x) (@lem1968725 y)). Qed.
Lemma lem1968729 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (@lem1483533 (term123 x y) (term124 x y)). Qed.
Lemma lem1968735 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem1483519 (term123 x y) (term124 x y)). Qed.
Lemma lem1968740 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (@lem1483488 (term128 x y) (term123 x y)). Qed.
Lemma lem1968742 (x : real) (y : real) : (term125 x y) = (term127 x y).
Proof. exact (TRANS (@lem1968735 x y) (@lem1968740 x y)). Qed.
Lemma lem1968743 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1968744 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1968743) (@lem1968742 x y)). Qed.
Lemma lem1968745 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968746 (x : real) (y : real) : (term122 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1968744 x y) (@lem1968745)). Qed.
Lemma lem1968747 (x : real) (y : real) : (term121 x y) = (term131 x y).
Proof. exact (TRANS (@lem1968729 x y) (@lem1968746 x y)). Qed.
Lemma lem1968748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968749 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1968748) (@lem1968728 x y)). Qed.
Lemma lem1968750 (x : real) (y : real) : (term108 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1968749 x y) (@lem1968747 x y)). Qed.
Lemma lem1968771 (x : real) (y : real) : (term107 x y) = (term134 x y).
Proof. exact (TRANS (@lem1968683 x y) (@lem1968750 x y)). Qed.
Lemma lem1968773 (a : real) (x : real) (r : real) : (term135 x a r) = (term136 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1968774 (x : real) (y : real) : (term131 x y) = (term137 x y).
Proof. exact (@lem1968773 (term123 x y) (real_add x y) term38). Qed.
Lemma lem1968787 (x : real) (y : real) : (term138 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1968790 (x : real) (y : real) : (term139 x y) = (term139 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1968791 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1968790 x y) (@lem1968787 x y)). Qed.
Lemma lem1968792 (x : real) (y : real) : (term141 x y) = (term142 x y).
Proof. exact (@lem1483484 x (term123 x y) y). Qed.
Lemma lem1968793 (x : real) (y : real) : (term143 x y) = (term144 x y).
Proof. exact (@lem1483488 y (term123 x y)). Qed.
Lemma lem1968794 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1968795 (x : real) (y : real) : (term142 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1968794 x) (@lem1968793 x y)). Qed.
Lemma lem1968796 (x : real) (y : real) : (term141 x y) = (term145 x y).
Proof. exact (TRANS (@lem1968792 x y) (@lem1968795 x y)). Qed.
Lemma lem1968797 (x : real) (y : real) : (term140 x y) = (term145 x y).
Proof. exact (TRANS (@lem1968791 x y) (@lem1968796 x y)). Qed.
Lemma lem1968798 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1968799 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1968798) (@lem1968797 x y)). Qed.
Lemma lem1968800 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968801 (x : real) (y : real) : (term148 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1968799 x y) (@lem1968800)). Qed.
Lemma lem1968820 (x : real) (y : real) : (term150 x y) = (term151 x y).
Proof. exact (@lem1483508 x term23 y). Qed.
Lemma lem1968823 (x : real) (y : real) : (term139 x y) = (term139 x y).
Proof. exact (eq_refl (term139 x y)). Qed.
Lemma lem1968824 (x : real) (y : real) : (term152 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem1968823 x y) (@lem1968820 x y)). Qed.
Lemma lem1968825 (x : real) (y : real) : (term153 x y) = (term154 x y).
Proof. exact (@lem1483484 (term11 x) (term123 x y) (term11 y)). Qed.
Lemma lem1968826 (x : real) (y : real) : (term155 x y) = (term156 x y).
Proof. exact (@lem1483488 (term11 y) (term123 x y)). Qed.
Lemma lem1968827 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1968828 (x : real) (y : real) : (term154 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1968827 x) (@lem1968826 x y)). Qed.
Lemma lem1968829 (x : real) (y : real) : (term153 x y) = (term158 x y).
Proof. exact (TRANS (@lem1968825 x y) (@lem1968828 x y)). Qed.
Lemma lem1968830 (x : real) (y : real) : (term152 x y) = (term158 x y).
Proof. exact (TRANS (@lem1968824 x y) (@lem1968829 x y)). Qed.
Lemma lem1968831 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1968832 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1968831) (@lem1968830 x y)). Qed.
Lemma lem1968833 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968834 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (MK_COMB (@lem1968832 x y) (@lem1968833)). Qed.
Lemma lem1968835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968836 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1968835) (@lem1968834 x y)). Qed.
Lemma lem1968837 (x : real) (y : real) : (term137 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1968836 x y) (@lem1968801 x y)). Qed.
Lemma lem1968838 (x : real) (y : real) : (term131 x y) = (term165 x y).
Proof. exact (TRANS (@lem1968774 x y) (@lem1968837 x y)). Qed.
Lemma lem1968839 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1968840 (x : real) (y : real) : (term134 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1968839 x y) (@lem1968838 x y)). Qed.
Lemma lem1968841 (x : real) (y : real) : (term167 x y) = (term166 x y).
Proof. exact (eq_refl (term167 x y)). Qed.
Lemma lem1968842 (x : real) (y : real) : (term166 x y) = (term167 x y).
Proof. exact (SYM (@lem1968841 x y)). Qed.
Lemma lem1968843 (x : real) (y : real) : (term167 x y) = (term168 x y).
Proof. exact (@lem1482981 (term169 x y) (real_sub x y)). Qed.
Lemma lem1968844 (x : real) (y : real) : (term166 x y) = (term168 x y).
Proof. exact (TRANS (@lem1968842 x y) (@lem1968843 x y)). Qed.
Lemma lem1968845 (x : real) (y : real) : (term170 x y) = (term171 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1968846 (x : real) (y : real) : (term172 x y) = (term172 x y).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1968847 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1968846 x y) (@lem1968845 x y)). Qed.
Lemma lem1968848 (x : real) (y : real) : (term175 x y) = (term176 x y).
Proof. exact (eq_refl (term175 x y)). Qed.
Lemma lem1968849 (x : real) (y : real) : (term177 x y) = (term177 x y).
Proof. exact (eq_refl (term177 x y)). Qed.
Lemma lem1968850 (x : real) (y : real) : (term178 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem1968849 x y) (@lem1968848 x y)). Qed.
Lemma lem1968851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1968852 (x : real) (y : real) : (term180 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1968851) (@lem1968850 x y)). Qed.
Lemma lem1968853 (x : real) (y : real) : (term168 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1968852 x y) (@lem1968847 x y)). Qed.
Lemma lem1968854 (x : real) (y : real) : (term183 x y) = (term183 x y).
Proof. exact (eq_refl (term183 x y)). Qed.
Lemma lem1968855 (x : real) (y : real) : ((term166 x y) = (term168 x y)) = ((term166 x y) = (term182 x y)).
Proof. exact (MK_COMB (@lem1968854 x y) (@lem1968853 x y)). Qed.
Lemma lem1968856 (x : real) (y : real) : (term166 x y) = (term182 x y).
Proof. exact (EQ_MP (@lem1968855 x y) (@lem1968844 x y)). Qed.
Lemma lem1968857 (x : real) (y : real) : (term184 x y) = (term185 x y).
Proof. exact (@lem1483527 (real_sub x y) term38). Qed.
Lemma lem1968858 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968871 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1968872 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1968873 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1968872) (@lem1968871 x y)). Qed.
Lemma lem1968874 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem1968873 x y) (@lem1968858)). Qed.
Lemma lem1968875 (x : real) (y : real) : (term189 x y) = (term190 x y).
Proof. exact (@lem1483519 (term6 x y) term38). Qed.
Lemma lem1968877 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968878 : term79 = term38.
Proof. exact (@lem1968877 term40). Qed.
Lemma lem1968879 (x : real) (y : real) : (term191 x y) = (term191 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1968880 (x : real) (y : real) : (term190 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1968879 x y) (@lem1968878)). Qed.
Lemma lem1968881 (x : real) (y : real) : (term192 x y) = (term6 x y).
Proof. exact (@lem1483450 (term6 x y)). Qed.
Lemma lem1968882 (x : real) (y : real) : (term190 x y) = (term6 x y).
Proof. exact (TRANS (@lem1968880 x y) (@lem1968881 x y)). Qed.
Lemma lem1968883 (x : real) (y : real) : (term189 x y) = (term6 x y).
Proof. exact (TRANS (@lem1968875 x y) (@lem1968882 x y)). Qed.
Lemma lem1968884 (x : real) (y : real) : (term188 x y) = (term6 x y).
Proof. exact (TRANS (@lem1968874 x y) (@lem1968883 x y)). Qed.
Lemma lem1968885 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1968886 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem1968885) (@lem1968884 x y)). Qed.
Lemma lem1968887 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968888 (x : real) (y : real) : (term185 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1968886 x y) (@lem1968887)). Qed.
Lemma lem1968889 (x : real) (y : real) : (term184 x y) = (term195 x y).
Proof. exact (TRANS (@lem1968857 x y) (@lem1968888 x y)). Qed.
Lemma lem1968890 (x : real) : (term117 x) = (term112 x).
Proof. exact (@lem1483527 x term38). Qed.
Lemma lem1968896 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1483519 x term38). Qed.
Lemma lem1968898 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968899 : term79 = term38.
Proof. exact (@lem1968898 term40). Qed.
Lemma lem1968900 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1968901 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1968900 x) (@lem1968899)). Qed.
Lemma lem1968902 (x : real) : (term115 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1968903 (x : real) : (term114 x) = x.
Proof. exact (TRANS (@lem1968901 x) (@lem1968902 x)). Qed.
Lemma lem1968905 (x : real) : (term113 x) = x.
Proof. exact (TRANS (@lem1968896 x) (@lem1968903 x)). Qed.
Lemma lem1968906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1968907 (x : real) : (term116 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1968906) (@lem1968905 x)). Qed.
Lemma lem1968908 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968909 (x : real) : (term112 x) = (term117 x).
Proof. exact (MK_COMB (@lem1968907 x) (@lem1968908)). Qed.
Lemma lem1968910 (x : real) : (term117 x) = (term117 x).
Proof. exact (TRANS (@lem1968890 x) (@lem1968909 x)). Qed.
Lemma lem1968911 (y : real) : (term117 y) = (term112 y).
Proof. exact (@lem1483527 y term38). Qed.
Lemma lem1968917 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483519 y term38). Qed.
Lemma lem1968919 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1968920 : term79 = term38.
Proof. exact (@lem1968919 term40). Qed.
Lemma lem1968921 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1968922 (y : real) : (term114 y) = (term115 y).
Proof. exact (MK_COMB (@lem1968921 y) (@lem1968920)). Qed.
Lemma lem1968923 (y : real) : (term115 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1968924 (y : real) : (term114 y) = y.
Proof. exact (TRANS (@lem1968922 y) (@lem1968923 y)). Qed.
Lemma lem1968926 (y : real) : (term113 y) = y.
Proof. exact (TRANS (@lem1968917 y) (@lem1968924 y)). Qed.
Lemma lem1968927 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1968928 (y : real) : (term116 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1968927) (@lem1968926 y)). Qed.
Lemma lem1968929 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968930 (y : real) : (term112 y) = (term117 y).
Proof. exact (MK_COMB (@lem1968928 y) (@lem1968929)). Qed.
Lemma lem1968931 (y : real) : (term117 y) = (term117 y).
Proof. exact (TRANS (@lem1968911 y) (@lem1968930 y)). Qed.
Lemma lem1968932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968933 (x : real) : (term119 x) = (term119 x).
Proof. exact (MK_COMB (@lem1968932) (@lem1968910 x)). Qed.
Lemma lem1968934 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1968933 x) (@lem1968931 y)). Qed.
Lemma lem1968935 (x : real) (y : real) : (term196 x y) = (term197 x y).
Proof. exact (@lem1483525 (term198 x y) term38). Qed.
Lemma lem1968936 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1968949 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1968958 (y : real) : (term157 y) = (term157 y).
Proof. exact (eq_refl (term157 y)). Qed.
Lemma lem1968959 (x : real) (y : real) : (term199 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1968958 y) (@lem1968949 x y)). Qed.
Lemma lem1968960 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (@lem1483484 x (term11 y) (term11 y)). Qed.
Lemma lem1968961 (y : real) : (term202 y) = (term203 y).
Proof. exact (@lem1483438 term23 term23 y). Qed.
Lemma lem1968962 : term204 = term205.
Proof. exact (@lem1367763 term40 term40). Qed.
Lemma lem1968963 : term206 = term207.
Proof. exact (@lem706885). Qed.
Lemma lem1968964 : (term206 = term207) = (term208 = term209).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term207). Qed.
Lemma lem1968965 : term208 = term209.
Proof. exact (EQ_MP (@lem1968964) (@lem1968963)). Qed.
Lemma lem1968966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1968967 : term210 = term211.
Proof. exact (MK_COMB (@lem1968966) (@lem1968965)). Qed.
Lemma lem1968968 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1968969 : term205 = term212.
Proof. exact (MK_COMB (@lem1968968) (@lem1968967)). Qed.
Lemma lem1968970 : term204 = term212.
Proof. exact (TRANS (@lem1968962) (@lem1968969)). Qed.
Lemma lem1968971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968972 : term213 = term214.
Proof. exact (MK_COMB (@lem1968971) (@lem1968970)). Qed.
Lemma lem1968973 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1968974 (y : real) : (term203 y) = (term215 y).
Proof. exact (MK_COMB (@lem1968972) (@lem1968973 y)). Qed.
Lemma lem1968975 (y : real) : (term202 y) = (term215 y).
Proof. exact (TRANS (@lem1968961 y) (@lem1968974 y)). Qed.
Lemma lem1968976 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1968977 (x : real) (y : real) : (term201 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem1968976 x) (@lem1968975 y)). Qed.
Lemma lem1968978 (x : real) (y : real) : (term200 x y) = (term216 x y).
Proof. exact (TRANS (@lem1968960 x y) (@lem1968977 x y)). Qed.
Lemma lem1968979 (x : real) (y : real) : (term199 x y) = (term216 x y).
Proof. exact (TRANS (@lem1968959 x y) (@lem1968978 x y)). Qed.
Lemma lem1968988 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1968989 (x : real) (y : real) : (term198 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1968988 x) (@lem1968979 x y)). Qed.
Lemma lem1968990 (x : real) (y : real) : (term217 x y) = (term218 x y).
Proof. exact (@lem1483490 (term11 x) x (term215 y)). Qed.
Lemma lem1968991 (x : real) : (term219 x) = (term220 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1968993 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1968994 : term39 = term38.
Proof. exact (@lem1968993 term40). Qed.
Lemma lem1968995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1968996 : term41 = term42.
Proof. exact (MK_COMB (@lem1968995) (@lem1968994)). Qed.
Lemma lem1968997 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1968998 (x : real) : (term220 x) = (term221 x).
Proof. exact (MK_COMB (@lem1968996) (@lem1968997 x)). Qed.
Lemma lem1968999 (x : real) : (term219 x) = (term221 x).
Proof. exact (TRANS (@lem1968991 x) (@lem1968998 x)). Qed.
Lemma lem1969000 (x : real) : (term221 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1969001 (x : real) : (term219 x) = term38.
Proof. exact (TRANS (@lem1968999 x) (@lem1969000 x)). Qed.
Lemma lem1969002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1969003 (x : real) : (term222 x) = term45.
Proof. exact (MK_COMB (@lem1969002) (@lem1969001 x)). Qed.
Lemma lem1969004 (y : real) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1969005 (x : real) (y : real) : (term218 x y) = (term223 y).
Proof. exact (MK_COMB (@lem1969003 x) (@lem1969004 y)). Qed.
Lemma lem1969006 (x : real) (y : real) : (term217 x y) = (term223 y).
Proof. exact (TRANS (@lem1968990 x y) (@lem1969005 x y)). Qed.
Lemma lem1969007 (y : real) : (term223 y) = (term215 y).
Proof. exact (@lem1483448 (term215 y)). Qed.
Lemma lem1969008 (x : real) (y : real) : (term217 x y) = (term215 y).
Proof. exact (TRANS (@lem1969006 x y) (@lem1969007 y)). Qed.
Lemma lem1969009 (x : real) (y : real) : (term198 x y) = (term215 y).
Proof. exact (TRANS (@lem1968989 x y) (@lem1969008 x y)). Qed.
Lemma lem1969010 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1969011 (x : real) (y : real) : (term224 x y) = (term225 y).
Proof. exact (MK_COMB (@lem1969010) (@lem1969009 x y)). Qed.
Lemma lem1969012 (x : real) (y : real) : (term226 x y) = (term227 y).
Proof. exact (MK_COMB (@lem1969011 x y) (@lem1968936)). Qed.
Lemma lem1969013 (y : real) : (term227 y) = (term228 y).
Proof. exact (@lem1483519 (term215 y) term38). Qed.
Lemma lem1969015 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1969016 : term79 = term38.
Proof. exact (@lem1969015 term40). Qed.
Lemma lem1969017 (y : real) : (term229 y) = (term229 y).
Proof. exact (eq_refl (term229 y)). Qed.
Lemma lem1969018 (y : real) : (term228 y) = (term230 y).
Proof. exact (MK_COMB (@lem1969017 y) (@lem1969016)). Qed.
Lemma lem1969019 (y : real) : (term230 y) = (term215 y).
Proof. exact (@lem1483450 (term215 y)). Qed.
Lemma lem1969020 (y : real) : (term228 y) = (term215 y).
Proof. exact (TRANS (@lem1969018 y) (@lem1969019 y)). Qed.
Lemma lem1969021 (y : real) : (term227 y) = (term215 y).
Proof. exact (TRANS (@lem1969013 y) (@lem1969020 y)). Qed.
Lemma lem1969022 (x : real) (y : real) : (term226 x y) = (term215 y).
Proof. exact (TRANS (@lem1969012 x y) (@lem1969021 y)). Qed.
Lemma lem1969023 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969024 (x : real) (y : real) : (term231 x y) = (term232 y).
Proof. exact (MK_COMB (@lem1969023) (@lem1969022 x y)). Qed.
Lemma lem1969025 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969026 (x : real) (y : real) : (term197 x y) = (term233 y).
Proof. exact (MK_COMB (@lem1969024 x y) (@lem1969025)). Qed.
Lemma lem1969027 (x : real) (y : real) : (term196 x y) = (term233 y).
Proof. exact (TRANS (@lem1968935 x y) (@lem1969026 x y)). Qed.
Lemma lem1969028 (x : real) (y : real) : (term234 x y) = (term235 x y).
Proof. exact (@lem1483525 (term236 x y) term38). Qed.
Lemma lem1969029 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969042 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1969045 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1969046 (x : real) (y : real) : (term237 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1969045 y) (@lem1969042 x y)). Qed.
Lemma lem1969047 (x : real) (y : real) : (term238 x y) = (term239 x y).
Proof. exact (@lem1483484 x y (term11 y)). Qed.
Lemma lem1969048 (y : real) : (term240 y) = (term220 y).
Proof. exact (@lem1483442 term23 y). Qed.
Lemma lem1969050 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1969051 : term39 = term38.
Proof. exact (@lem1969050 term40). Qed.
Lemma lem1969052 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969053 : term41 = term42.
Proof. exact (MK_COMB (@lem1969052) (@lem1969051)). Qed.
Lemma lem1969054 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969055 (y : real) : (term220 y) = (term221 y).
Proof. exact (MK_COMB (@lem1969053) (@lem1969054 y)). Qed.
Lemma lem1969056 (y : real) : (term240 y) = (term221 y).
Proof. exact (TRANS (@lem1969048 y) (@lem1969055 y)). Qed.
Lemma lem1969057 (y : real) : (term221 y) = term38.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1969058 (y : real) : (term240 y) = term38.
Proof. exact (TRANS (@lem1969056 y) (@lem1969057 y)). Qed.
Lemma lem1969059 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1969060 (y : real) (x : real) : (term239 x y) = (term115 x).
Proof. exact (MK_COMB (@lem1969059 x) (@lem1969058 y)). Qed.
Lemma lem1969061 (y : real) (x : real) : (term238 x y) = (term115 x).
Proof. exact (TRANS (@lem1969047 x y) (@lem1969060 y x)). Qed.
Lemma lem1969062 (x : real) : (term115 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1969063 (y : real) (x : real) : (term238 x y) = x.
Proof. exact (TRANS (@lem1969061 y x) (@lem1969062 x)). Qed.
Lemma lem1969064 (y : real) (x : real) : (term237 x y) = x.
Proof. exact (TRANS (@lem1969046 x y) (@lem1969063 y x)). Qed.
Lemma lem1969067 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1969068 (y : real) (x : real) : (term236 x y) = (real_add x x).
Proof. exact (MK_COMB (@lem1969067 x) (@lem1969064 y x)). Qed.
Lemma lem1969069 (x : real) : (real_add x x) = (term241 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1969070 : term242 = term210.
Proof. exact (@lem1367770 term40 term40). Qed.
Lemma lem1969071 : term206 = term207.
Proof. exact (@lem706885). Qed.
Lemma lem1969072 : (term206 = term207) = (term208 = term209).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term207). Qed.
Lemma lem1969073 : term208 = term209.
Proof. exact (EQ_MP (@lem1969072) (@lem1969071)). Qed.
Lemma lem1969074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969075 : term210 = term211.
Proof. exact (MK_COMB (@lem1969074) (@lem1969073)). Qed.
Lemma lem1969076 : term242 = term211.
Proof. exact (TRANS (@lem1969070) (@lem1969075)). Qed.
Lemma lem1969077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969078 : term243 = term244.
Proof. exact (MK_COMB (@lem1969077) (@lem1969076)). Qed.
Lemma lem1969079 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1969080 (x : real) : (term241 x) = (term245 x).
Proof. exact (MK_COMB (@lem1969078) (@lem1969079 x)). Qed.
Lemma lem1969081 (x : real) : (real_add x x) = (term245 x).
Proof. exact (TRANS (@lem1969069 x) (@lem1969080 x)). Qed.
Lemma lem1969082 (y : real) (x : real) : (term236 x y) = (term245 x).
Proof. exact (TRANS (@lem1969068 y x) (@lem1969081 x)). Qed.
Lemma lem1969083 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1969084 (y : real) (x : real) : (term246 x y) = (term247 x).
Proof. exact (MK_COMB (@lem1969083) (@lem1969082 y x)). Qed.
Lemma lem1969085 (y : real) (x : real) : (term248 x y) = (term249 x).
Proof. exact (MK_COMB (@lem1969084 y x) (@lem1969029)). Qed.
Lemma lem1969086 (x : real) : (term249 x) = (term250 x).
Proof. exact (@lem1483519 (term245 x) term38). Qed.
Lemma lem1969088 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1969089 : term79 = term38.
Proof. exact (@lem1969088 term40). Qed.
Lemma lem1969090 (x : real) : (term251 x) = (term251 x).
Proof. exact (eq_refl (term251 x)). Qed.
Lemma lem1969091 (x : real) : (term250 x) = (term252 x).
Proof. exact (MK_COMB (@lem1969090 x) (@lem1969089)). Qed.
Lemma lem1969092 (x : real) : (term252 x) = (term245 x).
Proof. exact (@lem1483450 (term245 x)). Qed.
Lemma lem1969093 (x : real) : (term250 x) = (term245 x).
Proof. exact (TRANS (@lem1969091 x) (@lem1969092 x)). Qed.
Lemma lem1969094 (x : real) : (term249 x) = (term245 x).
Proof. exact (TRANS (@lem1969086 x) (@lem1969093 x)). Qed.
Lemma lem1969095 (y : real) (x : real) : (term248 x y) = (term245 x).
Proof. exact (TRANS (@lem1969085 y x) (@lem1969094 x)). Qed.
Lemma lem1969096 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969097 (y : real) (x : real) : (term253 x y) = (term254 x).
Proof. exact (MK_COMB (@lem1969096) (@lem1969095 y x)). Qed.
Lemma lem1969098 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969099 (y : real) (x : real) : (term235 x y) = (term255 x).
Proof. exact (MK_COMB (@lem1969097 y x) (@lem1969098)). Qed.
Lemma lem1969100 (y : real) (x : real) : (term234 x y) = (term255 x).
Proof. exact (TRANS (@lem1969028 x y) (@lem1969099 y x)). Qed.
Lemma lem1969101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969102 (x : real) (y : real) : (term256 x y) = (term257 y).
Proof. exact (MK_COMB (@lem1969101) (@lem1969027 x y)). Qed.
Lemma lem1969103 (y : real) (x : real) : (term258 x y) = (term259 y x).
Proof. exact (MK_COMB (@lem1969102 x y) (@lem1969100 y x)). Qed.
Lemma lem1969104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969105 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1969104) (@lem1968934 x y)). Qed.
Lemma lem1969106 (y : real) (x : real) : (term176 x y) = (term260 y x).
Proof. exact (MK_COMB (@lem1969105 x y) (@lem1969103 y x)). Qed.
Lemma lem1969107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969108 (x : real) (y : real) : (term177 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1969107) (@lem1968889 x y)). Qed.
Lemma lem1969109 (y : real) (x : real) : (term179 x y) = (term262 y x).
Proof. exact (MK_COMB (@lem1969108 x y) (@lem1969106 y x)). Qed.
Lemma lem1969110 (x : real) (y : real) : (term263 x y) = (term264 x y).
Proof. exact (@lem1483525 term38 (real_sub x y)). Qed.
Lemma lem1969123 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1969126 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem1969127 (x : real) (y : real) : (term266 x y) = (term267 x y).
Proof. exact (MK_COMB (@lem1969126) (@lem1969123 x y)). Qed.
Lemma lem1969128 (x : real) (y : real) : (term267 x y) = (term268 x y).
Proof. exact (@lem1483519 term38 (term6 x y)). Qed.
Lemma lem1969129 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (@lem1483508 x term23 (term11 y)). Qed.
Lemma lem1969130 (y : real) : (term271 y) = (term272 y).
Proof. exact (@lem1483476 term23 term23 y). Qed.
Lemma lem1969132 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1969133 : term58 = term59.
Proof. exact (@lem1969132 term40 term40). Qed.
Lemma lem1969134 : (term60 = (BIT1 0)) = (term61 = term40).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1969135 : term61 = term40.
Proof. exact (EQ_MP (@lem1969134) (@lem940073)). Qed.
Lemma lem1969136 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969137 : term59 = term62.
Proof. exact (MK_COMB (@lem1969136) (@lem1969135)). Qed.
Lemma lem1969138 : term58 = term62.
Proof. exact (TRANS (@lem1969133) (@lem1969137)). Qed.
Lemma lem1969139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969140 : term63 = term64.
Proof. exact (MK_COMB (@lem1969139) (@lem1969138)). Qed.
Lemma lem1969141 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969142 (y : real) : (term272 y) = (term273 y).
Proof. exact (MK_COMB (@lem1969140) (@lem1969141 y)). Qed.
Lemma lem1969143 (y : real) : (term271 y) = (term273 y).
Proof. exact (TRANS (@lem1969130 y) (@lem1969142 y)). Qed.
Lemma lem1969144 (y : real) : (term273 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1969145 (y : real) : (term271 y) = y.
Proof. exact (TRANS (@lem1969143 y) (@lem1969144 y)). Qed.
Lemma lem1969148 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969149 (x : real) (y : real) : (term270 x y) = (term274 x y).
Proof. exact (MK_COMB (@lem1969148 x) (@lem1969145 y)). Qed.
Lemma lem1969150 (x : real) (y : real) : (term269 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969129 x y) (@lem1969149 x y)). Qed.
Lemma lem1969151 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem1969152 (x : real) (y : real) : (term268 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem1969151) (@lem1969150 x y)). Qed.
Lemma lem1969153 (x : real) (y : real) : (term275 x y) = (term274 x y).
Proof. exact (@lem1483448 (term274 x y)). Qed.
Lemma lem1969154 (x : real) (y : real) : (term268 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969152 x y) (@lem1969153 x y)). Qed.
Lemma lem1969155 (x : real) (y : real) : (term267 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969128 x y) (@lem1969154 x y)). Qed.
Lemma lem1969156 (x : real) (y : real) : (term266 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969127 x y) (@lem1969155 x y)). Qed.
Lemma lem1969157 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969158 (x : real) (y : real) : (term276 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1969157) (@lem1969156 x y)). Qed.
Lemma lem1969159 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969160 (x : real) (y : real) : (term264 x y) = (term278 x y).
Proof. exact (MK_COMB (@lem1969158 x y) (@lem1969159)). Qed.
Lemma lem1969161 (x : real) (y : real) : (term263 x y) = (term278 x y).
Proof. exact (TRANS (@lem1969110 x y) (@lem1969160 x y)). Qed.
Lemma lem1969162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969163 (x : real) : (term119 x) = (term119 x).
Proof. exact (MK_COMB (@lem1969162) (@lem1968910 x)). Qed.
Lemma lem1969164 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1969163 x) (@lem1968931 y)). Qed.
Lemma lem1969165 (x : real) (y : real) : (term279 x y) = (term280 x y).
Proof. exact (@lem1483525 (term281 x y) term38). Qed.
Lemma lem1969166 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969179 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1969180 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1969181 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem1969180) (@lem1969179 x y)). Qed.
Lemma lem1969182 (x : real) (y : real) : (term283 x y) = (term269 x y).
Proof. exact (@lem1483512 (term6 x y)). Qed.
Lemma lem1969183 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (@lem1483508 x term23 (term11 y)). Qed.
Lemma lem1969184 (y : real) : (term271 y) = (term272 y).
Proof. exact (@lem1483476 term23 term23 y). Qed.
Lemma lem1969186 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1969187 : term58 = term59.
Proof. exact (@lem1969186 term40 term40). Qed.
Lemma lem1969188 : (term60 = (BIT1 0)) = (term61 = term40).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1969189 : term61 = term40.
Proof. exact (EQ_MP (@lem1969188) (@lem940073)). Qed.
Lemma lem1969190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969191 : term59 = term62.
Proof. exact (MK_COMB (@lem1969190) (@lem1969189)). Qed.
Lemma lem1969192 : term58 = term62.
Proof. exact (TRANS (@lem1969187) (@lem1969191)). Qed.
Lemma lem1969193 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969194 : term63 = term64.
Proof. exact (MK_COMB (@lem1969193) (@lem1969192)). Qed.
Lemma lem1969195 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969196 (y : real) : (term272 y) = (term273 y).
Proof. exact (MK_COMB (@lem1969194) (@lem1969195 y)). Qed.
Lemma lem1969197 (y : real) : (term271 y) = (term273 y).
Proof. exact (TRANS (@lem1969184 y) (@lem1969196 y)). Qed.
Lemma lem1969198 (y : real) : (term273 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1969199 (y : real) : (term271 y) = y.
Proof. exact (TRANS (@lem1969197 y) (@lem1969198 y)). Qed.
Lemma lem1969202 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969203 (x : real) (y : real) : (term270 x y) = (term274 x y).
Proof. exact (MK_COMB (@lem1969202 x) (@lem1969199 y)). Qed.
Lemma lem1969204 (x : real) (y : real) : (term269 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969183 x y) (@lem1969203 x y)). Qed.
Lemma lem1969205 (x : real) (y : real) : (term283 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969182 x y) (@lem1969204 x y)). Qed.
Lemma lem1969206 (x : real) (y : real) : (term282 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969181 x y) (@lem1969205 x y)). Qed.
Lemma lem1969215 (y : real) : (term157 y) = (term157 y).
Proof. exact (eq_refl (term157 y)). Qed.
Lemma lem1969216 (x : real) (y : real) : (term284 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1969215 y) (@lem1969206 x y)). Qed.
Lemma lem1969217 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (@lem1483484 (term11 x) (term11 y) y). Qed.
Lemma lem1969218 (y : real) : (term219 y) = (term220 y).
Proof. exact (@lem1483440 term23 y). Qed.
Lemma lem1969220 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1969221 : term39 = term38.
Proof. exact (@lem1969220 term40). Qed.
Lemma lem1969222 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969223 : term41 = term42.
Proof. exact (MK_COMB (@lem1969222) (@lem1969221)). Qed.
Lemma lem1969224 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969225 (y : real) : (term220 y) = (term221 y).
Proof. exact (MK_COMB (@lem1969223) (@lem1969224 y)). Qed.
Lemma lem1969226 (y : real) : (term219 y) = (term221 y).
Proof. exact (TRANS (@lem1969218 y) (@lem1969225 y)). Qed.
Lemma lem1969227 (y : real) : (term221 y) = term38.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1969228 (y : real) : (term219 y) = term38.
Proof. exact (TRANS (@lem1969226 y) (@lem1969227 y)). Qed.
Lemma lem1969229 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969230 (y : real) (x : real) : (term286 x y) = (term287 x).
Proof. exact (MK_COMB (@lem1969229 x) (@lem1969228 y)). Qed.
Lemma lem1969231 (y : real) (x : real) : (term285 x y) = (term287 x).
Proof. exact (TRANS (@lem1969217 x y) (@lem1969230 y x)). Qed.
Lemma lem1969232 (x : real) : (term287 x) = (term11 x).
Proof. exact (@lem1483450 (term11 x)). Qed.
Lemma lem1969233 (y : real) (x : real) : (term285 x y) = (term11 x).
Proof. exact (TRANS (@lem1969231 y x) (@lem1969232 x)). Qed.
Lemma lem1969234 (y : real) (x : real) : (term284 x y) = (term11 x).
Proof. exact (TRANS (@lem1969216 x y) (@lem1969233 y x)). Qed.
Lemma lem1969243 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969244 (y : real) (x : real) : (term281 x y) = (term202 x).
Proof. exact (MK_COMB (@lem1969243 x) (@lem1969234 y x)). Qed.
Lemma lem1969245 (x : real) : (term202 x) = (term203 x).
Proof. exact (@lem1483438 term23 term23 x). Qed.
Lemma lem1969246 : term204 = term205.
Proof. exact (@lem1367763 term40 term40). Qed.
Lemma lem1969247 : term206 = term207.
Proof. exact (@lem706885). Qed.
Lemma lem1969248 : (term206 = term207) = (term208 = term209).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term207). Qed.
Lemma lem1969249 : term208 = term209.
Proof. exact (EQ_MP (@lem1969248) (@lem1969247)). Qed.
Lemma lem1969250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969251 : term210 = term211.
Proof. exact (MK_COMB (@lem1969250) (@lem1969249)). Qed.
Lemma lem1969252 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1969253 : term205 = term212.
Proof. exact (MK_COMB (@lem1969252) (@lem1969251)). Qed.
Lemma lem1969254 : term204 = term212.
Proof. exact (TRANS (@lem1969246) (@lem1969253)). Qed.
Lemma lem1969255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969256 : term213 = term214.
Proof. exact (MK_COMB (@lem1969255) (@lem1969254)). Qed.
Lemma lem1969257 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1969258 (x : real) : (term203 x) = (term215 x).
Proof. exact (MK_COMB (@lem1969256) (@lem1969257 x)). Qed.
Lemma lem1969259 (x : real) : (term202 x) = (term215 x).
Proof. exact (TRANS (@lem1969245 x) (@lem1969258 x)). Qed.
Lemma lem1969260 (y : real) (x : real) : (term281 x y) = (term215 x).
Proof. exact (TRANS (@lem1969244 y x) (@lem1969259 x)). Qed.
Lemma lem1969261 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1969262 (y : real) (x : real) : (term288 x y) = (term225 x).
Proof. exact (MK_COMB (@lem1969261) (@lem1969260 y x)). Qed.
Lemma lem1969263 (y : real) (x : real) : (term289 x y) = (term227 x).
Proof. exact (MK_COMB (@lem1969262 y x) (@lem1969166)). Qed.
Lemma lem1969264 (x : real) : (term227 x) = (term228 x).
Proof. exact (@lem1483519 (term215 x) term38). Qed.
Lemma lem1969266 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1969267 : term79 = term38.
Proof. exact (@lem1969266 term40). Qed.
Lemma lem1969268 (x : real) : (term229 x) = (term229 x).
Proof. exact (eq_refl (term229 x)). Qed.
Lemma lem1969269 (x : real) : (term228 x) = (term230 x).
Proof. exact (MK_COMB (@lem1969268 x) (@lem1969267)). Qed.
Lemma lem1969270 (x : real) : (term230 x) = (term215 x).
Proof. exact (@lem1483450 (term215 x)). Qed.
Lemma lem1969271 (x : real) : (term228 x) = (term215 x).
Proof. exact (TRANS (@lem1969269 x) (@lem1969270 x)). Qed.
Lemma lem1969272 (x : real) : (term227 x) = (term215 x).
Proof. exact (TRANS (@lem1969264 x) (@lem1969271 x)). Qed.
Lemma lem1969273 (y : real) (x : real) : (term289 x y) = (term215 x).
Proof. exact (TRANS (@lem1969263 y x) (@lem1969272 x)). Qed.
Lemma lem1969274 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969275 (y : real) (x : real) : (term290 x y) = (term232 x).
Proof. exact (MK_COMB (@lem1969274) (@lem1969273 y x)). Qed.
Lemma lem1969276 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969277 (y : real) (x : real) : (term280 x y) = (term233 x).
Proof. exact (MK_COMB (@lem1969275 y x) (@lem1969276)). Qed.
Lemma lem1969278 (y : real) (x : real) : (term279 x y) = (term233 x).
Proof. exact (TRANS (@lem1969165 x y) (@lem1969277 y x)). Qed.
Lemma lem1969279 (x : real) (y : real) : (term291 x y) = (term292 x y).
Proof. exact (@lem1483525 (term293 x y) term38). Qed.
Lemma lem1969280 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969293 (x : real) (y : real) : (real_sub x y) = (term6 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1969294 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1969295 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem1969294) (@lem1969293 x y)). Qed.
Lemma lem1969296 (x : real) (y : real) : (term283 x y) = (term269 x y).
Proof. exact (@lem1483512 (term6 x y)). Qed.
Lemma lem1969297 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (@lem1483508 x term23 (term11 y)). Qed.
Lemma lem1969298 (y : real) : (term271 y) = (term272 y).
Proof. exact (@lem1483476 term23 term23 y). Qed.
Lemma lem1969300 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1969301 : term58 = term59.
Proof. exact (@lem1969300 term40 term40). Qed.
Lemma lem1969302 : (term60 = (BIT1 0)) = (term61 = term40).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1969303 : term61 = term40.
Proof. exact (EQ_MP (@lem1969302) (@lem940073)). Qed.
Lemma lem1969304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969305 : term59 = term62.
Proof. exact (MK_COMB (@lem1969304) (@lem1969303)). Qed.
Lemma lem1969306 : term58 = term62.
Proof. exact (TRANS (@lem1969301) (@lem1969305)). Qed.
Lemma lem1969307 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969308 : term63 = term64.
Proof. exact (MK_COMB (@lem1969307) (@lem1969306)). Qed.
Lemma lem1969309 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969310 (y : real) : (term272 y) = (term273 y).
Proof. exact (MK_COMB (@lem1969308) (@lem1969309 y)). Qed.
Lemma lem1969311 (y : real) : (term271 y) = (term273 y).
Proof. exact (TRANS (@lem1969298 y) (@lem1969310 y)). Qed.
Lemma lem1969312 (y : real) : (term273 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1969313 (y : real) : (term271 y) = y.
Proof. exact (TRANS (@lem1969311 y) (@lem1969312 y)). Qed.
Lemma lem1969316 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969317 (x : real) (y : real) : (term270 x y) = (term274 x y).
Proof. exact (MK_COMB (@lem1969316 x) (@lem1969313 y)). Qed.
Lemma lem1969318 (x : real) (y : real) : (term269 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969297 x y) (@lem1969317 x y)). Qed.
Lemma lem1969319 (x : real) (y : real) : (term283 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969296 x y) (@lem1969318 x y)). Qed.
Lemma lem1969320 (x : real) (y : real) : (term282 x y) = (term274 x y).
Proof. exact (TRANS (@lem1969295 x y) (@lem1969319 x y)). Qed.
Lemma lem1969323 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1969324 (x : real) (y : real) : (term294 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1969323 y) (@lem1969320 x y)). Qed.
Lemma lem1969325 (x : real) (y : real) : (term295 x y) = (term296 x y).
Proof. exact (@lem1483484 (term11 x) y y). Qed.
Lemma lem1969326 (y : real) : (real_add y y) = (term241 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1969327 : term242 = term210.
Proof. exact (@lem1367770 term40 term40). Qed.
Lemma lem1969328 : term206 = term207.
Proof. exact (@lem706885). Qed.
Lemma lem1969329 : (term206 = term207) = (term208 = term209).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term207). Qed.
Lemma lem1969330 : term208 = term209.
Proof. exact (EQ_MP (@lem1969329) (@lem1969328)). Qed.
Lemma lem1969331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1969332 : term210 = term211.
Proof. exact (MK_COMB (@lem1969331) (@lem1969330)). Qed.
Lemma lem1969333 : term242 = term211.
Proof. exact (TRANS (@lem1969327) (@lem1969332)). Qed.
Lemma lem1969334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969335 : term243 = term244.
Proof. exact (MK_COMB (@lem1969334) (@lem1969333)). Qed.
Lemma lem1969336 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969337 (y : real) : (term241 y) = (term245 y).
Proof. exact (MK_COMB (@lem1969335) (@lem1969336 y)). Qed.
Lemma lem1969338 (y : real) : (real_add y y) = (term245 y).
Proof. exact (TRANS (@lem1969326 y) (@lem1969337 y)). Qed.
Lemma lem1969339 (x : real) : (term157 x) = (term157 x).
Proof. exact (eq_refl (term157 x)). Qed.
Lemma lem1969340 (x : real) (y : real) : (term296 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem1969339 x) (@lem1969338 y)). Qed.
Lemma lem1969341 (x : real) (y : real) : (term295 x y) = (term297 x y).
Proof. exact (TRANS (@lem1969325 x y) (@lem1969340 x y)). Qed.
Lemma lem1969342 (x : real) (y : real) : (term294 x y) = (term297 x y).
Proof. exact (TRANS (@lem1969324 x y) (@lem1969341 x y)). Qed.
Lemma lem1969345 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1969346 (x : real) (y : real) : (term293 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem1969345 x) (@lem1969342 x y)). Qed.
Lemma lem1969347 (x : real) (y : real) : (term298 x y) = (term299 x y).
Proof. exact (@lem1483490 x (term11 x) (term245 y)). Qed.
Lemma lem1969348 (x : real) : (term240 x) = (term220 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1969350 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1969351 : term39 = term38.
Proof. exact (@lem1969350 term40). Qed.
Lemma lem1969352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969353 : term41 = term42.
Proof. exact (MK_COMB (@lem1969352) (@lem1969351)). Qed.
Lemma lem1969354 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1969355 (x : real) : (term220 x) = (term221 x).
Proof. exact (MK_COMB (@lem1969353) (@lem1969354 x)). Qed.
Lemma lem1969356 (x : real) : (term240 x) = (term221 x).
Proof. exact (TRANS (@lem1969348 x) (@lem1969355 x)). Qed.
Lemma lem1969357 (x : real) : (term221 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1969358 (x : real) : (term240 x) = term38.
Proof. exact (TRANS (@lem1969356 x) (@lem1969357 x)). Qed.
Lemma lem1969359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1969360 (x : real) : (term300 x) = term45.
Proof. exact (MK_COMB (@lem1969359) (@lem1969358 x)). Qed.
Lemma lem1969361 (y : real) : (term245 y) = (term245 y).
Proof. exact (eq_refl (term245 y)). Qed.
Lemma lem1969362 (x : real) (y : real) : (term299 x y) = (term301 y).
Proof. exact (MK_COMB (@lem1969360 x) (@lem1969361 y)). Qed.
Lemma lem1969363 (x : real) (y : real) : (term298 x y) = (term301 y).
Proof. exact (TRANS (@lem1969347 x y) (@lem1969362 x y)). Qed.
Lemma lem1969364 (y : real) : (term301 y) = (term245 y).
Proof. exact (@lem1483448 (term245 y)). Qed.
Lemma lem1969365 (x : real) (y : real) : (term298 x y) = (term245 y).
Proof. exact (TRANS (@lem1969363 x y) (@lem1969364 y)). Qed.
Lemma lem1969366 (x : real) (y : real) : (term293 x y) = (term245 y).
Proof. exact (TRANS (@lem1969346 x y) (@lem1969365 x y)). Qed.
Lemma lem1969367 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1969368 (x : real) (y : real) : (term302 x y) = (term247 y).
Proof. exact (MK_COMB (@lem1969367) (@lem1969366 x y)). Qed.
Lemma lem1969369 (x : real) (y : real) : (term303 x y) = (term249 y).
Proof. exact (MK_COMB (@lem1969368 x y) (@lem1969280)). Qed.
Lemma lem1969370 (y : real) : (term249 y) = (term250 y).
Proof. exact (@lem1483519 (term245 y) term38). Qed.
Lemma lem1969372 (x : nat) : (term80 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1969373 : term79 = term38.
Proof. exact (@lem1969372 term40). Qed.
Lemma lem1969374 (y : real) : (term251 y) = (term251 y).
Proof. exact (eq_refl (term251 y)). Qed.
Lemma lem1969375 (y : real) : (term250 y) = (term252 y).
Proof. exact (MK_COMB (@lem1969374 y) (@lem1969373)). Qed.
Lemma lem1969376 (y : real) : (term252 y) = (term245 y).
Proof. exact (@lem1483450 (term245 y)). Qed.
Lemma lem1969377 (y : real) : (term250 y) = (term245 y).
Proof. exact (TRANS (@lem1969375 y) (@lem1969376 y)). Qed.
Lemma lem1969378 (y : real) : (term249 y) = (term245 y).
Proof. exact (TRANS (@lem1969370 y) (@lem1969377 y)). Qed.
Lemma lem1969379 (x : real) (y : real) : (term303 x y) = (term245 y).
Proof. exact (TRANS (@lem1969369 x y) (@lem1969378 y)). Qed.
Lemma lem1969380 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969381 (x : real) (y : real) : (term304 x y) = (term254 y).
Proof. exact (MK_COMB (@lem1969380) (@lem1969379 x y)). Qed.
Lemma lem1969382 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969383 (x : real) (y : real) : (term292 x y) = (term255 y).
Proof. exact (MK_COMB (@lem1969381 x y) (@lem1969382)). Qed.
Lemma lem1969384 (x : real) (y : real) : (term291 x y) = (term255 y).
Proof. exact (TRANS (@lem1969279 x y) (@lem1969383 x y)). Qed.
Lemma lem1969385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969386 (y : real) (x : real) : (term305 x y) = (term257 x).
Proof. exact (MK_COMB (@lem1969385) (@lem1969278 y x)). Qed.
Lemma lem1969387 (x : real) (y : real) : (term306 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem1969386 y x) (@lem1969384 x y)). Qed.
Lemma lem1969388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969389 (x : real) (y : real) : (term133 x y) = (term133 x y).
Proof. exact (MK_COMB (@lem1969388) (@lem1969164 x y)). Qed.
Lemma lem1969390 (x : real) (y : real) : (term171 x y) = (term307 x y).
Proof. exact (MK_COMB (@lem1969389 x y) (@lem1969387 x y)). Qed.
Lemma lem1969391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969392 (x : real) (y : real) : (term172 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1969391) (@lem1969161 x y)). Qed.
Lemma lem1969393 (x : real) (y : real) : (term174 x y) = (term309 x y).
Proof. exact (MK_COMB (@lem1969392 x y) (@lem1969390 x y)). Qed.
Lemma lem1969394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1969395 (y : real) (x : real) : (term181 x y) = (term310 y x).
Proof. exact (MK_COMB (@lem1969394) (@lem1969109 y x)). Qed.
Lemma lem1969396 (x : real) (y : real) : (term182 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1969395 y x) (@lem1969393 x y)). Qed.
Lemma lem1969407 (x : real) (y : real) : (term166 x y) = (term311 x y).
Proof. exact (TRANS (@lem1968856 x y) (@lem1969396 x y)). Qed.
Lemma lem1969408 (x : real) (y : real) : (term134 x y) = (term311 x y).
Proof. exact (TRANS (@lem1968840 x y) (@lem1969407 x y)). Qed.
Lemma lem1969409 (x : real) (y : real) (h1 : term311 x y) : term311 x y.
Proof. exact (h1). Qed.
Lemma lem1969410 (y : real) (x : real) (h1 : term262 y x) : term262 y x.
Proof. exact (h1). Qed.
Lemma lem1969411 (y : real) (x : real) (h1 : term262 y x) : term260 y x.
Proof. exact (proj2 (@lem1969410 y x h1)). Qed.
Lemma lem1969413 (y : real) (x : real) (h1 : term262 y x) : term259 y x.
Proof. exact (proj2 (@lem1969411 y x h1)). Qed.
Lemma lem1969414 (y : real) (x : real) (h1 : term262 y x) : term120 x y.
Proof. exact (proj1 (@lem1969411 y x h1)). Qed.
Lemma lem1969415 (y : real) (x : real) (h1 : term262 y x) : term117 y.
Proof. exact (proj2 (@lem1969414 y x h1)). Qed.
Lemma lem1969418 (y : real) (x : real) (h1 : term262 y x) : term233 y.
Proof. exact (proj1 (@lem1969413 y x h1)). Qed.
Lemma lem1969420 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969421 : term312 = term313.
Proof. exact (@lem1969420 (NUMERAL 0) term209). Qed.
Lemma lem1969422 : term314 = term207.
Proof. exact (@lem912803). Qed.
Lemma lem1969423 (h1 : term314 = term207) : term313 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term207 h1). Qed.
Lemma lem1969424 : (term314 = term207) = (term313 = True).
Proof. exact (prop_ext (fun h1 : term314 = term207 => @lem1969423 h1) (fun h1 : term313 = True => @lem1969422)). Qed.
Lemma lem1969425 : term313 = True.
Proof. exact (EQ_MP (@lem1969424) (@lem1969422)). Qed.
Lemma lem1969426 : term312 = True.
Proof. exact (TRANS (@lem1969421) (@lem1969425)). Qed.
Lemma lem1969427 : True = term312.
Proof. exact (SYM (@lem1969426)). Qed.
Lemma lem1969428 : term312.
Proof. exact (EQ_MP (@lem1969427) (@lem0)). Qed.
Lemma lem1969429 (y : real) (x : real) (h1 : term262 y x) : term315 y.
Proof. exact (conj (@lem1969428) (@lem1969415 y x h1)). Qed.
Lemma lem1969431 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1969432 (y : real) : term317 y.
Proof. exact (@lem1969431 term211 y). Qed.
Lemma lem1969439 (y : real) (x : real) (h1 : term262 y x) : term318 y.
Proof. exact (@lem1969432 y (@lem1969429 y x h1)). Qed.
Lemma lem1969441 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969442 : term319 = term320.
Proof. exact (@lem1969441 (NUMERAL 0) term40). Qed.
Lemma lem1969443 : term321 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1969444 (h1 : term321 = (BIT1 0)) : term320 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1969445 : (term321 = (BIT1 0)) = (term320 = True).
Proof. exact (prop_ext (fun h1 : term321 = (BIT1 0) => @lem1969444 h1) (fun h1 : term320 = True => @lem1969443)). Qed.
Lemma lem1969446 : term320 = True.
Proof. exact (EQ_MP (@lem1969445) (@lem1969443)). Qed.
Lemma lem1969447 : term319 = True.
Proof. exact (TRANS (@lem1969442) (@lem1969446)). Qed.
Lemma lem1969448 : True = term319.
Proof. exact (SYM (@lem1969447)). Qed.
Lemma lem1969449 : term319.
Proof. exact (EQ_MP (@lem1969448) (@lem0)). Qed.
Lemma lem1969450 (y : real) (x : real) (h1 : term262 y x) : term322 y.
Proof. exact (conj (@lem1969449) (@lem1969418 y x h1)). Qed.
Lemma lem1969452 (x : real) (y : real) : term323 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1969453 (y : real) : term324 y.
Proof. exact (@lem1969452 term62 (term215 y)). Qed.
Lemma lem1969454 (y : real) (x : real) (h1 : term262 y x) : term325 y.
Proof. exact (@lem1969453 y (@lem1969450 y x h1)). Qed.
Lemma lem1969455 (y : real) : (term326 y) = (term215 y).
Proof. exact (@lem1483460 (term215 y)). Qed.
Lemma lem1969456 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969457 (y : real) : (term327 y) = (term232 y).
Proof. exact (MK_COMB (@lem1969456) (@lem1969455 y)). Qed.
Lemma lem1969458 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969459 (y : real) : (term325 y) = (term233 y).
Proof. exact (MK_COMB (@lem1969457 y) (@lem1969458)). Qed.
Lemma lem1969460 (y : real) (x : real) (h1 : term262 y x) : term233 y.
Proof. exact (EQ_MP (@lem1969459 y) (@lem1969454 y x h1)). Qed.
Lemma lem1969461 (y : real) (x : real) (h1 : term262 y x) : term328 y.
Proof. exact (conj (@lem1969460 y x h1) (@lem1969439 y x h1)). Qed.
Lemma lem1969463 (x : real) (y : real) : term329 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1969464 (y : real) : term330 y.
Proof. exact (@lem1969463 (term215 y) (term245 y)). Qed.
Lemma lem1969465 (y : real) (x : real) (h1 : term262 y x) : term331 y.
Proof. exact (@lem1969464 y (@lem1969461 y x h1)). Qed.
Lemma lem1969466 (y : real) : (term332 y) = (term333 y).
Proof. exact (@lem1483438 term212 term211 y). Qed.
Lemma lem1969468 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1969469 : term334 = term38.
Proof. exact (@lem1969468 term209). Qed.
Lemma lem1969470 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969471 : term335 = term42.
Proof. exact (MK_COMB (@lem1969470) (@lem1969469)). Qed.
Lemma lem1969472 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1969473 (y : real) : (term333 y) = (term221 y).
Proof. exact (MK_COMB (@lem1969471) (@lem1969472 y)). Qed.
Lemma lem1969474 (y : real) : (term332 y) = (term221 y).
Proof. exact (TRANS (@lem1969466 y) (@lem1969473 y)). Qed.
Lemma lem1969475 (y : real) : (term221 y) = term38.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1969476 (y : real) : (term332 y) = term38.
Proof. exact (TRANS (@lem1969474 y) (@lem1969475 y)). Qed.
Lemma lem1969477 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969478 (y : real) : (term336 y) = term83.
Proof. exact (MK_COMB (@lem1969477) (@lem1969476 y)). Qed.
Lemma lem1969479 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969480 (y : real) : (term331 y) = term85.
Proof. exact (MK_COMB (@lem1969478 y) (@lem1969479)). Qed.
Lemma lem1969481 (y : real) (x : real) (h1 : term262 y x) : term85.
Proof. exact (EQ_MP (@lem1969480 y) (@lem1969465 y x h1)). Qed.
Lemma lem1969483 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969484 : term85 = term92.
Proof. exact (@lem1969483 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1969485 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1969486 : term85 = False.
Proof. exact (TRANS (@lem1969484) (@lem1969485)). Qed.
Lemma lem1969487 (y : real) (x : real) (h1 : term262 y x) : False.
Proof. exact (EQ_MP (@lem1969486) (@lem1969481 y x h1)). Qed.
Lemma lem1969488 (x : real) (y : real) (h1 : term309 x y) : term309 x y.
Proof. exact (h1). Qed.
Lemma lem1969489 (x : real) (y : real) (h1 : term309 x y) : term307 x y.
Proof. exact (proj2 (@lem1969488 x y h1)). Qed.
Lemma lem1969491 (x : real) (y : real) (h1 : term309 x y) : term259 x y.
Proof. exact (proj2 (@lem1969489 x y h1)). Qed.
Lemma lem1969492 (x : real) (y : real) (h1 : term309 x y) : term120 x y.
Proof. exact (proj1 (@lem1969489 x y h1)). Qed.
Lemma lem1969494 (x : real) (y : real) (h1 : term309 x y) : term117 x.
Proof. exact (proj1 (@lem1969492 x y h1)). Qed.
Lemma lem1969496 (x : real) (y : real) (h1 : term309 x y) : term233 x.
Proof. exact (proj1 (@lem1969491 x y h1)). Qed.
Lemma lem1969498 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969499 : term312 = term313.
Proof. exact (@lem1969498 (NUMERAL 0) term209). Qed.
Lemma lem1969500 : term314 = term207.
Proof. exact (@lem912803). Qed.
Lemma lem1969501 (h1 : term314 = term207) : term313 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term207 h1). Qed.
Lemma lem1969502 : (term314 = term207) = (term313 = True).
Proof. exact (prop_ext (fun h1 : term314 = term207 => @lem1969501 h1) (fun h1 : term313 = True => @lem1969500)). Qed.
Lemma lem1969503 : term313 = True.
Proof. exact (EQ_MP (@lem1969502) (@lem1969500)). Qed.
Lemma lem1969504 : term312 = True.
Proof. exact (TRANS (@lem1969499) (@lem1969503)). Qed.
Lemma lem1969505 : True = term312.
Proof. exact (SYM (@lem1969504)). Qed.
Lemma lem1969506 : term312.
Proof. exact (EQ_MP (@lem1969505) (@lem0)). Qed.
Lemma lem1969507 (x : real) (y : real) (h1 : term309 x y) : term315 x.
Proof. exact (conj (@lem1969506) (@lem1969494 x y h1)). Qed.
Lemma lem1969509 (x : real) (y : real) : term316 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1969510 (x : real) : term317 x.
Proof. exact (@lem1969509 term211 x). Qed.
Lemma lem1969517 (x : real) (y : real) (h1 : term309 x y) : term318 x.
Proof. exact (@lem1969510 x (@lem1969507 x y h1)). Qed.
Lemma lem1969519 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969520 : term319 = term320.
Proof. exact (@lem1969519 (NUMERAL 0) term40). Qed.
Lemma lem1969521 : term321 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1969522 (h1 : term321 = (BIT1 0)) : term320 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1969523 : (term321 = (BIT1 0)) = (term320 = True).
Proof. exact (prop_ext (fun h1 : term321 = (BIT1 0) => @lem1969522 h1) (fun h1 : term320 = True => @lem1969521)). Qed.
Lemma lem1969524 : term320 = True.
Proof. exact (EQ_MP (@lem1969523) (@lem1969521)). Qed.
Lemma lem1969525 : term319 = True.
Proof. exact (TRANS (@lem1969520) (@lem1969524)). Qed.
Lemma lem1969526 : True = term319.
Proof. exact (SYM (@lem1969525)). Qed.
Lemma lem1969527 : term319.
Proof. exact (EQ_MP (@lem1969526) (@lem0)). Qed.
Lemma lem1969528 (x : real) (y : real) (h1 : term309 x y) : term322 x.
Proof. exact (conj (@lem1969527) (@lem1969496 x y h1)). Qed.
Lemma lem1969530 (x : real) (y : real) : term323 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1969531 (x : real) : term324 x.
Proof. exact (@lem1969530 term62 (term215 x)). Qed.
Lemma lem1969532 (x : real) (y : real) (h1 : term309 x y) : term325 x.
Proof. exact (@lem1969531 x (@lem1969528 x y h1)). Qed.
Lemma lem1969533 (x : real) : (term326 x) = (term215 x).
Proof. exact (@lem1483460 (term215 x)). Qed.
Lemma lem1969534 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969535 (x : real) : (term327 x) = (term232 x).
Proof. exact (MK_COMB (@lem1969534) (@lem1969533 x)). Qed.
Lemma lem1969536 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969537 (x : real) : (term325 x) = (term233 x).
Proof. exact (MK_COMB (@lem1969535 x) (@lem1969536)). Qed.
Lemma lem1969538 (x : real) (y : real) (h1 : term309 x y) : term233 x.
Proof. exact (EQ_MP (@lem1969537 x) (@lem1969532 x y h1)). Qed.
Lemma lem1969539 (x : real) (y : real) (h1 : term309 x y) : term328 x.
Proof. exact (conj (@lem1969538 x y h1) (@lem1969517 x y h1)). Qed.
Lemma lem1969541 (x : real) (y : real) : term329 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1969542 (x : real) : term330 x.
Proof. exact (@lem1969541 (term215 x) (term245 x)). Qed.
Lemma lem1969543 (x : real) (y : real) (h1 : term309 x y) : term331 x.
Proof. exact (@lem1969542 x (@lem1969539 x y h1)). Qed.
Lemma lem1969544 (x : real) : (term332 x) = (term333 x).
Proof. exact (@lem1483438 term212 term211 x). Qed.
Lemma lem1969546 (m : nat) : (term37 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1969547 : term334 = term38.
Proof. exact (@lem1969546 term209). Qed.
Lemma lem1969548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1969549 : term335 = term42.
Proof. exact (MK_COMB (@lem1969548) (@lem1969547)). Qed.
Lemma lem1969550 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1969551 (x : real) : (term333 x) = (term221 x).
Proof. exact (MK_COMB (@lem1969549) (@lem1969550 x)). Qed.
Lemma lem1969552 (x : real) : (term332 x) = (term221 x).
Proof. exact (TRANS (@lem1969544 x) (@lem1969551 x)). Qed.
Lemma lem1969553 (x : real) : (term221 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1969554 (x : real) : (term332 x) = term38.
Proof. exact (TRANS (@lem1969552 x) (@lem1969553 x)). Qed.
Lemma lem1969555 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1969556 (x : real) : (term336 x) = term83.
Proof. exact (MK_COMB (@lem1969555) (@lem1969554 x)). Qed.
Lemma lem1969557 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1969558 (x : real) : (term331 x) = term85.
Proof. exact (MK_COMB (@lem1969556 x) (@lem1969557)). Qed.
Lemma lem1969559 (x : real) (y : real) (h1 : term309 x y) : term85.
Proof. exact (EQ_MP (@lem1969558 x) (@lem1969543 x y h1)). Qed.
Lemma lem1969561 (n : nat) (m : nat) : (term91 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1969562 : term85 = term92.
Proof. exact (@lem1969561 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1969563 : term92 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1969564 : term85 = False.
Proof. exact (TRANS (@lem1969562) (@lem1969563)). Qed.
Lemma lem1969565 (x : real) (y : real) (h1 : term309 x y) : False.
Proof. exact (EQ_MP (@lem1969564) (@lem1969559 x y h1)). Qed.
Lemma lem1969566 (x : real) (y : real) (h1 : term311 x y) : False.
Proof. exact (or_elim (@lem1969409 x y h1) (fun h0 : term262 y x => @lem1969487 y x h0) (fun h0 : term309 x y => @lem1969565 x y h0)). Qed.
Lemma lem1969567 (x : real) (y : real) (h1 : term134 x y) : term134 x y.
Proof. exact (h1). Qed.
Lemma lem1969568 (x : real) (y : real) (h1 : term134 x y) : term311 x y.
Proof. exact (EQ_MP (@lem1969408 x y) (@lem1969567 x y h1)). Qed.
Lemma lem1969569 (x : real) (y : real) (h1 : term134 x y) : (term311 x y) = False.
Proof. exact (prop_ext (fun h2 : term311 x y => @lem1969566 x y h2) (fun h2 : False => @lem1969568 x y h1)). Qed.
Lemma lem1969570 (x : real) (y : real) (h1 : term134 x y) : False.
Proof. exact (EQ_MP (@lem1969569 x y h1) (@lem1969568 x y h1)). Qed.
Lemma lem1969571 (x : real) (y : real) (h1 : term107 x y) : term107 x y.
Proof. exact (h1). Qed.
Lemma lem1969572 (x : real) (y : real) (h1 : term107 x y) : term134 x y.
Proof. exact (EQ_MP (@lem1968771 x y) (@lem1969571 x y h1)). Qed.
Lemma lem1969573 (x : real) (y : real) (h1 : term107 x y) : (term134 x y) = False.
Proof. exact (prop_ext (fun h2 : term134 x y => @lem1969570 x y h2) (fun h2 : False => @lem1969572 x y h1)). Qed.
Lemma lem1969574 (x : real) (y : real) (h1 : term107 x y) : False.
Proof. exact (EQ_MP (@lem1969573 x y h1) (@lem1969572 x y h1)). Qed.
Lemma lem1969575 (x : real) (y : real) : term337 x y.
Proof. exact (fun h0 : term107 x y => @lem1969574 x y h0). Qed.
Lemma lem1969576 (x : real) (y : real) : term338 x y.
Proof. exact (@lem1386578 (term339 x y)). Qed.
Lemma lem1969577 (x : real) (y : real) : term339 x y.
Proof. exact (@lem1969576 x y (@lem1969575 x y)). Qed.
Lemma lem1969578 (x : real) (y : real) (h1 : term339 x y) : term339 x y.
Proof. exact (h1). Qed.
Lemma lem1969579 (x : real) (y : real) (h1 : term109 x y) : term109 x y.
Proof. exact (h1). Qed.
Lemma lem1969580 (x : real) (y : real) (h1 : term109 x y) (h2 : term339 x y) : term110 x y.
Proof. exact (@lem1969578 x y h2 (@lem1969579 x y h1)). Qed.
Lemma lem1969581 (x : real) (y : real) (h1 : term109 x y) : term340 x y.
Proof. exact (fun h0 : term339 x y => @lem1969580 x y h1 h0). Qed.
Lemma lem1969582 (x : real) (y : real) (h1 : term339 x y) : term339 x y.
Proof. exact (h1). Qed.
Lemma lem1969583 (x : real) (y : real) (h1 : term109 x y) (h2 : term339 x y) : term110 x y.
Proof. exact (@lem1969581 x y h1 (@lem1969582 x y h2)). Qed.
Lemma lem1969584 (x : real) (y : real) (h1 : term339 x y) : term339 x y.
Proof. exact (fun h0 : term109 x y => @lem1969583 x y h0 h1). Qed.
Lemma lem1969585 (x : real) (y : real) : term341 x y.
Proof. exact (fun h0 : term339 x y => @lem1969584 x y h0). Qed.
Lemma lem1969587 (x : real) : term342 x.
Proof. exact (@lem1532076 x). Qed.
Lemma lem1969588 (x : real) : (term342 x) = (term343 x).
Proof. exact (eq_refl (term342 x)). Qed.
Lemma lem1969589 (x : real) : term343 x.
Proof. exact (EQ_MP (@lem1969588 x) (@lem1969587 x)). Qed.
Lemma lem1969590 (x : real) : (term343 x) = ((term343 x) = True).
Proof. exact (@lem7 (term343 x)). Qed.
Lemma lem1969592 (h1 : term344) : term344.
Proof. exact (h1). Qed.
Lemma lem1969593 (x : real) (h1 : term344) : term345 x.
Proof. exact (@lem1969592 h1 x). Qed.
Lemma lem1969594 (x : real) : (term345 x) = (term346 x).
Proof. exact (eq_refl (term345 x)). Qed.
Lemma lem1969595 (x : real) (h1 : term344) : term346 x.
Proof. exact (EQ_MP (@lem1969594 x) (@lem1969593 x h1)). Qed.
Lemma lem1969596 (x : real) (y : real) (h1 : term344) : term347 x y.
Proof. exact (@lem1969595 x h1 y). Qed.
Lemma lem1969597 (y : real) (x : real) : (term347 x y) = (term348 y x).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem1969598 (y : real) (x : real) (h1 : term344) : term348 y x.
Proof. exact (EQ_MP (@lem1969597 y x) (@lem1969596 x y h1)). Qed.
Lemma lem1969599 (y : real) (x : real) (z : real) (h1 : term344) : term349 y x z.
Proof. exact (@lem1969598 y x h1 z). Qed.
Lemma lem1969600 (y : real) (x : real) (z : real) : (term349 y x z) = (term350 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem1969601 (y : real) (x : real) (z : real) (h1 : term344) : term350 y x z.
Proof. exact (EQ_MP (@lem1969600 y x z) (@lem1969599 y x z h1)). Qed.
Lemma lem1969602 (x : real) (y : real) (z : real) (h1 : term351 x y z) : term351 x y z.
Proof. exact (h1). Qed.
Lemma lem1969603 (x : real) (y : real) (z : real) (h1 : term344) (h2 : term351 x y z) : term352 y x z.
Proof. exact (@lem1969601 y x z h1 (@lem1969602 x y z h2)). Qed.
Lemma lem1969604 (x : real) (y : real) (z : real) (h1 : term351 x y z) : term353 y x z.
Proof. exact (fun h0 : term344 => @lem1969603 x y z h0 h1). Qed.
Lemma lem1969605 (h1 : term344) : term344.
Proof. exact (h1). Qed.
Lemma lem1969606 (x : real) (y : real) (z : real) (h1 : term344) (h2 : term351 x y z) : term352 y x z.
Proof. exact (@lem1969604 x y z h2 (@lem1969605 h1)). Qed.
Lemma lem1969607 (y : real) (x : real) (z : real) (h1 : term344) : term350 y x z.
Proof. exact (fun h0 : term351 x y z => @lem1969606 x y z h1 h0). Qed.
Lemma lem1969608 (y : real) (x : real) (h1 : term344) : term348 y x.
Proof. exact (fun z : real => @lem1969607 y x z h1). Qed.
Lemma lem1969609 (y : real) (h1 : term344) : term354 y.
Proof. exact (fun x : real => @lem1969608 y x h1). Qed.
Lemma lem1969610 (h1 : term344) : term355.
Proof. exact (fun y : real => @lem1969609 y h1). Qed.
Lemma lem1969611 : term356.
Proof. exact (fun h0 : term344 => @lem1969610 h0). Qed.
Lemma lem1969612 : term355.
Proof. exact (@lem1969611 (@lem1583207)). Qed.
Lemma lem1969613 (y : real) : term357 y.
Proof. exact (@lem1969612 y). Qed.
Lemma lem1969614 (y : real) : (term357 y) = (term354 y).
Proof. exact (eq_refl (term357 y)). Qed.
Lemma lem1969615 (y : real) : term354 y.
Proof. exact (EQ_MP (@lem1969614 y) (@lem1969613 y)). Qed.
Lemma lem1969616 (y : real) (x : real) : term358 y x.
Proof. exact (@lem1969615 y x). Qed.
Lemma lem1969617 (y : real) (x : real) : (term358 y x) = (term348 y x).
Proof. exact (eq_refl (term358 y x)). Qed.
Lemma lem1969618 (y : real) (x : real) : term348 y x.
Proof. exact (EQ_MP (@lem1969617 y x) (@lem1969616 y x)). Qed.
Lemma lem1969619 (y : real) (x : real) (z : real) : term349 y x z.
Proof. exact (@lem1969618 y x z). Qed.
Lemma lem1969620 (y : real) (x : real) (z : real) : (term349 y x z) = (term350 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem1969622 (x : real) : term359 x.
Proof. exact (@lem1383497 x). Qed.
Lemma lem1969623 (x : real) : (term359 x) = ((term5 x) = (real_mul x x)).
Proof. exact (eq_refl (term359 x)). Qed.
Lemma lem1969625 (h1 : term360) : term360.
Proof. exact (h1). Qed.
Lemma lem1969626 (x : real) (h1 : term360) : term361 x.
Proof. exact (@lem1969625 h1 x). Qed.
Lemma lem1969627 (x : real) : (term361 x) = (term362 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem1969628 (x : real) (h1 : term360) : term362 x.
Proof. exact (EQ_MP (@lem1969627 x) (@lem1969626 x h1)). Qed.
Lemma lem1969629 (x : real) (y : real) (h1 : term360) : term363 x y.
Proof. exact (@lem1969628 x h1 y). Qed.
Lemma lem1969630 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem1969631 (x : real) (y : real) (h1 : term360) : term364 x y.
Proof. exact (EQ_MP (@lem1969630 x y) (@lem1969629 x y h1)). Qed.
Lemma lem1969632 (x : real) (y : real) (h1 : term365 x y) : term365 x y.
Proof. exact (h1). Qed.
Lemma lem1969633 (x : real) (y : real) (h1 : term360) (h2 : term365 x y) : term366 x y.
Proof. exact (@lem1969631 x y h1 (@lem1969632 x y h2)). Qed.
Lemma lem1969634 (x : real) (y : real) (h1 : term365 x y) : term367 x y.
Proof. exact (fun h0 : term360 => @lem1969633 x y h0 h1). Qed.
Lemma lem1969635 (h1 : term360) : term360.
Proof. exact (h1). Qed.
Lemma lem1969636 (x : real) (y : real) (h1 : term360) (h2 : term365 x y) : term366 x y.
Proof. exact (@lem1969634 x y h2 (@lem1969635 h1)). Qed.
Lemma lem1969637 (x : real) (y : real) (h1 : term360) : term364 x y.
Proof. exact (fun h0 : term365 x y => @lem1969636 x y h1 h0). Qed.
Lemma lem1969638 (x : real) (h1 : term360) : term362 x.
Proof. exact (fun y : real => @lem1969637 x y h1). Qed.
Lemma lem1969639 (h1 : term360) : term360.
Proof. exact (fun x : real => @lem1969638 x h1). Qed.
Lemma lem1969640 : term368.
Proof. exact (fun h0 : term360 => @lem1969639 h0). Qed.
Lemma lem1969641 : term360.
Proof. exact (@lem1969640 (@lem1961031)). Qed.
Lemma lem1969642 (x : real) : term361 x.
Proof. exact (@lem1969641 x). Qed.
Lemma lem1969643 (x : real) : (term361 x) = (term362 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem1969644 (x : real) : term362 x.
Proof. exact (EQ_MP (@lem1969643 x) (@lem1969642 x)). Qed.
Lemma lem1969645 (x : real) (y : real) : term363 x y.
Proof. exact (@lem1969644 x y). Qed.
Lemma lem1969646 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem1969648 (x : real) (y : real) (h1 : term109 x y) : term109 x y.
Proof. exact (h1). Qed.
Lemma lem1969649 (y : real) (h1 : term111 y) : term111 y.
Proof. exact (h1). Qed.
Lemma lem1969650 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (h1). Qed.
Lemma lem1969652 (x : real) (y : real) : term364 x y.
Proof. exact (EQ_MP (@lem1969646 x y) (@lem1969645 x y)). Qed.
Lemma lem1969653 (x : real) (y : real) : term369 x y.
Proof. exact (@lem1969652 (term370 x y) (term123 x y)). Qed.
Lemma lem1969655 (x : real) : (term5 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1969623 x) (@lem1969622 x)). Qed.
Lemma lem1969656 (x : real) (y : real) : (term371 x y) = (term372 x y).
Proof. exact (@lem1969655 (term370 x y)). Qed.
Lemma lem1969657 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1969658 (x : real) (y : real) : (term373 x y) = (term374 x y).
Proof. exact (MK_COMB (@lem1969657) (@lem1969656 x y)). Qed.
Lemma lem1969659 (x : real) (y : real) : (term123 x y) = (term123 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1969660 (x : real) (y : real) : (term375 x y) = (term376 x y).
Proof. exact (MK_COMB (@lem1969658 x y) (@lem1969659 x y)). Qed.
Lemma lem1969661 (x : real) (y : real) : (term376 x y) = (term375 x y).
Proof. exact (SYM (@lem1969660 x y)). Qed.
Lemma lem1969662 (h1 : term377) : term377.
Proof. exact (h1). Qed.
Lemma lem1969663 (x : real) (h1 : term377) : term378 x.
Proof. exact (@lem1969662 h1 x). Qed.
Lemma lem1969664 (x : real) : (term378 x) = (term379 x).
Proof. exact (eq_refl (term378 x)). Qed.
Lemma lem1969665 (x : real) (h1 : term377) : term379 x.
Proof. exact (EQ_MP (@lem1969664 x) (@lem1969663 x h1)). Qed.
Lemma lem1969666 (x : real) (y : real) (h1 : term377) : term380 x y.
Proof. exact (@lem1969665 x h1 y). Qed.
Lemma lem1969667 (y : real) (x : real) : (term380 x y) = (term381 y x).
Proof. exact (eq_refl (term380 x y)). Qed.
Lemma lem1969668 (y : real) (x : real) (h1 : term377) : term381 y x.
Proof. exact (EQ_MP (@lem1969667 y x) (@lem1969666 x y h1)). Qed.
Lemma lem1969669 (y : real) (x : real) (z : real) (h1 : term377) : term382 y x z.
Proof. exact (@lem1969668 y x h1 z). Qed.
Lemma lem1969670 (y : real) (x : real) (z : real) : (term382 y x z) = (term383 y x z).
Proof. exact (eq_refl (term382 y x z)). Qed.
Lemma lem1969671 (y : real) (x : real) (z : real) (h1 : term377) : term383 y x z.
Proof. exact (EQ_MP (@lem1969670 y x z) (@lem1969669 y x z h1)). Qed.
Lemma lem1969672 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term384 x y z.
Proof. exact (h1). Qed.
Lemma lem1969673 (x : real) (y : real) (z : real) (h1 : term377) (h2 : term384 x y z) : real_le x z.
Proof. exact (@lem1969671 y x z h1 (@lem1969672 x y z h2)). Qed.
Lemma lem1969674 (x : real) (y : real) (z : real) (h1 : term384 x y z) : term385 x z.
Proof. exact (fun h0 : term377 => @lem1969673 x y z h0 h1). Qed.
Lemma lem1969675 (x : real) (z : real) (h1 : term386 x z) : term386 x z.
Proof. exact (h1). Qed.
Lemma lem1969676 (x : real) (z : real) (h1 : term386 x z) : term385 x z.
Proof. exact (ex_elim (@lem1969675 x z h1) (fun y : real => fun h0 : term387 x z y => @lem1969674 x y z h0)). Qed.
Lemma lem1969677 (h1 : term377) : term377.
Proof. exact (h1). Qed.
Lemma lem1969678 (x : real) (z : real) (h1 : term377) (h2 : term386 x z) : real_le x z.
Proof. exact (@lem1969676 x z h2 (@lem1969677 h1)). Qed.
Lemma lem1969679 (x : real) (z : real) (h1 : term377) : term388 x z.
Proof. exact (fun h0 : term386 x z => @lem1969678 x z h1 h0). Qed.
Lemma lem1969680 (x : real) (h1 : term377) : term389 x.
Proof. exact (fun z : real => @lem1969679 x z h1). Qed.
Lemma lem1969681 (h1 : term377) : term390.
Proof. exact (fun x : real => @lem1969680 x h1). Qed.
Lemma lem1969682 : term391.
Proof. exact (fun h0 : term377 => @lem1969681 h0). Qed.
Lemma lem1969683 : term390.
Proof. exact (@lem1969682 (@lem1339577)). Qed.
Lemma lem1969684 (x : real) : term392 x.
Proof. exact (@lem1969683 x). Qed.
Lemma lem1969685 (x : real) : (term392 x) = (term389 x).
Proof. exact (eq_refl (term392 x)). Qed.
Lemma lem1969686 (x : real) : term389 x.
Proof. exact (EQ_MP (@lem1969685 x) (@lem1969684 x)). Qed.
Lemma lem1969687 (x : real) (z : real) : term393 x z.
Proof. exact (@lem1969686 x z). Qed.
Lemma lem1969688 (x : real) (z : real) : (term393 x z) = (term388 x z).
Proof. exact (eq_refl (term393 x z)). Qed.
Lemma lem1969691 (x : real) (z : real) : term388 x z.
Proof. exact (EQ_MP (@lem1969688 x z) (@lem1969687 x z)). Qed.
Lemma lem1969692 (x : real) (y : real) : term394 x y.
Proof. exact (@lem1969691 (term372 x y) (term123 x y)). Qed.
Lemma lem1969694 (y : real) (x : real) (z : real) : term350 y x z.
Proof. exact (EQ_MP (@lem1969620 y x z) (@lem1969619 y x z)). Qed.
Lemma lem1969695 (x : real) (y : real) : term395 x y.
Proof. exact (@lem1969694 (term370 x y) (term370 x y) (term396 x y)). Qed.
Lemma lem1969699 (x : real) : (term343 x) = True.
Proof. exact (EQ_MP (@lem1969590 x) (@lem1969589 x)). Qed.
Lemma lem1969700 (x : real) (y : real) : (term397 x y) = True.
Proof. exact (@lem1969699 (term398 x y)). Qed.
Lemma lem1969701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969702 (x : real) (y : real) : (term399 x y) = (and True).
Proof. exact (MK_COMB (@lem1969701) (@lem1969700 x y)). Qed.
Lemma lem1969703 (x : real) (y : real) : (term400 x y) = (term400 x y).
Proof. exact (eq_refl (term400 x y)). Qed.
Lemma lem1969704 (x : real) (y : real) : (term401 x y) = (term402 x y).
Proof. exact (MK_COMB (@lem1969702 x y) (@lem1969703 x y)). Qed.
Lemma lem1969706 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1969707 (x : real) (y : real) : (term402 x y) = (term400 x y).
Proof. exact (@lem1969706 (term400 x y)). Qed.
Lemma lem1969708 (x : real) (y : real) : (term401 x y) = (term400 x y).
Proof. exact (TRANS (@lem1969704 x y) (@lem1969707 x y)). Qed.
Lemma lem1969709 (x : real) (y : real) : (term400 x y) = (term401 x y).
Proof. exact (SYM (@lem1969708 x y)). Qed.
Lemma lem1969711 (x : real) (y : real) : term339 x y.
Proof. exact (@lem1969585 x y (@lem1969577 x y)). Qed.
Lemma lem1969712 (x : real) (y : real) : term403 x y.
Proof. exact (@lem1969711 (sqrt x) (sqrt y)). Qed.
Lemma lem1969713 (x : real) : term404 x.
Proof. exact (@lem1945292 x). Qed.
Lemma lem1969714 (x : real) : (term404 x) = (term405 x).
Proof. exact (eq_refl (term404 x)). Qed.
Lemma lem1969715 (x : real) : term405 x.
Proof. exact (EQ_MP (@lem1969714 x) (@lem1969713 x)). Qed.
Lemma lem1969716 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (h1). Qed.
Lemma lem1969717 (x : real) (h1 : term111 x) : term406 x.
Proof. exact (@lem1969715 x (@lem1969716 x h1)). Qed.
Lemma lem1969718 (x : real) : (term406 x) = ((term406 x) = True).
Proof. exact (@lem7 (term406 x)). Qed.
Lemma lem1969719 (x : real) (h1 : term111 x) : (term406 x) = True.
Proof. exact (EQ_MP (@lem1969718 x) (@lem1969717 x h1)). Qed.
Lemma lem1969725 (x : real) : (term111 x) = ((term111 x) = True).
Proof. exact (@lem7 (term111 x)). Qed.
Lemma lem1969727 (y : real) : (term111 y) = ((term111 y) = True).
Proof. exact (@lem7 (term111 y)). Qed.
Lemma lem1969732 (x : real) : term407 x.
Proof. exact (fun h0 : term111 x => @lem1969719 x h0). Qed.
Lemma lem1969734 (x : real) (h1 : term111 x) : (term111 x) = True.
Proof. exact (EQ_MP (@lem1969725 x) (@lem1969650 x h1)). Qed.
Lemma lem1969735 (x : real) (h1 : term111 x) : True = (term111 x).
Proof. exact (SYM (@lem1969734 x h1)). Qed.
Lemma lem1969736 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (EQ_MP (@lem1969735 x h1) (@lem0)). Qed.
Lemma lem1969737 (x : real) (h1 : term111 x) : (term406 x) = True.
Proof. exact (@lem1969732 x (@lem1969736 x h1)). Qed.
Lemma lem1969738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1969739 (x : real) (h1 : term111 x) : (term408 x) = (and True).
Proof. exact (MK_COMB (@lem1969738) (@lem1969737 x h1)). Qed.
Lemma lem1969741 (x : real) : term407 x.
Proof. exact (fun h0 : term111 x => @lem1969719 x h0). Qed.
Lemma lem1969742 (y : real) : term407 y.
Proof. exact (@lem1969741 y). Qed.
Lemma lem1969744 (y : real) (h1 : term111 y) : (term111 y) = True.
Proof. exact (EQ_MP (@lem1969727 y) (@lem1969649 y h1)). Qed.
Lemma lem1969745 (y : real) (h1 : term111 y) : True = (term111 y).
Proof. exact (SYM (@lem1969744 y h1)). Qed.
Lemma lem1969746 (y : real) (h1 : term111 y) : term111 y.
Proof. exact (EQ_MP (@lem1969745 y h1) (@lem0)). Qed.
Lemma lem1969747 (y : real) (h1 : term111 y) : (term406 y) = True.
Proof. exact (@lem1969742 y (@lem1969746 y h1)). Qed.
Lemma lem1969748 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term409 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1969739 x h1) (@lem1969747 y h2)). Qed.
Lemma lem1969750 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1969751 : (True /\ True) = True.
Proof. exact (@lem1969750 True). Qed.
Lemma lem1969752 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term409 x y) = True.
Proof. exact (TRANS (@lem1969748 x y h1 h2) (@lem1969751)). Qed.
Lemma lem1969753 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : True = (term409 x y).
Proof. exact (SYM (@lem1969752 x y h1 h2)). Qed.
Lemma lem1969754 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term409 x y.
Proof. exact (EQ_MP (@lem1969753 x y h1 h2) (@lem0)). Qed.
Lemma lem1969755 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term400 x y.
Proof. exact (@lem1969712 x y (@lem1969754 x y h1 h2)). Qed.
Lemma lem1969756 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term401 x y.
Proof. exact (EQ_MP (@lem1969709 x y) (@lem1969755 x y h1 h2)). Qed.
Lemma lem1969757 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term410 x y.
Proof. exact (@lem1969695 x y (@lem1969756 x y h1 h2)). Qed.
Lemma lem1969759 (x : real) (y : real) : (term96 x y) = (term95 x y).
Proof. exact (EQ_MP (@lem1968651 x y) (@lem1968650 x y)). Qed.
Lemma lem1969760 (x : real) (y : real) : (term411 x y) = (term412 x y).
Proof. exact (@lem1969759 (term398 x y) (term413 x y)). Qed.
Lemma lem1969762 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (@lem1968631 x y (@lem1968630 x y)). Qed.
Lemma lem1969763 (x : real) (y : real) : (term414 x y) = (term415 x y).
Proof. exact (@lem1969762 (sqrt x) (sqrt y)). Qed.
Lemma lem1969764 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1969765 (x : real) (y : real) : (term412 x y) = (term416 x y).
Proof. exact (MK_COMB (@lem1969764) (@lem1969763 x y)). Qed.
Lemma lem1969766 (x : real) (y : real) : (term411 x y) = (term416 x y).
Proof. exact (TRANS (@lem1969760 x y) (@lem1969765 x y)). Qed.
Lemma lem1969767 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1969768 (x : real) (y : real) : (term417 x y) = (term418 x y).
Proof. exact (MK_COMB (@lem1969767) (@lem1969766 x y)). Qed.
Lemma lem1969769 (x : real) (y : real) : (term123 x y) = (term123 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1969770 (x : real) (y : real) : (term419 x y) = (term420 x y).
Proof. exact (MK_COMB (@lem1969768 x y) (@lem1969769 x y)). Qed.
Lemma lem1969771 (x : real) (y : real) : (term420 x y) = (term419 x y).
Proof. exact (SYM (@lem1969770 x y)). Qed.
Lemma lem1969772 (x : real) : term421 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1969773 (x : real) : (term421 x) = (real_le x x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1969774 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1969773 x) (@lem1969772 x)). Qed.
Lemma lem1969775 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1969777 (x : real) : term422 x.
Proof. exact (@lem1945848 x). Qed.
Lemma lem1969778 (x : real) : (term422 x) = (term423 x).
Proof. exact (eq_refl (term422 x)). Qed.
Lemma lem1969779 (x : real) : term423 x.
Proof. exact (EQ_MP (@lem1969778 x) (@lem1969777 x)). Qed.
Lemma lem1969780 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (h1). Qed.
Lemma lem1969781 (x : real) (h1 : term111 x) : (term424 x) = x.
Proof. exact (@lem1969779 x (@lem1969780 x h1)). Qed.
Lemma lem1969787 (x : real) : (term111 x) = ((term111 x) = True).
Proof. exact (@lem7 (term111 x)). Qed.
Lemma lem1969789 (y : real) : (term111 y) = ((term111 y) = True).
Proof. exact (@lem7 (term111 y)). Qed.
Lemma lem1969794 (x : real) : term423 x.
Proof. exact (fun h0 : term111 x => @lem1969781 x h0). Qed.
Lemma lem1969796 (x : real) (h1 : term111 x) : (term111 x) = True.
Proof. exact (EQ_MP (@lem1969787 x) (@lem1969650 x h1)). Qed.
Lemma lem1969797 (x : real) (h1 : term111 x) : True = (term111 x).
Proof. exact (SYM (@lem1969796 x h1)). Qed.
Lemma lem1969798 (x : real) (h1 : term111 x) : term111 x.
Proof. exact (EQ_MP (@lem1969797 x h1) (@lem0)). Qed.
Lemma lem1969799 (x : real) (h1 : term111 x) : (term424 x) = x.
Proof. exact (@lem1969794 x (@lem1969798 x h1)). Qed.
Lemma lem1969800 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1969801 (x : real) (h1 : term111 x) : (term425 x) = (real_sub x).
Proof. exact (MK_COMB (@lem1969800) (@lem1969799 x h1)). Qed.
Lemma lem1969803 (x : real) : term423 x.
Proof. exact (fun h0 : term111 x => @lem1969781 x h0). Qed.
Lemma lem1969804 (y : real) : term423 y.
Proof. exact (@lem1969803 y). Qed.
Lemma lem1969806 (y : real) (h1 : term111 y) : (term111 y) = True.
Proof. exact (EQ_MP (@lem1969789 y) (@lem1969649 y h1)). Qed.
Lemma lem1969807 (y : real) (h1 : term111 y) : True = (term111 y).
Proof. exact (SYM (@lem1969806 y h1)). Qed.
Lemma lem1969808 (y : real) (h1 : term111 y) : term111 y.
Proof. exact (EQ_MP (@lem1969807 y h1) (@lem0)). Qed.
Lemma lem1969809 (y : real) (h1 : term111 y) : (term424 y) = y.
Proof. exact (@lem1969804 y (@lem1969808 y h1)). Qed.
Lemma lem1969810 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term415 x y) = (real_sub x y).
Proof. exact (MK_COMB (@lem1969801 x h1) (@lem1969809 y h2)). Qed.
Lemma lem1969811 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1969812 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term416 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1969811) (@lem1969810 x y h1 h2)). Qed.
Lemma lem1969813 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1969814 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term418 x y) = (term426 x y).
Proof. exact (MK_COMB (@lem1969813) (@lem1969812 x y h1 h2)). Qed.
Lemma lem1969815 (x : real) (y : real) : (term123 x y) = (term123 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1969816 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term420 x y) = (term427 x y).
Proof. exact (MK_COMB (@lem1969814 x y h1 h2) (@lem1969815 x y)). Qed.
Lemma lem1969818 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1969775 x) (@lem1969774 x)). Qed.
Lemma lem1969819 (x : real) (y : real) : (term427 x y) = True.
Proof. exact (@lem1969818 (term123 x y)). Qed.
Lemma lem1969820 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term420 x y) = True.
Proof. exact (TRANS (@lem1969816 x y h1 h2) (@lem1969819 x y)). Qed.
Lemma lem1969821 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : True = (term420 x y).
Proof. exact (SYM (@lem1969820 x y h1 h2)). Qed.
Lemma lem1969822 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term420 x y.
Proof. exact (EQ_MP (@lem1969821 x y h1 h2) (@lem0)). Qed.
Lemma lem1969823 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term419 x y.
Proof. exact (EQ_MP (@lem1969771 x y) (@lem1969822 x y h1 h2)). Qed.
Lemma lem1969824 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term428 x y.
Proof. exact (conj (@lem1969757 x y h1 h2) (@lem1969823 x y h1 h2)). Qed.
Lemma lem1969825 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term429 x y.
Proof. exact (ex_intro (term430 x y) (term411 x y) (@lem1969824 x y h1 h2)). Qed.
Lemma lem1969826 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term376 x y.
Proof. exact (@lem1969692 x y (@lem1969825 x y h1 h2)). Qed.
Lemma lem1969827 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term375 x y.
Proof. exact (EQ_MP (@lem1969661 x y) (@lem1969826 x y h1 h2)). Qed.
Lemma lem1969828 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term431 x y.
Proof. exact (@lem1969653 x y (@lem1969827 x y h1 h2)). Qed.
Lemma lem1969829 (x : real) (y : real) (h1 : term109 x y) : term111 y.
Proof. exact (proj2 (@lem1969648 x y h1)). Qed.
Lemma lem1969830 (x : real) (y : real) (h1 : term109 x y) : term111 x.
Proof. exact (proj1 (@lem1969648 x y h1)). Qed.
Lemma lem1969831 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term111 y) = (term431 x y).
Proof. exact (prop_ext (fun h3 : term111 y => @lem1969828 x y h1 h2) (fun h3 : term431 x y => @lem1969649 y h2)). Qed.
Lemma lem1969832 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term431 x y.
Proof. exact (EQ_MP (@lem1969831 x y h1 h2) (@lem1969649 y h2)). Qed.
Lemma lem1969833 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : (term111 x) = (term431 x y).
Proof. exact (prop_ext (fun h3 : term111 x => @lem1969832 x y h1 h2) (fun h3 : term431 x y => @lem1969650 x h1)). Qed.
Lemma lem1969834 (x : real) (y : real) (h1 : term111 x) (h2 : term111 y) : term431 x y.
Proof. exact (EQ_MP (@lem1969833 x y h1 h2) (@lem1969650 x h1)). Qed.
Lemma lem1969835 (y : real) (x : real) (h1 : term109 x y) (h2 : term111 x) : (term111 y) = (term431 x y).
Proof. exact (prop_ext (fun h3 : term111 y => @lem1969834 x y h2 h3) (fun h3 : term431 x y => @lem1969829 x y h1)). Qed.
Lemma lem1969836 (y : real) (x : real) (h1 : term109 x y) (h2 : term111 x) : term431 x y.
Proof. exact (EQ_MP (@lem1969835 y x h1 h2) (@lem1969829 x y h1)). Qed.
Lemma lem1969837 (x : real) (y : real) (h1 : term109 x y) : (term111 x) = (term431 x y).
Proof. exact (prop_ext (fun h2 : term111 x => @lem1969836 y x h1 h2) (fun h2 : term431 x y => @lem1969830 x y h1)). Qed.
Lemma lem1969838 (x : real) (y : real) (h1 : term109 x y) : term431 x y.
Proof. exact (EQ_MP (@lem1969837 x y h1) (@lem1969830 x y h1)). Qed.
Lemma lem1969839 (x : real) (y : real) : term432 x y.
Proof. exact (fun h0 : term109 x y => @lem1969838 x y h0). Qed.
Lemma lem1969844 (x : real) : term433 x.
Proof. exact (fun y : real => @lem1969839 x y). Qed.
Lemma lem1969849 : term434.
Proof. exact (fun x : real => @lem1969844 x). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RAT_LEMMA4_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import EQ_TRANS_spec.
Require Import REAL_LE_INV_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import REAL_LT_INV_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_MUL_RINV_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1338912_spec.
Require Import thm1340049_spec.
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
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1978411_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1978413 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1978414 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1978413 h1 x). Qed.
Lemma lem1978415 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1978416 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1978415 x) (@lem1978414 x h1)). Qed.
Lemma lem1978417 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1978416 x h1 y). Qed.
Lemma lem1978418 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1978419 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1978418 x y) (@lem1978417 x y h1)). Qed.
Lemma lem1978420 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1978421 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1978419 x y h1 (@lem1978420 x y h2)). Qed.
Lemma lem1978422 (x : real) (y : real) (h1 : real_lt x y) : term5 x y.
Proof. exact (fun h0 : term0 => @lem1978421 x y h0 h1). Qed.
Lemma lem1978423 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1978424 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1978422 x y h2 (@lem1978423 h1)). Qed.
Lemma lem1978425 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : real_lt x y => @lem1978424 x y h1 h0). Qed.
Lemma lem1978426 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1978425 x y h1). Qed.
Lemma lem1978427 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1978426 x h1). Qed.
Lemma lem1978428 : term6.
Proof. exact (fun h0 : term0 => @lem1978427 h0). Qed.
Lemma lem1978429 : term0.
Proof. exact (@lem1978428 (@lem1369133)). Qed.
Lemma lem1978430 (x : real) : term1 x.
Proof. exact (@lem1978429 x). Qed.
Lemma lem1978431 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1978432 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1978431 x) (@lem1978430 x)). Qed.
Lemma lem1978433 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1978432 x y). Qed.
Lemma lem1978434 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1978436 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1978437 (x : real) (h1 : term7) : term8 x.
Proof. exact (@lem1978436 h1 x). Qed.
Lemma lem1978438 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1978439 (x : real) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1978438 x) (@lem1978437 x h1)). Qed.
Lemma lem1978440 (x : real) (y : real) (h1 : term7) : term10 x y.
Proof. exact (@lem1978439 x h1 y). Qed.
Lemma lem1978441 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1978442 (x : real) (y : real) (h1 : term7) : term11 x y.
Proof. exact (EQ_MP (@lem1978441 x y) (@lem1978440 x y h1)). Qed.
Lemma lem1978443 (x : real) (y : real) (h1 : term12 x y) : term12 x y.
Proof. exact (h1). Qed.
Lemma lem1978444 (x : real) (y : real) (h1 : term7) (h2 : term12 x y) : term13 x y.
Proof. exact (@lem1978442 x y h1 (@lem1978443 x y h2)). Qed.
Lemma lem1978445 (x : real) (y : real) (h1 : term12 x y) : term14 x y.
Proof. exact (fun h0 : term7 => @lem1978444 x y h0 h1). Qed.
Lemma lem1978446 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1978447 (x : real) (y : real) (h1 : term7) (h2 : term12 x y) : term13 x y.
Proof. exact (@lem1978445 x y h2 (@lem1978446 h1)). Qed.
Lemma lem1978448 (x : real) (y : real) (h1 : term7) : term11 x y.
Proof. exact (fun h0 : term12 x y => @lem1978447 x y h1 h0). Qed.
Lemma lem1978449 (x : real) (h1 : term7) : term9 x.
Proof. exact (fun y : real => @lem1978448 x y h1). Qed.
Lemma lem1978450 (h1 : term7) : term7.
Proof. exact (fun x : real => @lem1978449 x h1). Qed.
Lemma lem1978451 : term15.
Proof. exact (fun h0 : term7 => @lem1978450 h0). Qed.
Lemma lem1978452 : term7.
Proof. exact (@lem1978451 (@lem1340049)). Qed.
Lemma lem1978453 (x : real) : term8 x.
Proof. exact (@lem1978452 x). Qed.
Lemma lem1978454 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1978455 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1978454 x) (@lem1978453 x)). Qed.
Lemma lem1978456 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1978455 x y). Qed.
Lemma lem1978457 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1978459 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1978460 (x : real) (h1 : term16) : term17 x.
Proof. exact (@lem1978459 h1 x). Qed.
Lemma lem1978461 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1978462 (x : real) (h1 : term16) : term18 x.
Proof. exact (EQ_MP (@lem1978461 x) (@lem1978460 x h1)). Qed.
Lemma lem1978463 (x : real) (h1 : term19 x) : term19 x.
Proof. exact (h1). Qed.
Lemma lem1978464 (x : real) (h1 : term16) (h2 : term19 x) : (term20 x) = term21.
Proof. exact (@lem1978462 x h1 (@lem1978463 x h2)). Qed.
Lemma lem1978465 (x : real) (h1 : term19 x) : term22 x.
Proof. exact (fun h0 : term16 => @lem1978464 x h0 h1). Qed.
Lemma lem1978466 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem1978467 (x : real) (h1 : term16) (h2 : term19 x) : (term20 x) = term21.
Proof. exact (@lem1978465 x h2 (@lem1978466 h1)). Qed.
Lemma lem1978468 (x : real) (h1 : term16) : term18 x.
Proof. exact (fun h0 : term19 x => @lem1978467 x h1 h0). Qed.
Lemma lem1978469 (h1 : term16) : term16.
Proof. exact (fun x : real => @lem1978468 x h1). Qed.
Lemma lem1978470 : term23.
Proof. exact (fun h0 : term16 => @lem1978469 h0). Qed.
Lemma lem1978471 : term16.
Proof. exact (@lem1978470 (@lem1591985)). Qed.
Lemma lem1978472 (x : real) : term17 x.
Proof. exact (@lem1978471 x). Qed.
Lemma lem1978473 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1978475 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1978476 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1978475 h1 x). Qed.
Lemma lem1978477 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1978478 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1978477 x) (@lem1978476 x h1)). Qed.
Lemma lem1978479 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1978478 x h1 y). Qed.
Lemma lem1978480 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1978481 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1978480 x y) (@lem1978479 x y h1)). Qed.
Lemma lem1978482 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1978483 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1978481 x y h1 (@lem1978482 x y h2)). Qed.
Lemma lem1978484 (x : real) (y : real) (h1 : real_lt x y) : term5 x y.
Proof. exact (fun h0 : term0 => @lem1978483 x y h0 h1). Qed.
Lemma lem1978485 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1978486 (x : real) (y : real) (h1 : term0) (h2 : real_lt x y) : real_le x y.
Proof. exact (@lem1978484 x y h2 (@lem1978485 h1)). Qed.
Lemma lem1978487 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : real_lt x y => @lem1978486 x y h1 h0). Qed.
Lemma lem1978488 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1978487 x y h1). Qed.
Lemma lem1978489 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1978488 x h1). Qed.
Lemma lem1978490 : term6.
Proof. exact (fun h0 : term0 => @lem1978489 h0). Qed.
Lemma lem1978491 : term0.
Proof. exact (@lem1978490 (@lem1369133)). Qed.
Lemma lem1978492 (x : real) : term1 x.
Proof. exact (@lem1978491 x). Qed.
Lemma lem1978493 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1978494 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1978493 x) (@lem1978492 x)). Qed.
Lemma lem1978495 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1978494 x y). Qed.
Lemma lem1978496 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1978498 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1978499 (x : real) (h1 : term24) : term25 x.
Proof. exact (@lem1978498 h1 x). Qed.
Lemma lem1978500 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1978501 (x : real) (h1 : term24) : term26 x.
Proof. exact (EQ_MP (@lem1978500 x) (@lem1978499 x h1)). Qed.
Lemma lem1978502 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1978503 (x : real) (h1 : term24) (h2 : term27 x) : term28 x.
Proof. exact (@lem1978501 x h1 (@lem1978502 x h2)). Qed.
Lemma lem1978504 (x : real) (h1 : term27 x) : term29 x.
Proof. exact (fun h0 : term24 => @lem1978503 x h0 h1). Qed.
Lemma lem1978505 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1978506 (x : real) (h1 : term24) (h2 : term27 x) : term28 x.
Proof. exact (@lem1978504 x h2 (@lem1978505 h1)). Qed.
Lemma lem1978507 (x : real) (h1 : term24) : term26 x.
Proof. exact (fun h0 : term27 x => @lem1978506 x h1 h0). Qed.
Lemma lem1978508 (h1 : term24) : term24.
Proof. exact (fun x : real => @lem1978507 x h1). Qed.
Lemma lem1978509 : term30.
Proof. exact (fun h0 : term24 => @lem1978508 h0). Qed.
Lemma lem1978510 : term24.
Proof. exact (@lem1978509 (@lem1591934)). Qed.
Lemma lem1978511 (x : real) : term25 x.
Proof. exact (@lem1978510 x). Qed.
Lemma lem1978512 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1978514 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1978515 (x : real) (h1 : term7) : term8 x.
Proof. exact (@lem1978514 h1 x). Qed.
Lemma lem1978516 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1978517 (x : real) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1978516 x) (@lem1978515 x h1)). Qed.
Lemma lem1978518 (x : real) (y : real) (h1 : term7) : term10 x y.
Proof. exact (@lem1978517 x h1 y). Qed.
Lemma lem1978519 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1978520 (x : real) (y : real) (h1 : term7) : term11 x y.
Proof. exact (EQ_MP (@lem1978519 x y) (@lem1978518 x y h1)). Qed.
Lemma lem1978521 (x : real) (y : real) (h1 : term12 x y) : term12 x y.
Proof. exact (h1). Qed.
Lemma lem1978522 (x : real) (y : real) (h1 : term7) (h2 : term12 x y) : term13 x y.
Proof. exact (@lem1978520 x y h1 (@lem1978521 x y h2)). Qed.
Lemma lem1978523 (x : real) (y : real) (h1 : term12 x y) : term14 x y.
Proof. exact (fun h0 : term7 => @lem1978522 x y h0 h1). Qed.
Lemma lem1978524 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1978525 (x : real) (y : real) (h1 : term7) (h2 : term12 x y) : term13 x y.
Proof. exact (@lem1978523 x y h2 (@lem1978524 h1)). Qed.
Lemma lem1978526 (x : real) (y : real) (h1 : term7) : term11 x y.
Proof. exact (fun h0 : term12 x y => @lem1978525 x y h1 h0). Qed.
Lemma lem1978527 (x : real) (h1 : term7) : term9 x.
Proof. exact (fun y : real => @lem1978526 x y h1). Qed.
Lemma lem1978528 (h1 : term7) : term7.
Proof. exact (fun x : real => @lem1978527 x h1). Qed.
Lemma lem1978529 : term15.
Proof. exact (fun h0 : term7 => @lem1978528 h0). Qed.
Lemma lem1978530 : term7.
Proof. exact (@lem1978529 (@lem1340049)). Qed.
Lemma lem1978531 (x : real) : term8 x.
Proof. exact (@lem1978530 x). Qed.
Lemma lem1978532 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1978533 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1978532 x) (@lem1978531 x)). Qed.
Lemma lem1978534 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1978533 x y). Qed.
Lemma lem1978535 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1978537 (x : real) : term31 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1978538 (x : real) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1978539 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1978538 x) (@lem1978537 x)). Qed.
Lemma lem1978540 (x : real) (y : real) : term33 x y.
Proof. exact (@lem1978539 x y). Qed.
Lemma lem1978541 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1978542 (x : real) (y : real) : term34 x y.
Proof. exact (EQ_MP (@lem1978541 x y) (@lem1978540 x y)). Qed.
Lemma lem1978543 (x : real) (y : real) (z : real) : term35 x y z.
Proof. exact (@lem1978542 x y z). Qed.
Lemma lem1978544 (x : real) (y : real) (z : real) : (term35 x y z) = ((term36 x y z) = (term37 x y z)).
Proof. exact (eq_refl (term35 x y z)). Qed.
Lemma lem1978546 (y : real) (h1 : term38 y) : term38 y.
Proof. exact (h1). Qed.
Lemma lem1978547 (x : real) (y : real) (h1 : term13 x y) : term13 x y.
Proof. exact (h1). Qed.
Lemma lem1978548 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1978549 (x : real) (y : real) (h1 : term39 x y) : term39 x y.
Proof. exact (h1). Qed.
Lemma lem1978551 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (EQ_MP (@lem1978544 x y z) (@lem1978543 x y z)). Qed.
Lemma lem1978552 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem1978551 x y (real_inv y)). Qed.
Lemma lem1978553 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1978554 (x : real) (y : real) : (term39 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1978553) (@lem1978552 x y)). Qed.
Lemma lem1978555 (x : real) (y : real) : (term43 x y) = (term39 x y).
Proof. exact (SYM (@lem1978554 x y)). Qed.
Lemma lem1978557 (x : real) (y : real) : term11 x y.
Proof. exact (EQ_MP (@lem1978535 x y) (@lem1978534 x y)). Qed.
Lemma lem1978558 (x : real) (y : real) : term44 x y.
Proof. exact (@lem1978557 (real_mul x y) (real_inv y)). Qed.
Lemma lem1978561 (x : real) (y : real) : (term13 x y) = ((term13 x y) = True).
Proof. exact (@lem7 (term13 x y)). Qed.
Lemma lem1978566 (x : real) (y : real) (h1 : term13 x y) : (term13 x y) = True.
Proof. exact (EQ_MP (@lem1978561 x y) (@lem1978547 x y h1)). Qed.
Lemma lem1978567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1978568 (x : real) (y : real) (h1 : term13 x y) : (term45 x y) = (and True).
Proof. exact (MK_COMB (@lem1978567) (@lem1978566 x y h1)). Qed.
Lemma lem1978569 (y : real) : (term28 y) = (term28 y).
Proof. exact (eq_refl (term28 y)). Qed.
Lemma lem1978570 (x : real) (y : real) (h1 : term13 x y) : (term46 x y) = (term47 y).
Proof. exact (MK_COMB (@lem1978568 x y h1) (@lem1978569 y)). Qed.
Lemma lem1978572 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1978573 (y : real) : (term47 y) = (term28 y).
Proof. exact (@lem1978572 (term28 y)). Qed.
Lemma lem1978574 (x : real) (y : real) (h1 : term13 x y) : (term46 x y) = (term28 y).
Proof. exact (TRANS (@lem1978570 x y h1) (@lem1978573 y)). Qed.
Lemma lem1978575 (x : real) (y : real) (h1 : term13 x y) : (term28 y) = (term46 x y).
Proof. exact (SYM (@lem1978574 x y h1)). Qed.
Lemma lem1978577 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1978512 x) (@lem1978511 x)). Qed.
Lemma lem1978578 (y : real) : term26 y.
Proof. exact (@lem1978577 y). Qed.
Lemma lem1978580 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1978496 x y) (@lem1978495 x y)). Qed.
Lemma lem1978581 (y : real) : term48 y.
Proof. exact (@lem1978580 term49 y). Qed.
Lemma lem1978582 (y : real) : (term38 y) = ((term38 y) = True).
Proof. exact (@lem7 (term38 y)). Qed.
Lemma lem1978587 (y : real) (h1 : term38 y) : (term38 y) = True.
Proof. exact (EQ_MP (@lem1978582 y) (@lem1978546 y h1)). Qed.
Lemma lem1978588 (y : real) (h1 : term38 y) : True = (term38 y).
Proof. exact (SYM (@lem1978587 y h1)). Qed.
Lemma lem1978589 (y : real) (h1 : term38 y) : term38 y.
Proof. exact (EQ_MP (@lem1978588 y h1) (@lem0)). Qed.
Lemma lem1978590 (y : real) (h1 : term38 y) : term27 y.
Proof. exact (@lem1978581 y (@lem1978589 y h1)). Qed.
Lemma lem1978591 (y : real) (h1 : term38 y) : term28 y.
Proof. exact (@lem1978578 y (@lem1978590 y h1)). Qed.
Lemma lem1978592 (x : real) (y : real) (h1 : term13 x y) (h2 : term38 y) : term46 x y.
Proof. exact (EQ_MP (@lem1978575 x y h1) (@lem1978591 y h2)). Qed.
Lemma lem1978593 (x : real) (y : real) (h1 : term13 x y) (h2 : term38 y) : term43 x y.
Proof. exact (@lem1978558 x y (@lem1978592 x y h1 h2)). Qed.
Lemma lem1978594 (x : real) (y : real) (h1 : term13 x y) (h2 : term38 y) : term39 x y.
Proof. exact (EQ_MP (@lem1978555 x y) (@lem1978593 x y h1 h2)). Qed.
Lemma lem1978596 (x : real) : term50 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1978597 (x : real) : (term50 x) = ((term51 x) = x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1978602 (y : real) (h1 : (term20 y) = term21) : (term20 y) = term21.
Proof. exact (h1). Qed.
Lemma lem1978603 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1978604 (x : real) (y : real) (h1 : (term20 y) = term21) : (term40 x y) = (term51 x).
Proof. exact (MK_COMB (@lem1978603 x) (@lem1978602 y h1)). Qed.
Lemma lem1978606 (x : real) : (term51 x) = x.
Proof. exact (EQ_MP (@lem1978597 x) (@lem1978596 x)). Qed.
Lemma lem1978607 (x : real) (y : real) (h1 : (term20 y) = term21) : (term40 x y) = x.
Proof. exact (TRANS (@lem1978604 x y h1) (@lem1978606 x)). Qed.
Lemma lem1978608 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1978609 (x : real) (y : real) (h1 : (term20 y) = term21) : (term39 x y) = (term27 x).
Proof. exact (MK_COMB (@lem1978608) (@lem1978607 x y h1)). Qed.
Lemma lem1978610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1978611 (x : real) (y : real) (h1 : (term20 y) = term21) : (term52 x y) = (term53 x).
Proof. exact (MK_COMB (@lem1978610) (@lem1978609 x y h1)). Qed.
Lemma lem1978612 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1978613 (x : real) (y : real) (h1 : (term20 y) = term21) : (term54 y x) = (term55 x).
Proof. exact (MK_COMB (@lem1978611 x y h1) (@lem1978612 x)). Qed.
Lemma lem1978615 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1978616 (x : real) : (term55 x) = True.
Proof. exact (@lem1978615 (term27 x)). Qed.
Lemma lem1978617 (x : real) (y : real) (h1 : (term20 y) = term21) : (term54 y x) = True.
Proof. exact (TRANS (@lem1978613 x y h1) (@lem1978616 x)). Qed.
Lemma lem1978618 (x : real) (y : real) (h1 : (term20 y) = term21) : True = (term54 y x).
Proof. exact (SYM (@lem1978617 x y h1)). Qed.
Lemma lem1978619 (x : real) (y : real) (h1 : (term20 y) = term21) : term54 y x.
Proof. exact (EQ_MP (@lem1978618 x y h1) (@lem0)). Qed.
Lemma lem1978621 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1978473 x) (@lem1978472 x)). Qed.
Lemma lem1978622 (y : real) : term18 y.
Proof. exact (@lem1978621 y). Qed.
Lemma lem1978631 (y : real) : (term56 y) = (y = term49).
Proof. exact (@lem16933 (y = term49)). Qed.
Lemma lem1978633 (y : real) : (term57 y) = (term57 y).
Proof. exact (eq_refl (term57 y)). Qed.
Lemma lem1978634 (y : real) : (term58 y) = (term59 y).
Proof. exact (MK_COMB (@lem1978633 y) (@lem1978631 y)). Qed.
Lemma lem1978635 (y : real) : (term60 y) = (term58 y).
Proof. exact (@lem17362 (term38 y) (term19 y)). Qed.
Lemma lem1978643 (y : real) : (term60 y) = (term59 y).
Proof. exact (TRANS (@lem1978635 y) (@lem1978634 y)). Qed.
Lemma lem1978644 (y : real) : (term38 y) = (term61 y).
Proof. exact (@lem1483521 y term49). Qed.
Lemma lem1978650 (y : real) : (term62 y) = (term63 y).
Proof. exact (@lem1483519 y term49). Qed.
Lemma lem1978652 (x : nat) : (term64 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1978653 : term65 = term49.
Proof. exact (@lem1978652 term66). Qed.
Lemma lem1978654 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1978655 (y : real) : (term63 y) = (term67 y).
Proof. exact (MK_COMB (@lem1978654 y) (@lem1978653)). Qed.
Lemma lem1978656 (y : real) : (term67 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1978657 (y : real) : (term63 y) = y.
Proof. exact (TRANS (@lem1978655 y) (@lem1978656 y)). Qed.
Lemma lem1978659 (y : real) : (term62 y) = y.
Proof. exact (TRANS (@lem1978650 y) (@lem1978657 y)). Qed.
Lemma lem1978660 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1978661 (y : real) : (term68 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1978660) (@lem1978659 y)). Qed.
Lemma lem1978662 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978663 (y : real) : (term61 y) = (term69 y).
Proof. exact (MK_COMB (@lem1978661 y) (@lem1978662)). Qed.
Lemma lem1978664 (y : real) : (term38 y) = (term69 y).
Proof. exact (TRANS (@lem1978644 y) (@lem1978663 y)). Qed.
Lemma lem1978665 (y : real) : (y = term49) = ((term62 y) = term49).
Proof. exact (@lem1483529 y term49). Qed.
Lemma lem1978671 (y : real) : (term62 y) = (term63 y).
Proof. exact (@lem1483519 y term49). Qed.
Lemma lem1978673 (x : nat) : (term64 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1978674 : term65 = term49.
Proof. exact (@lem1978673 term66). Qed.
Lemma lem1978675 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1978676 (y : real) : (term63 y) = (term67 y).
Proof. exact (MK_COMB (@lem1978675 y) (@lem1978674)). Qed.
Lemma lem1978677 (y : real) : (term67 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1978678 (y : real) : (term63 y) = y.
Proof. exact (TRANS (@lem1978676 y) (@lem1978677 y)). Qed.
Lemma lem1978680 (y : real) : (term62 y) = y.
Proof. exact (TRANS (@lem1978671 y) (@lem1978678 y)). Qed.
Lemma lem1978681 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1978682 (y : real) : (term70 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1978681) (@lem1978680 y)). Qed.
Lemma lem1978683 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978684 (y : real) : ((term62 y) = term49) = (y = term49).
Proof. exact (MK_COMB (@lem1978682 y) (@lem1978683)). Qed.
Lemma lem1978685 (y : real) : (y = term49) = (y = term49).
Proof. exact (TRANS (@lem1978665 y) (@lem1978684 y)). Qed.
Lemma lem1978686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1978687 (y : real) : (term57 y) = (term71 y).
Proof. exact (MK_COMB (@lem1978686) (@lem1978664 y)). Qed.
Lemma lem1978688 (y : real) : (term59 y) = (term72 y).
Proof. exact (MK_COMB (@lem1978687 y) (@lem1978685 y)). Qed.
Lemma lem1978703 (y : real) : (term60 y) = (term72 y).
Proof. exact (TRANS (@lem1978643 y) (@lem1978688 y)). Qed.
Lemma lem1978707 (y : real) (h1 : term72 y) : term72 y.
Proof. exact (h1). Qed.
Lemma lem1978708 (y : real) (h1 : term72 y) : y = term49.
Proof. exact (proj2 (@lem1978707 y h1)). Qed.
Lemma lem1978709 (y : real) (h1 : term72 y) : term69 y.
Proof. exact (proj1 (@lem1978707 y h1)). Qed.
Lemma lem1978711 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1978712 : term74 = term75.
Proof. exact (@lem1978711 (NUMERAL 0) term66). Qed.
Lemma lem1978713 : term76 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1978714 (h1 : term76 = (BIT1 0)) : term75 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1978715 : (term76 = (BIT1 0)) = (term75 = True).
Proof. exact (prop_ext (fun h1 : term76 = (BIT1 0) => @lem1978714 h1) (fun h1 : term75 = True => @lem1978713)). Qed.
Lemma lem1978716 : term75 = True.
Proof. exact (EQ_MP (@lem1978715) (@lem1978713)). Qed.
Lemma lem1978717 : term74 = True.
Proof. exact (TRANS (@lem1978712) (@lem1978716)). Qed.
Lemma lem1978718 : True = term74.
Proof. exact (SYM (@lem1978717)). Qed.
Lemma lem1978719 : term74.
Proof. exact (EQ_MP (@lem1978718) (@lem0)). Qed.
Lemma lem1978720 (y : real) (h1 : term72 y) : term77 y.
Proof. exact (conj (@lem1978719) (@lem1978709 y h1)). Qed.
Lemma lem1978722 (x : real) (y : real) : term78 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1978723 (y : real) : term79 y.
Proof. exact (@lem1978722 term21 y). Qed.
Lemma lem1978724 (y : real) (h1 : term72 y) : term80 y.
Proof. exact (@lem1978723 y (@lem1978720 y h1)). Qed.
Lemma lem1978725 (y : real) : (term81 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1978726 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1978727 (y : real) : (term82 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1978726) (@lem1978725 y)). Qed.
Lemma lem1978728 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978729 (y : real) : (term80 y) = (term69 y).
Proof. exact (MK_COMB (@lem1978727 y) (@lem1978728)). Qed.
Lemma lem1978730 (y : real) (h1 : term72 y) : term69 y.
Proof. exact (EQ_MP (@lem1978729 y) (@lem1978724 y h1)). Qed.
Lemma lem1978732 (y : real) : term83 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1978733 (y : real) (h1 : term72 y) : term84 y.
Proof. exact (@lem1978732 y (@lem1978708 y h1)). Qed.
Lemma lem1978734 (y : real) (h1 : term72 y) : term85 y.
Proof. exact (@lem1978733 y h1 term86). Qed.
Lemma lem1978735 (y : real) : (term85 y) = ((term87 y) = term49).
Proof. exact (eq_refl (term85 y)). Qed.
Lemma lem1978742 (y : real) (h1 : term72 y) : (term87 y) = term49.
Proof. exact (EQ_MP (@lem1978735 y) (@lem1978734 y h1)). Qed.
Lemma lem1978743 (y : real) (h1 : term72 y) : term88 y.
Proof. exact (conj (@lem1978742 y h1) (@lem1978730 y h1)). Qed.
Lemma lem1978745 (x : real) (y : real) : term89 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1978746 (y : real) : term90 y.
Proof. exact (@lem1978745 (term87 y) y). Qed.
Lemma lem1978747 (y : real) (h1 : term72 y) : term91 y.
Proof. exact (@lem1978746 y (@lem1978743 y h1)). Qed.
Lemma lem1978748 (y : real) : (term92 y) = (term93 y).
Proof. exact (@lem1483440 term86 y). Qed.
Lemma lem1978750 (m : nat) : (term94 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1978751 : term95 = term49.
Proof. exact (@lem1978750 term66). Qed.
Lemma lem1978752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1978753 : term96 = term97.
Proof. exact (MK_COMB (@lem1978752) (@lem1978751)). Qed.
Lemma lem1978754 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1978755 (y : real) : (term93 y) = (term98 y).
Proof. exact (MK_COMB (@lem1978753) (@lem1978754 y)). Qed.
Lemma lem1978756 (y : real) : (term92 y) = (term98 y).
Proof. exact (TRANS (@lem1978748 y) (@lem1978755 y)). Qed.
Lemma lem1978757 (y : real) : (term98 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1978758 (y : real) : (term92 y) = term49.
Proof. exact (TRANS (@lem1978756 y) (@lem1978757 y)). Qed.
Lemma lem1978759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1978760 (y : real) : (term99 y) = term100.
Proof. exact (MK_COMB (@lem1978759) (@lem1978758 y)). Qed.
Lemma lem1978761 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978762 (y : real) : (term91 y) = term101.
Proof. exact (MK_COMB (@lem1978760 y) (@lem1978761)). Qed.
Lemma lem1978763 (y : real) (h1 : term72 y) : term101.
Proof. exact (EQ_MP (@lem1978762 y) (@lem1978747 y h1)). Qed.
Lemma lem1978765 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1978766 : term101 = term102.
Proof. exact (@lem1978765 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1978767 : term102 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1978768 : term101 = False.
Proof. exact (TRANS (@lem1978766) (@lem1978767)). Qed.
Lemma lem1978769 (y : real) (h1 : term72 y) : False.
Proof. exact (EQ_MP (@lem1978768) (@lem1978763 y h1)). Qed.
Lemma lem1978771 (y : real) (h1 : term72 y) : term72 y.
Proof. exact (h1). Qed.
Lemma lem1978772 (y : real) (h1 : term72 y) : (term72 y) = False.
Proof. exact (prop_ext (fun h2 : term72 y => @lem1978769 y h1) (fun h2 : False => @lem1978771 y h1)). Qed.
Lemma lem1978773 (y : real) (h1 : term72 y) : False.
Proof. exact (EQ_MP (@lem1978772 y h1) (@lem1978771 y h1)). Qed.
Lemma lem1978774 (y : real) (h1 : term60 y) : term60 y.
Proof. exact (h1). Qed.
Lemma lem1978775 (y : real) (h1 : term60 y) : term72 y.
Proof. exact (EQ_MP (@lem1978703 y) (@lem1978774 y h1)). Qed.
Lemma lem1978776 (y : real) (h1 : term60 y) : (term72 y) = False.
Proof. exact (prop_ext (fun h2 : term72 y => @lem1978773 y h2) (fun h2 : False => @lem1978775 y h1)). Qed.
Lemma lem1978777 (y : real) (h1 : term60 y) : False.
Proof. exact (EQ_MP (@lem1978776 y h1) (@lem1978775 y h1)). Qed.
Lemma lem1978778 (y : real) : term103 y.
Proof. exact (fun h0 : term60 y => @lem1978777 y h0). Qed.
Lemma lem1978779 (y : real) : term104 y.
Proof. exact (@lem1386578 (term105 y)). Qed.
Lemma lem1978780 (y : real) : term105 y.
Proof. exact (@lem1978779 y (@lem1978778 y)). Qed.
Lemma lem1978781 (y : real) (h1 : term38 y) : term19 y.
Proof. exact (@lem1978780 y (@lem1978546 y h1)). Qed.
Lemma lem1978782 (y : real) (h1 : term38 y) : (term20 y) = term21.
Proof. exact (@lem1978622 y (@lem1978781 y h1)). Qed.
Lemma lem1978783 (x : real) (y : real) (h1 : term38 y) : ((term20 y) = term21) = (term54 y x).
Proof. exact (prop_ext (fun h2 : (term20 y) = term21 => @lem1978619 x y h2) (fun h2 : term54 y x => @lem1978782 y h1)). Qed.
Lemma lem1978784 (x : real) (y : real) (h1 : term38 y) : term54 y x.
Proof. exact (EQ_MP (@lem1978783 x y h1) (@lem1978782 y h1)). Qed.
Lemma lem1978785 (x : real) (y : real) (h1 : term39 x y) (h2 : term38 y) : term27 x.
Proof. exact (@lem1978784 x y h2 (@lem1978549 x y h1)). Qed.
Lemma lem1978786 (x : real) (y : real) (h1 : term13 x y) (h2 : term38 y) : (term39 x y) = (term27 x).
Proof. exact (prop_ext (fun h3 : term39 x y => @lem1978785 x y h3 h2) (fun h3 : term27 x => @lem1978594 x y h1 h2)). Qed.
Lemma lem1978787 (x : real) (y : real) (h1 : term13 x y) (h2 : term38 y) : term27 x.
Proof. exact (EQ_MP (@lem1978786 x y h1 h2) (@lem1978594 x y h1 h2)). Qed.
Lemma lem1978789 (x : real) (y : real) : term11 x y.
Proof. exact (EQ_MP (@lem1978457 x y) (@lem1978456 x y)). Qed.
Lemma lem1978792 (x : real) : (term27 x) = ((term27 x) = True).
Proof. exact (@lem7 (term27 x)). Qed.
Lemma lem1978797 (x : real) (h1 : term27 x) : (term27 x) = True.
Proof. exact (EQ_MP (@lem1978792 x) (@lem1978548 x h1)). Qed.
Lemma lem1978798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1978799 (x : real) (h1 : term27 x) : (term106 x) = (and True).
Proof. exact (MK_COMB (@lem1978798) (@lem1978797 x h1)). Qed.
Lemma lem1978800 (y : real) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1978801 (y : real) (x : real) (h1 : term27 x) : (term12 x y) = (term107 y).
Proof. exact (MK_COMB (@lem1978799 x h1) (@lem1978800 y)). Qed.
Lemma lem1978803 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1978804 (y : real) : (term107 y) = (term27 y).
Proof. exact (@lem1978803 (term27 y)). Qed.
Lemma lem1978805 (y : real) (x : real) (h1 : term27 x) : (term12 x y) = (term27 y).
Proof. exact (TRANS (@lem1978801 y x h1) (@lem1978804 y)). Qed.
Lemma lem1978806 (y : real) (x : real) (h1 : term27 x) : (term27 y) = (term12 x y).
Proof. exact (SYM (@lem1978805 y x h1)). Qed.
Lemma lem1978808 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1978434 x y) (@lem1978433 x y)). Qed.
Lemma lem1978809 (y : real) : term48 y.
Proof. exact (@lem1978808 term49 y). Qed.
Lemma lem1978810 (y : real) : (term38 y) = ((term38 y) = True).
Proof. exact (@lem7 (term38 y)). Qed.
Lemma lem1978815 (y : real) (h1 : term38 y) : (term38 y) = True.
Proof. exact (EQ_MP (@lem1978810 y) (@lem1978546 y h1)). Qed.
Lemma lem1978816 (y : real) (h1 : term38 y) : True = (term38 y).
Proof. exact (SYM (@lem1978815 y h1)). Qed.
Lemma lem1978817 (y : real) (h1 : term38 y) : term38 y.
Proof. exact (EQ_MP (@lem1978816 y h1) (@lem0)). Qed.
Lemma lem1978818 (y : real) (h1 : term38 y) : term27 y.
Proof. exact (@lem1978809 y (@lem1978817 y h1)). Qed.
Lemma lem1978819 (x : real) (y : real) (h1 : term27 x) (h2 : term38 y) : term12 x y.
Proof. exact (EQ_MP (@lem1978806 y x h1) (@lem1978818 y h2)). Qed.
Lemma lem1978820 (x : real) (y : real) (h1 : term27 x) (h2 : term38 y) : term13 x y.
Proof. exact (@lem1978789 x y (@lem1978819 x y h1 h2)). Qed.
Lemma lem1978821 (x : real) (y : real) (h1 : term38 y) : term108 x y.
Proof. exact (fun h0 : term27 x => @lem1978820 x y h0 h1). Qed.
Lemma lem1978822 (x : real) (y : real) (h1 : term38 y) : term109 y x.
Proof. exact (fun h0 : term13 x y => @lem1978787 x y h0 h1). Qed.
Lemma lem1978823 (x : real) (y : real) (h1 : term38 y) : term110 x y.
Proof. exact (conj (@lem1978822 x y h1) (@lem1978821 x y h1)). Qed.
Lemma lem1978824 (y : real) (x : real) : (term110 x y) = ((term13 x y) = (term27 x)).
Proof. exact (@lem32 (term13 x y) (term27 x)). Qed.
Lemma lem1978825 (x : real) (y : real) (h1 : term38 y) : (term13 x y) = (term27 x).
Proof. exact (EQ_MP (@lem1978824 y x) (@lem1978823 x y h1)). Qed.
Lemma lem1978826 (y : real) (x : real) : term111 y x.
Proof. exact (fun h0 : term38 y => @lem1978825 x y h0). Qed.
Lemma lem1978827 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1978828 (x : real) (h1 : term112) : term113 x.
Proof. exact (@lem1978827 h1 x). Qed.
Lemma lem1978829 (x : real) : (term113 x) = (term114 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1978830 (x : real) (h1 : term112) : term114 x.
Proof. exact (EQ_MP (@lem1978829 x) (@lem1978828 x h1)). Qed.
Lemma lem1978831 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1978832 (x : real) (h1 : term112) (h2 : term38 x) : term115 x.
Proof. exact (@lem1978830 x h1 (@lem1978831 x h2)). Qed.
Lemma lem1978833 (x : real) (h1 : term38 x) : term116 x.
Proof. exact (fun h0 : term112 => @lem1978832 x h0 h1). Qed.
Lemma lem1978834 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1978835 (x : real) (h1 : term112) (h2 : term38 x) : term115 x.
Proof. exact (@lem1978833 x h2 (@lem1978834 h1)). Qed.
Lemma lem1978836 (x : real) (h1 : term112) : term114 x.
Proof. exact (fun h0 : term38 x => @lem1978835 x h1 h0). Qed.
Lemma lem1978837 (h1 : term112) : term112.
Proof. exact (fun x : real => @lem1978836 x h1). Qed.
Lemma lem1978838 : term117.
Proof. exact (fun h0 : term112 => @lem1978837 h0). Qed.
Lemma lem1978839 : term112.
Proof. exact (@lem1978838 (@lem1589984)). Qed.
Lemma lem1978840 (x : real) : term113 x.
Proof. exact (@lem1978839 x). Qed.
Lemma lem1978841 (x : real) : (term113 x) = (term114 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1978843 (y : real) (x : real) (h1 : term111 y x) : term111 y x.
Proof. exact (h1). Qed.
Lemma lem1978844 (y : real) (h1 : term38 y) : term38 y.
Proof. exact (h1). Qed.
Lemma lem1978845 (x : real) (y : real) (h1 : term111 y x) (h2 : term38 y) : (term13 x y) = (term27 x).
Proof. exact (@lem1978843 y x h1 (@lem1978844 y h2)). Qed.
Lemma lem1978846 (x : real) (y : real) (h1 : term38 y) : term118 y x.
Proof. exact (fun h0 : term111 y x => @lem1978845 x y h0 h1). Qed.
Lemma lem1978847 (y : real) (x : real) (h1 : term111 y x) : term111 y x.
Proof. exact (h1). Qed.
Lemma lem1978848 (x : real) (y : real) (h1 : term111 y x) (h2 : term38 y) : (term13 x y) = (term27 x).
Proof. exact (@lem1978846 x y h2 (@lem1978847 y x h1)). Qed.
Lemma lem1978849 (y : real) (x : real) (h1 : term111 y x) : term111 y x.
Proof. exact (fun h0 : term38 y => @lem1978848 x y h1 h0). Qed.
Lemma lem1978850 (y : real) (x : real) : term119 y x.
Proof. exact (fun h0 : term111 y x => @lem1978849 y x h0). Qed.
Lemma lem1978852 (x : real) : term31 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1978853 (x : real) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1978854 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1978853 x) (@lem1978852 x)). Qed.
Lemma lem1978855 (x : real) (y : real) : term33 x y.
Proof. exact (@lem1978854 x y). Qed.
Lemma lem1978856 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1978857 (x : real) (y : real) : term34 x y.
Proof. exact (EQ_MP (@lem1978856 x y) (@lem1978855 x y)). Qed.
Lemma lem1978858 (x : real) (y : real) (z : real) : term35 x y z.
Proof. exact (@lem1978857 x y z). Qed.
Lemma lem1978859 (x : real) (y : real) (z : real) : (term35 x y z) = ((term36 x y z) = (term37 x y z)).
Proof. exact (eq_refl (term35 x y z)). Qed.
Lemma lem1978861 {A : Type'} (h1 : term120 A) : term120 A.
Proof. exact (h1). Qed.
Lemma lem1978862 {A : Type'} (x : A) (h1 : term120 A) : term121 A x.
Proof. exact (@lem1978861 A h1 x). Qed.
Lemma lem1978863 {A : Type'} (x : A) : (term121 A x) = (term122 A x).
Proof. exact (eq_refl (term121 A x)). Qed.
Lemma lem1978864 {A : Type'} (x : A) (h1 : term120 A) : term122 A x.
Proof. exact (EQ_MP (@lem1978863 A x) (@lem1978862 A x h1)). Qed.
Lemma lem1978865 {A : Type'} (x : A) (y : A) (h1 : term120 A) : term123 A x y.
Proof. exact (@lem1978864 A x h1 y). Qed.
Lemma lem1978866 {A : Type'} (y : A) (x : A) : (term123 A x y) = (term124 A y x).
Proof. exact (eq_refl (term123 A x y)). Qed.
Lemma lem1978867 {A : Type'} (y : A) (x : A) (h1 : term120 A) : term124 A y x.
Proof. exact (EQ_MP (@lem1978866 A y x) (@lem1978865 A x y h1)). Qed.
Lemma lem1978868 {A : Type'} (y : A) (x : A) (z : A) (h1 : term120 A) : term125 A y x z.
Proof. exact (@lem1978867 A y x h1 z). Qed.
Lemma lem1978869 {A : Type'} (y : A) (x : A) (z : A) : (term125 A y x z) = (term126 A y x z).
Proof. exact (eq_refl (term125 A y x z)). Qed.
Lemma lem1978870 {A : Type'} (y : A) (x : A) (z : A) (h1 : term120 A) : term126 A y x z.
Proof. exact (EQ_MP (@lem1978869 A y x z) (@lem1978868 A y x z h1)). Qed.
Lemma lem1978871 {A : Type'} (x : A) (y : A) (z : A) (h1 : term127 A x y z) : term127 A x y z.
Proof. exact (h1). Qed.
Lemma lem1978872 {A : Type'} (x : A) (y : A) (z : A) (h1 : term120 A) (h2 : term127 A x y z) : x = z.
Proof. exact (@lem1978870 A y x z h1 (@lem1978871 A x y z h2)). Qed.
Lemma lem1978873 {A : Type'} (x : A) (y : A) (z : A) (h1 : term127 A x y z) : term128 A x z.
Proof. exact (fun h0 : term120 A => @lem1978872 A x y z h0 h1). Qed.
Lemma lem1978874 {A : Type'} (x : A) (z : A) (h1 : term129 A x z) : term129 A x z.
Proof. exact (h1). Qed.
Lemma lem1978875 {A : Type'} (x : A) (z : A) (h1 : term129 A x z) : term128 A x z.
Proof. exact (ex_elim (@lem1978874 A x z h1) (fun y : A => fun h0 : term130 A x z y => @lem1978873 A x y z h0)). Qed.
Lemma lem1978876 {A : Type'} (h1 : term120 A) : term120 A.
Proof. exact (h1). Qed.
Lemma lem1978877 {A : Type'} (x : A) (z : A) (h1 : term120 A) (h2 : term129 A x z) : x = z.
Proof. exact (@lem1978875 A x z h2 (@lem1978876 A h1)). Qed.
Lemma lem1978878 {A : Type'} (x : A) (z : A) (h1 : term120 A) : term131 A x z.
Proof. exact (fun h0 : term129 A x z => @lem1978877 A x z h1 h0). Qed.
Lemma lem1978879 {A : Type'} (x : A) (h1 : term120 A) : term132 A x.
Proof. exact (fun z : A => @lem1978878 A x z h1). Qed.
Lemma lem1978880 {A : Type'} (h1 : term120 A) : term133 A.
Proof. exact (fun x : A => @lem1978879 A x h1). Qed.
Lemma lem1978881 {A : Type'} : term134 A.
Proof. exact (fun h0 : term120 A => @lem1978880 A h0). Qed.
Lemma lem1978882 {A : Type'} : term133 A.
Proof. exact (@lem1978881 A (@lem403 A)). Qed.
Lemma lem1978883 {A : Type'} (x : A) : term135 A x.
Proof. exact (@lem1978882 A x). Qed.
Lemma lem1978884 {A : Type'} (x : A) : (term135 A x) = (term132 A x).
Proof. exact (eq_refl (term135 A x)). Qed.
Lemma lem1978885 {A : Type'} (x : A) : term132 A x.
Proof. exact (EQ_MP (@lem1978884 A x) (@lem1978883 A x)). Qed.
Lemma lem1978886 {A : Type'} (x : A) (z : A) : term136 A x z.
Proof. exact (@lem1978885 A x z). Qed.
Lemma lem1978887 {A : Type'} (x : A) (z : A) : (term136 A x z) = (term131 A x z).
Proof. exact (eq_refl (term136 A x z)). Qed.
Lemma lem1978925 (b : real) (a : real) : (term137 b a) = (term138 b a).
Proof. exact (@lem17646 (real_le a b) (term139 b a)). Qed.
Lemma lem1978926 (b : real) (a : real) : (real_le a b) = (term140 b a).
Proof. exact (@lem1483523 b a). Qed.
Lemma lem1978932 (b : real) (a : real) : (real_sub b a) = (term141 b a).
Proof. exact (@lem1483519 b a). Qed.
Lemma lem1978937 (a : real) (b : real) : (term141 b a) = (term142 a b).
Proof. exact (@lem1483488 (term87 a) b). Qed.
Lemma lem1978939 (a : real) (b : real) : (real_sub b a) = (term142 a b).
Proof. exact (TRANS (@lem1978932 b a) (@lem1978937 a b)). Qed.
Lemma lem1978940 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1978941 (a : real) (b : real) : (term143 b a) = (term144 a b).
Proof. exact (MK_COMB (@lem1978940) (@lem1978939 a b)). Qed.
Lemma lem1978942 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978943 (a : real) (b : real) : (term140 b a) = (term145 a b).
Proof. exact (MK_COMB (@lem1978941 a b) (@lem1978942)). Qed.
Lemma lem1978944 (a : real) (b : real) : (real_le a b) = (term145 a b).
Proof. exact (TRANS (@lem1978926 b a) (@lem1978943 a b)). Qed.
Lemma lem1978945 (b : real) (a : real) : (term146 b a) = (term147 b a).
Proof. exact (@lem1483533 term49 (real_sub b a)). Qed.
Lemma lem1978951 (b : real) (a : real) : (real_sub b a) = (term141 b a).
Proof. exact (@lem1483519 b a). Qed.
Lemma lem1978956 (a : real) (b : real) : (term141 b a) = (term142 a b).
Proof. exact (@lem1483488 (term87 a) b). Qed.
Lemma lem1978958 (a : real) (b : real) : (real_sub b a) = (term142 a b).
Proof. exact (TRANS (@lem1978951 b a) (@lem1978956 a b)). Qed.
Lemma lem1978961 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem1978962 (a : real) (b : real) : (term149 b a) = (term150 a b).
Proof. exact (MK_COMB (@lem1978961) (@lem1978958 a b)). Qed.
Lemma lem1978963 (a : real) (b : real) : (term150 a b) = (term151 a b).
Proof. exact (@lem1483519 term49 (term142 a b)). Qed.
Lemma lem1978964 (a : real) (b : real) : (term152 a b) = (term153 a b).
Proof. exact (@lem1483508 (term87 a) term86 b). Qed.
Lemma lem1978965 (b : real) : (term87 b) = (term87 b).
Proof. exact (eq_refl (term87 b)). Qed.
Lemma lem1978966 (a : real) : (term154 a) = (term155 a).
Proof. exact (@lem1483476 term86 term86 a). Qed.
Lemma lem1978968 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1978969 : term158 = term159.
Proof. exact (@lem1978968 term66 term66). Qed.
Lemma lem1978970 : (term160 = (BIT1 0)) = (term161 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1978971 : term161 = term66.
Proof. exact (EQ_MP (@lem1978970) (@lem940073)). Qed.
Lemma lem1978972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1978973 : term159 = term21.
Proof. exact (MK_COMB (@lem1978972) (@lem1978971)). Qed.
Lemma lem1978974 : term158 = term21.
Proof. exact (TRANS (@lem1978969) (@lem1978973)). Qed.
Lemma lem1978975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1978976 : term162 = term163.
Proof. exact (MK_COMB (@lem1978975) (@lem1978974)). Qed.
Lemma lem1978977 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1978978 (a : real) : (term155 a) = (term81 a).
Proof. exact (MK_COMB (@lem1978976) (@lem1978977 a)). Qed.
Lemma lem1978979 (a : real) : (term154 a) = (term81 a).
Proof. exact (TRANS (@lem1978966 a) (@lem1978978 a)). Qed.
Lemma lem1978980 (a : real) : (term81 a) = a.
Proof. exact (@lem1483436 a). Qed.
Lemma lem1978981 (a : real) : (term154 a) = a.
Proof. exact (TRANS (@lem1978979 a) (@lem1978980 a)). Qed.
Lemma lem1978982 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1978983 (a : real) : (term164 a) = (real_add a).
Proof. exact (MK_COMB (@lem1978982) (@lem1978981 a)). Qed.
Lemma lem1978984 (a : real) (b : real) : (term153 a b) = (term141 a b).
Proof. exact (MK_COMB (@lem1978983 a) (@lem1978965 b)). Qed.
Lemma lem1978985 (a : real) (b : real) : (term152 a b) = (term141 a b).
Proof. exact (TRANS (@lem1978964 a b) (@lem1978984 a b)). Qed.
Lemma lem1978986 : term165 = term165.
Proof. exact (eq_refl term165). Qed.
Lemma lem1978987 (a : real) (b : real) : (term151 a b) = (term166 a b).
Proof. exact (MK_COMB (@lem1978986) (@lem1978985 a b)). Qed.
Lemma lem1978988 (a : real) (b : real) : (term166 a b) = (term141 a b).
Proof. exact (@lem1483448 (term141 a b)). Qed.
Lemma lem1978989 (a : real) (b : real) : (term151 a b) = (term141 a b).
Proof. exact (TRANS (@lem1978987 a b) (@lem1978988 a b)). Qed.
Lemma lem1978990 (a : real) (b : real) : (term150 a b) = (term141 a b).
Proof. exact (TRANS (@lem1978963 a b) (@lem1978989 a b)). Qed.
Lemma lem1978991 (a : real) (b : real) : (term149 b a) = (term141 a b).
Proof. exact (TRANS (@lem1978962 a b) (@lem1978990 a b)). Qed.
Lemma lem1978992 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1978993 (a : real) (b : real) : (term167 b a) = (term168 a b).
Proof. exact (MK_COMB (@lem1978992) (@lem1978991 a b)). Qed.
Lemma lem1978994 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1978995 (a : real) (b : real) : (term147 b a) = (term169 a b).
Proof. exact (MK_COMB (@lem1978993 a b) (@lem1978994)). Qed.
Lemma lem1978996 (a : real) (b : real) : (term146 b a) = (term169 a b).
Proof. exact (TRANS (@lem1978945 b a) (@lem1978995 a b)). Qed.
Lemma lem1978997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1978998 (a : real) (b : real) : (term170 a b) = (term171 a b).
Proof. exact (MK_COMB (@lem1978997) (@lem1978944 a b)). Qed.
Lemma lem1978999 (a : real) (b : real) : (term172 b a) = (term173 a b).
Proof. exact (MK_COMB (@lem1978998 a b) (@lem1978996 a b)). Qed.
Lemma lem1979000 (a : real) (b : real) : (term174 a b) = (term175 a b).
Proof. exact (@lem1483533 a b). Qed.
Lemma lem1979013 (a : real) (b : real) : (real_sub a b) = (term141 a b).
Proof. exact (@lem1483519 a b). Qed.
Lemma lem1979014 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1979015 (a : real) (b : real) : (term176 a b) = (term168 a b).
Proof. exact (MK_COMB (@lem1979014) (@lem1979013 a b)). Qed.
Lemma lem1979016 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979017 (a : real) (b : real) : (term175 a b) = (term169 a b).
Proof. exact (MK_COMB (@lem1979015 a b) (@lem1979016)). Qed.
Lemma lem1979018 (a : real) (b : real) : (term174 a b) = (term169 a b).
Proof. exact (TRANS (@lem1979000 a b) (@lem1979017 a b)). Qed.
Lemma lem1979019 (b : real) (a : real) : (term139 b a) = (term177 b a).
Proof. exact (@lem1483523 (real_sub b a) term49). Qed.
Lemma lem1979020 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979026 (b : real) (a : real) : (real_sub b a) = (term141 b a).
Proof. exact (@lem1483519 b a). Qed.
Lemma lem1979031 (a : real) (b : real) : (term141 b a) = (term142 a b).
Proof. exact (@lem1483488 (term87 a) b). Qed.
Lemma lem1979033 (a : real) (b : real) : (real_sub b a) = (term142 a b).
Proof. exact (TRANS (@lem1979026 b a) (@lem1979031 a b)). Qed.
Lemma lem1979034 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1979035 (a : real) (b : real) : (term178 b a) = (term179 a b).
Proof. exact (MK_COMB (@lem1979034) (@lem1979033 a b)). Qed.
Lemma lem1979036 (a : real) (b : real) : (term180 b a) = (term181 a b).
Proof. exact (MK_COMB (@lem1979035 a b) (@lem1979020)). Qed.
Lemma lem1979037 (a : real) (b : real) : (term181 a b) = (term182 a b).
Proof. exact (@lem1483519 (term142 a b) term49). Qed.
Lemma lem1979039 (x : nat) : (term64 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1979040 : term65 = term49.
Proof. exact (@lem1979039 term66). Qed.
Lemma lem1979041 (a : real) (b : real) : (term183 a b) = (term183 a b).
Proof. exact (eq_refl (term183 a b)). Qed.
Lemma lem1979042 (a : real) (b : real) : (term182 a b) = (term184 a b).
Proof. exact (MK_COMB (@lem1979041 a b) (@lem1979040)). Qed.
Lemma lem1979043 (a : real) (b : real) : (term184 a b) = (term142 a b).
Proof. exact (@lem1483450 (term142 a b)). Qed.
Lemma lem1979044 (a : real) (b : real) : (term182 a b) = (term142 a b).
Proof. exact (TRANS (@lem1979042 a b) (@lem1979043 a b)). Qed.
Lemma lem1979045 (a : real) (b : real) : (term181 a b) = (term142 a b).
Proof. exact (TRANS (@lem1979037 a b) (@lem1979044 a b)). Qed.
Lemma lem1979046 (a : real) (b : real) : (term180 b a) = (term142 a b).
Proof. exact (TRANS (@lem1979036 a b) (@lem1979045 a b)). Qed.
Lemma lem1979047 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1979048 (a : real) (b : real) : (term185 b a) = (term144 a b).
Proof. exact (MK_COMB (@lem1979047) (@lem1979046 a b)). Qed.
Lemma lem1979049 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979050 (a : real) (b : real) : (term177 b a) = (term145 a b).
Proof. exact (MK_COMB (@lem1979048 a b) (@lem1979049)). Qed.
Lemma lem1979051 (a : real) (b : real) : (term139 b a) = (term145 a b).
Proof. exact (TRANS (@lem1979019 b a) (@lem1979050 a b)). Qed.
Lemma lem1979052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979053 (a : real) (b : real) : (term186 a b) = (term187 a b).
Proof. exact (MK_COMB (@lem1979052) (@lem1979018 a b)). Qed.
Lemma lem1979054 (a : real) (b : real) : (term188 b a) = (term189 a b).
Proof. exact (MK_COMB (@lem1979053 a b) (@lem1979051 a b)). Qed.
Lemma lem1979055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1979056 (a : real) (b : real) : (term190 b a) = (term191 a b).
Proof. exact (MK_COMB (@lem1979055) (@lem1978999 a b)). Qed.
Lemma lem1979057 (a : real) (b : real) : (term138 b a) = (term192 a b).
Proof. exact (MK_COMB (@lem1979056 a b) (@lem1979054 a b)). Qed.
Lemma lem1979082 (a : real) (b : real) : (term137 b a) = (term192 a b).
Proof. exact (TRANS (@lem1978925 b a) (@lem1979057 a b)). Qed.
Lemma lem1979092 (a : real) (b : real) (h1 : term192 a b) : term192 a b.
Proof. exact (h1). Qed.
Lemma lem1979093 (a : real) (b : real) (h1 : term173 a b) : term173 a b.
Proof. exact (h1). Qed.
Lemma lem1979094 (a : real) (b : real) (h1 : term173 a b) : term169 a b.
Proof. exact (proj2 (@lem1979093 a b h1)). Qed.
Lemma lem1979095 (a : real) (b : real) (h1 : term173 a b) : term145 a b.
Proof. exact (proj1 (@lem1979093 a b h1)). Qed.
Lemma lem1979097 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979098 : term74 = term75.
Proof. exact (@lem1979097 (NUMERAL 0) term66). Qed.
Lemma lem1979099 : term76 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1979100 (h1 : term76 = (BIT1 0)) : term75 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1979101 : (term76 = (BIT1 0)) = (term75 = True).
Proof. exact (prop_ext (fun h1 : term76 = (BIT1 0) => @lem1979100 h1) (fun h1 : term75 = True => @lem1979099)). Qed.
Lemma lem1979102 : term75 = True.
Proof. exact (EQ_MP (@lem1979101) (@lem1979099)). Qed.
Lemma lem1979103 : term74 = True.
Proof. exact (TRANS (@lem1979098) (@lem1979102)). Qed.
Lemma lem1979104 : True = term74.
Proof. exact (SYM (@lem1979103)). Qed.
Lemma lem1979105 : term74.
Proof. exact (EQ_MP (@lem1979104) (@lem0)). Qed.
Lemma lem1979106 (a : real) (b : real) (h1 : term173 a b) : term193 a b.
Proof. exact (conj (@lem1979105) (@lem1979095 a b h1)). Qed.
Lemma lem1979108 (x : real) (y : real) : term194 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1979109 (a : real) (b : real) : term195 a b.
Proof. exact (@lem1979108 term21 (term142 a b)). Qed.
Lemma lem1979110 (a : real) (b : real) (h1 : term173 a b) : term196 a b.
Proof. exact (@lem1979109 a b (@lem1979106 a b h1)). Qed.
Lemma lem1979111 (a : real) (b : real) : (term197 a b) = (term142 a b).
Proof. exact (@lem1483460 (term142 a b)). Qed.
Lemma lem1979112 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1979113 (a : real) (b : real) : (term198 a b) = (term144 a b).
Proof. exact (MK_COMB (@lem1979112) (@lem1979111 a b)). Qed.
Lemma lem1979114 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979115 (a : real) (b : real) : (term196 a b) = (term145 a b).
Proof. exact (MK_COMB (@lem1979113 a b) (@lem1979114)). Qed.
Lemma lem1979116 (a : real) (b : real) (h1 : term173 a b) : term145 a b.
Proof. exact (EQ_MP (@lem1979115 a b) (@lem1979110 a b h1)). Qed.
Lemma lem1979118 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979119 : term74 = term75.
Proof. exact (@lem1979118 (NUMERAL 0) term66). Qed.
Lemma lem1979120 : term76 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1979121 (h1 : term76 = (BIT1 0)) : term75 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1979122 : (term76 = (BIT1 0)) = (term75 = True).
Proof. exact (prop_ext (fun h1 : term76 = (BIT1 0) => @lem1979121 h1) (fun h1 : term75 = True => @lem1979120)). Qed.
Lemma lem1979123 : term75 = True.
Proof. exact (EQ_MP (@lem1979122) (@lem1979120)). Qed.
Lemma lem1979124 : term74 = True.
Proof. exact (TRANS (@lem1979119) (@lem1979123)). Qed.
Lemma lem1979125 : True = term74.
Proof. exact (SYM (@lem1979124)). Qed.
Lemma lem1979126 : term74.
Proof. exact (EQ_MP (@lem1979125) (@lem0)). Qed.
Lemma lem1979127 (a : real) (b : real) (h1 : term173 a b) : term199 a b.
Proof. exact (conj (@lem1979126) (@lem1979094 a b h1)). Qed.
Lemma lem1979129 (x : real) (y : real) : term78 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1979130 (a : real) (b : real) : term200 a b.
Proof. exact (@lem1979129 term21 (term141 a b)). Qed.
Lemma lem1979131 (a : real) (b : real) (h1 : term173 a b) : term201 a b.
Proof. exact (@lem1979130 a b (@lem1979127 a b h1)). Qed.
Lemma lem1979132 (a : real) (b : real) : (term202 a b) = (term141 a b).
Proof. exact (@lem1483460 (term141 a b)). Qed.
Lemma lem1979133 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1979134 (a : real) (b : real) : (term203 a b) = (term168 a b).
Proof. exact (MK_COMB (@lem1979133) (@lem1979132 a b)). Qed.
Lemma lem1979135 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979136 (a : real) (b : real) : (term201 a b) = (term169 a b).
Proof. exact (MK_COMB (@lem1979134 a b) (@lem1979135)). Qed.
Lemma lem1979137 (a : real) (b : real) (h1 : term173 a b) : term169 a b.
Proof. exact (EQ_MP (@lem1979136 a b) (@lem1979131 a b h1)). Qed.
Lemma lem1979138 (a : real) (b : real) (h1 : term173 a b) : term189 a b.
Proof. exact (conj (@lem1979137 a b h1) (@lem1979116 a b h1)). Qed.
Lemma lem1979140 (x : real) (y : real) : term204 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1979141 (a : real) (b : real) : term205 a b.
Proof. exact (@lem1979140 (term141 a b) (term142 a b)). Qed.
Lemma lem1979142 (a : real) (b : real) (h1 : term173 a b) : term206 a b.
Proof. exact (@lem1979141 a b (@lem1979138 a b h1)). Qed.
Lemma lem1979143 (a : real) (b : real) : (term207 a b) = (term208 a b).
Proof. exact (@lem1483480 a (term87 a) (term87 b) b). Qed.
Lemma lem1979144 (a : real) : (term209 a) = (term93 a).
Proof. exact (@lem1483442 term86 a). Qed.
Lemma lem1979146 (m : nat) : (term94 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1979147 : term95 = term49.
Proof. exact (@lem1979146 term66). Qed.
Lemma lem1979148 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1979149 : term96 = term97.
Proof. exact (MK_COMB (@lem1979148) (@lem1979147)). Qed.
Lemma lem1979150 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1979151 (a : real) : (term93 a) = (term98 a).
Proof. exact (MK_COMB (@lem1979149) (@lem1979150 a)). Qed.
Lemma lem1979152 (a : real) : (term209 a) = (term98 a).
Proof. exact (TRANS (@lem1979144 a) (@lem1979151 a)). Qed.
Lemma lem1979153 (a : real) : (term98 a) = term49.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1979154 (a : real) : (term209 a) = term49.
Proof. exact (TRANS (@lem1979152 a) (@lem1979153 a)). Qed.
Lemma lem1979155 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1979156 (a : real) : (term210 a) = term165.
Proof. exact (MK_COMB (@lem1979155) (@lem1979154 a)). Qed.
Lemma lem1979157 (b : real) : (term92 b) = (term93 b).
Proof. exact (@lem1483440 term86 b). Qed.
Lemma lem1979159 (m : nat) : (term94 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1979160 : term95 = term49.
Proof. exact (@lem1979159 term66). Qed.
Lemma lem1979161 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1979162 : term96 = term97.
Proof. exact (MK_COMB (@lem1979161) (@lem1979160)). Qed.
Lemma lem1979163 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1979164 (b : real) : (term93 b) = (term98 b).
Proof. exact (MK_COMB (@lem1979162) (@lem1979163 b)). Qed.
Lemma lem1979165 (b : real) : (term92 b) = (term98 b).
Proof. exact (TRANS (@lem1979157 b) (@lem1979164 b)). Qed.
Lemma lem1979166 (b : real) : (term98 b) = term49.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1979167 (b : real) : (term92 b) = term49.
Proof. exact (TRANS (@lem1979165 b) (@lem1979166 b)). Qed.
Lemma lem1979168 (a : real) (b : real) : (term208 a b) = term211.
Proof. exact (MK_COMB (@lem1979156 a) (@lem1979167 b)). Qed.
Lemma lem1979169 (a : real) (b : real) : (term207 a b) = term211.
Proof. exact (TRANS (@lem1979143 a b) (@lem1979168 a b)). Qed.
Lemma lem1979170 : term211 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1979171 (a : real) (b : real) : (term207 a b) = term49.
Proof. exact (TRANS (@lem1979169 a b) (@lem1979170)). Qed.
Lemma lem1979172 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1979173 (a : real) (b : real) : (term212 a b) = term100.
Proof. exact (MK_COMB (@lem1979172) (@lem1979171 a b)). Qed.
Lemma lem1979174 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979175 (a : real) (b : real) : (term206 a b) = term101.
Proof. exact (MK_COMB (@lem1979173 a b) (@lem1979174)). Qed.
Lemma lem1979176 (a : real) (b : real) (h1 : term173 a b) : term101.
Proof. exact (EQ_MP (@lem1979175 a b) (@lem1979142 a b h1)). Qed.
Lemma lem1979178 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979179 : term101 = term102.
Proof. exact (@lem1979178 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1979180 : term102 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1979181 : term101 = False.
Proof. exact (TRANS (@lem1979179) (@lem1979180)). Qed.
Lemma lem1979182 (a : real) (b : real) (h1 : term173 a b) : False.
Proof. exact (EQ_MP (@lem1979181) (@lem1979176 a b h1)). Qed.
Lemma lem1979183 (a : real) (b : real) (h1 : term189 a b) : term189 a b.
Proof. exact (h1). Qed.
Lemma lem1979184 (a : real) (b : real) (h1 : term189 a b) : term145 a b.
Proof. exact (proj2 (@lem1979183 a b h1)). Qed.
Lemma lem1979185 (a : real) (b : real) (h1 : term189 a b) : term169 a b.
Proof. exact (proj1 (@lem1979183 a b h1)). Qed.
Lemma lem1979187 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979188 : term74 = term75.
Proof. exact (@lem1979187 (NUMERAL 0) term66). Qed.
Lemma lem1979189 : term76 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1979190 (h1 : term76 = (BIT1 0)) : term75 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1979191 : (term76 = (BIT1 0)) = (term75 = True).
Proof. exact (prop_ext (fun h1 : term76 = (BIT1 0) => @lem1979190 h1) (fun h1 : term75 = True => @lem1979189)). Qed.
Lemma lem1979192 : term75 = True.
Proof. exact (EQ_MP (@lem1979191) (@lem1979189)). Qed.
Lemma lem1979193 : term74 = True.
Proof. exact (TRANS (@lem1979188) (@lem1979192)). Qed.
Lemma lem1979194 : True = term74.
Proof. exact (SYM (@lem1979193)). Qed.
Lemma lem1979195 : term74.
Proof. exact (EQ_MP (@lem1979194) (@lem0)). Qed.
Lemma lem1979196 (a : real) (b : real) (h1 : term189 a b) : term193 a b.
Proof. exact (conj (@lem1979195) (@lem1979184 a b h1)). Qed.
Lemma lem1979198 (x : real) (y : real) : term194 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1979199 (a : real) (b : real) : term195 a b.
Proof. exact (@lem1979198 term21 (term142 a b)). Qed.
Lemma lem1979200 (a : real) (b : real) (h1 : term189 a b) : term196 a b.
Proof. exact (@lem1979199 a b (@lem1979196 a b h1)). Qed.
Lemma lem1979201 (a : real) (b : real) : (term197 a b) = (term142 a b).
Proof. exact (@lem1483460 (term142 a b)). Qed.
Lemma lem1979202 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1979203 (a : real) (b : real) : (term198 a b) = (term144 a b).
Proof. exact (MK_COMB (@lem1979202) (@lem1979201 a b)). Qed.
Lemma lem1979204 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979205 (a : real) (b : real) : (term196 a b) = (term145 a b).
Proof. exact (MK_COMB (@lem1979203 a b) (@lem1979204)). Qed.
Lemma lem1979206 (a : real) (b : real) (h1 : term189 a b) : term145 a b.
Proof. exact (EQ_MP (@lem1979205 a b) (@lem1979200 a b h1)). Qed.
Lemma lem1979208 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979209 : term74 = term75.
Proof. exact (@lem1979208 (NUMERAL 0) term66). Qed.
Lemma lem1979210 : term76 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1979211 (h1 : term76 = (BIT1 0)) : term75 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1979212 : (term76 = (BIT1 0)) = (term75 = True).
Proof. exact (prop_ext (fun h1 : term76 = (BIT1 0) => @lem1979211 h1) (fun h1 : term75 = True => @lem1979210)). Qed.
Lemma lem1979213 : term75 = True.
Proof. exact (EQ_MP (@lem1979212) (@lem1979210)). Qed.
Lemma lem1979214 : term74 = True.
Proof. exact (TRANS (@lem1979209) (@lem1979213)). Qed.
Lemma lem1979215 : True = term74.
Proof. exact (SYM (@lem1979214)). Qed.
Lemma lem1979216 : term74.
Proof. exact (EQ_MP (@lem1979215) (@lem0)). Qed.
Lemma lem1979217 (a : real) (b : real) (h1 : term189 a b) : term199 a b.
Proof. exact (conj (@lem1979216) (@lem1979185 a b h1)). Qed.
Lemma lem1979219 (x : real) (y : real) : term78 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1979220 (a : real) (b : real) : term200 a b.
Proof. exact (@lem1979219 term21 (term141 a b)). Qed.
Lemma lem1979221 (a : real) (b : real) (h1 : term189 a b) : term201 a b.
Proof. exact (@lem1979220 a b (@lem1979217 a b h1)). Qed.
Lemma lem1979222 (a : real) (b : real) : (term202 a b) = (term141 a b).
Proof. exact (@lem1483460 (term141 a b)). Qed.
Lemma lem1979223 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1979224 (a : real) (b : real) : (term203 a b) = (term168 a b).
Proof. exact (MK_COMB (@lem1979223) (@lem1979222 a b)). Qed.
Lemma lem1979225 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979226 (a : real) (b : real) : (term201 a b) = (term169 a b).
Proof. exact (MK_COMB (@lem1979224 a b) (@lem1979225)). Qed.
Lemma lem1979227 (a : real) (b : real) (h1 : term189 a b) : term169 a b.
Proof. exact (EQ_MP (@lem1979226 a b) (@lem1979221 a b h1)). Qed.
Lemma lem1979228 (a : real) (b : real) (h1 : term189 a b) : term189 a b.
Proof. exact (conj (@lem1979227 a b h1) (@lem1979206 a b h1)). Qed.
Lemma lem1979230 (x : real) (y : real) : term204 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1979231 (a : real) (b : real) : term205 a b.
Proof. exact (@lem1979230 (term141 a b) (term142 a b)). Qed.
Lemma lem1979232 (a : real) (b : real) (h1 : term189 a b) : term206 a b.
Proof. exact (@lem1979231 a b (@lem1979228 a b h1)). Qed.
Lemma lem1979233 (a : real) (b : real) : (term207 a b) = (term208 a b).
Proof. exact (@lem1483480 a (term87 a) (term87 b) b). Qed.
Lemma lem1979234 (a : real) : (term209 a) = (term93 a).
Proof. exact (@lem1483442 term86 a). Qed.
Lemma lem1979236 (m : nat) : (term94 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1979237 : term95 = term49.
Proof. exact (@lem1979236 term66). Qed.
Lemma lem1979238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1979239 : term96 = term97.
Proof. exact (MK_COMB (@lem1979238) (@lem1979237)). Qed.
Lemma lem1979240 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1979241 (a : real) : (term93 a) = (term98 a).
Proof. exact (MK_COMB (@lem1979239) (@lem1979240 a)). Qed.
Lemma lem1979242 (a : real) : (term209 a) = (term98 a).
Proof. exact (TRANS (@lem1979234 a) (@lem1979241 a)). Qed.
Lemma lem1979243 (a : real) : (term98 a) = term49.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1979244 (a : real) : (term209 a) = term49.
Proof. exact (TRANS (@lem1979242 a) (@lem1979243 a)). Qed.
Lemma lem1979245 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1979246 (a : real) : (term210 a) = term165.
Proof. exact (MK_COMB (@lem1979245) (@lem1979244 a)). Qed.
Lemma lem1979247 (b : real) : (term92 b) = (term93 b).
Proof. exact (@lem1483440 term86 b). Qed.
Lemma lem1979249 (m : nat) : (term94 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1979250 : term95 = term49.
Proof. exact (@lem1979249 term66). Qed.
Lemma lem1979251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1979252 : term96 = term97.
Proof. exact (MK_COMB (@lem1979251) (@lem1979250)). Qed.
Lemma lem1979253 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1979254 (b : real) : (term93 b) = (term98 b).
Proof. exact (MK_COMB (@lem1979252) (@lem1979253 b)). Qed.
Lemma lem1979255 (b : real) : (term92 b) = (term98 b).
Proof. exact (TRANS (@lem1979247 b) (@lem1979254 b)). Qed.
Lemma lem1979256 (b : real) : (term98 b) = term49.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1979257 (b : real) : (term92 b) = term49.
Proof. exact (TRANS (@lem1979255 b) (@lem1979256 b)). Qed.
Lemma lem1979258 (a : real) (b : real) : (term208 a b) = term211.
Proof. exact (MK_COMB (@lem1979246 a) (@lem1979257 b)). Qed.
Lemma lem1979259 (a : real) (b : real) : (term207 a b) = term211.
Proof. exact (TRANS (@lem1979233 a b) (@lem1979258 a b)). Qed.
Lemma lem1979260 : term211 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1979261 (a : real) (b : real) : (term207 a b) = term49.
Proof. exact (TRANS (@lem1979259 a b) (@lem1979260)). Qed.
Lemma lem1979262 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1979263 (a : real) (b : real) : (term212 a b) = term100.
Proof. exact (MK_COMB (@lem1979262) (@lem1979261 a b)). Qed.
Lemma lem1979264 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1979265 (a : real) (b : real) : (term206 a b) = term101.
Proof. exact (MK_COMB (@lem1979263 a b) (@lem1979264)). Qed.
Lemma lem1979266 (a : real) (b : real) (h1 : term189 a b) : term101.
Proof. exact (EQ_MP (@lem1979265 a b) (@lem1979232 a b h1)). Qed.
Lemma lem1979268 (n : nat) (m : nat) : (term73 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1979269 : term101 = term102.
Proof. exact (@lem1979268 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1979270 : term102 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1979271 : term101 = False.
Proof. exact (TRANS (@lem1979269) (@lem1979270)). Qed.
Lemma lem1979272 (a : real) (b : real) (h1 : term189 a b) : False.
Proof. exact (EQ_MP (@lem1979271) (@lem1979266 a b h1)). Qed.
Lemma lem1979273 (a : real) (b : real) (h1 : term192 a b) : False.
Proof. exact (or_elim (@lem1979092 a b h1) (fun h0 : term173 a b => @lem1979182 a b h0) (fun h0 : term189 a b => @lem1979272 a b h0)). Qed.
Lemma lem1979275 (a : real) (b : real) (h1 : term192 a b) : term192 a b.
Proof. exact (h1). Qed.
Lemma lem1979276 (a : real) (b : real) (h1 : term192 a b) : (term192 a b) = False.
Proof. exact (prop_ext (fun h2 : term192 a b => @lem1979273 a b h1) (fun h2 : False => @lem1979275 a b h1)). Qed.
Lemma lem1979277 (a : real) (b : real) (h1 : term192 a b) : False.
Proof. exact (EQ_MP (@lem1979276 a b h1) (@lem1979275 a b h1)). Qed.
Lemma lem1979278 (b : real) (a : real) (h1 : term137 b a) : term137 b a.
Proof. exact (h1). Qed.
Lemma lem1979279 (b : real) (a : real) (h1 : term137 b a) : term192 a b.
Proof. exact (EQ_MP (@lem1979082 a b) (@lem1979278 b a h1)). Qed.
Lemma lem1979280 (b : real) (a : real) (h1 : term137 b a) : (term192 a b) = False.
Proof. exact (prop_ext (fun h2 : term192 a b => @lem1979277 a b h2) (fun h2 : False => @lem1979279 b a h1)). Qed.
Lemma lem1979281 (b : real) (a : real) (h1 : term137 b a) : False.
Proof. exact (EQ_MP (@lem1979280 b a h1) (@lem1979279 b a h1)). Qed.
Lemma lem1979282 (b : real) (a : real) : term213 b a.
Proof. exact (fun h0 : term137 b a => @lem1979281 b a h0). Qed.
Lemma lem1979283 (b : real) (a : real) : term214 b a.
Proof. exact (@lem1386578 ((real_le a b) = (term139 b a))). Qed.
Lemma lem1979285 (t1 : Prop) : term215 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem1979286 (t1 : Prop) : (term215 t1) = (term216 t1).
Proof. exact (eq_refl (term215 t1)). Qed.
Lemma lem1979287 (t1 : Prop) : term216 t1.
Proof. exact (EQ_MP (@lem1979286 t1) (@lem1979285 t1)). Qed.
Lemma lem1979288 (t1 : Prop) (t2 : Prop) : term217 t1 t2.
Proof. exact (@lem1979287 t1 t2). Qed.
Lemma lem1979289 (t2 : Prop) (t1 : Prop) : (term217 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term217 t1 t2)). Qed.
Lemma lem1979296 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem1979289 t2 t1) (@lem1979288 t1 t2)). Qed.
Lemma lem1979297 (y2 : real) (y1 : real) : (term218 y1 y2) = (term218 y2 y1).
Proof. exact (@lem1979296 (term38 y2) (term38 y1)). Qed.
Lemma lem1979298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1979299 (y2 : real) (y1 : real) : (term219 y1 y2) = (term219 y2 y1).
Proof. exact (MK_COMB (@lem1979298) (@lem1979297 y2 y1)). Qed.
Lemma lem1979302 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : ((term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1)) = ((term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1)).
Proof. exact (eq_refl ((term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1))). Qed.
Lemma lem1979303 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term222 x1 y2 x2 y1) = (term223 x1 y2 x2 y1).
Proof. exact (MK_COMB (@lem1979299 y2 y1) (@lem1979302 x1 y2 x2 y1)). Qed.
Lemma lem1979304 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term223 x1 y2 x2 y1) = (term222 x1 y2 x2 y1).
Proof. exact (SYM (@lem1979303 x1 y2 x2 y1)). Qed.
Lemma lem1979305 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term218 y2 y1.
Proof. exact (h1). Qed.
Lemma lem1979309 (b : real) (a : real) : (real_le a b) = (term139 b a).
Proof. exact (@lem1979283 b a (@lem1979282 b a)). Qed.
Lemma lem1979310 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : (term220 x1 y1 x2 y2) = (term224 x2 y2 x1 y1).
Proof. exact (@lem1979309 (real_div x2 y2) (real_div x1 y1)). Qed.
Lemma lem1979311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979312 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : (term225 x1 y1 x2 y2) = (term226 x2 y2 x1 y1).
Proof. exact (MK_COMB (@lem1979311) (@lem1979310 x2 y2 x1 y1)). Qed.
Lemma lem1979314 (b : real) (a : real) : (real_le a b) = (term139 b a).
Proof. exact (@lem1979283 b a (@lem1979282 b a)). Qed.
Lemma lem1979315 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term221 x1 y2 x2 y1) = (term227 x2 y1 x1 y2).
Proof. exact (@lem1979314 (real_mul x2 y1) (real_mul x1 y2)). Qed.
Lemma lem1979316 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1)) = ((term224 x2 y2 x1 y1) = (term227 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1979312 x2 y2 x1 y1) (@lem1979315 x2 y1 x1 y2)). Qed.
Lemma lem1979317 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : ((term224 x2 y2 x1 y1) = (term227 x2 y1 x1 y2)) = ((term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1)).
Proof. exact (SYM (@lem1979316 x2 y1 x1 y2)). Qed.
Lemma lem1979319 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term228 x1 x2 y1 y2.
Proof. exact (fun h0 : term218 y1 y2 => @lem1978411 x1 x2 y1 y2 h0). Qed.
Lemma lem1979320 (x1 : real) (x2 : real) (y2 : real) (y1 : real) : term228 x1 x2 y2 y1.
Proof. exact (@lem1979319 x1 x2 y2 y1). Qed.
Lemma lem1979325 (x1 : real) (x2 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term229 x1 y2 x2 y1) = (term230 x1 x2 y2 y1).
Proof. exact (@lem1979320 x1 x2 y2 y1 (@lem1979305 y2 y1 h1)). Qed.
Lemma lem1979326 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term229 x2 y2 x1 y1) = (term230 x2 x1 y2 y1).
Proof. exact (@lem1979325 x2 x1 y2 y1 h1). Qed.
Lemma lem1979327 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1979328 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term224 x2 y2 x1 y1) = (term231 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1979327) (@lem1979326 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979330 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term226 x2 y2 x1 y1) = (term232 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1979329) (@lem1979328 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979331 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term227 x2 y1 x1 y2) = (term227 x2 y1 x1 y2).
Proof. exact (eq_refl (term227 x2 y1 x1 y2)). Qed.
Lemma lem1979332 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : ((term224 x2 y2 x1 y1) = (term227 x2 y1 x1 y2)) = ((term231 x2 x1 y2 y1) = (term227 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1979330 x2 x1 y2 y1 h1) (@lem1979331 x2 y1 x1 y2)). Qed.
Lemma lem1979335 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : ((term231 x2 x1 y2 y1) = (term227 x2 y1 x1 y2)) = ((term224 x2 y2 x1 y1) = (term227 x2 y1 x1 y2)).
Proof. exact (SYM (@lem1979332 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979337 {A : Type'} (x : A) (z : A) : term131 A x z.
Proof. exact (EQ_MP (@lem1978887 A x z) (@lem1978886 A x z)). Qed.
Lemma lem1979338 (x : Prop) (z : Prop) : term233 x z.
Proof. exact (@lem1979337 Prop x z). Qed.
Lemma lem1979339 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term234 x2 y1 x1 y2.
Proof. exact (@lem1979338 (term231 x2 x1 y2 y1) (term227 x2 y1 x1 y2)). Qed.
Lemma lem1979345 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (EQ_MP (@lem1978859 x y z) (@lem1978858 x y z)). Qed.
Lemma lem1979346 (x2 : real) (x1 : real) (y2 : real) (y1 : real) : (term230 x2 x1 y2 y1) = (term235 x2 x1 y2 y1).
Proof. exact (@lem1979345 (term236 x2 y1 x1 y2) (real_inv y2) (real_inv y1)). Qed.
Lemma lem1979347 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1979348 (x2 : real) (x1 : real) (y2 : real) (y1 : real) : (term231 x2 x1 y2 y1) = (term237 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1979347) (@lem1979346 x2 x1 y2 y1)). Qed.
Lemma lem1979349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1979350 (x2 : real) (x1 : real) (y2 : real) (y1 : real) : (term232 x2 x1 y2 y1) = (term238 x2 x1 y2 y1).
Proof. exact (MK_COMB (@lem1979349) (@lem1979348 x2 x1 y2 y1)). Qed.
Lemma lem1979351 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term239 x2 y1 x1 y2) = (term239 x2 y1 x1 y2).
Proof. exact (eq_refl (term239 x2 y1 x1 y2)). Qed.
Lemma lem1979352 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term231 x2 x1 y2 y1) = (term239 x2 y1 x1 y2)) = ((term237 x2 x1 y2 y1) = (term239 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1979350 x2 x1 y2 y1) (@lem1979351 x2 y1 x1 y2)). Qed.
Lemma lem1979355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979356 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term240 x2 y1 x1 y2) = (term241 x2 y1 x1 y2).
Proof. exact (MK_COMB (@lem1979355) (@lem1979352 x2 y1 x1 y2)). Qed.
Lemma lem1979359 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term239 x2 y1 x1 y2) = (term227 x2 y1 x1 y2)) = ((term239 x2 y1 x1 y2) = (term227 x2 y1 x1 y2)).
Proof. exact (eq_refl ((term239 x2 y1 x1 y2) = (term227 x2 y1 x1 y2))). Qed.
Lemma lem1979360 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term242 x2 y1 x1 y2) = (term243 x2 y1 x1 y2).
Proof. exact (MK_COMB (@lem1979356 x2 y1 x1 y2) (@lem1979359 x2 y1 x1 y2)). Qed.
Lemma lem1979363 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term243 x2 y1 x1 y2) = (term242 x2 y1 x1 y2).
Proof. exact (SYM (@lem1979360 x2 y1 x1 y2)). Qed.
Lemma lem1979365 (y : real) (x : real) : term111 y x.
Proof. exact (@lem1978850 y x (@lem1978826 y x)). Qed.
Lemma lem1979366 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term244 x2 y1 x1 y2.
Proof. exact (@lem1979365 (real_inv y1) (term245 x2 y1 x1 y2)). Qed.
Lemma lem1979368 (y : real) (x : real) : term111 y x.
Proof. exact (@lem1978850 y x (@lem1978826 y x)). Qed.
Lemma lem1979369 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term246 x2 y1 x1 y2.
Proof. exact (@lem1979368 (real_inv y2) (term236 x2 y1 x1 y2)). Qed.
Lemma lem1979371 (x : real) : term114 x.
Proof. exact (EQ_MP (@lem1978841 x) (@lem1978840 x)). Qed.
Lemma lem1979372 (y1 : real) : term114 y1.
Proof. exact (@lem1979371 y1). Qed.
Lemma lem1979374 (x : real) : term114 x.
Proof. exact (EQ_MP (@lem1978841 x) (@lem1978840 x)). Qed.
Lemma lem1979375 (y2 : real) : term114 y2.
Proof. exact (@lem1979374 y2). Qed.
Lemma lem1979376 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term38 y1.
Proof. exact (proj2 (@lem1979305 y2 y1 h1)). Qed.
Lemma lem1979377 (y1 : real) : (term38 y1) = ((term38 y1) = True).
Proof. exact (@lem7 (term38 y1)). Qed.
Lemma lem1979383 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term38 y1) = True.
Proof. exact (EQ_MP (@lem1979377 y1) (@lem1979376 y2 y1 h1)). Qed.
Lemma lem1979384 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : True = (term38 y1).
Proof. exact (SYM (@lem1979383 y2 y1 h1)). Qed.
Lemma lem1979385 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term38 y1.
Proof. exact (EQ_MP (@lem1979384 y2 y1 h1) (@lem0)). Qed.
Lemma lem1979389 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term38 y2.
Proof. exact (proj1 (@lem1979305 y2 y1 h1)). Qed.
Lemma lem1979390 (y2 : real) : (term38 y2) = ((term38 y2) = True).
Proof. exact (@lem7 (term38 y2)). Qed.
Lemma lem1979393 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term38 y2) = True.
Proof. exact (EQ_MP (@lem1979390 y2) (@lem1979389 y2 y1 h1)). Qed.
Lemma lem1979394 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : True = (term38 y2).
Proof. exact (SYM (@lem1979393 y2 y1 h1)). Qed.
Lemma lem1979395 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term38 y2.
Proof. exact (EQ_MP (@lem1979394 y2 y1 h1) (@lem0)). Qed.
Lemma lem1979396 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term115 y2.
Proof. exact (@lem1979375 y2 (@lem1979395 y2 y1 h1)). Qed.
Lemma lem1979397 (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term115 y1.
Proof. exact (@lem1979372 y1 (@lem1979385 y2 y1 h1)). Qed.
Lemma lem1979398 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term239 x2 y1 x1 y2) = (term227 x2 y1 x1 y2).
Proof. exact (@lem1979369 x2 y1 x1 y2 (@lem1979396 y2 y1 h1)). Qed.
Lemma lem1979399 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term237 x2 x1 y2 y1) = (term239 x2 y1 x1 y2).
Proof. exact (@lem1979366 x2 y1 x1 y2 (@lem1979397 y2 y1 h1)). Qed.
Lemma lem1979400 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term243 x2 y1 x1 y2.
Proof. exact (conj (@lem1979399 x2 x1 y2 y1 h1) (@lem1979398 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979401 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term242 x2 y1 x1 y2.
Proof. exact (EQ_MP (@lem1979363 x2 y1 x1 y2) (@lem1979400 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979402 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : term247 x2 y1 x1 y2.
Proof. exact (ex_intro (term248 x2 y1 x1 y2) (term239 x2 y1 x1 y2) (@lem1979401 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979403 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term231 x2 x1 y2 y1) = (term227 x2 y1 x1 y2).
Proof. exact (@lem1979339 x2 y1 x1 y2 (@lem1979402 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979404 (x2 : real) (x1 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term224 x2 y2 x1 y1) = (term227 x2 y1 x1 y2).
Proof. exact (EQ_MP (@lem1979335 x2 x1 y2 y1 h1) (@lem1979403 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979405 (x1 : real) (x2 : real) (y2 : real) (y1 : real) (h1 : term218 y2 y1) : (term220 x1 y1 x2 y2) = (term221 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1979317 x1 y2 x2 y1) (@lem1979404 x2 x1 y2 y1 h1)). Qed.
Lemma lem1979406 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term223 x1 y2 x2 y1.
Proof. exact (fun h0 : term218 y2 y1 => @lem1979405 x1 x2 y2 y1 h0). Qed.
Lemma lem1979407 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term222 x1 y2 x2 y1.
Proof. exact (EQ_MP (@lem1979304 x1 y2 x2 y1) (@lem1979406 x1 y2 x2 y1)). Qed.

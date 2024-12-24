Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SOS_EQ_0_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POW_2_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1338512_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483486_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483572_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1647412 (x : real) : term0 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1647413 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1647414 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1647413 x) (@lem1647412 x)). Qed.
Lemma lem1647415 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1647414 x y). Qed.
Lemma lem1647416 (x : real) (y : real) : (term2 x y) = (((real_mul x y) = term3) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1647418 (x : real) : term5 x.
Proof. exact (@lem1382902 x). Qed.
Lemma lem1647419 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1647420 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1647419 x) (@lem1647418 x)). Qed.
Lemma lem1647421 (x : real) : (term6 x) = ((term6 x) = True).
Proof. exact (@lem7 (term6 x)). Qed.
Lemma lem1647446 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (@lem17045 (x = term3) (y = term3)). Qed.
Lemma lem1647448 (x : real) (y : real) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1647449 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1647448 x y) (@lem1647446 x y)). Qed.
Lemma lem1647450 (x : real) (y : real) : (term12 x y) = (term10 x y).
Proof. exact (@lem17362 (term13 x y) (term14 x y)). Qed.
Lemma lem1647451 (x : real) (y : real) : (term12 x y) = (term11 x y).
Proof. exact (TRANS (@lem1647450 x y) (@lem1647449 x y)). Qed.
Lemma lem1647453 (x : real) (y : real) : (term15 x y) = (term15 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1647454 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1647453 x y) (@lem1647451 x y)). Qed.
Lemma lem1647455 (x : real) (y : real) : (term18 x y) = (term16 x y).
Proof. exact (@lem17362 ((real_add x y) = term3) (term19 x y)). Qed.
Lemma lem1647479 (x : real) (y : real) : (term18 x y) = (term17 x y).
Proof. exact (TRANS (@lem1647455 x y) (@lem1647454 x y)). Qed.
Lemma lem1647480 (x : real) (y : real) : ((real_add x y) = term3) = ((term20 x y) = term3).
Proof. exact (@lem1483529 (real_add x y) term3). Qed.
Lemma lem1647492 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (@lem1483519 (real_add x y) term3). Qed.
Lemma lem1647494 (x : nat) : (term22 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1647495 : term23 = term3.
Proof. exact (@lem1647494 term24). Qed.
Lemma lem1647496 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1647497 (x : real) (y : real) : (term21 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1647496 x y) (@lem1647495)). Qed.
Lemma lem1647498 (x : real) (y : real) : (term26 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1647499 (x : real) (y : real) : (term21 x y) = (real_add x y).
Proof. exact (TRANS (@lem1647497 x y) (@lem1647498 x y)). Qed.
Lemma lem1647501 (x : real) (y : real) : (term20 x y) = (real_add x y).
Proof. exact (TRANS (@lem1647492 x y) (@lem1647499 x y)). Qed.
Lemma lem1647502 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1647503 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1647502) (@lem1647501 x y)). Qed.
Lemma lem1647504 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647505 (x : real) (y : real) : ((term20 x y) = term3) = ((real_add x y) = term3).
Proof. exact (MK_COMB (@lem1647503 x y) (@lem1647504)). Qed.
Lemma lem1647506 (x : real) (y : real) : ((real_add x y) = term3) = ((real_add x y) = term3).
Proof. exact (TRANS (@lem1647480 x y) (@lem1647505 x y)). Qed.
Lemma lem1647507 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483523 x term3). Qed.
Lemma lem1647513 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1483519 x term3). Qed.
Lemma lem1647515 (x : nat) : (term22 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1647516 : term23 = term3.
Proof. exact (@lem1647515 term24). Qed.
Lemma lem1647517 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1647518 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1647517 x) (@lem1647516)). Qed.
Lemma lem1647519 (x : real) : (term33 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1647520 (x : real) : (term32 x) = x.
Proof. exact (TRANS (@lem1647518 x) (@lem1647519 x)). Qed.
Lemma lem1647522 (x : real) : (term31 x) = x.
Proof. exact (TRANS (@lem1647513 x) (@lem1647520 x)). Qed.
Lemma lem1647523 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647524 (x : real) : (term34 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1647523) (@lem1647522 x)). Qed.
Lemma lem1647525 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647526 (x : real) : (term30 x) = (term35 x).
Proof. exact (MK_COMB (@lem1647524 x) (@lem1647525)). Qed.
Lemma lem1647527 (x : real) : (term29 x) = (term35 x).
Proof. exact (TRANS (@lem1647507 x) (@lem1647526 x)). Qed.
Lemma lem1647528 (y : real) : (term29 y) = (term30 y).
Proof. exact (@lem1483523 y term3). Qed.
Lemma lem1647534 (y : real) : (term31 y) = (term32 y).
Proof. exact (@lem1483519 y term3). Qed.
Lemma lem1647536 (x : nat) : (term22 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1647537 : term23 = term3.
Proof. exact (@lem1647536 term24). Qed.
Lemma lem1647538 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1647539 (y : real) : (term32 y) = (term33 y).
Proof. exact (MK_COMB (@lem1647538 y) (@lem1647537)). Qed.
Lemma lem1647540 (y : real) : (term33 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1647541 (y : real) : (term32 y) = y.
Proof. exact (TRANS (@lem1647539 y) (@lem1647540 y)). Qed.
Lemma lem1647543 (y : real) : (term31 y) = y.
Proof. exact (TRANS (@lem1647534 y) (@lem1647541 y)). Qed.
Lemma lem1647544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647545 (y : real) : (term34 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1647544) (@lem1647543 y)). Qed.
Lemma lem1647546 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647547 (y : real) : (term30 y) = (term35 y).
Proof. exact (MK_COMB (@lem1647545 y) (@lem1647546)). Qed.
Lemma lem1647548 (y : real) : (term29 y) = (term35 y).
Proof. exact (TRANS (@lem1647528 y) (@lem1647547 y)). Qed.
Lemma lem1647549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1647550 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1647549) (@lem1647527 x)). Qed.
Lemma lem1647551 (x : real) (y : real) : (term13 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1647550 x) (@lem1647548 y)). Qed.
Lemma lem1647552 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483554 x term3). Qed.
Lemma lem1647558 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1483519 x term3). Qed.
Lemma lem1647560 (x : nat) : (term22 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1647561 : term23 = term3.
Proof. exact (@lem1647560 term24). Qed.
Lemma lem1647562 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1647563 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1647562 x) (@lem1647561)). Qed.
Lemma lem1647564 (x : real) : (term33 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1647565 (x : real) : (term32 x) = x.
Proof. exact (TRANS (@lem1647563 x) (@lem1647564 x)). Qed.
Lemma lem1647567 (x : real) : (term31 x) = x.
Proof. exact (TRANS (@lem1647558 x) (@lem1647565 x)). Qed.
Lemma lem1647568 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1647569 (x : real) : (term41 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1647568) (@lem1647567 x)). Qed.
Lemma lem1647572 (x : real) : (real_neg x) = (term42 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1647573 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1647574 (x : real) : ((term41 x) = (real_neg x)) = ((term41 x) = (term42 x)).
Proof. exact (MK_COMB (@lem1647573 x) (@lem1647572 x)). Qed.
Lemma lem1647575 (x : real) : (term41 x) = (term42 x).
Proof. exact (EQ_MP (@lem1647574 x) (@lem1647569 x)). Qed.
Lemma lem1647576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647577 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1647576) (@lem1647575 x)). Qed.
Lemma lem1647578 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647579 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1647577 x) (@lem1647578)). Qed.
Lemma lem1647580 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647581 (x : real) : (term48 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1647580) (@lem1647567 x)). Qed.
Lemma lem1647582 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647583 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1647581 x) (@lem1647582)). Qed.
Lemma lem1647584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1647585 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1647584) (@lem1647583 x)). Qed.
Lemma lem1647586 (x : real) : (term40 x) = (term53 x).
Proof. exact (MK_COMB (@lem1647585 x) (@lem1647579 x)). Qed.
Lemma lem1647587 (x : real) : (term39 x) = (term53 x).
Proof. exact (TRANS (@lem1647552 x) (@lem1647586 x)). Qed.
Lemma lem1647588 (y : real) : (term39 y) = (term40 y).
Proof. exact (@lem1483554 y term3). Qed.
Lemma lem1647594 (y : real) : (term31 y) = (term32 y).
Proof. exact (@lem1483519 y term3). Qed.
Lemma lem1647596 (x : nat) : (term22 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1647597 : term23 = term3.
Proof. exact (@lem1647596 term24). Qed.
Lemma lem1647598 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1647599 (y : real) : (term32 y) = (term33 y).
Proof. exact (MK_COMB (@lem1647598 y) (@lem1647597)). Qed.
Lemma lem1647600 (y : real) : (term33 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1647601 (y : real) : (term32 y) = y.
Proof. exact (TRANS (@lem1647599 y) (@lem1647600 y)). Qed.
Lemma lem1647603 (y : real) : (term31 y) = y.
Proof. exact (TRANS (@lem1647594 y) (@lem1647601 y)). Qed.
Lemma lem1647604 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1647605 (y : real) : (term41 y) = (real_neg y).
Proof. exact (MK_COMB (@lem1647604) (@lem1647603 y)). Qed.
Lemma lem1647608 (y : real) : (real_neg y) = (term42 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1647609 (y : real) : (term43 y) = (term43 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem1647610 (y : real) : ((term41 y) = (real_neg y)) = ((term41 y) = (term42 y)).
Proof. exact (MK_COMB (@lem1647609 y) (@lem1647608 y)). Qed.
Lemma lem1647611 (y : real) : (term41 y) = (term42 y).
Proof. exact (EQ_MP (@lem1647610 y) (@lem1647605 y)). Qed.
Lemma lem1647612 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647613 (y : real) : (term44 y) = (term45 y).
Proof. exact (MK_COMB (@lem1647612) (@lem1647611 y)). Qed.
Lemma lem1647614 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647615 (y : real) : (term46 y) = (term47 y).
Proof. exact (MK_COMB (@lem1647613 y) (@lem1647614)). Qed.
Lemma lem1647616 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647617 (y : real) : (term48 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1647616) (@lem1647603 y)). Qed.
Lemma lem1647618 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647619 (y : real) : (term49 y) = (term50 y).
Proof. exact (MK_COMB (@lem1647617 y) (@lem1647618)). Qed.
Lemma lem1647620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1647621 (y : real) : (term51 y) = (term52 y).
Proof. exact (MK_COMB (@lem1647620) (@lem1647619 y)). Qed.
Lemma lem1647622 (y : real) : (term40 y) = (term53 y).
Proof. exact (MK_COMB (@lem1647621 y) (@lem1647615 y)). Qed.
Lemma lem1647623 (y : real) : (term39 y) = (term53 y).
Proof. exact (TRANS (@lem1647588 y) (@lem1647622 y)). Qed.
Lemma lem1647624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1647625 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1647624) (@lem1647587 x)). Qed.
Lemma lem1647626 (x : real) (y : real) : (term8 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1647625 x) (@lem1647623 y)). Qed.
Lemma lem1647627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1647628 (x : real) (y : real) : (term9 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1647627) (@lem1647551 x y)). Qed.
Lemma lem1647629 (x : real) (y : real) : (term11 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1647628 x y) (@lem1647626 x y)). Qed.
Lemma lem1647630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1647631 (x : real) (y : real) : (term15 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1647630) (@lem1647506 x y)). Qed.
Lemma lem1647632 (x : real) (y : real) : (term17 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1647631 x y) (@lem1647629 x y)). Qed.
Lemma lem1647639 (x : real) (y : real) : (term18 x y) = (term59 x y).
Proof. exact (TRANS (@lem1647479 x y) (@lem1647632 x y)). Qed.
Lemma lem1647663 (x : real) (y : real) : (term58 x y) = (term60 x y).
Proof. exact (@lem19158 (term53 x) (term38 x y) (term53 y)). Qed.
Lemma lem1647670 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (@lem19158 (term50 y) (term38 x y) (term47 y)). Qed.
Lemma lem1647677 (y : real) (x : real) : (term63 y x) = (term64 y x).
Proof. exact (@lem19158 (term50 x) (term38 x y) (term47 x)). Qed.
Lemma lem1647678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1647679 (y : real) (x : real) : (term65 y x) = (term66 y x).
Proof. exact (MK_COMB (@lem1647678) (@lem1647677 y x)). Qed.
Lemma lem1647680 (x : real) (y : real) : (term60 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1647679 y x) (@lem1647670 x y)). Qed.
Lemma lem1647682 (x : real) (y : real) : (term58 x y) = (term67 x y).
Proof. exact (TRANS (@lem1647663 x y) (@lem1647680 x y)). Qed.
Lemma lem1647685 (x : real) (y : real) : (term15 x y) = (term15 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1647686 (x : real) (y : real) : (term59 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1647685 x y) (@lem1647682 x y)). Qed.
Lemma lem1647687 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (@lem19158 (term64 y x) ((real_add x y) = term3) (term62 x y)). Qed.
Lemma lem1647694 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem19158 (term72 x y) ((real_add x y) = term3) (term73 x y)). Qed.
Lemma lem1647701 (y : real) (x : real) : (term74 y x) = (term75 y x).
Proof. exact (@lem19158 (term76 y x) ((real_add x y) = term3) (term77 y x)). Qed.
Lemma lem1647702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1647703 (y : real) (x : real) : (term78 y x) = (term79 y x).
Proof. exact (MK_COMB (@lem1647702) (@lem1647701 y x)). Qed.
Lemma lem1647704 (x : real) (y : real) : (term69 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1647703 y x) (@lem1647694 x y)). Qed.
Lemma lem1647705 (x : real) (y : real) : (term68 x y) = (term80 x y).
Proof. exact (TRANS (@lem1647687 x y) (@lem1647704 x y)). Qed.
Lemma lem1647706 (x : real) (y : real) : (term59 x y) = (term80 x y).
Proof. exact (TRANS (@lem1647686 x y) (@lem1647705 x y)). Qed.
Lemma lem1647707 (x : real) (y : real) : (term18 x y) = (term80 x y).
Proof. exact (TRANS (@lem1647639 x y) (@lem1647706 x y)). Qed.
Lemma lem1647729 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1647730 (y : real) (x : real) (h1 : term75 y x) : term75 y x.
Proof. exact (h1). Qed.
Lemma lem1647731 (y : real) (x : real) (h1 : term81 y x) : term81 y x.
Proof. exact (h1). Qed.
Lemma lem1647732 (y : real) (x : real) (h1 : term81 y x) : term76 y x.
Proof. exact (proj2 (@lem1647731 y x h1)). Qed.
Lemma lem1647733 (y : real) (x : real) (h1 : term81 y x) : (real_add x y) = term3.
Proof. exact (proj1 (@lem1647731 y x h1)). Qed.
Lemma lem1647734 (y : real) (x : real) (h1 : term81 y x) : term50 x.
Proof. exact (proj2 (@lem1647732 y x h1)). Qed.
Lemma lem1647735 (y : real) (x : real) (h1 : term81 y x) : term38 x y.
Proof. exact (proj1 (@lem1647732 y x h1)). Qed.
Lemma lem1647736 (y : real) (x : real) (h1 : term81 y x) : term35 y.
Proof. exact (proj2 (@lem1647735 y x h1)). Qed.
Lemma lem1647739 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647740 : term83 = term84.
Proof. exact (@lem1647739 (NUMERAL 0) term24). Qed.
Lemma lem1647741 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647742 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647743 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647742 h1) (fun h1 : term84 = True => @lem1647741)). Qed.
Lemma lem1647744 : term84 = True.
Proof. exact (EQ_MP (@lem1647743) (@lem1647741)). Qed.
Lemma lem1647745 : term83 = True.
Proof. exact (TRANS (@lem1647740) (@lem1647744)). Qed.
Lemma lem1647746 : True = term83.
Proof. exact (SYM (@lem1647745)). Qed.
Lemma lem1647747 : term83.
Proof. exact (EQ_MP (@lem1647746) (@lem0)). Qed.
Lemma lem1647748 (y : real) (x : real) (h1 : term81 y x) : term86 y.
Proof. exact (conj (@lem1647747) (@lem1647736 y x h1)). Qed.
Lemma lem1647750 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1647751 (y : real) : term88 y.
Proof. exact (@lem1647750 term89 y). Qed.
Lemma lem1647752 (y : real) (x : real) (h1 : term81 y x) : term90 y.
Proof. exact (@lem1647751 y (@lem1647748 y x h1)). Qed.
Lemma lem1647753 (y : real) : (term91 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1647754 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647755 (y : real) : (term92 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1647754) (@lem1647753 y)). Qed.
Lemma lem1647756 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647757 (y : real) : (term90 y) = (term35 y).
Proof. exact (MK_COMB (@lem1647755 y) (@lem1647756)). Qed.
Lemma lem1647758 (y : real) (x : real) (h1 : term81 y x) : term35 y.
Proof. exact (EQ_MP (@lem1647757 y) (@lem1647752 y x h1)). Qed.
Lemma lem1647760 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647761 : term83 = term84.
Proof. exact (@lem1647760 (NUMERAL 0) term24). Qed.
Lemma lem1647762 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647763 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647764 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647763 h1) (fun h1 : term84 = True => @lem1647762)). Qed.
Lemma lem1647765 : term84 = True.
Proof. exact (EQ_MP (@lem1647764) (@lem1647762)). Qed.
Lemma lem1647766 : term83 = True.
Proof. exact (TRANS (@lem1647761) (@lem1647765)). Qed.
Lemma lem1647767 : True = term83.
Proof. exact (SYM (@lem1647766)). Qed.
Lemma lem1647768 : term83.
Proof. exact (EQ_MP (@lem1647767) (@lem0)). Qed.
Lemma lem1647769 (y : real) (x : real) (h1 : term81 y x) : term93 x.
Proof. exact (conj (@lem1647768) (@lem1647734 y x h1)). Qed.
Lemma lem1647771 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647772 (x : real) : term95 x.
Proof. exact (@lem1647771 term89 x). Qed.
Lemma lem1647773 (y : real) (x : real) (h1 : term81 y x) : term96 x.
Proof. exact (@lem1647772 x (@lem1647769 y x h1)). Qed.
Lemma lem1647774 (x : real) : (term91 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647775 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647776 (x : real) : (term97 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1647775) (@lem1647774 x)). Qed.
Lemma lem1647777 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647778 (x : real) : (term96 x) = (term50 x).
Proof. exact (MK_COMB (@lem1647776 x) (@lem1647777)). Qed.
Lemma lem1647779 (y : real) (x : real) (h1 : term81 y x) : term50 x.
Proof. exact (EQ_MP (@lem1647778 x) (@lem1647773 y x h1)). Qed.
Lemma lem1647781 (y : real) : term98 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1647782 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1647781 (real_add x y)). Qed.
Lemma lem1647783 (y : real) (x : real) (h1 : term81 y x) : term100 x y.
Proof. exact (@lem1647782 x y (@lem1647733 y x h1)). Qed.
Lemma lem1647784 (y : real) (x : real) (h1 : term81 y x) : term101 x y.
Proof. exact (@lem1647783 y x h1 term102). Qed.
Lemma lem1647785 (x : real) (y : real) : (term101 x y) = ((term103 x y) = term3).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1647786 (y : real) (x : real) (h1 : term81 y x) : (term103 x y) = term3.
Proof. exact (EQ_MP (@lem1647785 x y) (@lem1647784 y x h1)). Qed.
Lemma lem1647793 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1483508 x term102 y). Qed.
Lemma lem1647794 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1647795 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1647794) (@lem1647793 x y)). Qed.
Lemma lem1647796 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647797 (x : real) (y : real) : ((term103 x y) = term3) = ((term104 x y) = term3).
Proof. exact (MK_COMB (@lem1647795 x y) (@lem1647796)). Qed.
Lemma lem1647798 (y : real) (x : real) (h1 : term81 y x) : (term104 x y) = term3.
Proof. exact (EQ_MP (@lem1647797 x y) (@lem1647786 y x h1)). Qed.
Lemma lem1647799 (y : real) (x : real) (h1 : term81 y x) : term107 y x.
Proof. exact (conj (@lem1647798 y x h1) (@lem1647779 y x h1)). Qed.
Lemma lem1647801 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1647802 (y : real) (x : real) : term109 y x.
Proof. exact (@lem1647801 (term104 x y) x). Qed.
Lemma lem1647803 (y : real) (x : real) (h1 : term81 y x) : term110 y x.
Proof. exact (@lem1647802 y x (@lem1647799 y x h1)). Qed.
Lemma lem1647804 (x : real) (y : real) : (term111 y x) = (term112 x y).
Proof. exact (@lem1483486 (term42 x) x (term42 y)). Qed.
Lemma lem1647805 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1483440 term102 x). Qed.
Lemma lem1647807 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647808 : term116 = term3.
Proof. exact (@lem1647807 term24). Qed.
Lemma lem1647809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647810 : term117 = term118.
Proof. exact (MK_COMB (@lem1647809) (@lem1647808)). Qed.
Lemma lem1647811 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647812 (x : real) : (term114 x) = (term119 x).
Proof. exact (MK_COMB (@lem1647810) (@lem1647811 x)). Qed.
Lemma lem1647813 (x : real) : (term113 x) = (term119 x).
Proof. exact (TRANS (@lem1647805 x) (@lem1647812 x)). Qed.
Lemma lem1647814 (x : real) : (term119 x) = term3.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647815 (x : real) : (term113 x) = term3.
Proof. exact (TRANS (@lem1647813 x) (@lem1647814 x)). Qed.
Lemma lem1647816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1647817 (x : real) : (term120 x) = term121.
Proof. exact (MK_COMB (@lem1647816) (@lem1647815 x)). Qed.
Lemma lem1647818 (y : real) : (term42 y) = (term42 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem1647819 (x : real) (y : real) : (term112 x y) = (term122 y).
Proof. exact (MK_COMB (@lem1647817 x) (@lem1647818 y)). Qed.
Lemma lem1647820 (x : real) (y : real) : (term111 y x) = (term122 y).
Proof. exact (TRANS (@lem1647804 x y) (@lem1647819 x y)). Qed.
Lemma lem1647821 (y : real) : (term122 y) = (term42 y).
Proof. exact (@lem1483448 (term42 y)). Qed.
Lemma lem1647822 (x : real) (y : real) : (term111 y x) = (term42 y).
Proof. exact (TRANS (@lem1647820 x y) (@lem1647821 y)). Qed.
Lemma lem1647823 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647824 (x : real) (y : real) : (term123 y x) = (term45 y).
Proof. exact (MK_COMB (@lem1647823) (@lem1647822 x y)). Qed.
Lemma lem1647825 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647826 (x : real) (y : real) : (term110 y x) = (term47 y).
Proof. exact (MK_COMB (@lem1647824 x y) (@lem1647825)). Qed.
Lemma lem1647827 (y : real) (x : real) (h1 : term81 y x) : term47 y.
Proof. exact (EQ_MP (@lem1647826 x y) (@lem1647803 y x h1)). Qed.
Lemma lem1647829 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647830 : term83 = term84.
Proof. exact (@lem1647829 (NUMERAL 0) term24). Qed.
Lemma lem1647831 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647832 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647833 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647832 h1) (fun h1 : term84 = True => @lem1647831)). Qed.
Lemma lem1647834 : term84 = True.
Proof. exact (EQ_MP (@lem1647833) (@lem1647831)). Qed.
Lemma lem1647835 : term83 = True.
Proof. exact (TRANS (@lem1647830) (@lem1647834)). Qed.
Lemma lem1647836 : True = term83.
Proof. exact (SYM (@lem1647835)). Qed.
Lemma lem1647837 : term83.
Proof. exact (EQ_MP (@lem1647836) (@lem0)). Qed.
Lemma lem1647838 (y : real) (x : real) (h1 : term81 y x) : term124 y.
Proof. exact (conj (@lem1647837) (@lem1647827 y x h1)). Qed.
Lemma lem1647840 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647841 (y : real) : term125 y.
Proof. exact (@lem1647840 term89 (term42 y)). Qed.
Lemma lem1647842 (y : real) (x : real) (h1 : term81 y x) : term126 y.
Proof. exact (@lem1647841 y (@lem1647838 y x h1)). Qed.
Lemma lem1647843 (y : real) : (term127 y) = (term42 y).
Proof. exact (@lem1483460 (term42 y)). Qed.
Lemma lem1647844 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647845 (y : real) : (term128 y) = (term45 y).
Proof. exact (MK_COMB (@lem1647844) (@lem1647843 y)). Qed.
Lemma lem1647846 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647847 (y : real) : (term126 y) = (term47 y).
Proof. exact (MK_COMB (@lem1647845 y) (@lem1647846)). Qed.
Lemma lem1647848 (y : real) (x : real) (h1 : term81 y x) : term47 y.
Proof. exact (EQ_MP (@lem1647847 y) (@lem1647842 y x h1)). Qed.
Lemma lem1647849 (y : real) (x : real) (h1 : term81 y x) : term129 y.
Proof. exact (conj (@lem1647848 y x h1) (@lem1647758 y x h1)). Qed.
Lemma lem1647851 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1647852 (y : real) : term131 y.
Proof. exact (@lem1647851 (term42 y) y). Qed.
Lemma lem1647853 (y : real) (x : real) (h1 : term81 y x) : term132 y.
Proof. exact (@lem1647852 y (@lem1647849 y x h1)). Qed.
Lemma lem1647854 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483440 term102 y). Qed.
Lemma lem1647856 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647857 : term116 = term3.
Proof. exact (@lem1647856 term24). Qed.
Lemma lem1647858 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647859 : term117 = term118.
Proof. exact (MK_COMB (@lem1647858) (@lem1647857)). Qed.
Lemma lem1647860 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1647861 (y : real) : (term114 y) = (term119 y).
Proof. exact (MK_COMB (@lem1647859) (@lem1647860 y)). Qed.
Lemma lem1647862 (y : real) : (term113 y) = (term119 y).
Proof. exact (TRANS (@lem1647854 y) (@lem1647861 y)). Qed.
Lemma lem1647863 (y : real) : (term119 y) = term3.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1647864 (y : real) : (term113 y) = term3.
Proof. exact (TRANS (@lem1647862 y) (@lem1647863 y)). Qed.
Lemma lem1647865 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647866 (y : real) : (term133 y) = term134.
Proof. exact (MK_COMB (@lem1647865) (@lem1647864 y)). Qed.
Lemma lem1647867 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647868 (y : real) : (term132 y) = term135.
Proof. exact (MK_COMB (@lem1647866 y) (@lem1647867)). Qed.
Lemma lem1647869 (y : real) (x : real) (h1 : term81 y x) : term135.
Proof. exact (EQ_MP (@lem1647868 y) (@lem1647853 y x h1)). Qed.
Lemma lem1647871 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647872 : term135 = term136.
Proof. exact (@lem1647871 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1647873 : term136 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1647874 : term135 = False.
Proof. exact (TRANS (@lem1647872) (@lem1647873)). Qed.
Lemma lem1647875 (y : real) (x : real) (h1 : term81 y x) : False.
Proof. exact (EQ_MP (@lem1647874) (@lem1647869 y x h1)). Qed.
Lemma lem1647876 (y : real) (x : real) (h1 : term137 y x) : term137 y x.
Proof. exact (h1). Qed.
Lemma lem1647877 (y : real) (x : real) (h1 : term137 y x) : term77 y x.
Proof. exact (proj2 (@lem1647876 y x h1)). Qed.
Lemma lem1647878 (y : real) (x : real) (h1 : term137 y x) : (real_add x y) = term3.
Proof. exact (proj1 (@lem1647876 y x h1)). Qed.
Lemma lem1647879 (y : real) (x : real) (h1 : term137 y x) : term47 x.
Proof. exact (proj2 (@lem1647877 y x h1)). Qed.
Lemma lem1647880 (y : real) (x : real) (h1 : term137 y x) : term38 x y.
Proof. exact (proj1 (@lem1647877 y x h1)). Qed.
Lemma lem1647882 (y : real) (x : real) (h1 : term137 y x) : term35 x.
Proof. exact (proj1 (@lem1647880 y x h1)). Qed.
Lemma lem1647884 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647885 : term83 = term84.
Proof. exact (@lem1647884 (NUMERAL 0) term24). Qed.
Lemma lem1647886 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647887 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647888 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647887 h1) (fun h1 : term84 = True => @lem1647886)). Qed.
Lemma lem1647889 : term84 = True.
Proof. exact (EQ_MP (@lem1647888) (@lem1647886)). Qed.
Lemma lem1647890 : term83 = True.
Proof. exact (TRANS (@lem1647885) (@lem1647889)). Qed.
Lemma lem1647891 : True = term83.
Proof. exact (SYM (@lem1647890)). Qed.
Lemma lem1647892 : term83.
Proof. exact (EQ_MP (@lem1647891) (@lem0)). Qed.
Lemma lem1647893 (y : real) (x : real) (h1 : term137 y x) : term86 x.
Proof. exact (conj (@lem1647892) (@lem1647882 y x h1)). Qed.
Lemma lem1647895 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1647896 (x : real) : term88 x.
Proof. exact (@lem1647895 term89 x). Qed.
Lemma lem1647897 (y : real) (x : real) (h1 : term137 y x) : term90 x.
Proof. exact (@lem1647896 x (@lem1647893 y x h1)). Qed.
Lemma lem1647898 (x : real) : (term91 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1647899 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647900 (x : real) : (term92 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1647899) (@lem1647898 x)). Qed.
Lemma lem1647901 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647902 (x : real) : (term90 x) = (term35 x).
Proof. exact (MK_COMB (@lem1647900 x) (@lem1647901)). Qed.
Lemma lem1647903 (y : real) (x : real) (h1 : term137 y x) : term35 x.
Proof. exact (EQ_MP (@lem1647902 x) (@lem1647897 y x h1)). Qed.
Lemma lem1647905 (y : real) : term98 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1647906 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1647905 (real_add x y)). Qed.
Lemma lem1647907 (y : real) (x : real) (h1 : term137 y x) : term100 x y.
Proof. exact (@lem1647906 x y (@lem1647878 y x h1)). Qed.
Lemma lem1647908 (y : real) (x : real) (h1 : term137 y x) : term101 x y.
Proof. exact (@lem1647907 y x h1 term102). Qed.
Lemma lem1647909 (x : real) (y : real) : (term101 x y) = ((term103 x y) = term3).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1647910 (y : real) (x : real) (h1 : term137 y x) : (term103 x y) = term3.
Proof. exact (EQ_MP (@lem1647909 x y) (@lem1647908 y x h1)). Qed.
Lemma lem1647917 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1483508 x term102 y). Qed.
Lemma lem1647918 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1647919 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1647918) (@lem1647917 x y)). Qed.
Lemma lem1647920 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647921 (x : real) (y : real) : ((term103 x y) = term3) = ((term104 x y) = term3).
Proof. exact (MK_COMB (@lem1647919 x y) (@lem1647920)). Qed.
Lemma lem1647922 (y : real) (x : real) (h1 : term137 y x) : (term104 x y) = term3.
Proof. exact (EQ_MP (@lem1647921 x y) (@lem1647910 y x h1)). Qed.
Lemma lem1647923 (y : real) (x : real) (h1 : term137 y x) : term138 y x.
Proof. exact (conj (@lem1647922 y x h1) (@lem1647903 y x h1)). Qed.
Lemma lem1647925 (x : real) (y : real) : term139 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1647926 (y : real) (x : real) : term140 y x.
Proof. exact (@lem1647925 (term104 x y) x). Qed.
Lemma lem1647927 (y : real) (x : real) (h1 : term137 y x) : term141 y x.
Proof. exact (@lem1647926 y x (@lem1647923 y x h1)). Qed.
Lemma lem1647928 (x : real) (y : real) : (term111 y x) = (term112 x y).
Proof. exact (@lem1483486 (term42 x) x (term42 y)). Qed.
Lemma lem1647929 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1483440 term102 x). Qed.
Lemma lem1647931 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1647932 : term116 = term3.
Proof. exact (@lem1647931 term24). Qed.
Lemma lem1647933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1647934 : term117 = term118.
Proof. exact (MK_COMB (@lem1647933) (@lem1647932)). Qed.
Lemma lem1647935 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1647936 (x : real) : (term114 x) = (term119 x).
Proof. exact (MK_COMB (@lem1647934) (@lem1647935 x)). Qed.
Lemma lem1647937 (x : real) : (term113 x) = (term119 x).
Proof. exact (TRANS (@lem1647929 x) (@lem1647936 x)). Qed.
Lemma lem1647938 (x : real) : (term119 x) = term3.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1647939 (x : real) : (term113 x) = term3.
Proof. exact (TRANS (@lem1647937 x) (@lem1647938 x)). Qed.
Lemma lem1647940 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1647941 (x : real) : (term120 x) = term121.
Proof. exact (MK_COMB (@lem1647940) (@lem1647939 x)). Qed.
Lemma lem1647942 (y : real) : (term42 y) = (term42 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem1647943 (x : real) (y : real) : (term112 x y) = (term122 y).
Proof. exact (MK_COMB (@lem1647941 x) (@lem1647942 y)). Qed.
Lemma lem1647944 (x : real) (y : real) : (term111 y x) = (term122 y).
Proof. exact (TRANS (@lem1647928 x y) (@lem1647943 x y)). Qed.
Lemma lem1647945 (y : real) : (term122 y) = (term42 y).
Proof. exact (@lem1483448 (term42 y)). Qed.
Lemma lem1647946 (x : real) (y : real) : (term111 y x) = (term42 y).
Proof. exact (TRANS (@lem1647944 x y) (@lem1647945 y)). Qed.
Lemma lem1647947 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647948 (x : real) (y : real) : (term142 y x) = (term143 y).
Proof. exact (MK_COMB (@lem1647947) (@lem1647946 x y)). Qed.
Lemma lem1647949 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647950 (x : real) (y : real) : (term141 y x) = (term144 y).
Proof. exact (MK_COMB (@lem1647948 x y) (@lem1647949)). Qed.
Lemma lem1647951 (y : real) (x : real) (h1 : term137 y x) : term144 y.
Proof. exact (EQ_MP (@lem1647950 x y) (@lem1647927 y x h1)). Qed.
Lemma lem1647953 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647954 : term83 = term84.
Proof. exact (@lem1647953 (NUMERAL 0) term24). Qed.
Lemma lem1647955 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647956 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647957 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647956 h1) (fun h1 : term84 = True => @lem1647955)). Qed.
Lemma lem1647958 : term84 = True.
Proof. exact (EQ_MP (@lem1647957) (@lem1647955)). Qed.
Lemma lem1647959 : term83 = True.
Proof. exact (TRANS (@lem1647954) (@lem1647958)). Qed.
Lemma lem1647960 : True = term83.
Proof. exact (SYM (@lem1647959)). Qed.
Lemma lem1647961 : term83.
Proof. exact (EQ_MP (@lem1647960) (@lem0)). Qed.
Lemma lem1647962 (y : real) (x : real) (h1 : term137 y x) : term145 y.
Proof. exact (conj (@lem1647961) (@lem1647951 y x h1)). Qed.
Lemma lem1647964 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1647965 (y : real) : term146 y.
Proof. exact (@lem1647964 term89 (term42 y)). Qed.
Lemma lem1647966 (y : real) (x : real) (h1 : term137 y x) : term147 y.
Proof. exact (@lem1647965 y (@lem1647962 y x h1)). Qed.
Lemma lem1647967 (y : real) : (term127 y) = (term42 y).
Proof. exact (@lem1483460 (term42 y)). Qed.
Lemma lem1647968 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1647969 (y : real) : (term148 y) = (term143 y).
Proof. exact (MK_COMB (@lem1647968) (@lem1647967 y)). Qed.
Lemma lem1647970 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647971 (y : real) : (term147 y) = (term144 y).
Proof. exact (MK_COMB (@lem1647969 y) (@lem1647970)). Qed.
Lemma lem1647972 (y : real) (x : real) (h1 : term137 y x) : term144 y.
Proof. exact (EQ_MP (@lem1647971 y) (@lem1647966 y x h1)). Qed.
Lemma lem1647974 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1647975 : term83 = term84.
Proof. exact (@lem1647974 (NUMERAL 0) term24). Qed.
Lemma lem1647976 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1647977 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1647978 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1647977 h1) (fun h1 : term84 = True => @lem1647976)). Qed.
Lemma lem1647979 : term84 = True.
Proof. exact (EQ_MP (@lem1647978) (@lem1647976)). Qed.
Lemma lem1647980 : term83 = True.
Proof. exact (TRANS (@lem1647975) (@lem1647979)). Qed.
Lemma lem1647981 : True = term83.
Proof. exact (SYM (@lem1647980)). Qed.
Lemma lem1647982 : term83.
Proof. exact (EQ_MP (@lem1647981) (@lem0)). Qed.
Lemma lem1647983 (y : real) (x : real) (h1 : term137 y x) : term124 x.
Proof. exact (conj (@lem1647982) (@lem1647879 y x h1)). Qed.
Lemma lem1647985 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1647986 (x : real) : term125 x.
Proof. exact (@lem1647985 term89 (term42 x)). Qed.
Lemma lem1647987 (y : real) (x : real) (h1 : term137 y x) : term126 x.
Proof. exact (@lem1647986 x (@lem1647983 y x h1)). Qed.
Lemma lem1647988 (x : real) : (term127 x) = (term42 x).
Proof. exact (@lem1483460 (term42 x)). Qed.
Lemma lem1647989 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1647990 (x : real) : (term128 x) = (term45 x).
Proof. exact (MK_COMB (@lem1647989) (@lem1647988 x)). Qed.
Lemma lem1647991 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1647992 (x : real) : (term126 x) = (term47 x).
Proof. exact (MK_COMB (@lem1647990 x) (@lem1647991)). Qed.
Lemma lem1647993 (y : real) (x : real) (h1 : term137 y x) : term47 x.
Proof. exact (EQ_MP (@lem1647992 x) (@lem1647987 y x h1)). Qed.
Lemma lem1647995 (y : real) : term98 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1647996 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1647995 (real_add x y)). Qed.
Lemma lem1647997 (y : real) (x : real) (h1 : term137 y x) : term100 x y.
Proof. exact (@lem1647996 x y (@lem1647878 y x h1)). Qed.
Lemma lem1647998 (y : real) (x : real) (h1 : term137 y x) : term149 x y.
Proof. exact (@lem1647997 y x h1 term89). Qed.
Lemma lem1647999 (x : real) (y : real) : (term149 x y) = ((term150 x y) = term3).
Proof. exact (eq_refl (term149 x y)). Qed.
Lemma lem1648000 (y : real) (x : real) (h1 : term137 y x) : (term150 x y) = term3.
Proof. exact (EQ_MP (@lem1647999 x y) (@lem1647998 y x h1)). Qed.
Lemma lem1648001 (x : real) (y : real) : (term150 x y) = (real_add x y).
Proof. exact (@lem1483460 (real_add x y)). Qed.
Lemma lem1648002 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648003 (x : real) (y : real) : (term151 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1648002) (@lem1648001 x y)). Qed.
Lemma lem1648004 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648005 (x : real) (y : real) : ((term150 x y) = term3) = ((real_add x y) = term3).
Proof. exact (MK_COMB (@lem1648003 x y) (@lem1648004)). Qed.
Lemma lem1648006 (y : real) (x : real) (h1 : term137 y x) : (real_add x y) = term3.
Proof. exact (EQ_MP (@lem1648005 x y) (@lem1648000 y x h1)). Qed.
Lemma lem1648007 (y : real) (x : real) (h1 : term137 y x) : term152 y x.
Proof. exact (conj (@lem1648006 y x h1) (@lem1647993 y x h1)). Qed.
Lemma lem1648009 (x : real) (y : real) : term108 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1648010 (y : real) (x : real) : term153 y x.
Proof. exact (@lem1648009 (real_add x y) (term42 x)). Qed.
Lemma lem1648011 (y : real) (x : real) (h1 : term137 y x) : term154 y x.
Proof. exact (@lem1648010 y x (@lem1648007 y x h1)). Qed.
Lemma lem1648012 (x : real) (y : real) : (term155 y x) = (term156 x y).
Proof. exact (@lem1483486 x (term42 x) y). Qed.
Lemma lem1648013 (x : real) : (term157 x) = (term114 x).
Proof. exact (@lem1483442 term102 x). Qed.
Lemma lem1648015 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1648016 : term116 = term3.
Proof. exact (@lem1648015 term24). Qed.
Lemma lem1648017 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648018 : term117 = term118.
Proof. exact (MK_COMB (@lem1648017) (@lem1648016)). Qed.
Lemma lem1648019 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1648020 (x : real) : (term114 x) = (term119 x).
Proof. exact (MK_COMB (@lem1648018) (@lem1648019 x)). Qed.
Lemma lem1648021 (x : real) : (term157 x) = (term119 x).
Proof. exact (TRANS (@lem1648013 x) (@lem1648020 x)). Qed.
Lemma lem1648022 (x : real) : (term119 x) = term3.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1648023 (x : real) : (term157 x) = term3.
Proof. exact (TRANS (@lem1648021 x) (@lem1648022 x)). Qed.
Lemma lem1648024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1648025 (x : real) : (term158 x) = term121.
Proof. exact (MK_COMB (@lem1648024) (@lem1648023 x)). Qed.
Lemma lem1648026 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1648027 (x : real) (y : real) : (term156 x y) = (term159 y).
Proof. exact (MK_COMB (@lem1648025 x) (@lem1648026 y)). Qed.
Lemma lem1648028 (x : real) (y : real) : (term155 y x) = (term159 y).
Proof. exact (TRANS (@lem1648012 x y) (@lem1648027 x y)). Qed.
Lemma lem1648029 (y : real) : (term159 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1648030 (x : real) (y : real) : (term155 y x) = y.
Proof. exact (TRANS (@lem1648028 x y) (@lem1648029 y)). Qed.
Lemma lem1648031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648032 (x : real) (y : real) : (term160 y x) = (real_gt y).
Proof. exact (MK_COMB (@lem1648031) (@lem1648030 x y)). Qed.
Lemma lem1648033 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648034 (x : real) (y : real) : (term154 y x) = (term50 y).
Proof. exact (MK_COMB (@lem1648032 x y) (@lem1648033)). Qed.
Lemma lem1648035 (y : real) (x : real) (h1 : term137 y x) : term50 y.
Proof. exact (EQ_MP (@lem1648034 x y) (@lem1648011 y x h1)). Qed.
Lemma lem1648037 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648038 : term83 = term84.
Proof. exact (@lem1648037 (NUMERAL 0) term24). Qed.
Lemma lem1648039 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648040 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648041 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648040 h1) (fun h1 : term84 = True => @lem1648039)). Qed.
Lemma lem1648042 : term84 = True.
Proof. exact (EQ_MP (@lem1648041) (@lem1648039)). Qed.
Lemma lem1648043 : term83 = True.
Proof. exact (TRANS (@lem1648038) (@lem1648042)). Qed.
Lemma lem1648044 : True = term83.
Proof. exact (SYM (@lem1648043)). Qed.
Lemma lem1648045 : term83.
Proof. exact (EQ_MP (@lem1648044) (@lem0)). Qed.
Lemma lem1648046 (y : real) (x : real) (h1 : term137 y x) : term93 y.
Proof. exact (conj (@lem1648045) (@lem1648035 y x h1)). Qed.
Lemma lem1648048 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1648049 (y : real) : term95 y.
Proof. exact (@lem1648048 term89 y). Qed.
Lemma lem1648050 (y : real) (x : real) (h1 : term137 y x) : term96 y.
Proof. exact (@lem1648049 y (@lem1648046 y x h1)). Qed.
Lemma lem1648051 (y : real) : (term91 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1648052 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648053 (y : real) : (term97 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1648052) (@lem1648051 y)). Qed.
Lemma lem1648054 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648055 (y : real) : (term96 y) = (term50 y).
Proof. exact (MK_COMB (@lem1648053 y) (@lem1648054)). Qed.
Lemma lem1648056 (y : real) (x : real) (h1 : term137 y x) : term50 y.
Proof. exact (EQ_MP (@lem1648055 y) (@lem1648050 y x h1)). Qed.
Lemma lem1648057 (y : real) (x : real) (h1 : term137 y x) : term161 y.
Proof. exact (conj (@lem1648056 y x h1) (@lem1647972 y x h1)). Qed.
Lemma lem1648059 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1648060 (y : real) : term162 y.
Proof. exact (@lem1648059 y (term42 y)). Qed.
Lemma lem1648061 (y : real) (x : real) (h1 : term137 y x) : term163 y.
Proof. exact (@lem1648060 y (@lem1648057 y x h1)). Qed.
Lemma lem1648062 (y : real) : (term157 y) = (term114 y).
Proof. exact (@lem1483442 term102 y). Qed.
Lemma lem1648064 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1648065 : term116 = term3.
Proof. exact (@lem1648064 term24). Qed.
Lemma lem1648066 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648067 : term117 = term118.
Proof. exact (MK_COMB (@lem1648066) (@lem1648065)). Qed.
Lemma lem1648068 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1648069 (y : real) : (term114 y) = (term119 y).
Proof. exact (MK_COMB (@lem1648067) (@lem1648068 y)). Qed.
Lemma lem1648070 (y : real) : (term157 y) = (term119 y).
Proof. exact (TRANS (@lem1648062 y) (@lem1648069 y)). Qed.
Lemma lem1648071 (y : real) : (term119 y) = term3.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1648072 (y : real) : (term157 y) = term3.
Proof. exact (TRANS (@lem1648070 y) (@lem1648071 y)). Qed.
Lemma lem1648073 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648074 (y : real) : (term164 y) = term134.
Proof. exact (MK_COMB (@lem1648073) (@lem1648072 y)). Qed.
Lemma lem1648075 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648076 (y : real) : (term163 y) = term135.
Proof. exact (MK_COMB (@lem1648074 y) (@lem1648075)). Qed.
Lemma lem1648077 (y : real) (x : real) (h1 : term137 y x) : term135.
Proof. exact (EQ_MP (@lem1648076 y) (@lem1648061 y x h1)). Qed.
Lemma lem1648079 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648080 : term135 = term136.
Proof. exact (@lem1648079 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1648081 : term136 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1648082 : term135 = False.
Proof. exact (TRANS (@lem1648080) (@lem1648081)). Qed.
Lemma lem1648083 (y : real) (x : real) (h1 : term137 y x) : False.
Proof. exact (EQ_MP (@lem1648082) (@lem1648077 y x h1)). Qed.
Lemma lem1648084 (y : real) (x : real) (h1 : term75 y x) : False.
Proof. exact (or_elim (@lem1647730 y x h1) (fun h0 : term81 y x => @lem1647875 y x h0) (fun h0 : term137 y x => @lem1648083 y x h0)). Qed.
Lemma lem1648085 (x : real) (y : real) (h1 : term71 x y) : term71 x y.
Proof. exact (h1). Qed.
Lemma lem1648086 (x : real) (y : real) (h1 : term165 x y) : term165 x y.
Proof. exact (h1). Qed.
Lemma lem1648087 (x : real) (y : real) (h1 : term165 x y) : term72 x y.
Proof. exact (proj2 (@lem1648086 x y h1)). Qed.
Lemma lem1648088 (x : real) (y : real) (h1 : term165 x y) : (real_add x y) = term3.
Proof. exact (proj1 (@lem1648086 x y h1)). Qed.
Lemma lem1648089 (x : real) (y : real) (h1 : term165 x y) : term50 y.
Proof. exact (proj2 (@lem1648087 x y h1)). Qed.
Lemma lem1648090 (x : real) (y : real) (h1 : term165 x y) : term38 x y.
Proof. exact (proj1 (@lem1648087 x y h1)). Qed.
Lemma lem1648092 (x : real) (y : real) (h1 : term165 x y) : term35 x.
Proof. exact (proj1 (@lem1648090 x y h1)). Qed.
Lemma lem1648094 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648095 : term83 = term84.
Proof. exact (@lem1648094 (NUMERAL 0) term24). Qed.
Lemma lem1648096 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648097 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648098 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648097 h1) (fun h1 : term84 = True => @lem1648096)). Qed.
Lemma lem1648099 : term84 = True.
Proof. exact (EQ_MP (@lem1648098) (@lem1648096)). Qed.
Lemma lem1648100 : term83 = True.
Proof. exact (TRANS (@lem1648095) (@lem1648099)). Qed.
Lemma lem1648101 : True = term83.
Proof. exact (SYM (@lem1648100)). Qed.
Lemma lem1648102 : term83.
Proof. exact (EQ_MP (@lem1648101) (@lem0)). Qed.
Lemma lem1648103 (x : real) (y : real) (h1 : term165 x y) : term86 x.
Proof. exact (conj (@lem1648102) (@lem1648092 x y h1)). Qed.
Lemma lem1648105 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1648106 (x : real) : term88 x.
Proof. exact (@lem1648105 term89 x). Qed.
Lemma lem1648107 (x : real) (y : real) (h1 : term165 x y) : term90 x.
Proof. exact (@lem1648106 x (@lem1648103 x y h1)). Qed.
Lemma lem1648108 (x : real) : (term91 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1648109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1648110 (x : real) : (term92 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1648109) (@lem1648108 x)). Qed.
Lemma lem1648111 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648112 (x : real) : (term90 x) = (term35 x).
Proof. exact (MK_COMB (@lem1648110 x) (@lem1648111)). Qed.
Lemma lem1648113 (x : real) (y : real) (h1 : term165 x y) : term35 x.
Proof. exact (EQ_MP (@lem1648112 x) (@lem1648107 x y h1)). Qed.
Lemma lem1648115 (y : real) : term98 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1648116 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1648115 (real_add x y)). Qed.
Lemma lem1648117 (x : real) (y : real) (h1 : term165 x y) : term100 x y.
Proof. exact (@lem1648116 x y (@lem1648088 x y h1)). Qed.
Lemma lem1648118 (x : real) (y : real) (h1 : term165 x y) : term101 x y.
Proof. exact (@lem1648117 x y h1 term102). Qed.
Lemma lem1648119 (x : real) (y : real) : (term101 x y) = ((term103 x y) = term3).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1648120 (x : real) (y : real) (h1 : term165 x y) : (term103 x y) = term3.
Proof. exact (EQ_MP (@lem1648119 x y) (@lem1648118 x y h1)). Qed.
Lemma lem1648127 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1483508 x term102 y). Qed.
Lemma lem1648128 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648129 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1648128) (@lem1648127 x y)). Qed.
Lemma lem1648130 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648131 (x : real) (y : real) : ((term103 x y) = term3) = ((term104 x y) = term3).
Proof. exact (MK_COMB (@lem1648129 x y) (@lem1648130)). Qed.
Lemma lem1648132 (x : real) (y : real) (h1 : term165 x y) : (term104 x y) = term3.
Proof. exact (EQ_MP (@lem1648131 x y) (@lem1648120 x y h1)). Qed.
Lemma lem1648133 (x : real) (y : real) (h1 : term165 x y) : term138 y x.
Proof. exact (conj (@lem1648132 x y h1) (@lem1648113 x y h1)). Qed.
Lemma lem1648135 (x : real) (y : real) : term139 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1648136 (y : real) (x : real) : term140 y x.
Proof. exact (@lem1648135 (term104 x y) x). Qed.
Lemma lem1648137 (x : real) (y : real) (h1 : term165 x y) : term141 y x.
Proof. exact (@lem1648136 y x (@lem1648133 x y h1)). Qed.
Lemma lem1648138 (x : real) (y : real) : (term111 y x) = (term112 x y).
Proof. exact (@lem1483486 (term42 x) x (term42 y)). Qed.
Lemma lem1648139 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1483440 term102 x). Qed.
Lemma lem1648141 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1648142 : term116 = term3.
Proof. exact (@lem1648141 term24). Qed.
Lemma lem1648143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648144 : term117 = term118.
Proof. exact (MK_COMB (@lem1648143) (@lem1648142)). Qed.
Lemma lem1648145 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1648146 (x : real) : (term114 x) = (term119 x).
Proof. exact (MK_COMB (@lem1648144) (@lem1648145 x)). Qed.
Lemma lem1648147 (x : real) : (term113 x) = (term119 x).
Proof. exact (TRANS (@lem1648139 x) (@lem1648146 x)). Qed.
Lemma lem1648148 (x : real) : (term119 x) = term3.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1648149 (x : real) : (term113 x) = term3.
Proof. exact (TRANS (@lem1648147 x) (@lem1648148 x)). Qed.
Lemma lem1648150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1648151 (x : real) : (term120 x) = term121.
Proof. exact (MK_COMB (@lem1648150) (@lem1648149 x)). Qed.
Lemma lem1648152 (y : real) : (term42 y) = (term42 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem1648153 (x : real) (y : real) : (term112 x y) = (term122 y).
Proof. exact (MK_COMB (@lem1648151 x) (@lem1648152 y)). Qed.
Lemma lem1648154 (x : real) (y : real) : (term111 y x) = (term122 y).
Proof. exact (TRANS (@lem1648138 x y) (@lem1648153 x y)). Qed.
Lemma lem1648155 (y : real) : (term122 y) = (term42 y).
Proof. exact (@lem1483448 (term42 y)). Qed.
Lemma lem1648156 (x : real) (y : real) : (term111 y x) = (term42 y).
Proof. exact (TRANS (@lem1648154 x y) (@lem1648155 y)). Qed.
Lemma lem1648157 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1648158 (x : real) (y : real) : (term142 y x) = (term143 y).
Proof. exact (MK_COMB (@lem1648157) (@lem1648156 x y)). Qed.
Lemma lem1648159 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648160 (x : real) (y : real) : (term141 y x) = (term144 y).
Proof. exact (MK_COMB (@lem1648158 x y) (@lem1648159)). Qed.
Lemma lem1648161 (x : real) (y : real) (h1 : term165 x y) : term144 y.
Proof. exact (EQ_MP (@lem1648160 x y) (@lem1648137 x y h1)). Qed.
Lemma lem1648163 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648164 : term83 = term84.
Proof. exact (@lem1648163 (NUMERAL 0) term24). Qed.
Lemma lem1648165 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648166 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648167 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648166 h1) (fun h1 : term84 = True => @lem1648165)). Qed.
Lemma lem1648168 : term84 = True.
Proof. exact (EQ_MP (@lem1648167) (@lem1648165)). Qed.
Lemma lem1648169 : term83 = True.
Proof. exact (TRANS (@lem1648164) (@lem1648168)). Qed.
Lemma lem1648170 : True = term83.
Proof. exact (SYM (@lem1648169)). Qed.
Lemma lem1648171 : term83.
Proof. exact (EQ_MP (@lem1648170) (@lem0)). Qed.
Lemma lem1648172 (x : real) (y : real) (h1 : term165 x y) : term145 y.
Proof. exact (conj (@lem1648171) (@lem1648161 x y h1)). Qed.
Lemma lem1648174 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1648175 (y : real) : term146 y.
Proof. exact (@lem1648174 term89 (term42 y)). Qed.
Lemma lem1648176 (x : real) (y : real) (h1 : term165 x y) : term147 y.
Proof. exact (@lem1648175 y (@lem1648172 x y h1)). Qed.
Lemma lem1648177 (y : real) : (term127 y) = (term42 y).
Proof. exact (@lem1483460 (term42 y)). Qed.
Lemma lem1648178 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1648179 (y : real) : (term148 y) = (term143 y).
Proof. exact (MK_COMB (@lem1648178) (@lem1648177 y)). Qed.
Lemma lem1648180 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648181 (y : real) : (term147 y) = (term144 y).
Proof. exact (MK_COMB (@lem1648179 y) (@lem1648180)). Qed.
Lemma lem1648182 (x : real) (y : real) (h1 : term165 x y) : term144 y.
Proof. exact (EQ_MP (@lem1648181 y) (@lem1648176 x y h1)). Qed.
Lemma lem1648184 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648185 : term83 = term84.
Proof. exact (@lem1648184 (NUMERAL 0) term24). Qed.
Lemma lem1648186 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648187 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648188 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648187 h1) (fun h1 : term84 = True => @lem1648186)). Qed.
Lemma lem1648189 : term84 = True.
Proof. exact (EQ_MP (@lem1648188) (@lem1648186)). Qed.
Lemma lem1648190 : term83 = True.
Proof. exact (TRANS (@lem1648185) (@lem1648189)). Qed.
Lemma lem1648191 : True = term83.
Proof. exact (SYM (@lem1648190)). Qed.
Lemma lem1648192 : term83.
Proof. exact (EQ_MP (@lem1648191) (@lem0)). Qed.
Lemma lem1648193 (x : real) (y : real) (h1 : term165 x y) : term93 y.
Proof. exact (conj (@lem1648192) (@lem1648089 x y h1)). Qed.
Lemma lem1648195 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1648196 (y : real) : term95 y.
Proof. exact (@lem1648195 term89 y). Qed.
Lemma lem1648197 (x : real) (y : real) (h1 : term165 x y) : term96 y.
Proof. exact (@lem1648196 y (@lem1648193 x y h1)). Qed.
Lemma lem1648198 (y : real) : (term91 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1648199 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648200 (y : real) : (term97 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1648199) (@lem1648198 y)). Qed.
Lemma lem1648201 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648202 (y : real) : (term96 y) = (term50 y).
Proof. exact (MK_COMB (@lem1648200 y) (@lem1648201)). Qed.
Lemma lem1648203 (x : real) (y : real) (h1 : term165 x y) : term50 y.
Proof. exact (EQ_MP (@lem1648202 y) (@lem1648197 x y h1)). Qed.
Lemma lem1648204 (x : real) (y : real) (h1 : term165 x y) : term161 y.
Proof. exact (conj (@lem1648203 x y h1) (@lem1648182 x y h1)). Qed.
Lemma lem1648206 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1648207 (y : real) : term162 y.
Proof. exact (@lem1648206 y (term42 y)). Qed.
Lemma lem1648208 (x : real) (y : real) (h1 : term165 x y) : term163 y.
Proof. exact (@lem1648207 y (@lem1648204 x y h1)). Qed.
Lemma lem1648209 (y : real) : (term157 y) = (term114 y).
Proof. exact (@lem1483442 term102 y). Qed.
Lemma lem1648211 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1648212 : term116 = term3.
Proof. exact (@lem1648211 term24). Qed.
Lemma lem1648213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648214 : term117 = term118.
Proof. exact (MK_COMB (@lem1648213) (@lem1648212)). Qed.
Lemma lem1648215 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1648216 (y : real) : (term114 y) = (term119 y).
Proof. exact (MK_COMB (@lem1648214) (@lem1648215 y)). Qed.
Lemma lem1648217 (y : real) : (term157 y) = (term119 y).
Proof. exact (TRANS (@lem1648209 y) (@lem1648216 y)). Qed.
Lemma lem1648218 (y : real) : (term119 y) = term3.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1648219 (y : real) : (term157 y) = term3.
Proof. exact (TRANS (@lem1648217 y) (@lem1648218 y)). Qed.
Lemma lem1648220 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648221 (y : real) : (term164 y) = term134.
Proof. exact (MK_COMB (@lem1648220) (@lem1648219 y)). Qed.
Lemma lem1648222 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648223 (y : real) : (term163 y) = term135.
Proof. exact (MK_COMB (@lem1648221 y) (@lem1648222)). Qed.
Lemma lem1648224 (x : real) (y : real) (h1 : term165 x y) : term135.
Proof. exact (EQ_MP (@lem1648223 y) (@lem1648208 x y h1)). Qed.
Lemma lem1648226 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648227 : term135 = term136.
Proof. exact (@lem1648226 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1648228 : term136 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1648229 : term135 = False.
Proof. exact (TRANS (@lem1648227) (@lem1648228)). Qed.
Lemma lem1648230 (x : real) (y : real) (h1 : term165 x y) : False.
Proof. exact (EQ_MP (@lem1648229) (@lem1648224 x y h1)). Qed.
Lemma lem1648231 (x : real) (y : real) (h1 : term166 x y) : term166 x y.
Proof. exact (h1). Qed.
Lemma lem1648232 (x : real) (y : real) (h1 : term166 x y) : term73 x y.
Proof. exact (proj2 (@lem1648231 x y h1)). Qed.
Lemma lem1648234 (x : real) (y : real) (h1 : term166 x y) : term47 y.
Proof. exact (proj2 (@lem1648232 x y h1)). Qed.
Lemma lem1648235 (x : real) (y : real) (h1 : term166 x y) : term38 x y.
Proof. exact (proj1 (@lem1648232 x y h1)). Qed.
Lemma lem1648236 (x : real) (y : real) (h1 : term166 x y) : term35 y.
Proof. exact (proj2 (@lem1648235 x y h1)). Qed.
Lemma lem1648239 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648240 : term83 = term84.
Proof. exact (@lem1648239 (NUMERAL 0) term24). Qed.
Lemma lem1648241 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648242 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648243 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648242 h1) (fun h1 : term84 = True => @lem1648241)). Qed.
Lemma lem1648244 : term84 = True.
Proof. exact (EQ_MP (@lem1648243) (@lem1648241)). Qed.
Lemma lem1648245 : term83 = True.
Proof. exact (TRANS (@lem1648240) (@lem1648244)). Qed.
Lemma lem1648246 : True = term83.
Proof. exact (SYM (@lem1648245)). Qed.
Lemma lem1648247 : term83.
Proof. exact (EQ_MP (@lem1648246) (@lem0)). Qed.
Lemma lem1648248 (x : real) (y : real) (h1 : term166 x y) : term86 y.
Proof. exact (conj (@lem1648247) (@lem1648236 x y h1)). Qed.
Lemma lem1648250 (x : real) (y : real) : term87 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1648251 (y : real) : term88 y.
Proof. exact (@lem1648250 term89 y). Qed.
Lemma lem1648252 (x : real) (y : real) (h1 : term166 x y) : term90 y.
Proof. exact (@lem1648251 y (@lem1648248 x y h1)). Qed.
Lemma lem1648253 (y : real) : (term91 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1648254 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1648255 (y : real) : (term92 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1648254) (@lem1648253 y)). Qed.
Lemma lem1648256 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648257 (y : real) : (term90 y) = (term35 y).
Proof. exact (MK_COMB (@lem1648255 y) (@lem1648256)). Qed.
Lemma lem1648258 (x : real) (y : real) (h1 : term166 x y) : term35 y.
Proof. exact (EQ_MP (@lem1648257 y) (@lem1648252 x y h1)). Qed.
Lemma lem1648260 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648261 : term83 = term84.
Proof. exact (@lem1648260 (NUMERAL 0) term24). Qed.
Lemma lem1648262 : term85 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1648263 (h1 : term85 = (BIT1 0)) : term84 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1648264 : (term85 = (BIT1 0)) = (term84 = True).
Proof. exact (prop_ext (fun h1 : term85 = (BIT1 0) => @lem1648263 h1) (fun h1 : term84 = True => @lem1648262)). Qed.
Lemma lem1648265 : term84 = True.
Proof. exact (EQ_MP (@lem1648264) (@lem1648262)). Qed.
Lemma lem1648266 : term83 = True.
Proof. exact (TRANS (@lem1648261) (@lem1648265)). Qed.
Lemma lem1648267 : True = term83.
Proof. exact (SYM (@lem1648266)). Qed.
Lemma lem1648268 : term83.
Proof. exact (EQ_MP (@lem1648267) (@lem0)). Qed.
Lemma lem1648269 (x : real) (y : real) (h1 : term166 x y) : term124 y.
Proof. exact (conj (@lem1648268) (@lem1648234 x y h1)). Qed.
Lemma lem1648271 (x : real) (y : real) : term94 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1648272 (y : real) : term125 y.
Proof. exact (@lem1648271 term89 (term42 y)). Qed.
Lemma lem1648273 (x : real) (y : real) (h1 : term166 x y) : term126 y.
Proof. exact (@lem1648272 y (@lem1648269 x y h1)). Qed.
Lemma lem1648274 (y : real) : (term127 y) = (term42 y).
Proof. exact (@lem1483460 (term42 y)). Qed.
Lemma lem1648275 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648276 (y : real) : (term128 y) = (term45 y).
Proof. exact (MK_COMB (@lem1648275) (@lem1648274 y)). Qed.
Lemma lem1648277 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648278 (y : real) : (term126 y) = (term47 y).
Proof. exact (MK_COMB (@lem1648276 y) (@lem1648277)). Qed.
Lemma lem1648279 (x : real) (y : real) (h1 : term166 x y) : term47 y.
Proof. exact (EQ_MP (@lem1648278 y) (@lem1648273 x y h1)). Qed.
Lemma lem1648280 (x : real) (y : real) (h1 : term166 x y) : term129 y.
Proof. exact (conj (@lem1648279 x y h1) (@lem1648258 x y h1)). Qed.
Lemma lem1648282 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1648283 (y : real) : term131 y.
Proof. exact (@lem1648282 (term42 y) y). Qed.
Lemma lem1648284 (x : real) (y : real) (h1 : term166 x y) : term132 y.
Proof. exact (@lem1648283 y (@lem1648280 x y h1)). Qed.
Lemma lem1648285 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483440 term102 y). Qed.
Lemma lem1648287 (m : nat) : (term115 m) = term3.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1648288 : term116 = term3.
Proof. exact (@lem1648287 term24). Qed.
Lemma lem1648289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648290 : term117 = term118.
Proof. exact (MK_COMB (@lem1648289) (@lem1648288)). Qed.
Lemma lem1648291 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1648292 (y : real) : (term114 y) = (term119 y).
Proof. exact (MK_COMB (@lem1648290) (@lem1648291 y)). Qed.
Lemma lem1648293 (y : real) : (term113 y) = (term119 y).
Proof. exact (TRANS (@lem1648285 y) (@lem1648292 y)). Qed.
Lemma lem1648294 (y : real) : (term119 y) = term3.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1648295 (y : real) : (term113 y) = term3.
Proof. exact (TRANS (@lem1648293 y) (@lem1648294 y)). Qed.
Lemma lem1648296 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1648297 (y : real) : (term133 y) = term134.
Proof. exact (MK_COMB (@lem1648296) (@lem1648295 y)). Qed.
Lemma lem1648298 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648299 (y : real) : (term132 y) = term135.
Proof. exact (MK_COMB (@lem1648297 y) (@lem1648298)). Qed.
Lemma lem1648300 (x : real) (y : real) (h1 : term166 x y) : term135.
Proof. exact (EQ_MP (@lem1648299 y) (@lem1648284 x y h1)). Qed.
Lemma lem1648302 (n : nat) (m : nat) : (term82 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1648303 : term135 = term136.
Proof. exact (@lem1648302 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1648304 : term136 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1648305 : term135 = False.
Proof. exact (TRANS (@lem1648303) (@lem1648304)). Qed.
Lemma lem1648306 (x : real) (y : real) (h1 : term166 x y) : False.
Proof. exact (EQ_MP (@lem1648305) (@lem1648300 x y h1)). Qed.
Lemma lem1648307 (x : real) (y : real) (h1 : term71 x y) : False.
Proof. exact (or_elim (@lem1648085 x y h1) (fun h0 : term165 x y => @lem1648230 x y h0) (fun h0 : term166 x y => @lem1648306 x y h0)). Qed.
Lemma lem1648308 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (or_elim (@lem1647729 x y h1) (fun h0 : term75 y x => @lem1648084 y x h0) (fun h0 : term71 x y => @lem1648307 x y h0)). Qed.
Lemma lem1648310 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1648311 (x : real) (y : real) (h1 : term80 x y) : (term80 x y) = False.
Proof. exact (prop_ext (fun h2 : term80 x y => @lem1648308 x y h1) (fun h2 : False => @lem1648310 x y h1)). Qed.
Lemma lem1648312 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (EQ_MP (@lem1648311 x y h1) (@lem1648310 x y h1)). Qed.
Lemma lem1648313 (x : real) (y : real) (h1 : term18 x y) : term18 x y.
Proof. exact (h1). Qed.
Lemma lem1648314 (x : real) (y : real) (h1 : term18 x y) : term80 x y.
Proof. exact (EQ_MP (@lem1647707 x y) (@lem1648313 x y h1)). Qed.
Lemma lem1648315 (x : real) (y : real) (h1 : term18 x y) : (term80 x y) = False.
Proof. exact (prop_ext (fun h2 : term80 x y => @lem1648312 x y h2) (fun h2 : False => @lem1648314 x y h1)). Qed.
Lemma lem1648316 (x : real) (y : real) (h1 : term18 x y) : False.
Proof. exact (EQ_MP (@lem1648315 x y h1) (@lem1648314 x y h1)). Qed.
Lemma lem1648317 (x : real) (y : real) : term167 x y.
Proof. exact (fun h0 : term18 x y => @lem1648316 x y h0). Qed.
Lemma lem1648318 (x : real) (y : real) : term168 x y.
Proof. exact (@lem1386578 (term169 x y)). Qed.
Lemma lem1648320 (x : real) : term170 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1648321 (x : real) : (term170 x) = ((term159 x) = x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1648323 (x : real) : term171 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1648324 (x : real) : (term171 x) = ((term119 x) = term3).
Proof. exact (eq_refl (term171 x)). Qed.
Lemma lem1648326 (x : real) : term172 x.
Proof. exact (@lem1383497 x). Qed.
Lemma lem1648327 (x : real) : (term172 x) = ((term173 x) = (real_mul x x)).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1648334 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term174 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1648335 (p : Prop) (q : Prop) (p' : Prop) : term175 p q p'.
Proof. exact (fun q' : Prop => @lem1648334 p q p' q'). Qed.
Lemma lem1648336 (p : Prop) (q : Prop) : term176 p q.
Proof. exact (fun p' : Prop => @lem1648335 p q p'). Qed.
Lemma lem1648337 (x : real) (y : real) : term177 x y.
Proof. exact (@lem1648336 ((term178 x y) = term3) (term14 x y)). Qed.
Lemma lem1648338 (x : real) (y : real) (p' : Prop) : term179 x y p'.
Proof. exact (@lem1648337 x y p'). Qed.
Lemma lem1648339 (x : real) (y : real) (p' : Prop) : (term179 x y p') = (term180 x y p').
Proof. exact (eq_refl (term179 x y p')). Qed.
Lemma lem1648340 (x : real) (y : real) (p' : Prop) : term180 x y p'.
Proof. exact (EQ_MP (@lem1648339 x y p') (@lem1648338 x y p')). Qed.
Lemma lem1648341 (x : real) (y : real) (p' : Prop) (q' : Prop) : term181 x y p' q'.
Proof. exact (@lem1648340 x y p' q'). Qed.
Lemma lem1648342 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term181 x y p' q') = (term182 x y p' q').
Proof. exact (eq_refl (term181 x y p' q')). Qed.
Lemma lem1648343 (x : real) (y : real) (p' : Prop) (q' : Prop) : term182 x y p' q'.
Proof. exact (EQ_MP (@lem1648342 x y p' q') (@lem1648341 x y p' q')). Qed.
Lemma lem1648347 (x : real) : (term173 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1648327 x) (@lem1648326 x)). Qed.
Lemma lem1648348 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1648349 (x : real) : (term183 x) = (term184 x).
Proof. exact (MK_COMB (@lem1648348) (@lem1648347 x)). Qed.
Lemma lem1648351 (x : real) : (term173 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1648327 x) (@lem1648326 x)). Qed.
Lemma lem1648352 (y : real) : (term173 y) = (real_mul y y).
Proof. exact (@lem1648351 y). Qed.
Lemma lem1648353 (x : real) (y : real) : (term178 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1648349 x) (@lem1648352 y)). Qed.
Lemma lem1648354 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648355 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1648354) (@lem1648353 x y)). Qed.
Lemma lem1648356 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648357 (x : real) (y : real) : ((term178 x y) = term3) = ((term185 x y) = term3).
Proof. exact (MK_COMB (@lem1648355 x y) (@lem1648356)). Qed.
Lemma lem1648360 (x : real) (y : real) (q' : Prop) : term188 x y q'.
Proof. exact (@lem1648343 x y ((term185 x y) = term3) q'). Qed.
Lemma lem1648361 (x : real) (y : real) (q' : Prop) : term189 x y q'.
Proof. exact (@lem1648360 x y q' (@lem1648357 x y)). Qed.
Lemma lem1648369 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1648370 (x : real) (y : real) : term190 x y.
Proof. exact (fun h0 : (term185 x y) = term3 => @lem1648369 x y). Qed.
Lemma lem1648371 (x : real) (y : real) : term191 x y.
Proof. exact (@lem1648361 x y (term14 x y)). Qed.
Lemma lem1648372 (x : real) (y : real) : (term192 x y) = (term193 x y).
Proof. exact (@lem1648371 x y (@lem1648370 x y)). Qed.
Lemma lem1648412 (x : real) (y : real) : (term193 x y) = (term192 x y).
Proof. exact (SYM (@lem1648372 x y)). Qed.
Lemma lem1648416 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term174 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1648417 (p : Prop) (q : Prop) (p' : Prop) : term175 p q p'.
Proof. exact (fun q' : Prop => @lem1648416 p q p' q'). Qed.
Lemma lem1648418 (p : Prop) (q : Prop) : term176 p q.
Proof. exact (fun p' : Prop => @lem1648417 p q p'). Qed.
Lemma lem1648419 (x : real) (y : real) : term194 x y.
Proof. exact (@lem1648418 (term14 x y) ((term178 x y) = term3)). Qed.
Lemma lem1648420 (x : real) (y : real) (p' : Prop) : term195 x y p'.
Proof. exact (@lem1648419 x y p'). Qed.
Lemma lem1648421 (x : real) (y : real) (p' : Prop) : (term195 x y p') = (term196 x y p').
Proof. exact (eq_refl (term195 x y p')). Qed.
Lemma lem1648422 (x : real) (y : real) (p' : Prop) : term196 x y p'.
Proof. exact (EQ_MP (@lem1648421 x y p') (@lem1648420 x y p')). Qed.
Lemma lem1648423 (x : real) (y : real) (p' : Prop) (q' : Prop) : term197 x y p' q'.
Proof. exact (@lem1648422 x y p' q'). Qed.
Lemma lem1648424 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term197 x y p' q') = (term198 x y p' q').
Proof. exact (eq_refl (term197 x y p' q')). Qed.
Lemma lem1648425 (x : real) (y : real) (p' : Prop) (q' : Prop) : term198 x y p' q'.
Proof. exact (EQ_MP (@lem1648424 x y p' q') (@lem1648423 x y p' q')). Qed.
Lemma lem1648432 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1648433 (x : real) (y : real) (q' : Prop) : term199 x y q'.
Proof. exact (@lem1648425 x y (term14 x y) q'). Qed.
Lemma lem1648434 (x : real) (y : real) (q' : Prop) : term200 x y q'.
Proof. exact (@lem1648433 x y q' (@lem1648432 x y)). Qed.
Lemma lem1648435 (x : real) (y : real) (h1 : term14 x y) : term14 x y.
Proof. exact (h1). Qed.
Lemma lem1648441 (x : real) : (term173 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1648327 x) (@lem1648326 x)). Qed.
Lemma lem1648443 (x : real) (y : real) (h1 : term14 x y) : x = term3.
Proof. exact (proj1 (@lem1648435 x y h1)). Qed.
Lemma lem1648444 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648445 (x : real) (y : real) (h1 : term14 x y) : (real_mul x) = term118.
Proof. exact (MK_COMB (@lem1648444) (@lem1648443 x y h1)). Qed.
Lemma lem1648447 (x : real) (y : real) (h1 : term14 x y) : x = term3.
Proof. exact (proj1 (@lem1648435 x y h1)). Qed.
Lemma lem1648448 (x : real) (y : real) (h1 : term14 x y) : (real_mul x x) = term201.
Proof. exact (MK_COMB (@lem1648445 x y h1) (@lem1648447 x y h1)). Qed.
Lemma lem1648450 (x : real) : (term119 x) = term3.
Proof. exact (EQ_MP (@lem1648324 x) (@lem1648323 x)). Qed.
Lemma lem1648451 : term201 = term3.
Proof. exact (@lem1648450 term3). Qed.
Lemma lem1648452 (x : real) (y : real) (h1 : term14 x y) : (real_mul x x) = term3.
Proof. exact (TRANS (@lem1648448 x y h1) (@lem1648451)). Qed.
Lemma lem1648453 (x : real) (y : real) (h1 : term14 x y) : (term173 x) = term3.
Proof. exact (TRANS (@lem1648441 x) (@lem1648452 x y h1)). Qed.
Lemma lem1648454 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1648455 (x : real) (y : real) (h1 : term14 x y) : (term183 x) = term121.
Proof. exact (MK_COMB (@lem1648454) (@lem1648453 x y h1)). Qed.
Lemma lem1648457 (x : real) : (term173 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1648327 x) (@lem1648326 x)). Qed.
Lemma lem1648458 (y : real) : (term173 y) = (real_mul y y).
Proof. exact (@lem1648457 y). Qed.
Lemma lem1648460 (x : real) (y : real) (h1 : term14 x y) : y = term3.
Proof. exact (proj2 (@lem1648435 x y h1)). Qed.
Lemma lem1648461 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1648462 (x : real) (y : real) (h1 : term14 x y) : (real_mul y) = term118.
Proof. exact (MK_COMB (@lem1648461) (@lem1648460 x y h1)). Qed.
Lemma lem1648464 (x : real) (y : real) (h1 : term14 x y) : y = term3.
Proof. exact (proj2 (@lem1648435 x y h1)). Qed.
Lemma lem1648465 (x : real) (y : real) (h1 : term14 x y) : (real_mul y y) = term201.
Proof. exact (MK_COMB (@lem1648462 x y h1) (@lem1648464 x y h1)). Qed.
Lemma lem1648467 (x : real) : (term119 x) = term3.
Proof. exact (EQ_MP (@lem1648324 x) (@lem1648323 x)). Qed.
Lemma lem1648468 : term201 = term3.
Proof. exact (@lem1648467 term3). Qed.
Lemma lem1648469 (x : real) (y : real) (h1 : term14 x y) : (real_mul y y) = term3.
Proof. exact (TRANS (@lem1648465 x y h1) (@lem1648468)). Qed.
Lemma lem1648470 (x : real) (y : real) (h1 : term14 x y) : (term173 y) = term3.
Proof. exact (TRANS (@lem1648458 y) (@lem1648469 x y h1)). Qed.
Lemma lem1648471 (x : real) (y : real) (h1 : term14 x y) : (term178 x y) = term202.
Proof. exact (MK_COMB (@lem1648455 x y h1) (@lem1648470 x y h1)). Qed.
Lemma lem1648473 (x : real) : (term159 x) = x.
Proof. exact (EQ_MP (@lem1648321 x) (@lem1648320 x)). Qed.
Lemma lem1648474 : term202 = term3.
Proof. exact (@lem1648473 term3). Qed.
Lemma lem1648475 (x : real) (y : real) (h1 : term14 x y) : (term178 x y) = term3.
Proof. exact (TRANS (@lem1648471 x y h1) (@lem1648474)). Qed.
Lemma lem1648476 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1648477 (x : real) (y : real) (h1 : term14 x y) : (term186 x y) = term203.
Proof. exact (MK_COMB (@lem1648476) (@lem1648475 x y h1)). Qed.
Lemma lem1648478 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1648479 (x : real) (y : real) (h1 : term14 x y) : ((term178 x y) = term3) = (term3 = term3).
Proof. exact (MK_COMB (@lem1648477 x y h1) (@lem1648478)). Qed.
Lemma lem1648481 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1648482 (x : real) : (x = x) = True.
Proof. exact (@lem1648481 real x). Qed.
Lemma lem1648483 : (term3 = term3) = True.
Proof. exact (@lem1648482 term3). Qed.
Lemma lem1648484 (x : real) (y : real) (h1 : term14 x y) : ((term178 x y) = term3) = True.
Proof. exact (TRANS (@lem1648479 x y h1) (@lem1648483)). Qed.
Lemma lem1648485 (x : real) (y : real) : term204 x y.
Proof. exact (fun h0 : term14 x y => @lem1648484 x y h0). Qed.
Lemma lem1648486 (x : real) (y : real) : term205 x y.
Proof. exact (@lem1648434 x y True). Qed.
Lemma lem1648487 (x : real) (y : real) : (term206 x y) = (term207 x y).
Proof. exact (@lem1648486 x y (@lem1648485 x y)). Qed.
Lemma lem1648489 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1648490 (x : real) (y : real) : (term207 x y) = True.
Proof. exact (@lem1648489 (term14 x y)). Qed.
Lemma lem1648491 (x : real) (y : real) : (term206 x y) = True.
Proof. exact (TRANS (@lem1648487 x y) (@lem1648490 x y)). Qed.
Lemma lem1648492 (x : real) (y : real) : True = (term206 x y).
Proof. exact (SYM (@lem1648491 x y)). Qed.
Lemma lem1648493 (x : real) (y : real) : term206 x y.
Proof. exact (EQ_MP (@lem1648492 x y) (@lem0)). Qed.
Lemma lem1648494 (x : real) (y : real) (h1 : (term185 x y) = term3) : (term185 x y) = term3.
Proof. exact (h1). Qed.
Lemma lem1648496 (x : real) (y : real) : term169 x y.
Proof. exact (@lem1648318 x y (@lem1648317 x y)). Qed.
Lemma lem1648497 (x : real) (y : real) : term208 x y.
Proof. exact (@lem1648496 (real_mul x x) (real_mul y y)). Qed.
Lemma lem1648498 (x : real) (y : real) (h1 : (term185 x y) = term3) : term209 x y.
Proof. exact (@lem1648497 x y (@lem1648494 x y h1)). Qed.
Lemma lem1648506 (x : real) : (term6 x) = True.
Proof. exact (EQ_MP (@lem1647421 x) (@lem1647420 x)). Qed.
Lemma lem1648507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1648508 (x : real) : (term210 x) = (and True).
Proof. exact (MK_COMB (@lem1648507) (@lem1648506 x)). Qed.
Lemma lem1648510 (x : real) : (term6 x) = True.
Proof. exact (EQ_MP (@lem1647421 x) (@lem1647420 x)). Qed.
Lemma lem1648511 (y : real) : (term6 y) = True.
Proof. exact (@lem1648510 y). Qed.
Lemma lem1648512 (x : real) (y : real) : (term211 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1648508 x) (@lem1648511 y)). Qed.
Lemma lem1648514 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1648515 : (True /\ True) = True.
Proof. exact (@lem1648514 True). Qed.
Lemma lem1648516 (x : real) (y : real) : (term211 x y) = True.
Proof. exact (TRANS (@lem1648512 x y) (@lem1648515)). Qed.
Lemma lem1648517 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1648518 (x : real) (y : real) : (term212 x y) = (imp True).
Proof. exact (MK_COMB (@lem1648517) (@lem1648516 x y)). Qed.
Lemma lem1648522 (x : real) (y : real) : ((real_mul x y) = term3) = (term4 x y).
Proof. exact (EQ_MP (@lem1647416 x y) (@lem1647415 x y)). Qed.
Lemma lem1648523 (x : real) : ((real_mul x x) = term3) = (term213 x).
Proof. exact (@lem1648522 x x). Qed.
Lemma lem1648525 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem1648526 (x : real) : (term213 x) = (x = term3).
Proof. exact (@lem1648525 (x = term3)). Qed.
Lemma lem1648529 (x : real) : ((real_mul x x) = term3) = (x = term3).
Proof. exact (TRANS (@lem1648523 x) (@lem1648526 x)). Qed.
Lemma lem1648530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1648531 (x : real) : (term214 x) = (term215 x).
Proof. exact (MK_COMB (@lem1648530) (@lem1648529 x)). Qed.
Lemma lem1648533 (x : real) (y : real) : ((real_mul x y) = term3) = (term4 x y).
Proof. exact (EQ_MP (@lem1647416 x y) (@lem1647415 x y)). Qed.
Lemma lem1648534 (y : real) : ((real_mul y y) = term3) = (term213 y).
Proof. exact (@lem1648533 y y). Qed.
Lemma lem1648536 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem1648537 (y : real) : (term213 y) = (y = term3).
Proof. exact (@lem1648536 (y = term3)). Qed.
Lemma lem1648540 (y : real) : ((real_mul y y) = term3) = (y = term3).
Proof. exact (TRANS (@lem1648534 y) (@lem1648537 y)). Qed.
Lemma lem1648541 (x : real) (y : real) : (term216 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1648531 x) (@lem1648540 y)). Qed.
Lemma lem1648544 (x : real) (y : real) : (term209 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1648518 x y) (@lem1648541 x y)). Qed.
Lemma lem1648546 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1648547 (x : real) (y : real) : (term217 x y) = (term14 x y).
Proof. exact (@lem1648546 (term14 x y)). Qed.
Lemma lem1648554 (x : real) (y : real) : (term209 x y) = (term14 x y).
Proof. exact (TRANS (@lem1648544 x y) (@lem1648547 x y)). Qed.
Lemma lem1648555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1648556 (x : real) (y : real) : (term218 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1648555) (@lem1648554 x y)). Qed.
Lemma lem1648563 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1648564 (x : real) (y : real) : (term220 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1648556 x y) (@lem1648563 x y)). Qed.
Lemma lem1648566 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1648567 (x : real) (y : real) : (term221 x y) = True.
Proof. exact (@lem1648566 (term14 x y)). Qed.
Lemma lem1648568 (x : real) (y : real) : (term220 x y) = True.
Proof. exact (TRANS (@lem1648564 x y) (@lem1648567 x y)). Qed.
Lemma lem1648569 (x : real) (y : real) : True = (term220 x y).
Proof. exact (SYM (@lem1648568 x y)). Qed.
Lemma lem1648570 (x : real) (y : real) : term220 x y.
Proof. exact (EQ_MP (@lem1648569 x y) (@lem0)). Qed.
Lemma lem1648571 (x : real) (y : real) (h1 : (term185 x y) = term3) : term14 x y.
Proof. exact (@lem1648570 x y (@lem1648498 x y h1)). Qed.
Lemma lem1648572 (x : real) (y : real) : term193 x y.
Proof. exact (fun h0 : (term185 x y) = term3 => @lem1648571 x y h0). Qed.
Lemma lem1648573 (x : real) (y : real) : term192 x y.
Proof. exact (EQ_MP (@lem1648412 x y) (@lem1648572 x y)). Qed.
Lemma lem1648574 (x : real) (y : real) : term222 x y.
Proof. exact (conj (@lem1648573 x y) (@lem1648493 x y)). Qed.
Lemma lem1648575 (x : real) (y : real) : (term222 x y) = (((term178 x y) = term3) = (term14 x y)).
Proof. exact (@lem32 ((term178 x y) = term3) (term14 x y)). Qed.
Lemma lem1648576 (x : real) (y : real) : ((term178 x y) = term3) = (term14 x y).
Proof. exact (EQ_MP (@lem1648575 x y) (@lem1648574 x y)). Qed.
Lemma lem1648581 (x : real) : term223 x.
Proof. exact (fun y : real => @lem1648576 x y). Qed.
Lemma lem1648586 : term224.
Proof. exact (fun x : real => @lem1648581 x). Qed.

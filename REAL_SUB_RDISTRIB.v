Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_RDISTRIB_term_abbrevs.
Require Import thm1008952_spec.
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
Require Import thm1483452_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1526461 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526462 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (@lem1526461 (term4 x y)). Qed.
Lemma lem1526463 (x : real) (y : real) (z : real) : (term5 x y z) = ((term6 x y z) = (term7 x y z)).
Proof. exact (eq_refl (term5 x y z)). Qed.
Lemma lem1526464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526466 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1526464) (@lem1526463 x y z)). Qed.
Lemma lem1526467 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1526466 x y z)). Qed.
Lemma lem1526468 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526469 (x : real) (y : real) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1526468) (@lem1526467 x y)). Qed.
Lemma lem1526470 (x : real) (y : real) : (term2 x y) = (term12 x y).
Proof. exact (TRANS (@lem1526462 x y) (@lem1526469 x y)). Qed.
Lemma lem1526471 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526472 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1526471 (term15 x)). Qed.
Lemma lem1526473 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1526474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526475 (x : real) (y : real) : (term18 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1526474) (@lem1526473 x y)). Qed.
Lemma lem1526476 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1526475 x y) (@lem1526470 x y)). Qed.
Lemma lem1526477 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1526476 x y)). Qed.
Lemma lem1526478 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526479 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1526478) (@lem1526477 x)). Qed.
Lemma lem1526480 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1526472 x) (@lem1526479 x)). Qed.
Lemma lem1526481 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526482 : term22 = term23.
Proof. exact (@lem1526481 term24). Qed.
Lemma lem1526483 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1526484 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526485 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1526484) (@lem1526483 x)). Qed.
Lemma lem1526486 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1526485 x) (@lem1526480 x)). Qed.
Lemma lem1526487 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1526486 x)). Qed.
Lemma lem1526488 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526489 : term23 = term30.
Proof. exact (MK_COMB (@lem1526488) (@lem1526487)). Qed.
Lemma lem1526491 : term22 = term30.
Proof. exact (TRANS (@lem1526482) (@lem1526489)). Qed.
Lemma lem1526494 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1526495 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1526494 x y z)). Qed.
Lemma lem1526496 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526497 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1526496) (@lem1526495 x y)). Qed.
Lemma lem1526498 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1526497 x y)). Qed.
Lemma lem1526499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526500 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1526499) (@lem1526498 x)). Qed.
Lemma lem1526501 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1526500 x)). Qed.
Lemma lem1526502 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526503 : term30 = term30.
Proof. exact (MK_COMB (@lem1526502) (@lem1526501)). Qed.
Lemma lem1526504 : term22 = term30.
Proof. exact (TRANS (@lem1526491) (@lem1526503)). Qed.
Lemma lem1526505 (x : real) (y : real) (z : real) : (term9 x y z) = (term31 x y z).
Proof. exact (@lem1483554 (term6 x y z) (term7 x y z)). Qed.
Lemma lem1526530 (x : real) (y : real) (z : real) : (term7 x y z) = (term32 x y z).
Proof. exact (@lem1483519 (real_mul x z) (real_mul y z)). Qed.
Lemma lem1526531 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1526544 (x : real) (y : real) : (real_sub x y) = (term33 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1526545 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526546 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1526545) (@lem1526544 x y)). Qed.
Lemma lem1526547 (x : real) (y : real) (z : real) : (term6 x y z) = (term36 x y z).
Proof. exact (MK_COMB (@lem1526546 x y) (@lem1526531 z)). Qed.
Lemma lem1526548 (z : real) (x : real) (y : real) : (term36 x y z) = (term37 z x y).
Proof. exact (@lem1483452 z (term33 x y)). Qed.
Lemma lem1526549 (x : real) (z : real) (y : real) : (term37 z x y) = (term38 x z y).
Proof. exact (@lem1483508 x z (term39 y)). Qed.
Lemma lem1526550 (z : real) (y : real) : (term40 z y) = (term41 z y).
Proof. exact (@lem1483478 term42 z y). Qed.
Lemma lem1526551 (y : real) (z : real) : (real_mul z y) = (real_mul y z).
Proof. exact (@lem1483474 y z). Qed.
Lemma lem1526552 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1526553 (y : real) (z : real) : (term41 z y) = (term41 y z).
Proof. exact (MK_COMB (@lem1526552) (@lem1526551 y z)). Qed.
Lemma lem1526554 (y : real) (z : real) : (term40 z y) = (term41 y z).
Proof. exact (TRANS (@lem1526550 z y) (@lem1526553 y z)). Qed.
Lemma lem1526555 (x : real) (z : real) : (real_mul z x) = (real_mul x z).
Proof. exact (@lem1483474 x z). Qed.
Lemma lem1526556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1526557 (x : real) (z : real) : (term44 z x) = (term44 x z).
Proof. exact (MK_COMB (@lem1526556) (@lem1526555 x z)). Qed.
Lemma lem1526558 (x : real) (y : real) (z : real) : (term38 x z y) = (term32 x y z).
Proof. exact (MK_COMB (@lem1526557 x z) (@lem1526554 y z)). Qed.
Lemma lem1526559 (x : real) (y : real) (z : real) : (term37 z x y) = (term32 x y z).
Proof. exact (TRANS (@lem1526549 x z y) (@lem1526558 x y z)). Qed.
Lemma lem1526560 (x : real) (y : real) (z : real) : (term36 x y z) = (term32 x y z).
Proof. exact (TRANS (@lem1526548 z x y) (@lem1526559 x y z)). Qed.
Lemma lem1526561 (x : real) (y : real) (z : real) : (term6 x y z) = (term32 x y z).
Proof. exact (TRANS (@lem1526547 x y z) (@lem1526560 x y z)). Qed.
Lemma lem1526562 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1526563 (x : real) (y : real) (z : real) : (term45 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1526562) (@lem1526561 x y z)). Qed.
Lemma lem1526564 (x : real) (y : real) (z : real) : (term47 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem1526563 x y z) (@lem1526530 x y z)). Qed.
Lemma lem1526565 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (@lem1483519 (term32 x y z) (term32 x y z)). Qed.
Lemma lem1526566 (x : real) (y : real) (z : real) : (term50 x y z) = (term51 x y z).
Proof. exact (@lem1483508 (real_mul x z) term42 (term41 y z)). Qed.
Lemma lem1526567 (y : real) (z : real) : (term52 y z) = (term53 y z).
Proof. exact (@lem1483476 term42 term42 (real_mul y z)). Qed.
Lemma lem1526569 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1526570 : term56 = term57.
Proof. exact (@lem1526569 term58 term58). Qed.
Lemma lem1526571 : (term59 = (BIT1 0)) = (term60 = term58).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1526572 : term60 = term58.
Proof. exact (EQ_MP (@lem1526571) (@lem940073)). Qed.
Lemma lem1526573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1526574 : term57 = term61.
Proof. exact (MK_COMB (@lem1526573) (@lem1526572)). Qed.
Lemma lem1526575 : term56 = term61.
Proof. exact (TRANS (@lem1526570) (@lem1526574)). Qed.
Lemma lem1526576 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526577 : term62 = term63.
Proof. exact (MK_COMB (@lem1526576) (@lem1526575)). Qed.
Lemma lem1526578 (y : real) (z : real) : (real_mul y z) = (real_mul y z).
Proof. exact (eq_refl (real_mul y z)). Qed.
Lemma lem1526579 (y : real) (z : real) : (term53 y z) = (term64 y z).
Proof. exact (MK_COMB (@lem1526577) (@lem1526578 y z)). Qed.
Lemma lem1526580 (y : real) (z : real) : (term52 y z) = (term64 y z).
Proof. exact (TRANS (@lem1526567 y z) (@lem1526579 y z)). Qed.
Lemma lem1526581 (y : real) (z : real) : (term64 y z) = (real_mul y z).
Proof. exact (@lem1483436 (real_mul y z)). Qed.
Lemma lem1526582 (y : real) (z : real) : (term52 y z) = (real_mul y z).
Proof. exact (TRANS (@lem1526580 y z) (@lem1526581 y z)). Qed.
Lemma lem1526585 (x : real) (z : real) : (term65 x z) = (term65 x z).
Proof. exact (eq_refl (term65 x z)). Qed.
Lemma lem1526586 (x : real) (y : real) (z : real) : (term51 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1526585 x z) (@lem1526582 y z)). Qed.
Lemma lem1526587 (x : real) (y : real) (z : real) : (term50 x y z) = (term66 x y z).
Proof. exact (TRANS (@lem1526566 x y z) (@lem1526586 x y z)). Qed.
Lemma lem1526588 (x : real) (y : real) (z : real) : (term67 x y z) = (term67 x y z).
Proof. exact (eq_refl (term67 x y z)). Qed.
Lemma lem1526589 (x : real) (y : real) (z : real) : (term49 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1526588 x y z) (@lem1526587 x y z)). Qed.
Lemma lem1526590 (x : real) (y : real) (z : real) : (term68 x y z) = (term69 x y z).
Proof. exact (@lem1483480 (real_mul x z) (term41 x z) (term41 y z) (real_mul y z)). Qed.
Lemma lem1526591 (x : real) (z : real) : (term70 x z) = (term71 x z).
Proof. exact (@lem1483442 term42 (real_mul x z)). Qed.
Lemma lem1526593 (m : nat) : (term72 m) = term73.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526594 : term74 = term73.
Proof. exact (@lem1526593 term58). Qed.
Lemma lem1526595 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526596 : term75 = term76.
Proof. exact (MK_COMB (@lem1526595) (@lem1526594)). Qed.
Lemma lem1526597 (x : real) (z : real) : (real_mul x z) = (real_mul x z).
Proof. exact (eq_refl (real_mul x z)). Qed.
Lemma lem1526598 (x : real) (z : real) : (term71 x z) = (term77 x z).
Proof. exact (MK_COMB (@lem1526596) (@lem1526597 x z)). Qed.
Lemma lem1526599 (x : real) (z : real) : (term70 x z) = (term77 x z).
Proof. exact (TRANS (@lem1526591 x z) (@lem1526598 x z)). Qed.
Lemma lem1526600 (x : real) (z : real) : (term77 x z) = term73.
Proof. exact (@lem1483446 (real_mul x z)). Qed.
Lemma lem1526601 (x : real) (z : real) : (term70 x z) = term73.
Proof. exact (TRANS (@lem1526599 x z) (@lem1526600 x z)). Qed.
Lemma lem1526602 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1526603 (x : real) (z : real) : (term78 x z) = term79.
Proof. exact (MK_COMB (@lem1526602) (@lem1526601 x z)). Qed.
Lemma lem1526604 (y : real) (z : real) : (term80 y z) = (term71 y z).
Proof. exact (@lem1483440 term42 (real_mul y z)). Qed.
Lemma lem1526606 (m : nat) : (term72 m) = term73.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526607 : term74 = term73.
Proof. exact (@lem1526606 term58). Qed.
Lemma lem1526608 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526609 : term75 = term76.
Proof. exact (MK_COMB (@lem1526608) (@lem1526607)). Qed.
Lemma lem1526610 (y : real) (z : real) : (real_mul y z) = (real_mul y z).
Proof. exact (eq_refl (real_mul y z)). Qed.
Lemma lem1526611 (y : real) (z : real) : (term71 y z) = (term77 y z).
Proof. exact (MK_COMB (@lem1526609) (@lem1526610 y z)). Qed.
Lemma lem1526612 (y : real) (z : real) : (term80 y z) = (term77 y z).
Proof. exact (TRANS (@lem1526604 y z) (@lem1526611 y z)). Qed.
Lemma lem1526613 (y : real) (z : real) : (term77 y z) = term73.
Proof. exact (@lem1483446 (real_mul y z)). Qed.
Lemma lem1526614 (y : real) (z : real) : (term80 y z) = term73.
Proof. exact (TRANS (@lem1526612 y z) (@lem1526613 y z)). Qed.
Lemma lem1526615 (x : real) (y : real) (z : real) : (term69 x y z) = term81.
Proof. exact (MK_COMB (@lem1526603 x z) (@lem1526614 y z)). Qed.
Lemma lem1526616 (x : real) (y : real) (z : real) : (term68 x y z) = term81.
Proof. exact (TRANS (@lem1526590 x y z) (@lem1526615 x y z)). Qed.
Lemma lem1526617 : term81 = term73.
Proof. exact (@lem1483448 term73). Qed.
Lemma lem1526618 (x : real) (y : real) (z : real) : (term68 x y z) = term73.
Proof. exact (TRANS (@lem1526616 x y z) (@lem1526617)). Qed.
Lemma lem1526619 (x : real) (y : real) (z : real) : (term49 x y z) = term73.
Proof. exact (TRANS (@lem1526589 x y z) (@lem1526618 x y z)). Qed.
Lemma lem1526620 (x : real) (y : real) (z : real) : (term48 x y z) = term73.
Proof. exact (TRANS (@lem1526565 x y z) (@lem1526619 x y z)). Qed.
Lemma lem1526621 (x : real) (y : real) (z : real) : (term47 x y z) = term73.
Proof. exact (TRANS (@lem1526564 x y z) (@lem1526620 x y z)). Qed.
Lemma lem1526622 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1526623 (x : real) (y : real) (z : real) : (term82 x y z) = term83.
Proof. exact (MK_COMB (@lem1526622) (@lem1526621 x y z)). Qed.
Lemma lem1526624 : term83 = term84.
Proof. exact (@lem1483512 term73). Qed.
Lemma lem1526626 (x : nat) : (term85 x) = term73.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526627 : term84 = term73.
Proof. exact (@lem1526626 term58). Qed.
Lemma lem1526628 : term83 = term73.
Proof. exact (TRANS (@lem1526624) (@lem1526627)). Qed.
Lemma lem1526629 (x : real) (y : real) (z : real) : (term86 x y z) = (term86 x y z).
Proof. exact (eq_refl (term86 x y z)). Qed.
Lemma lem1526630 (x : real) (y : real) (z : real) : ((term82 x y z) = term83) = ((term82 x y z) = term73).
Proof. exact (MK_COMB (@lem1526629 x y z) (@lem1526628)). Qed.
Lemma lem1526631 (x : real) (y : real) (z : real) : (term82 x y z) = term73.
Proof. exact (EQ_MP (@lem1526630 x y z) (@lem1526623 x y z)). Qed.
Lemma lem1526632 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526633 (x : real) (y : real) (z : real) : (term87 x y z) = term88.
Proof. exact (MK_COMB (@lem1526632) (@lem1526631 x y z)). Qed.
Lemma lem1526634 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1526635 (x : real) (y : real) (z : real) : (term89 x y z) = term90.
Proof. exact (MK_COMB (@lem1526633 x y z) (@lem1526634)). Qed.
Lemma lem1526636 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526637 (x : real) (y : real) (z : real) : (term91 x y z) = term88.
Proof. exact (MK_COMB (@lem1526636) (@lem1526621 x y z)). Qed.
Lemma lem1526638 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1526639 (x : real) (y : real) (z : real) : (term92 x y z) = term90.
Proof. exact (MK_COMB (@lem1526637 x y z) (@lem1526638)). Qed.
Lemma lem1526640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526641 (x : real) (y : real) (z : real) : (term93 x y z) = term94.
Proof. exact (MK_COMB (@lem1526640) (@lem1526639 x y z)). Qed.
Lemma lem1526642 (x : real) (y : real) (z : real) : (term31 x y z) = term95.
Proof. exact (MK_COMB (@lem1526641 x y z) (@lem1526635 x y z)). Qed.
Lemma lem1526643 (x : real) (y : real) (z : real) : (term9 x y z) = term95.
Proof. exact (TRANS (@lem1526505 x y z) (@lem1526642 x y z)). Qed.
Lemma lem1526644 (x : real) (y : real) : (term11 x y) = term96.
Proof. exact (fun_ext (fun z : real => @lem1526643 x y z)). Qed.
Lemma lem1526645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526646 (x : real) (y : real) : (term12 x y) = term97.
Proof. exact (MK_COMB (@lem1526645) (@lem1526644 x y)). Qed.
Lemma lem1526647 (x : real) : (term20 x) = term98.
Proof. exact (fun_ext (fun y : real => @lem1526646 x y)). Qed.
Lemma lem1526648 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526649 (x : real) : (term21 x) = term99.
Proof. exact (MK_COMB (@lem1526648) (@lem1526647 x)). Qed.
Lemma lem1526650 : term29 = term100.
Proof. exact (fun_ext (fun x : real => @lem1526649 x)). Qed.
Lemma lem1526651 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526652 : term30 = term101.
Proof. exact (MK_COMB (@lem1526651) (@lem1526650)). Qed.
Lemma lem1526653 : term22 = term101.
Proof. exact (TRANS (@lem1526504) (@lem1526652)). Qed.
Lemma lem1526655 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526656 (t : Prop) : (term103 t) = t.
Proof. exact (@lem1526655 real t). Qed.
Lemma lem1526657 : term101 = term99.
Proof. exact (@lem1526656 term99). Qed.
Lemma lem1526659 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526660 (t : Prop) : (term103 t) = t.
Proof. exact (@lem1526659 real t). Qed.
Lemma lem1526661 : term99 = term97.
Proof. exact (@lem1526660 term97). Qed.
Lemma lem1526663 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1526664 (P : real -> Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1526663 real P Q). Qed.
Lemma lem1526665 : term108 = term109.
Proof. exact (@lem1526664 term110 term110). Qed.
Lemma lem1526666 (z : real) : (term111 z) = term90.
Proof. exact (eq_refl (term111 z)). Qed.
Lemma lem1526667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526668 (z : real) : (term112 z) = term94.
Proof. exact (MK_COMB (@lem1526667) (@lem1526666 z)). Qed.
Lemma lem1526669 (z : real) : (term111 z) = term90.
Proof. exact (eq_refl (term111 z)). Qed.
Lemma lem1526670 (z : real) : (term113 z) = term95.
Proof. exact (MK_COMB (@lem1526668 z) (@lem1526669 z)). Qed.
Lemma lem1526671 : term114 = term96.
Proof. exact (fun_ext (fun z : real => @lem1526670 z)). Qed.
Lemma lem1526672 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526673 : term108 = term97.
Proof. exact (MK_COMB (@lem1526672) (@lem1526671)). Qed.
Lemma lem1526674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1526675 : term115 = term116.
Proof. exact (MK_COMB (@lem1526674) (@lem1526673)). Qed.
Lemma lem1526676 (z : real) : (term111 z) = term90.
Proof. exact (eq_refl (term111 z)). Qed.
Lemma lem1526677 : term117 = term110.
Proof. exact (fun_ext (fun z : real => @lem1526676 z)). Qed.
Lemma lem1526678 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526679 : term118 = term119.
Proof. exact (MK_COMB (@lem1526678) (@lem1526677)). Qed.
Lemma lem1526680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526681 : term120 = term121.
Proof. exact (MK_COMB (@lem1526680) (@lem1526679)). Qed.
Lemma lem1526682 (z : real) : (term111 z) = term90.
Proof. exact (eq_refl (term111 z)). Qed.
Lemma lem1526683 : term117 = term110.
Proof. exact (fun_ext (fun z : real => @lem1526682 z)). Qed.
Lemma lem1526684 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526685 : term118 = term119.
Proof. exact (MK_COMB (@lem1526684) (@lem1526683)). Qed.
Lemma lem1526686 : term109 = term122.
Proof. exact (MK_COMB (@lem1526681) (@lem1526685)). Qed.
Lemma lem1526687 : (term108 = term109) = (term97 = term122).
Proof. exact (MK_COMB (@lem1526675) (@lem1526686)). Qed.
Lemma lem1526688 : term97 = term122.
Proof. exact (EQ_MP (@lem1526687) (@lem1526665)). Qed.
Lemma lem1526689 : term99 = term122.
Proof. exact (TRANS (@lem1526661) (@lem1526688)). Qed.
Lemma lem1526690 : term101 = term122.
Proof. exact (TRANS (@lem1526657) (@lem1526689)). Qed.
Lemma lem1526692 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526693 (t : Prop) : (term103 t) = t.
Proof. exact (@lem1526692 real t). Qed.
Lemma lem1526694 : term119 = term90.
Proof. exact (@lem1526693 term90). Qed.
Lemma lem1526695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526696 : term121 = term94.
Proof. exact (MK_COMB (@lem1526695) (@lem1526694)). Qed.
Lemma lem1526698 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1526699 (t : Prop) : (term103 t) = t.
Proof. exact (@lem1526698 real t). Qed.
Lemma lem1526700 : term119 = term90.
Proof. exact (@lem1526699 term90). Qed.
Lemma lem1526701 : term122 = term95.
Proof. exact (MK_COMB (@lem1526696) (@lem1526700)). Qed.
Lemma lem1526704 : term101 = term95.
Proof. exact (TRANS (@lem1526690) (@lem1526701)). Qed.
Lemma lem1526713 : term22 = term95.
Proof. exact (TRANS (@lem1526653) (@lem1526704)). Qed.
Lemma lem1526723 (h1 : term95) : term95.
Proof. exact (h1). Qed.
Lemma lem1526724 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem1526726 (n : nat) (m : nat) : (term123 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526727 : term90 = term124.
Proof. exact (@lem1526726 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526728 : term124 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526729 : term90 = False.
Proof. exact (TRANS (@lem1526727) (@lem1526728)). Qed.
Lemma lem1526730 (h1 : term90) : False.
Proof. exact (EQ_MP (@lem1526729) (@lem1526724 h1)). Qed.
Lemma lem1526731 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem1526733 (n : nat) (m : nat) : (term123 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526734 : term90 = term124.
Proof. exact (@lem1526733 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526735 : term124 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526736 : term90 = False.
Proof. exact (TRANS (@lem1526734) (@lem1526735)). Qed.
Lemma lem1526737 (h1 : term90) : False.
Proof. exact (EQ_MP (@lem1526736) (@lem1526731 h1)). Qed.
Lemma lem1526738 (h1 : term95) : False.
Proof. exact (or_elim (@lem1526723 h1) (fun h0 : term90 => @lem1526730 h0) (fun h0 : term90 => @lem1526737 h0)). Qed.
Lemma lem1526740 (h1 : term95) : term95.
Proof. exact (h1). Qed.
Lemma lem1526741 (h1 : term95) : term95 = False.
Proof. exact (prop_ext (fun h2 : term95 => @lem1526738 h1) (fun h2 : False => @lem1526740 h1)). Qed.
Lemma lem1526742 (h1 : term95) : False.
Proof. exact (EQ_MP (@lem1526741 h1) (@lem1526740 h1)). Qed.
Lemma lem1526743 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1526744 (h1 : term22) : term95.
Proof. exact (EQ_MP (@lem1526713) (@lem1526743 h1)). Qed.
Lemma lem1526745 (h1 : term22) : term95 = False.
Proof. exact (prop_ext (fun h2 : term95 => @lem1526742 h2) (fun h2 : False => @lem1526744 h1)). Qed.
Lemma lem1526746 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1526745 h1) (@lem1526744 h1)). Qed.
Lemma lem1526747 : term125.
Proof. exact (fun h0 : term22 => @lem1526746 h0). Qed.
Lemma lem1526748 : term126.
Proof. exact (@lem1386578 term127). Qed.
Lemma lem1526749 : term127.
Proof. exact (@lem1526748 (@lem1526747)). Qed.

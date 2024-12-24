Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_ARCH_SIMPLE_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1340339_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483484_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483578_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1698455 (x : real) (n : real) : (term0 x n) = (term1 x n).
Proof. exact (@lem17362 (real_le x n) (term2 x n)). Qed.
Lemma lem1698456 (n : real) (x : real) : (real_le x n) = (term3 n x).
Proof. exact (@lem1483523 n x). Qed.
Lemma lem1698469 (n : real) (x : real) : (real_sub n x) = (term4 n x).
Proof. exact (@lem1483519 n x). Qed.
Lemma lem1698470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1698471 (n : real) (x : real) : (term5 n x) = (term6 n x).
Proof. exact (MK_COMB (@lem1698470) (@lem1698469 n x)). Qed.
Lemma lem1698472 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1698473 (n : real) (x : real) : (term3 n x) = (term8 n x).
Proof. exact (MK_COMB (@lem1698471 n x) (@lem1698472)). Qed.
Lemma lem1698474 (n : real) (x : real) : (real_le x n) = (term8 n x).
Proof. exact (TRANS (@lem1698456 n x) (@lem1698473 n x)). Qed.
Lemma lem1698475 (x : real) (n : real) : (term9 x n) = (term10 x n).
Proof. exact (@lem1483531 x (term11 n)). Qed.
Lemma lem1698487 (x : real) (n : real) : (term12 x n) = (term13 x n).
Proof. exact (@lem1483519 x (term11 n)). Qed.
Lemma lem1698488 (n : real) : (term14 n) = (term15 n).
Proof. exact (@lem1483508 n term16 term17). Qed.
Lemma lem1698490 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1698491 : term20 = term21.
Proof. exact (@lem1698490 term22 term22). Qed.
Lemma lem1698492 : (term23 = (BIT1 0)) = (term24 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1698493 : term24 = term22.
Proof. exact (EQ_MP (@lem1698492) (@lem940073)). Qed.
Lemma lem1698494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1698495 : term25 = term17.
Proof. exact (MK_COMB (@lem1698494) (@lem1698493)). Qed.
Lemma lem1698496 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1698497 : term21 = term16.
Proof. exact (MK_COMB (@lem1698496) (@lem1698495)). Qed.
Lemma lem1698498 : term20 = term16.
Proof. exact (TRANS (@lem1698491) (@lem1698497)). Qed.
Lemma lem1698501 (n : real) : (term26 n) = (term26 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem1698502 (n : real) : (term15 n) = (term27 n).
Proof. exact (MK_COMB (@lem1698501 n) (@lem1698498)). Qed.
Lemma lem1698503 (n : real) : (term14 n) = (term27 n).
Proof. exact (TRANS (@lem1698488 n) (@lem1698502 n)). Qed.
Lemma lem1698504 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1698505 (x : real) (n : real) : (term13 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem1698504 x) (@lem1698503 n)). Qed.
Lemma lem1698510 (n : real) (x : real) : (term28 x n) = (term29 n x).
Proof. exact (@lem1483484 (term30 n) x term16). Qed.
Lemma lem1698511 (n : real) (x : real) : (term13 x n) = (term29 n x).
Proof. exact (TRANS (@lem1698505 x n) (@lem1698510 n x)). Qed.
Lemma lem1698513 (n : real) (x : real) : (term12 x n) = (term29 n x).
Proof. exact (TRANS (@lem1698487 x n) (@lem1698511 n x)). Qed.
Lemma lem1698514 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1698515 (n : real) (x : real) : (term31 x n) = (term32 n x).
Proof. exact (MK_COMB (@lem1698514) (@lem1698513 n x)). Qed.
Lemma lem1698516 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1698517 (n : real) (x : real) : (term10 x n) = (term33 n x).
Proof. exact (MK_COMB (@lem1698515 n x) (@lem1698516)). Qed.
Lemma lem1698518 (n : real) (x : real) : (term9 x n) = (term33 n x).
Proof. exact (TRANS (@lem1698475 x n) (@lem1698517 n x)). Qed.
Lemma lem1698519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1698520 (n : real) (x : real) : (term34 x n) = (term35 n x).
Proof. exact (MK_COMB (@lem1698519) (@lem1698474 n x)). Qed.
Lemma lem1698521 (n : real) (x : real) : (term1 x n) = (term36 n x).
Proof. exact (MK_COMB (@lem1698520 n x) (@lem1698518 n x)). Qed.
Lemma lem1698536 (n : real) (x : real) : (term0 x n) = (term36 n x).
Proof. exact (TRANS (@lem1698455 x n) (@lem1698521 n x)). Qed.
Lemma lem1698540 (n : real) (x : real) (h1 : term36 n x) : term36 n x.
Proof. exact (h1). Qed.
Lemma lem1698541 (n : real) (x : real) (h1 : term36 n x) : term33 n x.
Proof. exact (proj2 (@lem1698540 n x h1)). Qed.
Lemma lem1698542 (n : real) (x : real) (h1 : term36 n x) : term8 n x.
Proof. exact (proj1 (@lem1698540 n x h1)). Qed.
Lemma lem1698544 (n : nat) (m : nat) : (term37 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1698545 : term38 = term39.
Proof. exact (@lem1698544 (NUMERAL 0) term22). Qed.
Lemma lem1698546 : term40 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1698547 (h1 : term40 = (BIT1 0)) : term39 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1698548 : (term40 = (BIT1 0)) = (term39 = True).
Proof. exact (prop_ext (fun h1 : term40 = (BIT1 0) => @lem1698547 h1) (fun h1 : term39 = True => @lem1698546)). Qed.
Lemma lem1698549 : term39 = True.
Proof. exact (EQ_MP (@lem1698548) (@lem1698546)). Qed.
Lemma lem1698550 : term38 = True.
Proof. exact (TRANS (@lem1698545) (@lem1698549)). Qed.
Lemma lem1698551 : True = term38.
Proof. exact (SYM (@lem1698550)). Qed.
Lemma lem1698552 : term38.
Proof. exact (EQ_MP (@lem1698551) (@lem0)). Qed.
Lemma lem1698553 (n : real) (x : real) (h1 : term36 n x) : term41 n x.
Proof. exact (conj (@lem1698552) (@lem1698541 n x h1)). Qed.
Lemma lem1698555 (x : real) (y : real) : term42 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1698556 (n : real) (x : real) : term43 n x.
Proof. exact (@lem1698555 term17 (term29 n x)). Qed.
Lemma lem1698557 (n : real) (x : real) (h1 : term36 n x) : term44 n x.
Proof. exact (@lem1698556 n x (@lem1698553 n x h1)). Qed.
Lemma lem1698558 (n : real) (x : real) : (term45 n x) = (term29 n x).
Proof. exact (@lem1483460 (term29 n x)). Qed.
Lemma lem1698559 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1698560 (n : real) (x : real) : (term46 n x) = (term32 n x).
Proof. exact (MK_COMB (@lem1698559) (@lem1698558 n x)). Qed.
Lemma lem1698561 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1698562 (n : real) (x : real) : (term44 n x) = (term33 n x).
Proof. exact (MK_COMB (@lem1698560 n x) (@lem1698561)). Qed.
Lemma lem1698563 (n : real) (x : real) (h1 : term36 n x) : term33 n x.
Proof. exact (EQ_MP (@lem1698562 n x) (@lem1698557 n x h1)). Qed.
Lemma lem1698565 (n : nat) (m : nat) : (term37 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1698566 : term38 = term39.
Proof. exact (@lem1698565 (NUMERAL 0) term22). Qed.
Lemma lem1698567 : term40 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1698568 (h1 : term40 = (BIT1 0)) : term39 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1698569 : (term40 = (BIT1 0)) = (term39 = True).
Proof. exact (prop_ext (fun h1 : term40 = (BIT1 0) => @lem1698568 h1) (fun h1 : term39 = True => @lem1698567)). Qed.
Lemma lem1698570 : term39 = True.
Proof. exact (EQ_MP (@lem1698569) (@lem1698567)). Qed.
Lemma lem1698571 : term38 = True.
Proof. exact (TRANS (@lem1698566) (@lem1698570)). Qed.
Lemma lem1698572 : True = term38.
Proof. exact (SYM (@lem1698571)). Qed.
Lemma lem1698573 : term38.
Proof. exact (EQ_MP (@lem1698572) (@lem0)). Qed.
Lemma lem1698574 (n : real) (x : real) (h1 : term36 n x) : term47 n x.
Proof. exact (conj (@lem1698573) (@lem1698542 n x h1)). Qed.
Lemma lem1698576 (x : real) (y : real) : term42 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1698577 (n : real) (x : real) : term48 n x.
Proof. exact (@lem1698576 term17 (term4 n x)). Qed.
Lemma lem1698578 (n : real) (x : real) (h1 : term36 n x) : term49 n x.
Proof. exact (@lem1698577 n x (@lem1698574 n x h1)). Qed.
Lemma lem1698579 (n : real) (x : real) : (term50 n x) = (term4 n x).
Proof. exact (@lem1483460 (term4 n x)). Qed.
Lemma lem1698580 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1698581 (n : real) (x : real) : (term51 n x) = (term6 n x).
Proof. exact (MK_COMB (@lem1698580) (@lem1698579 n x)). Qed.
Lemma lem1698582 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1698583 (n : real) (x : real) : (term49 n x) = (term8 n x).
Proof. exact (MK_COMB (@lem1698581 n x) (@lem1698582)). Qed.
Lemma lem1698584 (n : real) (x : real) (h1 : term36 n x) : term8 n x.
Proof. exact (EQ_MP (@lem1698583 n x) (@lem1698578 n x h1)). Qed.
Lemma lem1698585 (n : real) (x : real) (h1 : term36 n x) : term36 n x.
Proof. exact (conj (@lem1698584 n x h1) (@lem1698563 n x h1)). Qed.
Lemma lem1698587 (x : real) (y : real) : term52 x y.
Proof. exact (proj1 (@lem1483578 x y)). Qed.
Lemma lem1698588 (n : real) (x : real) : term53 n x.
Proof. exact (@lem1698587 (term4 n x) (term29 n x)). Qed.
Lemma lem1698589 (n : real) (x : real) (h1 : term36 n x) : term54 n x.
Proof. exact (@lem1698588 n x (@lem1698585 n x h1)). Qed.
Lemma lem1698590 (n : real) (x : real) : (term55 n x) = (term56 n x).
Proof. exact (@lem1483480 n (term30 n) (term30 x) (term57 x)). Qed.
Lemma lem1698591 (n : real) : (term58 n) = (term59 n).
Proof. exact (@lem1483442 term16 n). Qed.
Lemma lem1698593 (m : nat) : (term60 m) = term7.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1698594 : term61 = term7.
Proof. exact (@lem1698593 term22). Qed.
Lemma lem1698595 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1698596 : term62 = term63.
Proof. exact (MK_COMB (@lem1698595) (@lem1698594)). Qed.
Lemma lem1698597 (n : real) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1698598 (n : real) : (term59 n) = (term64 n).
Proof. exact (MK_COMB (@lem1698596) (@lem1698597 n)). Qed.
Lemma lem1698599 (n : real) : (term58 n) = (term64 n).
Proof. exact (TRANS (@lem1698591 n) (@lem1698598 n)). Qed.
Lemma lem1698600 (n : real) : (term64 n) = term7.
Proof. exact (@lem1483446 n). Qed.
Lemma lem1698601 (n : real) : (term58 n) = term7.
Proof. exact (TRANS (@lem1698599 n) (@lem1698600 n)). Qed.
Lemma lem1698602 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1698603 (n : real) : (term65 n) = term66.
Proof. exact (MK_COMB (@lem1698602) (@lem1698601 n)). Qed.
Lemma lem1698604 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem1483490 (term30 x) x term16). Qed.
Lemma lem1698605 (x : real) : (term69 x) = (term59 x).
Proof. exact (@lem1483440 term16 x). Qed.
Lemma lem1698607 (m : nat) : (term60 m) = term7.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1698608 : term61 = term7.
Proof. exact (@lem1698607 term22). Qed.
Lemma lem1698609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1698610 : term62 = term63.
Proof. exact (MK_COMB (@lem1698609) (@lem1698608)). Qed.
Lemma lem1698611 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1698612 (x : real) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1698610) (@lem1698611 x)). Qed.
Lemma lem1698613 (x : real) : (term69 x) = (term64 x).
Proof. exact (TRANS (@lem1698605 x) (@lem1698612 x)). Qed.
Lemma lem1698614 (x : real) : (term64 x) = term7.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1698615 (x : real) : (term69 x) = term7.
Proof. exact (TRANS (@lem1698613 x) (@lem1698614 x)). Qed.
Lemma lem1698616 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1698617 (x : real) : (term70 x) = term66.
Proof. exact (MK_COMB (@lem1698616) (@lem1698615 x)). Qed.
Lemma lem1698618 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1698619 (x : real) : (term68 x) = term71.
Proof. exact (MK_COMB (@lem1698617 x) (@lem1698618)). Qed.
Lemma lem1698620 (x : real) : (term67 x) = term71.
Proof. exact (TRANS (@lem1698604 x) (@lem1698619 x)). Qed.
Lemma lem1698621 : term71 = term16.
Proof. exact (@lem1483448 term16). Qed.
Lemma lem1698622 (x : real) : (term67 x) = term16.
Proof. exact (TRANS (@lem1698620 x) (@lem1698621)). Qed.
Lemma lem1698623 (n : real) (x : real) : (term56 n x) = term71.
Proof. exact (MK_COMB (@lem1698603 n) (@lem1698622 x)). Qed.
Lemma lem1698624 (n : real) (x : real) : (term55 n x) = term71.
Proof. exact (TRANS (@lem1698590 n x) (@lem1698623 n x)). Qed.
Lemma lem1698625 : term71 = term16.
Proof. exact (@lem1483448 term16). Qed.
Lemma lem1698626 (n : real) (x : real) : (term55 n x) = term16.
Proof. exact (TRANS (@lem1698624 n x) (@lem1698625)). Qed.
Lemma lem1698627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1698628 (n : real) (x : real) : (term72 n x) = term73.
Proof. exact (MK_COMB (@lem1698627) (@lem1698626 n x)). Qed.
Lemma lem1698629 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1698630 (n : real) (x : real) : (term54 n x) = term74.
Proof. exact (MK_COMB (@lem1698628 n x) (@lem1698629)). Qed.
Lemma lem1698631 (n : real) (x : real) (h1 : term36 n x) : term74.
Proof. exact (EQ_MP (@lem1698630 n x) (@lem1698589 n x h1)). Qed.
Lemma lem1698633 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1698634 : term74 = term77.
Proof. exact (@lem1698633 term22 (NUMERAL 0)). Qed.
Lemma lem1698635 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1698636 : term40 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1698637 (h1 : term40 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1698638 : (term40 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term40 = (BIT1 0) => @lem1698637 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem1698636)). Qed.
Lemma lem1698639 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1698638) (@lem1698636)). Qed.
Lemma lem1698640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1698641 : term78 = (and False).
Proof. exact (MK_COMB (@lem1698640) (@lem1698639)). Qed.
Lemma lem1698642 : term77 = (False /\ True).
Proof. exact (MK_COMB (@lem1698641) (@lem1698635)). Qed.
Lemma lem1698644 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1698645 : term77 = False.
Proof. exact (TRANS (@lem1698642) (@lem1698644)). Qed.
Lemma lem1698646 : term74 = False.
Proof. exact (TRANS (@lem1698634) (@lem1698645)). Qed.
Lemma lem1698647 (n : real) (x : real) (h1 : term36 n x) : False.
Proof. exact (EQ_MP (@lem1698646) (@lem1698631 n x h1)). Qed.
Lemma lem1698649 (n : real) (x : real) (h1 : term36 n x) : term36 n x.
Proof. exact (h1). Qed.
Lemma lem1698650 (n : real) (x : real) (h1 : term36 n x) : (term36 n x) = False.
Proof. exact (prop_ext (fun h2 : term36 n x => @lem1698647 n x h1) (fun h2 : False => @lem1698649 n x h1)). Qed.
Lemma lem1698651 (n : real) (x : real) (h1 : term36 n x) : False.
Proof. exact (EQ_MP (@lem1698650 n x h1) (@lem1698649 n x h1)). Qed.
Lemma lem1698652 (x : real) (n : real) (h1 : term0 x n) : term0 x n.
Proof. exact (h1). Qed.
Lemma lem1698653 (x : real) (n : real) (h1 : term0 x n) : term36 n x.
Proof. exact (EQ_MP (@lem1698536 n x) (@lem1698652 x n h1)). Qed.
Lemma lem1698654 (x : real) (n : real) (h1 : term0 x n) : (term36 n x) = False.
Proof. exact (prop_ext (fun h2 : term36 n x => @lem1698651 n x h2) (fun h2 : False => @lem1698653 x n h1)). Qed.
Lemma lem1698655 (x : real) (n : real) (h1 : term0 x n) : False.
Proof. exact (EQ_MP (@lem1698654 x n h1) (@lem1698653 x n h1)). Qed.
Lemma lem1698656 (x : real) (n : real) : term79 x n.
Proof. exact (fun h0 : term0 x n => @lem1698655 x n h0). Qed.
Lemma lem1698657 (x : real) (n : real) : term80 x n.
Proof. exact (@lem1386578 (term81 x n)). Qed.
Lemma lem1698658 (x : real) (n : real) : term81 x n.
Proof. exact (@lem1698657 x n (@lem1698656 x n)). Qed.
Lemma lem1698669 (x : real) : term82 x.
Proof. exact (fun n : real => @lem1698658 x n). Qed.
Lemma lem1698670 : term83.
Proof. exact (fun x : real => @lem1698669 x). Qed.
Lemma lem1698672 (p : Prop) : p = (term84 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1698673 : term85 = term86.
Proof. exact (@lem1698672 term85). Qed.
Lemma lem1698674 : term86 = term85.
Proof. exact (SYM (@lem1698673)). Qed.
Lemma lem1698675 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem1698678 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem1698679 : term89.
Proof. exact (fun h0 : term88 => @lem1698678 h0). Qed.
Lemma lem1698680 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1698681 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem1698682 (h1 : term88) (h2 : term89) : term88.
Proof. exact (@lem1698680 h2 (@lem1698681 h1)). Qed.
Lemma lem1698683 (h1 : term88) : term90.
Proof. exact (fun h0 : term89 => @lem1698682 h1 h0). Qed.
Lemma lem1698684 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1698685 (h1 : term88) (h2 : term89) : term88.
Proof. exact (@lem1698683 h1 (@lem1698684 h2)). Qed.
Lemma lem1698686 (h1 : term89) : term89.
Proof. exact (fun h0 : term88 => @lem1698685 h0 h1). Qed.
Lemma lem1698687 : term91.
Proof. exact (fun h0 : term89 => @lem1698686 h0). Qed.
Lemma lem1698690 : term89.
Proof. exact (@lem1698687 (@lem1698679)). Qed.
Lemma lem1698724 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1698725 : term92 = term93.
Proof. exact (@lem1698724 term94). Qed.
Lemma lem1698734 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1698735 : term96 = term97.
Proof. exact (MK_COMB (@lem1698734) (@lem1698725)). Qed.
Lemma lem1698738 : term98 = term98.
Proof. exact (eq_refl term98). Qed.
Lemma lem1698739 : term99 = term100.
Proof. exact (MK_COMB (@lem1698738) (@lem1698735)). Qed.
Lemma lem1698742 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem1698749 : term88 = term102.
Proof. exact (MK_COMB (@lem1698742) (@lem1698739)). Qed.
Lemma lem1698750 (x : real) (n : nat) : (term103 x n) = (term103 x n).
Proof. exact (eq_refl (term103 x n)). Qed.
Lemma lem1698751 (x : real) : (term104 x) = (term104 x).
Proof. exact (fun_ext (fun n : nat => @lem1698750 x n)). Qed.
Lemma lem1698752 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1698753 (x : real) : (term105 x) = (term105 x).
Proof. exact (MK_COMB (@lem1698752) (@lem1698751 x)). Qed.
Lemma lem1698754 : term106 = term106.
Proof. exact (fun_ext (fun x : real => @lem1698753 x)). Qed.
Lemma lem1698755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698756 : term94 = term94.
Proof. exact (MK_COMB (@lem1698755) (@lem1698754)). Qed.
Lemma lem1698757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1698758 : term93 = term93.
Proof. exact (MK_COMB (@lem1698757) (@lem1698756)). Qed.
Lemma lem1698759 (m : nat) (n : nat) : ((term107 m n) = (term108 m n)) = ((term107 m n) = (term108 m n)).
Proof. exact (eq_refl ((term107 m n) = (term108 m n))). Qed.
Lemma lem1698760 (m : nat) : (term109 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem1698759 m n)). Qed.
Lemma lem1698761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1698762 (m : nat) : (term110 m) = (term110 m).
Proof. exact (MK_COMB (@lem1698761) (@lem1698760 m)). Qed.
Lemma lem1698763 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem1698762 m)). Qed.
Lemma lem1698764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1698765 : term112 = term112.
Proof. exact (MK_COMB (@lem1698764) (@lem1698763)). Qed.
Lemma lem1698766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698767 : term95 = term95.
Proof. exact (MK_COMB (@lem1698766) (@lem1698765)). Qed.
Lemma lem1698768 : term97 = term97.
Proof. exact (MK_COMB (@lem1698767) (@lem1698758)). Qed.
Lemma lem1698773 (x : real) (n : real) : (term81 x n) = (term81 x n).
Proof. exact (eq_refl (term81 x n)). Qed.
Lemma lem1698774 (x : real) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun n : real => @lem1698773 x n)). Qed.
Lemma lem1698775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698776 (x : real) : (term82 x) = (term82 x).
Proof. exact (MK_COMB (@lem1698775) (@lem1698774 x)). Qed.
Lemma lem1698777 : term114 = term114.
Proof. exact (fun_ext (fun x : real => @lem1698776 x)). Qed.
Lemma lem1698778 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698779 : term83 = term83.
Proof. exact (MK_COMB (@lem1698778) (@lem1698777)). Qed.
Lemma lem1698780 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698781 : term98 = term98.
Proof. exact (MK_COMB (@lem1698780) (@lem1698779)). Qed.
Lemma lem1698782 : term100 = term100.
Proof. exact (MK_COMB (@lem1698781) (@lem1698768)). Qed.
Lemma lem1698783 (x : real) (n : nat) : (term115 x n) = (term115 x n).
Proof. exact (eq_refl (term115 x n)). Qed.
Lemma lem1698784 (x : real) : (term116 x) = (term116 x).
Proof. exact (fun_ext (fun n : nat => @lem1698783 x n)). Qed.
Lemma lem1698785 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1698786 (x : real) : (term117 x) = (term117 x).
Proof. exact (MK_COMB (@lem1698785) (@lem1698784 x)). Qed.
Lemma lem1698787 : term118 = term118.
Proof. exact (fun_ext (fun x : real => @lem1698786 x)). Qed.
Lemma lem1698788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698789 : term85 = term85.
Proof. exact (MK_COMB (@lem1698788) (@lem1698787)). Qed.
Lemma lem1698790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1698791 : term87 = term87.
Proof. exact (MK_COMB (@lem1698790) (@lem1698789)). Qed.
Lemma lem1698792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1698793 : term101 = term101.
Proof. exact (MK_COMB (@lem1698792) (@lem1698791)). Qed.
Lemma lem1698794 : term102 = term102.
Proof. exact (MK_COMB (@lem1698793) (@lem1698782)). Qed.
Lemma lem1698853 : term88 = term102.
Proof. exact (TRANS (@lem1698749) (@lem1698794)). Qed.
Lemma lem1698854 : term102 = term88.
Proof. exact (SYM (@lem1698853)). Qed.
Lemma lem1698855 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem1698856 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1698857 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1698858 (h1 : term94) : term94.
Proof. exact (h1). Qed.
Lemma lem1698860 (P : nat -> Prop) : (term119 P) = (term120 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1698861 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1698860 (term116 x)). Qed.
Lemma lem1698862 (x : real) (n : nat) : (term123 x n) = (term115 x n).
Proof. exact (eq_refl (term123 x n)). Qed.
Lemma lem1698863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1698865 (x : real) (n : nat) : (term124 x n) = (term125 x n).
Proof. exact (MK_COMB (@lem1698863) (@lem1698862 x n)). Qed.
Lemma lem1698866 (x : real) : (term126 x) = (term127 x).
Proof. exact (fun_ext (fun n : nat => @lem1698865 x n)). Qed.
Lemma lem1698867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1698868 (x : real) : (term122 x) = (term128 x).
Proof. exact (MK_COMB (@lem1698867) (@lem1698866 x)). Qed.
Lemma lem1698869 (x : real) : (term121 x) = (term128 x).
Proof. exact (TRANS (@lem1698861 x) (@lem1698868 x)). Qed.
Lemma lem1698870 (P : real -> Prop) : (term129 P) = (term130 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1698871 : term87 = term131.
Proof. exact (@lem1698870 term118). Qed.
Lemma lem1698872 (x : real) : (term132 x) = (term117 x).
Proof. exact (eq_refl (term132 x)). Qed.
Lemma lem1698873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1698874 (x : real) : (term133 x) = (term121 x).
Proof. exact (MK_COMB (@lem1698873) (@lem1698872 x)). Qed.
Lemma lem1698875 (x : real) : (term133 x) = (term128 x).
Proof. exact (TRANS (@lem1698874 x) (@lem1698869 x)). Qed.
Lemma lem1698876 : term134 = term135.
Proof. exact (fun_ext (fun x : real => @lem1698875 x)). Qed.
Lemma lem1698877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1698878 : term131 = term136.
Proof. exact (MK_COMB (@lem1698877) (@lem1698876)). Qed.
Lemma lem1698891 : term87 = term136.
Proof. exact (TRANS (@lem1698871) (@lem1698878)). Qed.
Lemma lem1698892 (h1 : term87) : term136.
Proof. exact (EQ_MP (@lem1698891) (@lem1698855 h1)). Qed.
Lemma lem1698899 (x : real) (n : real) : (term81 x n) = (term137 x n).
Proof. exact (@lem17265 (real_le x n) (term2 x n)). Qed.
Lemma lem1698900 (x : real) : (term113 x) = (term138 x).
Proof. exact (fun_ext (fun n : real => @lem1698899 x n)). Qed.
Lemma lem1698901 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698902 (x : real) : (term82 x) = (term139 x).
Proof. exact (MK_COMB (@lem1698901) (@lem1698900 x)). Qed.
Lemma lem1698903 : term114 = term140.
Proof. exact (fun_ext (fun x : real => @lem1698902 x)). Qed.
Lemma lem1698904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698961 : term83 = term141.
Proof. exact (MK_COMB (@lem1698904) (@lem1698903)). Qed.
Lemma lem1698962 (h1 : term83) : term141.
Proof. exact (EQ_MP (@lem1698961) (@lem1698856 h1)). Qed.
Lemma lem1698963 (m : nat) (n : nat) : ((term107 m n) = (term108 m n)) = ((term107 m n) = (term108 m n)).
Proof. exact (eq_refl ((term107 m n) = (term108 m n))). Qed.
Lemma lem1698964 (m : nat) : (term109 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem1698963 m n)). Qed.
Lemma lem1698965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1698966 (m : nat) : (term110 m) = (term110 m).
Proof. exact (MK_COMB (@lem1698965) (@lem1698964 m)). Qed.
Lemma lem1698967 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem1698966 m)). Qed.
Lemma lem1698968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1698981 : term112 = term112.
Proof. exact (MK_COMB (@lem1698968) (@lem1698967)). Qed.
Lemma lem1698982 (h1 : term112) : term112.
Proof. exact (EQ_MP (@lem1698981) (@lem1698857 h1)). Qed.
Lemma lem1698983 (x : real) (n : nat) : (term103 x n) = (term103 x n).
Proof. exact (eq_refl (term103 x n)). Qed.
Lemma lem1698984 (x : real) : (term104 x) = (term104 x).
Proof. exact (fun_ext (fun n : nat => @lem1698983 x n)). Qed.
Lemma lem1698985 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1698986 (x : real) : (term105 x) = (term105 x).
Proof. exact (MK_COMB (@lem1698985) (@lem1698984 x)). Qed.
Lemma lem1698987 : term106 = term106.
Proof. exact (fun_ext (fun x : real => @lem1698986 x)). Qed.
Lemma lem1698988 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1698989 : term94 = term94.
Proof. exact (MK_COMB (@lem1698988) (@lem1698987)). Qed.
Lemma lem1699000 {A B : Type'} (P : type1413 A B) : (term142 A B P) = (term143 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1699001 (P : type1622) : (term144 P) = (term145 P).
Proof. exact (@lem1699000 real nat P). Qed.
Lemma lem1699002 : term146 = term147.
Proof. exact (@lem1699001 term148). Qed.
Lemma lem1699003 (x : real) : (term149 x) = (term104 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1699004 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1699005 (x : real) (n : nat) : (term150 x n) = (term151 x n).
Proof. exact (MK_COMB (@lem1699003 x) (@lem1699004 n)). Qed.
Lemma lem1699006 (x : real) (n : nat) : (term151 x n) = (term103 x n).
Proof. exact (eq_refl (term151 x n)). Qed.
Lemma lem1699007 (x : real) (n : nat) : (term150 x n) = (term103 x n).
Proof. exact (TRANS (@lem1699005 x n) (@lem1699006 x n)). Qed.
Lemma lem1699008 (x : real) : (term152 x) = (term104 x).
Proof. exact (fun_ext (fun n : nat => @lem1699007 x n)). Qed.
Lemma lem1699009 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1699010 (x : real) : (term153 x) = (term105 x).
Proof. exact (MK_COMB (@lem1699009) (@lem1699008 x)). Qed.
Lemma lem1699011 : term154 = term106.
Proof. exact (fun_ext (fun x : real => @lem1699010 x)). Qed.
Lemma lem1699012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699013 : term146 = term94.
Proof. exact (MK_COMB (@lem1699012) (@lem1699011)). Qed.
Lemma lem1699014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1699015 : term155 = term156.
Proof. exact (MK_COMB (@lem1699014) (@lem1699013)). Qed.
Lemma lem1699016 (x : real) : (term149 x) = (term104 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1699017 (n : real -> nat) (x : real) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem1699018 (n : real -> nat) (x : real) : (term157 n x) = (term158 n x).
Proof. exact (MK_COMB (@lem1699016 x) (@lem1699017 n x)). Qed.
Lemma lem1699019 (n : real -> nat) (x : real) : (term158 n x) = (term159 n x).
Proof. exact (eq_refl (term158 n x)). Qed.
Lemma lem1699020 (n : real -> nat) (x : real) : (term157 n x) = (term159 n x).
Proof. exact (TRANS (@lem1699018 n x) (@lem1699019 n x)). Qed.
Lemma lem1699021 (n : real -> nat) : (term160 n) = (term161 n).
Proof. exact (fun_ext (fun x : real => @lem1699020 n x)). Qed.
Lemma lem1699022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699023 (n : real -> nat) : (term162 n) = (term163 n).
Proof. exact (MK_COMB (@lem1699022) (@lem1699021 n)). Qed.
Lemma lem1699024 : term164 = term165.
Proof. exact (fun_ext (fun n : real -> nat => @lem1699023 n)). Qed.
Lemma lem1699025 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1699026 : term147 = term166.
Proof. exact (MK_COMB (@lem1699025) (@lem1699024)). Qed.
Lemma lem1699027 : (term146 = term147) = (term94 = term166).
Proof. exact (MK_COMB (@lem1699015) (@lem1699026)). Qed.
Lemma lem1699029 : term94 = term166.
Proof. exact (EQ_MP (@lem1699027) (@lem1699002)). Qed.
Lemma lem1699030 : term94 = term166.
Proof. exact (TRANS (@lem1698989) (@lem1699029)). Qed.
Lemma lem1699031 (h1 : term94) : term166.
Proof. exact (EQ_MP (@lem1699030) (@lem1698858 h1)). Qed.
Lemma lem1699032 (n : real -> nat) (h1 : term163 n) : term163 n.
Proof. exact (h1). Qed.
Lemma lem1699033 (x : real) (h1 : term128 x) : term128 x.
Proof. exact (h1). Qed.
Lemma lem1699058 (x : real) (n : real) : (term137 x n) = (term137 x n).
Proof. exact (eq_refl (term137 x n)). Qed.
Lemma lem1699059 (x : real) : (term138 x) = (term138 x).
Proof. exact (fun_ext (fun n : real => @lem1699058 x n)). Qed.
Lemma lem1699060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699061 (x : real) : (term139 x) = (term139 x).
Proof. exact (MK_COMB (@lem1699060) (@lem1699059 x)). Qed.
Lemma lem1699062 : term140 = term140.
Proof. exact (fun_ext (fun x : real => @lem1699061 x)). Qed.
Lemma lem1699063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699064 : term141 = term141.
Proof. exact (MK_COMB (@lem1699063) (@lem1699062)). Qed.
Lemma lem1699065 (h1 : term83) : term141.
Proof. exact (EQ_MP (@lem1699064) (@lem1698962 h1)). Qed.
Lemma lem1699084 (m : nat) (n : nat) : ((term107 m n) = (term108 m n)) = ((term107 m n) = (term108 m n)).
Proof. exact (eq_refl ((term107 m n) = (term108 m n))). Qed.
Lemma lem1699085 (m : nat) : (term109 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem1699084 m n)). Qed.
Lemma lem1699086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699087 (m : nat) : (term110 m) = (term110 m).
Proof. exact (MK_COMB (@lem1699086) (@lem1699085 m)). Qed.
Lemma lem1699088 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem1699087 m)). Qed.
Lemma lem1699089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699090 : term112 = term112.
Proof. exact (MK_COMB (@lem1699089) (@lem1699088)). Qed.
Lemma lem1699091 (h1 : term112) : term112.
Proof. exact (EQ_MP (@lem1699090) (@lem1698982 h1)). Qed.
Lemma lem1699100 (n : real -> nat) (x : real) : (term159 n x) = (term159 n x).
Proof. exact (eq_refl (term159 n x)). Qed.
Lemma lem1699101 (n : real -> nat) : (term161 n) = (term161 n).
Proof. exact (fun_ext (fun x : real => @lem1699100 n x)). Qed.
Lemma lem1699102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699103 (n : real -> nat) : (term163 n) = (term163 n).
Proof. exact (MK_COMB (@lem1699102) (@lem1699101 n)). Qed.
Lemma lem1699104 (n : real -> nat) (h1 : term163 n) : term163 n.
Proof. exact (EQ_MP (@lem1699103 n) (@lem1699032 n h1)). Qed.
Lemma lem1699113 (x : real) (n : nat) : (term125 x n) = (term125 x n).
Proof. exact (eq_refl (term125 x n)). Qed.
Lemma lem1699114 (x : real) : (term127 x) = (term127 x).
Proof. exact (fun_ext (fun n : nat => @lem1699113 x n)). Qed.
Lemma lem1699115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699116 (x : real) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem1699115) (@lem1699114 x)). Qed.
Lemma lem1699117 (x : real) (h1 : term128 x) : term128 x.
Proof. exact (EQ_MP (@lem1699116 x) (@lem1699033 x h1)). Qed.
Lemma lem1699125 (x : real) (n : real) : (term137 x n) = (term137 x n).
Proof. exact (eq_refl (term137 x n)). Qed.
Lemma lem1699126 (x : real) : (term138 x) = (term138 x).
Proof. exact (fun_ext (fun n : real => @lem1699125 x n)). Qed.
Lemma lem1699127 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699128 (x : real) : (term139 x) = (term139 x).
Proof. exact (MK_COMB (@lem1699127) (@lem1699126 x)). Qed.
Lemma lem1699129 : term140 = term140.
Proof. exact (fun_ext (fun x : real => @lem1699128 x)). Qed.
Lemma lem1699130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699132 : term141 = term141.
Proof. exact (MK_COMB (@lem1699130) (@lem1699129)). Qed.
Lemma lem1699133 (h1 : term83) : term141.
Proof. exact (EQ_MP (@lem1699132) (@lem1699065 h1)). Qed.
Lemma lem1699135 (m : nat) (n : nat) : ((term107 m n) = (term108 m n)) = ((term107 m n) = (term108 m n)).
Proof. exact (eq_refl ((term107 m n) = (term108 m n))). Qed.
Lemma lem1699136 (m : nat) : (term109 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem1699135 m n)). Qed.
Lemma lem1699137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699138 (m : nat) : (term110 m) = (term110 m).
Proof. exact (MK_COMB (@lem1699137) (@lem1699136 m)). Qed.
Lemma lem1699139 : term111 = term111.
Proof. exact (fun_ext (fun m : nat => @lem1699138 m)). Qed.
Lemma lem1699140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699142 : term112 = term112.
Proof. exact (MK_COMB (@lem1699140) (@lem1699139)). Qed.
Lemma lem1699143 (h1 : term112) : term112.
Proof. exact (EQ_MP (@lem1699142) (@lem1699091 h1)). Qed.
Lemma lem1699145 (n : real -> nat) (x : real) : (term159 n x) = (term159 n x).
Proof. exact (eq_refl (term159 n x)). Qed.
Lemma lem1699146 (n : real -> nat) : (term161 n) = (term161 n).
Proof. exact (fun_ext (fun x : real => @lem1699145 n x)). Qed.
Lemma lem1699147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699149 (n : real -> nat) : (term163 n) = (term163 n).
Proof. exact (MK_COMB (@lem1699147) (@lem1699146 n)). Qed.
Lemma lem1699150 (n : real -> nat) (h1 : term163 n) : term163 n.
Proof. exact (EQ_MP (@lem1699149 n) (@lem1699104 n h1)). Qed.
Lemma lem1699152 (x : real) (n : nat) : (term125 x n) = (term125 x n).
Proof. exact (eq_refl (term125 x n)). Qed.
Lemma lem1699153 (x : real) : (term127 x) = (term127 x).
Proof. exact (fun_ext (fun n : nat => @lem1699152 x n)). Qed.
Lemma lem1699154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699156 (x : real) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem1699154) (@lem1699153 x)). Qed.
Lemma lem1699157 (x : real) (h1 : term128 x) : term128 x.
Proof. exact (EQ_MP (@lem1699156 x) (@lem1699117 x h1)). Qed.
Lemma lem1699158 (_26283 : real) (h1 : term83) : term167 _26283.
Proof. exact (@lem1699133 h1 _26283). Qed.
Lemma lem1699159 (_26283 : real) : (term167 _26283) = (term139 _26283).
Proof. exact (eq_refl (term167 _26283)). Qed.
Lemma lem1699160 (_26283 : real) (h1 : term83) : term139 _26283.
Proof. exact (EQ_MP (@lem1699159 _26283) (@lem1699158 _26283 h1)). Qed.
Lemma lem1699161 (_26283 : real) (_26284 : real) (h1 : term83) : term168 _26283 _26284.
Proof. exact (@lem1699160 _26283 h1 _26284). Qed.
Lemma lem1699162 (_26283 : real) (_26284 : real) : (term168 _26283 _26284) = (term137 _26283 _26284).
Proof. exact (eq_refl (term168 _26283 _26284)). Qed.
Lemma lem1699164 (_26285 : nat) (h1 : term112) : term169 _26285.
Proof. exact (@lem1699143 h1 _26285). Qed.
Lemma lem1699165 (_26285 : nat) : (term169 _26285) = (term110 _26285).
Proof. exact (eq_refl (term169 _26285)). Qed.
Lemma lem1699166 (_26285 : nat) (h1 : term112) : term110 _26285.
Proof. exact (EQ_MP (@lem1699165 _26285) (@lem1699164 _26285 h1)). Qed.
Lemma lem1699167 (_26285 : nat) (_26286 : nat) (h1 : term112) : term170 _26285 _26286.
Proof. exact (@lem1699166 _26285 h1 _26286). Qed.
Lemma lem1699168 (_26285 : nat) (_26286 : nat) : (term170 _26285 _26286) = ((term107 _26285 _26286) = (term108 _26285 _26286)).
Proof. exact (eq_refl (term170 _26285 _26286)). Qed.
Lemma lem1699170 (_26287 : real) (n : real -> nat) (h1 : term163 n) : term171 n _26287.
Proof. exact (@lem1699150 n h1 _26287). Qed.
Lemma lem1699171 (n : real -> nat) (_26287 : real) : (term171 n _26287) = (term159 n _26287).
Proof. exact (eq_refl (term171 n _26287)). Qed.
Lemma lem1699173 (_26288 : nat) (x : real) (h1 : term128 x) : term172 x _26288.
Proof. exact (@lem1699157 x h1 _26288). Qed.
Lemma lem1699174 (x : real) (_26288 : nat) : (term172 x _26288) = (term125 x _26288).
Proof. exact (eq_refl (term172 x _26288)). Qed.
Lemma lem1699181 (_26283 : real) (_26284 : real) (h1 : term83) : term137 _26283 _26284.
Proof. exact (EQ_MP (@lem1699162 _26283 _26284) (@lem1699161 _26283 _26284 h1)). Qed.
Lemma lem1699187 (_26288 : nat) (x : real) (h1 : term128 x) : term125 x _26288.
Proof. exact (EQ_MP (@lem1699174 x _26288) (@lem1699173 _26288 x h1)). Qed.
Lemma lem1699207 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1699208 (_26293 : real) (_26295 : real) (h1 : _26293 = _26295) : _26293 = _26295.
Proof. exact (h1). Qed.
Lemma lem1699209 (_26294 : real) (_26296 : real) (h1 : _26294 = _26296) : _26294 = _26296.
Proof. exact (h1). Qed.
Lemma lem1699210 (_26293 : real) (_26295 : real) (h1 : _26293 = _26295) : (real_lt _26293) = (real_lt _26295).
Proof. exact (MK_COMB (@lem1699207) (@lem1699208 _26293 _26295 h1)). Qed.
Lemma lem1699211 (_26293 : real) (_26295 : real) (_26294 : real) (_26296 : real) (h1 : _26293 = _26295) (h2 : _26294 = _26296) : (real_lt _26293 _26294) = (real_lt _26295 _26296).
Proof. exact (MK_COMB (@lem1699210 _26293 _26295 h1) (@lem1699209 _26294 _26296 h2)). Qed.
Lemma lem1699213 (b : Prop) (a : Prop) : term173 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1699214 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : term174 _26295 _26296 _26293 _26294.
Proof. exact (@lem1699213 (real_lt _26295 _26296) (real_lt _26293 _26294)). Qed.
Lemma lem1699215 (_26293 : real) (_26295 : real) (_26294 : real) (_26296 : real) (h1 : _26293 = _26295) (h2 : _26294 = _26296) : term175 _26295 _26296 _26293 _26294.
Proof. exact (@lem1699214 _26295 _26296 _26293 _26294 (@lem1699211 _26293 _26295 _26294 _26296 h1 h2)). Qed.
Lemma lem1699216 (_26296 : real) (_26294 : real) (_26293 : real) (_26295 : real) (h1 : _26293 = _26295) : term176 _26295 _26296 _26293 _26294.
Proof. exact (fun h0 : _26294 = _26296 => @lem1699215 _26293 _26295 _26294 _26296 h1 h0). Qed.
Lemma lem1699218 (a : Prop) (b : Prop) : (a -> b) = (term177 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1699219 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term176 _26295 _26296 _26293 _26294) = (term178 _26295 _26296 _26293 _26294).
Proof. exact (@lem1699218 (_26294 = _26296) (term175 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699220 (_26296 : real) (_26294 : real) (_26293 : real) (_26295 : real) (h1 : _26293 = _26295) : term178 _26295 _26296 _26293 _26294.
Proof. exact (EQ_MP (@lem1699219 _26295 _26296 _26293 _26294) (@lem1699216 _26296 _26294 _26293 _26295 h1)). Qed.
Lemma lem1699221 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : term179 _26295 _26296 _26293 _26294.
Proof. exact (fun h0 : _26293 = _26295 => @lem1699220 _26296 _26294 _26293 _26295 h0). Qed.
Lemma lem1699223 (a : Prop) (b : Prop) : (a -> b) = (term177 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1699224 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term179 _26295 _26296 _26293 _26294) = (term180 _26295 _26296 _26293 _26294).
Proof. exact (@lem1699223 (_26293 = _26295) (term178 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699225 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : term180 _26295 _26296 _26293 _26294.
Proof. exact (EQ_MP (@lem1699224 _26295 _26296 _26293 _26294) (@lem1699221 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699293 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1699294 (x : real) : term181 x.
Proof. exact (fun h0 : term182 x => @lem1699293 x). Qed.
Lemma lem1699296 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699297 (x : real) : (term181 x) = (x = x).
Proof. exact (@lem1699296 (x = x)). Qed.
Lemma lem1699298 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1699297 x) (@lem1699294 x)). Qed.
Lemma lem1699300 (_26285 : nat) (_26286 : nat) (h1 : term112) : (term107 _26285 _26286) = (term108 _26285 _26286).
Proof. exact (EQ_MP (@lem1699168 _26285 _26286) (@lem1699167 _26285 _26286 h1)). Qed.
Lemma lem1699301 (n : real -> nat) (x : real) (h1 : term112) : (term184 n x) = (term185 n x).
Proof. exact (@lem1699300 (n x) term22 h1). Qed.
Lemma lem1699302 (n : real -> nat) (x : real) (h1 : term112) : term186 n x.
Proof. exact (fun h0 : term187 n x => @lem1699301 n x h1). Qed.
Lemma lem1699304 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699305 (n : real -> nat) (x : real) : (term186 n x) = ((term184 n x) = (term185 n x)).
Proof. exact (@lem1699304 ((term184 n x) = (term185 n x))). Qed.
Lemma lem1699306 (n : real -> nat) (x : real) (h1 : term112) : (term184 n x) = (term185 n x).
Proof. exact (EQ_MP (@lem1699305 n x) (@lem1699302 n x h1)). Qed.
Lemma lem1699308 (_26287 : real) (n : real -> nat) (h1 : term163 n) : term159 n _26287.
Proof. exact (EQ_MP (@lem1699171 n _26287) (@lem1699170 _26287 n h1)). Qed.
Lemma lem1699309 (x : real) (n : real -> nat) (h1 : term163 n) : term159 n x.
Proof. exact (@lem1699308 x n h1). Qed.
Lemma lem1699310 (x : real) (n : real -> nat) (h1 : term163 n) : term188 n x.
Proof. exact (fun h0 : term189 n x => @lem1699309 x n h1). Qed.
Lemma lem1699312 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699313 (n : real -> nat) (x : real) : (term188 n x) = (term159 n x).
Proof. exact (@lem1699312 (term159 n x)). Qed.
Lemma lem1699314 (x : real) (n : real -> nat) (h1 : term163 n) : term159 n x.
Proof. exact (EQ_MP (@lem1699313 n x) (@lem1699310 x n h1)). Qed.
Lemma lem1699320 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1699321 (_26283 : real) (_26284 : real) : (term137 _26283 _26284) = (term190 _26283 _26284).
Proof. exact (@lem1699320 (term2 _26283 _26284) (term191 _26283 _26284)). Qed.
Lemma lem1699327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1699328 (_26283 : real) (_26284 : real) : (term192 _26283 _26284) = (term193 _26283 _26284).
Proof. exact (MK_COMB (@lem1699327) (@lem1699321 _26283 _26284)). Qed.
Lemma lem1699334 (_26283 : real) (_26284 : real) : (term190 _26283 _26284) = (term190 _26283 _26284).
Proof. exact (eq_refl (term190 _26283 _26284)). Qed.
Lemma lem1699335 (_26283 : real) (_26284 : real) : ((term137 _26283 _26284) = (term190 _26283 _26284)) = ((term190 _26283 _26284) = (term190 _26283 _26284)).
Proof. exact (MK_COMB (@lem1699328 _26283 _26284) (@lem1699334 _26283 _26284)). Qed.
Lemma lem1699337 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1699338 (x : Prop) : (x = x) = True.
Proof. exact (@lem1699337 Prop x). Qed.
Lemma lem1699339 (_26283 : real) (_26284 : real) : ((term190 _26283 _26284) = (term190 _26283 _26284)) = True.
Proof. exact (@lem1699338 (term190 _26283 _26284)). Qed.
Lemma lem1699340 (_26283 : real) (_26284 : real) : ((term137 _26283 _26284) = (term190 _26283 _26284)) = True.
Proof. exact (TRANS (@lem1699335 _26283 _26284) (@lem1699339 _26283 _26284)). Qed.
Lemma lem1699341 (_26283 : real) (_26284 : real) : True = ((term137 _26283 _26284) = (term190 _26283 _26284)).
Proof. exact (SYM (@lem1699340 _26283 _26284)). Qed.
Lemma lem1699342 (_26283 : real) (_26284 : real) : (term137 _26283 _26284) = (term190 _26283 _26284).
Proof. exact (EQ_MP (@lem1699341 _26283 _26284) (@lem0)). Qed.
Lemma lem1699343 (_26283 : real) (_26284 : real) (h1 : term83) : term190 _26283 _26284.
Proof. exact (EQ_MP (@lem1699342 _26283 _26284) (@lem1699181 _26283 _26284 h1)). Qed.
Lemma lem1699345 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1699346 (_26283 : real) (_26284 : real) : (term190 _26283 _26284) = (term195 _26283 _26284).
Proof. exact (@lem1699345 (term191 _26283 _26284) (term2 _26283 _26284)). Qed.
Lemma lem1699348 (a : Prop) : (term196 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1699349 (_26283 : real) (_26284 : real) : (term197 _26283 _26284) = (real_le _26283 _26284).
Proof. exact (@lem1699348 (real_le _26283 _26284)). Qed.
Lemma lem1699350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1699351 (_26283 : real) (_26284 : real) : (term198 _26283 _26284) = (term199 _26283 _26284).
Proof. exact (MK_COMB (@lem1699350) (@lem1699349 _26283 _26284)). Qed.
Lemma lem1699352 (_26283 : real) (_26284 : real) : (term2 _26283 _26284) = (term2 _26283 _26284).
Proof. exact (eq_refl (term2 _26283 _26284)). Qed.
Lemma lem1699353 (_26283 : real) (_26284 : real) : (term195 _26283 _26284) = (term81 _26283 _26284).
Proof. exact (MK_COMB (@lem1699351 _26283 _26284) (@lem1699352 _26283 _26284)). Qed.
Lemma lem1699354 (_26283 : real) (_26284 : real) : (term190 _26283 _26284) = (term81 _26283 _26284).
Proof. exact (TRANS (@lem1699346 _26283 _26284) (@lem1699353 _26283 _26284)). Qed.
Lemma lem1699357 (_26283 : real) (_26284 : real) (h1 : term83) : term81 _26283 _26284.
Proof. exact (EQ_MP (@lem1699354 _26283 _26284) (@lem1699343 _26283 _26284 h1)). Qed.
Lemma lem1699358 (n : real -> nat) (x : real) (h1 : term83) : term200 n x.
Proof. exact (@lem1699357 x (term201 n x) h1). Qed.
Lemma lem1699361 (x : real) (n : real -> nat) (h1 : term83) (h2 : term163 n) : term202 n x.
Proof. exact (@lem1699358 n x h1 (@lem1699314 x n h2)). Qed.
Lemma lem1699362 (x : real) (n : real -> nat) (h1 : term83) (h2 : term163 n) : term203 n x.
Proof. exact (fun h0 : term204 n x => @lem1699361 x n h1 h2). Qed.
Lemma lem1699364 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699365 (n : real -> nat) (x : real) : (term203 n x) = (term202 n x).
Proof. exact (@lem1699364 (term202 n x)). Qed.
Lemma lem1699366 (x : real) (n : real -> nat) (h1 : term83) (h2 : term163 n) : term202 n x.
Proof. exact (EQ_MP (@lem1699365 n x) (@lem1699362 x n h1 h2)). Qed.
Lemma lem1699384 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1699385 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term178 _26295 _26296 _26293 _26294) = (term206 _26295 _26296 _26293 _26294).
Proof. exact (@lem1699384 (real_lt _26295 _26296) (term207 _26294 _26296) (term208 _26293 _26294)). Qed.
Lemma lem1699403 (_26293 : real) (_26295 : real) : (term209 _26293 _26295) = (term209 _26293 _26295).
Proof. exact (eq_refl (term209 _26293 _26295)). Qed.
Lemma lem1699404 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term180 _26295 _26296 _26293 _26294) = (term210 _26295 _26296 _26293 _26294).
Proof. exact (MK_COMB (@lem1699403 _26293 _26295) (@lem1699385 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699408 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1699409 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term210 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294).
Proof. exact (@lem1699408 (real_lt _26295 _26296) (term207 _26293 _26295) (term212 _26296 _26293 _26294)). Qed.
Lemma lem1699439 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term180 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294).
Proof. exact (TRANS (@lem1699404 _26295 _26296 _26293 _26294) (@lem1699409 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1699441 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term213 _26295 _26296 _26293 _26294) = (term214 _26295 _26296 _26293 _26294).
Proof. exact (MK_COMB (@lem1699440) (@lem1699439 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699471 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term211 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294).
Proof. exact (eq_refl (term211 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699472 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : ((term180 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294)) = ((term211 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294)).
Proof. exact (MK_COMB (@lem1699441 _26295 _26296 _26293 _26294) (@lem1699471 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1699475 (x : Prop) : (x = x) = True.
Proof. exact (@lem1699474 Prop x). Qed.
Lemma lem1699476 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : ((term211 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294)) = True.
Proof. exact (@lem1699475 (term211 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699477 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : ((term180 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294)) = True.
Proof. exact (TRANS (@lem1699472 _26295 _26296 _26293 _26294) (@lem1699476 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699478 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : True = ((term180 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294)).
Proof. exact (SYM (@lem1699477 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699479 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term180 _26295 _26296 _26293 _26294) = (term211 _26295 _26296 _26293 _26294).
Proof. exact (EQ_MP (@lem1699478 _26295 _26296 _26293 _26294) (@lem0)). Qed.
Lemma lem1699480 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : term211 _26295 _26296 _26293 _26294.
Proof. exact (EQ_MP (@lem1699479 _26295 _26296 _26293 _26294) (@lem1699225 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699482 (b : Prop) (a : Prop) : (a \/ b) = (term194 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1699483 (_26293 : real) (_26294 : real) (_26295 : real) (_26296 : real) : (term211 _26295 _26296 _26293 _26294) = (term215 _26293 _26294 _26295 _26296).
Proof. exact (@lem1699482 (term216 _26295 _26296 _26293 _26294) (real_lt _26295 _26296)). Qed.
Lemma lem1699485 (a : Prop) (b : Prop) : (term217 a b) = (term218 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1699486 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term219 _26295 _26296 _26293 _26294) = (term220 _26295 _26296 _26293 _26294).
Proof. exact (@lem1699485 (term207 _26293 _26295) (term212 _26296 _26293 _26294)). Qed.
Lemma lem1699488 (a : Prop) : (term196 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1699489 (_26293 : real) (_26295 : real) : (term221 _26293 _26295) = (_26293 = _26295).
Proof. exact (@lem1699488 (_26293 = _26295)). Qed.
Lemma lem1699490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1699491 (_26293 : real) (_26295 : real) : (term222 _26293 _26295) = (term223 _26293 _26295).
Proof. exact (MK_COMB (@lem1699490) (@lem1699489 _26293 _26295)). Qed.
Lemma lem1699493 (a : Prop) (b : Prop) : (term217 a b) = (term218 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1699494 (_26296 : real) (_26293 : real) (_26294 : real) : (term224 _26296 _26293 _26294) = (term225 _26296 _26293 _26294).
Proof. exact (@lem1699493 (term207 _26294 _26296) (term208 _26293 _26294)). Qed.
Lemma lem1699496 (a : Prop) : (term196 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1699497 (_26294 : real) (_26296 : real) : (term221 _26294 _26296) = (_26294 = _26296).
Proof. exact (@lem1699496 (_26294 = _26296)). Qed.
Lemma lem1699498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1699499 (_26294 : real) (_26296 : real) : (term222 _26294 _26296) = (term223 _26294 _26296).
Proof. exact (MK_COMB (@lem1699498) (@lem1699497 _26294 _26296)). Qed.
Lemma lem1699501 (a : Prop) : (term196 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1699502 (_26293 : real) (_26294 : real) : (term226 _26293 _26294) = (real_lt _26293 _26294).
Proof. exact (@lem1699501 (real_lt _26293 _26294)). Qed.
Lemma lem1699503 (_26296 : real) (_26293 : real) (_26294 : real) : (term225 _26296 _26293 _26294) = (term227 _26296 _26293 _26294).
Proof. exact (MK_COMB (@lem1699499 _26294 _26296) (@lem1699502 _26293 _26294)). Qed.
Lemma lem1699504 (_26296 : real) (_26293 : real) (_26294 : real) : (term224 _26296 _26293 _26294) = (term227 _26296 _26293 _26294).
Proof. exact (TRANS (@lem1699494 _26296 _26293 _26294) (@lem1699503 _26296 _26293 _26294)). Qed.
Lemma lem1699505 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term220 _26295 _26296 _26293 _26294) = (term228 _26295 _26296 _26293 _26294).
Proof. exact (MK_COMB (@lem1699491 _26293 _26295) (@lem1699504 _26296 _26293 _26294)). Qed.
Lemma lem1699506 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term219 _26295 _26296 _26293 _26294) = (term228 _26295 _26296 _26293 _26294).
Proof. exact (TRANS (@lem1699486 _26295 _26296 _26293 _26294) (@lem1699505 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1699508 (_26295 : real) (_26296 : real) (_26293 : real) (_26294 : real) : (term229 _26295 _26296 _26293 _26294) = (term230 _26295 _26296 _26293 _26294).
Proof. exact (MK_COMB (@lem1699507) (@lem1699506 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699509 (_26295 : real) (_26296 : real) : (real_lt _26295 _26296) = (real_lt _26295 _26296).
Proof. exact (eq_refl (real_lt _26295 _26296)). Qed.
Lemma lem1699510 (_26293 : real) (_26294 : real) (_26295 : real) (_26296 : real) : (term215 _26293 _26294 _26295 _26296) = (term231 _26293 _26294 _26295 _26296).
Proof. exact (MK_COMB (@lem1699508 _26295 _26296 _26293 _26294) (@lem1699509 _26295 _26296)). Qed.
Lemma lem1699511 (_26293 : real) (_26294 : real) (_26295 : real) (_26296 : real) : (term211 _26295 _26296 _26293 _26294) = (term231 _26293 _26294 _26295 _26296).
Proof. exact (TRANS (@lem1699483 _26293 _26294 _26295 _26296) (@lem1699510 _26293 _26294 _26295 _26296)). Qed.
Lemma lem1699513 (x : real) (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) : term232 n x.
Proof. exact (conj (@lem1699306 n x h1) (@lem1699366 x n h2 h3)). Qed.
Lemma lem1699514 (x : real) (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) : term233 n x.
Proof. exact (conj (@lem1699298 x) (@lem1699513 x n h1 h2 h3)). Qed.
Lemma lem1699516 (_26293 : real) (_26294 : real) (_26295 : real) (_26296 : real) : term231 _26293 _26294 _26295 _26296.
Proof. exact (EQ_MP (@lem1699511 _26293 _26294 _26295 _26296) (@lem1699480 _26295 _26296 _26293 _26294)). Qed.
Lemma lem1699517 (n : real -> nat) (x : real) : term234 n x.
Proof. exact (@lem1699516 x (term184 n x) x (term185 n x)). Qed.
Lemma lem1699520 (x : real) (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) : term235 n x.
Proof. exact (@lem1699517 n x (@lem1699514 x n h1 h2 h3)). Qed.
Lemma lem1699521 (x : real) (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) : term236 n x.
Proof. exact (fun h0 : term237 n x => @lem1699520 x n h1 h2 h3). Qed.
Lemma lem1699523 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699524 (n : real -> nat) (x : real) : (term236 n x) = (term235 n x).
Proof. exact (@lem1699523 (term235 n x)). Qed.
Lemma lem1699525 (x : real) (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) : term235 n x.
Proof. exact (EQ_MP (@lem1699524 n x) (@lem1699521 x n h1 h2 h3)). Qed.
Lemma lem1699528 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1699530 (x : real) (_26288 : nat) : (term125 x _26288) = (term238 x _26288).
Proof. exact (@lem1699528 (term115 x _26288)). Qed.
Lemma lem1699533 (_26288 : nat) (x : real) (h1 : term128 x) : term238 x _26288.
Proof. exact (EQ_MP (@lem1699530 x _26288) (@lem1699187 _26288 x h1)). Qed.
Lemma lem1699534 (n : real -> nat) (x : real) (h1 : term128 x) : term239 n x.
Proof. exact (@lem1699533 (term240 n x) x h1). Qed.
Lemma lem1699537 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (@lem1699534 n x h2 (@lem1699525 x n h1 h3 h4)). Qed.
Lemma lem1699538 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : term241.
Proof. exact (fun h0 : ~ False => @lem1699537 x n h1 h2 h3 h4). Qed.
Lemma lem1699540 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1699541 : term241 = False.
Proof. exact (@lem1699540 False). Qed.
Lemma lem1699542 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699541) (@lem1699538 x n h1 h2 h3 h4)). Qed.
Lemma lem1699543 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : (term128 x) = False.
Proof. exact (prop_ext (fun h5 : term128 x => @lem1699542 x n h1 h2 h3 h4) (fun h5 : False => @lem1699157 x h2)). Qed.
Lemma lem1699544 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699543 x n h1 h2 h3 h4) (@lem1699157 x h2)). Qed.
Lemma lem1699545 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : (term163 n) = False.
Proof. exact (prop_ext (fun h5 : term163 n => @lem1699544 x n h1 h2 h3 h4) (fun h5 : False => @lem1699150 n h4)). Qed.
Lemma lem1699546 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699545 x n h1 h2 h3 h4) (@lem1699150 n h4)). Qed.
Lemma lem1699547 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : term112 = False.
Proof. exact (prop_ext (fun h5 : term112 => @lem1699546 x n h1 h2 h3 h4) (fun h5 : False => @lem1699143 h1)). Qed.
Lemma lem1699548 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699547 x n h1 h2 h3 h4) (@lem1699143 h1)). Qed.
Lemma lem1699549 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : (term128 x) = False.
Proof. exact (prop_ext (fun h5 : term128 x => @lem1699548 x n h1 h2 h3 h4) (fun h5 : False => @lem1699117 x h2)). Qed.
Lemma lem1699550 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699549 x n h1 h2 h3 h4) (@lem1699117 x h2)). Qed.
Lemma lem1699551 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : (term163 n) = False.
Proof. exact (prop_ext (fun h5 : term163 n => @lem1699550 x n h1 h2 h3 h4) (fun h5 : False => @lem1699104 n h4)). Qed.
Lemma lem1699552 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699551 x n h1 h2 h3 h4) (@lem1699104 n h4)). Qed.
Lemma lem1699553 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : term112 = False.
Proof. exact (prop_ext (fun h5 : term112 => @lem1699552 x n h1 h2 h3 h4) (fun h5 : False => @lem1699091 h1)). Qed.
Lemma lem1699554 (x : real) (n : real -> nat) (h1 : term112) (h2 : term128 x) (h3 : term83) (h4 : term163 n) : False.
Proof. exact (EQ_MP (@lem1699553 x n h1 h2 h3 h4) (@lem1699091 h1)). Qed.
Lemma lem1699555 (n : real -> nat) (h1 : term112) (h2 : term83) (h3 : term163 n) (h4 : term87) : False.
Proof. exact (ex_elim (@lem1698892 h4) (fun x : real => fun h0 : term135 x => @lem1699554 x n h1 h0 h2 h3)). Qed.
Lemma lem1699556 (h1 : term112) (h2 : term83) (h3 : term94) (h4 : term87) : False.
Proof. exact (ex_elim (@lem1699031 h3) (fun n : real -> nat => fun h0 : term165 n => @lem1699555 n h1 h2 h0 h4)). Qed.
Lemma lem1699557 (h1 : term112) (h2 : term83) (h3 : term94) (h4 : term87) : term112 = False.
Proof. exact (prop_ext (fun h5 : term112 => @lem1699556 h1 h2 h3 h4) (fun h5 : False => @lem1698982 h1)). Qed.
Lemma lem1699558 (h1 : term112) (h2 : term83) (h3 : term94) (h4 : term87) : False.
Proof. exact (EQ_MP (@lem1699557 h1 h2 h3 h4) (@lem1698982 h1)). Qed.
Lemma lem1699559 (h1 : term112) (h2 : term83) (h3 : term87) : term92.
Proof. exact (fun h0 : term94 => @lem1699558 h1 h2 h0 h3). Qed.
Lemma lem1699560 : term92 = term93.
Proof. exact (@lem69 term94). Qed.
Lemma lem1699561 (h1 : term112) (h2 : term83) (h3 : term87) : term93.
Proof. exact (EQ_MP (@lem1699560) (@lem1699559 h1 h2 h3)). Qed.
Lemma lem1699562 (h1 : term83) (h2 : term87) : term97.
Proof. exact (fun h0 : term112 => @lem1699561 h0 h1 h2). Qed.
Lemma lem1699563 (h1 : term87) : term100.
Proof. exact (fun h0 : term83 => @lem1699562 h0 h1). Qed.
Lemma lem1699564 : term102.
Proof. exact (fun h0 : term87 => @lem1699563 h0). Qed.
Lemma lem1699565 : term88.
Proof. exact (EQ_MP (@lem1698854) (@lem1699564)). Qed.
Lemma lem1699567 : term88.
Proof. exact (@lem1698690 (@lem1699565)). Qed.
Lemma lem1699568 (h1 : term87) : term99.
Proof. exact (@lem1699567 (@lem1698675 h1)). Qed.
Lemma lem1699569 (h1 : term87) : term96.
Proof. exact (@lem1699568 h1 (@lem1698670)). Qed.
Lemma lem1699570 (h1 : term87) : term92.
Proof. exact (@lem1699569 h1 (@lem1340339)). Qed.
Lemma lem1699571 (h1 : term87) : False.
Proof. exact (@lem1699570 h1 (@lem1698434)). Qed.
Lemma lem1699572 (h1 : term87) : term87 = False.
Proof. exact (prop_ext (fun h2 : term87 => @lem1699571 h1) (fun h2 : False => @lem1698675 h1)). Qed.
Lemma lem1699573 (h1 : term87) : False.
Proof. exact (EQ_MP (@lem1699572 h1) (@lem1698675 h1)). Qed.
Lemma lem1699574 : term86.
Proof. exact (fun h0 : term87 => @lem1699573 h0). Qed.
Lemma lem1699575 : term85.
Proof. exact (EQ_MP (@lem1698674) (@lem1699574)). Qed.

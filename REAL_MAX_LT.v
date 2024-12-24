Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_LT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482710_spec.
Require Import thm1483205_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1568473 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17045 (real_lt x z) (real_lt y z)). Qed.
Lemma lem1568479 (x : real) (y : real) (z : real) : (term2 x y z) = (term2 x y z).
Proof. exact (eq_refl (term2 x y z)). Qed.
Lemma lem1568481 (x : real) (y : real) (z : real) : (term3 x y z) = (term3 x y z).
Proof. exact (eq_refl (term3 x y z)). Qed.
Lemma lem1568482 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (MK_COMB (@lem1568481 x y z) (@lem1568473 x y z)). Qed.
Lemma lem1568483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568484 (x : real) (y : real) (z : real) : (term6 x y z) = (term7 x y z).
Proof. exact (MK_COMB (@lem1568483) (@lem1568482 x y z)). Qed.
Lemma lem1568485 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1568484 x y z) (@lem1568479 x y z)). Qed.
Lemma lem1568486 (x : real) (y : real) (z : real) : (term10 x y z) = (term8 x y z).
Proof. exact (@lem17646 (term11 x y z) (term12 x y z)). Qed.
Lemma lem1568487 (x : real) (y : real) (z : real) : (term10 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1568486 x y z) (@lem1568485 x y z)). Qed.
Lemma lem1568488 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1568489 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1568488 (term17 x y)). Qed.
Lemma lem1568490 (x : real) (y : real) (z : real) : (term18 x y z) = ((term11 x y z) = (term12 x y z)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1568491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1568492 (x : real) (y : real) (z : real) : (term19 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1568491) (@lem1568490 x y z)). Qed.
Lemma lem1568493 (x : real) (y : real) (z : real) : (term19 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1568492 x y z) (@lem1568487 x y z)). Qed.
Lemma lem1568494 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1568493 x y z)). Qed.
Lemma lem1568495 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568496 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1568495) (@lem1568494 x y)). Qed.
Lemma lem1568497 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1568489 x y) (@lem1568496 x y)). Qed.
Lemma lem1568498 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1568499 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1568498 (term25 x)). Qed.
Lemma lem1568500 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1568501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1568502 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1568501) (@lem1568500 x y)). Qed.
Lemma lem1568503 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1568502 x y) (@lem1568497 x y)). Qed.
Lemma lem1568504 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1568503 x y)). Qed.
Lemma lem1568505 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568506 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1568505) (@lem1568504 x)). Qed.
Lemma lem1568507 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1568499 x) (@lem1568506 x)). Qed.
Lemma lem1568508 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1568509 : term32 = term33.
Proof. exact (@lem1568508 term34). Qed.
Lemma lem1568510 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1568511 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1568512 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1568511) (@lem1568510 x)). Qed.
Lemma lem1568513 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1568512 x) (@lem1568507 x)). Qed.
Lemma lem1568514 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1568513 x)). Qed.
Lemma lem1568515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568516 : term33 = term40.
Proof. exact (MK_COMB (@lem1568515) (@lem1568514)). Qed.
Lemma lem1568518 : term32 = term40.
Proof. exact (TRANS (@lem1568509) (@lem1568516)). Qed.
Lemma lem1568545 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1568546 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1568545 x y z)). Qed.
Lemma lem1568547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568548 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1568547) (@lem1568546 x y)). Qed.
Lemma lem1568549 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1568548 x y)). Qed.
Lemma lem1568550 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568551 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1568550) (@lem1568549 x)). Qed.
Lemma lem1568552 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1568551 x)). Qed.
Lemma lem1568553 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568554 : term40 = term40.
Proof. exact (MK_COMB (@lem1568553) (@lem1568552)). Qed.
Lemma lem1568555 : term32 = term40.
Proof. exact (TRANS (@lem1568518) (@lem1568554)). Qed.
Lemma lem1568556 (z : real) (x : real) (y : real) : (term11 x y z) = (term41 z x y).
Proof. exact (@lem1483521 z (real_max x y)). Qed.
Lemma lem1568569 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1568570 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568571 (z : real) (x : real) (y : real) : (term44 z x y) = (term45 z x y).
Proof. exact (MK_COMB (@lem1568570) (@lem1568569 z x y)). Qed.
Lemma lem1568572 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568573 (z : real) (x : real) (y : real) : (term41 z x y) = (term47 z x y).
Proof. exact (MK_COMB (@lem1568571 z x y) (@lem1568572)). Qed.
Lemma lem1568574 (z : real) (x : real) (y : real) : (term11 x y z) = (term47 z x y).
Proof. exact (TRANS (@lem1568556 z x y) (@lem1568573 z x y)). Qed.
Lemma lem1568575 (x : real) (z : real) : (term48 x z) = (term49 x z).
Proof. exact (@lem1483531 x z). Qed.
Lemma lem1568588 (x : real) (z : real) : (real_sub x z) = (term50 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1568589 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568590 (x : real) (z : real) : (term51 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1568589) (@lem1568588 x z)). Qed.
Lemma lem1568591 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568592 (x : real) (z : real) : (term49 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1568590 x z) (@lem1568591)). Qed.
Lemma lem1568593 (x : real) (z : real) : (term48 x z) = (term53 x z).
Proof. exact (TRANS (@lem1568575 x z) (@lem1568592 x z)). Qed.
Lemma lem1568594 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483531 y z). Qed.
Lemma lem1568607 (y : real) (z : real) : (real_sub y z) = (term50 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1568608 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568609 (y : real) (z : real) : (term51 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1568608) (@lem1568607 y z)). Qed.
Lemma lem1568610 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568611 (y : real) (z : real) : (term49 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1568609 y z) (@lem1568610)). Qed.
Lemma lem1568612 (y : real) (z : real) : (term48 y z) = (term53 y z).
Proof. exact (TRANS (@lem1568594 y z) (@lem1568611 y z)). Qed.
Lemma lem1568613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568614 (x : real) (z : real) : (term54 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1568613) (@lem1568593 x z)). Qed.
Lemma lem1568615 (x : real) (y : real) (z : real) : (term1 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1568614 x z) (@lem1568612 y z)). Qed.
Lemma lem1568616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1568617 (z : real) (x : real) (y : real) : (term3 x y z) = (term57 z x y).
Proof. exact (MK_COMB (@lem1568616) (@lem1568574 z x y)). Qed.
Lemma lem1568618 (x : real) (y : real) (z : real) : (term5 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem1568617 z x y) (@lem1568615 x y z)). Qed.
Lemma lem1568619 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483531 (real_max x y) z). Qed.
Lemma lem1568625 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1568630 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (@lem1483488 (term64 z) (real_max x y)). Qed.
Lemma lem1568632 (z : real) (x : real) (y : real) : (term61 x y z) = (term63 z x y).
Proof. exact (TRANS (@lem1568625 x y z) (@lem1568630 z x y)). Qed.
Lemma lem1568633 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568634 (z : real) (x : real) (y : real) : (term65 x y z) = (term66 z x y).
Proof. exact (MK_COMB (@lem1568633) (@lem1568632 z x y)). Qed.
Lemma lem1568635 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568636 (z : real) (x : real) (y : real) : (term60 x y z) = (term67 z x y).
Proof. exact (MK_COMB (@lem1568634 z x y) (@lem1568635)). Qed.
Lemma lem1568637 (z : real) (x : real) (y : real) : (term59 x y z) = (term67 z x y).
Proof. exact (TRANS (@lem1568619 x y z) (@lem1568636 z x y)). Qed.
Lemma lem1568638 (z : real) (x : real) : (real_lt x z) = (term68 z x).
Proof. exact (@lem1483521 z x). Qed.
Lemma lem1568644 (z : real) (x : real) : (real_sub z x) = (term50 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1568649 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1568651 (x : real) (z : real) : (real_sub z x) = (term69 x z).
Proof. exact (TRANS (@lem1568644 z x) (@lem1568649 x z)). Qed.
Lemma lem1568652 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568653 (x : real) (z : real) : (term70 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1568652) (@lem1568651 x z)). Qed.
Lemma lem1568654 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568655 (x : real) (z : real) : (term68 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1568653 x z) (@lem1568654)). Qed.
Lemma lem1568656 (x : real) (z : real) : (real_lt x z) = (term72 x z).
Proof. exact (TRANS (@lem1568638 z x) (@lem1568655 x z)). Qed.
Lemma lem1568657 (z : real) (y : real) : (real_lt y z) = (term68 z y).
Proof. exact (@lem1483521 z y). Qed.
Lemma lem1568663 (z : real) (y : real) : (real_sub z y) = (term50 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1568668 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1568670 (y : real) (z : real) : (real_sub z y) = (term69 y z).
Proof. exact (TRANS (@lem1568663 z y) (@lem1568668 y z)). Qed.
Lemma lem1568671 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568672 (y : real) (z : real) : (term70 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1568671) (@lem1568670 y z)). Qed.
Lemma lem1568673 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568674 (y : real) (z : real) : (term68 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1568672 y z) (@lem1568673)). Qed.
Lemma lem1568675 (y : real) (z : real) : (real_lt y z) = (term72 y z).
Proof. exact (TRANS (@lem1568657 z y) (@lem1568674 y z)). Qed.
Lemma lem1568676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1568677 (x : real) (z : real) : (term73 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1568676) (@lem1568656 x z)). Qed.
Lemma lem1568678 (x : real) (y : real) (z : real) : (term12 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1568677 x z) (@lem1568675 y z)). Qed.
Lemma lem1568679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1568680 (z : real) (x : real) (y : real) : (term76 x y z) = (term77 z x y).
Proof. exact (MK_COMB (@lem1568679) (@lem1568637 z x y)). Qed.
Lemma lem1568681 (x : real) (y : real) (z : real) : (term2 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1568680 z x y) (@lem1568678 x y z)). Qed.
Lemma lem1568682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568683 (x : real) (y : real) (z : real) : (term7 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1568682) (@lem1568618 x y z)). Qed.
Lemma lem1568684 (x : real) (y : real) (z : real) : (term9 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1568683 x y z) (@lem1568681 x y z)). Qed.
Lemma lem1568685 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1568684 x y z)). Qed.
Lemma lem1568686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568687 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1568686) (@lem1568685 x y)). Qed.
Lemma lem1568688 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1568687 x y)). Qed.
Lemma lem1568689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568690 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1568689) (@lem1568688 x)). Qed.
Lemma lem1568691 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1568690 x)). Qed.
Lemma lem1568692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568693 : term40 = term86.
Proof. exact (MK_COMB (@lem1568692) (@lem1568691)). Qed.
Lemma lem1568694 : term32 = term86.
Proof. exact (TRANS (@lem1568555) (@lem1568693)). Qed.
Lemma lem1568704 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1568705 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1568704 real P Q). Qed.
Lemma lem1568706 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1568705 (term93 x y) (term94 x y)). Qed.
Lemma lem1568707 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1568708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568709 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1568708) (@lem1568707 x y z)). Qed.
Lemma lem1568710 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1568711 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1568709 x y z) (@lem1568710 x y z)). Qed.
Lemma lem1568712 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1568711 x y z)). Qed.
Lemma lem1568713 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568714 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1568713) (@lem1568712 x y)). Qed.
Lemma lem1568715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1568716 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1568715) (@lem1568714 x y)). Qed.
Lemma lem1568717 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1568718 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1568717 x y z)). Qed.
Lemma lem1568719 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568720 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1568719) (@lem1568718 x y)). Qed.
Lemma lem1568721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568722 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1568721) (@lem1568720 x y)). Qed.
Lemma lem1568723 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1568724 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1568723 x y z)). Qed.
Lemma lem1568725 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568726 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1568725) (@lem1568724 x y)). Qed.
Lemma lem1568727 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1568722 x y) (@lem1568726 x y)). Qed.
Lemma lem1568728 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1568716 x y) (@lem1568727 x y)). Qed.
Lemma lem1568729 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1568728 x y) (@lem1568706 x y)). Qed.
Lemma lem1568826 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1568729 x y)). Qed.
Lemma lem1568827 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568828 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1568827) (@lem1568826 x)). Qed.
Lemma lem1568830 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1568831 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1568830 real P Q). Qed.
Lemma lem1568832 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1568831 (term115 x) (term116 x)). Qed.
Lemma lem1568833 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1568834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568835 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1568834) (@lem1568833 x y)). Qed.
Lemma lem1568836 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1568837 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1568835 x y) (@lem1568836 x y)). Qed.
Lemma lem1568838 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1568837 x y)). Qed.
Lemma lem1568839 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568840 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1568839) (@lem1568838 x)). Qed.
Lemma lem1568841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1568842 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1568841) (@lem1568840 x)). Qed.
Lemma lem1568843 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1568844 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1568843 x y)). Qed.
Lemma lem1568845 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568846 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1568845) (@lem1568844 x)). Qed.
Lemma lem1568847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568848 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1568847) (@lem1568846 x)). Qed.
Lemma lem1568849 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1568850 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1568849 x y)). Qed.
Lemma lem1568851 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568852 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1568851) (@lem1568850 x)). Qed.
Lemma lem1568853 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1568848 x) (@lem1568852 x)). Qed.
Lemma lem1568854 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1568842 x) (@lem1568853 x)). Qed.
Lemma lem1568855 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1568854 x) (@lem1568832 x)). Qed.
Lemma lem1568960 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1568828 x) (@lem1568855 x)). Qed.
Lemma lem1568961 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1568960 x)). Qed.
Lemma lem1568962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568963 : term86 = term134.
Proof. exact (MK_COMB (@lem1568962) (@lem1568961)). Qed.
Lemma lem1568965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1568966 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1568965 real P Q). Qed.
Lemma lem1568967 : term135 = term136.
Proof. exact (@lem1568966 term137 term138). Qed.
Lemma lem1568968 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1568969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568970 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1568969) (@lem1568968 x)). Qed.
Lemma lem1568971 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1568972 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1568970 x) (@lem1568971 x)). Qed.
Lemma lem1568973 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1568972 x)). Qed.
Lemma lem1568974 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568975 : term135 = term134.
Proof. exact (MK_COMB (@lem1568974) (@lem1568973)). Qed.
Lemma lem1568976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1568977 : term144 = term145.
Proof. exact (MK_COMB (@lem1568976) (@lem1568975)). Qed.
Lemma lem1568978 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1568979 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1568978 x)). Qed.
Lemma lem1568980 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568981 : term147 = term148.
Proof. exact (MK_COMB (@lem1568980) (@lem1568979)). Qed.
Lemma lem1568982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568983 : term149 = term150.
Proof. exact (MK_COMB (@lem1568982) (@lem1568981)). Qed.
Lemma lem1568984 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1568985 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1568984 x)). Qed.
Lemma lem1568986 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1568987 : term152 = term153.
Proof. exact (MK_COMB (@lem1568986) (@lem1568985)). Qed.
Lemma lem1568988 : term136 = term154.
Proof. exact (MK_COMB (@lem1568983) (@lem1568987)). Qed.
Lemma lem1568989 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1568977) (@lem1568988)). Qed.
Lemma lem1568990 : term134 = term154.
Proof. exact (EQ_MP (@lem1568989) (@lem1568967)). Qed.
Lemma lem1569103 : term86 = term154.
Proof. exact (TRANS (@lem1568963) (@lem1568990)). Qed.
Lemma lem1569105 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1569106 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1569105 real P Q). Qed.
Lemma lem1569107 : term136 = term135.
Proof. exact (@lem1569106 term137 term138). Qed.
Lemma lem1569108 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1569109 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1569108 x)). Qed.
Lemma lem1569110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569111 : term147 = term148.
Proof. exact (MK_COMB (@lem1569110) (@lem1569109)). Qed.
Lemma lem1569112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569113 : term149 = term150.
Proof. exact (MK_COMB (@lem1569112) (@lem1569111)). Qed.
Lemma lem1569114 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1569115 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1569114 x)). Qed.
Lemma lem1569116 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569117 : term152 = term153.
Proof. exact (MK_COMB (@lem1569116) (@lem1569115)). Qed.
Lemma lem1569118 : term136 = term154.
Proof. exact (MK_COMB (@lem1569113) (@lem1569117)). Qed.
Lemma lem1569119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1569120 : term155 = term156.
Proof. exact (MK_COMB (@lem1569119) (@lem1569118)). Qed.
Lemma lem1569121 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1569122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569123 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1569122) (@lem1569121 x)). Qed.
Lemma lem1569124 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1569125 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1569123 x) (@lem1569124 x)). Qed.
Lemma lem1569126 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1569125 x)). Qed.
Lemma lem1569127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569128 : term135 = term134.
Proof. exact (MK_COMB (@lem1569127) (@lem1569126)). Qed.
Lemma lem1569129 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1569120) (@lem1569128)). Qed.
Lemma lem1569130 : term154 = term134.
Proof. exact (EQ_MP (@lem1569129) (@lem1569107)). Qed.
Lemma lem1569132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1569133 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1569132 real P Q). Qed.
Lemma lem1569134 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1569133 (term115 x) (term116 x)). Qed.
Lemma lem1569135 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1569136 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1569135 x y)). Qed.
Lemma lem1569137 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569138 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1569137) (@lem1569136 x)). Qed.
Lemma lem1569139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569140 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1569139) (@lem1569138 x)). Qed.
Lemma lem1569141 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1569142 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1569141 x y)). Qed.
Lemma lem1569143 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569144 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1569143) (@lem1569142 x)). Qed.
Lemma lem1569145 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1569140 x) (@lem1569144 x)). Qed.
Lemma lem1569146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1569147 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1569146) (@lem1569145 x)). Qed.
Lemma lem1569148 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1569149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569150 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1569149) (@lem1569148 x y)). Qed.
Lemma lem1569151 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1569152 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1569150 x y) (@lem1569151 x y)). Qed.
Lemma lem1569153 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1569152 x y)). Qed.
Lemma lem1569154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569155 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1569154) (@lem1569153 x)). Qed.
Lemma lem1569156 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1569147 x) (@lem1569155 x)). Qed.
Lemma lem1569157 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1569156 x) (@lem1569134 x)). Qed.
Lemma lem1569159 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1569160 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1569159 real P Q). Qed.
Lemma lem1569161 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1569160 (term93 x y) (term94 x y)). Qed.
Lemma lem1569162 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1569163 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1569162 x y z)). Qed.
Lemma lem1569164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569165 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1569164) (@lem1569163 x y)). Qed.
Lemma lem1569166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569167 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1569166) (@lem1569165 x y)). Qed.
Lemma lem1569168 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1569169 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1569168 x y z)). Qed.
Lemma lem1569170 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569171 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1569170) (@lem1569169 x y)). Qed.
Lemma lem1569172 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1569167 x y) (@lem1569171 x y)). Qed.
Lemma lem1569173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1569174 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1569173) (@lem1569172 x y)). Qed.
Lemma lem1569175 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1569176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569177 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1569176) (@lem1569175 x y z)). Qed.
Lemma lem1569178 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1569179 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1569177 x y z) (@lem1569178 x y z)). Qed.
Lemma lem1569180 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1569179 x y z)). Qed.
Lemma lem1569181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569182 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1569181) (@lem1569180 x y)). Qed.
Lemma lem1569183 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1569174 x y) (@lem1569182 x y)). Qed.
Lemma lem1569184 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1569183 x y) (@lem1569161 x y)). Qed.
Lemma lem1569185 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1569184 x y)). Qed.
Lemma lem1569186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569187 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1569186) (@lem1569185 x)). Qed.
Lemma lem1569188 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1569157 x) (@lem1569187 x)). Qed.
Lemma lem1569189 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1569188 x)). Qed.
Lemma lem1569190 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569191 : term134 = term86.
Proof. exact (MK_COMB (@lem1569190) (@lem1569189)). Qed.
Lemma lem1569192 : term154 = term86.
Proof. exact (TRANS (@lem1569130) (@lem1569191)). Qed.
Lemma lem1569193 : term86 = term86.
Proof. exact (TRANS (@lem1569103) (@lem1569192)). Qed.
Lemma lem1569196 : term32 = term86.
Proof. exact (TRANS (@lem1568694) (@lem1569193)). Qed.
Lemma lem1569209 (x : real) (y : real) (z : real) : (term78 x y z) = (term78 x y z).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1569226 (x : real) (y : real) (z : real) : (term58 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term53 x z) (term47 z x y) (term53 y z)). Qed.
Lemma lem1569227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569228 (x : real) (y : real) (z : real) : (term79 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1569227) (@lem1569226 x y z)). Qed.
Lemma lem1569229 (x : real) (y : real) (z : real) : (term80 x y z) = (term163 x y z).
Proof. exact (MK_COMB (@lem1569228 x y z) (@lem1569209 x y z)). Qed.
Lemma lem1569230 (x : real) (y : real) : (term81 x y) = (term164 x y).
Proof. exact (fun_ext (fun z : real => @lem1569229 x y z)). Qed.
Lemma lem1569231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569232 (x : real) (y : real) : (term82 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1569231) (@lem1569230 x y)). Qed.
Lemma lem1569233 (x : real) : (term83 x) = (term166 x).
Proof. exact (fun_ext (fun y : real => @lem1569232 x y)). Qed.
Lemma lem1569234 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569235 (x : real) : (term84 x) = (term167 x).
Proof. exact (MK_COMB (@lem1569234) (@lem1569233 x)). Qed.
Lemma lem1569236 : term85 = term168.
Proof. exact (fun_ext (fun x : real => @lem1569235 x)). Qed.
Lemma lem1569237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1569238 : term86 = term169.
Proof. exact (MK_COMB (@lem1569237) (@lem1569236)). Qed.
Lemma lem1569239 : term32 = term169.
Proof. exact (TRANS (@lem1569196) (@lem1569238)). Qed.
Lemma lem1569241 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1569242 (x : real) (z : real) (y : real) : (term47 z x y) = (term172 x z y).
Proof. exact (@lem1569241 x z y term46). Qed.
Lemma lem1569255 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1569256 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569257 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1569256) (@lem1569255 y z)). Qed.
Lemma lem1569258 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569259 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1569257 y z) (@lem1569258)). Qed.
Lemma lem1569272 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1569273 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569274 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1569273) (@lem1569272 x z)). Qed.
Lemma lem1569275 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569276 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1569274 x z) (@lem1569275)). Qed.
Lemma lem1569277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569278 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1569277) (@lem1569276 x z)). Qed.
Lemma lem1569279 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1569278 x z) (@lem1569259 y z)). Qed.
Lemma lem1569280 (x : real) (y : real) (z : real) : (term47 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1569242 x z y) (@lem1569279 x y z)). Qed.
Lemma lem1569281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569282 (x : real) (y : real) (z : real) : (term57 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1569281) (@lem1569280 x y z)). Qed.
Lemma lem1569283 (x : real) (z : real) : (term53 x z) = (term53 x z).
Proof. exact (eq_refl (term53 x z)). Qed.
Lemma lem1569286 (y : real) (x : real) (z : real) : (term177 y x z) = (term178 y x z).
Proof. exact (MK_COMB (@lem1569282 x y z) (@lem1569283 x z)). Qed.
Lemma lem1569288 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1569289 (x : real) (z : real) (y : real) : (term47 z x y) = (term172 x z y).
Proof. exact (@lem1569288 x z y term46). Qed.
Lemma lem1569302 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1569303 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569304 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1569303) (@lem1569302 y z)). Qed.
Lemma lem1569305 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569306 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1569304 y z) (@lem1569305)). Qed.
Lemma lem1569319 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1569320 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569321 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1569320) (@lem1569319 x z)). Qed.
Lemma lem1569322 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569323 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1569321 x z) (@lem1569322)). Qed.
Lemma lem1569324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569325 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1569324) (@lem1569323 x z)). Qed.
Lemma lem1569326 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1569325 x z) (@lem1569306 y z)). Qed.
Lemma lem1569327 (x : real) (y : real) (z : real) : (term47 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1569289 x z y) (@lem1569326 x y z)). Qed.
Lemma lem1569328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569329 (x : real) (y : real) (z : real) : (term57 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1569328) (@lem1569327 x y z)). Qed.
Lemma lem1569330 (y : real) (z : real) : (term53 y z) = (term53 y z).
Proof. exact (eq_refl (term53 y z)). Qed.
Lemma lem1569333 (x : real) (y : real) (z : real) : (term179 x y z) = (term180 x y z).
Proof. exact (MK_COMB (@lem1569329 x y z) (@lem1569330 y z)). Qed.
Lemma lem1569334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569335 (y : real) (x : real) (z : real) : (term181 y x z) = (term182 y x z).
Proof. exact (MK_COMB (@lem1569334) (@lem1569286 y x z)). Qed.
Lemma lem1569336 (x : real) (y : real) (z : real) : (term161 x y z) = (term183 x y z).
Proof. exact (MK_COMB (@lem1569335 y x z) (@lem1569333 x y z)). Qed.
Lemma lem1569338 (x : real) (y : real) (z : real) : (term184 z x y) = (term78 x y z).
Proof. exact (eq_refl (term184 z x y)). Qed.
Lemma lem1569339 (z : real) (x : real) (y : real) : (term78 x y z) = (term184 z x y).
Proof. exact (SYM (@lem1569338 x y z)). Qed.
Lemma lem1569340 (y : real) (z : real) (x : real) : (term184 z x y) = (term185 y z x).
Proof. exact (@lem1483205 y (term186 x y z) x). Qed.
Lemma lem1569341 (y : real) (z : real) (x : real) : (term78 x y z) = (term185 y z x).
Proof. exact (TRANS (@lem1569339 z x y) (@lem1569340 y z x)). Qed.
Lemma lem1569342 (x : real) (y : real) (z : real) : (term187 y z x) = (term188 x y z).
Proof. exact (eq_refl (term187 y z x)). Qed.
Lemma lem1569343 (x : real) (y : real) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1569344 (x : real) (y : real) (z : real) : (term190 y z x) = (term191 x y z).
Proof. exact (MK_COMB (@lem1569343 x y) (@lem1569342 x y z)). Qed.
Lemma lem1569345 (x : real) (y : real) (z : real) : (term192 x z y) = (term193 x y z).
Proof. exact (eq_refl (term192 x z y)). Qed.
Lemma lem1569346 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1569347 (x : real) (y : real) (z : real) : (term195 x z y) = (term196 x y z).
Proof. exact (MK_COMB (@lem1569346 y x) (@lem1569345 x y z)). Qed.
Lemma lem1569348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569349 (x : real) (y : real) (z : real) : (term197 x z y) = (term198 x y z).
Proof. exact (MK_COMB (@lem1569348) (@lem1569347 x y z)). Qed.
Lemma lem1569350 (x : real) (y : real) (z : real) : (term185 y z x) = (term199 x y z).
Proof. exact (MK_COMB (@lem1569349 x y z) (@lem1569344 x y z)). Qed.
Lemma lem1569351 (x : real) (y : real) (z : real) : (term200 x y z) = (term200 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1569352 (x : real) (y : real) (z : real) : ((term78 x y z) = (term185 y z x)) = ((term78 x y z) = (term199 x y z)).
Proof. exact (MK_COMB (@lem1569351 x y z) (@lem1569350 x y z)). Qed.
Lemma lem1569353 (x : real) (y : real) (z : real) : (term78 x y z) = (term199 x y z).
Proof. exact (EQ_MP (@lem1569352 x y z) (@lem1569341 y z x)). Qed.
Lemma lem1569354 (y : real) (x : real) : (real_ge y x) = (term49 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1569360 (y : real) (x : real) : (real_sub y x) = (term50 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1569365 (x : real) (y : real) : (term50 y x) = (term69 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1569367 (x : real) (y : real) : (real_sub y x) = (term69 x y).
Proof. exact (TRANS (@lem1569360 y x) (@lem1569365 x y)). Qed.
Lemma lem1569368 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569369 (x : real) (y : real) : (term51 y x) = (term201 x y).
Proof. exact (MK_COMB (@lem1569368) (@lem1569367 x y)). Qed.
Lemma lem1569370 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569371 (x : real) (y : real) : (term49 y x) = (term202 x y).
Proof. exact (MK_COMB (@lem1569369 x y) (@lem1569370)). Qed.
Lemma lem1569372 (x : real) (y : real) : (real_ge y x) = (term202 x y).
Proof. exact (TRANS (@lem1569354 y x) (@lem1569371 x y)). Qed.
Lemma lem1569373 (z : real) (y : real) : (term202 z y) = (term203 z y).
Proof. exact (@lem1483527 (term69 z y) term46). Qed.
Lemma lem1569374 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569387 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1569388 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1569389 (y : real) (z : real) : (term204 z y) = (term205 y z).
Proof. exact (MK_COMB (@lem1569388) (@lem1569387 y z)). Qed.
Lemma lem1569390 (y : real) (z : real) : (term206 z y) = (term207 y z).
Proof. exact (MK_COMB (@lem1569389 y z) (@lem1569374)). Qed.
Lemma lem1569391 (y : real) (z : real) : (term207 y z) = (term208 y z).
Proof. exact (@lem1483519 (term50 y z) term46). Qed.
Lemma lem1569393 (x : nat) : (term209 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1569394 : term210 = term46.
Proof. exact (@lem1569393 term211). Qed.
Lemma lem1569395 (y : real) (z : real) : (term212 y z) = (term212 y z).
Proof. exact (eq_refl (term212 y z)). Qed.
Lemma lem1569396 (y : real) (z : real) : (term208 y z) = (term213 y z).
Proof. exact (MK_COMB (@lem1569395 y z) (@lem1569394)). Qed.
Lemma lem1569397 (y : real) (z : real) : (term213 y z) = (term50 y z).
Proof. exact (@lem1483450 (term50 y z)). Qed.
Lemma lem1569398 (y : real) (z : real) : (term208 y z) = (term50 y z).
Proof. exact (TRANS (@lem1569396 y z) (@lem1569397 y z)). Qed.
Lemma lem1569399 (y : real) (z : real) : (term207 y z) = (term50 y z).
Proof. exact (TRANS (@lem1569391 y z) (@lem1569398 y z)). Qed.
Lemma lem1569400 (y : real) (z : real) : (term206 z y) = (term50 y z).
Proof. exact (TRANS (@lem1569390 y z) (@lem1569399 y z)). Qed.
Lemma lem1569401 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569402 (y : real) (z : real) : (term214 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1569401) (@lem1569400 y z)). Qed.
Lemma lem1569403 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569404 (y : real) (z : real) : (term203 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1569402 y z) (@lem1569403)). Qed.
Lemma lem1569405 (y : real) (z : real) : (term202 z y) = (term53 y z).
Proof. exact (TRANS (@lem1569373 z y) (@lem1569404 y z)). Qed.
Lemma lem1569406 (x : real) (z : real) : (term72 x z) = (term215 x z).
Proof. exact (@lem1483525 (term69 x z) term46). Qed.
Lemma lem1569424 (x : real) (z : real) : (term206 x z) = (term216 x z).
Proof. exact (@lem1483519 (term69 x z) term46). Qed.
Lemma lem1569426 (x : nat) : (term209 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1569427 : term210 = term46.
Proof. exact (@lem1569426 term211). Qed.
Lemma lem1569428 (x : real) (z : real) : (term217 x z) = (term217 x z).
Proof. exact (eq_refl (term217 x z)). Qed.
Lemma lem1569429 (x : real) (z : real) : (term216 x z) = (term218 x z).
Proof. exact (MK_COMB (@lem1569428 x z) (@lem1569427)). Qed.
Lemma lem1569430 (x : real) (z : real) : (term218 x z) = (term69 x z).
Proof. exact (@lem1483450 (term69 x z)). Qed.
Lemma lem1569431 (x : real) (z : real) : (term216 x z) = (term69 x z).
Proof. exact (TRANS (@lem1569429 x z) (@lem1569430 x z)). Qed.
Lemma lem1569433 (x : real) (z : real) : (term206 x z) = (term69 x z).
Proof. exact (TRANS (@lem1569424 x z) (@lem1569431 x z)). Qed.
Lemma lem1569434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569435 (x : real) (z : real) : (term219 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1569434) (@lem1569433 x z)). Qed.
Lemma lem1569436 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569437 (x : real) (z : real) : (term215 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1569435 x z) (@lem1569436)). Qed.
Lemma lem1569438 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (TRANS (@lem1569406 x z) (@lem1569437 x z)). Qed.
Lemma lem1569439 (y : real) (z : real) : (term72 y z) = (term215 y z).
Proof. exact (@lem1483525 (term69 y z) term46). Qed.
Lemma lem1569457 (y : real) (z : real) : (term206 y z) = (term216 y z).
Proof. exact (@lem1483519 (term69 y z) term46). Qed.
Lemma lem1569459 (x : nat) : (term209 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1569460 : term210 = term46.
Proof. exact (@lem1569459 term211). Qed.
Lemma lem1569461 (y : real) (z : real) : (term217 y z) = (term217 y z).
Proof. exact (eq_refl (term217 y z)). Qed.
Lemma lem1569462 (y : real) (z : real) : (term216 y z) = (term218 y z).
Proof. exact (MK_COMB (@lem1569461 y z) (@lem1569460)). Qed.
Lemma lem1569463 (y : real) (z : real) : (term218 y z) = (term69 y z).
Proof. exact (@lem1483450 (term69 y z)). Qed.
Lemma lem1569464 (y : real) (z : real) : (term216 y z) = (term69 y z).
Proof. exact (TRANS (@lem1569462 y z) (@lem1569463 y z)). Qed.
Lemma lem1569466 (y : real) (z : real) : (term206 y z) = (term69 y z).
Proof. exact (TRANS (@lem1569457 y z) (@lem1569464 y z)). Qed.
Lemma lem1569467 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569468 (y : real) (z : real) : (term219 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1569467) (@lem1569466 y z)). Qed.
Lemma lem1569469 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569470 (y : real) (z : real) : (term215 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1569468 y z) (@lem1569469)). Qed.
Lemma lem1569471 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (TRANS (@lem1569439 y z) (@lem1569470 y z)). Qed.
Lemma lem1569472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569473 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1569472) (@lem1569438 x z)). Qed.
Lemma lem1569474 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1569473 x z) (@lem1569471 y z)). Qed.
Lemma lem1569475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569476 (y : real) (z : real) : (term220 z y) = (term221 y z).
Proof. exact (MK_COMB (@lem1569475) (@lem1569405 y z)). Qed.
Lemma lem1569477 (x : real) (y : real) (z : real) : (term193 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1569476 y z) (@lem1569474 x y z)). Qed.
Lemma lem1569478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569479 (x : real) (y : real) : (term194 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem1569478) (@lem1569372 x y)). Qed.
Lemma lem1569480 (x : real) (y : real) (z : real) : (term196 x y z) = (term223 x y z).
Proof. exact (MK_COMB (@lem1569479 x y) (@lem1569477 x y z)). Qed.
Lemma lem1569481 (x : real) (y : real) : (real_gt x y) = (term68 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1569494 (x : real) (y : real) : (real_sub x y) = (term50 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1569495 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569496 (x : real) (y : real) : (term70 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1569495) (@lem1569494 x y)). Qed.
Lemma lem1569497 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569498 (x : real) (y : real) : (term68 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1569496 x y) (@lem1569497)). Qed.
Lemma lem1569499 (x : real) (y : real) : (real_gt x y) = (term174 x y).
Proof. exact (TRANS (@lem1569481 x y) (@lem1569498 x y)). Qed.
Lemma lem1569500 (z : real) (x : real) : (term202 z x) = (term203 z x).
Proof. exact (@lem1483527 (term69 z x) term46). Qed.
Lemma lem1569501 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569514 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1569515 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1569516 (x : real) (z : real) : (term204 z x) = (term205 x z).
Proof. exact (MK_COMB (@lem1569515) (@lem1569514 x z)). Qed.
Lemma lem1569517 (x : real) (z : real) : (term206 z x) = (term207 x z).
Proof. exact (MK_COMB (@lem1569516 x z) (@lem1569501)). Qed.
Lemma lem1569518 (x : real) (z : real) : (term207 x z) = (term208 x z).
Proof. exact (@lem1483519 (term50 x z) term46). Qed.
Lemma lem1569520 (x : nat) : (term209 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1569521 : term210 = term46.
Proof. exact (@lem1569520 term211). Qed.
Lemma lem1569522 (x : real) (z : real) : (term212 x z) = (term212 x z).
Proof. exact (eq_refl (term212 x z)). Qed.
Lemma lem1569523 (x : real) (z : real) : (term208 x z) = (term213 x z).
Proof. exact (MK_COMB (@lem1569522 x z) (@lem1569521)). Qed.
Lemma lem1569524 (x : real) (z : real) : (term213 x z) = (term50 x z).
Proof. exact (@lem1483450 (term50 x z)). Qed.
Lemma lem1569525 (x : real) (z : real) : (term208 x z) = (term50 x z).
Proof. exact (TRANS (@lem1569523 x z) (@lem1569524 x z)). Qed.
Lemma lem1569526 (x : real) (z : real) : (term207 x z) = (term50 x z).
Proof. exact (TRANS (@lem1569518 x z) (@lem1569525 x z)). Qed.
Lemma lem1569527 (x : real) (z : real) : (term206 z x) = (term50 x z).
Proof. exact (TRANS (@lem1569517 x z) (@lem1569526 x z)). Qed.
Lemma lem1569528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569529 (x : real) (z : real) : (term214 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1569528) (@lem1569527 x z)). Qed.
Lemma lem1569530 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569531 (x : real) (z : real) : (term203 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1569529 x z) (@lem1569530)). Qed.
Lemma lem1569532 (x : real) (z : real) : (term202 z x) = (term53 x z).
Proof. exact (TRANS (@lem1569500 z x) (@lem1569531 x z)). Qed.
Lemma lem1569533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569534 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1569533) (@lem1569438 x z)). Qed.
Lemma lem1569535 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1569534 x z) (@lem1569471 y z)). Qed.
Lemma lem1569536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569537 (x : real) (z : real) : (term220 z x) = (term221 x z).
Proof. exact (MK_COMB (@lem1569536) (@lem1569532 x z)). Qed.
Lemma lem1569538 (x : real) (y : real) (z : real) : (term188 x y z) = (term224 x y z).
Proof. exact (MK_COMB (@lem1569537 x z) (@lem1569535 x y z)). Qed.
Lemma lem1569539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1569540 (x : real) (y : real) : (term189 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1569539) (@lem1569499 x y)). Qed.
Lemma lem1569541 (x : real) (y : real) (z : real) : (term191 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1569540 x y) (@lem1569538 x y z)). Qed.
Lemma lem1569542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569543 (x : real) (y : real) (z : real) : (term198 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1569542) (@lem1569480 x y z)). Qed.
Lemma lem1569544 (x : real) (y : real) (z : real) : (term199 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1569543 x y z) (@lem1569541 x y z)). Qed.
Lemma lem1569556 (x : real) (y : real) (z : real) : (term78 x y z) = (term227 x y z).
Proof. exact (TRANS (@lem1569353 x y z) (@lem1569544 x y z)). Qed.
Lemma lem1569557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1569558 (x : real) (y : real) (z : real) : (term162 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1569557) (@lem1569336 x y z)). Qed.
Lemma lem1569559 (x : real) (y : real) (z : real) : (term163 x y z) = (term229 x y z).
Proof. exact (MK_COMB (@lem1569558 x y z) (@lem1569556 x y z)). Qed.
Lemma lem1569560 (x : real) (y : real) (z : real) (h1 : term229 x y z) : term229 x y z.
Proof. exact (h1). Qed.
Lemma lem1569561 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1569562 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term178 y x z.
Proof. exact (h1). Qed.
Lemma lem1569563 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term53 x z.
Proof. exact (proj2 (@lem1569562 y x z h1)). Qed.
Lemma lem1569564 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term75 x y z.
Proof. exact (proj1 (@lem1569562 y x z h1)). Qed.
Lemma lem1569566 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (proj1 (@lem1569564 y x z h1)). Qed.
Lemma lem1569568 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569569 : term231 = term232.
Proof. exact (@lem1569568 (NUMERAL 0) term211). Qed.
Lemma lem1569570 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569571 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569572 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569571 h1) (fun h1 : term232 = True => @lem1569570)). Qed.
Lemma lem1569573 : term232 = True.
Proof. exact (EQ_MP (@lem1569572) (@lem1569570)). Qed.
Lemma lem1569574 : term231 = True.
Proof. exact (TRANS (@lem1569569) (@lem1569573)). Qed.
Lemma lem1569575 : True = term231.
Proof. exact (SYM (@lem1569574)). Qed.
Lemma lem1569576 : term231.
Proof. exact (EQ_MP (@lem1569575) (@lem0)). Qed.
Lemma lem1569577 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term234 x z.
Proof. exact (conj (@lem1569576) (@lem1569563 y x z h1)). Qed.
Lemma lem1569579 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1569580 (x : real) (z : real) : term236 x z.
Proof. exact (@lem1569579 term237 (term50 x z)). Qed.
Lemma lem1569581 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term238 x z.
Proof. exact (@lem1569580 x z (@lem1569577 y x z h1)). Qed.
Lemma lem1569582 (x : real) (z : real) : (term239 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1569583 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569584 (x : real) (z : real) : (term240 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1569583) (@lem1569582 x z)). Qed.
Lemma lem1569585 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569586 (x : real) (z : real) : (term238 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1569584 x z) (@lem1569585)). Qed.
Lemma lem1569587 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term53 x z.
Proof. exact (EQ_MP (@lem1569586 x z) (@lem1569581 y x z h1)). Qed.
Lemma lem1569589 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569590 : term231 = term232.
Proof. exact (@lem1569589 (NUMERAL 0) term211). Qed.
Lemma lem1569591 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569592 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569593 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569592 h1) (fun h1 : term232 = True => @lem1569591)). Qed.
Lemma lem1569594 : term232 = True.
Proof. exact (EQ_MP (@lem1569593) (@lem1569591)). Qed.
Lemma lem1569595 : term231 = True.
Proof. exact (TRANS (@lem1569590) (@lem1569594)). Qed.
Lemma lem1569596 : True = term231.
Proof. exact (SYM (@lem1569595)). Qed.
Lemma lem1569597 : term231.
Proof. exact (EQ_MP (@lem1569596) (@lem0)). Qed.
Lemma lem1569598 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term241 x z.
Proof. exact (conj (@lem1569597) (@lem1569566 y x z h1)). Qed.
Lemma lem1569600 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1569601 (x : real) (z : real) : term243 x z.
Proof. exact (@lem1569600 term237 (term69 x z)). Qed.
Lemma lem1569602 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term244 x z.
Proof. exact (@lem1569601 x z (@lem1569598 y x z h1)). Qed.
Lemma lem1569603 (x : real) (z : real) : (term245 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1569604 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569605 (x : real) (z : real) : (term246 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1569604) (@lem1569603 x z)). Qed.
Lemma lem1569606 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569607 (x : real) (z : real) : (term244 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1569605 x z) (@lem1569606)). Qed.
Lemma lem1569608 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1569607 x z) (@lem1569602 y x z h1)). Qed.
Lemma lem1569609 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term247 x z.
Proof. exact (conj (@lem1569608 y x z h1) (@lem1569587 y x z h1)). Qed.
Lemma lem1569611 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1569612 (x : real) (z : real) : term249 x z.
Proof. exact (@lem1569611 (term69 x z) (term50 x z)). Qed.
Lemma lem1569613 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term250 x z.
Proof. exact (@lem1569612 x z (@lem1569609 y x z h1)). Qed.
Lemma lem1569614 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483480 (term64 x) x z (term64 z)). Qed.
Lemma lem1569615 (x : real) : (term253 x) = (term254 x).
Proof. exact (@lem1483440 term255 x). Qed.
Lemma lem1569617 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569618 : term257 = term46.
Proof. exact (@lem1569617 term211). Qed.
Lemma lem1569619 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569620 : term258 = term259.
Proof. exact (MK_COMB (@lem1569619) (@lem1569618)). Qed.
Lemma lem1569621 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1569622 (x : real) : (term254 x) = (term260 x).
Proof. exact (MK_COMB (@lem1569620) (@lem1569621 x)). Qed.
Lemma lem1569623 (x : real) : (term253 x) = (term260 x).
Proof. exact (TRANS (@lem1569615 x) (@lem1569622 x)). Qed.
Lemma lem1569624 (x : real) : (term260 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1569625 (x : real) : (term253 x) = term46.
Proof. exact (TRANS (@lem1569623 x) (@lem1569624 x)). Qed.
Lemma lem1569626 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1569627 (x : real) : (term261 x) = term262.
Proof. exact (MK_COMB (@lem1569626) (@lem1569625 x)). Qed.
Lemma lem1569628 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1569630 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569631 : term257 = term46.
Proof. exact (@lem1569630 term211). Qed.
Lemma lem1569632 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569633 : term258 = term259.
Proof. exact (MK_COMB (@lem1569632) (@lem1569631)). Qed.
Lemma lem1569634 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1569635 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1569633) (@lem1569634 z)). Qed.
Lemma lem1569636 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1569628 z) (@lem1569635 z)). Qed.
Lemma lem1569637 (z : real) : (term260 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1569638 (z : real) : (term263 z) = term46.
Proof. exact (TRANS (@lem1569636 z) (@lem1569637 z)). Qed.
Lemma lem1569639 (x : real) (z : real) : (term252 x z) = term264.
Proof. exact (MK_COMB (@lem1569627 x) (@lem1569638 z)). Qed.
Lemma lem1569640 (x : real) (z : real) : (term251 x z) = term264.
Proof. exact (TRANS (@lem1569614 x z) (@lem1569639 x z)). Qed.
Lemma lem1569641 : term264 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1569642 (x : real) (z : real) : (term251 x z) = term46.
Proof. exact (TRANS (@lem1569640 x z) (@lem1569641)). Qed.
Lemma lem1569643 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569644 (x : real) (z : real) : (term265 x z) = term266.
Proof. exact (MK_COMB (@lem1569643) (@lem1569642 x z)). Qed.
Lemma lem1569645 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569646 (x : real) (z : real) : (term250 x z) = term267.
Proof. exact (MK_COMB (@lem1569644 x z) (@lem1569645)). Qed.
Lemma lem1569647 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term267.
Proof. exact (EQ_MP (@lem1569646 x z) (@lem1569613 y x z h1)). Qed.
Lemma lem1569649 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569650 : term267 = term268.
Proof. exact (@lem1569649 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1569651 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1569652 : term267 = False.
Proof. exact (TRANS (@lem1569650) (@lem1569651)). Qed.
Lemma lem1569653 (y : real) (x : real) (z : real) (h1 : term178 y x z) : False.
Proof. exact (EQ_MP (@lem1569652) (@lem1569647 y x z h1)). Qed.
Lemma lem1569654 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term180 x y z.
Proof. exact (h1). Qed.
Lemma lem1569655 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term53 y z.
Proof. exact (proj2 (@lem1569654 x y z h1)). Qed.
Lemma lem1569656 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term75 x y z.
Proof. exact (proj1 (@lem1569654 x y z h1)). Qed.
Lemma lem1569657 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (proj2 (@lem1569656 x y z h1)). Qed.
Lemma lem1569660 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569661 : term231 = term232.
Proof. exact (@lem1569660 (NUMERAL 0) term211). Qed.
Lemma lem1569662 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569663 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569664 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569663 h1) (fun h1 : term232 = True => @lem1569662)). Qed.
Lemma lem1569665 : term232 = True.
Proof. exact (EQ_MP (@lem1569664) (@lem1569662)). Qed.
Lemma lem1569666 : term231 = True.
Proof. exact (TRANS (@lem1569661) (@lem1569665)). Qed.
Lemma lem1569667 : True = term231.
Proof. exact (SYM (@lem1569666)). Qed.
Lemma lem1569668 : term231.
Proof. exact (EQ_MP (@lem1569667) (@lem0)). Qed.
Lemma lem1569669 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term234 y z.
Proof. exact (conj (@lem1569668) (@lem1569655 x y z h1)). Qed.
Lemma lem1569671 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1569672 (y : real) (z : real) : term236 y z.
Proof. exact (@lem1569671 term237 (term50 y z)). Qed.
Lemma lem1569673 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term238 y z.
Proof. exact (@lem1569672 y z (@lem1569669 x y z h1)). Qed.
Lemma lem1569674 (y : real) (z : real) : (term239 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1569675 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569676 (y : real) (z : real) : (term240 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1569675) (@lem1569674 y z)). Qed.
Lemma lem1569677 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569678 (y : real) (z : real) : (term238 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1569676 y z) (@lem1569677)). Qed.
Lemma lem1569679 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1569678 y z) (@lem1569673 x y z h1)). Qed.
Lemma lem1569681 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569682 : term231 = term232.
Proof. exact (@lem1569681 (NUMERAL 0) term211). Qed.
Lemma lem1569683 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569684 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569685 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569684 h1) (fun h1 : term232 = True => @lem1569683)). Qed.
Lemma lem1569686 : term232 = True.
Proof. exact (EQ_MP (@lem1569685) (@lem1569683)). Qed.
Lemma lem1569687 : term231 = True.
Proof. exact (TRANS (@lem1569682) (@lem1569686)). Qed.
Lemma lem1569688 : True = term231.
Proof. exact (SYM (@lem1569687)). Qed.
Lemma lem1569689 : term231.
Proof. exact (EQ_MP (@lem1569688) (@lem0)). Qed.
Lemma lem1569690 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term241 y z.
Proof. exact (conj (@lem1569689) (@lem1569657 x y z h1)). Qed.
Lemma lem1569692 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1569693 (y : real) (z : real) : term243 y z.
Proof. exact (@lem1569692 term237 (term69 y z)). Qed.
Lemma lem1569694 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term244 y z.
Proof. exact (@lem1569693 y z (@lem1569690 x y z h1)). Qed.
Lemma lem1569695 (y : real) (z : real) : (term245 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1569696 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569697 (y : real) (z : real) : (term246 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1569696) (@lem1569695 y z)). Qed.
Lemma lem1569698 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569699 (y : real) (z : real) : (term244 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1569697 y z) (@lem1569698)). Qed.
Lemma lem1569700 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1569699 y z) (@lem1569694 x y z h1)). Qed.
Lemma lem1569701 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term247 y z.
Proof. exact (conj (@lem1569700 x y z h1) (@lem1569679 x y z h1)). Qed.
Lemma lem1569703 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1569704 (y : real) (z : real) : term249 y z.
Proof. exact (@lem1569703 (term69 y z) (term50 y z)). Qed.
Lemma lem1569705 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term250 y z.
Proof. exact (@lem1569704 y z (@lem1569701 x y z h1)). Qed.
Lemma lem1569706 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483480 (term64 y) y z (term64 z)). Qed.
Lemma lem1569707 (y : real) : (term253 y) = (term254 y).
Proof. exact (@lem1483440 term255 y). Qed.
Lemma lem1569709 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569710 : term257 = term46.
Proof. exact (@lem1569709 term211). Qed.
Lemma lem1569711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569712 : term258 = term259.
Proof. exact (MK_COMB (@lem1569711) (@lem1569710)). Qed.
Lemma lem1569713 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1569714 (y : real) : (term254 y) = (term260 y).
Proof. exact (MK_COMB (@lem1569712) (@lem1569713 y)). Qed.
Lemma lem1569715 (y : real) : (term253 y) = (term260 y).
Proof. exact (TRANS (@lem1569707 y) (@lem1569714 y)). Qed.
Lemma lem1569716 (y : real) : (term260 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1569717 (y : real) : (term253 y) = term46.
Proof. exact (TRANS (@lem1569715 y) (@lem1569716 y)). Qed.
Lemma lem1569718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1569719 (y : real) : (term261 y) = term262.
Proof. exact (MK_COMB (@lem1569718) (@lem1569717 y)). Qed.
Lemma lem1569720 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1569722 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569723 : term257 = term46.
Proof. exact (@lem1569722 term211). Qed.
Lemma lem1569724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569725 : term258 = term259.
Proof. exact (MK_COMB (@lem1569724) (@lem1569723)). Qed.
Lemma lem1569726 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1569727 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1569725) (@lem1569726 z)). Qed.
Lemma lem1569728 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1569720 z) (@lem1569727 z)). Qed.
Lemma lem1569729 (z : real) : (term260 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1569730 (z : real) : (term263 z) = term46.
Proof. exact (TRANS (@lem1569728 z) (@lem1569729 z)). Qed.
Lemma lem1569731 (y : real) (z : real) : (term252 y z) = term264.
Proof. exact (MK_COMB (@lem1569719 y) (@lem1569730 z)). Qed.
Lemma lem1569732 (y : real) (z : real) : (term251 y z) = term264.
Proof. exact (TRANS (@lem1569706 y z) (@lem1569731 y z)). Qed.
Lemma lem1569733 : term264 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1569734 (y : real) (z : real) : (term251 y z) = term46.
Proof. exact (TRANS (@lem1569732 y z) (@lem1569733)). Qed.
Lemma lem1569735 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569736 (y : real) (z : real) : (term265 y z) = term266.
Proof. exact (MK_COMB (@lem1569735) (@lem1569734 y z)). Qed.
Lemma lem1569737 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569738 (y : real) (z : real) : (term250 y z) = term267.
Proof. exact (MK_COMB (@lem1569736 y z) (@lem1569737)). Qed.
Lemma lem1569739 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term267.
Proof. exact (EQ_MP (@lem1569738 y z) (@lem1569705 x y z h1)). Qed.
Lemma lem1569741 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569742 : term267 = term268.
Proof. exact (@lem1569741 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1569743 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1569744 : term267 = False.
Proof. exact (TRANS (@lem1569742) (@lem1569743)). Qed.
Lemma lem1569745 (x : real) (y : real) (z : real) (h1 : term180 x y z) : False.
Proof. exact (EQ_MP (@lem1569744) (@lem1569739 x y z h1)). Qed.
Lemma lem1569746 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1569561 x y z h1) (fun h0 : term178 y x z => @lem1569653 y x z h0) (fun h0 : term180 x y z => @lem1569745 x y z h0)). Qed.
Lemma lem1569747 (x : real) (y : real) (z : real) (h1 : term227 x y z) : term227 x y z.
Proof. exact (h1). Qed.
Lemma lem1569748 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term223 x y z.
Proof. exact (h1). Qed.
Lemma lem1569749 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term222 x y z.
Proof. exact (proj2 (@lem1569748 x y z h1)). Qed.
Lemma lem1569751 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1569749 x y z h1)). Qed.
Lemma lem1569752 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term53 y z.
Proof. exact (proj1 (@lem1569749 x y z h1)). Qed.
Lemma lem1569753 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (proj2 (@lem1569751 x y z h1)). Qed.
Lemma lem1569756 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569757 : term231 = term232.
Proof. exact (@lem1569756 (NUMERAL 0) term211). Qed.
Lemma lem1569758 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569759 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569760 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569759 h1) (fun h1 : term232 = True => @lem1569758)). Qed.
Lemma lem1569761 : term232 = True.
Proof. exact (EQ_MP (@lem1569760) (@lem1569758)). Qed.
Lemma lem1569762 : term231 = True.
Proof. exact (TRANS (@lem1569757) (@lem1569761)). Qed.
Lemma lem1569763 : True = term231.
Proof. exact (SYM (@lem1569762)). Qed.
Lemma lem1569764 : term231.
Proof. exact (EQ_MP (@lem1569763) (@lem0)). Qed.
Lemma lem1569765 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term234 y z.
Proof. exact (conj (@lem1569764) (@lem1569752 x y z h1)). Qed.
Lemma lem1569767 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1569768 (y : real) (z : real) : term236 y z.
Proof. exact (@lem1569767 term237 (term50 y z)). Qed.
Lemma lem1569769 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term238 y z.
Proof. exact (@lem1569768 y z (@lem1569765 x y z h1)). Qed.
Lemma lem1569770 (y : real) (z : real) : (term239 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1569771 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569772 (y : real) (z : real) : (term240 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1569771) (@lem1569770 y z)). Qed.
Lemma lem1569773 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569774 (y : real) (z : real) : (term238 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1569772 y z) (@lem1569773)). Qed.
Lemma lem1569775 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1569774 y z) (@lem1569769 x y z h1)). Qed.
Lemma lem1569777 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569778 : term231 = term232.
Proof. exact (@lem1569777 (NUMERAL 0) term211). Qed.
Lemma lem1569779 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569780 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569781 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569780 h1) (fun h1 : term232 = True => @lem1569779)). Qed.
Lemma lem1569782 : term232 = True.
Proof. exact (EQ_MP (@lem1569781) (@lem1569779)). Qed.
Lemma lem1569783 : term231 = True.
Proof. exact (TRANS (@lem1569778) (@lem1569782)). Qed.
Lemma lem1569784 : True = term231.
Proof. exact (SYM (@lem1569783)). Qed.
Lemma lem1569785 : term231.
Proof. exact (EQ_MP (@lem1569784) (@lem0)). Qed.
Lemma lem1569786 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term241 y z.
Proof. exact (conj (@lem1569785) (@lem1569753 x y z h1)). Qed.
Lemma lem1569788 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1569789 (y : real) (z : real) : term243 y z.
Proof. exact (@lem1569788 term237 (term69 y z)). Qed.
Lemma lem1569790 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term244 y z.
Proof. exact (@lem1569789 y z (@lem1569786 x y z h1)). Qed.
Lemma lem1569791 (y : real) (z : real) : (term245 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1569792 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569793 (y : real) (z : real) : (term246 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1569792) (@lem1569791 y z)). Qed.
Lemma lem1569794 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569795 (y : real) (z : real) : (term244 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1569793 y z) (@lem1569794)). Qed.
Lemma lem1569796 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1569795 y z) (@lem1569790 x y z h1)). Qed.
Lemma lem1569797 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term247 y z.
Proof. exact (conj (@lem1569796 x y z h1) (@lem1569775 x y z h1)). Qed.
Lemma lem1569799 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1569800 (y : real) (z : real) : term249 y z.
Proof. exact (@lem1569799 (term69 y z) (term50 y z)). Qed.
Lemma lem1569801 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term250 y z.
Proof. exact (@lem1569800 y z (@lem1569797 x y z h1)). Qed.
Lemma lem1569802 (y : real) (z : real) : (term251 y z) = (term252 y z).
Proof. exact (@lem1483480 (term64 y) y z (term64 z)). Qed.
Lemma lem1569803 (y : real) : (term253 y) = (term254 y).
Proof. exact (@lem1483440 term255 y). Qed.
Lemma lem1569805 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569806 : term257 = term46.
Proof. exact (@lem1569805 term211). Qed.
Lemma lem1569807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569808 : term258 = term259.
Proof. exact (MK_COMB (@lem1569807) (@lem1569806)). Qed.
Lemma lem1569809 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1569810 (y : real) : (term254 y) = (term260 y).
Proof. exact (MK_COMB (@lem1569808) (@lem1569809 y)). Qed.
Lemma lem1569811 (y : real) : (term253 y) = (term260 y).
Proof. exact (TRANS (@lem1569803 y) (@lem1569810 y)). Qed.
Lemma lem1569812 (y : real) : (term260 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1569813 (y : real) : (term253 y) = term46.
Proof. exact (TRANS (@lem1569811 y) (@lem1569812 y)). Qed.
Lemma lem1569814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1569815 (y : real) : (term261 y) = term262.
Proof. exact (MK_COMB (@lem1569814) (@lem1569813 y)). Qed.
Lemma lem1569816 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1569818 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569819 : term257 = term46.
Proof. exact (@lem1569818 term211). Qed.
Lemma lem1569820 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569821 : term258 = term259.
Proof. exact (MK_COMB (@lem1569820) (@lem1569819)). Qed.
Lemma lem1569822 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1569823 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1569821) (@lem1569822 z)). Qed.
Lemma lem1569824 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1569816 z) (@lem1569823 z)). Qed.
Lemma lem1569825 (z : real) : (term260 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1569826 (z : real) : (term263 z) = term46.
Proof. exact (TRANS (@lem1569824 z) (@lem1569825 z)). Qed.
Lemma lem1569827 (y : real) (z : real) : (term252 y z) = term264.
Proof. exact (MK_COMB (@lem1569815 y) (@lem1569826 z)). Qed.
Lemma lem1569828 (y : real) (z : real) : (term251 y z) = term264.
Proof. exact (TRANS (@lem1569802 y z) (@lem1569827 y z)). Qed.
Lemma lem1569829 : term264 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1569830 (y : real) (z : real) : (term251 y z) = term46.
Proof. exact (TRANS (@lem1569828 y z) (@lem1569829)). Qed.
Lemma lem1569831 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569832 (y : real) (z : real) : (term265 y z) = term266.
Proof. exact (MK_COMB (@lem1569831) (@lem1569830 y z)). Qed.
Lemma lem1569833 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569834 (y : real) (z : real) : (term250 y z) = term267.
Proof. exact (MK_COMB (@lem1569832 y z) (@lem1569833)). Qed.
Lemma lem1569835 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term267.
Proof. exact (EQ_MP (@lem1569834 y z) (@lem1569801 x y z h1)). Qed.
Lemma lem1569837 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569838 : term267 = term268.
Proof. exact (@lem1569837 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1569839 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1569840 : term267 = False.
Proof. exact (TRANS (@lem1569838) (@lem1569839)). Qed.
Lemma lem1569841 (x : real) (y : real) (z : real) (h1 : term223 x y z) : False.
Proof. exact (EQ_MP (@lem1569840) (@lem1569835 x y z h1)). Qed.
Lemma lem1569842 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term225 x y z.
Proof. exact (h1). Qed.
Lemma lem1569843 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term224 x y z.
Proof. exact (proj2 (@lem1569842 x y z h1)). Qed.
Lemma lem1569845 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1569843 x y z h1)). Qed.
Lemma lem1569846 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term53 x z.
Proof. exact (proj1 (@lem1569843 x y z h1)). Qed.
Lemma lem1569848 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term72 x z.
Proof. exact (proj1 (@lem1569845 x y z h1)). Qed.
Lemma lem1569850 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569851 : term231 = term232.
Proof. exact (@lem1569850 (NUMERAL 0) term211). Qed.
Lemma lem1569852 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569853 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569854 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569853 h1) (fun h1 : term232 = True => @lem1569852)). Qed.
Lemma lem1569855 : term232 = True.
Proof. exact (EQ_MP (@lem1569854) (@lem1569852)). Qed.
Lemma lem1569856 : term231 = True.
Proof. exact (TRANS (@lem1569851) (@lem1569855)). Qed.
Lemma lem1569857 : True = term231.
Proof. exact (SYM (@lem1569856)). Qed.
Lemma lem1569858 : term231.
Proof. exact (EQ_MP (@lem1569857) (@lem0)). Qed.
Lemma lem1569859 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term234 x z.
Proof. exact (conj (@lem1569858) (@lem1569846 x y z h1)). Qed.
Lemma lem1569861 (x : real) (y : real) : term235 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1569862 (x : real) (z : real) : term236 x z.
Proof. exact (@lem1569861 term237 (term50 x z)). Qed.
Lemma lem1569863 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term238 x z.
Proof. exact (@lem1569862 x z (@lem1569859 x y z h1)). Qed.
Lemma lem1569864 (x : real) (z : real) : (term239 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1569865 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1569866 (x : real) (z : real) : (term240 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1569865) (@lem1569864 x z)). Qed.
Lemma lem1569867 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569868 (x : real) (z : real) : (term238 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1569866 x z) (@lem1569867)). Qed.
Lemma lem1569869 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term53 x z.
Proof. exact (EQ_MP (@lem1569868 x z) (@lem1569863 x y z h1)). Qed.
Lemma lem1569871 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569872 : term231 = term232.
Proof. exact (@lem1569871 (NUMERAL 0) term211). Qed.
Lemma lem1569873 : term233 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1569874 (h1 : term233 = (BIT1 0)) : term232 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1569875 : (term233 = (BIT1 0)) = (term232 = True).
Proof. exact (prop_ext (fun h1 : term233 = (BIT1 0) => @lem1569874 h1) (fun h1 : term232 = True => @lem1569873)). Qed.
Lemma lem1569876 : term232 = True.
Proof. exact (EQ_MP (@lem1569875) (@lem1569873)). Qed.
Lemma lem1569877 : term231 = True.
Proof. exact (TRANS (@lem1569872) (@lem1569876)). Qed.
Lemma lem1569878 : True = term231.
Proof. exact (SYM (@lem1569877)). Qed.
Lemma lem1569879 : term231.
Proof. exact (EQ_MP (@lem1569878) (@lem0)). Qed.
Lemma lem1569880 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term241 x z.
Proof. exact (conj (@lem1569879) (@lem1569848 x y z h1)). Qed.
Lemma lem1569882 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1569883 (x : real) (z : real) : term243 x z.
Proof. exact (@lem1569882 term237 (term69 x z)). Qed.
Lemma lem1569884 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term244 x z.
Proof. exact (@lem1569883 x z (@lem1569880 x y z h1)). Qed.
Lemma lem1569885 (x : real) (z : real) : (term245 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1569886 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569887 (x : real) (z : real) : (term246 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1569886) (@lem1569885 x z)). Qed.
Lemma lem1569888 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569889 (x : real) (z : real) : (term244 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1569887 x z) (@lem1569888)). Qed.
Lemma lem1569890 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1569889 x z) (@lem1569884 x y z h1)). Qed.
Lemma lem1569891 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term247 x z.
Proof. exact (conj (@lem1569890 x y z h1) (@lem1569869 x y z h1)). Qed.
Lemma lem1569893 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1569894 (x : real) (z : real) : term249 x z.
Proof. exact (@lem1569893 (term69 x z) (term50 x z)). Qed.
Lemma lem1569895 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term250 x z.
Proof. exact (@lem1569894 x z (@lem1569891 x y z h1)). Qed.
Lemma lem1569896 (x : real) (z : real) : (term251 x z) = (term252 x z).
Proof. exact (@lem1483480 (term64 x) x z (term64 z)). Qed.
Lemma lem1569897 (x : real) : (term253 x) = (term254 x).
Proof. exact (@lem1483440 term255 x). Qed.
Lemma lem1569899 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569900 : term257 = term46.
Proof. exact (@lem1569899 term211). Qed.
Lemma lem1569901 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569902 : term258 = term259.
Proof. exact (MK_COMB (@lem1569901) (@lem1569900)). Qed.
Lemma lem1569903 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1569904 (x : real) : (term254 x) = (term260 x).
Proof. exact (MK_COMB (@lem1569902) (@lem1569903 x)). Qed.
Lemma lem1569905 (x : real) : (term253 x) = (term260 x).
Proof. exact (TRANS (@lem1569897 x) (@lem1569904 x)). Qed.
Lemma lem1569906 (x : real) : (term260 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1569907 (x : real) : (term253 x) = term46.
Proof. exact (TRANS (@lem1569905 x) (@lem1569906 x)). Qed.
Lemma lem1569908 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1569909 (x : real) : (term261 x) = term262.
Proof. exact (MK_COMB (@lem1569908) (@lem1569907 x)). Qed.
Lemma lem1569910 (z : real) : (term263 z) = (term254 z).
Proof. exact (@lem1483442 term255 z). Qed.
Lemma lem1569912 (m : nat) : (term256 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1569913 : term257 = term46.
Proof. exact (@lem1569912 term211). Qed.
Lemma lem1569914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1569915 : term258 = term259.
Proof. exact (MK_COMB (@lem1569914) (@lem1569913)). Qed.
Lemma lem1569916 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1569917 (z : real) : (term254 z) = (term260 z).
Proof. exact (MK_COMB (@lem1569915) (@lem1569916 z)). Qed.
Lemma lem1569918 (z : real) : (term263 z) = (term260 z).
Proof. exact (TRANS (@lem1569910 z) (@lem1569917 z)). Qed.
Lemma lem1569919 (z : real) : (term260 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1569920 (z : real) : (term263 z) = term46.
Proof. exact (TRANS (@lem1569918 z) (@lem1569919 z)). Qed.
Lemma lem1569921 (x : real) (z : real) : (term252 x z) = term264.
Proof. exact (MK_COMB (@lem1569909 x) (@lem1569920 z)). Qed.
Lemma lem1569922 (x : real) (z : real) : (term251 x z) = term264.
Proof. exact (TRANS (@lem1569896 x z) (@lem1569921 x z)). Qed.
Lemma lem1569923 : term264 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1569924 (x : real) (z : real) : (term251 x z) = term46.
Proof. exact (TRANS (@lem1569922 x z) (@lem1569923)). Qed.
Lemma lem1569925 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1569926 (x : real) (z : real) : (term265 x z) = term266.
Proof. exact (MK_COMB (@lem1569925) (@lem1569924 x z)). Qed.
Lemma lem1569927 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1569928 (x : real) (z : real) : (term250 x z) = term267.
Proof. exact (MK_COMB (@lem1569926 x z) (@lem1569927)). Qed.
Lemma lem1569929 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term267.
Proof. exact (EQ_MP (@lem1569928 x z) (@lem1569895 x y z h1)). Qed.
Lemma lem1569931 (n : nat) (m : nat) : (term230 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1569932 : term267 = term268.
Proof. exact (@lem1569931 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1569933 : term268 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1569934 : term267 = False.
Proof. exact (TRANS (@lem1569932) (@lem1569933)). Qed.
Lemma lem1569935 (x : real) (y : real) (z : real) (h1 : term225 x y z) : False.
Proof. exact (EQ_MP (@lem1569934) (@lem1569929 x y z h1)). Qed.
Lemma lem1569936 (x : real) (y : real) (z : real) (h1 : term227 x y z) : False.
Proof. exact (or_elim (@lem1569747 x y z h1) (fun h0 : term223 x y z => @lem1569841 x y z h0) (fun h0 : term225 x y z => @lem1569935 x y z h0)). Qed.
Lemma lem1569937 (x : real) (y : real) (z : real) (h1 : term229 x y z) : False.
Proof. exact (or_elim (@lem1569560 x y z h1) (fun h0 : term183 x y z => @lem1569746 x y z h0) (fun h0 : term227 x y z => @lem1569936 x y z h0)). Qed.
Lemma lem1569938 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term163 x y z.
Proof. exact (h1). Qed.
Lemma lem1569939 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term229 x y z.
Proof. exact (EQ_MP (@lem1569559 x y z) (@lem1569938 x y z h1)). Qed.
Lemma lem1569940 (x : real) (y : real) (z : real) (h1 : term163 x y z) : (term229 x y z) = False.
Proof. exact (prop_ext (fun h2 : term229 x y z => @lem1569937 x y z h2) (fun h2 : False => @lem1569939 x y z h1)). Qed.
Lemma lem1569941 (x : real) (y : real) (z : real) (h1 : term163 x y z) : False.
Proof. exact (EQ_MP (@lem1569940 x y z h1) (@lem1569939 x y z h1)). Qed.
Lemma lem1569942 (x : real) (y : real) (h1 : term165 x y) : term165 x y.
Proof. exact (h1). Qed.
Lemma lem1569943 (x : real) (y : real) (h1 : term165 x y) : False.
Proof. exact (ex_elim (@lem1569942 x y h1) (fun z : real => fun h0 : term164 x y z => @lem1569941 x y z h0)). Qed.
Lemma lem1569944 (x : real) (h1 : term167 x) : term167 x.
Proof. exact (h1). Qed.
Lemma lem1569945 (x : real) (h1 : term167 x) : False.
Proof. exact (ex_elim (@lem1569944 x h1) (fun y : real => fun h0 : term166 x y => @lem1569943 x y h0)). Qed.
Lemma lem1569946 (h1 : term169) : term169.
Proof. exact (h1). Qed.
Lemma lem1569947 (h1 : term169) : False.
Proof. exact (ex_elim (@lem1569946 h1) (fun x : real => fun h0 : term168 x => @lem1569945 x h0)). Qed.
Lemma lem1569948 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1569949 (h1 : term32) : term169.
Proof. exact (EQ_MP (@lem1569239) (@lem1569948 h1)). Qed.
Lemma lem1569950 (h1 : term32) : term169 = False.
Proof. exact (prop_ext (fun h2 : term169 => @lem1569947 h2) (fun h2 : False => @lem1569949 h1)). Qed.
Lemma lem1569951 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1569950 h1) (@lem1569949 h1)). Qed.
Lemma lem1569952 : term269.
Proof. exact (fun h0 : term32 => @lem1569951 h0). Qed.
Lemma lem1569953 : term270.
Proof. exact (@lem1386578 term271). Qed.
Lemma lem1569954 : term271.
Proof. exact (@lem1569953 (@lem1569952)). Qed.

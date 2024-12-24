Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
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
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1565455 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17045 (real_le x z) (real_le y z)). Qed.
Lemma lem1565461 (x : real) (y : real) (z : real) : (term2 x y z) = (term2 x y z).
Proof. exact (eq_refl (term2 x y z)). Qed.
Lemma lem1565463 (x : real) (y : real) (z : real) : (term3 x y z) = (term3 x y z).
Proof. exact (eq_refl (term3 x y z)). Qed.
Lemma lem1565464 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (MK_COMB (@lem1565463 x y z) (@lem1565455 x y z)). Qed.
Lemma lem1565465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565466 (x : real) (y : real) (z : real) : (term6 x y z) = (term7 x y z).
Proof. exact (MK_COMB (@lem1565465) (@lem1565464 x y z)). Qed.
Lemma lem1565467 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1565466 x y z) (@lem1565461 x y z)). Qed.
Lemma lem1565468 (x : real) (y : real) (z : real) : (term10 x y z) = (term8 x y z).
Proof. exact (@lem17646 (term11 x y z) (term12 x y z)). Qed.
Lemma lem1565469 (x : real) (y : real) (z : real) : (term10 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1565468 x y z) (@lem1565467 x y z)). Qed.
Lemma lem1565470 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1565471 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1565470 (term17 x y)). Qed.
Lemma lem1565472 (x : real) (y : real) (z : real) : (term18 x y z) = ((term11 x y z) = (term12 x y z)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1565473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1565474 (x : real) (y : real) (z : real) : (term19 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1565473) (@lem1565472 x y z)). Qed.
Lemma lem1565475 (x : real) (y : real) (z : real) : (term19 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1565474 x y z) (@lem1565469 x y z)). Qed.
Lemma lem1565476 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1565475 x y z)). Qed.
Lemma lem1565477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565478 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1565477) (@lem1565476 x y)). Qed.
Lemma lem1565479 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1565471 x y) (@lem1565478 x y)). Qed.
Lemma lem1565480 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1565481 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1565480 (term25 x)). Qed.
Lemma lem1565482 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1565483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1565484 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1565483) (@lem1565482 x y)). Qed.
Lemma lem1565485 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1565484 x y) (@lem1565479 x y)). Qed.
Lemma lem1565486 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1565485 x y)). Qed.
Lemma lem1565487 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565488 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1565487) (@lem1565486 x)). Qed.
Lemma lem1565489 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1565481 x) (@lem1565488 x)). Qed.
Lemma lem1565490 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1565491 : term32 = term33.
Proof. exact (@lem1565490 term34). Qed.
Lemma lem1565492 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1565493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1565494 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1565493) (@lem1565492 x)). Qed.
Lemma lem1565495 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1565494 x) (@lem1565489 x)). Qed.
Lemma lem1565496 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1565495 x)). Qed.
Lemma lem1565497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565498 : term33 = term40.
Proof. exact (MK_COMB (@lem1565497) (@lem1565496)). Qed.
Lemma lem1565500 : term32 = term40.
Proof. exact (TRANS (@lem1565491) (@lem1565498)). Qed.
Lemma lem1565527 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1565528 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1565527 x y z)). Qed.
Lemma lem1565529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565530 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1565529) (@lem1565528 x y)). Qed.
Lemma lem1565531 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1565530 x y)). Qed.
Lemma lem1565532 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565533 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1565532) (@lem1565531 x)). Qed.
Lemma lem1565534 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1565533 x)). Qed.
Lemma lem1565535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565536 : term40 = term40.
Proof. exact (MK_COMB (@lem1565535) (@lem1565534)). Qed.
Lemma lem1565537 : term32 = term40.
Proof. exact (TRANS (@lem1565500) (@lem1565536)). Qed.
Lemma lem1565538 (z : real) (x : real) (y : real) : (term11 x y z) = (term41 z x y).
Proof. exact (@lem1483523 z (real_max x y)). Qed.
Lemma lem1565551 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1565552 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565553 (z : real) (x : real) (y : real) : (term44 z x y) = (term45 z x y).
Proof. exact (MK_COMB (@lem1565552) (@lem1565551 z x y)). Qed.
Lemma lem1565554 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565555 (z : real) (x : real) (y : real) : (term41 z x y) = (term47 z x y).
Proof. exact (MK_COMB (@lem1565553 z x y) (@lem1565554)). Qed.
Lemma lem1565556 (z : real) (x : real) (y : real) : (term11 x y z) = (term47 z x y).
Proof. exact (TRANS (@lem1565538 z x y) (@lem1565555 z x y)). Qed.
Lemma lem1565557 (x : real) (z : real) : (term48 x z) = (term49 x z).
Proof. exact (@lem1483533 x z). Qed.
Lemma lem1565570 (x : real) (z : real) : (real_sub x z) = (term50 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1565571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565572 (x : real) (z : real) : (term51 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1565571) (@lem1565570 x z)). Qed.
Lemma lem1565573 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565574 (x : real) (z : real) : (term49 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1565572 x z) (@lem1565573)). Qed.
Lemma lem1565575 (x : real) (z : real) : (term48 x z) = (term53 x z).
Proof. exact (TRANS (@lem1565557 x z) (@lem1565574 x z)). Qed.
Lemma lem1565576 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483533 y z). Qed.
Lemma lem1565589 (y : real) (z : real) : (real_sub y z) = (term50 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1565590 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565591 (y : real) (z : real) : (term51 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1565590) (@lem1565589 y z)). Qed.
Lemma lem1565592 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565593 (y : real) (z : real) : (term49 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1565591 y z) (@lem1565592)). Qed.
Lemma lem1565594 (y : real) (z : real) : (term48 y z) = (term53 y z).
Proof. exact (TRANS (@lem1565576 y z) (@lem1565593 y z)). Qed.
Lemma lem1565595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565596 (x : real) (z : real) : (term54 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1565595) (@lem1565575 x z)). Qed.
Lemma lem1565597 (x : real) (y : real) (z : real) : (term1 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1565596 x z) (@lem1565594 y z)). Qed.
Lemma lem1565598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565599 (z : real) (x : real) (y : real) : (term3 x y z) = (term57 z x y).
Proof. exact (MK_COMB (@lem1565598) (@lem1565556 z x y)). Qed.
Lemma lem1565600 (x : real) (y : real) (z : real) : (term5 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem1565599 z x y) (@lem1565597 x y z)). Qed.
Lemma lem1565601 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483533 (real_max x y) z). Qed.
Lemma lem1565607 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1565612 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (@lem1483488 (term64 z) (real_max x y)). Qed.
Lemma lem1565614 (z : real) (x : real) (y : real) : (term61 x y z) = (term63 z x y).
Proof. exact (TRANS (@lem1565607 x y z) (@lem1565612 z x y)). Qed.
Lemma lem1565615 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1565616 (z : real) (x : real) (y : real) : (term65 x y z) = (term66 z x y).
Proof. exact (MK_COMB (@lem1565615) (@lem1565614 z x y)). Qed.
Lemma lem1565617 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565618 (z : real) (x : real) (y : real) : (term60 x y z) = (term67 z x y).
Proof. exact (MK_COMB (@lem1565616 z x y) (@lem1565617)). Qed.
Lemma lem1565619 (z : real) (x : real) (y : real) : (term59 x y z) = (term67 z x y).
Proof. exact (TRANS (@lem1565601 x y z) (@lem1565618 z x y)). Qed.
Lemma lem1565620 (z : real) (x : real) : (real_le x z) = (term68 z x).
Proof. exact (@lem1483523 z x). Qed.
Lemma lem1565626 (z : real) (x : real) : (real_sub z x) = (term50 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1565631 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1565633 (x : real) (z : real) : (real_sub z x) = (term69 x z).
Proof. exact (TRANS (@lem1565626 z x) (@lem1565631 x z)). Qed.
Lemma lem1565634 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565635 (x : real) (z : real) : (term70 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1565634) (@lem1565633 x z)). Qed.
Lemma lem1565636 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565637 (x : real) (z : real) : (term68 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1565635 x z) (@lem1565636)). Qed.
Lemma lem1565638 (x : real) (z : real) : (real_le x z) = (term72 x z).
Proof. exact (TRANS (@lem1565620 z x) (@lem1565637 x z)). Qed.
Lemma lem1565639 (z : real) (y : real) : (real_le y z) = (term68 z y).
Proof. exact (@lem1483523 z y). Qed.
Lemma lem1565645 (z : real) (y : real) : (real_sub z y) = (term50 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1565650 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1565652 (y : real) (z : real) : (real_sub z y) = (term69 y z).
Proof. exact (TRANS (@lem1565645 z y) (@lem1565650 y z)). Qed.
Lemma lem1565653 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1565654 (y : real) (z : real) : (term70 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1565653) (@lem1565652 y z)). Qed.
Lemma lem1565655 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1565656 (y : real) (z : real) : (term68 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1565654 y z) (@lem1565655)). Qed.
Lemma lem1565657 (y : real) (z : real) : (real_le y z) = (term72 y z).
Proof. exact (TRANS (@lem1565639 z y) (@lem1565656 y z)). Qed.
Lemma lem1565658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565659 (x : real) (z : real) : (term73 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1565658) (@lem1565638 x z)). Qed.
Lemma lem1565660 (x : real) (y : real) (z : real) : (term12 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1565659 x z) (@lem1565657 y z)). Qed.
Lemma lem1565661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1565662 (z : real) (x : real) (y : real) : (term76 x y z) = (term77 z x y).
Proof. exact (MK_COMB (@lem1565661) (@lem1565619 z x y)). Qed.
Lemma lem1565663 (x : real) (y : real) (z : real) : (term2 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1565662 z x y) (@lem1565660 x y z)). Qed.
Lemma lem1565664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565665 (x : real) (y : real) (z : real) : (term7 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1565664) (@lem1565600 x y z)). Qed.
Lemma lem1565666 (x : real) (y : real) (z : real) : (term9 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1565665 x y z) (@lem1565663 x y z)). Qed.
Lemma lem1565667 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1565666 x y z)). Qed.
Lemma lem1565668 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565669 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1565668) (@lem1565667 x y)). Qed.
Lemma lem1565670 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1565669 x y)). Qed.
Lemma lem1565671 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565672 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1565671) (@lem1565670 x)). Qed.
Lemma lem1565673 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1565672 x)). Qed.
Lemma lem1565674 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565675 : term40 = term86.
Proof. exact (MK_COMB (@lem1565674) (@lem1565673)). Qed.
Lemma lem1565676 : term32 = term86.
Proof. exact (TRANS (@lem1565537) (@lem1565675)). Qed.
Lemma lem1565686 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1565687 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1565686 real P Q). Qed.
Lemma lem1565688 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1565687 (term93 x y) (term94 x y)). Qed.
Lemma lem1565689 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1565690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565691 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1565690) (@lem1565689 x y z)). Qed.
Lemma lem1565692 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1565693 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1565691 x y z) (@lem1565692 x y z)). Qed.
Lemma lem1565694 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1565693 x y z)). Qed.
Lemma lem1565695 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565696 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1565695) (@lem1565694 x y)). Qed.
Lemma lem1565697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1565698 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1565697) (@lem1565696 x y)). Qed.
Lemma lem1565699 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1565700 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1565699 x y z)). Qed.
Lemma lem1565701 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565702 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1565701) (@lem1565700 x y)). Qed.
Lemma lem1565703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565704 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1565703) (@lem1565702 x y)). Qed.
Lemma lem1565705 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1565706 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1565705 x y z)). Qed.
Lemma lem1565707 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565708 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1565707) (@lem1565706 x y)). Qed.
Lemma lem1565709 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1565704 x y) (@lem1565708 x y)). Qed.
Lemma lem1565710 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1565698 x y) (@lem1565709 x y)). Qed.
Lemma lem1565711 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1565710 x y) (@lem1565688 x y)). Qed.
Lemma lem1565808 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1565711 x y)). Qed.
Lemma lem1565809 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565810 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1565809) (@lem1565808 x)). Qed.
Lemma lem1565812 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1565813 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1565812 real P Q). Qed.
Lemma lem1565814 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1565813 (term115 x) (term116 x)). Qed.
Lemma lem1565815 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1565816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565817 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1565816) (@lem1565815 x y)). Qed.
Lemma lem1565818 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1565819 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1565817 x y) (@lem1565818 x y)). Qed.
Lemma lem1565820 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1565819 x y)). Qed.
Lemma lem1565821 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565822 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1565821) (@lem1565820 x)). Qed.
Lemma lem1565823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1565824 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1565823) (@lem1565822 x)). Qed.
Lemma lem1565825 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1565826 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1565825 x y)). Qed.
Lemma lem1565827 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565828 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1565827) (@lem1565826 x)). Qed.
Lemma lem1565829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565830 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1565829) (@lem1565828 x)). Qed.
Lemma lem1565831 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1565832 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1565831 x y)). Qed.
Lemma lem1565833 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565834 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1565833) (@lem1565832 x)). Qed.
Lemma lem1565835 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1565830 x) (@lem1565834 x)). Qed.
Lemma lem1565836 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1565824 x) (@lem1565835 x)). Qed.
Lemma lem1565837 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1565836 x) (@lem1565814 x)). Qed.
Lemma lem1565942 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1565810 x) (@lem1565837 x)). Qed.
Lemma lem1565943 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1565942 x)). Qed.
Lemma lem1565944 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565945 : term86 = term134.
Proof. exact (MK_COMB (@lem1565944) (@lem1565943)). Qed.
Lemma lem1565947 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1565948 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1565947 real P Q). Qed.
Lemma lem1565949 : term135 = term136.
Proof. exact (@lem1565948 term137 term138). Qed.
Lemma lem1565950 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1565951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565952 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1565951) (@lem1565950 x)). Qed.
Lemma lem1565953 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1565954 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1565952 x) (@lem1565953 x)). Qed.
Lemma lem1565955 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1565954 x)). Qed.
Lemma lem1565956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565957 : term135 = term134.
Proof. exact (MK_COMB (@lem1565956) (@lem1565955)). Qed.
Lemma lem1565958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1565959 : term144 = term145.
Proof. exact (MK_COMB (@lem1565958) (@lem1565957)). Qed.
Lemma lem1565960 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1565961 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1565960 x)). Qed.
Lemma lem1565962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565963 : term147 = term148.
Proof. exact (MK_COMB (@lem1565962) (@lem1565961)). Qed.
Lemma lem1565964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1565965 : term149 = term150.
Proof. exact (MK_COMB (@lem1565964) (@lem1565963)). Qed.
Lemma lem1565966 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1565967 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1565966 x)). Qed.
Lemma lem1565968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1565969 : term152 = term153.
Proof. exact (MK_COMB (@lem1565968) (@lem1565967)). Qed.
Lemma lem1565970 : term136 = term154.
Proof. exact (MK_COMB (@lem1565965) (@lem1565969)). Qed.
Lemma lem1565971 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1565959) (@lem1565970)). Qed.
Lemma lem1565972 : term134 = term154.
Proof. exact (EQ_MP (@lem1565971) (@lem1565949)). Qed.
Lemma lem1566085 : term86 = term154.
Proof. exact (TRANS (@lem1565945) (@lem1565972)). Qed.
Lemma lem1566087 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1566088 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1566087 real P Q). Qed.
Lemma lem1566089 : term136 = term135.
Proof. exact (@lem1566088 term137 term138). Qed.
Lemma lem1566090 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1566091 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1566090 x)). Qed.
Lemma lem1566092 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566093 : term147 = term148.
Proof. exact (MK_COMB (@lem1566092) (@lem1566091)). Qed.
Lemma lem1566094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566095 : term149 = term150.
Proof. exact (MK_COMB (@lem1566094) (@lem1566093)). Qed.
Lemma lem1566096 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1566097 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1566096 x)). Qed.
Lemma lem1566098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566099 : term152 = term153.
Proof. exact (MK_COMB (@lem1566098) (@lem1566097)). Qed.
Lemma lem1566100 : term136 = term154.
Proof. exact (MK_COMB (@lem1566095) (@lem1566099)). Qed.
Lemma lem1566101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1566102 : term155 = term156.
Proof. exact (MK_COMB (@lem1566101) (@lem1566100)). Qed.
Lemma lem1566103 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1566104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566105 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1566104) (@lem1566103 x)). Qed.
Lemma lem1566106 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1566107 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1566105 x) (@lem1566106 x)). Qed.
Lemma lem1566108 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1566107 x)). Qed.
Lemma lem1566109 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566110 : term135 = term134.
Proof. exact (MK_COMB (@lem1566109) (@lem1566108)). Qed.
Lemma lem1566111 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1566102) (@lem1566110)). Qed.
Lemma lem1566112 : term154 = term134.
Proof. exact (EQ_MP (@lem1566111) (@lem1566089)). Qed.
Lemma lem1566114 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1566115 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1566114 real P Q). Qed.
Lemma lem1566116 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1566115 (term115 x) (term116 x)). Qed.
Lemma lem1566117 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1566118 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1566117 x y)). Qed.
Lemma lem1566119 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566120 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1566119) (@lem1566118 x)). Qed.
Lemma lem1566121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566122 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1566121) (@lem1566120 x)). Qed.
Lemma lem1566123 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1566124 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1566123 x y)). Qed.
Lemma lem1566125 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566126 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1566125) (@lem1566124 x)). Qed.
Lemma lem1566127 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1566122 x) (@lem1566126 x)). Qed.
Lemma lem1566128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1566129 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1566128) (@lem1566127 x)). Qed.
Lemma lem1566130 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1566131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566132 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1566131) (@lem1566130 x y)). Qed.
Lemma lem1566133 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1566134 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1566132 x y) (@lem1566133 x y)). Qed.
Lemma lem1566135 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1566134 x y)). Qed.
Lemma lem1566136 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566137 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1566136) (@lem1566135 x)). Qed.
Lemma lem1566138 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1566129 x) (@lem1566137 x)). Qed.
Lemma lem1566139 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1566138 x) (@lem1566116 x)). Qed.
Lemma lem1566141 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1566142 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1566141 real P Q). Qed.
Lemma lem1566143 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1566142 (term93 x y) (term94 x y)). Qed.
Lemma lem1566144 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1566145 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1566144 x y z)). Qed.
Lemma lem1566146 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566147 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1566146) (@lem1566145 x y)). Qed.
Lemma lem1566148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566149 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1566148) (@lem1566147 x y)). Qed.
Lemma lem1566150 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1566151 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1566150 x y z)). Qed.
Lemma lem1566152 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566153 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1566152) (@lem1566151 x y)). Qed.
Lemma lem1566154 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1566149 x y) (@lem1566153 x y)). Qed.
Lemma lem1566155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1566156 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1566155) (@lem1566154 x y)). Qed.
Lemma lem1566157 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1566158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566159 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1566158) (@lem1566157 x y z)). Qed.
Lemma lem1566160 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1566161 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1566159 x y z) (@lem1566160 x y z)). Qed.
Lemma lem1566162 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1566161 x y z)). Qed.
Lemma lem1566163 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566164 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1566163) (@lem1566162 x y)). Qed.
Lemma lem1566165 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1566156 x y) (@lem1566164 x y)). Qed.
Lemma lem1566166 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1566165 x y) (@lem1566143 x y)). Qed.
Lemma lem1566167 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1566166 x y)). Qed.
Lemma lem1566168 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566169 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1566168) (@lem1566167 x)). Qed.
Lemma lem1566170 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1566139 x) (@lem1566169 x)). Qed.
Lemma lem1566171 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1566170 x)). Qed.
Lemma lem1566172 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566173 : term134 = term86.
Proof. exact (MK_COMB (@lem1566172) (@lem1566171)). Qed.
Lemma lem1566174 : term154 = term86.
Proof. exact (TRANS (@lem1566112) (@lem1566173)). Qed.
Lemma lem1566175 : term86 = term86.
Proof. exact (TRANS (@lem1566085) (@lem1566174)). Qed.
Lemma lem1566178 : term32 = term86.
Proof. exact (TRANS (@lem1565676) (@lem1566175)). Qed.
Lemma lem1566191 (x : real) (y : real) (z : real) : (term78 x y z) = (term78 x y z).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1566208 (x : real) (y : real) (z : real) : (term58 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term53 x z) (term47 z x y) (term53 y z)). Qed.
Lemma lem1566209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566210 (x : real) (y : real) (z : real) : (term79 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1566209) (@lem1566208 x y z)). Qed.
Lemma lem1566211 (x : real) (y : real) (z : real) : (term80 x y z) = (term163 x y z).
Proof. exact (MK_COMB (@lem1566210 x y z) (@lem1566191 x y z)). Qed.
Lemma lem1566212 (x : real) (y : real) : (term81 x y) = (term164 x y).
Proof. exact (fun_ext (fun z : real => @lem1566211 x y z)). Qed.
Lemma lem1566213 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566214 (x : real) (y : real) : (term82 x y) = (term165 x y).
Proof. exact (MK_COMB (@lem1566213) (@lem1566212 x y)). Qed.
Lemma lem1566215 (x : real) : (term83 x) = (term166 x).
Proof. exact (fun_ext (fun y : real => @lem1566214 x y)). Qed.
Lemma lem1566216 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566217 (x : real) : (term84 x) = (term167 x).
Proof. exact (MK_COMB (@lem1566216) (@lem1566215 x)). Qed.
Lemma lem1566218 : term85 = term168.
Proof. exact (fun_ext (fun x : real => @lem1566217 x)). Qed.
Lemma lem1566219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566220 : term86 = term169.
Proof. exact (MK_COMB (@lem1566219) (@lem1566218)). Qed.
Lemma lem1566221 : term32 = term169.
Proof. exact (TRANS (@lem1566178) (@lem1566220)). Qed.
Lemma lem1566223 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1566224 (x : real) (z : real) (y : real) : (term47 z x y) = (term172 x z y).
Proof. exact (@lem1566223 x z y term46). Qed.
Lemma lem1566237 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1566238 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566239 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1566238) (@lem1566237 y z)). Qed.
Lemma lem1566240 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566241 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1566239 y z) (@lem1566240)). Qed.
Lemma lem1566254 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1566255 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566256 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1566255) (@lem1566254 x z)). Qed.
Lemma lem1566257 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566258 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1566256 x z) (@lem1566257)). Qed.
Lemma lem1566259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566260 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1566259) (@lem1566258 x z)). Qed.
Lemma lem1566261 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1566260 x z) (@lem1566241 y z)). Qed.
Lemma lem1566262 (x : real) (y : real) (z : real) : (term47 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1566224 x z y) (@lem1566261 x y z)). Qed.
Lemma lem1566263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566264 (x : real) (y : real) (z : real) : (term57 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1566263) (@lem1566262 x y z)). Qed.
Lemma lem1566265 (x : real) (z : real) : (term53 x z) = (term53 x z).
Proof. exact (eq_refl (term53 x z)). Qed.
Lemma lem1566268 (y : real) (x : real) (z : real) : (term177 y x z) = (term178 y x z).
Proof. exact (MK_COMB (@lem1566264 x y z) (@lem1566265 x z)). Qed.
Lemma lem1566270 (x : real) (a : real) (y : real) (r : real) : (term170 a x y r) = (term171 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1566271 (x : real) (z : real) (y : real) : (term47 z x y) = (term172 x z y).
Proof. exact (@lem1566270 x z y term46). Qed.
Lemma lem1566284 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1566285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566286 (y : real) (z : real) : (term173 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1566285) (@lem1566284 y z)). Qed.
Lemma lem1566287 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566288 (y : real) (z : real) : (term174 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1566286 y z) (@lem1566287)). Qed.
Lemma lem1566301 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1566302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566303 (x : real) (z : real) : (term173 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1566302) (@lem1566301 x z)). Qed.
Lemma lem1566304 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566305 (x : real) (z : real) : (term174 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1566303 x z) (@lem1566304)). Qed.
Lemma lem1566306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566307 (x : real) (z : real) : (term175 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1566306) (@lem1566305 x z)). Qed.
Lemma lem1566308 (x : real) (y : real) (z : real) : (term172 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1566307 x z) (@lem1566288 y z)). Qed.
Lemma lem1566309 (x : real) (y : real) (z : real) : (term47 z x y) = (term75 x y z).
Proof. exact (TRANS (@lem1566271 x z y) (@lem1566308 x y z)). Qed.
Lemma lem1566310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566311 (x : real) (y : real) (z : real) : (term57 z x y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1566310) (@lem1566309 x y z)). Qed.
Lemma lem1566312 (y : real) (z : real) : (term53 y z) = (term53 y z).
Proof. exact (eq_refl (term53 y z)). Qed.
Lemma lem1566315 (x : real) (y : real) (z : real) : (term179 x y z) = (term180 x y z).
Proof. exact (MK_COMB (@lem1566311 x y z) (@lem1566312 y z)). Qed.
Lemma lem1566316 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566317 (y : real) (x : real) (z : real) : (term181 y x z) = (term182 y x z).
Proof. exact (MK_COMB (@lem1566316) (@lem1566268 y x z)). Qed.
Lemma lem1566318 (x : real) (y : real) (z : real) : (term161 x y z) = (term183 x y z).
Proof. exact (MK_COMB (@lem1566317 y x z) (@lem1566315 x y z)). Qed.
Lemma lem1566320 (x : real) (y : real) (z : real) : (term184 z x y) = (term78 x y z).
Proof. exact (eq_refl (term184 z x y)). Qed.
Lemma lem1566321 (z : real) (x : real) (y : real) : (term78 x y z) = (term184 z x y).
Proof. exact (SYM (@lem1566320 x y z)). Qed.
Lemma lem1566322 (y : real) (z : real) (x : real) : (term184 z x y) = (term185 y z x).
Proof. exact (@lem1483205 y (term186 x y z) x). Qed.
Lemma lem1566323 (y : real) (z : real) (x : real) : (term78 x y z) = (term185 y z x).
Proof. exact (TRANS (@lem1566321 z x y) (@lem1566322 y z x)). Qed.
Lemma lem1566324 (x : real) (y : real) (z : real) : (term187 y z x) = (term188 x y z).
Proof. exact (eq_refl (term187 y z x)). Qed.
Lemma lem1566325 (x : real) (y : real) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1566326 (x : real) (y : real) (z : real) : (term190 y z x) = (term191 x y z).
Proof. exact (MK_COMB (@lem1566325 x y) (@lem1566324 x y z)). Qed.
Lemma lem1566327 (x : real) (y : real) (z : real) : (term192 x z y) = (term193 x y z).
Proof. exact (eq_refl (term192 x z y)). Qed.
Lemma lem1566328 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (eq_refl (term194 y x)). Qed.
Lemma lem1566329 (x : real) (y : real) (z : real) : (term195 x z y) = (term196 x y z).
Proof. exact (MK_COMB (@lem1566328 y x) (@lem1566327 x y z)). Qed.
Lemma lem1566330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566331 (x : real) (y : real) (z : real) : (term197 x z y) = (term198 x y z).
Proof. exact (MK_COMB (@lem1566330) (@lem1566329 x y z)). Qed.
Lemma lem1566332 (x : real) (y : real) (z : real) : (term185 y z x) = (term199 x y z).
Proof. exact (MK_COMB (@lem1566331 x y z) (@lem1566326 x y z)). Qed.
Lemma lem1566333 (x : real) (y : real) (z : real) : (term200 x y z) = (term200 x y z).
Proof. exact (eq_refl (term200 x y z)). Qed.
Lemma lem1566334 (x : real) (y : real) (z : real) : ((term78 x y z) = (term185 y z x)) = ((term78 x y z) = (term199 x y z)).
Proof. exact (MK_COMB (@lem1566333 x y z) (@lem1566332 x y z)). Qed.
Lemma lem1566335 (x : real) (y : real) (z : real) : (term78 x y z) = (term199 x y z).
Proof. exact (EQ_MP (@lem1566334 x y z) (@lem1566323 y z x)). Qed.
Lemma lem1566336 (y : real) (x : real) : (real_ge y x) = (term68 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1566342 (y : real) (x : real) : (real_sub y x) = (term50 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1566347 (x : real) (y : real) : (term50 y x) = (term69 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1566349 (x : real) (y : real) : (real_sub y x) = (term69 x y).
Proof. exact (TRANS (@lem1566342 y x) (@lem1566347 x y)). Qed.
Lemma lem1566350 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566351 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1566350) (@lem1566349 x y)). Qed.
Lemma lem1566352 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566353 (x : real) (y : real) : (term68 y x) = (term72 x y).
Proof. exact (MK_COMB (@lem1566351 x y) (@lem1566352)). Qed.
Lemma lem1566354 (x : real) (y : real) : (real_ge y x) = (term72 x y).
Proof. exact (TRANS (@lem1566336 y x) (@lem1566353 x y)). Qed.
Lemma lem1566355 (z : real) (y : real) : (term201 z y) = (term202 z y).
Proof. exact (@lem1483525 (term69 z y) term46). Qed.
Lemma lem1566356 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566369 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1566370 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1566371 (y : real) (z : real) : (term203 z y) = (term204 y z).
Proof. exact (MK_COMB (@lem1566370) (@lem1566369 y z)). Qed.
Lemma lem1566372 (y : real) (z : real) : (term205 z y) = (term206 y z).
Proof. exact (MK_COMB (@lem1566371 y z) (@lem1566356)). Qed.
Lemma lem1566373 (y : real) (z : real) : (term206 y z) = (term207 y z).
Proof. exact (@lem1483519 (term50 y z) term46). Qed.
Lemma lem1566375 (x : nat) : (term208 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1566376 : term209 = term46.
Proof. exact (@lem1566375 term210). Qed.
Lemma lem1566377 (y : real) (z : real) : (term211 y z) = (term211 y z).
Proof. exact (eq_refl (term211 y z)). Qed.
Lemma lem1566378 (y : real) (z : real) : (term207 y z) = (term212 y z).
Proof. exact (MK_COMB (@lem1566377 y z) (@lem1566376)). Qed.
Lemma lem1566379 (y : real) (z : real) : (term212 y z) = (term50 y z).
Proof. exact (@lem1483450 (term50 y z)). Qed.
Lemma lem1566380 (y : real) (z : real) : (term207 y z) = (term50 y z).
Proof. exact (TRANS (@lem1566378 y z) (@lem1566379 y z)). Qed.
Lemma lem1566381 (y : real) (z : real) : (term206 y z) = (term50 y z).
Proof. exact (TRANS (@lem1566373 y z) (@lem1566380 y z)). Qed.
Lemma lem1566382 (y : real) (z : real) : (term205 z y) = (term50 y z).
Proof. exact (TRANS (@lem1566372 y z) (@lem1566381 y z)). Qed.
Lemma lem1566383 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566384 (y : real) (z : real) : (term213 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1566383) (@lem1566382 y z)). Qed.
Lemma lem1566385 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566386 (y : real) (z : real) : (term202 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1566384 y z) (@lem1566385)). Qed.
Lemma lem1566387 (y : real) (z : real) : (term201 z y) = (term53 y z).
Proof. exact (TRANS (@lem1566355 z y) (@lem1566386 y z)). Qed.
Lemma lem1566388 (x : real) (z : real) : (term72 x z) = (term214 x z).
Proof. exact (@lem1483527 (term69 x z) term46). Qed.
Lemma lem1566406 (x : real) (z : real) : (term205 x z) = (term215 x z).
Proof. exact (@lem1483519 (term69 x z) term46). Qed.
Lemma lem1566408 (x : nat) : (term208 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1566409 : term209 = term46.
Proof. exact (@lem1566408 term210). Qed.
Lemma lem1566410 (x : real) (z : real) : (term216 x z) = (term216 x z).
Proof. exact (eq_refl (term216 x z)). Qed.
Lemma lem1566411 (x : real) (z : real) : (term215 x z) = (term217 x z).
Proof. exact (MK_COMB (@lem1566410 x z) (@lem1566409)). Qed.
Lemma lem1566412 (x : real) (z : real) : (term217 x z) = (term69 x z).
Proof. exact (@lem1483450 (term69 x z)). Qed.
Lemma lem1566413 (x : real) (z : real) : (term215 x z) = (term69 x z).
Proof. exact (TRANS (@lem1566411 x z) (@lem1566412 x z)). Qed.
Lemma lem1566415 (x : real) (z : real) : (term205 x z) = (term69 x z).
Proof. exact (TRANS (@lem1566406 x z) (@lem1566413 x z)). Qed.
Lemma lem1566416 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566417 (x : real) (z : real) : (term218 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1566416) (@lem1566415 x z)). Qed.
Lemma lem1566418 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566419 (x : real) (z : real) : (term214 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1566417 x z) (@lem1566418)). Qed.
Lemma lem1566420 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (TRANS (@lem1566388 x z) (@lem1566419 x z)). Qed.
Lemma lem1566421 (y : real) (z : real) : (term72 y z) = (term214 y z).
Proof. exact (@lem1483527 (term69 y z) term46). Qed.
Lemma lem1566439 (y : real) (z : real) : (term205 y z) = (term215 y z).
Proof. exact (@lem1483519 (term69 y z) term46). Qed.
Lemma lem1566441 (x : nat) : (term208 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1566442 : term209 = term46.
Proof. exact (@lem1566441 term210). Qed.
Lemma lem1566443 (y : real) (z : real) : (term216 y z) = (term216 y z).
Proof. exact (eq_refl (term216 y z)). Qed.
Lemma lem1566444 (y : real) (z : real) : (term215 y z) = (term217 y z).
Proof. exact (MK_COMB (@lem1566443 y z) (@lem1566442)). Qed.
Lemma lem1566445 (y : real) (z : real) : (term217 y z) = (term69 y z).
Proof. exact (@lem1483450 (term69 y z)). Qed.
Lemma lem1566446 (y : real) (z : real) : (term215 y z) = (term69 y z).
Proof. exact (TRANS (@lem1566444 y z) (@lem1566445 y z)). Qed.
Lemma lem1566448 (y : real) (z : real) : (term205 y z) = (term69 y z).
Proof. exact (TRANS (@lem1566439 y z) (@lem1566446 y z)). Qed.
Lemma lem1566449 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566450 (y : real) (z : real) : (term218 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1566449) (@lem1566448 y z)). Qed.
Lemma lem1566451 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566452 (y : real) (z : real) : (term214 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1566450 y z) (@lem1566451)). Qed.
Lemma lem1566453 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (TRANS (@lem1566421 y z) (@lem1566452 y z)). Qed.
Lemma lem1566454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566455 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1566454) (@lem1566420 x z)). Qed.
Lemma lem1566456 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1566455 x z) (@lem1566453 y z)). Qed.
Lemma lem1566457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566458 (y : real) (z : real) : (term219 z y) = (term220 y z).
Proof. exact (MK_COMB (@lem1566457) (@lem1566387 y z)). Qed.
Lemma lem1566459 (x : real) (y : real) (z : real) : (term193 x y z) = (term221 x y z).
Proof. exact (MK_COMB (@lem1566458 y z) (@lem1566456 x y z)). Qed.
Lemma lem1566460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566461 (x : real) (y : real) : (term194 y x) = (term74 x y).
Proof. exact (MK_COMB (@lem1566460) (@lem1566354 x y)). Qed.
Lemma lem1566462 (x : real) (y : real) (z : real) : (term196 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1566461 x y) (@lem1566459 x y z)). Qed.
Lemma lem1566463 (x : real) (y : real) : (real_gt x y) = (term49 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1566476 (x : real) (y : real) : (real_sub x y) = (term50 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1566477 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566478 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1566477) (@lem1566476 x y)). Qed.
Lemma lem1566479 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566480 (x : real) (y : real) : (term49 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1566478 x y) (@lem1566479)). Qed.
Lemma lem1566481 (x : real) (y : real) : (real_gt x y) = (term53 x y).
Proof. exact (TRANS (@lem1566463 x y) (@lem1566480 x y)). Qed.
Lemma lem1566482 (z : real) (x : real) : (term201 z x) = (term202 z x).
Proof. exact (@lem1483525 (term69 z x) term46). Qed.
Lemma lem1566483 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566496 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1566497 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1566498 (x : real) (z : real) : (term203 z x) = (term204 x z).
Proof. exact (MK_COMB (@lem1566497) (@lem1566496 x z)). Qed.
Lemma lem1566499 (x : real) (z : real) : (term205 z x) = (term206 x z).
Proof. exact (MK_COMB (@lem1566498 x z) (@lem1566483)). Qed.
Lemma lem1566500 (x : real) (z : real) : (term206 x z) = (term207 x z).
Proof. exact (@lem1483519 (term50 x z) term46). Qed.
Lemma lem1566502 (x : nat) : (term208 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1566503 : term209 = term46.
Proof. exact (@lem1566502 term210). Qed.
Lemma lem1566504 (x : real) (z : real) : (term211 x z) = (term211 x z).
Proof. exact (eq_refl (term211 x z)). Qed.
Lemma lem1566505 (x : real) (z : real) : (term207 x z) = (term212 x z).
Proof. exact (MK_COMB (@lem1566504 x z) (@lem1566503)). Qed.
Lemma lem1566506 (x : real) (z : real) : (term212 x z) = (term50 x z).
Proof. exact (@lem1483450 (term50 x z)). Qed.
Lemma lem1566507 (x : real) (z : real) : (term207 x z) = (term50 x z).
Proof. exact (TRANS (@lem1566505 x z) (@lem1566506 x z)). Qed.
Lemma lem1566508 (x : real) (z : real) : (term206 x z) = (term50 x z).
Proof. exact (TRANS (@lem1566500 x z) (@lem1566507 x z)). Qed.
Lemma lem1566509 (x : real) (z : real) : (term205 z x) = (term50 x z).
Proof. exact (TRANS (@lem1566499 x z) (@lem1566508 x z)). Qed.
Lemma lem1566510 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566511 (x : real) (z : real) : (term213 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1566510) (@lem1566509 x z)). Qed.
Lemma lem1566512 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566513 (x : real) (z : real) : (term202 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1566511 x z) (@lem1566512)). Qed.
Lemma lem1566514 (x : real) (z : real) : (term201 z x) = (term53 x z).
Proof. exact (TRANS (@lem1566482 z x) (@lem1566513 x z)). Qed.
Lemma lem1566515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566516 (x : real) (z : real) : (term74 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1566515) (@lem1566420 x z)). Qed.
Lemma lem1566517 (x : real) (y : real) (z : real) : (term75 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1566516 x z) (@lem1566453 y z)). Qed.
Lemma lem1566518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566519 (x : real) (z : real) : (term219 z x) = (term220 x z).
Proof. exact (MK_COMB (@lem1566518) (@lem1566514 x z)). Qed.
Lemma lem1566520 (x : real) (y : real) (z : real) : (term188 x y z) = (term223 x y z).
Proof. exact (MK_COMB (@lem1566519 x z) (@lem1566517 x y z)). Qed.
Lemma lem1566521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1566522 (x : real) (y : real) : (term189 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1566521) (@lem1566481 x y)). Qed.
Lemma lem1566523 (x : real) (y : real) (z : real) : (term191 x y z) = (term224 x y z).
Proof. exact (MK_COMB (@lem1566522 x y) (@lem1566520 x y z)). Qed.
Lemma lem1566524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566525 (x : real) (y : real) (z : real) : (term198 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1566524) (@lem1566462 x y z)). Qed.
Lemma lem1566526 (x : real) (y : real) (z : real) : (term199 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1566525 x y z) (@lem1566523 x y z)). Qed.
Lemma lem1566538 (x : real) (y : real) (z : real) : (term78 x y z) = (term226 x y z).
Proof. exact (TRANS (@lem1566335 x y z) (@lem1566526 x y z)). Qed.
Lemma lem1566539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566540 (x : real) (y : real) (z : real) : (term162 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1566539) (@lem1566318 x y z)). Qed.
Lemma lem1566541 (x : real) (y : real) (z : real) : (term163 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1566540 x y z) (@lem1566538 x y z)). Qed.
Lemma lem1566542 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term228 x y z.
Proof. exact (h1). Qed.
Lemma lem1566543 (x : real) (y : real) (z : real) (h1 : term183 x y z) : term183 x y z.
Proof. exact (h1). Qed.
Lemma lem1566544 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term178 y x z.
Proof. exact (h1). Qed.
Lemma lem1566545 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term53 x z.
Proof. exact (proj2 (@lem1566544 y x z h1)). Qed.
Lemma lem1566546 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term75 x y z.
Proof. exact (proj1 (@lem1566544 y x z h1)). Qed.
Lemma lem1566548 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (proj1 (@lem1566546 y x z h1)). Qed.
Lemma lem1566550 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566551 : term230 = term231.
Proof. exact (@lem1566550 (NUMERAL 0) term210). Qed.
Lemma lem1566552 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566553 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566554 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566553 h1) (fun h1 : term231 = True => @lem1566552)). Qed.
Lemma lem1566555 : term231 = True.
Proof. exact (EQ_MP (@lem1566554) (@lem1566552)). Qed.
Lemma lem1566556 : term230 = True.
Proof. exact (TRANS (@lem1566551) (@lem1566555)). Qed.
Lemma lem1566557 : True = term230.
Proof. exact (SYM (@lem1566556)). Qed.
Lemma lem1566558 : term230.
Proof. exact (EQ_MP (@lem1566557) (@lem0)). Qed.
Lemma lem1566559 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term233 x z.
Proof. exact (conj (@lem1566558) (@lem1566548 y x z h1)). Qed.
Lemma lem1566561 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1566562 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1566561 term236 (term69 x z)). Qed.
Lemma lem1566563 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term237 x z.
Proof. exact (@lem1566562 x z (@lem1566559 y x z h1)). Qed.
Lemma lem1566564 (x : real) (z : real) : (term238 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1566565 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566566 (x : real) (z : real) : (term239 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1566565) (@lem1566564 x z)). Qed.
Lemma lem1566567 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566568 (x : real) (z : real) : (term237 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1566566 x z) (@lem1566567)). Qed.
Lemma lem1566569 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1566568 x z) (@lem1566563 y x z h1)). Qed.
Lemma lem1566571 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566572 : term230 = term231.
Proof. exact (@lem1566571 (NUMERAL 0) term210). Qed.
Lemma lem1566573 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566574 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566575 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566574 h1) (fun h1 : term231 = True => @lem1566573)). Qed.
Lemma lem1566576 : term231 = True.
Proof. exact (EQ_MP (@lem1566575) (@lem1566573)). Qed.
Lemma lem1566577 : term230 = True.
Proof. exact (TRANS (@lem1566572) (@lem1566576)). Qed.
Lemma lem1566578 : True = term230.
Proof. exact (SYM (@lem1566577)). Qed.
Lemma lem1566579 : term230.
Proof. exact (EQ_MP (@lem1566578) (@lem0)). Qed.
Lemma lem1566580 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term240 x z.
Proof. exact (conj (@lem1566579) (@lem1566545 y x z h1)). Qed.
Lemma lem1566582 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1566583 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1566582 term236 (term50 x z)). Qed.
Lemma lem1566584 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term243 x z.
Proof. exact (@lem1566583 x z (@lem1566580 y x z h1)). Qed.
Lemma lem1566585 (x : real) (z : real) : (term244 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1566586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566587 (x : real) (z : real) : (term245 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1566586) (@lem1566585 x z)). Qed.
Lemma lem1566588 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566589 (x : real) (z : real) : (term243 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1566587 x z) (@lem1566588)). Qed.
Lemma lem1566590 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term53 x z.
Proof. exact (EQ_MP (@lem1566589 x z) (@lem1566584 y x z h1)). Qed.
Lemma lem1566591 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term246 x z.
Proof. exact (conj (@lem1566590 y x z h1) (@lem1566569 y x z h1)). Qed.
Lemma lem1566593 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1566594 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1566593 (term50 x z) (term69 x z)). Qed.
Lemma lem1566595 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term249 x z.
Proof. exact (@lem1566594 x z (@lem1566591 y x z h1)). Qed.
Lemma lem1566596 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 x (term64 x) (term64 z) z). Qed.
Lemma lem1566597 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483442 term254 x). Qed.
Lemma lem1566599 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566600 : term256 = term46.
Proof. exact (@lem1566599 term210). Qed.
Lemma lem1566601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566602 : term257 = term258.
Proof. exact (MK_COMB (@lem1566601) (@lem1566600)). Qed.
Lemma lem1566603 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1566604 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1566602) (@lem1566603 x)). Qed.
Lemma lem1566605 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1566597 x) (@lem1566604 x)). Qed.
Lemma lem1566606 (x : real) : (term259 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1566607 (x : real) : (term252 x) = term46.
Proof. exact (TRANS (@lem1566605 x) (@lem1566606 x)). Qed.
Lemma lem1566608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1566609 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1566608) (@lem1566607 x)). Qed.
Lemma lem1566610 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1566612 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566613 : term256 = term46.
Proof. exact (@lem1566612 term210). Qed.
Lemma lem1566614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566615 : term257 = term258.
Proof. exact (MK_COMB (@lem1566614) (@lem1566613)). Qed.
Lemma lem1566616 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1566617 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1566615) (@lem1566616 z)). Qed.
Lemma lem1566618 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1566610 z) (@lem1566617 z)). Qed.
Lemma lem1566619 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1566620 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1566618 z) (@lem1566619 z)). Qed.
Lemma lem1566621 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1566609 x) (@lem1566620 z)). Qed.
Lemma lem1566622 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1566596 x z) (@lem1566621 x z)). Qed.
Lemma lem1566623 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1566624 (x : real) (z : real) : (term250 x z) = term46.
Proof. exact (TRANS (@lem1566622 x z) (@lem1566623)). Qed.
Lemma lem1566625 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566626 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1566625) (@lem1566624 x z)). Qed.
Lemma lem1566627 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566628 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1566626 x z) (@lem1566627)). Qed.
Lemma lem1566629 (y : real) (x : real) (z : real) (h1 : term178 y x z) : term266.
Proof. exact (EQ_MP (@lem1566628 x z) (@lem1566595 y x z h1)). Qed.
Lemma lem1566631 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566632 : term266 = term267.
Proof. exact (@lem1566631 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1566633 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1566634 : term266 = False.
Proof. exact (TRANS (@lem1566632) (@lem1566633)). Qed.
Lemma lem1566635 (y : real) (x : real) (z : real) (h1 : term178 y x z) : False.
Proof. exact (EQ_MP (@lem1566634) (@lem1566629 y x z h1)). Qed.
Lemma lem1566636 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term180 x y z.
Proof. exact (h1). Qed.
Lemma lem1566637 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term53 y z.
Proof. exact (proj2 (@lem1566636 x y z h1)). Qed.
Lemma lem1566638 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term75 x y z.
Proof. exact (proj1 (@lem1566636 x y z h1)). Qed.
Lemma lem1566639 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (proj2 (@lem1566638 x y z h1)). Qed.
Lemma lem1566642 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566643 : term230 = term231.
Proof. exact (@lem1566642 (NUMERAL 0) term210). Qed.
Lemma lem1566644 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566645 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566646 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566645 h1) (fun h1 : term231 = True => @lem1566644)). Qed.
Lemma lem1566647 : term231 = True.
Proof. exact (EQ_MP (@lem1566646) (@lem1566644)). Qed.
Lemma lem1566648 : term230 = True.
Proof. exact (TRANS (@lem1566643) (@lem1566647)). Qed.
Lemma lem1566649 : True = term230.
Proof. exact (SYM (@lem1566648)). Qed.
Lemma lem1566650 : term230.
Proof. exact (EQ_MP (@lem1566649) (@lem0)). Qed.
Lemma lem1566651 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term233 y z.
Proof. exact (conj (@lem1566650) (@lem1566639 x y z h1)). Qed.
Lemma lem1566653 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1566654 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1566653 term236 (term69 y z)). Qed.
Lemma lem1566655 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term237 y z.
Proof. exact (@lem1566654 y z (@lem1566651 x y z h1)). Qed.
Lemma lem1566656 (y : real) (z : real) : (term238 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1566657 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566658 (y : real) (z : real) : (term239 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1566657) (@lem1566656 y z)). Qed.
Lemma lem1566659 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566660 (y : real) (z : real) : (term237 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1566658 y z) (@lem1566659)). Qed.
Lemma lem1566661 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1566660 y z) (@lem1566655 x y z h1)). Qed.
Lemma lem1566663 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566664 : term230 = term231.
Proof. exact (@lem1566663 (NUMERAL 0) term210). Qed.
Lemma lem1566665 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566666 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566667 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566666 h1) (fun h1 : term231 = True => @lem1566665)). Qed.
Lemma lem1566668 : term231 = True.
Proof. exact (EQ_MP (@lem1566667) (@lem1566665)). Qed.
Lemma lem1566669 : term230 = True.
Proof. exact (TRANS (@lem1566664) (@lem1566668)). Qed.
Lemma lem1566670 : True = term230.
Proof. exact (SYM (@lem1566669)). Qed.
Lemma lem1566671 : term230.
Proof. exact (EQ_MP (@lem1566670) (@lem0)). Qed.
Lemma lem1566672 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term240 y z.
Proof. exact (conj (@lem1566671) (@lem1566637 x y z h1)). Qed.
Lemma lem1566674 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1566675 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1566674 term236 (term50 y z)). Qed.
Lemma lem1566676 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term243 y z.
Proof. exact (@lem1566675 y z (@lem1566672 x y z h1)). Qed.
Lemma lem1566677 (y : real) (z : real) : (term244 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1566678 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566679 (y : real) (z : real) : (term245 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1566678) (@lem1566677 y z)). Qed.
Lemma lem1566680 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566681 (y : real) (z : real) : (term243 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1566679 y z) (@lem1566680)). Qed.
Lemma lem1566682 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1566681 y z) (@lem1566676 x y z h1)). Qed.
Lemma lem1566683 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term246 y z.
Proof. exact (conj (@lem1566682 x y z h1) (@lem1566661 x y z h1)). Qed.
Lemma lem1566685 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1566686 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1566685 (term50 y z) (term69 y z)). Qed.
Lemma lem1566687 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term249 y z.
Proof. exact (@lem1566686 y z (@lem1566683 x y z h1)). Qed.
Lemma lem1566688 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 y (term64 y) (term64 z) z). Qed.
Lemma lem1566689 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483442 term254 y). Qed.
Lemma lem1566691 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566692 : term256 = term46.
Proof. exact (@lem1566691 term210). Qed.
Lemma lem1566693 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566694 : term257 = term258.
Proof. exact (MK_COMB (@lem1566693) (@lem1566692)). Qed.
Lemma lem1566695 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1566696 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1566694) (@lem1566695 y)). Qed.
Lemma lem1566697 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1566689 y) (@lem1566696 y)). Qed.
Lemma lem1566698 (y : real) : (term259 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1566699 (y : real) : (term252 y) = term46.
Proof. exact (TRANS (@lem1566697 y) (@lem1566698 y)). Qed.
Lemma lem1566700 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1566701 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1566700) (@lem1566699 y)). Qed.
Lemma lem1566702 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1566704 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566705 : term256 = term46.
Proof. exact (@lem1566704 term210). Qed.
Lemma lem1566706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566707 : term257 = term258.
Proof. exact (MK_COMB (@lem1566706) (@lem1566705)). Qed.
Lemma lem1566708 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1566709 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1566707) (@lem1566708 z)). Qed.
Lemma lem1566710 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1566702 z) (@lem1566709 z)). Qed.
Lemma lem1566711 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1566712 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1566710 z) (@lem1566711 z)). Qed.
Lemma lem1566713 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1566701 y) (@lem1566712 z)). Qed.
Lemma lem1566714 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1566688 y z) (@lem1566713 y z)). Qed.
Lemma lem1566715 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1566716 (y : real) (z : real) : (term250 y z) = term46.
Proof. exact (TRANS (@lem1566714 y z) (@lem1566715)). Qed.
Lemma lem1566717 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566718 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1566717) (@lem1566716 y z)). Qed.
Lemma lem1566719 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566720 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1566718 y z) (@lem1566719)). Qed.
Lemma lem1566721 (x : real) (y : real) (z : real) (h1 : term180 x y z) : term266.
Proof. exact (EQ_MP (@lem1566720 y z) (@lem1566687 x y z h1)). Qed.
Lemma lem1566723 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566724 : term266 = term267.
Proof. exact (@lem1566723 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1566725 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1566726 : term266 = False.
Proof. exact (TRANS (@lem1566724) (@lem1566725)). Qed.
Lemma lem1566727 (x : real) (y : real) (z : real) (h1 : term180 x y z) : False.
Proof. exact (EQ_MP (@lem1566726) (@lem1566721 x y z h1)). Qed.
Lemma lem1566728 (x : real) (y : real) (z : real) (h1 : term183 x y z) : False.
Proof. exact (or_elim (@lem1566543 x y z h1) (fun h0 : term178 y x z => @lem1566635 y x z h0) (fun h0 : term180 x y z => @lem1566727 x y z h0)). Qed.
Lemma lem1566729 (x : real) (y : real) (z : real) (h1 : term226 x y z) : term226 x y z.
Proof. exact (h1). Qed.
Lemma lem1566730 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1566731 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term221 x y z.
Proof. exact (proj2 (@lem1566730 x y z h1)). Qed.
Lemma lem1566733 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1566731 x y z h1)). Qed.
Lemma lem1566734 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term53 y z.
Proof. exact (proj1 (@lem1566731 x y z h1)). Qed.
Lemma lem1566735 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (proj2 (@lem1566733 x y z h1)). Qed.
Lemma lem1566738 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566739 : term230 = term231.
Proof. exact (@lem1566738 (NUMERAL 0) term210). Qed.
Lemma lem1566740 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566741 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566742 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566741 h1) (fun h1 : term231 = True => @lem1566740)). Qed.
Lemma lem1566743 : term231 = True.
Proof. exact (EQ_MP (@lem1566742) (@lem1566740)). Qed.
Lemma lem1566744 : term230 = True.
Proof. exact (TRANS (@lem1566739) (@lem1566743)). Qed.
Lemma lem1566745 : True = term230.
Proof. exact (SYM (@lem1566744)). Qed.
Lemma lem1566746 : term230.
Proof. exact (EQ_MP (@lem1566745) (@lem0)). Qed.
Lemma lem1566747 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term233 y z.
Proof. exact (conj (@lem1566746) (@lem1566735 x y z h1)). Qed.
Lemma lem1566749 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1566750 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1566749 term236 (term69 y z)). Qed.
Lemma lem1566751 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term237 y z.
Proof. exact (@lem1566750 y z (@lem1566747 x y z h1)). Qed.
Lemma lem1566752 (y : real) (z : real) : (term238 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1566753 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566754 (y : real) (z : real) : (term239 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1566753) (@lem1566752 y z)). Qed.
Lemma lem1566755 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566756 (y : real) (z : real) : (term237 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1566754 y z) (@lem1566755)). Qed.
Lemma lem1566757 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1566756 y z) (@lem1566751 x y z h1)). Qed.
Lemma lem1566759 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566760 : term230 = term231.
Proof. exact (@lem1566759 (NUMERAL 0) term210). Qed.
Lemma lem1566761 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566762 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566763 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566762 h1) (fun h1 : term231 = True => @lem1566761)). Qed.
Lemma lem1566764 : term231 = True.
Proof. exact (EQ_MP (@lem1566763) (@lem1566761)). Qed.
Lemma lem1566765 : term230 = True.
Proof. exact (TRANS (@lem1566760) (@lem1566764)). Qed.
Lemma lem1566766 : True = term230.
Proof. exact (SYM (@lem1566765)). Qed.
Lemma lem1566767 : term230.
Proof. exact (EQ_MP (@lem1566766) (@lem0)). Qed.
Lemma lem1566768 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term240 y z.
Proof. exact (conj (@lem1566767) (@lem1566734 x y z h1)). Qed.
Lemma lem1566770 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1566771 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1566770 term236 (term50 y z)). Qed.
Lemma lem1566772 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term243 y z.
Proof. exact (@lem1566771 y z (@lem1566768 x y z h1)). Qed.
Lemma lem1566773 (y : real) (z : real) : (term244 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1566774 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566775 (y : real) (z : real) : (term245 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1566774) (@lem1566773 y z)). Qed.
Lemma lem1566776 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566777 (y : real) (z : real) : (term243 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1566775 y z) (@lem1566776)). Qed.
Lemma lem1566778 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1566777 y z) (@lem1566772 x y z h1)). Qed.
Lemma lem1566779 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term246 y z.
Proof. exact (conj (@lem1566778 x y z h1) (@lem1566757 x y z h1)). Qed.
Lemma lem1566781 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1566782 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1566781 (term50 y z) (term69 y z)). Qed.
Lemma lem1566783 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term249 y z.
Proof. exact (@lem1566782 y z (@lem1566779 x y z h1)). Qed.
Lemma lem1566784 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 y (term64 y) (term64 z) z). Qed.
Lemma lem1566785 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483442 term254 y). Qed.
Lemma lem1566787 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566788 : term256 = term46.
Proof. exact (@lem1566787 term210). Qed.
Lemma lem1566789 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566790 : term257 = term258.
Proof. exact (MK_COMB (@lem1566789) (@lem1566788)). Qed.
Lemma lem1566791 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1566792 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1566790) (@lem1566791 y)). Qed.
Lemma lem1566793 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1566785 y) (@lem1566792 y)). Qed.
Lemma lem1566794 (y : real) : (term259 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1566795 (y : real) : (term252 y) = term46.
Proof. exact (TRANS (@lem1566793 y) (@lem1566794 y)). Qed.
Lemma lem1566796 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1566797 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1566796) (@lem1566795 y)). Qed.
Lemma lem1566798 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1566800 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566801 : term256 = term46.
Proof. exact (@lem1566800 term210). Qed.
Lemma lem1566802 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566803 : term257 = term258.
Proof. exact (MK_COMB (@lem1566802) (@lem1566801)). Qed.
Lemma lem1566804 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1566805 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1566803) (@lem1566804 z)). Qed.
Lemma lem1566806 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1566798 z) (@lem1566805 z)). Qed.
Lemma lem1566807 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1566808 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1566806 z) (@lem1566807 z)). Qed.
Lemma lem1566809 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1566797 y) (@lem1566808 z)). Qed.
Lemma lem1566810 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1566784 y z) (@lem1566809 y z)). Qed.
Lemma lem1566811 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1566812 (y : real) (z : real) : (term250 y z) = term46.
Proof. exact (TRANS (@lem1566810 y z) (@lem1566811)). Qed.
Lemma lem1566813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566814 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1566813) (@lem1566812 y z)). Qed.
Lemma lem1566815 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566816 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1566814 y z) (@lem1566815)). Qed.
Lemma lem1566817 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term266.
Proof. exact (EQ_MP (@lem1566816 y z) (@lem1566783 x y z h1)). Qed.
Lemma lem1566819 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566820 : term266 = term267.
Proof. exact (@lem1566819 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1566821 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1566822 : term266 = False.
Proof. exact (TRANS (@lem1566820) (@lem1566821)). Qed.
Lemma lem1566823 (x : real) (y : real) (z : real) (h1 : term222 x y z) : False.
Proof. exact (EQ_MP (@lem1566822) (@lem1566817 x y z h1)). Qed.
Lemma lem1566824 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term224 x y z.
Proof. exact (h1). Qed.
Lemma lem1566825 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term223 x y z.
Proof. exact (proj2 (@lem1566824 x y z h1)). Qed.
Lemma lem1566827 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term75 x y z.
Proof. exact (proj2 (@lem1566825 x y z h1)). Qed.
Lemma lem1566828 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term53 x z.
Proof. exact (proj1 (@lem1566825 x y z h1)). Qed.
Lemma lem1566830 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term72 x z.
Proof. exact (proj1 (@lem1566827 x y z h1)). Qed.
Lemma lem1566832 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566833 : term230 = term231.
Proof. exact (@lem1566832 (NUMERAL 0) term210). Qed.
Lemma lem1566834 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566835 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566836 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566835 h1) (fun h1 : term231 = True => @lem1566834)). Qed.
Lemma lem1566837 : term231 = True.
Proof. exact (EQ_MP (@lem1566836) (@lem1566834)). Qed.
Lemma lem1566838 : term230 = True.
Proof. exact (TRANS (@lem1566833) (@lem1566837)). Qed.
Lemma lem1566839 : True = term230.
Proof. exact (SYM (@lem1566838)). Qed.
Lemma lem1566840 : term230.
Proof. exact (EQ_MP (@lem1566839) (@lem0)). Qed.
Lemma lem1566841 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term233 x z.
Proof. exact (conj (@lem1566840) (@lem1566830 x y z h1)). Qed.
Lemma lem1566843 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1566844 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1566843 term236 (term69 x z)). Qed.
Lemma lem1566845 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term237 x z.
Proof. exact (@lem1566844 x z (@lem1566841 x y z h1)). Qed.
Lemma lem1566846 (x : real) (z : real) : (term238 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1566847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1566848 (x : real) (z : real) : (term239 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1566847) (@lem1566846 x z)). Qed.
Lemma lem1566849 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566850 (x : real) (z : real) : (term237 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1566848 x z) (@lem1566849)). Qed.
Lemma lem1566851 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1566850 x z) (@lem1566845 x y z h1)). Qed.
Lemma lem1566853 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566854 : term230 = term231.
Proof. exact (@lem1566853 (NUMERAL 0) term210). Qed.
Lemma lem1566855 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1566856 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1566857 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1566856 h1) (fun h1 : term231 = True => @lem1566855)). Qed.
Lemma lem1566858 : term231 = True.
Proof. exact (EQ_MP (@lem1566857) (@lem1566855)). Qed.
Lemma lem1566859 : term230 = True.
Proof. exact (TRANS (@lem1566854) (@lem1566858)). Qed.
Lemma lem1566860 : True = term230.
Proof. exact (SYM (@lem1566859)). Qed.
Lemma lem1566861 : term230.
Proof. exact (EQ_MP (@lem1566860) (@lem0)). Qed.
Lemma lem1566862 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term240 x z.
Proof. exact (conj (@lem1566861) (@lem1566828 x y z h1)). Qed.
Lemma lem1566864 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1566865 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1566864 term236 (term50 x z)). Qed.
Lemma lem1566866 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term243 x z.
Proof. exact (@lem1566865 x z (@lem1566862 x y z h1)). Qed.
Lemma lem1566867 (x : real) (z : real) : (term244 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1566868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566869 (x : real) (z : real) : (term245 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1566868) (@lem1566867 x z)). Qed.
Lemma lem1566870 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566871 (x : real) (z : real) : (term243 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1566869 x z) (@lem1566870)). Qed.
Lemma lem1566872 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term53 x z.
Proof. exact (EQ_MP (@lem1566871 x z) (@lem1566866 x y z h1)). Qed.
Lemma lem1566873 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term246 x z.
Proof. exact (conj (@lem1566872 x y z h1) (@lem1566851 x y z h1)). Qed.
Lemma lem1566875 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1566876 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1566875 (term50 x z) (term69 x z)). Qed.
Lemma lem1566877 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term249 x z.
Proof. exact (@lem1566876 x z (@lem1566873 x y z h1)). Qed.
Lemma lem1566878 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 x (term64 x) (term64 z) z). Qed.
Lemma lem1566879 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483442 term254 x). Qed.
Lemma lem1566881 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566882 : term256 = term46.
Proof. exact (@lem1566881 term210). Qed.
Lemma lem1566883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566884 : term257 = term258.
Proof. exact (MK_COMB (@lem1566883) (@lem1566882)). Qed.
Lemma lem1566885 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1566886 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1566884) (@lem1566885 x)). Qed.
Lemma lem1566887 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1566879 x) (@lem1566886 x)). Qed.
Lemma lem1566888 (x : real) : (term259 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1566889 (x : real) : (term252 x) = term46.
Proof. exact (TRANS (@lem1566887 x) (@lem1566888 x)). Qed.
Lemma lem1566890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1566891 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1566890) (@lem1566889 x)). Qed.
Lemma lem1566892 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483440 term254 z). Qed.
Lemma lem1566894 (m : nat) : (term255 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1566895 : term256 = term46.
Proof. exact (@lem1566894 term210). Qed.
Lemma lem1566896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1566897 : term257 = term258.
Proof. exact (MK_COMB (@lem1566896) (@lem1566895)). Qed.
Lemma lem1566898 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1566899 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1566897) (@lem1566898 z)). Qed.
Lemma lem1566900 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1566892 z) (@lem1566899 z)). Qed.
Lemma lem1566901 (z : real) : (term259 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1566902 (z : real) : (term262 z) = term46.
Proof. exact (TRANS (@lem1566900 z) (@lem1566901 z)). Qed.
Lemma lem1566903 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1566891 x) (@lem1566902 z)). Qed.
Lemma lem1566904 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1566878 x z) (@lem1566903 x z)). Qed.
Lemma lem1566905 : term263 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1566906 (x : real) (z : real) : (term250 x z) = term46.
Proof. exact (TRANS (@lem1566904 x z) (@lem1566905)). Qed.
Lemma lem1566907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1566908 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1566907) (@lem1566906 x z)). Qed.
Lemma lem1566909 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1566910 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1566908 x z) (@lem1566909)). Qed.
Lemma lem1566911 (x : real) (y : real) (z : real) (h1 : term224 x y z) : term266.
Proof. exact (EQ_MP (@lem1566910 x z) (@lem1566877 x y z h1)). Qed.
Lemma lem1566913 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1566914 : term266 = term267.
Proof. exact (@lem1566913 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1566915 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1566916 : term266 = False.
Proof. exact (TRANS (@lem1566914) (@lem1566915)). Qed.
Lemma lem1566917 (x : real) (y : real) (z : real) (h1 : term224 x y z) : False.
Proof. exact (EQ_MP (@lem1566916) (@lem1566911 x y z h1)). Qed.
Lemma lem1566918 (x : real) (y : real) (z : real) (h1 : term226 x y z) : False.
Proof. exact (or_elim (@lem1566729 x y z h1) (fun h0 : term222 x y z => @lem1566823 x y z h0) (fun h0 : term224 x y z => @lem1566917 x y z h0)). Qed.
Lemma lem1566919 (x : real) (y : real) (z : real) (h1 : term228 x y z) : False.
Proof. exact (or_elim (@lem1566542 x y z h1) (fun h0 : term183 x y z => @lem1566728 x y z h0) (fun h0 : term226 x y z => @lem1566918 x y z h0)). Qed.
Lemma lem1566920 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term163 x y z.
Proof. exact (h1). Qed.
Lemma lem1566921 (x : real) (y : real) (z : real) (h1 : term163 x y z) : term228 x y z.
Proof. exact (EQ_MP (@lem1566541 x y z) (@lem1566920 x y z h1)). Qed.
Lemma lem1566922 (x : real) (y : real) (z : real) (h1 : term163 x y z) : (term228 x y z) = False.
Proof. exact (prop_ext (fun h2 : term228 x y z => @lem1566919 x y z h2) (fun h2 : False => @lem1566921 x y z h1)). Qed.
Lemma lem1566923 (x : real) (y : real) (z : real) (h1 : term163 x y z) : False.
Proof. exact (EQ_MP (@lem1566922 x y z h1) (@lem1566921 x y z h1)). Qed.
Lemma lem1566924 (x : real) (y : real) (h1 : term165 x y) : term165 x y.
Proof. exact (h1). Qed.
Lemma lem1566925 (x : real) (y : real) (h1 : term165 x y) : False.
Proof. exact (ex_elim (@lem1566924 x y h1) (fun z : real => fun h0 : term164 x y z => @lem1566923 x y z h0)). Qed.
Lemma lem1566926 (x : real) (h1 : term167 x) : term167 x.
Proof. exact (h1). Qed.
Lemma lem1566927 (x : real) (h1 : term167 x) : False.
Proof. exact (ex_elim (@lem1566926 x h1) (fun y : real => fun h0 : term166 x y => @lem1566925 x y h0)). Qed.
Lemma lem1566928 (h1 : term169) : term169.
Proof. exact (h1). Qed.
Lemma lem1566929 (h1 : term169) : False.
Proof. exact (ex_elim (@lem1566928 h1) (fun x : real => fun h0 : term168 x => @lem1566927 x h0)). Qed.
Lemma lem1566930 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1566931 (h1 : term32) : term169.
Proof. exact (EQ_MP (@lem1566221) (@lem1566930 h1)). Qed.
Lemma lem1566932 (h1 : term32) : term169 = False.
Proof. exact (prop_ext (fun h2 : term169 => @lem1566929 h2) (fun h2 : False => @lem1566931 h1)). Qed.
Lemma lem1566933 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1566932 h1) (@lem1566931 h1)). Qed.
Lemma lem1566934 : term268.
Proof. exact (fun h0 : term32 => @lem1566933 h0). Qed.
Lemma lem1566935 : term269.
Proof. exact (@lem1386578 term270). Qed.
Lemma lem1566936 : term270.
Proof. exact (@lem1566935 (@lem1566934)). Qed.

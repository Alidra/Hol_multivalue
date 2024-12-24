Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SUB_ABS_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482703_spec.
Require Import thm1482704_spec.
Require Import thm1482706_spec.
Require Import thm1482707_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Require Import thm940073_spec.
Lemma lem1545475 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1545476 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1545475 (term4 x)). Qed.
Lemma lem1545477 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1545478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1545480 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1545478) (@lem1545477 x y)). Qed.
Lemma lem1545481 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1545480 x y)). Qed.
Lemma lem1545482 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545483 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1545482) (@lem1545481 x)). Qed.
Lemma lem1545484 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1545476 x) (@lem1545483 x)). Qed.
Lemma lem1545485 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1545486 : term12 = term13.
Proof. exact (@lem1545485 term14). Qed.
Lemma lem1545487 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1545488 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1545489 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1545488) (@lem1545487 x)). Qed.
Lemma lem1545490 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1545489 x) (@lem1545484 x)). Qed.
Lemma lem1545491 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1545490 x)). Qed.
Lemma lem1545492 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545493 : term13 = term20.
Proof. exact (MK_COMB (@lem1545492) (@lem1545491)). Qed.
Lemma lem1545495 : term12 = term20.
Proof. exact (TRANS (@lem1545486) (@lem1545493)). Qed.
Lemma lem1545498 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1545499 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1545498 x y)). Qed.
Lemma lem1545500 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545501 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1545500) (@lem1545499 x)). Qed.
Lemma lem1545502 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1545501 x)). Qed.
Lemma lem1545503 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545504 : term20 = term20.
Proof. exact (MK_COMB (@lem1545503) (@lem1545502)). Qed.
Lemma lem1545505 : term12 = term20.
Proof. exact (TRANS (@lem1545495) (@lem1545504)). Qed.
Lemma lem1545506 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483533 (term22 x y) (term23 x y)). Qed.
Lemma lem1545512 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483519 (term22 x y) (term23 x y)). Qed.
Lemma lem1545517 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483488 (term27 x y) (term22 x y)). Qed.
Lemma lem1545519 (x : real) (y : real) : (term24 x y) = (term26 x y).
Proof. exact (TRANS (@lem1545512 x y) (@lem1545517 x y)). Qed.
Lemma lem1545520 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545521 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1545520) (@lem1545519 x y)). Qed.
Lemma lem1545522 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545523 (x : real) (y : real) : (term21 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1545521 x y) (@lem1545522)). Qed.
Lemma lem1545524 (x : real) (y : real) : (term8 x y) = (term31 x y).
Proof. exact (TRANS (@lem1545506 x y) (@lem1545523 x y)). Qed.
Lemma lem1545525 (x : real) : (term10 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1545524 x y)). Qed.
Lemma lem1545526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545527 (x : real) : (term11 x) = (term33 x).
Proof. exact (MK_COMB (@lem1545526) (@lem1545525 x)). Qed.
Lemma lem1545528 : term19 = term34.
Proof. exact (fun_ext (fun x : real => @lem1545527 x)). Qed.
Lemma lem1545529 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545530 : term20 = term35.
Proof. exact (MK_COMB (@lem1545529) (@lem1545528)). Qed.
Lemma lem1545545 : term12 = term35.
Proof. exact (TRANS (@lem1545505) (@lem1545530)). Qed.
Lemma lem1545546 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1545547 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1545546 x y)). Qed.
Lemma lem1545548 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545549 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1545548) (@lem1545547 x)). Qed.
Lemma lem1545550 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1545549 x)). Qed.
Lemma lem1545551 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1545552 : term35 = term35.
Proof. exact (MK_COMB (@lem1545551) (@lem1545550)). Qed.
Lemma lem1545553 : term12 = term35.
Proof. exact (TRANS (@lem1545545) (@lem1545552)). Qed.
Lemma lem1545555 (a : real) (x : real) (r : real) : (term36 x a r) = (term37 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1545556 (x : real) (y : real) : (term31 x y) = (term38 x y).
Proof. exact (@lem1545555 (term22 x y) (real_sub x y) term30). Qed.
Lemma lem1545569 (x : real) (y : real) : (real_sub x y) = (term39 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1545572 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem1545573 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1545572) (@lem1545569 x y)). Qed.
Lemma lem1545574 (x : real) (y : real) : (term42 x y) = (term39 x y).
Proof. exact (@lem1483460 (term39 x y)). Qed.
Lemma lem1545575 (x : real) (y : real) : (term41 x y) = (term39 x y).
Proof. exact (TRANS (@lem1545573 x y) (@lem1545574 x y)). Qed.
Lemma lem1545578 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1545579 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1545578 x y) (@lem1545575 x y)). Qed.
Lemma lem1545580 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (@lem1483484 x (term22 x y) (term47 y)). Qed.
Lemma lem1545581 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (@lem1483488 (term47 y) (term22 x y)). Qed.
Lemma lem1545582 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1545583 (x : real) (y : real) : (term46 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1545582 x) (@lem1545581 x y)). Qed.
Lemma lem1545584 (x : real) (y : real) : (term45 x y) = (term50 x y).
Proof. exact (TRANS (@lem1545580 x y) (@lem1545583 x y)). Qed.
Lemma lem1545585 (x : real) (y : real) : (term44 x y) = (term50 x y).
Proof. exact (TRANS (@lem1545579 x y) (@lem1545584 x y)). Qed.
Lemma lem1545586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545587 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1545586) (@lem1545585 x y)). Qed.
Lemma lem1545588 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545589 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1545587 x y) (@lem1545588)). Qed.
Lemma lem1545602 (x : real) (y : real) : (real_sub x y) = (term39 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1545605 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem1545606 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1545605) (@lem1545602 x y)). Qed.
Lemma lem1545607 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (@lem1483508 x term59 (term47 y)). Qed.
Lemma lem1545608 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1483476 term59 term59 y). Qed.
Lemma lem1545610 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1545611 : term64 = term65.
Proof. exact (@lem1545610 term66 term66). Qed.
Lemma lem1545612 : (term67 = (BIT1 0)) = (term68 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1545613 : term68 = term66.
Proof. exact (EQ_MP (@lem1545612) (@lem940073)). Qed.
Lemma lem1545614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545615 : term65 = term69.
Proof. exact (MK_COMB (@lem1545614) (@lem1545613)). Qed.
Lemma lem1545616 : term64 = term69.
Proof. exact (TRANS (@lem1545611) (@lem1545615)). Qed.
Lemma lem1545617 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545618 : term70 = term40.
Proof. exact (MK_COMB (@lem1545617) (@lem1545616)). Qed.
Lemma lem1545619 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1545620 (y : real) : (term61 y) = (term71 y).
Proof. exact (MK_COMB (@lem1545618) (@lem1545619 y)). Qed.
Lemma lem1545621 (y : real) : (term60 y) = (term71 y).
Proof. exact (TRANS (@lem1545608 y) (@lem1545620 y)). Qed.
Lemma lem1545622 (y : real) : (term71 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1545623 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem1545621 y) (@lem1545622 y)). Qed.
Lemma lem1545626 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1545627 (x : real) (y : real) : (term58 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1545626 x) (@lem1545623 y)). Qed.
Lemma lem1545628 (x : real) (y : real) : (term57 x y) = (term73 x y).
Proof. exact (TRANS (@lem1545607 x y) (@lem1545627 x y)). Qed.
Lemma lem1545629 (x : real) (y : real) : (term56 x y) = (term73 x y).
Proof. exact (TRANS (@lem1545606 x y) (@lem1545628 x y)). Qed.
Lemma lem1545632 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1545633 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1545632 x y) (@lem1545629 x y)). Qed.
Lemma lem1545634 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (@lem1483484 (term47 x) (term22 x y) y). Qed.
Lemma lem1545635 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (@lem1483488 y (term22 x y)). Qed.
Lemma lem1545636 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1545637 (x : real) (y : real) : (term76 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1545636 x) (@lem1545635 x y)). Qed.
Lemma lem1545638 (x : real) (y : real) : (term75 x y) = (term79 x y).
Proof. exact (TRANS (@lem1545634 x y) (@lem1545637 x y)). Qed.
Lemma lem1545639 (x : real) (y : real) : (term74 x y) = (term79 x y).
Proof. exact (TRANS (@lem1545633 x y) (@lem1545638 x y)). Qed.
Lemma lem1545640 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545641 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1545640) (@lem1545639 x y)). Qed.
Lemma lem1545642 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545643 (x : real) (y : real) : (term82 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1545641 x y) (@lem1545642)). Qed.
Lemma lem1545644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545645 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1545644) (@lem1545643 x y)). Qed.
Lemma lem1545646 (x : real) (y : real) : (term38 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1545645 x y) (@lem1545589 x y)). Qed.
Lemma lem1545647 (x : real) (y : real) : (term31 x y) = (term86 x y).
Proof. exact (TRANS (@lem1545556 x y) (@lem1545646 x y)). Qed.
Lemma lem1545648 (x : real) (y : real) : (term87 x y) = (term86 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1545649 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (SYM (@lem1545648 x y)). Qed.
Lemma lem1545650 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (@lem1482981 (term89 x y) (term90 x y)). Qed.
Lemma lem1545651 (x : real) (y : real) : (term86 x y) = (term88 x y).
Proof. exact (TRANS (@lem1545649 x y) (@lem1545650 x y)). Qed.
Lemma lem1545652 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (eq_refl (term91 x y)). Qed.
Lemma lem1545653 (x : real) (y : real) : (term93 x y) = (term93 x y).
Proof. exact (eq_refl (term93 x y)). Qed.
Lemma lem1545654 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1545653 x y) (@lem1545652 x y)). Qed.
Lemma lem1545655 (x : real) (y : real) : (term96 x y) = (term97 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem1545656 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1545657 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1545656 x y) (@lem1545655 x y)). Qed.
Lemma lem1545658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1545659 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1545658) (@lem1545657 x y)). Qed.
Lemma lem1545660 (x : real) (y : real) : (term88 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1545659 x y) (@lem1545654 x y)). Qed.
Lemma lem1545661 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1545662 (x : real) (y : real) : ((term86 x y) = (term88 x y)) = ((term86 x y) = (term103 x y)).
Proof. exact (MK_COMB (@lem1545661 x y) (@lem1545660 x y)). Qed.
Lemma lem1545663 (x : real) (y : real) : (term86 x y) = (term103 x y).
Proof. exact (EQ_MP (@lem1545662 x y) (@lem1545651 x y)). Qed.
Lemma lem1545664 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (@lem1483527 (term90 x y) term30). Qed.
Lemma lem1545665 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545678 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545679 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545680 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1545679) (@lem1545678 x y)). Qed.
Lemma lem1545681 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1545680 x y) (@lem1545665)). Qed.
Lemma lem1545682 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483519 (term107 x y) term30). Qed.
Lemma lem1545684 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545685 : term114 = term30.
Proof. exact (@lem1545684 term66). Qed.
Lemma lem1545686 (x : real) (y : real) : (term115 x y) = (term115 x y).
Proof. exact (eq_refl (term115 x y)). Qed.
Lemma lem1545687 (x : real) (y : real) : (term112 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1545686 x y) (@lem1545685)). Qed.
Lemma lem1545688 (x : real) (y : real) : (term116 x y) = (term107 x y).
Proof. exact (@lem1483450 (term107 x y)). Qed.
Lemma lem1545689 (x : real) (y : real) : (term112 x y) = (term107 x y).
Proof. exact (TRANS (@lem1545687 x y) (@lem1545688 x y)). Qed.
Lemma lem1545690 (x : real) (y : real) : (term111 x y) = (term107 x y).
Proof. exact (TRANS (@lem1545682 x y) (@lem1545689 x y)). Qed.
Lemma lem1545691 (x : real) (y : real) : (term110 x y) = (term107 x y).
Proof. exact (TRANS (@lem1545681 x y) (@lem1545690 x y)). Qed.
Lemma lem1545692 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1545693 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1545692) (@lem1545691 x y)). Qed.
Lemma lem1545694 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545695 (x : real) (y : real) : (term106 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1545693 x y) (@lem1545694)). Qed.
Lemma lem1545696 (x : real) (y : real) : (term105 x y) = (term119 x y).
Proof. exact (TRANS (@lem1545664 x y) (@lem1545695 x y)). Qed.
Lemma lem1545697 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (@lem1483525 (term122 x y) term30). Qed.
Lemma lem1545698 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545711 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545714 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1545717 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1545714 y) (@lem1545711 x y)). Qed.
Lemma lem1545726 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1545729 (x : real) (y : real) : (term122 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1545726 x) (@lem1545717 x y)). Qed.
Lemma lem1545730 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545731 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1545730) (@lem1545729 x y)). Qed.
Lemma lem1545732 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1545731 x y) (@lem1545698)). Qed.
Lemma lem1545733 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (@lem1483519 (term125 x y) term30). Qed.
Lemma lem1545735 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545736 : term114 = term30.
Proof. exact (@lem1545735 term66). Qed.
Lemma lem1545737 (x : real) (y : real) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1545738 (x : real) (y : real) : (term130 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1545737 x y) (@lem1545736)). Qed.
Lemma lem1545739 (x : real) (y : real) : (term132 x y) = (term125 x y).
Proof. exact (@lem1483450 (term125 x y)). Qed.
Lemma lem1545740 (x : real) (y : real) : (term130 x y) = (term125 x y).
Proof. exact (TRANS (@lem1545738 x y) (@lem1545739 x y)). Qed.
Lemma lem1545741 (x : real) (y : real) : (term129 x y) = (term125 x y).
Proof. exact (TRANS (@lem1545733 x y) (@lem1545740 x y)). Qed.
Lemma lem1545742 (x : real) (y : real) : (term128 x y) = (term125 x y).
Proof. exact (TRANS (@lem1545732 x y) (@lem1545741 x y)). Qed.
Lemma lem1545743 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545744 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1545743) (@lem1545742 x y)). Qed.
Lemma lem1545745 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545746 (x : real) (y : real) : (term121 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1545744 x y) (@lem1545745)). Qed.
Lemma lem1545747 (x : real) (y : real) : (term120 x y) = (term135 x y).
Proof. exact (TRANS (@lem1545697 x y) (@lem1545746 x y)). Qed.
Lemma lem1545748 (x : real) (y : real) : (term136 x y) = (term137 x y).
Proof. exact (@lem1483525 (term138 x y) term30). Qed.
Lemma lem1545749 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545762 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545771 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1545774 (x : real) (y : real) : (term139 x y) = (term140 x y).
Proof. exact (MK_COMB (@lem1545771 y) (@lem1545762 x y)). Qed.
Lemma lem1545777 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1545780 (x : real) (y : real) : (term138 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1545777 x) (@lem1545774 x y)). Qed.
Lemma lem1545781 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545782 (x : real) (y : real) : (term142 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1545781) (@lem1545780 x y)). Qed.
Lemma lem1545783 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1545782 x y) (@lem1545749)). Qed.
Lemma lem1545784 (x : real) (y : real) : (term145 x y) = (term146 x y).
Proof. exact (@lem1483519 (term141 x y) term30). Qed.
Lemma lem1545786 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545787 : term114 = term30.
Proof. exact (@lem1545786 term66). Qed.
Lemma lem1545788 (x : real) (y : real) : (term147 x y) = (term147 x y).
Proof. exact (eq_refl (term147 x y)). Qed.
Lemma lem1545789 (x : real) (y : real) : (term146 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1545788 x y) (@lem1545787)). Qed.
Lemma lem1545790 (x : real) (y : real) : (term148 x y) = (term141 x y).
Proof. exact (@lem1483450 (term141 x y)). Qed.
Lemma lem1545791 (x : real) (y : real) : (term146 x y) = (term141 x y).
Proof. exact (TRANS (@lem1545789 x y) (@lem1545790 x y)). Qed.
Lemma lem1545792 (x : real) (y : real) : (term145 x y) = (term141 x y).
Proof. exact (TRANS (@lem1545784 x y) (@lem1545791 x y)). Qed.
Lemma lem1545793 (x : real) (y : real) : (term144 x y) = (term141 x y).
Proof. exact (TRANS (@lem1545783 x y) (@lem1545792 x y)). Qed.
Lemma lem1545794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545795 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1545794) (@lem1545793 x y)). Qed.
Lemma lem1545796 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545797 (x : real) (y : real) : (term137 x y) = (term151 x y).
Proof. exact (MK_COMB (@lem1545795 x y) (@lem1545796)). Qed.
Lemma lem1545798 (x : real) (y : real) : (term136 x y) = (term151 x y).
Proof. exact (TRANS (@lem1545748 x y) (@lem1545797 x y)). Qed.
Lemma lem1545799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545800 (x : real) (y : real) : (term152 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem1545799) (@lem1545747 x y)). Qed.
Lemma lem1545801 (x : real) (y : real) : (term97 x y) = (term154 x y).
Proof. exact (MK_COMB (@lem1545800 x y) (@lem1545798 x y)). Qed.
Lemma lem1545802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545803 (x : real) (y : real) : (term98 x y) = (term155 x y).
Proof. exact (MK_COMB (@lem1545802) (@lem1545696 x y)). Qed.
Lemma lem1545804 (x : real) (y : real) : (term100 x y) = (term156 x y).
Proof. exact (MK_COMB (@lem1545803 x y) (@lem1545801 x y)). Qed.
Lemma lem1545805 (x : real) (y : real) : (term157 x y) = (term158 x y).
Proof. exact (@lem1483525 term30 (term90 x y)). Qed.
Lemma lem1545818 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545821 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem1545822 (x : real) (y : real) : (term160 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1545821) (@lem1545818 x y)). Qed.
Lemma lem1545823 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem1483519 term30 (term107 x y)). Qed.
Lemma lem1545824 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (@lem1483508 (real_abs x) term59 (term165 y)). Qed.
Lemma lem1545825 (y : real) : (term166 y) = (term167 y).
Proof. exact (@lem1483476 term59 term59 (real_abs y)). Qed.
Lemma lem1545827 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1545828 : term64 = term65.
Proof. exact (@lem1545827 term66 term66). Qed.
Lemma lem1545829 : (term67 = (BIT1 0)) = (term68 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1545830 : term68 = term66.
Proof. exact (EQ_MP (@lem1545829) (@lem940073)). Qed.
Lemma lem1545831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545832 : term65 = term69.
Proof. exact (MK_COMB (@lem1545831) (@lem1545830)). Qed.
Lemma lem1545833 : term64 = term69.
Proof. exact (TRANS (@lem1545828) (@lem1545832)). Qed.
Lemma lem1545834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545835 : term70 = term40.
Proof. exact (MK_COMB (@lem1545834) (@lem1545833)). Qed.
Lemma lem1545836 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1545837 (y : real) : (term167 y) = (term168 y).
Proof. exact (MK_COMB (@lem1545835) (@lem1545836 y)). Qed.
Lemma lem1545838 (y : real) : (term166 y) = (term168 y).
Proof. exact (TRANS (@lem1545825 y) (@lem1545837 y)). Qed.
Lemma lem1545839 (y : real) : (term168 y) = (real_abs y).
Proof. exact (@lem1483436 (real_abs y)). Qed.
Lemma lem1545840 (y : real) : (term166 y) = (real_abs y).
Proof. exact (TRANS (@lem1545838 y) (@lem1545839 y)). Qed.
Lemma lem1545843 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1545844 (x : real) (y : real) : (term164 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1545843 x) (@lem1545840 y)). Qed.
Lemma lem1545845 (x : real) (y : real) : (term163 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545824 x y) (@lem1545844 x y)). Qed.
Lemma lem1545846 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem1545847 (x : real) (y : real) : (term162 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1545846) (@lem1545845 x y)). Qed.
Lemma lem1545848 (x : real) (y : real) : (term172 x y) = (term170 x y).
Proof. exact (@lem1483448 (term170 x y)). Qed.
Lemma lem1545849 (x : real) (y : real) : (term162 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545847 x y) (@lem1545848 x y)). Qed.
Lemma lem1545850 (x : real) (y : real) : (term161 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545823 x y) (@lem1545849 x y)). Qed.
Lemma lem1545851 (x : real) (y : real) : (term160 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545822 x y) (@lem1545850 x y)). Qed.
Lemma lem1545852 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545853 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1545852) (@lem1545851 x y)). Qed.
Lemma lem1545854 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545855 (x : real) (y : real) : (term158 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1545853 x y) (@lem1545854)). Qed.
Lemma lem1545856 (x : real) (y : real) : (term157 x y) = (term175 x y).
Proof. exact (TRANS (@lem1545805 x y) (@lem1545855 x y)). Qed.
Lemma lem1545857 (x : real) (y : real) : (term176 x y) = (term177 x y).
Proof. exact (@lem1483525 (term178 x y) term30). Qed.
Lemma lem1545858 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545871 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545872 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1545873 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1545872) (@lem1545871 x y)). Qed.
Lemma lem1545874 (x : real) (y : real) : (term180 x y) = (term163 x y).
Proof. exact (@lem1483512 (term107 x y)). Qed.
Lemma lem1545875 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (@lem1483508 (real_abs x) term59 (term165 y)). Qed.
Lemma lem1545876 (y : real) : (term166 y) = (term167 y).
Proof. exact (@lem1483476 term59 term59 (real_abs y)). Qed.
Lemma lem1545878 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1545879 : term64 = term65.
Proof. exact (@lem1545878 term66 term66). Qed.
Lemma lem1545880 : (term67 = (BIT1 0)) = (term68 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1545881 : term68 = term66.
Proof. exact (EQ_MP (@lem1545880) (@lem940073)). Qed.
Lemma lem1545882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545883 : term65 = term69.
Proof. exact (MK_COMB (@lem1545882) (@lem1545881)). Qed.
Lemma lem1545884 : term64 = term69.
Proof. exact (TRANS (@lem1545879) (@lem1545883)). Qed.
Lemma lem1545885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545886 : term70 = term40.
Proof. exact (MK_COMB (@lem1545885) (@lem1545884)). Qed.
Lemma lem1545887 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1545888 (y : real) : (term167 y) = (term168 y).
Proof. exact (MK_COMB (@lem1545886) (@lem1545887 y)). Qed.
Lemma lem1545889 (y : real) : (term166 y) = (term168 y).
Proof. exact (TRANS (@lem1545876 y) (@lem1545888 y)). Qed.
Lemma lem1545890 (y : real) : (term168 y) = (real_abs y).
Proof. exact (@lem1483436 (real_abs y)). Qed.
Lemma lem1545891 (y : real) : (term166 y) = (real_abs y).
Proof. exact (TRANS (@lem1545889 y) (@lem1545890 y)). Qed.
Lemma lem1545894 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1545895 (x : real) (y : real) : (term164 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1545894 x) (@lem1545891 y)). Qed.
Lemma lem1545896 (x : real) (y : real) : (term163 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545875 x y) (@lem1545895 x y)). Qed.
Lemma lem1545897 (x : real) (y : real) : (term180 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545874 x y) (@lem1545896 x y)). Qed.
Lemma lem1545898 (x : real) (y : real) : (term179 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545873 x y) (@lem1545897 x y)). Qed.
Lemma lem1545901 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1545904 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1545901 y) (@lem1545898 x y)). Qed.
Lemma lem1545913 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1545916 (x : real) (y : real) : (term178 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1545913 x) (@lem1545904 x y)). Qed.
Lemma lem1545917 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545918 (x : real) (y : real) : (term184 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1545917) (@lem1545916 x y)). Qed.
Lemma lem1545919 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1545918 x y) (@lem1545858)). Qed.
Lemma lem1545920 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (@lem1483519 (term183 x y) term30). Qed.
Lemma lem1545922 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545923 : term114 = term30.
Proof. exact (@lem1545922 term66). Qed.
Lemma lem1545924 (x : real) (y : real) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem1545925 (x : real) (y : real) : (term188 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1545924 x y) (@lem1545923)). Qed.
Lemma lem1545926 (x : real) (y : real) : (term190 x y) = (term183 x y).
Proof. exact (@lem1483450 (term183 x y)). Qed.
Lemma lem1545927 (x : real) (y : real) : (term188 x y) = (term183 x y).
Proof. exact (TRANS (@lem1545925 x y) (@lem1545926 x y)). Qed.
Lemma lem1545928 (x : real) (y : real) : (term187 x y) = (term183 x y).
Proof. exact (TRANS (@lem1545920 x y) (@lem1545927 x y)). Qed.
Lemma lem1545929 (x : real) (y : real) : (term186 x y) = (term183 x y).
Proof. exact (TRANS (@lem1545919 x y) (@lem1545928 x y)). Qed.
Lemma lem1545930 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545931 (x : real) (y : real) : (term191 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1545930) (@lem1545929 x y)). Qed.
Lemma lem1545932 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545933 (x : real) (y : real) : (term177 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1545931 x y) (@lem1545932)). Qed.
Lemma lem1545934 (x : real) (y : real) : (term176 x y) = (term193 x y).
Proof. exact (TRANS (@lem1545857 x y) (@lem1545933 x y)). Qed.
Lemma lem1545935 (x : real) (y : real) : (term194 x y) = (term195 x y).
Proof. exact (@lem1483525 (term196 x y) term30). Qed.
Lemma lem1545936 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1545949 (x : real) (y : real) : (term90 x y) = (term107 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1545950 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1545951 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1545950) (@lem1545949 x y)). Qed.
Lemma lem1545952 (x : real) (y : real) : (term180 x y) = (term163 x y).
Proof. exact (@lem1483512 (term107 x y)). Qed.
Lemma lem1545953 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (@lem1483508 (real_abs x) term59 (term165 y)). Qed.
Lemma lem1545954 (y : real) : (term166 y) = (term167 y).
Proof. exact (@lem1483476 term59 term59 (real_abs y)). Qed.
Lemma lem1545956 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1545957 : term64 = term65.
Proof. exact (@lem1545956 term66 term66). Qed.
Lemma lem1545958 : (term67 = (BIT1 0)) = (term68 = term66).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1545959 : term68 = term66.
Proof. exact (EQ_MP (@lem1545958) (@lem940073)). Qed.
Lemma lem1545960 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545961 : term65 = term69.
Proof. exact (MK_COMB (@lem1545960) (@lem1545959)). Qed.
Lemma lem1545962 : term64 = term69.
Proof. exact (TRANS (@lem1545957) (@lem1545961)). Qed.
Lemma lem1545963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545964 : term70 = term40.
Proof. exact (MK_COMB (@lem1545963) (@lem1545962)). Qed.
Lemma lem1545965 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1545966 (y : real) : (term167 y) = (term168 y).
Proof. exact (MK_COMB (@lem1545964) (@lem1545965 y)). Qed.
Lemma lem1545967 (y : real) : (term166 y) = (term168 y).
Proof. exact (TRANS (@lem1545954 y) (@lem1545966 y)). Qed.
Lemma lem1545968 (y : real) : (term168 y) = (real_abs y).
Proof. exact (@lem1483436 (real_abs y)). Qed.
Lemma lem1545969 (y : real) : (term166 y) = (real_abs y).
Proof. exact (TRANS (@lem1545967 y) (@lem1545968 y)). Qed.
Lemma lem1545972 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1545973 (x : real) (y : real) : (term164 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1545972 x) (@lem1545969 y)). Qed.
Lemma lem1545974 (x : real) (y : real) : (term163 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545953 x y) (@lem1545973 x y)). Qed.
Lemma lem1545975 (x : real) (y : real) : (term180 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545952 x y) (@lem1545974 x y)). Qed.
Lemma lem1545976 (x : real) (y : real) : (term179 x y) = (term170 x y).
Proof. exact (TRANS (@lem1545951 x y) (@lem1545975 x y)). Qed.
Lemma lem1545985 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1545988 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (MK_COMB (@lem1545985 y) (@lem1545976 x y)). Qed.
Lemma lem1545991 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1545994 (x : real) (y : real) : (term196 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem1545991 x) (@lem1545988 x y)). Qed.
Lemma lem1545995 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545996 (x : real) (y : real) : (term200 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1545995) (@lem1545994 x y)). Qed.
Lemma lem1545997 (x : real) (y : real) : (term202 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1545996 x y) (@lem1545936)). Qed.
Lemma lem1545998 (x : real) (y : real) : (term203 x y) = (term204 x y).
Proof. exact (@lem1483519 (term199 x y) term30). Qed.
Lemma lem1546000 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546001 : term114 = term30.
Proof. exact (@lem1546000 term66). Qed.
Lemma lem1546002 (x : real) (y : real) : (term205 x y) = (term205 x y).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem1546003 (x : real) (y : real) : (term204 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1546002 x y) (@lem1546001)). Qed.
Lemma lem1546004 (x : real) (y : real) : (term206 x y) = (term199 x y).
Proof. exact (@lem1483450 (term199 x y)). Qed.
Lemma lem1546005 (x : real) (y : real) : (term204 x y) = (term199 x y).
Proof. exact (TRANS (@lem1546003 x y) (@lem1546004 x y)). Qed.
Lemma lem1546006 (x : real) (y : real) : (term203 x y) = (term199 x y).
Proof. exact (TRANS (@lem1545998 x y) (@lem1546005 x y)). Qed.
Lemma lem1546007 (x : real) (y : real) : (term202 x y) = (term199 x y).
Proof. exact (TRANS (@lem1545997 x y) (@lem1546006 x y)). Qed.
Lemma lem1546008 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546009 (x : real) (y : real) : (term207 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem1546008) (@lem1546007 x y)). Qed.
Lemma lem1546010 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546011 (x : real) (y : real) : (term195 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1546009 x y) (@lem1546010)). Qed.
Lemma lem1546012 (x : real) (y : real) : (term194 x y) = (term209 x y).
Proof. exact (TRANS (@lem1545935 x y) (@lem1546011 x y)). Qed.
Lemma lem1546013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546014 (x : real) (y : real) : (term210 x y) = (term211 x y).
Proof. exact (MK_COMB (@lem1546013) (@lem1545934 x y)). Qed.
Lemma lem1546015 (x : real) (y : real) : (term92 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem1546014 x y) (@lem1546012 x y)). Qed.
Lemma lem1546016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546017 (x : real) (y : real) : (term93 x y) = (term213 x y).
Proof. exact (MK_COMB (@lem1546016) (@lem1545856 x y)). Qed.
Lemma lem1546018 (x : real) (y : real) : (term95 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1546017 x y) (@lem1546015 x y)). Qed.
Lemma lem1546019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1546020 (x : real) (y : real) : (term102 x y) = (term215 x y).
Proof. exact (MK_COMB (@lem1546019) (@lem1545804 x y)). Qed.
Lemma lem1546021 (x : real) (y : real) : (term103 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem1546020 x y) (@lem1546018 x y)). Qed.
Lemma lem1546022 (x : real) (y : real) : (term86 x y) = (term216 x y).
Proof. exact (TRANS (@lem1545663 x y) (@lem1546021 x y)). Qed.
Lemma lem1546024 (a : real) (x : real) (r : real) : (term36 x a r) = (term37 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1546025 (y : real) (x : real) : (term175 x y) = (term217 y x).
Proof. exact (@lem1546024 (real_abs y) x term30). Qed.
Lemma lem1546032 (x : real) : (term71 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1546035 (y : real) : (term218 y) = (term218 y).
Proof. exact (eq_refl (term218 y)). Qed.
Lemma lem1546036 (y : real) (x : real) : (term219 y x) = (term220 y x).
Proof. exact (MK_COMB (@lem1546035 y) (@lem1546032 x)). Qed.
Lemma lem1546037 (x : real) (y : real) : (term220 y x) = (term221 x y).
Proof. exact (@lem1483488 x (real_abs y)). Qed.
Lemma lem1546038 (x : real) (y : real) : (term219 y x) = (term221 x y).
Proof. exact (TRANS (@lem1546036 y x) (@lem1546037 x y)). Qed.
Lemma lem1546039 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546040 (x : real) (y : real) : (term222 y x) = (term223 x y).
Proof. exact (MK_COMB (@lem1546039) (@lem1546038 x y)). Qed.
Lemma lem1546041 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546042 (x : real) (y : real) : (term224 y x) = (term225 x y).
Proof. exact (MK_COMB (@lem1546040 x y) (@lem1546041)). Qed.
Lemma lem1546055 (x : real) (y : real) : (term226 y x) = (term227 x y).
Proof. exact (@lem1483488 (term47 x) (real_abs y)). Qed.
Lemma lem1546056 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546057 (x : real) (y : real) : (term228 y x) = (term229 x y).
Proof. exact (MK_COMB (@lem1546056) (@lem1546055 x y)). Qed.
Lemma lem1546058 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546059 (x : real) (y : real) : (term230 y x) = (term231 x y).
Proof. exact (MK_COMB (@lem1546057 x y) (@lem1546058)). Qed.
Lemma lem1546060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546061 (x : real) (y : real) : (term232 y x) = (term233 x y).
Proof. exact (MK_COMB (@lem1546060) (@lem1546059 x y)). Qed.
Lemma lem1546062 (x : real) (y : real) : (term217 y x) = (term234 x y).
Proof. exact (MK_COMB (@lem1546061 x y) (@lem1546042 x y)). Qed.
Lemma lem1546063 (x : real) (y : real) : (term175 x y) = (term234 x y).
Proof. exact (TRANS (@lem1546025 y x) (@lem1546062 x y)). Qed.
Lemma lem1546064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546065 (x : real) (y : real) : (term213 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1546064) (@lem1546063 x y)). Qed.
Lemma lem1546067 (a : real) (b : real) (x : real) (c : real) (r : real) : (term236 a b x c r) = (term237 a b x c r).
Proof. exact (proj1 (@lem1482707 x a b (@el real) c r)). Qed.
Lemma lem1546068 (x : real) (y : real) : (term193 x y) = (term238 x y).
Proof. exact (@lem1546067 (term47 x) y x (real_abs y) term30). Qed.
Lemma lem1546069 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1546076 (x : real) : (term71 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1546077 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546078 (x : real) : (term239 x) = (real_add x).
Proof. exact (MK_COMB (@lem1546077) (@lem1546076 x)). Qed.
Lemma lem1546081 (x : real) (y : real) : (term240 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1546078 x) (@lem1546069 y)). Qed.
Lemma lem1546084 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1546085 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1546084 y) (@lem1546081 x y)). Qed.
Lemma lem1546090 (x : real) (y : real) : (term242 x y) = (term243 x y).
Proof. exact (@lem1483484 x y (real_abs y)). Qed.
Lemma lem1546091 (x : real) (y : real) : (term241 x y) = (term243 x y).
Proof. exact (TRANS (@lem1546085 x y) (@lem1546090 x y)). Qed.
Lemma lem1546100 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1546101 (x : real) (y : real) : (term244 x y) = (term245 x y).
Proof. exact (MK_COMB (@lem1546100 x) (@lem1546091 x y)). Qed.
Lemma lem1546102 (x : real) (y : real) : (term245 x y) = (term246 x y).
Proof. exact (@lem1483490 (term47 x) x (term247 y)). Qed.
Lemma lem1546103 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem1483440 term59 x). Qed.
Lemma lem1546105 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546106 : term251 = term30.
Proof. exact (@lem1546105 term66). Qed.
Lemma lem1546107 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546108 : term252 = term253.
Proof. exact (MK_COMB (@lem1546107) (@lem1546106)). Qed.
Lemma lem1546109 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1546110 (x : real) : (term249 x) = (term254 x).
Proof. exact (MK_COMB (@lem1546108) (@lem1546109 x)). Qed.
Lemma lem1546111 (x : real) : (term248 x) = (term254 x).
Proof. exact (TRANS (@lem1546103 x) (@lem1546110 x)). Qed.
Lemma lem1546112 (x : real) : (term254 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1546113 (x : real) : (term248 x) = term30.
Proof. exact (TRANS (@lem1546111 x) (@lem1546112 x)). Qed.
Lemma lem1546114 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546115 (x : real) : (term255 x) = term171.
Proof. exact (MK_COMB (@lem1546114) (@lem1546113 x)). Qed.
Lemma lem1546116 (y : real) : (term247 y) = (term247 y).
Proof. exact (eq_refl (term247 y)). Qed.
Lemma lem1546117 (x : real) (y : real) : (term246 x y) = (term256 y).
Proof. exact (MK_COMB (@lem1546115 x) (@lem1546116 y)). Qed.
Lemma lem1546118 (x : real) (y : real) : (term245 x y) = (term256 y).
Proof. exact (TRANS (@lem1546102 x y) (@lem1546117 x y)). Qed.
Lemma lem1546119 (y : real) : (term256 y) = (term247 y).
Proof. exact (@lem1483448 (term247 y)). Qed.
Lemma lem1546120 (x : real) (y : real) : (term245 x y) = (term247 y).
Proof. exact (TRANS (@lem1546118 x y) (@lem1546119 y)). Qed.
Lemma lem1546121 (x : real) (y : real) : (term244 x y) = (term247 y).
Proof. exact (TRANS (@lem1546101 x y) (@lem1546120 x y)). Qed.
Lemma lem1546122 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546123 (x : real) (y : real) : (term257 x y) = (term258 y).
Proof. exact (MK_COMB (@lem1546122) (@lem1546121 x y)). Qed.
Lemma lem1546124 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546125 (x : real) (y : real) : (term259 x y) = (term260 y).
Proof. exact (MK_COMB (@lem1546123 x y) (@lem1546124)). Qed.
Lemma lem1546148 (x : real) (y : real) : (term261 x y) = (term262 x y).
Proof. exact (@lem1483484 (term47 x) y (real_abs y)). Qed.
Lemma lem1546157 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1546158 (x : real) (y : real) : (term263 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem1546157 x) (@lem1546148 x y)). Qed.
Lemma lem1546159 (x : real) (y : real) : (term264 x y) = (term265 x y).
Proof. exact (@lem1483490 (term47 x) (term47 x) (term247 y)). Qed.
Lemma lem1546160 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483438 term59 term59 x). Qed.
Lemma lem1546161 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1546162 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546163 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546164 : term272 = term273.
Proof. exact (EQ_MP (@lem1546163) (@lem1546162)). Qed.
Lemma lem1546165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546166 : term274 = term275.
Proof. exact (MK_COMB (@lem1546165) (@lem1546164)). Qed.
Lemma lem1546167 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1546168 : term269 = term276.
Proof. exact (MK_COMB (@lem1546167) (@lem1546166)). Qed.
Lemma lem1546169 : term268 = term276.
Proof. exact (TRANS (@lem1546161) (@lem1546168)). Qed.
Lemma lem1546170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546171 : term277 = term278.
Proof. exact (MK_COMB (@lem1546170) (@lem1546169)). Qed.
Lemma lem1546172 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1546173 (x : real) : (term267 x) = (term279 x).
Proof. exact (MK_COMB (@lem1546171) (@lem1546172 x)). Qed.
Lemma lem1546174 (x : real) : (term266 x) = (term279 x).
Proof. exact (TRANS (@lem1546160 x) (@lem1546173 x)). Qed.
Lemma lem1546175 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546176 (x : real) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem1546175) (@lem1546174 x)). Qed.
Lemma lem1546177 (y : real) : (term247 y) = (term247 y).
Proof. exact (eq_refl (term247 y)). Qed.
Lemma lem1546178 (x : real) (y : real) : (term265 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1546176 x) (@lem1546177 y)). Qed.
Lemma lem1546179 (x : real) (y : real) : (term264 x y) = (term282 x y).
Proof. exact (TRANS (@lem1546159 x y) (@lem1546178 x y)). Qed.
Lemma lem1546180 (x : real) (y : real) : (term263 x y) = (term282 x y).
Proof. exact (TRANS (@lem1546158 x y) (@lem1546179 x y)). Qed.
Lemma lem1546181 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546182 (x : real) (y : real) : (term283 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1546181) (@lem1546180 x y)). Qed.
Lemma lem1546183 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546184 (x : real) (y : real) : (term285 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1546182 x y) (@lem1546183)). Qed.
Lemma lem1546185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546186 (x : real) (y : real) : (term287 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem1546185) (@lem1546184 x y)). Qed.
Lemma lem1546187 (x : real) (y : real) : (term238 x y) = (term289 x y).
Proof. exact (MK_COMB (@lem1546186 x y) (@lem1546125 x y)). Qed.
Lemma lem1546188 (x : real) (y : real) : (term193 x y) = (term289 x y).
Proof. exact (TRANS (@lem1546068 x y) (@lem1546187 x y)). Qed.
Lemma lem1546189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546190 (x : real) (y : real) : (term211 x y) = (term290 x y).
Proof. exact (MK_COMB (@lem1546189) (@lem1546188 x y)). Qed.
Lemma lem1546192 (a : real) (b : real) (x : real) (c : real) (r : real) : (term236 a b x c r) = (term237 a b x c r).
Proof. exact (proj1 (@lem1482707 x a b (@el real) c r)). Qed.
Lemma lem1546193 (x : real) (y : real) : (term209 x y) = (term291 x y).
Proof. exact (@lem1546192 x (term47 y) x (real_abs y) term30). Qed.
Lemma lem1546194 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1546201 (x : real) : (term71 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1546202 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546203 (x : real) : (term239 x) = (real_add x).
Proof. exact (MK_COMB (@lem1546202) (@lem1546201 x)). Qed.
Lemma lem1546206 (x : real) (y : real) : (term240 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1546203 x) (@lem1546194 y)). Qed.
Lemma lem1546215 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1546216 (x : real) (y : real) : (term292 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem1546215 y) (@lem1546206 x y)). Qed.
Lemma lem1546221 (x : real) (y : real) : (term293 x y) = (term294 x y).
Proof. exact (@lem1483484 x (term47 y) (real_abs y)). Qed.
Lemma lem1546222 (x : real) (y : real) : (term292 x y) = (term294 x y).
Proof. exact (TRANS (@lem1546216 x y) (@lem1546221 x y)). Qed.
Lemma lem1546225 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1546226 (x : real) (y : real) : (term295 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1546225 x) (@lem1546222 x y)). Qed.
Lemma lem1546227 (x : real) (y : real) : (term296 x y) = (term297 x y).
Proof. exact (@lem1483490 x x (term298 y)). Qed.
Lemma lem1546228 (x : real) : (real_add x x) = (term299 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1546229 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1546230 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546231 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546232 : term272 = term273.
Proof. exact (EQ_MP (@lem1546231) (@lem1546230)). Qed.
Lemma lem1546233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546234 : term274 = term275.
Proof. exact (MK_COMB (@lem1546233) (@lem1546232)). Qed.
Lemma lem1546235 : term300 = term275.
Proof. exact (TRANS (@lem1546229) (@lem1546234)). Qed.
Lemma lem1546236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546237 : term301 = term302.
Proof. exact (MK_COMB (@lem1546236) (@lem1546235)). Qed.
Lemma lem1546238 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1546239 (x : real) : (term299 x) = (term303 x).
Proof. exact (MK_COMB (@lem1546237) (@lem1546238 x)). Qed.
Lemma lem1546240 (x : real) : (real_add x x) = (term303 x).
Proof. exact (TRANS (@lem1546228 x) (@lem1546239 x)). Qed.
Lemma lem1546241 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546242 (x : real) : (term304 x) = (term305 x).
Proof. exact (MK_COMB (@lem1546241) (@lem1546240 x)). Qed.
Lemma lem1546243 (y : real) : (term298 y) = (term298 y).
Proof. exact (eq_refl (term298 y)). Qed.
Lemma lem1546244 (x : real) (y : real) : (term297 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem1546242 x) (@lem1546243 y)). Qed.
Lemma lem1546245 (x : real) (y : real) : (term296 x y) = (term306 x y).
Proof. exact (TRANS (@lem1546227 x y) (@lem1546244 x y)). Qed.
Lemma lem1546246 (x : real) (y : real) : (term295 x y) = (term306 x y).
Proof. exact (TRANS (@lem1546226 x y) (@lem1546245 x y)). Qed.
Lemma lem1546247 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546248 (x : real) (y : real) : (term307 x y) = (term308 x y).
Proof. exact (MK_COMB (@lem1546247) (@lem1546246 x y)). Qed.
Lemma lem1546249 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546250 (x : real) (y : real) : (term309 x y) = (term310 x y).
Proof. exact (MK_COMB (@lem1546248 x y) (@lem1546249)). Qed.
Lemma lem1546279 (x : real) (y : real) : (term311 x y) = (term312 x y).
Proof. exact (@lem1483484 (term47 x) (term47 y) (real_abs y)). Qed.
Lemma lem1546282 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1546283 (x : real) (y : real) : (term313 x y) = (term314 x y).
Proof. exact (MK_COMB (@lem1546282 x) (@lem1546279 x y)). Qed.
Lemma lem1546284 (x : real) (y : real) : (term314 x y) = (term315 x y).
Proof. exact (@lem1483490 x (term47 x) (term298 y)). Qed.
Lemma lem1546285 (x : real) : (term316 x) = (term249 x).
Proof. exact (@lem1483442 term59 x). Qed.
Lemma lem1546287 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546288 : term251 = term30.
Proof. exact (@lem1546287 term66). Qed.
Lemma lem1546289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546290 : term252 = term253.
Proof. exact (MK_COMB (@lem1546289) (@lem1546288)). Qed.
Lemma lem1546291 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1546292 (x : real) : (term249 x) = (term254 x).
Proof. exact (MK_COMB (@lem1546290) (@lem1546291 x)). Qed.
Lemma lem1546293 (x : real) : (term316 x) = (term254 x).
Proof. exact (TRANS (@lem1546285 x) (@lem1546292 x)). Qed.
Lemma lem1546294 (x : real) : (term254 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1546295 (x : real) : (term316 x) = term30.
Proof. exact (TRANS (@lem1546293 x) (@lem1546294 x)). Qed.
Lemma lem1546296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1546297 (x : real) : (term317 x) = term171.
Proof. exact (MK_COMB (@lem1546296) (@lem1546295 x)). Qed.
Lemma lem1546298 (y : real) : (term298 y) = (term298 y).
Proof. exact (eq_refl (term298 y)). Qed.
Lemma lem1546299 (x : real) (y : real) : (term315 x y) = (term318 y).
Proof. exact (MK_COMB (@lem1546297 x) (@lem1546298 y)). Qed.
Lemma lem1546300 (x : real) (y : real) : (term314 x y) = (term318 y).
Proof. exact (TRANS (@lem1546284 x y) (@lem1546299 x y)). Qed.
Lemma lem1546301 (y : real) : (term318 y) = (term298 y).
Proof. exact (@lem1483448 (term298 y)). Qed.
Lemma lem1546302 (x : real) (y : real) : (term314 x y) = (term298 y).
Proof. exact (TRANS (@lem1546300 x y) (@lem1546301 y)). Qed.
Lemma lem1546303 (x : real) (y : real) : (term313 x y) = (term298 y).
Proof. exact (TRANS (@lem1546283 x y) (@lem1546302 x y)). Qed.
Lemma lem1546304 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546305 (x : real) (y : real) : (term319 x y) = (term320 y).
Proof. exact (MK_COMB (@lem1546304) (@lem1546303 x y)). Qed.
Lemma lem1546306 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546307 (x : real) (y : real) : (term321 x y) = (term322 y).
Proof. exact (MK_COMB (@lem1546305 x y) (@lem1546306)). Qed.
Lemma lem1546308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546309 (x : real) (y : real) : (term323 x y) = (term324 y).
Proof. exact (MK_COMB (@lem1546308) (@lem1546307 x y)). Qed.
Lemma lem1546310 (x : real) (y : real) : (term291 x y) = (term325 x y).
Proof. exact (MK_COMB (@lem1546309 x y) (@lem1546250 x y)). Qed.
Lemma lem1546311 (x : real) (y : real) : (term209 x y) = (term325 x y).
Proof. exact (TRANS (@lem1546193 x y) (@lem1546310 x y)). Qed.
Lemma lem1546312 (x : real) (y : real) : (term212 x y) = (term326 x y).
Proof. exact (MK_COMB (@lem1546190 x y) (@lem1546311 x y)). Qed.
Lemma lem1546313 (x : real) (y : real) : (term214 x y) = (term327 x y).
Proof. exact (MK_COMB (@lem1546065 x y) (@lem1546312 x y)). Qed.
Lemma lem1546314 (x : real) (y : real) : (term328 x y) = (term327 x y).
Proof. exact (eq_refl (term328 x y)). Qed.
Lemma lem1546315 (x : real) (y : real) : (term327 x y) = (term328 x y).
Proof. exact (SYM (@lem1546314 x y)). Qed.
Lemma lem1546316 (x : real) (y : real) : (term328 x y) = (term329 x y).
Proof. exact (@lem1482981 (term330 x y) y). Qed.
Lemma lem1546317 (x : real) (y : real) : (term327 x y) = (term329 x y).
Proof. exact (TRANS (@lem1546315 x y) (@lem1546316 x y)). Qed.
Lemma lem1546318 (x : real) (y : real) : (term331 x y) = (term332 x y).
Proof. exact (eq_refl (term331 x y)). Qed.
Lemma lem1546319 (y : real) : (term333 y) = (term333 y).
Proof. exact (eq_refl (term333 y)). Qed.
Lemma lem1546320 (x : real) (y : real) : (term334 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem1546319 y) (@lem1546318 x y)). Qed.
Lemma lem1546321 (x : real) (y : real) : (term336 x y) = (term337 x y).
Proof. exact (eq_refl (term336 x y)). Qed.
Lemma lem1546322 (y : real) : (term338 y) = (term338 y).
Proof. exact (eq_refl (term338 y)). Qed.
Lemma lem1546323 (x : real) (y : real) : (term339 x y) = (term340 x y).
Proof. exact (MK_COMB (@lem1546322 y) (@lem1546321 x y)). Qed.
Lemma lem1546324 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1546325 (x : real) (y : real) : (term341 x y) = (term342 x y).
Proof. exact (MK_COMB (@lem1546324) (@lem1546323 x y)). Qed.
Lemma lem1546326 (x : real) (y : real) : (term329 x y) = (term343 x y).
Proof. exact (MK_COMB (@lem1546325 x y) (@lem1546320 x y)). Qed.
Lemma lem1546327 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1546328 (x : real) (y : real) : ((term327 x y) = (term329 x y)) = ((term327 x y) = (term343 x y)).
Proof. exact (MK_COMB (@lem1546327 x y) (@lem1546326 x y)). Qed.
Lemma lem1546329 (x : real) (y : real) : (term327 x y) = (term343 x y).
Proof. exact (EQ_MP (@lem1546328 x y) (@lem1546317 x y)). Qed.
Lemma lem1546330 (y : real) : (term345 y) = (term346 y).
Proof. exact (@lem1483527 y term30). Qed.
Lemma lem1546336 (y : real) : (term347 y) = (term348 y).
Proof. exact (@lem1483519 y term30). Qed.
Lemma lem1546338 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546339 : term114 = term30.
Proof. exact (@lem1546338 term66). Qed.
Lemma lem1546340 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1546341 (y : real) : (term348 y) = (term349 y).
Proof. exact (MK_COMB (@lem1546340 y) (@lem1546339)). Qed.
Lemma lem1546342 (y : real) : (term349 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1546343 (y : real) : (term348 y) = y.
Proof. exact (TRANS (@lem1546341 y) (@lem1546342 y)). Qed.
Lemma lem1546345 (y : real) : (term347 y) = y.
Proof. exact (TRANS (@lem1546336 y) (@lem1546343 y)). Qed.
Lemma lem1546346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1546347 (y : real) : (term350 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1546346) (@lem1546345 y)). Qed.
Lemma lem1546348 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546349 (y : real) : (term346 y) = (term345 y).
Proof. exact (MK_COMB (@lem1546347 y) (@lem1546348)). Qed.
Lemma lem1546350 (y : real) : (term345 y) = (term345 y).
Proof. exact (TRANS (@lem1546330 y) (@lem1546349 y)). Qed.
Lemma lem1546351 (x : real) (y : real) : (term351 x y) = (term352 x y).
Proof. exact (@lem1483525 (term73 x y) term30). Qed.
Lemma lem1546369 (x : real) (y : real) : (term353 x y) = (term354 x y).
Proof. exact (@lem1483519 (term73 x y) term30). Qed.
Lemma lem1546371 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546372 : term114 = term30.
Proof. exact (@lem1546371 term66). Qed.
Lemma lem1546373 (x : real) (y : real) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem1546374 (x : real) (y : real) : (term354 x y) = (term356 x y).
Proof. exact (MK_COMB (@lem1546373 x y) (@lem1546372)). Qed.
Lemma lem1546375 (x : real) (y : real) : (term356 x y) = (term73 x y).
Proof. exact (@lem1483450 (term73 x y)). Qed.
Lemma lem1546376 (x : real) (y : real) : (term354 x y) = (term73 x y).
Proof. exact (TRANS (@lem1546374 x y) (@lem1546375 x y)). Qed.
Lemma lem1546378 (x : real) (y : real) : (term353 x y) = (term73 x y).
Proof. exact (TRANS (@lem1546369 x y) (@lem1546376 x y)). Qed.
Lemma lem1546379 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546380 (x : real) (y : real) : (term357 x y) = (term358 x y).
Proof. exact (MK_COMB (@lem1546379) (@lem1546378 x y)). Qed.
Lemma lem1546381 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546382 (x : real) (y : real) : (term352 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem1546380 x y) (@lem1546381)). Qed.
Lemma lem1546383 (x : real) (y : real) : (term351 x y) = (term351 x y).
Proof. exact (TRANS (@lem1546351 x y) (@lem1546382 x y)). Qed.
Lemma lem1546384 (x : real) (y : real) : (term359 x y) = (term360 x y).
Proof. exact (@lem1483525 (real_add x y) term30). Qed.
Lemma lem1546396 (x : real) (y : real) : (term361 x y) = (term362 x y).
Proof. exact (@lem1483519 (real_add x y) term30). Qed.
Lemma lem1546398 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546399 : term114 = term30.
Proof. exact (@lem1546398 term66). Qed.
Lemma lem1546400 (x : real) (y : real) : (term363 x y) = (term363 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem1546401 (x : real) (y : real) : (term362 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem1546400 x y) (@lem1546399)). Qed.
Lemma lem1546402 (x : real) (y : real) : (term364 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1546403 (x : real) (y : real) : (term362 x y) = (real_add x y).
Proof. exact (TRANS (@lem1546401 x y) (@lem1546402 x y)). Qed.
Lemma lem1546405 (x : real) (y : real) : (term361 x y) = (real_add x y).
Proof. exact (TRANS (@lem1546396 x y) (@lem1546403 x y)). Qed.
Lemma lem1546406 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546407 (x : real) (y : real) : (term365 x y) = (term366 x y).
Proof. exact (MK_COMB (@lem1546406) (@lem1546405 x y)). Qed.
Lemma lem1546408 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546409 (x : real) (y : real) : (term360 x y) = (term359 x y).
Proof. exact (MK_COMB (@lem1546407 x y) (@lem1546408)). Qed.
Lemma lem1546410 (x : real) (y : real) : (term359 x y) = (term359 x y).
Proof. exact (TRANS (@lem1546384 x y) (@lem1546409 x y)). Qed.
Lemma lem1546411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546412 (x : real) (y : real) : (term367 x y) = (term367 x y).
Proof. exact (MK_COMB (@lem1546411) (@lem1546383 x y)). Qed.
Lemma lem1546413 (x : real) (y : real) : (term368 x y) = (term368 x y).
Proof. exact (MK_COMB (@lem1546412 x y) (@lem1546410 x y)). Qed.
Lemma lem1546414 (x : real) (y : real) : (term369 x y) = (term370 x y).
Proof. exact (@lem1483525 (term371 x y) term30). Qed.
Lemma lem1546415 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546421 (y : real) : (real_add y y) = (term299 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1546422 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1546423 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546424 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546425 : term272 = term273.
Proof. exact (EQ_MP (@lem1546424) (@lem1546423)). Qed.
Lemma lem1546426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546427 : term274 = term275.
Proof. exact (MK_COMB (@lem1546426) (@lem1546425)). Qed.
Lemma lem1546428 : term300 = term275.
Proof. exact (TRANS (@lem1546422) (@lem1546427)). Qed.
Lemma lem1546429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546430 : term301 = term302.
Proof. exact (MK_COMB (@lem1546429) (@lem1546428)). Qed.
Lemma lem1546431 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546432 (y : real) : (term299 y) = (term303 y).
Proof. exact (MK_COMB (@lem1546430) (@lem1546431 y)). Qed.
Lemma lem1546434 (y : real) : (real_add y y) = (term303 y).
Proof. exact (TRANS (@lem1546421 y) (@lem1546432 y)). Qed.
Lemma lem1546443 (x : real) : (term281 x) = (term281 x).
Proof. exact (eq_refl (term281 x)). Qed.
Lemma lem1546446 (x : real) (y : real) : (term371 x y) = (term372 x y).
Proof. exact (MK_COMB (@lem1546443 x) (@lem1546434 y)). Qed.
Lemma lem1546447 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546448 (x : real) (y : real) : (term373 x y) = (term374 x y).
Proof. exact (MK_COMB (@lem1546447) (@lem1546446 x y)). Qed.
Lemma lem1546449 (x : real) (y : real) : (term375 x y) = (term376 x y).
Proof. exact (MK_COMB (@lem1546448 x y) (@lem1546415)). Qed.
Lemma lem1546450 (x : real) (y : real) : (term376 x y) = (term377 x y).
Proof. exact (@lem1483519 (term372 x y) term30). Qed.
Lemma lem1546452 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546453 : term114 = term30.
Proof. exact (@lem1546452 term66). Qed.
Lemma lem1546454 (x : real) (y : real) : (term378 x y) = (term378 x y).
Proof. exact (eq_refl (term378 x y)). Qed.
Lemma lem1546455 (x : real) (y : real) : (term377 x y) = (term379 x y).
Proof. exact (MK_COMB (@lem1546454 x y) (@lem1546453)). Qed.
Lemma lem1546456 (x : real) (y : real) : (term379 x y) = (term372 x y).
Proof. exact (@lem1483450 (term372 x y)). Qed.
Lemma lem1546457 (x : real) (y : real) : (term377 x y) = (term372 x y).
Proof. exact (TRANS (@lem1546455 x y) (@lem1546456 x y)). Qed.
Lemma lem1546458 (x : real) (y : real) : (term376 x y) = (term372 x y).
Proof. exact (TRANS (@lem1546450 x y) (@lem1546457 x y)). Qed.
Lemma lem1546459 (x : real) (y : real) : (term375 x y) = (term372 x y).
Proof. exact (TRANS (@lem1546449 x y) (@lem1546458 x y)). Qed.
Lemma lem1546460 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546461 (x : real) (y : real) : (term380 x y) = (term381 x y).
Proof. exact (MK_COMB (@lem1546460) (@lem1546459 x y)). Qed.
Lemma lem1546462 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546463 (x : real) (y : real) : (term370 x y) = (term382 x y).
Proof. exact (MK_COMB (@lem1546461 x y) (@lem1546462)). Qed.
Lemma lem1546464 (x : real) (y : real) : (term369 x y) = (term382 x y).
Proof. exact (TRANS (@lem1546414 x y) (@lem1546463 x y)). Qed.
Lemma lem1546465 (y : real) : (term383 y) = (term384 y).
Proof. exact (@lem1483525 (real_add y y) term30). Qed.
Lemma lem1546466 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546472 (y : real) : (real_add y y) = (term299 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1546473 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1546474 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546475 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546476 : term272 = term273.
Proof. exact (EQ_MP (@lem1546475) (@lem1546474)). Qed.
Lemma lem1546477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546478 : term274 = term275.
Proof. exact (MK_COMB (@lem1546477) (@lem1546476)). Qed.
Lemma lem1546479 : term300 = term275.
Proof. exact (TRANS (@lem1546473) (@lem1546478)). Qed.
Lemma lem1546480 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546481 : term301 = term302.
Proof. exact (MK_COMB (@lem1546480) (@lem1546479)). Qed.
Lemma lem1546482 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546483 (y : real) : (term299 y) = (term303 y).
Proof. exact (MK_COMB (@lem1546481) (@lem1546482 y)). Qed.
Lemma lem1546485 (y : real) : (real_add y y) = (term303 y).
Proof. exact (TRANS (@lem1546472 y) (@lem1546483 y)). Qed.
Lemma lem1546486 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546487 (y : real) : (term385 y) = (term386 y).
Proof. exact (MK_COMB (@lem1546486) (@lem1546485 y)). Qed.
Lemma lem1546488 (y : real) : (term387 y) = (term388 y).
Proof. exact (MK_COMB (@lem1546487 y) (@lem1546466)). Qed.
Lemma lem1546489 (y : real) : (term388 y) = (term389 y).
Proof. exact (@lem1483519 (term303 y) term30). Qed.
Lemma lem1546491 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546492 : term114 = term30.
Proof. exact (@lem1546491 term66). Qed.
Lemma lem1546493 (y : real) : (term305 y) = (term305 y).
Proof. exact (eq_refl (term305 y)). Qed.
Lemma lem1546494 (y : real) : (term389 y) = (term390 y).
Proof. exact (MK_COMB (@lem1546493 y) (@lem1546492)). Qed.
Lemma lem1546495 (y : real) : (term390 y) = (term303 y).
Proof. exact (@lem1483450 (term303 y)). Qed.
Lemma lem1546496 (y : real) : (term389 y) = (term303 y).
Proof. exact (TRANS (@lem1546494 y) (@lem1546495 y)). Qed.
Lemma lem1546497 (y : real) : (term388 y) = (term303 y).
Proof. exact (TRANS (@lem1546489 y) (@lem1546496 y)). Qed.
Lemma lem1546498 (y : real) : (term387 y) = (term303 y).
Proof. exact (TRANS (@lem1546488 y) (@lem1546497 y)). Qed.
Lemma lem1546499 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546500 (y : real) : (term391 y) = (term392 y).
Proof. exact (MK_COMB (@lem1546499) (@lem1546498 y)). Qed.
Lemma lem1546501 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546502 (y : real) : (term384 y) = (term393 y).
Proof. exact (MK_COMB (@lem1546500 y) (@lem1546501)). Qed.
Lemma lem1546503 (y : real) : (term383 y) = (term393 y).
Proof. exact (TRANS (@lem1546465 y) (@lem1546502 y)). Qed.
Lemma lem1546504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546505 (x : real) (y : real) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem1546504) (@lem1546464 x y)). Qed.
Lemma lem1546506 (x : real) (y : real) : (term396 x y) = (term397 x y).
Proof. exact (MK_COMB (@lem1546505 x y) (@lem1546503 y)). Qed.
Lemma lem1546507 (y : real) : (term398 y) = (term399 y).
Proof. exact (@lem1483525 (term248 y) term30). Qed.
Lemma lem1546508 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546520 (y : real) : (term248 y) = (term249 y).
Proof. exact (@lem1483440 term59 y). Qed.
Lemma lem1546522 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546523 : term251 = term30.
Proof. exact (@lem1546522 term66). Qed.
Lemma lem1546524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546525 : term252 = term253.
Proof. exact (MK_COMB (@lem1546524) (@lem1546523)). Qed.
Lemma lem1546526 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546527 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1546525) (@lem1546526 y)). Qed.
Lemma lem1546528 (y : real) : (term248 y) = (term254 y).
Proof. exact (TRANS (@lem1546520 y) (@lem1546527 y)). Qed.
Lemma lem1546529 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1546531 (y : real) : (term248 y) = term30.
Proof. exact (TRANS (@lem1546528 y) (@lem1546529 y)). Qed.
Lemma lem1546532 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546533 (y : real) : (term400 y) = term159.
Proof. exact (MK_COMB (@lem1546532) (@lem1546531 y)). Qed.
Lemma lem1546534 (y : real) : (term401 y) = term402.
Proof. exact (MK_COMB (@lem1546533 y) (@lem1546508)). Qed.
Lemma lem1546535 : term402 = term403.
Proof. exact (@lem1483519 term30 term30). Qed.
Lemma lem1546537 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546538 : term114 = term30.
Proof. exact (@lem1546537 term66). Qed.
Lemma lem1546539 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem1546540 : term403 = term404.
Proof. exact (MK_COMB (@lem1546539) (@lem1546538)). Qed.
Lemma lem1546541 : term404 = term30.
Proof. exact (@lem1483448 term30). Qed.
Lemma lem1546542 : term403 = term30.
Proof. exact (TRANS (@lem1546540) (@lem1546541)). Qed.
Lemma lem1546543 : term402 = term30.
Proof. exact (TRANS (@lem1546535) (@lem1546542)). Qed.
Lemma lem1546544 (y : real) : (term401 y) = term30.
Proof. exact (TRANS (@lem1546534 y) (@lem1546543)). Qed.
Lemma lem1546545 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546546 (y : real) : (term405 y) = term406.
Proof. exact (MK_COMB (@lem1546545) (@lem1546544 y)). Qed.
Lemma lem1546547 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546548 (y : real) : (term399 y) = term407.
Proof. exact (MK_COMB (@lem1546546 y) (@lem1546547)). Qed.
Lemma lem1546549 (y : real) : (term398 y) = term407.
Proof. exact (TRANS (@lem1546507 y) (@lem1546548 y)). Qed.
Lemma lem1546550 (x : real) (y : real) : (term408 x y) = (term409 x y).
Proof. exact (@lem1483525 (term410 x y) term30). Qed.
Lemma lem1546551 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546563 (y : real) : (term248 y) = (term249 y).
Proof. exact (@lem1483440 term59 y). Qed.
Lemma lem1546565 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546566 : term251 = term30.
Proof. exact (@lem1546565 term66). Qed.
Lemma lem1546567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546568 : term252 = term253.
Proof. exact (MK_COMB (@lem1546567) (@lem1546566)). Qed.
Lemma lem1546569 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546570 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1546568) (@lem1546569 y)). Qed.
Lemma lem1546571 (y : real) : (term248 y) = (term254 y).
Proof. exact (TRANS (@lem1546563 y) (@lem1546570 y)). Qed.
Lemma lem1546572 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1546574 (y : real) : (term248 y) = term30.
Proof. exact (TRANS (@lem1546571 y) (@lem1546572 y)). Qed.
Lemma lem1546583 (x : real) : (term305 x) = (term305 x).
Proof. exact (eq_refl (term305 x)). Qed.
Lemma lem1546584 (y : real) (x : real) : (term410 x y) = (term390 x).
Proof. exact (MK_COMB (@lem1546583 x) (@lem1546574 y)). Qed.
Lemma lem1546585 (x : real) : (term390 x) = (term303 x).
Proof. exact (@lem1483450 (term303 x)). Qed.
Lemma lem1546586 (y : real) (x : real) : (term410 x y) = (term303 x).
Proof. exact (TRANS (@lem1546584 y x) (@lem1546585 x)). Qed.
Lemma lem1546587 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546588 (y : real) (x : real) : (term411 x y) = (term386 x).
Proof. exact (MK_COMB (@lem1546587) (@lem1546586 y x)). Qed.
Lemma lem1546589 (y : real) (x : real) : (term412 x y) = (term388 x).
Proof. exact (MK_COMB (@lem1546588 y x) (@lem1546551)). Qed.
Lemma lem1546590 (x : real) : (term388 x) = (term389 x).
Proof. exact (@lem1483519 (term303 x) term30). Qed.
Lemma lem1546592 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546593 : term114 = term30.
Proof. exact (@lem1546592 term66). Qed.
Lemma lem1546594 (x : real) : (term305 x) = (term305 x).
Proof. exact (eq_refl (term305 x)). Qed.
Lemma lem1546595 (x : real) : (term389 x) = (term390 x).
Proof. exact (MK_COMB (@lem1546594 x) (@lem1546593)). Qed.
Lemma lem1546596 (x : real) : (term390 x) = (term303 x).
Proof. exact (@lem1483450 (term303 x)). Qed.
Lemma lem1546597 (x : real) : (term389 x) = (term303 x).
Proof. exact (TRANS (@lem1546595 x) (@lem1546596 x)). Qed.
Lemma lem1546598 (x : real) : (term388 x) = (term303 x).
Proof. exact (TRANS (@lem1546590 x) (@lem1546597 x)). Qed.
Lemma lem1546599 (y : real) (x : real) : (term412 x y) = (term303 x).
Proof. exact (TRANS (@lem1546589 y x) (@lem1546598 x)). Qed.
Lemma lem1546600 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546601 (y : real) (x : real) : (term413 x y) = (term392 x).
Proof. exact (MK_COMB (@lem1546600) (@lem1546599 y x)). Qed.
Lemma lem1546602 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546603 (y : real) (x : real) : (term409 x y) = (term393 x).
Proof. exact (MK_COMB (@lem1546601 y x) (@lem1546602)). Qed.
Lemma lem1546604 (y : real) (x : real) : (term408 x y) = (term393 x).
Proof. exact (TRANS (@lem1546550 x y) (@lem1546603 y x)). Qed.
Lemma lem1546605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546606 (y : real) : (term414 y) = term415.
Proof. exact (MK_COMB (@lem1546605) (@lem1546549 y)). Qed.
Lemma lem1546607 (y : real) (x : real) : (term416 x y) = (term417 x).
Proof. exact (MK_COMB (@lem1546606 y) (@lem1546604 y x)). Qed.
Lemma lem1546608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546609 (x : real) (y : real) : (term418 x y) = (term419 x y).
Proof. exact (MK_COMB (@lem1546608) (@lem1546506 x y)). Qed.
Lemma lem1546610 (y : real) (x : real) : (term420 x y) = (term421 y x).
Proof. exact (MK_COMB (@lem1546609 x y) (@lem1546607 y x)). Qed.
Lemma lem1546611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546612 (x : real) (y : real) : (term422 x y) = (term422 x y).
Proof. exact (MK_COMB (@lem1546611) (@lem1546413 x y)). Qed.
Lemma lem1546613 (y : real) (x : real) : (term337 x y) = (term423 y x).
Proof. exact (MK_COMB (@lem1546612 x y) (@lem1546610 y x)). Qed.
Lemma lem1546614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546615 (y : real) : (term338 y) = (term338 y).
Proof. exact (MK_COMB (@lem1546614) (@lem1546350 y)). Qed.
Lemma lem1546616 (y : real) (x : real) : (term340 x y) = (term424 y x).
Proof. exact (MK_COMB (@lem1546615 y) (@lem1546613 y x)). Qed.
Lemma lem1546617 (y : real) : (term425 y) = (term426 y).
Proof. exact (@lem1483525 term30 y). Qed.
Lemma lem1546623 (y : real) : (term427 y) = (term428 y).
Proof. exact (@lem1483519 term30 y). Qed.
Lemma lem1546628 (y : real) : (term428 y) = (term47 y).
Proof. exact (@lem1483448 (term47 y)). Qed.
Lemma lem1546630 (y : real) : (term427 y) = (term47 y).
Proof. exact (TRANS (@lem1546623 y) (@lem1546628 y)). Qed.
Lemma lem1546631 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546632 (y : real) : (term429 y) = (term430 y).
Proof. exact (MK_COMB (@lem1546631) (@lem1546630 y)). Qed.
Lemma lem1546633 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546634 (y : real) : (term426 y) = (term431 y).
Proof. exact (MK_COMB (@lem1546632 y) (@lem1546633)). Qed.
Lemma lem1546635 (y : real) : (term425 y) = (term431 y).
Proof. exact (TRANS (@lem1546617 y) (@lem1546634 y)). Qed.
Lemma lem1546636 (x : real) (y : real) : (term432 x y) = (term433 x y).
Proof. exact (@lem1483525 (term434 x y) term30). Qed.
Lemma lem1546637 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546644 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546653 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1546656 (x : real) (y : real) : (term434 x y) = (term435 x y).
Proof. exact (MK_COMB (@lem1546653 x) (@lem1546644 y)). Qed.
Lemma lem1546657 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546658 (x : real) (y : real) : (term436 x y) = (term437 x y).
Proof. exact (MK_COMB (@lem1546657) (@lem1546656 x y)). Qed.
Lemma lem1546659 (x : real) (y : real) : (term438 x y) = (term439 x y).
Proof. exact (MK_COMB (@lem1546658 x y) (@lem1546637)). Qed.
Lemma lem1546660 (x : real) (y : real) : (term439 x y) = (term440 x y).
Proof. exact (@lem1483519 (term435 x y) term30). Qed.
Lemma lem1546662 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546663 : term114 = term30.
Proof. exact (@lem1546662 term66). Qed.
Lemma lem1546664 (x : real) (y : real) : (term441 x y) = (term441 x y).
Proof. exact (eq_refl (term441 x y)). Qed.
Lemma lem1546665 (x : real) (y : real) : (term440 x y) = (term442 x y).
Proof. exact (MK_COMB (@lem1546664 x y) (@lem1546663)). Qed.
Lemma lem1546666 (x : real) (y : real) : (term442 x y) = (term435 x y).
Proof. exact (@lem1483450 (term435 x y)). Qed.
Lemma lem1546667 (x : real) (y : real) : (term440 x y) = (term435 x y).
Proof. exact (TRANS (@lem1546665 x y) (@lem1546666 x y)). Qed.
Lemma lem1546668 (x : real) (y : real) : (term439 x y) = (term435 x y).
Proof. exact (TRANS (@lem1546660 x y) (@lem1546667 x y)). Qed.
Lemma lem1546669 (x : real) (y : real) : (term438 x y) = (term435 x y).
Proof. exact (TRANS (@lem1546659 x y) (@lem1546668 x y)). Qed.
Lemma lem1546670 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546671 (x : real) (y : real) : (term443 x y) = (term444 x y).
Proof. exact (MK_COMB (@lem1546670) (@lem1546669 x y)). Qed.
Lemma lem1546672 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546673 (x : real) (y : real) : (term433 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1546671 x y) (@lem1546672)). Qed.
Lemma lem1546674 (x : real) (y : real) : (term432 x y) = (term445 x y).
Proof. exact (TRANS (@lem1546636 x y) (@lem1546673 x y)). Qed.
Lemma lem1546675 (x : real) (y : real) : (term446 x y) = (term447 x y).
Proof. exact (@lem1483525 (term448 x y) term30). Qed.
Lemma lem1546676 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546683 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546686 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1546689 (x : real) (y : real) : (term448 x y) = (term39 x y).
Proof. exact (MK_COMB (@lem1546686 x) (@lem1546683 y)). Qed.
Lemma lem1546690 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546691 (x : real) (y : real) : (term449 x y) = (term450 x y).
Proof. exact (MK_COMB (@lem1546690) (@lem1546689 x y)). Qed.
Lemma lem1546692 (x : real) (y : real) : (term451 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1546691 x y) (@lem1546676)). Qed.
Lemma lem1546693 (x : real) (y : real) : (term452 x y) = (term453 x y).
Proof. exact (@lem1483519 (term39 x y) term30). Qed.
Lemma lem1546695 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546696 : term114 = term30.
Proof. exact (@lem1546695 term66). Qed.
Lemma lem1546697 (x : real) (y : real) : (term454 x y) = (term454 x y).
Proof. exact (eq_refl (term454 x y)). Qed.
Lemma lem1546698 (x : real) (y : real) : (term453 x y) = (term455 x y).
Proof. exact (MK_COMB (@lem1546697 x y) (@lem1546696)). Qed.
Lemma lem1546699 (x : real) (y : real) : (term455 x y) = (term39 x y).
Proof. exact (@lem1483450 (term39 x y)). Qed.
Lemma lem1546700 (x : real) (y : real) : (term453 x y) = (term39 x y).
Proof. exact (TRANS (@lem1546698 x y) (@lem1546699 x y)). Qed.
Lemma lem1546701 (x : real) (y : real) : (term452 x y) = (term39 x y).
Proof. exact (TRANS (@lem1546693 x y) (@lem1546700 x y)). Qed.
Lemma lem1546702 (x : real) (y : real) : (term451 x y) = (term39 x y).
Proof. exact (TRANS (@lem1546692 x y) (@lem1546701 x y)). Qed.
Lemma lem1546703 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546704 (x : real) (y : real) : (term456 x y) = (term457 x y).
Proof. exact (MK_COMB (@lem1546703) (@lem1546702 x y)). Qed.
Lemma lem1546705 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546706 (x : real) (y : real) : (term447 x y) = (term458 x y).
Proof. exact (MK_COMB (@lem1546704 x y) (@lem1546705)). Qed.
Lemma lem1546707 (x : real) (y : real) : (term446 x y) = (term458 x y).
Proof. exact (TRANS (@lem1546675 x y) (@lem1546706 x y)). Qed.
Lemma lem1546708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546709 (x : real) (y : real) : (term459 x y) = (term460 x y).
Proof. exact (MK_COMB (@lem1546708) (@lem1546674 x y)). Qed.
Lemma lem1546710 (x : real) (y : real) : (term461 x y) = (term462 x y).
Proof. exact (MK_COMB (@lem1546709 x y) (@lem1546707 x y)). Qed.
Lemma lem1546711 (x : real) (y : real) : (term463 x y) = (term464 x y).
Proof. exact (@lem1483525 (term465 x y) term30). Qed.
Lemma lem1546712 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546719 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546722 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1546723 (y : real) : (term466 y) = (term316 y).
Proof. exact (MK_COMB (@lem1546722 y) (@lem1546719 y)). Qed.
Lemma lem1546724 (y : real) : (term316 y) = (term249 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1546726 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546727 : term251 = term30.
Proof. exact (@lem1546726 term66). Qed.
Lemma lem1546728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546729 : term252 = term253.
Proof. exact (MK_COMB (@lem1546728) (@lem1546727)). Qed.
Lemma lem1546730 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546731 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1546729) (@lem1546730 y)). Qed.
Lemma lem1546732 (y : real) : (term316 y) = (term254 y).
Proof. exact (TRANS (@lem1546724 y) (@lem1546731 y)). Qed.
Lemma lem1546733 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1546734 (y : real) : (term316 y) = term30.
Proof. exact (TRANS (@lem1546732 y) (@lem1546733 y)). Qed.
Lemma lem1546735 (y : real) : (term466 y) = term30.
Proof. exact (TRANS (@lem1546723 y) (@lem1546734 y)). Qed.
Lemma lem1546744 (x : real) : (term281 x) = (term281 x).
Proof. exact (eq_refl (term281 x)). Qed.
Lemma lem1546745 (y : real) (x : real) : (term465 x y) = (term467 x).
Proof. exact (MK_COMB (@lem1546744 x) (@lem1546735 y)). Qed.
Lemma lem1546746 (x : real) : (term467 x) = (term279 x).
Proof. exact (@lem1483450 (term279 x)). Qed.
Lemma lem1546747 (y : real) (x : real) : (term465 x y) = (term279 x).
Proof. exact (TRANS (@lem1546745 y x) (@lem1546746 x)). Qed.
Lemma lem1546748 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546749 (y : real) (x : real) : (term468 x y) = (term469 x).
Proof. exact (MK_COMB (@lem1546748) (@lem1546747 y x)). Qed.
Lemma lem1546750 (y : real) (x : real) : (term470 x y) = (term471 x).
Proof. exact (MK_COMB (@lem1546749 y x) (@lem1546712)). Qed.
Lemma lem1546751 (x : real) : (term471 x) = (term472 x).
Proof. exact (@lem1483519 (term279 x) term30). Qed.
Lemma lem1546753 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546754 : term114 = term30.
Proof. exact (@lem1546753 term66). Qed.
Lemma lem1546755 (x : real) : (term281 x) = (term281 x).
Proof. exact (eq_refl (term281 x)). Qed.
Lemma lem1546756 (x : real) : (term472 x) = (term467 x).
Proof. exact (MK_COMB (@lem1546755 x) (@lem1546754)). Qed.
Lemma lem1546757 (x : real) : (term467 x) = (term279 x).
Proof. exact (@lem1483450 (term279 x)). Qed.
Lemma lem1546758 (x : real) : (term472 x) = (term279 x).
Proof. exact (TRANS (@lem1546756 x) (@lem1546757 x)). Qed.
Lemma lem1546759 (x : real) : (term471 x) = (term279 x).
Proof. exact (TRANS (@lem1546751 x) (@lem1546758 x)). Qed.
Lemma lem1546760 (y : real) (x : real) : (term470 x y) = (term279 x).
Proof. exact (TRANS (@lem1546750 y x) (@lem1546759 x)). Qed.
Lemma lem1546761 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546762 (y : real) (x : real) : (term473 x y) = (term474 x).
Proof. exact (MK_COMB (@lem1546761) (@lem1546760 y x)). Qed.
Lemma lem1546763 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546764 (y : real) (x : real) : (term464 x y) = (term475 x).
Proof. exact (MK_COMB (@lem1546762 y x) (@lem1546763)). Qed.
Lemma lem1546765 (y : real) (x : real) : (term463 x y) = (term475 x).
Proof. exact (TRANS (@lem1546711 x y) (@lem1546764 y x)). Qed.
Lemma lem1546766 (y : real) : (term476 y) = (term477 y).
Proof. exact (@lem1483525 (term466 y) term30). Qed.
Lemma lem1546767 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546774 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546777 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1546778 (y : real) : (term466 y) = (term316 y).
Proof. exact (MK_COMB (@lem1546777 y) (@lem1546774 y)). Qed.
Lemma lem1546779 (y : real) : (term316 y) = (term249 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1546781 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1546782 : term251 = term30.
Proof. exact (@lem1546781 term66). Qed.
Lemma lem1546783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546784 : term252 = term253.
Proof. exact (MK_COMB (@lem1546783) (@lem1546782)). Qed.
Lemma lem1546785 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546786 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1546784) (@lem1546785 y)). Qed.
Lemma lem1546787 (y : real) : (term316 y) = (term254 y).
Proof. exact (TRANS (@lem1546779 y) (@lem1546786 y)). Qed.
Lemma lem1546788 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1546789 (y : real) : (term316 y) = term30.
Proof. exact (TRANS (@lem1546787 y) (@lem1546788 y)). Qed.
Lemma lem1546790 (y : real) : (term466 y) = term30.
Proof. exact (TRANS (@lem1546778 y) (@lem1546789 y)). Qed.
Lemma lem1546791 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546792 (y : real) : (term478 y) = term159.
Proof. exact (MK_COMB (@lem1546791) (@lem1546790 y)). Qed.
Lemma lem1546793 (y : real) : (term479 y) = term402.
Proof. exact (MK_COMB (@lem1546792 y) (@lem1546767)). Qed.
Lemma lem1546794 : term402 = term403.
Proof. exact (@lem1483519 term30 term30). Qed.
Lemma lem1546796 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546797 : term114 = term30.
Proof. exact (@lem1546796 term66). Qed.
Lemma lem1546798 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem1546799 : term403 = term404.
Proof. exact (MK_COMB (@lem1546798) (@lem1546797)). Qed.
Lemma lem1546800 : term404 = term30.
Proof. exact (@lem1483448 term30). Qed.
Lemma lem1546801 : term403 = term30.
Proof. exact (TRANS (@lem1546799) (@lem1546800)). Qed.
Lemma lem1546802 : term402 = term30.
Proof. exact (TRANS (@lem1546794) (@lem1546801)). Qed.
Lemma lem1546803 (y : real) : (term479 y) = term30.
Proof. exact (TRANS (@lem1546793 y) (@lem1546802)). Qed.
Lemma lem1546804 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546805 (y : real) : (term480 y) = term406.
Proof. exact (MK_COMB (@lem1546804) (@lem1546803 y)). Qed.
Lemma lem1546806 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546807 (y : real) : (term477 y) = term407.
Proof. exact (MK_COMB (@lem1546805 y) (@lem1546806)). Qed.
Lemma lem1546808 (y : real) : (term476 y) = term407.
Proof. exact (TRANS (@lem1546766 y) (@lem1546807 y)). Qed.
Lemma lem1546809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546810 (y : real) (x : real) : (term481 x y) = (term482 x).
Proof. exact (MK_COMB (@lem1546809) (@lem1546765 y x)). Qed.
Lemma lem1546811 (y : real) (x : real) : (term483 x y) = (term484 x).
Proof. exact (MK_COMB (@lem1546810 y x) (@lem1546808 y)). Qed.
Lemma lem1546812 (y : real) : (term485 y) = (term486 y).
Proof. exact (@lem1483525 (term487 y) term30). Qed.
Lemma lem1546813 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546820 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546829 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1546830 (y : real) : (term487 y) = (term266 y).
Proof. exact (MK_COMB (@lem1546829 y) (@lem1546820 y)). Qed.
Lemma lem1546831 (y : real) : (term266 y) = (term267 y).
Proof. exact (@lem1483438 term59 term59 y). Qed.
Lemma lem1546832 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1546833 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546834 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546835 : term272 = term273.
Proof. exact (EQ_MP (@lem1546834) (@lem1546833)). Qed.
Lemma lem1546836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546837 : term274 = term275.
Proof. exact (MK_COMB (@lem1546836) (@lem1546835)). Qed.
Lemma lem1546838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1546839 : term269 = term276.
Proof. exact (MK_COMB (@lem1546838) (@lem1546837)). Qed.
Lemma lem1546840 : term268 = term276.
Proof. exact (TRANS (@lem1546832) (@lem1546839)). Qed.
Lemma lem1546841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546842 : term277 = term278.
Proof. exact (MK_COMB (@lem1546841) (@lem1546840)). Qed.
Lemma lem1546843 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546844 (y : real) : (term267 y) = (term279 y).
Proof. exact (MK_COMB (@lem1546842) (@lem1546843 y)). Qed.
Lemma lem1546845 (y : real) : (term266 y) = (term279 y).
Proof. exact (TRANS (@lem1546831 y) (@lem1546844 y)). Qed.
Lemma lem1546846 (y : real) : (term487 y) = (term279 y).
Proof. exact (TRANS (@lem1546830 y) (@lem1546845 y)). Qed.
Lemma lem1546847 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546848 (y : real) : (term488 y) = (term469 y).
Proof. exact (MK_COMB (@lem1546847) (@lem1546846 y)). Qed.
Lemma lem1546849 (y : real) : (term489 y) = (term471 y).
Proof. exact (MK_COMB (@lem1546848 y) (@lem1546813)). Qed.
Lemma lem1546850 (y : real) : (term471 y) = (term472 y).
Proof. exact (@lem1483519 (term279 y) term30). Qed.
Lemma lem1546852 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546853 : term114 = term30.
Proof. exact (@lem1546852 term66). Qed.
Lemma lem1546854 (y : real) : (term281 y) = (term281 y).
Proof. exact (eq_refl (term281 y)). Qed.
Lemma lem1546855 (y : real) : (term472 y) = (term467 y).
Proof. exact (MK_COMB (@lem1546854 y) (@lem1546853)). Qed.
Lemma lem1546856 (y : real) : (term467 y) = (term279 y).
Proof. exact (@lem1483450 (term279 y)). Qed.
Lemma lem1546857 (y : real) : (term472 y) = (term279 y).
Proof. exact (TRANS (@lem1546855 y) (@lem1546856 y)). Qed.
Lemma lem1546858 (y : real) : (term471 y) = (term279 y).
Proof. exact (TRANS (@lem1546850 y) (@lem1546857 y)). Qed.
Lemma lem1546859 (y : real) : (term489 y) = (term279 y).
Proof. exact (TRANS (@lem1546849 y) (@lem1546858 y)). Qed.
Lemma lem1546860 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546861 (y : real) : (term490 y) = (term474 y).
Proof. exact (MK_COMB (@lem1546860) (@lem1546859 y)). Qed.
Lemma lem1546862 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546863 (y : real) : (term486 y) = (term475 y).
Proof. exact (MK_COMB (@lem1546861 y) (@lem1546862)). Qed.
Lemma lem1546864 (y : real) : (term485 y) = (term475 y).
Proof. exact (TRANS (@lem1546812 y) (@lem1546863 y)). Qed.
Lemma lem1546865 (x : real) (y : real) : (term491 x y) = (term492 x y).
Proof. exact (@lem1483525 (term493 x y) term30). Qed.
Lemma lem1546866 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546873 (y : real) : (real_neg y) = (term47 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1546882 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1546883 (y : real) : (term487 y) = (term266 y).
Proof. exact (MK_COMB (@lem1546882 y) (@lem1546873 y)). Qed.
Lemma lem1546884 (y : real) : (term266 y) = (term267 y).
Proof. exact (@lem1483438 term59 term59 y). Qed.
Lemma lem1546885 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1546886 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1546887 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1546888 : term272 = term273.
Proof. exact (EQ_MP (@lem1546887) (@lem1546886)). Qed.
Lemma lem1546889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1546890 : term274 = term275.
Proof. exact (MK_COMB (@lem1546889) (@lem1546888)). Qed.
Lemma lem1546891 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1546892 : term269 = term276.
Proof. exact (MK_COMB (@lem1546891) (@lem1546890)). Qed.
Lemma lem1546893 : term268 = term276.
Proof. exact (TRANS (@lem1546885) (@lem1546892)). Qed.
Lemma lem1546894 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1546895 : term277 = term278.
Proof. exact (MK_COMB (@lem1546894) (@lem1546893)). Qed.
Lemma lem1546896 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1546897 (y : real) : (term267 y) = (term279 y).
Proof. exact (MK_COMB (@lem1546895) (@lem1546896 y)). Qed.
Lemma lem1546898 (y : real) : (term266 y) = (term279 y).
Proof. exact (TRANS (@lem1546884 y) (@lem1546897 y)). Qed.
Lemma lem1546899 (y : real) : (term487 y) = (term279 y).
Proof. exact (TRANS (@lem1546883 y) (@lem1546898 y)). Qed.
Lemma lem1546908 (x : real) : (term305 x) = (term305 x).
Proof. exact (eq_refl (term305 x)). Qed.
Lemma lem1546911 (x : real) (y : real) : (term493 x y) = (term494 x y).
Proof. exact (MK_COMB (@lem1546908 x) (@lem1546899 y)). Qed.
Lemma lem1546912 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1546913 (x : real) (y : real) : (term495 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem1546912) (@lem1546911 x y)). Qed.
Lemma lem1546914 (x : real) (y : real) : (term497 x y) = (term498 x y).
Proof. exact (MK_COMB (@lem1546913 x y) (@lem1546866)). Qed.
Lemma lem1546915 (x : real) (y : real) : (term498 x y) = (term499 x y).
Proof. exact (@lem1483519 (term494 x y) term30). Qed.
Lemma lem1546917 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1546918 : term114 = term30.
Proof. exact (@lem1546917 term66). Qed.
Lemma lem1546919 (x : real) (y : real) : (term500 x y) = (term500 x y).
Proof. exact (eq_refl (term500 x y)). Qed.
Lemma lem1546920 (x : real) (y : real) : (term499 x y) = (term501 x y).
Proof. exact (MK_COMB (@lem1546919 x y) (@lem1546918)). Qed.
Lemma lem1546921 (x : real) (y : real) : (term501 x y) = (term494 x y).
Proof. exact (@lem1483450 (term494 x y)). Qed.
Lemma lem1546922 (x : real) (y : real) : (term499 x y) = (term494 x y).
Proof. exact (TRANS (@lem1546920 x y) (@lem1546921 x y)). Qed.
Lemma lem1546923 (x : real) (y : real) : (term498 x y) = (term494 x y).
Proof. exact (TRANS (@lem1546915 x y) (@lem1546922 x y)). Qed.
Lemma lem1546924 (x : real) (y : real) : (term497 x y) = (term494 x y).
Proof. exact (TRANS (@lem1546914 x y) (@lem1546923 x y)). Qed.
Lemma lem1546925 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1546926 (x : real) (y : real) : (term502 x y) = (term503 x y).
Proof. exact (MK_COMB (@lem1546925) (@lem1546924 x y)). Qed.
Lemma lem1546927 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546928 (x : real) (y : real) : (term492 x y) = (term504 x y).
Proof. exact (MK_COMB (@lem1546926 x y) (@lem1546927)). Qed.
Lemma lem1546929 (x : real) (y : real) : (term491 x y) = (term504 x y).
Proof. exact (TRANS (@lem1546865 x y) (@lem1546928 x y)). Qed.
Lemma lem1546930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546931 (y : real) : (term505 y) = (term482 y).
Proof. exact (MK_COMB (@lem1546930) (@lem1546864 y)). Qed.
Lemma lem1546932 (x : real) (y : real) : (term506 x y) = (term507 x y).
Proof. exact (MK_COMB (@lem1546931 y) (@lem1546929 x y)). Qed.
Lemma lem1546933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546934 (y : real) (x : real) : (term508 x y) = (term509 x).
Proof. exact (MK_COMB (@lem1546933) (@lem1546811 y x)). Qed.
Lemma lem1546935 (x : real) (y : real) : (term510 x y) = (term511 x y).
Proof. exact (MK_COMB (@lem1546934 y x) (@lem1546932 x y)). Qed.
Lemma lem1546936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546937 (x : real) (y : real) : (term512 x y) = (term513 x y).
Proof. exact (MK_COMB (@lem1546936) (@lem1546710 x y)). Qed.
Lemma lem1546938 (x : real) (y : real) : (term332 x y) = (term514 x y).
Proof. exact (MK_COMB (@lem1546937 x y) (@lem1546935 x y)). Qed.
Lemma lem1546939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546940 (y : real) : (term333 y) = (term515 y).
Proof. exact (MK_COMB (@lem1546939) (@lem1546635 y)). Qed.
Lemma lem1546941 (x : real) (y : real) : (term335 x y) = (term516 x y).
Proof. exact (MK_COMB (@lem1546940 y) (@lem1546938 x y)). Qed.
Lemma lem1546942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1546943 (y : real) (x : real) : (term342 x y) = (term517 y x).
Proof. exact (MK_COMB (@lem1546942) (@lem1546616 y x)). Qed.
Lemma lem1546944 (x : real) (y : real) : (term343 x y) = (term518 x y).
Proof. exact (MK_COMB (@lem1546943 y x) (@lem1546941 x y)). Qed.
Lemma lem1546955 (x : real) (y : real) : (term327 x y) = (term518 x y).
Proof. exact (TRANS (@lem1546329 x y) (@lem1546944 x y)). Qed.
Lemma lem1546956 (x : real) (y : real) : (term214 x y) = (term518 x y).
Proof. exact (TRANS (@lem1546313 x y) (@lem1546955 x y)). Qed.
Lemma lem1546958 (a : real) (x : real) (r : real) : (term519 a x r) = (term520 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1546959 (x : real) (y : real) : (term119 x y) = (term521 x y).
Proof. exact (@lem1546958 (real_abs x) y term30). Qed.
Lemma lem1546966 (y : real) : (term71 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1546969 (x : real) : (term218 x) = (term218 x).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem1546970 (x : real) (y : real) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1546969 x) (@lem1546966 y)). Qed.
Lemma lem1546971 (y : real) (x : real) : (term220 x y) = (term221 y x).
Proof. exact (@lem1483488 y (real_abs x)). Qed.
Lemma lem1546972 (y : real) (x : real) : (term219 x y) = (term221 y x).
Proof. exact (TRANS (@lem1546970 x y) (@lem1546971 y x)). Qed.
Lemma lem1546973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1546974 (y : real) (x : real) : (term522 x y) = (term523 y x).
Proof. exact (MK_COMB (@lem1546973) (@lem1546972 y x)). Qed.
Lemma lem1546975 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546976 (y : real) (x : real) : (term524 x y) = (term525 y x).
Proof. exact (MK_COMB (@lem1546974 y x) (@lem1546975)). Qed.
Lemma lem1546989 (y : real) (x : real) : (term226 x y) = (term227 y x).
Proof. exact (@lem1483488 (term47 y) (real_abs x)). Qed.
Lemma lem1546990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1546991 (y : real) (x : real) : (term526 x y) = (term527 y x).
Proof. exact (MK_COMB (@lem1546990) (@lem1546989 y x)). Qed.
Lemma lem1546992 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1546993 (y : real) (x : real) : (term528 x y) = (term529 y x).
Proof. exact (MK_COMB (@lem1546991 y x) (@lem1546992)). Qed.
Lemma lem1546994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546995 (y : real) (x : real) : (term530 x y) = (term531 y x).
Proof. exact (MK_COMB (@lem1546994) (@lem1546993 y x)). Qed.
Lemma lem1546996 (y : real) (x : real) : (term521 x y) = (term532 y x).
Proof. exact (MK_COMB (@lem1546995 y x) (@lem1546976 y x)). Qed.
Lemma lem1546997 (y : real) (x : real) : (term119 x y) = (term532 y x).
Proof. exact (TRANS (@lem1546959 x y) (@lem1546996 y x)). Qed.
Lemma lem1546998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1546999 (y : real) (x : real) : (term155 x y) = (term533 y x).
Proof. exact (MK_COMB (@lem1546998) (@lem1546997 y x)). Qed.
Lemma lem1547000 (x : real) (y : real) : (term154 x y) = (term154 x y).
Proof. exact (eq_refl (term154 x y)). Qed.
Lemma lem1547001 (x : real) (y : real) : (term156 x y) = (term534 x y).
Proof. exact (MK_COMB (@lem1546999 y x) (@lem1547000 x y)). Qed.
Lemma lem1547002 (x : real) (y : real) : (term535 y x) = (term534 x y).
Proof. exact (eq_refl (term535 y x)). Qed.
Lemma lem1547003 (y : real) (x : real) : (term534 x y) = (term535 y x).
Proof. exact (SYM (@lem1547002 x y)). Qed.
Lemma lem1547004 (y : real) (x : real) : (term535 y x) = (term536 y x).
Proof. exact (@lem1482981 (term537 x y) x). Qed.
Lemma lem1547005 (y : real) (x : real) : (term534 x y) = (term536 y x).
Proof. exact (TRANS (@lem1547003 y x) (@lem1547004 y x)). Qed.
Lemma lem1547006 (x : real) (y : real) : (term538 y x) = (term539 x y).
Proof. exact (eq_refl (term538 y x)). Qed.
Lemma lem1547007 (x : real) : (term333 x) = (term333 x).
Proof. exact (eq_refl (term333 x)). Qed.
Lemma lem1547008 (x : real) (y : real) : (term540 y x) = (term541 x y).
Proof. exact (MK_COMB (@lem1547007 x) (@lem1547006 x y)). Qed.
Lemma lem1547009 (x : real) (y : real) : (term542 y x) = (term543 x y).
Proof. exact (eq_refl (term542 y x)). Qed.
Lemma lem1547010 (x : real) : (term338 x) = (term338 x).
Proof. exact (eq_refl (term338 x)). Qed.
Lemma lem1547011 (x : real) (y : real) : (term544 y x) = (term545 x y).
Proof. exact (MK_COMB (@lem1547010 x) (@lem1547009 x y)). Qed.
Lemma lem1547012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1547013 (x : real) (y : real) : (term546 y x) = (term547 x y).
Proof. exact (MK_COMB (@lem1547012) (@lem1547011 x y)). Qed.
Lemma lem1547014 (x : real) (y : real) : (term536 y x) = (term548 x y).
Proof. exact (MK_COMB (@lem1547013 x y) (@lem1547008 x y)). Qed.
Lemma lem1547015 (x : real) (y : real) : (term549 x y) = (term549 x y).
Proof. exact (eq_refl (term549 x y)). Qed.
Lemma lem1547016 (x : real) (y : real) : ((term534 x y) = (term536 y x)) = ((term534 x y) = (term548 x y)).
Proof. exact (MK_COMB (@lem1547015 x y) (@lem1547014 x y)). Qed.
Lemma lem1547017 (x : real) (y : real) : (term534 x y) = (term548 x y).
Proof. exact (EQ_MP (@lem1547016 x y) (@lem1547005 y x)). Qed.
Lemma lem1547018 (x : real) : (term345 x) = (term346 x).
Proof. exact (@lem1483527 x term30). Qed.
Lemma lem1547024 (x : real) : (term347 x) = (term348 x).
Proof. exact (@lem1483519 x term30). Qed.
Lemma lem1547026 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547027 : term114 = term30.
Proof. exact (@lem1547026 term66). Qed.
Lemma lem1547028 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1547029 (x : real) : (term348 x) = (term349 x).
Proof. exact (MK_COMB (@lem1547028 x) (@lem1547027)). Qed.
Lemma lem1547030 (x : real) : (term349 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1547031 (x : real) : (term348 x) = x.
Proof. exact (TRANS (@lem1547029 x) (@lem1547030 x)). Qed.
Lemma lem1547033 (x : real) : (term347 x) = x.
Proof. exact (TRANS (@lem1547024 x) (@lem1547031 x)). Qed.
Lemma lem1547034 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1547035 (x : real) : (term350 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1547034) (@lem1547033 x)). Qed.
Lemma lem1547036 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547037 (x : real) : (term346 x) = (term345 x).
Proof. exact (MK_COMB (@lem1547035 x) (@lem1547036)). Qed.
Lemma lem1547038 (x : real) : (term345 x) = (term345 x).
Proof. exact (TRANS (@lem1547018 x) (@lem1547037 x)). Qed.
Lemma lem1547039 (y : real) (x : real) : (term550 y x) = (term551 y x).
Proof. exact (@lem1483527 (term73 y x) term30). Qed.
Lemma lem1547040 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547053 (x : real) (y : real) : (term73 y x) = (term39 x y).
Proof. exact (@lem1483488 x (term47 y)). Qed.
Lemma lem1547054 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547055 (x : real) (y : real) : (term552 y x) = (term450 x y).
Proof. exact (MK_COMB (@lem1547054) (@lem1547053 x y)). Qed.
Lemma lem1547056 (x : real) (y : real) : (term353 y x) = (term452 x y).
Proof. exact (MK_COMB (@lem1547055 x y) (@lem1547040)). Qed.
Lemma lem1547057 (x : real) (y : real) : (term452 x y) = (term453 x y).
Proof. exact (@lem1483519 (term39 x y) term30). Qed.
Lemma lem1547059 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547060 : term114 = term30.
Proof. exact (@lem1547059 term66). Qed.
Lemma lem1547061 (x : real) (y : real) : (term454 x y) = (term454 x y).
Proof. exact (eq_refl (term454 x y)). Qed.
Lemma lem1547062 (x : real) (y : real) : (term453 x y) = (term455 x y).
Proof. exact (MK_COMB (@lem1547061 x y) (@lem1547060)). Qed.
Lemma lem1547063 (x : real) (y : real) : (term455 x y) = (term39 x y).
Proof. exact (@lem1483450 (term39 x y)). Qed.
Lemma lem1547064 (x : real) (y : real) : (term453 x y) = (term39 x y).
Proof. exact (TRANS (@lem1547062 x y) (@lem1547063 x y)). Qed.
Lemma lem1547065 (x : real) (y : real) : (term452 x y) = (term39 x y).
Proof. exact (TRANS (@lem1547057 x y) (@lem1547064 x y)). Qed.
Lemma lem1547066 (x : real) (y : real) : (term353 y x) = (term39 x y).
Proof. exact (TRANS (@lem1547056 x y) (@lem1547065 x y)). Qed.
Lemma lem1547067 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1547068 (x : real) (y : real) : (term553 y x) = (term554 x y).
Proof. exact (MK_COMB (@lem1547067) (@lem1547066 x y)). Qed.
Lemma lem1547069 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547070 (x : real) (y : real) : (term551 y x) = (term555 x y).
Proof. exact (MK_COMB (@lem1547068 x y) (@lem1547069)). Qed.
Lemma lem1547071 (x : real) (y : real) : (term550 y x) = (term555 x y).
Proof. exact (TRANS (@lem1547039 y x) (@lem1547070 x y)). Qed.
Lemma lem1547072 (y : real) (x : real) : (term556 y x) = (term557 y x).
Proof. exact (@lem1483527 (real_add y x) term30). Qed.
Lemma lem1547073 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547080 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1483488 x y). Qed.
Lemma lem1547081 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547082 (x : real) (y : real) : (term558 y x) = (term558 x y).
Proof. exact (MK_COMB (@lem1547081) (@lem1547080 x y)). Qed.
Lemma lem1547083 (x : real) (y : real) : (term361 y x) = (term361 x y).
Proof. exact (MK_COMB (@lem1547082 x y) (@lem1547073)). Qed.
Lemma lem1547084 (x : real) (y : real) : (term361 x y) = (term362 x y).
Proof. exact (@lem1483519 (real_add x y) term30). Qed.
Lemma lem1547086 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547087 : term114 = term30.
Proof. exact (@lem1547086 term66). Qed.
Lemma lem1547088 (x : real) (y : real) : (term363 x y) = (term363 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem1547089 (x : real) (y : real) : (term362 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem1547088 x y) (@lem1547087)). Qed.
Lemma lem1547090 (x : real) (y : real) : (term364 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1547091 (x : real) (y : real) : (term362 x y) = (real_add x y).
Proof. exact (TRANS (@lem1547089 x y) (@lem1547090 x y)). Qed.
Lemma lem1547092 (x : real) (y : real) : (term361 x y) = (real_add x y).
Proof. exact (TRANS (@lem1547084 x y) (@lem1547091 x y)). Qed.
Lemma lem1547093 (x : real) (y : real) : (term361 y x) = (real_add x y).
Proof. exact (TRANS (@lem1547083 x y) (@lem1547092 x y)). Qed.
Lemma lem1547094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1547095 (x : real) (y : real) : (term559 y x) = (term560 x y).
Proof. exact (MK_COMB (@lem1547094) (@lem1547093 x y)). Qed.
Lemma lem1547096 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547097 (x : real) (y : real) : (term557 y x) = (term556 x y).
Proof. exact (MK_COMB (@lem1547095 x y) (@lem1547096)). Qed.
Lemma lem1547098 (x : real) (y : real) : (term556 y x) = (term556 x y).
Proof. exact (TRANS (@lem1547072 y x) (@lem1547097 x y)). Qed.
Lemma lem1547099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547100 (x : real) (y : real) : (term561 y x) = (term562 x y).
Proof. exact (MK_COMB (@lem1547099) (@lem1547071 x y)). Qed.
Lemma lem1547101 (x : real) (y : real) : (term563 y x) = (term564 x y).
Proof. exact (MK_COMB (@lem1547100 x y) (@lem1547098 x y)). Qed.
Lemma lem1547102 (x : real) (y : real) : (term565 x y) = (term566 x y).
Proof. exact (@lem1483525 (term567 x y) term30). Qed.
Lemma lem1547103 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547126 (x : real) (y : real) : (term568 x y) = (term569 x y).
Proof. exact (@lem1483484 x y (term165 y)). Qed.
Lemma lem1547135 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1547136 (x : real) (y : real) : (term567 x y) = (term570 x y).
Proof. exact (MK_COMB (@lem1547135 x) (@lem1547126 x y)). Qed.
Lemma lem1547137 (x : real) (y : real) : (term570 x y) = (term571 x y).
Proof. exact (@lem1483490 (term47 x) x (term572 y)). Qed.
Lemma lem1547138 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem1483440 term59 x). Qed.
Lemma lem1547140 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547141 : term251 = term30.
Proof. exact (@lem1547140 term66). Qed.
Lemma lem1547142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547143 : term252 = term253.
Proof. exact (MK_COMB (@lem1547142) (@lem1547141)). Qed.
Lemma lem1547144 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1547145 (x : real) : (term249 x) = (term254 x).
Proof. exact (MK_COMB (@lem1547143) (@lem1547144 x)). Qed.
Lemma lem1547146 (x : real) : (term248 x) = (term254 x).
Proof. exact (TRANS (@lem1547138 x) (@lem1547145 x)). Qed.
Lemma lem1547147 (x : real) : (term254 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1547148 (x : real) : (term248 x) = term30.
Proof. exact (TRANS (@lem1547146 x) (@lem1547147 x)). Qed.
Lemma lem1547149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547150 (x : real) : (term255 x) = term171.
Proof. exact (MK_COMB (@lem1547149) (@lem1547148 x)). Qed.
Lemma lem1547151 (y : real) : (term572 y) = (term572 y).
Proof. exact (eq_refl (term572 y)). Qed.
Lemma lem1547152 (x : real) (y : real) : (term571 x y) = (term573 y).
Proof. exact (MK_COMB (@lem1547150 x) (@lem1547151 y)). Qed.
Lemma lem1547153 (x : real) (y : real) : (term570 x y) = (term573 y).
Proof. exact (TRANS (@lem1547137 x y) (@lem1547152 x y)). Qed.
Lemma lem1547154 (y : real) : (term573 y) = (term572 y).
Proof. exact (@lem1483448 (term572 y)). Qed.
Lemma lem1547155 (x : real) (y : real) : (term570 x y) = (term572 y).
Proof. exact (TRANS (@lem1547153 x y) (@lem1547154 y)). Qed.
Lemma lem1547156 (x : real) (y : real) : (term567 x y) = (term572 y).
Proof. exact (TRANS (@lem1547136 x y) (@lem1547155 x y)). Qed.
Lemma lem1547157 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547158 (x : real) (y : real) : (term574 x y) = (term575 y).
Proof. exact (MK_COMB (@lem1547157) (@lem1547156 x y)). Qed.
Lemma lem1547159 (x : real) (y : real) : (term576 x y) = (term577 y).
Proof. exact (MK_COMB (@lem1547158 x y) (@lem1547103)). Qed.
Lemma lem1547160 (y : real) : (term577 y) = (term578 y).
Proof. exact (@lem1483519 (term572 y) term30). Qed.
Lemma lem1547162 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547163 : term114 = term30.
Proof. exact (@lem1547162 term66). Qed.
Lemma lem1547164 (y : real) : (term579 y) = (term579 y).
Proof. exact (eq_refl (term579 y)). Qed.
Lemma lem1547165 (y : real) : (term578 y) = (term580 y).
Proof. exact (MK_COMB (@lem1547164 y) (@lem1547163)). Qed.
Lemma lem1547166 (y : real) : (term580 y) = (term572 y).
Proof. exact (@lem1483450 (term572 y)). Qed.
Lemma lem1547167 (y : real) : (term578 y) = (term572 y).
Proof. exact (TRANS (@lem1547165 y) (@lem1547166 y)). Qed.
Lemma lem1547168 (y : real) : (term577 y) = (term572 y).
Proof. exact (TRANS (@lem1547160 y) (@lem1547167 y)). Qed.
Lemma lem1547169 (x : real) (y : real) : (term576 x y) = (term572 y).
Proof. exact (TRANS (@lem1547159 x y) (@lem1547168 y)). Qed.
Lemma lem1547170 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547171 (x : real) (y : real) : (term581 x y) = (term582 y).
Proof. exact (MK_COMB (@lem1547170) (@lem1547169 x y)). Qed.
Lemma lem1547172 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547173 (x : real) (y : real) : (term566 x y) = (term583 y).
Proof. exact (MK_COMB (@lem1547171 x y) (@lem1547172)). Qed.
Lemma lem1547174 (x : real) (y : real) : (term565 x y) = (term583 y).
Proof. exact (TRANS (@lem1547102 x y) (@lem1547173 x y)). Qed.
Lemma lem1547175 (x : real) (y : real) : (term584 x y) = (term585 x y).
Proof. exact (@lem1483525 (term586 x y) term30). Qed.
Lemma lem1547176 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547205 (x : real) (y : real) : (term587 x y) = (term588 x y).
Proof. exact (@lem1483484 x (term47 y) (term165 y)). Qed.
Lemma lem1547208 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1547209 (x : real) (y : real) : (term586 x y) = (term589 x y).
Proof. exact (MK_COMB (@lem1547208 x) (@lem1547205 x y)). Qed.
Lemma lem1547210 (x : real) (y : real) : (term589 x y) = (term590 x y).
Proof. exact (@lem1483490 x x (term591 y)). Qed.
Lemma lem1547211 (x : real) : (real_add x x) = (term299 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1547212 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1547213 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547214 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547215 : term272 = term273.
Proof. exact (EQ_MP (@lem1547214) (@lem1547213)). Qed.
Lemma lem1547216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547217 : term274 = term275.
Proof. exact (MK_COMB (@lem1547216) (@lem1547215)). Qed.
Lemma lem1547218 : term300 = term275.
Proof. exact (TRANS (@lem1547212) (@lem1547217)). Qed.
Lemma lem1547219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547220 : term301 = term302.
Proof. exact (MK_COMB (@lem1547219) (@lem1547218)). Qed.
Lemma lem1547221 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1547222 (x : real) : (term299 x) = (term303 x).
Proof. exact (MK_COMB (@lem1547220) (@lem1547221 x)). Qed.
Lemma lem1547223 (x : real) : (real_add x x) = (term303 x).
Proof. exact (TRANS (@lem1547211 x) (@lem1547222 x)). Qed.
Lemma lem1547224 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547225 (x : real) : (term304 x) = (term305 x).
Proof. exact (MK_COMB (@lem1547224) (@lem1547223 x)). Qed.
Lemma lem1547226 (y : real) : (term591 y) = (term591 y).
Proof. exact (eq_refl (term591 y)). Qed.
Lemma lem1547227 (x : real) (y : real) : (term590 x y) = (term592 x y).
Proof. exact (MK_COMB (@lem1547225 x) (@lem1547226 y)). Qed.
Lemma lem1547228 (x : real) (y : real) : (term589 x y) = (term592 x y).
Proof. exact (TRANS (@lem1547210 x y) (@lem1547227 x y)). Qed.
Lemma lem1547229 (x : real) (y : real) : (term586 x y) = (term592 x y).
Proof. exact (TRANS (@lem1547209 x y) (@lem1547228 x y)). Qed.
Lemma lem1547230 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547231 (x : real) (y : real) : (term593 x y) = (term594 x y).
Proof. exact (MK_COMB (@lem1547230) (@lem1547229 x y)). Qed.
Lemma lem1547232 (x : real) (y : real) : (term595 x y) = (term596 x y).
Proof. exact (MK_COMB (@lem1547231 x y) (@lem1547176)). Qed.
Lemma lem1547233 (x : real) (y : real) : (term596 x y) = (term597 x y).
Proof. exact (@lem1483519 (term592 x y) term30). Qed.
Lemma lem1547235 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547236 : term114 = term30.
Proof. exact (@lem1547235 term66). Qed.
Lemma lem1547237 (x : real) (y : real) : (term598 x y) = (term598 x y).
Proof. exact (eq_refl (term598 x y)). Qed.
Lemma lem1547238 (x : real) (y : real) : (term597 x y) = (term599 x y).
Proof. exact (MK_COMB (@lem1547237 x y) (@lem1547236)). Qed.
Lemma lem1547239 (x : real) (y : real) : (term599 x y) = (term592 x y).
Proof. exact (@lem1483450 (term592 x y)). Qed.
Lemma lem1547240 (x : real) (y : real) : (term597 x y) = (term592 x y).
Proof. exact (TRANS (@lem1547238 x y) (@lem1547239 x y)). Qed.
Lemma lem1547241 (x : real) (y : real) : (term596 x y) = (term592 x y).
Proof. exact (TRANS (@lem1547233 x y) (@lem1547240 x y)). Qed.
Lemma lem1547242 (x : real) (y : real) : (term595 x y) = (term592 x y).
Proof. exact (TRANS (@lem1547232 x y) (@lem1547241 x y)). Qed.
Lemma lem1547243 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547244 (x : real) (y : real) : (term600 x y) = (term601 x y).
Proof. exact (MK_COMB (@lem1547243) (@lem1547242 x y)). Qed.
Lemma lem1547245 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547246 (x : real) (y : real) : (term585 x y) = (term602 x y).
Proof. exact (MK_COMB (@lem1547244 x y) (@lem1547245)). Qed.
Lemma lem1547247 (x : real) (y : real) : (term584 x y) = (term602 x y).
Proof. exact (TRANS (@lem1547175 x y) (@lem1547246 x y)). Qed.
Lemma lem1547248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547249 (x : real) (y : real) : (term603 x y) = (term604 y).
Proof. exact (MK_COMB (@lem1547248) (@lem1547174 x y)). Qed.
Lemma lem1547250 (x : real) (y : real) : (term605 x y) = (term606 x y).
Proof. exact (MK_COMB (@lem1547249 x y) (@lem1547247 x y)). Qed.
Lemma lem1547251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547252 (x : real) (y : real) : (term607 y x) = (term608 x y).
Proof. exact (MK_COMB (@lem1547251) (@lem1547101 x y)). Qed.
Lemma lem1547253 (x : real) (y : real) : (term543 x y) = (term609 x y).
Proof. exact (MK_COMB (@lem1547252 x y) (@lem1547250 x y)). Qed.
Lemma lem1547254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547255 (x : real) : (term338 x) = (term338 x).
Proof. exact (MK_COMB (@lem1547254) (@lem1547038 x)). Qed.
Lemma lem1547256 (x : real) (y : real) : (term545 x y) = (term610 x y).
Proof. exact (MK_COMB (@lem1547255 x) (@lem1547253 x y)). Qed.
Lemma lem1547257 (x : real) : (term425 x) = (term426 x).
Proof. exact (@lem1483525 term30 x). Qed.
Lemma lem1547263 (x : real) : (term427 x) = (term428 x).
Proof. exact (@lem1483519 term30 x). Qed.
Lemma lem1547268 (x : real) : (term428 x) = (term47 x).
Proof. exact (@lem1483448 (term47 x)). Qed.
Lemma lem1547270 (x : real) : (term427 x) = (term47 x).
Proof. exact (TRANS (@lem1547263 x) (@lem1547268 x)). Qed.
Lemma lem1547271 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547272 (x : real) : (term429 x) = (term430 x).
Proof. exact (MK_COMB (@lem1547271) (@lem1547270 x)). Qed.
Lemma lem1547273 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547274 (x : real) : (term426 x) = (term431 x).
Proof. exact (MK_COMB (@lem1547272 x) (@lem1547273)). Qed.
Lemma lem1547275 (x : real) : (term425 x) = (term431 x).
Proof. exact (TRANS (@lem1547257 x) (@lem1547274 x)). Qed.
Lemma lem1547276 (y : real) (x : real) : (term611 y x) = (term612 y x).
Proof. exact (@lem1483527 (term434 y x) term30). Qed.
Lemma lem1547277 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547284 (x : real) : (real_neg x) = (term47 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1547293 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1547294 (y : real) (x : real) : (term434 y x) = (term435 y x).
Proof. exact (MK_COMB (@lem1547293 y) (@lem1547284 x)). Qed.
Lemma lem1547295 (x : real) (y : real) : (term435 y x) = (term435 x y).
Proof. exact (@lem1483488 (term47 x) (term47 y)). Qed.
Lemma lem1547296 (x : real) (y : real) : (term434 y x) = (term435 x y).
Proof. exact (TRANS (@lem1547294 y x) (@lem1547295 x y)). Qed.
Lemma lem1547297 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547298 (x : real) (y : real) : (term436 y x) = (term437 x y).
Proof. exact (MK_COMB (@lem1547297) (@lem1547296 x y)). Qed.
Lemma lem1547299 (x : real) (y : real) : (term438 y x) = (term439 x y).
Proof. exact (MK_COMB (@lem1547298 x y) (@lem1547277)). Qed.
Lemma lem1547300 (x : real) (y : real) : (term439 x y) = (term440 x y).
Proof. exact (@lem1483519 (term435 x y) term30). Qed.
Lemma lem1547302 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547303 : term114 = term30.
Proof. exact (@lem1547302 term66). Qed.
Lemma lem1547304 (x : real) (y : real) : (term441 x y) = (term441 x y).
Proof. exact (eq_refl (term441 x y)). Qed.
Lemma lem1547305 (x : real) (y : real) : (term440 x y) = (term442 x y).
Proof. exact (MK_COMB (@lem1547304 x y) (@lem1547303)). Qed.
Lemma lem1547306 (x : real) (y : real) : (term442 x y) = (term435 x y).
Proof. exact (@lem1483450 (term435 x y)). Qed.
Lemma lem1547307 (x : real) (y : real) : (term440 x y) = (term435 x y).
Proof. exact (TRANS (@lem1547305 x y) (@lem1547306 x y)). Qed.
Lemma lem1547308 (x : real) (y : real) : (term439 x y) = (term435 x y).
Proof. exact (TRANS (@lem1547300 x y) (@lem1547307 x y)). Qed.
Lemma lem1547309 (x : real) (y : real) : (term438 y x) = (term435 x y).
Proof. exact (TRANS (@lem1547299 x y) (@lem1547308 x y)). Qed.
Lemma lem1547310 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1547311 (x : real) (y : real) : (term613 y x) = (term614 x y).
Proof. exact (MK_COMB (@lem1547310) (@lem1547309 x y)). Qed.
Lemma lem1547312 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547313 (x : real) (y : real) : (term612 y x) = (term615 x y).
Proof. exact (MK_COMB (@lem1547311 x y) (@lem1547312)). Qed.
Lemma lem1547314 (x : real) (y : real) : (term611 y x) = (term615 x y).
Proof. exact (TRANS (@lem1547276 y x) (@lem1547313 x y)). Qed.
Lemma lem1547315 (y : real) (x : real) : (term616 y x) = (term617 y x).
Proof. exact (@lem1483527 (term448 y x) term30). Qed.
Lemma lem1547316 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547323 (x : real) : (real_neg x) = (term47 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1547326 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1547327 (y : real) (x : real) : (term448 y x) = (term39 y x).
Proof. exact (MK_COMB (@lem1547326 y) (@lem1547323 x)). Qed.
Lemma lem1547328 (x : real) (y : real) : (term39 y x) = (term73 x y).
Proof. exact (@lem1483488 (term47 x) y). Qed.
Lemma lem1547329 (x : real) (y : real) : (term448 y x) = (term73 x y).
Proof. exact (TRANS (@lem1547327 y x) (@lem1547328 x y)). Qed.
Lemma lem1547330 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547331 (x : real) (y : real) : (term449 y x) = (term552 x y).
Proof. exact (MK_COMB (@lem1547330) (@lem1547329 x y)). Qed.
Lemma lem1547332 (x : real) (y : real) : (term451 y x) = (term353 x y).
Proof. exact (MK_COMB (@lem1547331 x y) (@lem1547316)). Qed.
Lemma lem1547333 (x : real) (y : real) : (term353 x y) = (term354 x y).
Proof. exact (@lem1483519 (term73 x y) term30). Qed.
Lemma lem1547335 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547336 : term114 = term30.
Proof. exact (@lem1547335 term66). Qed.
Lemma lem1547337 (x : real) (y : real) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem1547338 (x : real) (y : real) : (term354 x y) = (term356 x y).
Proof. exact (MK_COMB (@lem1547337 x y) (@lem1547336)). Qed.
Lemma lem1547339 (x : real) (y : real) : (term356 x y) = (term73 x y).
Proof. exact (@lem1483450 (term73 x y)). Qed.
Lemma lem1547340 (x : real) (y : real) : (term354 x y) = (term73 x y).
Proof. exact (TRANS (@lem1547338 x y) (@lem1547339 x y)). Qed.
Lemma lem1547341 (x : real) (y : real) : (term353 x y) = (term73 x y).
Proof. exact (TRANS (@lem1547333 x y) (@lem1547340 x y)). Qed.
Lemma lem1547342 (x : real) (y : real) : (term451 y x) = (term73 x y).
Proof. exact (TRANS (@lem1547332 x y) (@lem1547341 x y)). Qed.
Lemma lem1547343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1547344 (x : real) (y : real) : (term618 y x) = (term619 x y).
Proof. exact (MK_COMB (@lem1547343) (@lem1547342 x y)). Qed.
Lemma lem1547345 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547346 (x : real) (y : real) : (term617 y x) = (term550 x y).
Proof. exact (MK_COMB (@lem1547344 x y) (@lem1547345)). Qed.
Lemma lem1547347 (x : real) (y : real) : (term616 y x) = (term550 x y).
Proof. exact (TRANS (@lem1547315 y x) (@lem1547346 x y)). Qed.
Lemma lem1547348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547349 (x : real) (y : real) : (term620 y x) = (term621 x y).
Proof. exact (MK_COMB (@lem1547348) (@lem1547314 x y)). Qed.
Lemma lem1547350 (x : real) (y : real) : (term622 y x) = (term623 x y).
Proof. exact (MK_COMB (@lem1547349 x y) (@lem1547347 x y)). Qed.
Lemma lem1547351 (x : real) (y : real) : (term624 x y) = (term625 x y).
Proof. exact (@lem1483525 (term626 x y) term30). Qed.
Lemma lem1547352 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547359 (y : real) : (term165 y) = (term165 y).
Proof. exact (eq_refl (term165 y)). Qed.
Lemma lem1547366 (x : real) : (real_neg x) = (term47 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1547367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547368 (x : real) : (term627 x) = (term72 x).
Proof. exact (MK_COMB (@lem1547367) (@lem1547366 x)). Qed.
Lemma lem1547371 (x : real) (y : real) : (term628 x y) = (term629 x y).
Proof. exact (MK_COMB (@lem1547368 x) (@lem1547359 y)). Qed.
Lemma lem1547374 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1547375 (x : real) (y : real) : (term630 x y) = (term631 x y).
Proof. exact (MK_COMB (@lem1547374 y) (@lem1547371 x y)). Qed.
Lemma lem1547380 (x : real) (y : real) : (term631 x y) = (term632 x y).
Proof. exact (@lem1483484 (term47 x) y (term165 y)). Qed.
Lemma lem1547381 (x : real) (y : real) : (term630 x y) = (term632 x y).
Proof. exact (TRANS (@lem1547375 x y) (@lem1547380 x y)). Qed.
Lemma lem1547390 (x : real) : (term72 x) = (term72 x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem1547391 (x : real) (y : real) : (term626 x y) = (term633 x y).
Proof. exact (MK_COMB (@lem1547390 x) (@lem1547381 x y)). Qed.
Lemma lem1547392 (x : real) (y : real) : (term633 x y) = (term634 x y).
Proof. exact (@lem1483490 (term47 x) (term47 x) (term572 y)). Qed.
Lemma lem1547393 (x : real) : (term266 x) = (term267 x).
Proof. exact (@lem1483438 term59 term59 x). Qed.
Lemma lem1547394 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1547395 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547396 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547397 : term272 = term273.
Proof. exact (EQ_MP (@lem1547396) (@lem1547395)). Qed.
Lemma lem1547398 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547399 : term274 = term275.
Proof. exact (MK_COMB (@lem1547398) (@lem1547397)). Qed.
Lemma lem1547400 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1547401 : term269 = term276.
Proof. exact (MK_COMB (@lem1547400) (@lem1547399)). Qed.
Lemma lem1547402 : term268 = term276.
Proof. exact (TRANS (@lem1547394) (@lem1547401)). Qed.
Lemma lem1547403 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547404 : term277 = term278.
Proof. exact (MK_COMB (@lem1547403) (@lem1547402)). Qed.
Lemma lem1547405 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1547406 (x : real) : (term267 x) = (term279 x).
Proof. exact (MK_COMB (@lem1547404) (@lem1547405 x)). Qed.
Lemma lem1547407 (x : real) : (term266 x) = (term279 x).
Proof. exact (TRANS (@lem1547393 x) (@lem1547406 x)). Qed.
Lemma lem1547408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547409 (x : real) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem1547408) (@lem1547407 x)). Qed.
Lemma lem1547410 (y : real) : (term572 y) = (term572 y).
Proof. exact (eq_refl (term572 y)). Qed.
Lemma lem1547411 (x : real) (y : real) : (term634 x y) = (term635 x y).
Proof. exact (MK_COMB (@lem1547409 x) (@lem1547410 y)). Qed.
Lemma lem1547412 (x : real) (y : real) : (term633 x y) = (term635 x y).
Proof. exact (TRANS (@lem1547392 x y) (@lem1547411 x y)). Qed.
Lemma lem1547413 (x : real) (y : real) : (term626 x y) = (term635 x y).
Proof. exact (TRANS (@lem1547391 x y) (@lem1547412 x y)). Qed.
Lemma lem1547414 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547415 (x : real) (y : real) : (term636 x y) = (term637 x y).
Proof. exact (MK_COMB (@lem1547414) (@lem1547413 x y)). Qed.
Lemma lem1547416 (x : real) (y : real) : (term638 x y) = (term639 x y).
Proof. exact (MK_COMB (@lem1547415 x y) (@lem1547352)). Qed.
Lemma lem1547417 (x : real) (y : real) : (term639 x y) = (term640 x y).
Proof. exact (@lem1483519 (term635 x y) term30). Qed.
Lemma lem1547419 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547420 : term114 = term30.
Proof. exact (@lem1547419 term66). Qed.
Lemma lem1547421 (x : real) (y : real) : (term641 x y) = (term641 x y).
Proof. exact (eq_refl (term641 x y)). Qed.
Lemma lem1547422 (x : real) (y : real) : (term640 x y) = (term642 x y).
Proof. exact (MK_COMB (@lem1547421 x y) (@lem1547420)). Qed.
Lemma lem1547423 (x : real) (y : real) : (term642 x y) = (term635 x y).
Proof. exact (@lem1483450 (term635 x y)). Qed.
Lemma lem1547424 (x : real) (y : real) : (term640 x y) = (term635 x y).
Proof. exact (TRANS (@lem1547422 x y) (@lem1547423 x y)). Qed.
Lemma lem1547425 (x : real) (y : real) : (term639 x y) = (term635 x y).
Proof. exact (TRANS (@lem1547417 x y) (@lem1547424 x y)). Qed.
Lemma lem1547426 (x : real) (y : real) : (term638 x y) = (term635 x y).
Proof. exact (TRANS (@lem1547416 x y) (@lem1547425 x y)). Qed.
Lemma lem1547427 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547428 (x : real) (y : real) : (term643 x y) = (term644 x y).
Proof. exact (MK_COMB (@lem1547427) (@lem1547426 x y)). Qed.
Lemma lem1547429 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547430 (x : real) (y : real) : (term625 x y) = (term645 x y).
Proof. exact (MK_COMB (@lem1547428 x y) (@lem1547429)). Qed.
Lemma lem1547431 (x : real) (y : real) : (term624 x y) = (term645 x y).
Proof. exact (TRANS (@lem1547351 x y) (@lem1547430 x y)). Qed.
Lemma lem1547432 (x : real) (y : real) : (term646 x y) = (term647 x y).
Proof. exact (@lem1483525 (term648 x y) term30). Qed.
Lemma lem1547433 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547440 (y : real) : (term165 y) = (term165 y).
Proof. exact (eq_refl (term165 y)). Qed.
Lemma lem1547447 (x : real) : (real_neg x) = (term47 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1547448 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547449 (x : real) : (term627 x) = (term72 x).
Proof. exact (MK_COMB (@lem1547448) (@lem1547447 x)). Qed.
Lemma lem1547452 (x : real) (y : real) : (term628 x y) = (term629 x y).
Proof. exact (MK_COMB (@lem1547449 x) (@lem1547440 y)). Qed.
Lemma lem1547461 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1547462 (x : real) (y : real) : (term649 x y) = (term650 x y).
Proof. exact (MK_COMB (@lem1547461 y) (@lem1547452 x y)). Qed.
Lemma lem1547467 (x : real) (y : real) : (term650 x y) = (term651 x y).
Proof. exact (@lem1483484 (term47 x) (term47 y) (term165 y)). Qed.
Lemma lem1547468 (x : real) (y : real) : (term649 x y) = (term651 x y).
Proof. exact (TRANS (@lem1547462 x y) (@lem1547467 x y)). Qed.
Lemma lem1547471 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1547472 (x : real) (y : real) : (term648 x y) = (term652 x y).
Proof. exact (MK_COMB (@lem1547471 x) (@lem1547468 x y)). Qed.
Lemma lem1547473 (x : real) (y : real) : (term652 x y) = (term653 x y).
Proof. exact (@lem1483490 x (term47 x) (term591 y)). Qed.
Lemma lem1547474 (x : real) : (term316 x) = (term249 x).
Proof. exact (@lem1483442 term59 x). Qed.
Lemma lem1547476 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547477 : term251 = term30.
Proof. exact (@lem1547476 term66). Qed.
Lemma lem1547478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547479 : term252 = term253.
Proof. exact (MK_COMB (@lem1547478) (@lem1547477)). Qed.
Lemma lem1547480 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1547481 (x : real) : (term249 x) = (term254 x).
Proof. exact (MK_COMB (@lem1547479) (@lem1547480 x)). Qed.
Lemma lem1547482 (x : real) : (term316 x) = (term254 x).
Proof. exact (TRANS (@lem1547474 x) (@lem1547481 x)). Qed.
Lemma lem1547483 (x : real) : (term254 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1547484 (x : real) : (term316 x) = term30.
Proof. exact (TRANS (@lem1547482 x) (@lem1547483 x)). Qed.
Lemma lem1547485 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1547486 (x : real) : (term317 x) = term171.
Proof. exact (MK_COMB (@lem1547485) (@lem1547484 x)). Qed.
Lemma lem1547487 (y : real) : (term591 y) = (term591 y).
Proof. exact (eq_refl (term591 y)). Qed.
Lemma lem1547488 (x : real) (y : real) : (term653 x y) = (term654 y).
Proof. exact (MK_COMB (@lem1547486 x) (@lem1547487 y)). Qed.
Lemma lem1547489 (x : real) (y : real) : (term652 x y) = (term654 y).
Proof. exact (TRANS (@lem1547473 x y) (@lem1547488 x y)). Qed.
Lemma lem1547490 (y : real) : (term654 y) = (term591 y).
Proof. exact (@lem1483448 (term591 y)). Qed.
Lemma lem1547491 (x : real) (y : real) : (term652 x y) = (term591 y).
Proof. exact (TRANS (@lem1547489 x y) (@lem1547490 y)). Qed.
Lemma lem1547492 (x : real) (y : real) : (term648 x y) = (term591 y).
Proof. exact (TRANS (@lem1547472 x y) (@lem1547491 x y)). Qed.
Lemma lem1547493 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1547494 (x : real) (y : real) : (term655 x y) = (term656 y).
Proof. exact (MK_COMB (@lem1547493) (@lem1547492 x y)). Qed.
Lemma lem1547495 (x : real) (y : real) : (term657 x y) = (term658 y).
Proof. exact (MK_COMB (@lem1547494 x y) (@lem1547433)). Qed.
Lemma lem1547496 (y : real) : (term658 y) = (term659 y).
Proof. exact (@lem1483519 (term591 y) term30). Qed.
Lemma lem1547498 (x : nat) : (term113 x) = term30.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1547499 : term114 = term30.
Proof. exact (@lem1547498 term66). Qed.
Lemma lem1547500 (y : real) : (term660 y) = (term660 y).
Proof. exact (eq_refl (term660 y)). Qed.
Lemma lem1547501 (y : real) : (term659 y) = (term661 y).
Proof. exact (MK_COMB (@lem1547500 y) (@lem1547499)). Qed.
Lemma lem1547502 (y : real) : (term661 y) = (term591 y).
Proof. exact (@lem1483450 (term591 y)). Qed.
Lemma lem1547503 (y : real) : (term659 y) = (term591 y).
Proof. exact (TRANS (@lem1547501 y) (@lem1547502 y)). Qed.
Lemma lem1547504 (y : real) : (term658 y) = (term591 y).
Proof. exact (TRANS (@lem1547496 y) (@lem1547503 y)). Qed.
Lemma lem1547505 (x : real) (y : real) : (term657 x y) = (term591 y).
Proof. exact (TRANS (@lem1547495 x y) (@lem1547504 y)). Qed.
Lemma lem1547506 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547507 (x : real) (y : real) : (term662 x y) = (term663 y).
Proof. exact (MK_COMB (@lem1547506) (@lem1547505 x y)). Qed.
Lemma lem1547508 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547509 (x : real) (y : real) : (term647 x y) = (term664 y).
Proof. exact (MK_COMB (@lem1547507 x y) (@lem1547508)). Qed.
Lemma lem1547510 (x : real) (y : real) : (term646 x y) = (term664 y).
Proof. exact (TRANS (@lem1547432 x y) (@lem1547509 x y)). Qed.
Lemma lem1547511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547512 (x : real) (y : real) : (term665 x y) = (term666 x y).
Proof. exact (MK_COMB (@lem1547511) (@lem1547431 x y)). Qed.
Lemma lem1547513 (x : real) (y : real) : (term667 x y) = (term668 x y).
Proof. exact (MK_COMB (@lem1547512 x y) (@lem1547510 x y)). Qed.
Lemma lem1547514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547515 (x : real) (y : real) : (term669 y x) = (term670 x y).
Proof. exact (MK_COMB (@lem1547514) (@lem1547350 x y)). Qed.
Lemma lem1547516 (x : real) (y : real) : (term539 x y) = (term671 x y).
Proof. exact (MK_COMB (@lem1547515 x y) (@lem1547513 x y)). Qed.
Lemma lem1547517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547518 (x : real) : (term333 x) = (term515 x).
Proof. exact (MK_COMB (@lem1547517) (@lem1547275 x)). Qed.
Lemma lem1547519 (x : real) (y : real) : (term541 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem1547518 x) (@lem1547516 x y)). Qed.
Lemma lem1547520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1547521 (x : real) (y : real) : (term547 x y) = (term673 x y).
Proof. exact (MK_COMB (@lem1547520) (@lem1547256 x y)). Qed.
Lemma lem1547522 (x : real) (y : real) : (term548 x y) = (term674 x y).
Proof. exact (MK_COMB (@lem1547521 x y) (@lem1547519 x y)). Qed.
Lemma lem1547523 (x : real) (y : real) : (term534 x y) = (term674 x y).
Proof. exact (TRANS (@lem1547017 x y) (@lem1547522 x y)). Qed.
Lemma lem1547525 (a : real) (b : real) (x : real) (r : real) : (term675 a b x r) = (term676 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1547526 (x : real) (y : real) : (term645 x y) = (term677 x y).
Proof. exact (@lem1547525 (term279 x) y y term30). Qed.
Lemma lem1547533 (y : real) : (term71 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1547536 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1547537 (y : real) : (term678 y) = (real_add y y).
Proof. exact (MK_COMB (@lem1547536 y) (@lem1547533 y)). Qed.
Lemma lem1547538 (y : real) : (real_add y y) = (term299 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1547539 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1547540 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547541 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547542 : term272 = term273.
Proof. exact (EQ_MP (@lem1547541) (@lem1547540)). Qed.
Lemma lem1547543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547544 : term274 = term275.
Proof. exact (MK_COMB (@lem1547543) (@lem1547542)). Qed.
Lemma lem1547545 : term300 = term275.
Proof. exact (TRANS (@lem1547539) (@lem1547544)). Qed.
Lemma lem1547546 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547547 : term301 = term302.
Proof. exact (MK_COMB (@lem1547546) (@lem1547545)). Qed.
Lemma lem1547548 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547549 (y : real) : (term299 y) = (term303 y).
Proof. exact (MK_COMB (@lem1547547) (@lem1547548 y)). Qed.
Lemma lem1547550 (y : real) : (real_add y y) = (term303 y).
Proof. exact (TRANS (@lem1547538 y) (@lem1547549 y)). Qed.
Lemma lem1547551 (y : real) : (term678 y) = (term303 y).
Proof. exact (TRANS (@lem1547537 y) (@lem1547550 y)). Qed.
Lemma lem1547560 (x : real) : (term281 x) = (term281 x).
Proof. exact (eq_refl (term281 x)). Qed.
Lemma lem1547563 (x : real) (y : real) : (term679 x y) = (term372 x y).
Proof. exact (MK_COMB (@lem1547560 x) (@lem1547551 y)). Qed.
Lemma lem1547564 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547565 (x : real) (y : real) : (term680 x y) = (term381 x y).
Proof. exact (MK_COMB (@lem1547564) (@lem1547563 x y)). Qed.
Lemma lem1547566 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547567 (x : real) (y : real) : (term681 x y) = (term382 x y).
Proof. exact (MK_COMB (@lem1547565 x y) (@lem1547566)). Qed.
Lemma lem1547579 (y : real) : (term316 y) = (term249 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1547581 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547582 : term251 = term30.
Proof. exact (@lem1547581 term66). Qed.
Lemma lem1547583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547584 : term252 = term253.
Proof. exact (MK_COMB (@lem1547583) (@lem1547582)). Qed.
Lemma lem1547585 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547586 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1547584) (@lem1547585 y)). Qed.
Lemma lem1547587 (y : real) : (term316 y) = (term254 y).
Proof. exact (TRANS (@lem1547579 y) (@lem1547586 y)). Qed.
Lemma lem1547588 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1547590 (y : real) : (term316 y) = term30.
Proof. exact (TRANS (@lem1547587 y) (@lem1547588 y)). Qed.
Lemma lem1547599 (x : real) : (term281 x) = (term281 x).
Proof. exact (eq_refl (term281 x)). Qed.
Lemma lem1547600 (y : real) (x : real) : (term682 x y) = (term467 x).
Proof. exact (MK_COMB (@lem1547599 x) (@lem1547590 y)). Qed.
Lemma lem1547601 (x : real) : (term467 x) = (term279 x).
Proof. exact (@lem1483450 (term279 x)). Qed.
Lemma lem1547602 (y : real) (x : real) : (term682 x y) = (term279 x).
Proof. exact (TRANS (@lem1547600 y x) (@lem1547601 x)). Qed.
Lemma lem1547603 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547604 (y : real) (x : real) : (term683 x y) = (term474 x).
Proof. exact (MK_COMB (@lem1547603) (@lem1547602 y x)). Qed.
Lemma lem1547605 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547606 (y : real) (x : real) : (term684 x y) = (term475 x).
Proof. exact (MK_COMB (@lem1547604 y x) (@lem1547605)). Qed.
Lemma lem1547607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547608 (y : real) (x : real) : (term685 x y) = (term482 x).
Proof. exact (MK_COMB (@lem1547607) (@lem1547606 y x)). Qed.
Lemma lem1547609 (x : real) (y : real) : (term677 x y) = (term686 x y).
Proof. exact (MK_COMB (@lem1547608 y x) (@lem1547567 x y)). Qed.
Lemma lem1547610 (x : real) (y : real) : (term645 x y) = (term686 x y).
Proof. exact (TRANS (@lem1547526 x y) (@lem1547609 x y)). Qed.
Lemma lem1547611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547612 (x : real) (y : real) : (term666 x y) = (term687 x y).
Proof. exact (MK_COMB (@lem1547611) (@lem1547610 x y)). Qed.
Lemma lem1547614 (a : real) (x : real) (r : real) : (term688 a x r) = (term37 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1547615 (y : real) : (term664 y) = (term689 y).
Proof. exact (@lem1547614 (term47 y) y term30). Qed.
Lemma lem1547622 (y : real) : (term71 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1547631 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1547632 (y : real) : (term690 y) = (term248 y).
Proof. exact (MK_COMB (@lem1547631 y) (@lem1547622 y)). Qed.
Lemma lem1547633 (y : real) : (term248 y) = (term249 y).
Proof. exact (@lem1483440 term59 y). Qed.
Lemma lem1547635 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547636 : term251 = term30.
Proof. exact (@lem1547635 term66). Qed.
Lemma lem1547637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547638 : term252 = term253.
Proof. exact (MK_COMB (@lem1547637) (@lem1547636)). Qed.
Lemma lem1547639 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547640 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1547638) (@lem1547639 y)). Qed.
Lemma lem1547641 (y : real) : (term248 y) = (term254 y).
Proof. exact (TRANS (@lem1547633 y) (@lem1547640 y)). Qed.
Lemma lem1547642 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1547643 (y : real) : (term248 y) = term30.
Proof. exact (TRANS (@lem1547641 y) (@lem1547642 y)). Qed.
Lemma lem1547644 (y : real) : (term690 y) = term30.
Proof. exact (TRANS (@lem1547632 y) (@lem1547643 y)). Qed.
Lemma lem1547645 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547646 (y : real) : (term691 y) = term406.
Proof. exact (MK_COMB (@lem1547645) (@lem1547644 y)). Qed.
Lemma lem1547647 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547648 (y : real) : (term692 y) = term407.
Proof. exact (MK_COMB (@lem1547646 y) (@lem1547647)). Qed.
Lemma lem1547666 (y : real) : (term266 y) = (term267 y).
Proof. exact (@lem1483438 term59 term59 y). Qed.
Lemma lem1547667 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1547668 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547669 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547670 : term272 = term273.
Proof. exact (EQ_MP (@lem1547669) (@lem1547668)). Qed.
Lemma lem1547671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547672 : term274 = term275.
Proof. exact (MK_COMB (@lem1547671) (@lem1547670)). Qed.
Lemma lem1547673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1547674 : term269 = term276.
Proof. exact (MK_COMB (@lem1547673) (@lem1547672)). Qed.
Lemma lem1547675 : term268 = term276.
Proof. exact (TRANS (@lem1547667) (@lem1547674)). Qed.
Lemma lem1547676 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547677 : term277 = term278.
Proof. exact (MK_COMB (@lem1547676) (@lem1547675)). Qed.
Lemma lem1547678 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547679 (y : real) : (term267 y) = (term279 y).
Proof. exact (MK_COMB (@lem1547677) (@lem1547678 y)). Qed.
Lemma lem1547681 (y : real) : (term266 y) = (term279 y).
Proof. exact (TRANS (@lem1547666 y) (@lem1547679 y)). Qed.
Lemma lem1547682 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547683 (y : real) : (term693 y) = (term474 y).
Proof. exact (MK_COMB (@lem1547682) (@lem1547681 y)). Qed.
Lemma lem1547684 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547685 (y : real) : (term694 y) = (term475 y).
Proof. exact (MK_COMB (@lem1547683 y) (@lem1547684)). Qed.
Lemma lem1547686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547687 (y : real) : (term695 y) = (term482 y).
Proof. exact (MK_COMB (@lem1547686) (@lem1547685 y)). Qed.
Lemma lem1547688 (y : real) : (term689 y) = (term484 y).
Proof. exact (MK_COMB (@lem1547687 y) (@lem1547648 y)). Qed.
Lemma lem1547689 (y : real) : (term664 y) = (term484 y).
Proof. exact (TRANS (@lem1547615 y) (@lem1547688 y)). Qed.
Lemma lem1547690 (x : real) (y : real) : (term668 x y) = (term696 x y).
Proof. exact (MK_COMB (@lem1547612 x y) (@lem1547689 y)). Qed.
Lemma lem1547691 (x : real) (y : real) : (term670 x y) = (term670 x y).
Proof. exact (eq_refl (term670 x y)). Qed.
Lemma lem1547692 (x : real) (y : real) : (term671 x y) = (term697 x y).
Proof. exact (MK_COMB (@lem1547691 x y) (@lem1547690 x y)). Qed.
Lemma lem1547693 (x : real) : (term515 x) = (term515 x).
Proof. exact (eq_refl (term515 x)). Qed.
Lemma lem1547696 (x : real) (y : real) : (term672 x y) = (term698 x y).
Proof. exact (MK_COMB (@lem1547693 x) (@lem1547692 x y)). Qed.
Lemma lem1547698 (a : real) (x : real) (r : real) : (term688 a x r) = (term37 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1547699 (y : real) : (term583 y) = (term699 y).
Proof. exact (@lem1547698 y y term30). Qed.
Lemma lem1547706 (y : real) : (term71 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1547709 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1547710 (y : real) : (term678 y) = (real_add y y).
Proof. exact (MK_COMB (@lem1547709 y) (@lem1547706 y)). Qed.
Lemma lem1547711 (y : real) : (real_add y y) = (term299 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1547712 : term300 = term274.
Proof. exact (@lem1367770 term66 term66). Qed.
Lemma lem1547713 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547714 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547715 : term272 = term273.
Proof. exact (EQ_MP (@lem1547714) (@lem1547713)). Qed.
Lemma lem1547716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547717 : term274 = term275.
Proof. exact (MK_COMB (@lem1547716) (@lem1547715)). Qed.
Lemma lem1547718 : term300 = term275.
Proof. exact (TRANS (@lem1547712) (@lem1547717)). Qed.
Lemma lem1547719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547720 : term301 = term302.
Proof. exact (MK_COMB (@lem1547719) (@lem1547718)). Qed.
Lemma lem1547721 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547722 (y : real) : (term299 y) = (term303 y).
Proof. exact (MK_COMB (@lem1547720) (@lem1547721 y)). Qed.
Lemma lem1547723 (y : real) : (real_add y y) = (term303 y).
Proof. exact (TRANS (@lem1547711 y) (@lem1547722 y)). Qed.
Lemma lem1547724 (y : real) : (term678 y) = (term303 y).
Proof. exact (TRANS (@lem1547710 y) (@lem1547723 y)). Qed.
Lemma lem1547725 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547726 (y : real) : (term700 y) = (term392 y).
Proof. exact (MK_COMB (@lem1547725) (@lem1547724 y)). Qed.
Lemma lem1547727 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547728 (y : real) : (term701 y) = (term393 y).
Proof. exact (MK_COMB (@lem1547726 y) (@lem1547727)). Qed.
Lemma lem1547740 (y : real) : (term316 y) = (term249 y).
Proof. exact (@lem1483442 term59 y). Qed.
Lemma lem1547742 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547743 : term251 = term30.
Proof. exact (@lem1547742 term66). Qed.
Lemma lem1547744 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547745 : term252 = term253.
Proof. exact (MK_COMB (@lem1547744) (@lem1547743)). Qed.
Lemma lem1547746 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547747 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1547745) (@lem1547746 y)). Qed.
Lemma lem1547748 (y : real) : (term316 y) = (term254 y).
Proof. exact (TRANS (@lem1547740 y) (@lem1547747 y)). Qed.
Lemma lem1547749 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1547751 (y : real) : (term316 y) = term30.
Proof. exact (TRANS (@lem1547748 y) (@lem1547749 y)). Qed.
Lemma lem1547752 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547753 (y : real) : (term702 y) = term406.
Proof. exact (MK_COMB (@lem1547752) (@lem1547751 y)). Qed.
Lemma lem1547754 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547755 (y : real) : (term703 y) = term407.
Proof. exact (MK_COMB (@lem1547753 y) (@lem1547754)). Qed.
Lemma lem1547756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547757 (y : real) : (term704 y) = term415.
Proof. exact (MK_COMB (@lem1547756) (@lem1547755 y)). Qed.
Lemma lem1547758 (y : real) : (term699 y) = (term417 y).
Proof. exact (MK_COMB (@lem1547757 y) (@lem1547728 y)). Qed.
Lemma lem1547759 (y : real) : (term583 y) = (term417 y).
Proof. exact (TRANS (@lem1547699 y) (@lem1547758 y)). Qed.
Lemma lem1547760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547761 (y : real) : (term604 y) = (term705 y).
Proof. exact (MK_COMB (@lem1547760) (@lem1547759 y)). Qed.
Lemma lem1547763 (a : real) (b : real) (x : real) (r : real) : (term675 a b x r) = (term676 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1547764 (x : real) (y : real) : (term602 x y) = (term706 x y).
Proof. exact (@lem1547763 (term303 x) (term47 y) y term30). Qed.
Lemma lem1547771 (y : real) : (term71 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1547780 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1547781 (y : real) : (term690 y) = (term248 y).
Proof. exact (MK_COMB (@lem1547780 y) (@lem1547771 y)). Qed.
Lemma lem1547782 (y : real) : (term248 y) = (term249 y).
Proof. exact (@lem1483440 term59 y). Qed.
Lemma lem1547784 (m : nat) : (term250 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1547785 : term251 = term30.
Proof. exact (@lem1547784 term66). Qed.
Lemma lem1547786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547787 : term252 = term253.
Proof. exact (MK_COMB (@lem1547786) (@lem1547785)). Qed.
Lemma lem1547788 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547789 (y : real) : (term249 y) = (term254 y).
Proof. exact (MK_COMB (@lem1547787) (@lem1547788 y)). Qed.
Lemma lem1547790 (y : real) : (term248 y) = (term254 y).
Proof. exact (TRANS (@lem1547782 y) (@lem1547789 y)). Qed.
Lemma lem1547791 (y : real) : (term254 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1547792 (y : real) : (term248 y) = term30.
Proof. exact (TRANS (@lem1547790 y) (@lem1547791 y)). Qed.
Lemma lem1547793 (y : real) : (term690 y) = term30.
Proof. exact (TRANS (@lem1547781 y) (@lem1547792 y)). Qed.
Lemma lem1547802 (x : real) : (term305 x) = (term305 x).
Proof. exact (eq_refl (term305 x)). Qed.
Lemma lem1547803 (y : real) (x : real) : (term707 x y) = (term390 x).
Proof. exact (MK_COMB (@lem1547802 x) (@lem1547793 y)). Qed.
Lemma lem1547804 (x : real) : (term390 x) = (term303 x).
Proof. exact (@lem1483450 (term303 x)). Qed.
Lemma lem1547805 (y : real) (x : real) : (term707 x y) = (term303 x).
Proof. exact (TRANS (@lem1547803 y x) (@lem1547804 x)). Qed.
Lemma lem1547806 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547807 (y : real) (x : real) : (term708 x y) = (term392 x).
Proof. exact (MK_COMB (@lem1547806) (@lem1547805 y x)). Qed.
Lemma lem1547808 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547809 (y : real) (x : real) : (term709 x y) = (term393 x).
Proof. exact (MK_COMB (@lem1547807 y x) (@lem1547808)). Qed.
Lemma lem1547827 (y : real) : (term266 y) = (term267 y).
Proof. exact (@lem1483438 term59 term59 y). Qed.
Lemma lem1547828 : term268 = term269.
Proof. exact (@lem1367763 term66 term66). Qed.
Lemma lem1547829 : term270 = term271.
Proof. exact (@lem706885). Qed.
Lemma lem1547830 : (term270 = term271) = (term272 = term273).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term271). Qed.
Lemma lem1547831 : term272 = term273.
Proof. exact (EQ_MP (@lem1547830) (@lem1547829)). Qed.
Lemma lem1547832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1547833 : term274 = term275.
Proof. exact (MK_COMB (@lem1547832) (@lem1547831)). Qed.
Lemma lem1547834 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1547835 : term269 = term276.
Proof. exact (MK_COMB (@lem1547834) (@lem1547833)). Qed.
Lemma lem1547836 : term268 = term276.
Proof. exact (TRANS (@lem1547828) (@lem1547835)). Qed.
Lemma lem1547837 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1547838 : term277 = term278.
Proof. exact (MK_COMB (@lem1547837) (@lem1547836)). Qed.
Lemma lem1547839 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1547840 (y : real) : (term267 y) = (term279 y).
Proof. exact (MK_COMB (@lem1547838) (@lem1547839 y)). Qed.
Lemma lem1547842 (y : real) : (term266 y) = (term279 y).
Proof. exact (TRANS (@lem1547827 y) (@lem1547840 y)). Qed.
Lemma lem1547851 (x : real) : (term305 x) = (term305 x).
Proof. exact (eq_refl (term305 x)). Qed.
Lemma lem1547854 (x : real) (y : real) : (term710 x y) = (term494 x y).
Proof. exact (MK_COMB (@lem1547851 x) (@lem1547842 y)). Qed.
Lemma lem1547855 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1547856 (x : real) (y : real) : (term711 x y) = (term503 x y).
Proof. exact (MK_COMB (@lem1547855) (@lem1547854 x y)). Qed.
Lemma lem1547857 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1547858 (x : real) (y : real) : (term712 x y) = (term504 x y).
Proof. exact (MK_COMB (@lem1547856 x y) (@lem1547857)). Qed.
Lemma lem1547859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1547860 (x : real) (y : real) : (term713 x y) = (term714 x y).
Proof. exact (MK_COMB (@lem1547859) (@lem1547858 x y)). Qed.
Lemma lem1547861 (y : real) (x : real) : (term706 x y) = (term715 y x).
Proof. exact (MK_COMB (@lem1547860 x y) (@lem1547809 y x)). Qed.
Lemma lem1547862 (y : real) (x : real) : (term602 x y) = (term715 y x).
Proof. exact (TRANS (@lem1547764 x y) (@lem1547861 y x)). Qed.
Lemma lem1547863 (y : real) (x : real) : (term606 x y) = (term716 y x).
Proof. exact (MK_COMB (@lem1547761 y) (@lem1547862 y x)). Qed.
Lemma lem1547864 (x : real) (y : real) : (term608 x y) = (term608 x y).
Proof. exact (eq_refl (term608 x y)). Qed.
Lemma lem1547865 (y : real) (x : real) : (term609 x y) = (term717 y x).
Proof. exact (MK_COMB (@lem1547864 x y) (@lem1547863 y x)). Qed.
Lemma lem1547866 (x : real) : (term338 x) = (term338 x).
Proof. exact (eq_refl (term338 x)). Qed.
Lemma lem1547869 (y : real) (x : real) : (term610 x y) = (term718 y x).
Proof. exact (MK_COMB (@lem1547866 x) (@lem1547865 y x)). Qed.
Lemma lem1547870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1547871 (y : real) (x : real) : (term673 x y) = (term719 y x).
Proof. exact (MK_COMB (@lem1547870) (@lem1547869 y x)). Qed.
Lemma lem1547872 (x : real) (y : real) : (term674 x y) = (term720 x y).
Proof. exact (MK_COMB (@lem1547871 y x) (@lem1547696 x y)). Qed.
Lemma lem1547873 (x : real) (y : real) : (term534 x y) = (term720 x y).
Proof. exact (TRANS (@lem1547523 x y) (@lem1547872 x y)). Qed.
Lemma lem1547874 (x : real) (y : real) : (term156 x y) = (term720 x y).
Proof. exact (TRANS (@lem1547001 x y) (@lem1547873 x y)). Qed.
Lemma lem1547875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1547876 (x : real) (y : real) : (term215 x y) = (term721 x y).
Proof. exact (MK_COMB (@lem1547875) (@lem1547874 x y)). Qed.
Lemma lem1547877 (x : real) (y : real) : (term216 x y) = (term722 x y).
Proof. exact (MK_COMB (@lem1547876 x y) (@lem1546956 x y)). Qed.
Lemma lem1547878 (x : real) (y : real) : (term86 x y) = (term722 x y).
Proof. exact (TRANS (@lem1546022 x y) (@lem1547877 x y)). Qed.
Lemma lem1547879 (x : real) (y : real) : (term31 x y) = (term722 x y).
Proof. exact (TRANS (@lem1545647 x y) (@lem1547878 x y)). Qed.
Lemma lem1547880 (x : real) (y : real) (h1 : term722 x y) : term722 x y.
Proof. exact (h1). Qed.
Lemma lem1547881 (x : real) (y : real) (h1 : term720 x y) : term720 x y.
Proof. exact (h1). Qed.
Lemma lem1547882 (y : real) (x : real) (h1 : term718 y x) : term718 y x.
Proof. exact (h1). Qed.
Lemma lem1547883 (y : real) (x : real) (h1 : term718 y x) : term717 y x.
Proof. exact (proj2 (@lem1547882 y x h1)). Qed.
Lemma lem1547885 (y : real) (x : real) (h1 : term718 y x) : term716 y x.
Proof. exact (proj2 (@lem1547883 y x h1)). Qed.
Lemma lem1547890 (y : real) (x : real) (h1 : term718 y x) : term417 y.
Proof. exact (proj1 (@lem1547885 y x h1)). Qed.
Lemma lem1547892 (y : real) (x : real) (h1 : term718 y x) : term407.
Proof. exact (proj1 (@lem1547890 y x h1)). Qed.
Lemma lem1547896 (n : nat) (m : nat) : (term723 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1547897 : term407 = term724.
Proof. exact (@lem1547896 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1547898 : term724 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1547899 : term407 = False.
Proof. exact (TRANS (@lem1547897) (@lem1547898)). Qed.
Lemma lem1547900 (y : real) (x : real) (h1 : term718 y x) : False.
Proof. exact (EQ_MP (@lem1547899) (@lem1547892 y x h1)). Qed.
Lemma lem1547901 (x : real) (y : real) (h1 : term698 x y) : term698 x y.
Proof. exact (h1). Qed.
Lemma lem1547902 (x : real) (y : real) (h1 : term698 x y) : term697 x y.
Proof. exact (proj2 (@lem1547901 x y h1)). Qed.
Lemma lem1547904 (x : real) (y : real) (h1 : term698 x y) : term696 x y.
Proof. exact (proj2 (@lem1547902 x y h1)). Qed.
Lemma lem1547908 (x : real) (y : real) (h1 : term698 x y) : term484 y.
Proof. exact (proj2 (@lem1547904 x y h1)). Qed.
Lemma lem1547912 (x : real) (y : real) (h1 : term698 x y) : term407.
Proof. exact (proj2 (@lem1547908 x y h1)). Qed.
Lemma lem1547915 (n : nat) (m : nat) : (term723 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1547916 : term407 = term724.
Proof. exact (@lem1547915 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1547917 : term724 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1547918 : term407 = False.
Proof. exact (TRANS (@lem1547916) (@lem1547917)). Qed.
Lemma lem1547919 (x : real) (y : real) (h1 : term698 x y) : False.
Proof. exact (EQ_MP (@lem1547918) (@lem1547912 x y h1)). Qed.
Lemma lem1547920 (x : real) (y : real) (h1 : term720 x y) : False.
Proof. exact (or_elim (@lem1547881 x y h1) (fun h0 : term718 y x => @lem1547900 y x h0) (fun h0 : term698 x y => @lem1547919 x y h0)). Qed.
Lemma lem1547921 (x : real) (y : real) (h1 : term518 x y) : term518 x y.
Proof. exact (h1). Qed.
Lemma lem1547922 (y : real) (x : real) (h1 : term424 y x) : term424 y x.
Proof. exact (h1). Qed.
Lemma lem1547923 (y : real) (x : real) (h1 : term424 y x) : term423 y x.
Proof. exact (proj2 (@lem1547922 y x h1)). Qed.
Lemma lem1547925 (y : real) (x : real) (h1 : term424 y x) : term421 y x.
Proof. exact (proj2 (@lem1547923 y x h1)). Qed.
Lemma lem1547929 (y : real) (x : real) (h1 : term424 y x) : term417 x.
Proof. exact (proj2 (@lem1547925 y x h1)). Qed.
Lemma lem1547934 (y : real) (x : real) (h1 : term424 y x) : term407.
Proof. exact (proj1 (@lem1547929 y x h1)). Qed.
Lemma lem1547936 (n : nat) (m : nat) : (term723 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1547937 : term407 = term724.
Proof. exact (@lem1547936 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1547938 : term724 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1547939 : term407 = False.
Proof. exact (TRANS (@lem1547937) (@lem1547938)). Qed.
Lemma lem1547940 (y : real) (x : real) (h1 : term424 y x) : False.
Proof. exact (EQ_MP (@lem1547939) (@lem1547934 y x h1)). Qed.
Lemma lem1547941 (x : real) (y : real) (h1 : term516 x y) : term516 x y.
Proof. exact (h1). Qed.
Lemma lem1547942 (x : real) (y : real) (h1 : term516 x y) : term514 x y.
Proof. exact (proj2 (@lem1547941 x y h1)). Qed.
Lemma lem1547944 (x : real) (y : real) (h1 : term516 x y) : term511 x y.
Proof. exact (proj2 (@lem1547942 x y h1)). Qed.
Lemma lem1547949 (x : real) (y : real) (h1 : term516 x y) : term484 x.
Proof. exact (proj1 (@lem1547944 x y h1)). Qed.
Lemma lem1547950 (x : real) (y : real) (h1 : term516 x y) : term407.
Proof. exact (proj2 (@lem1547949 x y h1)). Qed.
Lemma lem1547955 (n : nat) (m : nat) : (term723 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1547956 : term407 = term724.
Proof. exact (@lem1547955 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1547957 : term724 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1547958 : term407 = False.
Proof. exact (TRANS (@lem1547956) (@lem1547957)). Qed.
Lemma lem1547959 (x : real) (y : real) (h1 : term516 x y) : False.
Proof. exact (EQ_MP (@lem1547958) (@lem1547950 x y h1)). Qed.
Lemma lem1547960 (x : real) (y : real) (h1 : term518 x y) : False.
Proof. exact (or_elim (@lem1547921 x y h1) (fun h0 : term424 y x => @lem1547940 y x h0) (fun h0 : term516 x y => @lem1547959 x y h0)). Qed.
Lemma lem1547961 (x : real) (y : real) (h1 : term722 x y) : False.
Proof. exact (or_elim (@lem1547880 x y h1) (fun h0 : term720 x y => @lem1547920 x y h0) (fun h0 : term518 x y => @lem1547960 x y h0)). Qed.
Lemma lem1547962 (x : real) (y : real) (h1 : term31 x y) : term31 x y.
Proof. exact (h1). Qed.
Lemma lem1547963 (x : real) (y : real) (h1 : term31 x y) : term722 x y.
Proof. exact (EQ_MP (@lem1547879 x y) (@lem1547962 x y h1)). Qed.
Lemma lem1547964 (x : real) (y : real) (h1 : term31 x y) : (term722 x y) = False.
Proof. exact (prop_ext (fun h2 : term722 x y => @lem1547961 x y h2) (fun h2 : False => @lem1547963 x y h1)). Qed.
Lemma lem1547965 (x : real) (y : real) (h1 : term31 x y) : False.
Proof. exact (EQ_MP (@lem1547964 x y h1) (@lem1547963 x y h1)). Qed.
Lemma lem1547966 (x : real) (h1 : term33 x) : term33 x.
Proof. exact (h1). Qed.
Lemma lem1547967 (x : real) (h1 : term33 x) : False.
Proof. exact (ex_elim (@lem1547966 x h1) (fun y : real => fun h0 : term32 x y => @lem1547965 x y h0)). Qed.
Lemma lem1547968 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1547969 (h1 : term35) : False.
Proof. exact (ex_elim (@lem1547968 h1) (fun x : real => fun h0 : term34 x => @lem1547967 x h0)). Qed.
Lemma lem1547970 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1547971 (h1 : term12) : term35.
Proof. exact (EQ_MP (@lem1545553) (@lem1547970 h1)). Qed.
Lemma lem1547972 (h1 : term12) : term35 = False.
Proof. exact (prop_ext (fun h2 : term35 => @lem1547969 h2) (fun h2 : False => @lem1547971 h1)). Qed.
Lemma lem1547973 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1547972 h1) (@lem1547971 h1)). Qed.
Lemma lem1547974 : term725.
Proof. exact (fun h0 : term12 => @lem1547973 h0). Qed.
Lemma lem1547975 : term726.
Proof. exact (@lem1386578 term727). Qed.
Lemma lem1547976 : term727.
Proof. exact (@lem1547975 (@lem1547974)). Qed.

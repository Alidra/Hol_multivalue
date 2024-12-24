Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ENTIRE_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1340174_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm82_spec.
Lemma lem1382498 (x : real) : term0 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1382499 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1382501 (x : real) : term3 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1382502 (x : real) : (term3 x) = ((term4 x) = x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1382504 (x : real) : term5 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1382505 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1382506 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1382505 x) (@lem1382504 x)). Qed.
Lemma lem1382507 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1382506 x y). Qed.
Lemma lem1382508 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1382509 (x : real) (y : real) : term8 x y.
Proof. exact (EQ_MP (@lem1382508 x y) (@lem1382507 x y)). Qed.
Lemma lem1382510 (x : real) (y : real) (z : real) : term9 x y z.
Proof. exact (@lem1382509 x y z). Qed.
Lemma lem1382511 (x : real) (y : real) (z : real) : (term9 x y z) = ((term10 x y z) = (term11 x y z)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1382513 (x : real) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1382514 (x : real) : term13 x.
Proof. exact (@lem9784 (x = term2)). Qed.
Lemma lem1382515 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1382516 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1382515 x) (@lem1382514 x)). Qed.
Lemma lem1382518 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1382519 (x : real) (y : real) (h1 : (real_mul x y) = term2) : (real_mul x y) = term2.
Proof. exact (h1). Qed.
Lemma lem1382520 (x : real) (y : real) (h1 : term16 x y) : term16 x y.
Proof. exact (h1). Qed.
Lemma lem1382521 (x : real) (h1 : x = term2) : x = term2.
Proof. exact (h1). Qed.
Lemma lem1382522 (y : real) (h1 : y = term2) : y = term2.
Proof. exact (h1). Qed.
Lemma lem1382540 (x : real) : term17 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1382541 (x : real) : (term17 x) = ((term18 x) = term2).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1382546 (x : real) (h1 : x = term2) : x = term2.
Proof. exact (h1). Qed.
Lemma lem1382547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1382548 (x : real) (h1 : x = term2) : (real_mul x) = term19.
Proof. exact (MK_COMB (@lem1382547) (@lem1382546 x h1)). Qed.
Lemma lem1382549 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1382550 (y : real) (x : real) (h1 : x = term2) : (real_mul x y) = (term18 y).
Proof. exact (MK_COMB (@lem1382548 x h1) (@lem1382549 y)). Qed.
Lemma lem1382552 (x : real) : (term18 x) = term2.
Proof. exact (EQ_MP (@lem1382541 x) (@lem1382540 x)). Qed.
Lemma lem1382553 (y : real) : (term18 y) = term2.
Proof. exact (@lem1382552 y). Qed.
Lemma lem1382554 (y : real) (x : real) (h1 : x = term2) : (real_mul x y) = term2.
Proof. exact (TRANS (@lem1382550 y x h1) (@lem1382553 y)). Qed.
Lemma lem1382555 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382556 (y : real) (x : real) (h1 : x = term2) : (term20 x y) = term21.
Proof. exact (MK_COMB (@lem1382555) (@lem1382554 y x h1)). Qed.
Lemma lem1382557 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1382558 (y : real) (x : real) (h1 : x = term2) : ((real_mul x y) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1382556 y x h1) (@lem1382557)). Qed.
Lemma lem1382560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1382561 (x : real) : (x = x) = True.
Proof. exact (@lem1382560 real x). Qed.
Lemma lem1382562 : (term2 = term2) = True.
Proof. exact (@lem1382561 term2). Qed.
Lemma lem1382563 (y : real) (x : real) (h1 : x = term2) : ((real_mul x y) = term2) = True.
Proof. exact (TRANS (@lem1382558 y x h1) (@lem1382562)). Qed.
Lemma lem1382564 (y : real) (x : real) (h1 : x = term2) : True = ((real_mul x y) = term2).
Proof. exact (SYM (@lem1382563 y x h1)). Qed.
Lemma lem1382565 (y : real) (x : real) (h1 : x = term2) : (real_mul x y) = term2.
Proof. exact (EQ_MP (@lem1382564 y x h1) (@lem0)). Qed.
Lemma lem1382566 (x : real) : term0 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1382567 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1382575 (y : real) (h1 : y = term2) : y = term2.
Proof. exact (h1). Qed.
Lemma lem1382576 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1382577 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = (term1 x).
Proof. exact (MK_COMB (@lem1382576 x) (@lem1382575 y h1)). Qed.
Lemma lem1382579 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1382567 x) (@lem1382566 x)). Qed.
Lemma lem1382580 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = term2.
Proof. exact (TRANS (@lem1382577 x y h1) (@lem1382579 x)). Qed.
Lemma lem1382581 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382582 (x : real) (y : real) (h1 : y = term2) : (term20 x y) = term21.
Proof. exact (MK_COMB (@lem1382581) (@lem1382580 x y h1)). Qed.
Lemma lem1382583 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1382584 (x : real) (y : real) (h1 : y = term2) : ((real_mul x y) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1382582 x y h1) (@lem1382583)). Qed.
Lemma lem1382586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1382587 (x : real) : (x = x) = True.
Proof. exact (@lem1382586 real x). Qed.
Lemma lem1382588 : (term2 = term2) = True.
Proof. exact (@lem1382587 term2). Qed.
Lemma lem1382589 (x : real) (y : real) (h1 : y = term2) : ((real_mul x y) = term2) = True.
Proof. exact (TRANS (@lem1382584 x y h1) (@lem1382588)). Qed.
Lemma lem1382590 (x : real) (y : real) (h1 : y = term2) : True = ((real_mul x y) = term2).
Proof. exact (SYM (@lem1382589 x y h1)). Qed.
Lemma lem1382591 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = term2.
Proof. exact (EQ_MP (@lem1382590 x y h1) (@lem0)). Qed.
Lemma lem1382597 (x : real) (h1 : x = term2) : x = term2.
Proof. exact (h1). Qed.
Lemma lem1382598 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382599 (x : real) (h1 : x = term2) : (@eq real x) = term21.
Proof. exact (MK_COMB (@lem1382598) (@lem1382597 x h1)). Qed.
Lemma lem1382600 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1382601 (x : real) (h1 : x = term2) : (x = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1382599 x h1) (@lem1382600)). Qed.
Lemma lem1382603 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1382604 (x : real) : (x = x) = True.
Proof. exact (@lem1382603 real x). Qed.
Lemma lem1382605 : (term2 = term2) = True.
Proof. exact (@lem1382604 term2). Qed.
Lemma lem1382606 (x : real) (h1 : x = term2) : (x = term2) = True.
Proof. exact (TRANS (@lem1382601 x h1) (@lem1382605)). Qed.
Lemma lem1382607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1382608 (x : real) (h1 : x = term2) : (term22 x) = (or True).
Proof. exact (MK_COMB (@lem1382607) (@lem1382606 x h1)). Qed.
Lemma lem1382611 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1382612 (y : real) (x : real) (h1 : x = term2) : (term16 x y) = (term23 y).
Proof. exact (MK_COMB (@lem1382608 x h1) (@lem1382611 y)). Qed.
Lemma lem1382614 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1382615 (y : real) : (term23 y) = True.
Proof. exact (@lem1382614 (y = term2)). Qed.
Lemma lem1382616 (y : real) (x : real) (h1 : x = term2) : (term16 x y) = True.
Proof. exact (TRANS (@lem1382612 y x h1) (@lem1382615 y)). Qed.
Lemma lem1382617 (y : real) (x : real) (h1 : x = term2) : True = (term16 x y).
Proof. exact (SYM (@lem1382616 y x h1)). Qed.
Lemma lem1382618 (y : real) (x : real) (h1 : x = term2) : term16 x y.
Proof. exact (EQ_MP (@lem1382617 y x h1) (@lem0)). Qed.
Lemma lem1382619 (x : real) : term24 x.
Proof. exact (@lem82 (x = term2)). Qed.
Lemma lem1382635 (x : real) (h1 : term15 x) : (x = term2) = False.
Proof. exact (@lem1382619 x (@lem1382518 x h1)). Qed.
Lemma lem1382636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1382637 (x : real) (h1 : term15 x) : (term22 x) = (or False).
Proof. exact (MK_COMB (@lem1382636) (@lem1382635 x h1)). Qed.
Lemma lem1382640 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1382641 (y : real) (x : real) (h1 : term15 x) : (term16 x y) = (term25 y).
Proof. exact (MK_COMB (@lem1382637 x h1) (@lem1382640 y)). Qed.
Lemma lem1382643 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1382644 (y : real) : (term25 y) = (y = term2).
Proof. exact (@lem1382643 (y = term2)). Qed.
Lemma lem1382647 (y : real) (x : real) (h1 : term15 x) : (term16 x y) = (y = term2).
Proof. exact (TRANS (@lem1382641 y x h1) (@lem1382644 y)). Qed.
Lemma lem1382648 (y : real) (x : real) (h1 : term15 x) : (y = term2) = (term16 x y).
Proof. exact (SYM (@lem1382647 y x h1)). Qed.
Lemma lem1382649 (x : real) (y : real) (h1 : (real_mul x y) = term2) : (term26 x y) = (term27 x).
Proof. exact (MK_COMB (@lem1382513 x) (@lem1382519 x y h1)). Qed.
Lemma lem1382657 (x : real) (y : real) (z : real) : (term10 x y z) = (term11 x y z).
Proof. exact (EQ_MP (@lem1382511 x y z) (@lem1382510 x y z)). Qed.
Lemma lem1382658 (x : real) (y : real) : (term26 x y) = (term28 x y).
Proof. exact (@lem1382657 (real_inv x) x y). Qed.
Lemma lem1382659 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382660 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1382659) (@lem1382658 x y)). Qed.
Lemma lem1382661 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1382662 (y : real) (x : real) : ((term26 x y) = (term27 x)) = ((term28 x y) = (term27 x)).
Proof. exact (MK_COMB (@lem1382660 x y) (@lem1382661 x)). Qed.
Lemma lem1382665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382666 (y : real) (x : real) : (term31 y x) = (term32 y x).
Proof. exact (MK_COMB (@lem1382665) (@lem1382662 y x)). Qed.
Lemma lem1382669 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1382670 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1382666 y x) (@lem1382669 y)). Qed.
Lemma lem1382675 (x : real) (y : real) : (term34 x y) = (term33 x y).
Proof. exact (SYM (@lem1382670 x y)). Qed.
Lemma lem1382676 (x : real) : term35 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1382677 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1382680 (x : real) : term36 x.
Proof. exact (EQ_MP (@lem1382677 x) (@lem1382676 x)). Qed.
Lemma lem1382689 (x : real) (h1 : term15 x) : (term37 x) = term38.
Proof. exact (@lem1382680 x (@lem1382518 x h1)). Qed.
Lemma lem1382690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1382691 (x : real) (h1 : term15 x) : (term39 x) = term40.
Proof. exact (MK_COMB (@lem1382690) (@lem1382689 x h1)). Qed.
Lemma lem1382692 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1382693 (y : real) (x : real) (h1 : term15 x) : (term28 x y) = (term4 y).
Proof. exact (MK_COMB (@lem1382691 x h1) (@lem1382692 y)). Qed.
Lemma lem1382694 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382695 (y : real) (x : real) (h1 : term15 x) : (term30 x y) = (term41 y).
Proof. exact (MK_COMB (@lem1382694) (@lem1382693 y x h1)). Qed.
Lemma lem1382696 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1382697 (y : real) (x : real) (h1 : term15 x) : ((term28 x y) = (term27 x)) = ((term4 y) = (term27 x)).
Proof. exact (MK_COMB (@lem1382695 y x h1) (@lem1382696 x)). Qed.
Lemma lem1382700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382701 (y : real) (x : real) (h1 : term15 x) : (term32 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1382700) (@lem1382697 y x h1)). Qed.
Lemma lem1382704 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1382705 (y : real) (x : real) (h1 : term15 x) : (term34 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1382701 y x h1) (@lem1382704 y)). Qed.
Lemma lem1382710 (y : real) (x : real) (h1 : term15 x) : (term43 x y) = (term34 x y).
Proof. exact (SYM (@lem1382705 y x h1)). Qed.
Lemma lem1382718 (x : real) : (term4 x) = x.
Proof. exact (EQ_MP (@lem1382502 x) (@lem1382501 x)). Qed.
Lemma lem1382719 (y : real) : (term4 y) = y.
Proof. exact (@lem1382718 y). Qed.
Lemma lem1382720 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1382721 (y : real) : (term41 y) = (@eq real y).
Proof. exact (MK_COMB (@lem1382720) (@lem1382719 y)). Qed.
Lemma lem1382723 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1382499 x) (@lem1382498 x)). Qed.
Lemma lem1382724 (x : real) : (term27 x) = term2.
Proof. exact (@lem1382723 (real_inv x)). Qed.
Lemma lem1382725 (x : real) (y : real) : ((term4 y) = (term27 x)) = (y = term2).
Proof. exact (MK_COMB (@lem1382721 y) (@lem1382724 x)). Qed.
Lemma lem1382728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382729 (x : real) (y : real) : (term42 y x) = (term44 y).
Proof. exact (MK_COMB (@lem1382728) (@lem1382725 x y)). Qed.
Lemma lem1382732 (y : real) : (y = term2) = (y = term2).
Proof. exact (eq_refl (y = term2)). Qed.
Lemma lem1382733 (x : real) (y : real) : (term43 x y) = (term45 y).
Proof. exact (MK_COMB (@lem1382729 x y) (@lem1382732 y)). Qed.
Lemma lem1382737 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1382738 (y : real) : (term45 y) = True.
Proof. exact (@lem1382737 (y = term2)). Qed.
Lemma lem1382739 (x : real) (y : real) : (term43 x y) = True.
Proof. exact (TRANS (@lem1382733 x y) (@lem1382738 y)). Qed.
Lemma lem1382740 (x : real) (y : real) : True = (term43 x y).
Proof. exact (SYM (@lem1382739 x y)). Qed.
Lemma lem1382741 (x : real) (y : real) : term43 x y.
Proof. exact (EQ_MP (@lem1382740 x y) (@lem0)). Qed.
Lemma lem1382742 (y : real) (x : real) (h1 : term15 x) : term34 x y.
Proof. exact (EQ_MP (@lem1382710 y x h1) (@lem1382741 x y)). Qed.
Lemma lem1382743 (y : real) (x : real) (h1 : term15 x) : term33 x y.
Proof. exact (EQ_MP (@lem1382675 x y) (@lem1382742 y x h1)). Qed.
Lemma lem1382744 (x : real) (y : real) (h1 : term15 x) (h2 : (real_mul x y) = term2) : y = term2.
Proof. exact (@lem1382743 y x h1 (@lem1382649 x y h2)). Qed.
Lemma lem1382745 (x : real) (y : real) (h1 : term15 x) (h2 : (real_mul x y) = term2) : term16 x y.
Proof. exact (EQ_MP (@lem1382648 y x h1) (@lem1382744 x y h1 h2)). Qed.
Lemma lem1382747 (x : real) (y : real) (h1 : (real_mul x y) = term2) : term16 x y.
Proof. exact (or_elim (@lem1382516 x) (fun h0 : x = term2 => @lem1382618 y x h0) (fun h0 : term15 x => @lem1382745 x y h0 h1)). Qed.
Lemma lem1382748 (x : real) (y : real) (h1 : y = term2) : (y = term2) = ((real_mul x y) = term2).
Proof. exact (prop_ext (fun h2 : y = term2 => @lem1382591 x y h1) (fun h2 : (real_mul x y) = term2 => @lem1382522 y h1)). Qed.
Lemma lem1382749 (x : real) (y : real) (h1 : y = term2) : (real_mul x y) = term2.
Proof. exact (EQ_MP (@lem1382748 x y h1) (@lem1382522 y h1)). Qed.
Lemma lem1382750 (y : real) (x : real) (h1 : x = term2) : (x = term2) = ((real_mul x y) = term2).
Proof. exact (prop_ext (fun h2 : x = term2 => @lem1382565 y x h1) (fun h2 : (real_mul x y) = term2 => @lem1382521 x h1)). Qed.
Lemma lem1382751 (y : real) (x : real) (h1 : x = term2) : (real_mul x y) = term2.
Proof. exact (EQ_MP (@lem1382750 y x h1) (@lem1382521 x h1)). Qed.
Lemma lem1382752 (x : real) (y : real) (h1 : term16 x y) : (real_mul x y) = term2.
Proof. exact (or_elim (@lem1382520 x y h1) (fun h0 : x = term2 => @lem1382751 y x h0) (fun h0 : y = term2 => @lem1382749 x y h0)). Qed.
Lemma lem1382753 (x : real) (y : real) : term46 x y.
Proof. exact (fun h0 : term16 x y => @lem1382752 x y h0). Qed.
Lemma lem1382754 (x : real) (y : real) (h1 : (real_mul x y) = term2) : ((real_mul x y) = term2) = (term16 x y).
Proof. exact (prop_ext (fun h2 : (real_mul x y) = term2 => @lem1382747 x y h1) (fun h2 : term16 x y => @lem1382519 x y h1)). Qed.
Lemma lem1382755 (x : real) (y : real) (h1 : (real_mul x y) = term2) : term16 x y.
Proof. exact (EQ_MP (@lem1382754 x y h1) (@lem1382519 x y h1)). Qed.
Lemma lem1382756 (x : real) (y : real) : term47 x y.
Proof. exact (fun h0 : (real_mul x y) = term2 => @lem1382755 x y h0). Qed.
Lemma lem1382757 (x : real) (y : real) : term48 x y.
Proof. exact (conj (@lem1382756 x y) (@lem1382753 x y)). Qed.
Lemma lem1382758 (x : real) (y : real) : (term48 x y) = (((real_mul x y) = term2) = (term16 x y)).
Proof. exact (@lem32 ((real_mul x y) = term2) (term16 x y)). Qed.
Lemma lem1382759 (x : real) (y : real) : ((real_mul x y) = term2) = (term16 x y).
Proof. exact (EQ_MP (@lem1382758 x y) (@lem1382757 x y)). Qed.
Lemma lem1382764 (x : real) : term49 x.
Proof. exact (fun y : real => @lem1382759 x y). Qed.
Lemma lem1382769 : term50.
Proof. exact (fun x : real => @lem1382764 x). Qed.

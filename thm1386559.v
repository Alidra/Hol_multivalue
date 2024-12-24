Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1386559_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NEG_SUB_spec.
Require Import REAL_SUB_0_spec.
Require Import REAL_SUB_LE_spec.
Require Import REAL_SUB_LT_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
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
Require Import thm69_spec.
Lemma lem1384586 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1384587 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1384588 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1384587 t1) (@lem1384586 t1)). Qed.
Lemma lem1384589 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1384588 t1 t2). Qed.
Lemma lem1384590 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1384591 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1384590 t1 t2) (@lem1384589 t1 t2)). Qed.
Lemma lem1384592 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1384591 t1 t2 t3). Qed.
Lemma lem1384593 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1384594 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1384593 t1 t2 t3) (@lem1384592 t1 t2 t3)). Qed.
Lemma lem1384595 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1384594 t1 t2 t3)). Qed.
Lemma lem1384596 (y : real) : term7 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1384597 (y : real) : (term7 y) = (term8 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem1384598 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1384597 y) (@lem1384596 y)). Qed.
Lemma lem1384599 (y : real) (x : real) : term9 y x.
Proof. exact (@lem1384598 y x). Qed.
Lemma lem1384600 (y : real) (x : real) : (term9 y x) = ((real_lt x y) = (term10 y x)).
Proof. exact (eq_refl (term9 y x)). Qed.
Lemma lem1384602 (x : real) : term11 x.
Proof. exact (@lem1376695 x). Qed.
Lemma lem1384603 (x : real) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1384604 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1384603 x) (@lem1384602 x)). Qed.
Lemma lem1384605 (x : real) (y : real) : term13 x y.
Proof. exact (@lem1384604 x y). Qed.
Lemma lem1384606 (x : real) (y : real) : (term13 x y) = (((real_sub x y) = term14) = (x = y)).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1384608 (x : real) : term15 x.
Proof. exact (@lem1374337 x). Qed.
Lemma lem1384609 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1384610 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem1384609 x) (@lem1384608 x)). Qed.
Lemma lem1384611 (x : real) (y : real) : term17 x y.
Proof. exact (@lem1384610 x y). Qed.
Lemma lem1384612 (y : real) (x : real) : (term17 x y) = ((term18 x y) = (real_sub y x)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1384614 (x : real) : term19 x.
Proof. exact (@lem1374224 x). Qed.
Lemma lem1384615 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1384616 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem1384615 x) (@lem1384614 x)). Qed.
Lemma lem1384617 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1384616 x y). Qed.
Lemma lem1384618 (y : real) (x : real) : (term21 x y) = ((term22 x y) = (real_le y x)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1384620 (x : real) : term23 x.
Proof. exact (@lem1376486 x). Qed.
Lemma lem1384621 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1384622 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem1384621 x) (@lem1384620 x)). Qed.
Lemma lem1384623 (x : real) (y : real) : term25 x y.
Proof. exact (@lem1384622 x y). Qed.
Lemma lem1384624 (y : real) (x : real) : (term25 x y) = ((term26 x y) = (real_lt y x)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1384626 (y : real) : term27 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1384627 (y : real) : (term27 y) = (term28 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1384628 (y : real) : term28 y.
Proof. exact (EQ_MP (@lem1384627 y) (@lem1384626 y)). Qed.
Lemma lem1384629 (y : real) (x : real) : term29 y x.
Proof. exact (@lem1384628 y x). Qed.
Lemma lem1384630 (y : real) (x : real) : (term29 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term29 y x)). Qed.
Lemma lem1384632 (y : real) : term30 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1384633 (y : real) : (term30 y) = (term31 y).
Proof. exact (eq_refl (term30 y)). Qed.
Lemma lem1384634 (y : real) : term31 y.
Proof. exact (EQ_MP (@lem1384633 y) (@lem1384632 y)). Qed.
Lemma lem1384635 (y : real) (x : real) : term32 y x.
Proof. exact (@lem1384634 y x). Qed.
Lemma lem1384636 (y : real) (x : real) : (term32 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1384643 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384644 (y : real) (x : real) : (term33 y x) = (term26 y x).
Proof. exact (@lem1384643 term14 (real_sub y x)). Qed.
Lemma lem1384646 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384647 (x : real) (y : real) : (term26 y x) = (real_lt x y).
Proof. exact (@lem1384646 x y). Qed.
Lemma lem1384648 (x : real) (y : real) : (term33 y x) = (real_lt x y).
Proof. exact (TRANS (@lem1384644 y x) (@lem1384647 x y)). Qed.
Lemma lem1384649 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1384650 (x : real) (y : real) : ((real_lt x y) = (term33 y x)) = ((real_lt x y) = (real_lt x y)).
Proof. exact (MK_COMB (@lem1384649 x y) (@lem1384648 x y)). Qed.
Lemma lem1384652 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384653 (x : Prop) : (x = x) = True.
Proof. exact (@lem1384652 Prop x). Qed.
Lemma lem1384654 (x : real) (y : real) : ((real_lt x y) = (real_lt x y)) = True.
Proof. exact (@lem1384653 (real_lt x y)). Qed.
Lemma lem1384655 (y : real) (x : real) : ((real_lt x y) = (term33 y x)) = True.
Proof. exact (TRANS (@lem1384650 x y) (@lem1384654 x y)). Qed.
Lemma lem1384656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384657 (y : real) (x : real) : (term35 y x) = (and True).
Proof. exact (MK_COMB (@lem1384656) (@lem1384655 y x)). Qed.
Lemma lem1384663 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384664 (y : real) (x : real) : (term36 y x) = (term22 y x).
Proof. exact (@lem1384663 term14 (real_sub y x)). Qed.
Lemma lem1384666 (y : real) (x : real) : (term22 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384618 y x) (@lem1384617 x y)). Qed.
Lemma lem1384667 (x : real) (y : real) : (term22 y x) = (real_le x y).
Proof. exact (@lem1384666 x y). Qed.
Lemma lem1384668 (x : real) (y : real) : (term36 y x) = (real_le x y).
Proof. exact (TRANS (@lem1384664 y x) (@lem1384667 x y)). Qed.
Lemma lem1384669 (x : real) (y : real) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1384670 (x : real) (y : real) : ((real_le x y) = (term36 y x)) = ((real_le x y) = (real_le x y)).
Proof. exact (MK_COMB (@lem1384669 x y) (@lem1384668 x y)). Qed.
Lemma lem1384672 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384673 (x : Prop) : (x = x) = True.
Proof. exact (@lem1384672 Prop x). Qed.
Lemma lem1384674 (x : real) (y : real) : ((real_le x y) = (real_le x y)) = True.
Proof. exact (@lem1384673 (real_le x y)). Qed.
Lemma lem1384675 (y : real) (x : real) : ((real_le x y) = (term36 y x)) = True.
Proof. exact (TRANS (@lem1384670 x y) (@lem1384674 x y)). Qed.
Lemma lem1384676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384677 (y : real) (x : real) : (term38 y x) = (and True).
Proof. exact (MK_COMB (@lem1384676) (@lem1384675 y x)). Qed.
Lemma lem1384683 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384685 (y : real) (x : real) : (term39 x y) = (term34 y x).
Proof. exact (MK_COMB (@lem1384684) (@lem1384683 y x)). Qed.
Lemma lem1384687 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384688 (x : real) (y : real) : (term33 x y) = (term26 x y).
Proof. exact (@lem1384687 term14 (real_sub x y)). Qed.
Lemma lem1384690 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384691 (y : real) (x : real) : (term33 x y) = (real_lt y x).
Proof. exact (TRANS (@lem1384688 x y) (@lem1384690 y x)). Qed.
Lemma lem1384692 (y : real) (x : real) : ((real_gt x y) = (term33 x y)) = ((real_lt y x) = (real_lt y x)).
Proof. exact (MK_COMB (@lem1384685 y x) (@lem1384691 y x)). Qed.
Lemma lem1384694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384695 (x : Prop) : (x = x) = True.
Proof. exact (@lem1384694 Prop x). Qed.
Lemma lem1384696 (y : real) (x : real) : ((real_lt y x) = (real_lt y x)) = True.
Proof. exact (@lem1384695 (real_lt y x)). Qed.
Lemma lem1384697 (x : real) (y : real) : ((real_gt x y) = (term33 x y)) = True.
Proof. exact (TRANS (@lem1384692 y x) (@lem1384696 y x)). Qed.
Lemma lem1384698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384699 (x : real) (y : real) : (term40 x y) = (and True).
Proof. exact (MK_COMB (@lem1384698) (@lem1384697 x y)). Qed.
Lemma lem1384705 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384707 (y : real) (x : real) : (term41 x y) = (term37 y x).
Proof. exact (MK_COMB (@lem1384706) (@lem1384705 y x)). Qed.
Lemma lem1384709 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384710 (x : real) (y : real) : (term36 x y) = (term22 x y).
Proof. exact (@lem1384709 term14 (real_sub x y)). Qed.
Lemma lem1384712 (y : real) (x : real) : (term22 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384618 y x) (@lem1384617 x y)). Qed.
Lemma lem1384713 (y : real) (x : real) : (term36 x y) = (real_le y x).
Proof. exact (TRANS (@lem1384710 x y) (@lem1384712 y x)). Qed.
Lemma lem1384714 (y : real) (x : real) : ((real_ge x y) = (term36 x y)) = ((real_le y x) = (real_le y x)).
Proof. exact (MK_COMB (@lem1384707 y x) (@lem1384713 y x)). Qed.
Lemma lem1384716 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384717 (x : Prop) : (x = x) = True.
Proof. exact (@lem1384716 Prop x). Qed.
Lemma lem1384718 (y : real) (x : real) : ((real_le y x) = (real_le y x)) = True.
Proof. exact (@lem1384717 (real_le y x)). Qed.
Lemma lem1384719 (x : real) (y : real) : ((real_ge x y) = (term36 x y)) = True.
Proof. exact (TRANS (@lem1384714 y x) (@lem1384718 y x)). Qed.
Lemma lem1384720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384721 (x : real) (y : real) : (term42 x y) = (and True).
Proof. exact (MK_COMB (@lem1384720) (@lem1384719 x y)). Qed.
Lemma lem1384735 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384736 (x : real) (y : real) : (term36 x y) = (term22 x y).
Proof. exact (@lem1384735 term14 (real_sub x y)). Qed.
Lemma lem1384738 (y : real) (x : real) : (term22 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384618 y x) (@lem1384617 x y)). Qed.
Lemma lem1384739 (y : real) (x : real) : (term36 x y) = (real_le y x).
Proof. exact (TRANS (@lem1384736 x y) (@lem1384738 y x)). Qed.
Lemma lem1384740 (x : real) (y : real) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1384741 (y : real) (x : real) : ((term44 x y) = (term36 x y)) = ((term44 x y) = (real_le y x)).
Proof. exact (MK_COMB (@lem1384740 x y) (@lem1384739 y x)). Qed.
Lemma lem1384744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384745 (y : real) (x : real) : (term45 x y) = (term46 y x).
Proof. exact (MK_COMB (@lem1384744) (@lem1384741 y x)). Qed.
Lemma lem1384751 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384752 (x : real) (y : real) : (term33 x y) = (term26 x y).
Proof. exact (@lem1384751 term14 (real_sub x y)). Qed.
Lemma lem1384754 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384755 (y : real) (x : real) : (term33 x y) = (real_lt y x).
Proof. exact (TRANS (@lem1384752 x y) (@lem1384754 y x)). Qed.
Lemma lem1384756 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1384757 (y : real) (x : real) : ((term10 x y) = (term33 x y)) = ((term10 x y) = (real_lt y x)).
Proof. exact (MK_COMB (@lem1384756 x y) (@lem1384755 y x)). Qed.
Lemma lem1384760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384761 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (MK_COMB (@lem1384760) (@lem1384757 y x)). Qed.
Lemma lem1384767 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384769 (y : real) (x : real) : (term50 x y) = (term44 y x).
Proof. exact (MK_COMB (@lem1384768) (@lem1384767 y x)). Qed.
Lemma lem1384770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384771 (y : real) (x : real) : (term51 x y) = (term43 y x).
Proof. exact (MK_COMB (@lem1384770) (@lem1384769 y x)). Qed.
Lemma lem1384773 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384774 (y : real) (x : real) : (term36 y x) = (term22 y x).
Proof. exact (@lem1384773 term14 (real_sub y x)). Qed.
Lemma lem1384776 (y : real) (x : real) : (term22 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384618 y x) (@lem1384617 x y)). Qed.
Lemma lem1384777 (x : real) (y : real) : (term22 y x) = (real_le x y).
Proof. exact (@lem1384776 x y). Qed.
Lemma lem1384778 (x : real) (y : real) : (term36 y x) = (real_le x y).
Proof. exact (TRANS (@lem1384774 y x) (@lem1384777 x y)). Qed.
Lemma lem1384779 (x : real) (y : real) : ((term50 x y) = (term36 y x)) = ((term44 y x) = (real_le x y)).
Proof. exact (MK_COMB (@lem1384771 y x) (@lem1384778 x y)). Qed.
Lemma lem1384782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384783 (x : real) (y : real) : (term52 y x) = (term46 x y).
Proof. exact (MK_COMB (@lem1384782) (@lem1384779 x y)). Qed.
Lemma lem1384789 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1384630 y x) (@lem1384629 y x)). Qed.
Lemma lem1384790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1384791 (y : real) (x : real) : (term53 x y) = (term10 y x).
Proof. exact (MK_COMB (@lem1384790) (@lem1384789 y x)). Qed.
Lemma lem1384792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1384793 (y : real) (x : real) : (term54 x y) = (term47 y x).
Proof. exact (MK_COMB (@lem1384792) (@lem1384791 y x)). Qed.
Lemma lem1384795 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384796 (y : real) (x : real) : (term33 y x) = (term26 y x).
Proof. exact (@lem1384795 term14 (real_sub y x)). Qed.
Lemma lem1384798 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384799 (x : real) (y : real) : (term26 y x) = (real_lt x y).
Proof. exact (@lem1384798 x y). Qed.
Lemma lem1384800 (x : real) (y : real) : (term33 y x) = (real_lt x y).
Proof. exact (TRANS (@lem1384796 y x) (@lem1384799 x y)). Qed.
Lemma lem1384801 (x : real) (y : real) : ((term53 x y) = (term33 y x)) = ((term10 y x) = (real_lt x y)).
Proof. exact (MK_COMB (@lem1384793 y x) (@lem1384800 x y)). Qed.
Lemma lem1384804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384805 (x : real) (y : real) : (term55 y x) = (term49 x y).
Proof. exact (MK_COMB (@lem1384804) (@lem1384801 x y)). Qed.
Lemma lem1384813 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384814 (x : real) (y : real) : (term33 x y) = (term26 x y).
Proof. exact (@lem1384813 term14 (real_sub x y)). Qed.
Lemma lem1384816 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384817 (y : real) (x : real) : (term33 x y) = (real_lt y x).
Proof. exact (TRANS (@lem1384814 x y) (@lem1384816 y x)). Qed.
Lemma lem1384818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1384819 (y : real) (x : real) : (term56 x y) = (term57 y x).
Proof. exact (MK_COMB (@lem1384818) (@lem1384817 y x)). Qed.
Lemma lem1384821 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384636 y x) (@lem1384635 y x)). Qed.
Lemma lem1384822 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1384821 term14 (term18 x y)). Qed.
Lemma lem1384824 (y : real) (x : real) : (term18 x y) = (real_sub y x).
Proof. exact (EQ_MP (@lem1384612 y x) (@lem1384611 x y)). Qed.
Lemma lem1384825 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1384826 (y : real) (x : real) : (term59 x y) = (term26 y x).
Proof. exact (MK_COMB (@lem1384825) (@lem1384824 y x)). Qed.
Lemma lem1384828 (y : real) (x : real) : (term26 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1384624 y x) (@lem1384623 x y)). Qed.
Lemma lem1384829 (x : real) (y : real) : (term26 y x) = (real_lt x y).
Proof. exact (@lem1384828 x y). Qed.
Lemma lem1384830 (x : real) (y : real) : (term59 x y) = (real_lt x y).
Proof. exact (TRANS (@lem1384826 y x) (@lem1384829 x y)). Qed.
Lemma lem1384831 (x : real) (y : real) : (term58 x y) = (real_lt x y).
Proof. exact (TRANS (@lem1384822 x y) (@lem1384830 x y)). Qed.
Lemma lem1384832 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1384819 y x) (@lem1384831 x y)). Qed.
Lemma lem1384835 (x : real) (y : real) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1384836 (x : real) (y : real) : ((term64 x y) = (term61 x y)) = ((term64 x y) = (term62 x y)).
Proof. exact (MK_COMB (@lem1384835 x y) (@lem1384832 x y)). Qed.
Lemma lem1384839 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1384805 x y) (@lem1384836 x y)). Qed.
Lemma lem1384842 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1384783 x y) (@lem1384839 x y)). Qed.
Lemma lem1384845 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1384761 y x) (@lem1384842 x y)). Qed.
Lemma lem1384848 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1384745 y x) (@lem1384845 x y)). Qed.
Lemma lem1384851 (x : real) (y : real) : (term73 x y) = (term73 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1384852 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1384851 x y) (@lem1384848 x y)). Qed.
Lemma lem1384855 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1384721 x y) (@lem1384852 x y)). Qed.
Lemma lem1384857 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384858 (x : real) (y : real) : (term77 x y) = (term75 x y).
Proof. exact (@lem1384857 (term75 x y)). Qed.
Lemma lem1384889 (x : real) (y : real) : (term76 x y) = (term75 x y).
Proof. exact (TRANS (@lem1384855 x y) (@lem1384858 x y)). Qed.
Lemma lem1384890 (x : real) (y : real) : (term78 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1384699 x y) (@lem1384889 x y)). Qed.
Lemma lem1384892 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384893 (x : real) (y : real) : (term77 x y) = (term75 x y).
Proof. exact (@lem1384892 (term75 x y)). Qed.
Lemma lem1384924 (x : real) (y : real) : (term78 x y) = (term75 x y).
Proof. exact (TRANS (@lem1384890 x y) (@lem1384893 x y)). Qed.
Lemma lem1384925 (x : real) (y : real) : (term79 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1384677 y x) (@lem1384924 x y)). Qed.
Lemma lem1384927 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384928 (x : real) (y : real) : (term77 x y) = (term75 x y).
Proof. exact (@lem1384927 (term75 x y)). Qed.
Lemma lem1384959 (x : real) (y : real) : (term79 x y) = (term75 x y).
Proof. exact (TRANS (@lem1384925 x y) (@lem1384928 x y)). Qed.
Lemma lem1384960 (x : real) (y : real) : (term80 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1384657 y x) (@lem1384959 x y)). Qed.
Lemma lem1384962 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384963 (x : real) (y : real) : (term77 x y) = (term75 x y).
Proof. exact (@lem1384962 (term75 x y)). Qed.
Lemma lem1384994 (x : real) (y : real) : (term80 x y) = (term75 x y).
Proof. exact (TRANS (@lem1384960 x y) (@lem1384963 x y)). Qed.
Lemma lem1384995 (x : real) (y : real) : (term75 x y) = (term80 x y).
Proof. exact (SYM (@lem1384994 x y)). Qed.
Lemma lem1385003 (x : real) (y : real) : ((real_sub x y) = term14) = (x = y).
Proof. exact (EQ_MP (@lem1384606 x y) (@lem1384605 x y)). Qed.
Lemma lem1385006 (x : real) (y : real) : (term81 x y) = (term81 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem1385007 (x : real) (y : real) : ((x = y) = ((real_sub x y) = term14)) = ((x = y) = (x = y)).
Proof. exact (MK_COMB (@lem1385006 x y) (@lem1385003 x y)). Qed.
Lemma lem1385009 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1385010 (x : Prop) : (x = x) = True.
Proof. exact (@lem1385009 Prop x). Qed.
Lemma lem1385011 (x : real) (y : real) : ((x = y) = (x = y)) = True.
Proof. exact (@lem1385010 (x = y)). Qed.
Lemma lem1385012 (x : real) (y : real) : ((x = y) = ((real_sub x y) = term14)) = True.
Proof. exact (TRANS (@lem1385007 x y) (@lem1385011 x y)). Qed.
Lemma lem1385013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385014 (x : real) (y : real) : (term73 x y) = (and True).
Proof. exact (MK_COMB (@lem1385013) (@lem1385012 x y)). Qed.
Lemma lem1385020 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1385022 (y : real) (x : real) : (term44 x y) = (term82 y x).
Proof. exact (MK_COMB (@lem1385021) (@lem1385020 y x)). Qed.
Lemma lem1385024 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1385025 (y : real) (x : real) : (term82 y x) = (real_le y x).
Proof. exact (@lem1385024 (real_le y x)). Qed.
Lemma lem1385026 (y : real) (x : real) : (term44 x y) = (real_le y x).
Proof. exact (TRANS (@lem1385022 y x) (@lem1385025 y x)). Qed.
Lemma lem1385027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1385028 (y : real) (x : real) : (term43 x y) = (term37 y x).
Proof. exact (MK_COMB (@lem1385027) (@lem1385026 y x)). Qed.
Lemma lem1385029 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1385030 (y : real) (x : real) : ((term44 x y) = (real_le y x)) = ((real_le y x) = (real_le y x)).
Proof. exact (MK_COMB (@lem1385028 y x) (@lem1385029 y x)). Qed.
Lemma lem1385032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1385033 (x : Prop) : (x = x) = True.
Proof. exact (@lem1385032 Prop x). Qed.
Lemma lem1385034 (y : real) (x : real) : ((real_le y x) = (real_le y x)) = True.
Proof. exact (@lem1385033 (real_le y x)). Qed.
Lemma lem1385035 (y : real) (x : real) : ((term44 x y) = (real_le y x)) = True.
Proof. exact (TRANS (@lem1385030 y x) (@lem1385034 y x)). Qed.
Lemma lem1385036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385037 (y : real) (x : real) : (term46 y x) = (and True).
Proof. exact (MK_COMB (@lem1385036) (@lem1385035 y x)). Qed.
Lemma lem1385043 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385044 (x : real) (y : real) : (real_lt y x) = (term10 x y).
Proof. exact (@lem1385043 x y). Qed.
Lemma lem1385045 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1385046 (x : real) (y : real) : ((term10 x y) = (real_lt y x)) = ((term10 x y) = (term10 x y)).
Proof. exact (MK_COMB (@lem1385045 x y) (@lem1385044 x y)). Qed.
Lemma lem1385048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1385049 (x : Prop) : (x = x) = True.
Proof. exact (@lem1385048 Prop x). Qed.
Lemma lem1385050 (x : real) (y : real) : ((term10 x y) = (term10 x y)) = True.
Proof. exact (@lem1385049 (term10 x y)). Qed.
Lemma lem1385051 (y : real) (x : real) : ((term10 x y) = (real_lt y x)) = True.
Proof. exact (TRANS (@lem1385046 x y) (@lem1385050 x y)). Qed.
Lemma lem1385052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385053 (y : real) (x : real) : (term49 y x) = (and True).
Proof. exact (MK_COMB (@lem1385052) (@lem1385051 y x)). Qed.
Lemma lem1385059 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385060 (x : real) (y : real) : (real_lt y x) = (term10 x y).
Proof. exact (@lem1385059 x y). Qed.
Lemma lem1385061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1385062 (x : real) (y : real) : (term44 y x) = (term82 x y).
Proof. exact (MK_COMB (@lem1385061) (@lem1385060 x y)). Qed.
Lemma lem1385064 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1385065 (x : real) (y : real) : (term82 x y) = (real_le x y).
Proof. exact (@lem1385064 (real_le x y)). Qed.
Lemma lem1385066 (x : real) (y : real) : (term44 y x) = (real_le x y).
Proof. exact (TRANS (@lem1385062 x y) (@lem1385065 x y)). Qed.
Lemma lem1385067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1385068 (x : real) (y : real) : (term43 y x) = (term37 x y).
Proof. exact (MK_COMB (@lem1385067) (@lem1385066 x y)). Qed.
Lemma lem1385069 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1385070 (x : real) (y : real) : ((term44 y x) = (real_le x y)) = ((real_le x y) = (real_le x y)).
Proof. exact (MK_COMB (@lem1385068 x y) (@lem1385069 x y)). Qed.
Lemma lem1385072 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1385073 (x : Prop) : (x = x) = True.
Proof. exact (@lem1385072 Prop x). Qed.
Lemma lem1385074 (x : real) (y : real) : ((real_le x y) = (real_le x y)) = True.
Proof. exact (@lem1385073 (real_le x y)). Qed.
Lemma lem1385075 (x : real) (y : real) : ((term44 y x) = (real_le x y)) = True.
Proof. exact (TRANS (@lem1385070 x y) (@lem1385074 x y)). Qed.
Lemma lem1385076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385077 (x : real) (y : real) : (term46 x y) = (and True).
Proof. exact (MK_COMB (@lem1385076) (@lem1385075 x y)). Qed.
Lemma lem1385083 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385084 (y : real) (x : real) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem1385085 (y : real) (x : real) : ((term10 y x) = (real_lt x y)) = ((term10 y x) = (term10 y x)).
Proof. exact (MK_COMB (@lem1385084 y x) (@lem1385083 y x)). Qed.
Lemma lem1385087 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1385088 (x : Prop) : (x = x) = True.
Proof. exact (@lem1385087 Prop x). Qed.
Lemma lem1385089 (y : real) (x : real) : ((term10 y x) = (term10 y x)) = True.
Proof. exact (@lem1385088 (term10 y x)). Qed.
Lemma lem1385090 (x : real) (y : real) : ((term10 y x) = (real_lt x y)) = True.
Proof. exact (TRANS (@lem1385085 y x) (@lem1385089 y x)). Qed.
Lemma lem1385091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385092 (x : real) (y : real) : (term49 x y) = (and True).
Proof. exact (MK_COMB (@lem1385091) (@lem1385090 x y)). Qed.
Lemma lem1385100 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385101 (x : real) (y : real) : (real_lt y x) = (term10 x y).
Proof. exact (@lem1385100 x y). Qed.
Lemma lem1385102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1385103 (x : real) (y : real) : (term57 y x) = (term84 x y).
Proof. exact (MK_COMB (@lem1385102) (@lem1385101 x y)). Qed.
Lemma lem1385105 (y : real) (x : real) : (real_lt x y) = (term10 y x).
Proof. exact (EQ_MP (@lem1384600 y x) (@lem1384599 y x)). Qed.
Lemma lem1385106 (y : real) (x : real) : (term62 x y) = (term85 y x).
Proof. exact (MK_COMB (@lem1385103 x y) (@lem1385105 y x)). Qed.
Lemma lem1385109 (x : real) (y : real) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1385110 (y : real) (x : real) : ((term64 x y) = (term62 x y)) = ((term64 x y) = (term85 y x)).
Proof. exact (MK_COMB (@lem1385109 x y) (@lem1385106 y x)). Qed.
Lemma lem1385113 (y : real) (x : real) : (term66 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1385092 x y) (@lem1385110 y x)). Qed.
Lemma lem1385115 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1385116 (y : real) (x : real) : (term86 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (@lem1385115 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385123 (y : real) (x : real) : (term66 x y) = ((term64 x y) = (term85 y x)).
Proof. exact (TRANS (@lem1385113 y x) (@lem1385116 y x)). Qed.
Lemma lem1385124 (y : real) (x : real) : (term68 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1385077 x y) (@lem1385123 y x)). Qed.
Lemma lem1385126 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1385127 (y : real) (x : real) : (term86 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (@lem1385126 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385134 (y : real) (x : real) : (term68 x y) = ((term64 x y) = (term85 y x)).
Proof. exact (TRANS (@lem1385124 y x) (@lem1385127 y x)). Qed.
Lemma lem1385135 (y : real) (x : real) : (term70 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1385053 y x) (@lem1385134 y x)). Qed.
Lemma lem1385137 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1385138 (y : real) (x : real) : (term86 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (@lem1385137 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385145 (y : real) (x : real) : (term70 x y) = ((term64 x y) = (term85 y x)).
Proof. exact (TRANS (@lem1385135 y x) (@lem1385138 y x)). Qed.
Lemma lem1385146 (y : real) (x : real) : (term72 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1385037 y x) (@lem1385145 y x)). Qed.
Lemma lem1385148 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1385149 (y : real) (x : real) : (term86 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (@lem1385148 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385156 (y : real) (x : real) : (term72 x y) = ((term64 x y) = (term85 y x)).
Proof. exact (TRANS (@lem1385146 y x) (@lem1385149 y x)). Qed.
Lemma lem1385157 (y : real) (x : real) : (term75 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem1385014 x y) (@lem1385156 y x)). Qed.
Lemma lem1385159 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1385160 (y : real) (x : real) : (term86 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (@lem1385159 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385167 (y : real) (x : real) : (term75 x y) = ((term64 x y) = (term85 y x)).
Proof. exact (TRANS (@lem1385157 y x) (@lem1385160 y x)). Qed.
Lemma lem1385168 (x : real) (y : real) : ((term64 x y) = (term85 y x)) = (term75 x y).
Proof. exact (SYM (@lem1385167 y x)). Qed.
Lemma lem1385170 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1385171 (y : real) (x : real) : ((term64 x y) = (term85 y x)) = (term88 y x).
Proof. exact (@lem1385170 ((term64 x y) = (term85 y x))). Qed.
Lemma lem1385172 (y : real) (x : real) : (term88 y x) = ((term64 x y) = (term85 y x)).
Proof. exact (SYM (@lem1385171 y x)). Qed.
Lemma lem1385173 (y : real) (x : real) (h1 : term89 y x) : term89 y x.
Proof. exact (h1). Qed.
Lemma lem1385176 (y : real) (x : real) (h1 : term90 y x) : term90 y x.
Proof. exact (h1). Qed.
Lemma lem1385177 (y : real) (x : real) : term91 y x.
Proof. exact (fun h0 : term90 y x => @lem1385176 y x h0). Qed.
Lemma lem1385178 (y : real) (x : real) (h1 : term91 y x) : term91 y x.
Proof. exact (h1). Qed.
Lemma lem1385179 (y : real) (x : real) (h1 : term90 y x) : term90 y x.
Proof. exact (h1). Qed.
Lemma lem1385180 (y : real) (x : real) (h1 : term90 y x) (h2 : term91 y x) : term90 y x.
Proof. exact (@lem1385178 y x h2 (@lem1385179 y x h1)). Qed.
Lemma lem1385181 (y : real) (x : real) (h1 : term90 y x) : term92 y x.
Proof. exact (fun h0 : term91 y x => @lem1385180 y x h1 h0). Qed.
Lemma lem1385182 (y : real) (x : real) (h1 : term91 y x) : term91 y x.
Proof. exact (h1). Qed.
Lemma lem1385183 (y : real) (x : real) (h1 : term90 y x) (h2 : term91 y x) : term90 y x.
Proof. exact (@lem1385181 y x h1 (@lem1385182 y x h2)). Qed.
Lemma lem1385184 (y : real) (x : real) (h1 : term91 y x) : term91 y x.
Proof. exact (fun h0 : term90 y x => @lem1385183 y x h0 h1). Qed.
Lemma lem1385185 (y : real) (x : real) : term93 y x.
Proof. exact (fun h0 : term91 y x => @lem1385184 y x h0). Qed.
Lemma lem1385188 (y : real) (x : real) : term91 y x.
Proof. exact (@lem1385185 y x (@lem1385177 y x)). Qed.
Lemma lem1385202 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1385203 : term94 = term95.
Proof. exact (@lem1385202 term96). Qed.
Lemma lem1385214 (y : real) (x : real) : (term97 y x) = (term97 y x).
Proof. exact (eq_refl (term97 y x)). Qed.
Lemma lem1385215 (y : real) (x : real) : (term90 y x) = (term98 y x).
Proof. exact (MK_COMB (@lem1385214 y x) (@lem1385203)). Qed.
Lemma lem1385218 (x : real) : (term99 x) = (term100 x).
Proof. exact (fun_ext (fun y : real => @lem1385215 y x)). Qed.
Lemma lem1385219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385220 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1385219) (@lem1385218 x)). Qed.
Lemma lem1385225 : term103 = term104.
Proof. exact (fun_ext (fun x : real => @lem1385220 x)). Qed.
Lemma lem1385226 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385235 : term105 = term106.
Proof. exact (MK_COMB (@lem1385226) (@lem1385225)). Qed.
Lemma lem1385244 (x : real) (y : real) : ((term107 y x) = (x = y)) = ((term107 y x) = (x = y)).
Proof. exact (eq_refl ((term107 y x) = (x = y))). Qed.
Lemma lem1385245 (x : real) : (term108 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1385244 x y)). Qed.
Lemma lem1385246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385247 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1385246) (@lem1385245 x)). Qed.
Lemma lem1385248 : term110 = term110.
Proof. exact (fun_ext (fun x : real => @lem1385247 x)). Qed.
Lemma lem1385249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385250 : term96 = term96.
Proof. exact (MK_COMB (@lem1385249) (@lem1385248)). Qed.
Lemma lem1385251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1385252 : term95 = term95.
Proof. exact (MK_COMB (@lem1385251) (@lem1385250)). Qed.
Lemma lem1385271 (y : real) (x : real) : (term97 y x) = (term97 y x).
Proof. exact (eq_refl (term97 y x)). Qed.
Lemma lem1385272 (y : real) (x : real) : (term98 y x) = (term98 y x).
Proof. exact (MK_COMB (@lem1385271 y x) (@lem1385252)). Qed.
Lemma lem1385273 (x : real) : (term100 x) = (term100 x).
Proof. exact (fun_ext (fun y : real => @lem1385272 y x)). Qed.
Lemma lem1385274 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385275 (x : real) : (term102 x) = (term102 x).
Proof. exact (MK_COMB (@lem1385274) (@lem1385273 x)). Qed.
Lemma lem1385276 : term104 = term104.
Proof. exact (fun_ext (fun x : real => @lem1385275 x)). Qed.
Lemma lem1385277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385278 : term106 = term106.
Proof. exact (MK_COMB (@lem1385277) (@lem1385276)). Qed.
Lemma lem1385311 : term105 = term106.
Proof. exact (TRANS (@lem1385235) (@lem1385278)). Qed.
Lemma lem1385312 : term106 = term105.
Proof. exact (SYM (@lem1385311)). Qed.
Lemma lem1385313 (y : real) (x : real) (h1 : term89 y x) : term89 y x.
Proof. exact (h1). Qed.
Lemma lem1385314 (h1 : term96) : term96.
Proof. exact (h1). Qed.
Lemma lem1385318 (x : real) (y : real) : (term111 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem1385322 (x : real) (y : real) : (term82 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1385326 (y : real) (x : real) : (term82 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1385327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385328 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1385327) (@lem1385322 x y)). Qed.
Lemma lem1385329 (y : real) (x : real) : (term114 y x) = (term107 y x).
Proof. exact (MK_COMB (@lem1385328 x y) (@lem1385326 y x)). Qed.
Lemma lem1385330 (y : real) (x : real) : (term115 y x) = (term114 y x).
Proof. exact (@lem17160 (term10 x y) (term10 y x)). Qed.
Lemma lem1385331 (y : real) (x : real) : (term115 y x) = (term107 y x).
Proof. exact (TRANS (@lem1385330 y x) (@lem1385329 y x)). Qed.
Lemma lem1385334 (y : real) (x : real) : (term85 y x) = (term85 y x).
Proof. exact (eq_refl (term85 y x)). Qed.
Lemma lem1385335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385336 (x : real) (y : real) : (term116 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1385335) (@lem1385318 x y)). Qed.
Lemma lem1385337 (y : real) (x : real) : (term118 y x) = (term119 y x).
Proof. exact (MK_COMB (@lem1385336 x y) (@lem1385334 y x)). Qed.
Lemma lem1385339 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem1385340 (y : real) (x : real) : (term121 y x) = (term122 y x).
Proof. exact (MK_COMB (@lem1385339 x y) (@lem1385331 y x)). Qed.
Lemma lem1385341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1385342 (y : real) (x : real) : (term123 y x) = (term124 y x).
Proof. exact (MK_COMB (@lem1385341) (@lem1385340 y x)). Qed.
Lemma lem1385343 (y : real) (x : real) : (term125 y x) = (term126 y x).
Proof. exact (MK_COMB (@lem1385342 y x) (@lem1385337 y x)). Qed.
Lemma lem1385344 (y : real) (x : real) : (term89 y x) = (term125 y x).
Proof. exact (@lem17646 (term64 x y) (term85 y x)). Qed.
Lemma lem1385349 (y : real) (x : real) : (term89 y x) = (term126 y x).
Proof. exact (TRANS (@lem1385344 y x) (@lem1385343 y x)). Qed.
Lemma lem1385359 (y : real) (x : real) : (term127 y x) = (term85 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem1385364 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1385365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1385366 (y : real) (x : real) : (term128 y x) = (term129 y x).
Proof. exact (MK_COMB (@lem1385365) (@lem1385359 y x)). Qed.
Lemma lem1385367 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1385366 y x) (@lem1385364 x y)). Qed.
Lemma lem1385372 (x : real) (y : real) : (term132 x y) = (term132 x y).
Proof. exact (eq_refl (term132 x y)). Qed.
Lemma lem1385373 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1385372 x y) (@lem1385367 x y)). Qed.
Lemma lem1385374 (x : real) (y : real) : ((term107 y x) = (x = y)) = (term133 x y).
Proof. exact (@lem17784 (term107 y x) (x = y)). Qed.
Lemma lem1385375 (x : real) (y : real) : ((term107 y x) = (x = y)) = (term134 x y).
Proof. exact (TRANS (@lem1385374 x y) (@lem1385373 x y)). Qed.
Lemma lem1385376 (x : real) : (term108 x) = (term135 x).
Proof. exact (fun_ext (fun y : real => @lem1385375 x y)). Qed.
Lemma lem1385377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385378 (x : real) : (term109 x) = (term136 x).
Proof. exact (MK_COMB (@lem1385377) (@lem1385376 x)). Qed.
Lemma lem1385379 : term110 = term137.
Proof. exact (fun_ext (fun x : real => @lem1385378 x)). Qed.
Lemma lem1385380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385381 : term96 = term138.
Proof. exact (MK_COMB (@lem1385380) (@lem1385379)). Qed.
Lemma lem1385387 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1385388 (P : real -> Prop) (Q : real -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem1385387 real P Q). Qed.
Lemma lem1385389 (x : real) : (term143 x) = (term144 x).
Proof. exact (@lem1385388 (term145 x) (term146 x)). Qed.
Lemma lem1385390 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (eq_refl (term147 x y)). Qed.
Lemma lem1385391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385392 (x : real) (y : real) : (term149 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1385391) (@lem1385390 x y)). Qed.
Lemma lem1385393 (x : real) (y : real) : (term150 x y) = (term131 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1385394 (x : real) (y : real) : (term151 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1385392 x y) (@lem1385393 x y)). Qed.
Lemma lem1385395 (x : real) : (term152 x) = (term135 x).
Proof. exact (fun_ext (fun y : real => @lem1385394 x y)). Qed.
Lemma lem1385396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385397 (x : real) : (term143 x) = (term136 x).
Proof. exact (MK_COMB (@lem1385396) (@lem1385395 x)). Qed.
Lemma lem1385398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1385399 (x : real) : (term153 x) = (term154 x).
Proof. exact (MK_COMB (@lem1385398) (@lem1385397 x)). Qed.
Lemma lem1385400 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (eq_refl (term147 x y)). Qed.
Lemma lem1385401 (x : real) : (term155 x) = (term145 x).
Proof. exact (fun_ext (fun y : real => @lem1385400 x y)). Qed.
Lemma lem1385402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385403 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1385402) (@lem1385401 x)). Qed.
Lemma lem1385404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385405 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1385404) (@lem1385403 x)). Qed.
Lemma lem1385406 (x : real) (y : real) : (term150 x y) = (term131 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1385407 (x : real) : (term160 x) = (term146 x).
Proof. exact (fun_ext (fun y : real => @lem1385406 x y)). Qed.
Lemma lem1385408 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385409 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1385408) (@lem1385407 x)). Qed.
Lemma lem1385410 (x : real) : (term144 x) = (term163 x).
Proof. exact (MK_COMB (@lem1385405 x) (@lem1385409 x)). Qed.
Lemma lem1385411 (x : real) : ((term143 x) = (term144 x)) = ((term136 x) = (term163 x)).
Proof. exact (MK_COMB (@lem1385399 x) (@lem1385410 x)). Qed.
Lemma lem1385412 (x : real) : (term136 x) = (term163 x).
Proof. exact (EQ_MP (@lem1385411 x) (@lem1385389 x)). Qed.
Lemma lem1385509 : term137 = term164.
Proof. exact (fun_ext (fun x : real => @lem1385412 x)). Qed.
Lemma lem1385510 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385511 : term138 = term165.
Proof. exact (MK_COMB (@lem1385510) (@lem1385509)). Qed.
Lemma lem1385513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1385514 (P : real -> Prop) (Q : real -> Prop) : (term141 P Q) = (term142 P Q).
Proof. exact (@lem1385513 real P Q). Qed.
Lemma lem1385515 : term166 = term167.
Proof. exact (@lem1385514 term168 term169). Qed.
Lemma lem1385516 (x : real) : (term170 x) = (term157 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1385517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385518 (x : real) : (term171 x) = (term159 x).
Proof. exact (MK_COMB (@lem1385517) (@lem1385516 x)). Qed.
Lemma lem1385519 (x : real) : (term172 x) = (term162 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1385520 (x : real) : (term173 x) = (term163 x).
Proof. exact (MK_COMB (@lem1385518 x) (@lem1385519 x)). Qed.
Lemma lem1385521 : term174 = term164.
Proof. exact (fun_ext (fun x : real => @lem1385520 x)). Qed.
Lemma lem1385522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385523 : term166 = term165.
Proof. exact (MK_COMB (@lem1385522) (@lem1385521)). Qed.
Lemma lem1385524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1385525 : term175 = term176.
Proof. exact (MK_COMB (@lem1385524) (@lem1385523)). Qed.
Lemma lem1385526 (x : real) : (term170 x) = (term157 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1385527 : term177 = term168.
Proof. exact (fun_ext (fun x : real => @lem1385526 x)). Qed.
Lemma lem1385528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385529 : term178 = term179.
Proof. exact (MK_COMB (@lem1385528) (@lem1385527)). Qed.
Lemma lem1385530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385531 : term180 = term181.
Proof. exact (MK_COMB (@lem1385530) (@lem1385529)). Qed.
Lemma lem1385532 (x : real) : (term172 x) = (term162 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1385533 : term182 = term169.
Proof. exact (fun_ext (fun x : real => @lem1385532 x)). Qed.
Lemma lem1385534 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385535 : term183 = term184.
Proof. exact (MK_COMB (@lem1385534) (@lem1385533)). Qed.
Lemma lem1385536 : term167 = term185.
Proof. exact (MK_COMB (@lem1385531) (@lem1385535)). Qed.
Lemma lem1385537 : (term166 = term167) = (term165 = term185).
Proof. exact (MK_COMB (@lem1385525) (@lem1385536)). Qed.
Lemma lem1385538 : term165 = term185.
Proof. exact (EQ_MP (@lem1385537) (@lem1385515)). Qed.
Lemma lem1385645 : term138 = term185.
Proof. exact (TRANS (@lem1385511) (@lem1385538)). Qed.
Lemma lem1385646 : term96 = term185.
Proof. exact (TRANS (@lem1385381) (@lem1385645)). Qed.
Lemma lem1385647 (h1 : term96) : term185.
Proof. exact (EQ_MP (@lem1385646) (@lem1385314 h1)). Qed.
Lemma lem1385699 (y : real) (x : real) (h1 : term89 y x) : term126 y x.
Proof. exact (EQ_MP (@lem1385349 y x) (@lem1385313 y x h1)). Qed.
Lemma lem1385724 (x : real) (y : real) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1385725 (x : real) : (term146 x) = (term146 x).
Proof. exact (fun_ext (fun y : real => @lem1385724 x y)). Qed.
Lemma lem1385726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385727 (x : real) : (term162 x) = (term162 x).
Proof. exact (MK_COMB (@lem1385726) (@lem1385725 x)). Qed.
Lemma lem1385728 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem1385727 x)). Qed.
Lemma lem1385729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385730 : term184 = term184.
Proof. exact (MK_COMB (@lem1385729) (@lem1385728)). Qed.
Lemma lem1385753 (x : real) (y : real) : (term148 x y) = (term148 x y).
Proof. exact (eq_refl (term148 x y)). Qed.
Lemma lem1385754 (x : real) : (term145 x) = (term145 x).
Proof. exact (fun_ext (fun y : real => @lem1385753 x y)). Qed.
Lemma lem1385755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385756 (x : real) : (term157 x) = (term157 x).
Proof. exact (MK_COMB (@lem1385755) (@lem1385754 x)). Qed.
Lemma lem1385757 : term168 = term168.
Proof. exact (fun_ext (fun x : real => @lem1385756 x)). Qed.
Lemma lem1385758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385759 : term179 = term179.
Proof. exact (MK_COMB (@lem1385758) (@lem1385757)). Qed.
Lemma lem1385760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1385761 : term181 = term181.
Proof. exact (MK_COMB (@lem1385760) (@lem1385759)). Qed.
Lemma lem1385762 : term185 = term185.
Proof. exact (MK_COMB (@lem1385761) (@lem1385730)). Qed.
Lemma lem1385763 (h1 : term96) : term185.
Proof. exact (EQ_MP (@lem1385762) (@lem1385647 h1)). Qed.
Lemma lem1385764 (h1 : term96) : term184.
Proof. exact (proj2 (@lem1385763 h1)). Qed.
Lemma lem1385765 (h1 : term96) : term179.
Proof. exact (proj1 (@lem1385763 h1)). Qed.
Lemma lem1385766 (y : real) (x : real) (h1 : term122 y x) : term122 y x.
Proof. exact (h1). Qed.
Lemma lem1385767 (y : real) (x : real) (h1 : term119 y x) : term119 y x.
Proof. exact (h1). Qed.
Lemma lem1385768 (y : real) (x : real) (h1 : term122 y x) : term107 y x.
Proof. exact (proj2 (@lem1385766 y x h1)). Qed.
Lemma lem1385772 (y : real) (x : real) (h1 : term119 y x) : term85 y x.
Proof. exact (proj2 (@lem1385767 y x h1)). Qed.
Lemma lem1385815 (x : real) (y : real) : (term131 x y) = (term131 x y).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem1385816 (x : real) : (term146 x) = (term146 x).
Proof. exact (fun_ext (fun y : real => @lem1385815 x y)). Qed.
Lemma lem1385817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385818 (x : real) : (term162 x) = (term162 x).
Proof. exact (MK_COMB (@lem1385817) (@lem1385816 x)). Qed.
Lemma lem1385819 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem1385818 x)). Qed.
Lemma lem1385820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385822 : term184 = term184.
Proof. exact (MK_COMB (@lem1385820) (@lem1385819)). Qed.
Lemma lem1385823 (h1 : term96) : term184.
Proof. exact (EQ_MP (@lem1385822) (@lem1385764 h1)). Qed.
Lemma lem1385853 (x : real) (y : real) : (term148 x y) = (term186 x y).
Proof. exact (@lem19699 (real_le x y) (real_le y x) (term64 x y)). Qed.
Lemma lem1385854 (x : real) : (term145 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1385853 x y)). Qed.
Lemma lem1385855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385856 (x : real) : (term157 x) = (term188 x).
Proof. exact (MK_COMB (@lem1385855) (@lem1385854 x)). Qed.
Lemma lem1385857 : term168 = term189.
Proof. exact (fun_ext (fun x : real => @lem1385856 x)). Qed.
Lemma lem1385858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385860 : term179 = term190.
Proof. exact (MK_COMB (@lem1385858) (@lem1385857)). Qed.
Lemma lem1385861 (h1 : term96) : term190.
Proof. exact (EQ_MP (@lem1385860) (@lem1385765 h1)). Qed.
Lemma lem1385891 (x : real) (y : real) (h1 : term10 x y) : term10 x y.
Proof. exact (h1). Qed.
Lemma lem1385909 (x : real) (y : real) : (term148 x y) = (term186 x y).
Proof. exact (@lem19699 (real_le x y) (real_le y x) (term64 x y)). Qed.
Lemma lem1385910 (x : real) : (term145 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1385909 x y)). Qed.
Lemma lem1385911 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385912 (x : real) : (term157 x) = (term188 x).
Proof. exact (MK_COMB (@lem1385911) (@lem1385910 x)). Qed.
Lemma lem1385913 : term168 = term189.
Proof. exact (fun_ext (fun x : real => @lem1385912 x)). Qed.
Lemma lem1385914 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1385916 : term179 = term190.
Proof. exact (MK_COMB (@lem1385914) (@lem1385913)). Qed.
Lemma lem1385917 (h1 : term96) : term190.
Proof. exact (EQ_MP (@lem1385916) (@lem1385765 h1)). Qed.
Lemma lem1385947 (y : real) (x : real) (h1 : term10 y x) : term10 y x.
Proof. exact (h1). Qed.
Lemma lem1385954 (_24510 : real) (h1 : term96) : term172 _24510.
Proof. exact (@lem1385823 h1 _24510). Qed.
Lemma lem1385955 (_24510 : real) : (term172 _24510) = (term162 _24510).
Proof. exact (eq_refl (term172 _24510)). Qed.
Lemma lem1385956 (_24510 : real) (h1 : term96) : term162 _24510.
Proof. exact (EQ_MP (@lem1385955 _24510) (@lem1385954 _24510 h1)). Qed.
Lemma lem1385957 (_24510 : real) (_24511 : real) (h1 : term96) : term150 _24510 _24511.
Proof. exact (@lem1385956 _24510 h1 _24511). Qed.
Lemma lem1385958 (_24510 : real) (_24511 : real) : (term150 _24510 _24511) = (term131 _24510 _24511).
Proof. exact (eq_refl (term150 _24510 _24511)). Qed.
Lemma lem1385959 (_24510 : real) (_24511 : real) (h1 : term96) : term131 _24510 _24511.
Proof. exact (EQ_MP (@lem1385958 _24510 _24511) (@lem1385957 _24510 _24511 h1)). Qed.
Lemma lem1385960 (_24512 : real) (h1 : term96) : term191 _24512.
Proof. exact (@lem1385861 h1 _24512). Qed.
Lemma lem1385961 (_24512 : real) : (term191 _24512) = (term188 _24512).
Proof. exact (eq_refl (term191 _24512)). Qed.
Lemma lem1385962 (_24512 : real) (h1 : term96) : term188 _24512.
Proof. exact (EQ_MP (@lem1385961 _24512) (@lem1385960 _24512 h1)). Qed.
Lemma lem1385963 (_24512 : real) (_24513 : real) (h1 : term96) : term192 _24512 _24513.
Proof. exact (@lem1385962 _24512 h1 _24513). Qed.
Lemma lem1385964 (_24512 : real) (_24513 : real) : (term192 _24512 _24513) = (term186 _24512 _24513).
Proof. exact (eq_refl (term192 _24512 _24513)). Qed.
Lemma lem1385965 (_24512 : real) (_24513 : real) (h1 : term96) : term186 _24512 _24513.
Proof. exact (EQ_MP (@lem1385964 _24512 _24513) (@lem1385963 _24512 _24513 h1)). Qed.
Lemma lem1385972 (_24516 : real) (h1 : term96) : term191 _24516.
Proof. exact (@lem1385917 h1 _24516). Qed.
Lemma lem1385973 (_24516 : real) : (term191 _24516) = (term188 _24516).
Proof. exact (eq_refl (term191 _24516)). Qed.
Lemma lem1385974 (_24516 : real) (h1 : term96) : term188 _24516.
Proof. exact (EQ_MP (@lem1385973 _24516) (@lem1385972 _24516 h1)). Qed.
Lemma lem1385975 (_24516 : real) (_24517 : real) (h1 : term96) : term192 _24516 _24517.
Proof. exact (@lem1385974 _24516 h1 _24517). Qed.
Lemma lem1385976 (_24516 : real) (_24517 : real) : (term192 _24516 _24517) = (term186 _24516 _24517).
Proof. exact (eq_refl (term192 _24516 _24517)). Qed.
Lemma lem1385977 (_24516 : real) (_24517 : real) (h1 : term96) : term186 _24516 _24517.
Proof. exact (EQ_MP (@lem1385976 _24516 _24517) (@lem1385975 _24516 _24517 h1)). Qed.
Lemma lem1386000 (_24510 : real) (_24511 : real) : (term131 _24510 _24511) = (term193 _24510 _24511).
Proof. exact (@lem1384595 (term10 _24510 _24511) (term10 _24511 _24510) (_24510 = _24511)). Qed.
Lemma lem1386001 (_24510 : real) (_24511 : real) (h1 : term96) : term193 _24510 _24511.
Proof. exact (EQ_MP (@lem1386000 _24510 _24511) (@lem1385959 _24510 _24511 h1)). Qed.
Lemma lem1386003 (y : real) (x : real) (h1 : term122 y x) : term64 x y.
Proof. exact (proj1 (@lem1385766 y x h1)). Qed.
Lemma lem1386033 (y : real) (x : real) (h1 : term119 y x) : x = y.
Proof. exact (proj1 (@lem1385767 y x h1)). Qed.
Lemma lem1386035 (x : real) (y : real) (h1 : term10 x y) : term10 x y.
Proof. exact (h1). Qed.
Lemma lem1386061 (y : real) (x : real) (h1 : term119 y x) : x = y.
Proof. exact (proj1 (@lem1385767 y x h1)). Qed.
Lemma lem1386063 (y : real) (x : real) (h1 : term10 y x) : term10 y x.
Proof. exact (h1). Qed.
Lemma lem1386104 (y : real) : (term194 y) = (term194 y).
Proof. exact (eq_refl (term194 y)). Qed.
Lemma lem1386105 (y : real) (x : real) (h1 : term119 y x) : (term195 y x) = (term196 y).
Proof. exact (MK_COMB (@lem1386104 y) (@lem1386033 y x h1)). Qed.
Lemma lem1386106 (y : real) : (term196 y) = (term197 y).
Proof. exact (eq_refl (term196 y)). Qed.
Lemma lem1386107 (y : real) (x : real) : (term198 y x) = (term198 y x).
Proof. exact (eq_refl (term198 y x)). Qed.
Lemma lem1386108 (x : real) (y : real) : ((term195 y x) = (term196 y)) = ((term195 y x) = (term197 y)).
Proof. exact (MK_COMB (@lem1386107 y x) (@lem1386106 y)). Qed.
Lemma lem1386109 (x : real) (y : real) : (term195 y x) = (term10 x y).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem1386110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1386111 (x : real) (y : real) : (term198 y x) = (term47 x y).
Proof. exact (MK_COMB (@lem1386110) (@lem1386109 x y)). Qed.
Lemma lem1386112 (y : real) : (term197 y) = (term197 y).
Proof. exact (eq_refl (term197 y)). Qed.
Lemma lem1386113 (x : real) (y : real) : ((term195 y x) = (term197 y)) = ((term10 x y) = (term197 y)).
Proof. exact (MK_COMB (@lem1386111 x y) (@lem1386112 y)). Qed.
Lemma lem1386114 (x : real) (y : real) : ((term195 y x) = (term196 y)) = ((term10 x y) = (term197 y)).
Proof. exact (TRANS (@lem1386108 x y) (@lem1386113 x y)). Qed.
Lemma lem1386115 (y : real) (x : real) (h1 : term119 y x) : (term10 x y) = (term197 y).
Proof. exact (EQ_MP (@lem1386114 x y) (@lem1386105 y x h1)). Qed.
Lemma lem1386116 (y : real) (x : real) (h1 : term10 x y) (h2 : term119 y x) : term197 y.
Proof. exact (EQ_MP (@lem1386115 y x h2) (@lem1386035 x y h1)). Qed.
Lemma lem1386144 (_24512 : real) (_24513 : real) (h1 : term96) : term199 _24512 _24513.
Proof. exact (proj2 (@lem1385965 _24512 _24513 h1)). Qed.
Lemma lem1386173 (y : real) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem1386174 (y : real) (x : real) (h1 : term119 y x) : (term201 y x) = (term202 y).
Proof. exact (MK_COMB (@lem1386173 y) (@lem1386061 y x h1)). Qed.
Lemma lem1386175 (y : real) : (term202 y) = (term197 y).
Proof. exact (eq_refl (term202 y)). Qed.
Lemma lem1386176 (y : real) (x : real) : (term203 y x) = (term203 y x).
Proof. exact (eq_refl (term203 y x)). Qed.
Lemma lem1386177 (x : real) (y : real) : ((term201 y x) = (term202 y)) = ((term201 y x) = (term197 y)).
Proof. exact (MK_COMB (@lem1386176 y x) (@lem1386175 y)). Qed.
Lemma lem1386178 (y : real) (x : real) : (term201 y x) = (term10 y x).
Proof. exact (eq_refl (term201 y x)). Qed.
Lemma lem1386179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1386180 (y : real) (x : real) : (term203 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1386179) (@lem1386178 y x)). Qed.
Lemma lem1386181 (y : real) : (term197 y) = (term197 y).
Proof. exact (eq_refl (term197 y)). Qed.
Lemma lem1386182 (x : real) (y : real) : ((term201 y x) = (term197 y)) = ((term10 y x) = (term197 y)).
Proof. exact (MK_COMB (@lem1386180 y x) (@lem1386181 y)). Qed.
Lemma lem1386183 (x : real) (y : real) : ((term201 y x) = (term202 y)) = ((term10 y x) = (term197 y)).
Proof. exact (TRANS (@lem1386177 x y) (@lem1386182 x y)). Qed.
Lemma lem1386184 (y : real) (x : real) (h1 : term119 y x) : (term10 y x) = (term197 y).
Proof. exact (EQ_MP (@lem1386183 x y) (@lem1386174 y x h1)). Qed.
Lemma lem1386185 (y : real) (x : real) (h1 : term10 y x) (h2 : term119 y x) : term197 y.
Proof. exact (EQ_MP (@lem1386184 y x h2) (@lem1386063 y x h1)). Qed.
Lemma lem1386213 (_24516 : real) (_24517 : real) (h1 : term96) : term199 _24516 _24517.
Proof. exact (proj2 (@lem1385977 _24516 _24517 h1)). Qed.
Lemma lem1386236 (y : real) (x : real) (h1 : term122 y x) : real_le x y.
Proof. exact (proj1 (@lem1385768 y x h1)). Qed.
Lemma lem1386237 (y : real) (x : real) (h1 : term122 y x) : term204 x y.
Proof. exact (fun h0 : term10 x y => @lem1386236 y x h1). Qed.
Lemma lem1386239 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386240 (x : real) (y : real) : (term204 x y) = (real_le x y).
Proof. exact (@lem1386239 (real_le x y)). Qed.
Lemma lem1386241 (y : real) (x : real) (h1 : term122 y x) : real_le x y.
Proof. exact (EQ_MP (@lem1386240 x y) (@lem1386237 y x h1)). Qed.
Lemma lem1386243 (y : real) (x : real) (h1 : term122 y x) : real_le y x.
Proof. exact (proj2 (@lem1385768 y x h1)). Qed.
Lemma lem1386244 (y : real) (x : real) (h1 : term122 y x) : term204 y x.
Proof. exact (fun h0 : term10 y x => @lem1386243 y x h1). Qed.
Lemma lem1386246 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386247 (y : real) (x : real) : (term204 y x) = (real_le y x).
Proof. exact (@lem1386246 (real_le y x)). Qed.
Lemma lem1386248 (y : real) (x : real) (h1 : term122 y x) : real_le y x.
Proof. exact (EQ_MP (@lem1386247 y x) (@lem1386244 y x h1)). Qed.
Lemma lem1386264 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1386265 (_24511 : real) (_24510 : real) : (term206 _24510 _24511) = (term207 _24511 _24510).
Proof. exact (@lem1386264 (_24510 = _24511) (term10 _24511 _24510)). Qed.
Lemma lem1386273 (_24510 : real) (_24511 : real) : (term84 _24510 _24511) = (term84 _24510 _24511).
Proof. exact (eq_refl (term84 _24510 _24511)). Qed.
Lemma lem1386274 (_24511 : real) (_24510 : real) : (term193 _24510 _24511) = (term208 _24511 _24510).
Proof. exact (MK_COMB (@lem1386273 _24510 _24511) (@lem1386265 _24511 _24510)). Qed.
Lemma lem1386278 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1386279 (_24511 : real) (_24510 : real) : (term208 _24511 _24510) = (term209 _24511 _24510).
Proof. exact (@lem1386278 (_24510 = _24511) (term10 _24510 _24511) (term10 _24511 _24510)). Qed.
Lemma lem1386297 (_24511 : real) (_24510 : real) : (term193 _24510 _24511) = (term209 _24511 _24510).
Proof. exact (TRANS (@lem1386274 _24511 _24510) (@lem1386279 _24511 _24510)). Qed.
Lemma lem1386298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1386299 (_24511 : real) (_24510 : real) : (term210 _24510 _24511) = (term211 _24511 _24510).
Proof. exact (MK_COMB (@lem1386298) (@lem1386297 _24511 _24510)). Qed.
Lemma lem1386317 (_24511 : real) (_24510 : real) : (term209 _24511 _24510) = (term209 _24511 _24510).
Proof. exact (eq_refl (term209 _24511 _24510)). Qed.
Lemma lem1386318 (_24511 : real) (_24510 : real) : ((term193 _24510 _24511) = (term209 _24511 _24510)) = ((term209 _24511 _24510) = (term209 _24511 _24510)).
Proof. exact (MK_COMB (@lem1386299 _24511 _24510) (@lem1386317 _24511 _24510)). Qed.
Lemma lem1386320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1386321 (x : Prop) : (x = x) = True.
Proof. exact (@lem1386320 Prop x). Qed.
Lemma lem1386322 (_24511 : real) (_24510 : real) : ((term209 _24511 _24510) = (term209 _24511 _24510)) = True.
Proof. exact (@lem1386321 (term209 _24511 _24510)). Qed.
Lemma lem1386323 (_24511 : real) (_24510 : real) : ((term193 _24510 _24511) = (term209 _24511 _24510)) = True.
Proof. exact (TRANS (@lem1386318 _24511 _24510) (@lem1386322 _24511 _24510)). Qed.
Lemma lem1386324 (_24511 : real) (_24510 : real) : True = ((term193 _24510 _24511) = (term209 _24511 _24510)).
Proof. exact (SYM (@lem1386323 _24511 _24510)). Qed.
Lemma lem1386325 (_24511 : real) (_24510 : real) : (term193 _24510 _24511) = (term209 _24511 _24510).
Proof. exact (EQ_MP (@lem1386324 _24511 _24510) (@lem0)). Qed.
Lemma lem1386326 (_24511 : real) (_24510 : real) (h1 : term96) : term209 _24511 _24510.
Proof. exact (EQ_MP (@lem1386325 _24511 _24510) (@lem1386001 _24510 _24511 h1)). Qed.
Lemma lem1386328 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1386329 (_24510 : real) (_24511 : real) : (term209 _24511 _24510) = (term213 _24510 _24511).
Proof. exact (@lem1386328 (term85 _24511 _24510) (_24510 = _24511)). Qed.
Lemma lem1386331 (a : Prop) (b : Prop) : (term214 a b) = (term215 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1386332 (_24511 : real) (_24510 : real) : (term115 _24511 _24510) = (term114 _24511 _24510).
Proof. exact (@lem1386331 (term10 _24510 _24511) (term10 _24511 _24510)). Qed.
Lemma lem1386334 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1386335 (_24510 : real) (_24511 : real) : (term82 _24510 _24511) = (real_le _24510 _24511).
Proof. exact (@lem1386334 (real_le _24510 _24511)). Qed.
Lemma lem1386336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386337 (_24510 : real) (_24511 : real) : (term112 _24510 _24511) = (term113 _24510 _24511).
Proof. exact (MK_COMB (@lem1386336) (@lem1386335 _24510 _24511)). Qed.
Lemma lem1386339 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1386340 (_24511 : real) (_24510 : real) : (term82 _24511 _24510) = (real_le _24511 _24510).
Proof. exact (@lem1386339 (real_le _24511 _24510)). Qed.
Lemma lem1386341 (_24511 : real) (_24510 : real) : (term114 _24511 _24510) = (term107 _24511 _24510).
Proof. exact (MK_COMB (@lem1386337 _24510 _24511) (@lem1386340 _24511 _24510)). Qed.
Lemma lem1386342 (_24511 : real) (_24510 : real) : (term115 _24511 _24510) = (term107 _24511 _24510).
Proof. exact (TRANS (@lem1386332 _24511 _24510) (@lem1386341 _24511 _24510)). Qed.
Lemma lem1386343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1386344 (_24511 : real) (_24510 : real) : (term216 _24511 _24510) = (term217 _24511 _24510).
Proof. exact (MK_COMB (@lem1386343) (@lem1386342 _24511 _24510)). Qed.
Lemma lem1386345 (_24510 : real) (_24511 : real) : (_24510 = _24511) = (_24510 = _24511).
Proof. exact (eq_refl (_24510 = _24511)). Qed.
Lemma lem1386346 (_24510 : real) (_24511 : real) : (term213 _24510 _24511) = (term218 _24510 _24511).
Proof. exact (MK_COMB (@lem1386344 _24511 _24510) (@lem1386345 _24510 _24511)). Qed.
Lemma lem1386347 (_24510 : real) (_24511 : real) : (term209 _24511 _24510) = (term218 _24510 _24511).
Proof. exact (TRANS (@lem1386329 _24510 _24511) (@lem1386346 _24510 _24511)). Qed.
Lemma lem1386349 (y : real) (x : real) (h1 : term122 y x) : term107 y x.
Proof. exact (conj (@lem1386241 y x h1) (@lem1386248 y x h1)). Qed.
Lemma lem1386351 (_24510 : real) (_24511 : real) (h1 : term96) : term218 _24510 _24511.
Proof. exact (EQ_MP (@lem1386347 _24510 _24511) (@lem1386326 _24511 _24510 h1)). Qed.
Lemma lem1386352 (x : real) (y : real) (h1 : term96) : term218 x y.
Proof. exact (@lem1386351 x y h1). Qed.
Lemma lem1386355 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : x = y.
Proof. exact (@lem1386352 x y h1 (@lem1386349 y x h2)). Qed.
Lemma lem1386356 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : term219 x y.
Proof. exact (fun h0 : term64 x y => @lem1386355 y x h1 h2). Qed.
Lemma lem1386358 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386359 (x : real) (y : real) : (term219 x y) = (x = y).
Proof. exact (@lem1386358 (x = y)). Qed.
Lemma lem1386360 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : x = y.
Proof. exact (EQ_MP (@lem1386359 x y) (@lem1386356 y x h1 h2)). Qed.
Lemma lem1386363 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1386365 (x : real) (y : real) : (term64 x y) = (term220 x y).
Proof. exact (@lem1386363 (x = y)). Qed.
Lemma lem1386368 (y : real) (x : real) (h1 : term122 y x) : term220 x y.
Proof. exact (EQ_MP (@lem1386365 x y) (@lem1386003 y x h1)). Qed.
Lemma lem1386371 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : False.
Proof. exact (@lem1386368 y x h2 (@lem1386360 y x h1 h2)). Qed.
Lemma lem1386372 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : term221.
Proof. exact (fun h0 : ~ False => @lem1386371 y x h1 h2). Qed.
Lemma lem1386374 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386375 : term221 = False.
Proof. exact (@lem1386374 False). Qed.
Lemma lem1386376 (y : real) (x : real) (h1 : term96) (h2 : term122 y x) : False.
Proof. exact (EQ_MP (@lem1386375) (@lem1386372 y x h1 h2)). Qed.
Lemma lem1386399 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1386400 (y : real) : y = y.
Proof. exact (@lem1386399 y). Qed.
Lemma lem1386401 (y : real) : term222 y.
Proof. exact (fun h0 : term223 y => @lem1386400 y). Qed.
Lemma lem1386403 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386404 (y : real) : (term222 y) = (y = y).
Proof. exact (@lem1386403 (y = y)). Qed.
Lemma lem1386405 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1386404 y) (@lem1386401 y)). Qed.
Lemma lem1386407 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1386408 (_24513 : real) (_24512 : real) : (term199 _24512 _24513) = (term224 _24513 _24512).
Proof. exact (@lem1386407 (term64 _24512 _24513) (real_le _24513 _24512)). Qed.
Lemma lem1386410 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1386411 (_24512 : real) (_24513 : real) : (term111 _24512 _24513) = (_24512 = _24513).
Proof. exact (@lem1386410 (_24512 = _24513)). Qed.
Lemma lem1386412 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1386413 (_24512 : real) (_24513 : real) : (term225 _24512 _24513) = (term226 _24512 _24513).
Proof. exact (MK_COMB (@lem1386412) (@lem1386411 _24512 _24513)). Qed.
Lemma lem1386414 (_24513 : real) (_24512 : real) : (real_le _24513 _24512) = (real_le _24513 _24512).
Proof. exact (eq_refl (real_le _24513 _24512)). Qed.
Lemma lem1386415 (_24513 : real) (_24512 : real) : (term224 _24513 _24512) = (term227 _24513 _24512).
Proof. exact (MK_COMB (@lem1386413 _24512 _24513) (@lem1386414 _24513 _24512)). Qed.
Lemma lem1386416 (_24513 : real) (_24512 : real) : (term199 _24512 _24513) = (term227 _24513 _24512).
Proof. exact (TRANS (@lem1386408 _24513 _24512) (@lem1386415 _24513 _24512)). Qed.
Lemma lem1386419 (_24513 : real) (_24512 : real) (h1 : term96) : term227 _24513 _24512.
Proof. exact (EQ_MP (@lem1386416 _24513 _24512) (@lem1386144 _24512 _24513 h1)). Qed.
Lemma lem1386420 (y : real) (h1 : term96) : term228 y.
Proof. exact (@lem1386419 y y h1). Qed.
Lemma lem1386423 (y : real) (h1 : term96) : real_le y y.
Proof. exact (@lem1386420 y h1 (@lem1386405 y)). Qed.
Lemma lem1386424 (y : real) (h1 : term96) : term229 y.
Proof. exact (fun h0 : term197 y => @lem1386423 y h1). Qed.
Lemma lem1386426 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386427 (y : real) : (term229 y) = (real_le y y).
Proof. exact (@lem1386426 (real_le y y)). Qed.
Lemma lem1386428 (y : real) (h1 : term96) : real_le y y.
Proof. exact (EQ_MP (@lem1386427 y) (@lem1386424 y h1)). Qed.
Lemma lem1386431 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1386433 (y : real) : (term197 y) = (term230 y).
Proof. exact (@lem1386431 (real_le y y)). Qed.
Lemma lem1386436 (y : real) (x : real) (h1 : term10 x y) (h2 : term119 y x) : term230 y.
Proof. exact (EQ_MP (@lem1386433 y) (@lem1386116 y x h1 h2)). Qed.
Lemma lem1386439 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : False.
Proof. exact (@lem1386436 y x h2 h3 (@lem1386428 y h1)). Qed.
Lemma lem1386440 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : term221.
Proof. exact (fun h0 : ~ False => @lem1386439 y x h1 h2 h3). Qed.
Lemma lem1386442 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386443 : term221 = False.
Proof. exact (@lem1386442 False). Qed.
Lemma lem1386467 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1386468 (y : real) : y = y.
Proof. exact (@lem1386467 y). Qed.
Lemma lem1386469 (y : real) : term222 y.
Proof. exact (fun h0 : term223 y => @lem1386468 y). Qed.
Lemma lem1386471 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386472 (y : real) : (term222 y) = (y = y).
Proof. exact (@lem1386471 (y = y)). Qed.
Lemma lem1386473 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1386472 y) (@lem1386469 y)). Qed.
Lemma lem1386475 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1386476 (_24517 : real) (_24516 : real) : (term199 _24516 _24517) = (term224 _24517 _24516).
Proof. exact (@lem1386475 (term64 _24516 _24517) (real_le _24517 _24516)). Qed.
Lemma lem1386478 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1386479 (_24516 : real) (_24517 : real) : (term111 _24516 _24517) = (_24516 = _24517).
Proof. exact (@lem1386478 (_24516 = _24517)). Qed.
Lemma lem1386480 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1386481 (_24516 : real) (_24517 : real) : (term225 _24516 _24517) = (term226 _24516 _24517).
Proof. exact (MK_COMB (@lem1386480) (@lem1386479 _24516 _24517)). Qed.
Lemma lem1386482 (_24517 : real) (_24516 : real) : (real_le _24517 _24516) = (real_le _24517 _24516).
Proof. exact (eq_refl (real_le _24517 _24516)). Qed.
Lemma lem1386483 (_24517 : real) (_24516 : real) : (term224 _24517 _24516) = (term227 _24517 _24516).
Proof. exact (MK_COMB (@lem1386481 _24516 _24517) (@lem1386482 _24517 _24516)). Qed.
Lemma lem1386484 (_24517 : real) (_24516 : real) : (term199 _24516 _24517) = (term227 _24517 _24516).
Proof. exact (TRANS (@lem1386476 _24517 _24516) (@lem1386483 _24517 _24516)). Qed.
Lemma lem1386487 (_24517 : real) (_24516 : real) (h1 : term96) : term227 _24517 _24516.
Proof. exact (EQ_MP (@lem1386484 _24517 _24516) (@lem1386213 _24516 _24517 h1)). Qed.
Lemma lem1386488 (y : real) (h1 : term96) : term228 y.
Proof. exact (@lem1386487 y y h1). Qed.
Lemma lem1386491 (y : real) (h1 : term96) : real_le y y.
Proof. exact (@lem1386488 y h1 (@lem1386473 y)). Qed.
Lemma lem1386492 (y : real) (h1 : term96) : term229 y.
Proof. exact (fun h0 : term197 y => @lem1386491 y h1). Qed.
Lemma lem1386494 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386495 (y : real) : (term229 y) = (real_le y y).
Proof. exact (@lem1386494 (real_le y y)). Qed.
Lemma lem1386496 (y : real) (h1 : term96) : real_le y y.
Proof. exact (EQ_MP (@lem1386495 y) (@lem1386492 y h1)). Qed.
Lemma lem1386499 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1386501 (y : real) : (term197 y) = (term230 y).
Proof. exact (@lem1386499 (real_le y y)). Qed.
Lemma lem1386504 (y : real) (x : real) (h1 : term10 y x) (h2 : term119 y x) : term230 y.
Proof. exact (EQ_MP (@lem1386501 y) (@lem1386185 y x h1 h2)). Qed.
Lemma lem1386507 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : False.
Proof. exact (@lem1386504 y x h2 h3 (@lem1386496 y h1)). Qed.
Lemma lem1386508 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : term221.
Proof. exact (fun h0 : ~ False => @lem1386507 y x h1 h2 h3). Qed.
Lemma lem1386510 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1386511 : term221 = False.
Proof. exact (@lem1386510 False). Qed.
Lemma lem1386513 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386511) (@lem1386508 y x h1 h2 h3)). Qed.
Lemma lem1386514 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386443) (@lem1386440 y x h1 h2 h3)). Qed.
Lemma lem1386515 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1386513 y x h1 h2 h3) (fun h4 : False => @lem1386063 y x h2)). Qed.
Lemma lem1386516 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386515 y x h1 h2 h3) (@lem1386063 y x h2)). Qed.
Lemma lem1386517 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : (term10 x y) = False.
Proof. exact (prop_ext (fun h4 : term10 x y => @lem1386514 y x h1 h2 h3) (fun h4 : False => @lem1386035 x y h2)). Qed.
Lemma lem1386518 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386517 y x h1 h2 h3) (@lem1386035 x y h2)). Qed.
Lemma lem1386519 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1386516 y x h1 h2 h3) (fun h4 : False => @lem1385947 y x h2)). Qed.
Lemma lem1386520 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386519 y x h1 h2 h3) (@lem1385947 y x h2)). Qed.
Lemma lem1386521 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : (term10 x y) = False.
Proof. exact (prop_ext (fun h4 : term10 x y => @lem1386518 y x h1 h2 h3) (fun h4 : False => @lem1385891 x y h2)). Qed.
Lemma lem1386522 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386521 y x h1 h2 h3) (@lem1385891 x y h2)). Qed.
Lemma lem1386523 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : (term10 y x) = False.
Proof. exact (prop_ext (fun h4 : term10 y x => @lem1386520 y x h1 h2 h3) (fun h4 : False => @lem1385947 y x h2)). Qed.
Lemma lem1386524 (y : real) (x : real) (h1 : term96) (h2 : term10 y x) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386523 y x h1 h2 h3) (@lem1385947 y x h2)). Qed.
Lemma lem1386525 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : (term10 x y) = False.
Proof. exact (prop_ext (fun h4 : term10 x y => @lem1386522 y x h1 h2 h3) (fun h4 : False => @lem1385891 x y h2)). Qed.
Lemma lem1386526 (y : real) (x : real) (h1 : term96) (h2 : term10 x y) (h3 : term119 y x) : False.
Proof. exact (EQ_MP (@lem1386525 y x h1 h2 h3) (@lem1385891 x y h2)). Qed.
Lemma lem1386527 (y : real) (x : real) (h1 : term96) (h2 : term119 y x) : False.
Proof. exact (or_elim (@lem1385772 y x h2) (fun h0 : term10 x y => @lem1386526 y x h1 h0 h2) (fun h0 : term10 y x => @lem1386524 y x h1 h0 h2)). Qed.
Lemma lem1386528 (y : real) (x : real) (h1 : term96) (h2 : term89 y x) : False.
Proof. exact (or_elim (@lem1385699 y x h2) (fun h0 : term122 y x => @lem1386376 y x h1 h0) (fun h0 : term119 y x => @lem1386527 y x h1 h0)). Qed.
Lemma lem1386529 (y : real) (x : real) (h1 : term89 y x) : term94.
Proof. exact (fun h0 : term96 => @lem1386528 y x h0 h1). Qed.
Lemma lem1386530 : term94 = term95.
Proof. exact (@lem69 term96). Qed.
Lemma lem1386531 (y : real) (x : real) (h1 : term89 y x) : term95.
Proof. exact (EQ_MP (@lem1386530) (@lem1386529 y x h1)). Qed.
Lemma lem1386532 (y : real) (x : real) : term98 y x.
Proof. exact (fun h0 : term89 y x => @lem1386531 y x h0). Qed.
Lemma lem1386537 (x : real) : term102 x.
Proof. exact (fun y : real => @lem1386532 y x). Qed.
Lemma lem1386542 : term106.
Proof. exact (fun x : real => @lem1386537 x). Qed.
Lemma lem1386543 : term105.
Proof. exact (EQ_MP (@lem1385312) (@lem1386542)). Qed.
Lemma lem1386544 (x : real) : term231 x.
Proof. exact (@lem1386543 x). Qed.
Lemma lem1386545 (x : real) : (term231 x) = (term101 x).
Proof. exact (eq_refl (term231 x)). Qed.
Lemma lem1386546 (x : real) : term101 x.
Proof. exact (EQ_MP (@lem1386545 x) (@lem1386544 x)). Qed.
Lemma lem1386547 (x : real) (y : real) : term232 x y.
Proof. exact (@lem1386546 x y). Qed.
Lemma lem1386548 (y : real) (x : real) : (term232 x y) = (term90 y x).
Proof. exact (eq_refl (term232 x y)). Qed.
Lemma lem1386549 (y : real) (x : real) : term90 y x.
Proof. exact (EQ_MP (@lem1386548 y x) (@lem1386547 x y)). Qed.
Lemma lem1386551 (y : real) (x : real) : term90 y x.
Proof. exact (@lem1385188 y x (@lem1386549 y x)). Qed.
Lemma lem1386552 (y : real) (x : real) (h1 : term89 y x) : term94.
Proof. exact (@lem1386551 y x (@lem1385173 y x h1)). Qed.
Lemma lem1386553 (y : real) (x : real) (h1 : term89 y x) : False.
Proof. exact (@lem1386552 y x h1 (@lem1339379)). Qed.
Lemma lem1386554 (y : real) (x : real) (h1 : term89 y x) : (term89 y x) = False.
Proof. exact (prop_ext (fun h2 : term89 y x => @lem1386553 y x h1) (fun h2 : False => @lem1385173 y x h1)). Qed.
Lemma lem1386555 (y : real) (x : real) (h1 : term89 y x) : False.
Proof. exact (EQ_MP (@lem1386554 y x h1) (@lem1385173 y x h1)). Qed.
Lemma lem1386556 (y : real) (x : real) : term88 y x.
Proof. exact (fun h0 : term89 y x => @lem1386555 y x h0). Qed.
Lemma lem1386557 (y : real) (x : real) : (term64 x y) = (term85 y x).
Proof. exact (EQ_MP (@lem1385172 y x) (@lem1386556 y x)). Qed.
Lemma lem1386558 (x : real) (y : real) : term75 x y.
Proof. exact (EQ_MP (@lem1385168 x y) (@lem1386557 y x)). Qed.
Lemma lem1386559 (x : real) (y : real) : term80 x y.
Proof. exact (EQ_MP (@lem1384995 x y) (@lem1386558 x y)). Qed.

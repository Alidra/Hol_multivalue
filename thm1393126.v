Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1393126_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RID_spec.
Require Import REAL_LE_LT_spec.
Require Import REAL_LT_ADD_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338512_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1386579 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1386580 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1386581 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1386580 t1) (@lem1386579 t1)). Qed.
Lemma lem1386582 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1386581 t1 t2). Qed.
Lemma lem1386583 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1386584 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1386583 t1 t2) (@lem1386582 t1 t2)). Qed.
Lemma lem1386585 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1386584 t1 t2 t3). Qed.
Lemma lem1386586 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1386587 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1386586 t1 t2 t3) (@lem1386585 t1 t2 t3)). Qed.
Lemma lem1386588 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1386587 t1 t2 t3)). Qed.
Lemma lem1386589 (x : real) : term7 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1386590 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1386591 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1386590 x) (@lem1386589 x)). Qed.
Lemma lem1386592 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1386591 x y). Qed.
Lemma lem1386593 (x : real) (y : real) : (term9 x y) = ((real_le x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1386595 (y : real) : term11 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1386596 (y : real) : (term11 y) = (term12 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1386597 (y : real) : term12 y.
Proof. exact (EQ_MP (@lem1386596 y) (@lem1386595 y)). Qed.
Lemma lem1386598 (y : real) (x : real) : term13 y x.
Proof. exact (@lem1386597 y x). Qed.
Lemma lem1386599 (y : real) (x : real) : (term13 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1386601 (y : real) : term14 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1386602 (y : real) : (term14 y) = (term15 y).
Proof. exact (eq_refl (term14 y)). Qed.
Lemma lem1386603 (y : real) : term15 y.
Proof. exact (EQ_MP (@lem1386602 y) (@lem1386601 y)). Qed.
Lemma lem1386604 (y : real) (x : real) : term16 y x.
Proof. exact (@lem1386603 y x). Qed.
Lemma lem1386605 (y : real) (x : real) : (term16 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem1386607 (x : real) : term17 x.
Proof. exact (@lem1361590 x). Qed.
Lemma lem1386608 (x : real) : (term17 x) = ((term18 x) = x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1386610 (x : real) : term19 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1386611 (x : real) : (term19 x) = ((term20 x) = x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1386618 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386619 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386618 p q p' q'). Qed.
Lemma lem1386620 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386619 p q p'). Qed.
Lemma lem1386621 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1386620 (term25 x y) ((real_add x y) = term26)). Qed.
Lemma lem1386622 (x : real) (y : real) (p' : Prop) : term27 x y p'.
Proof. exact (@lem1386621 x y p'). Qed.
Lemma lem1386623 (x : real) (y : real) (p' : Prop) : (term27 x y p') = (term28 x y p').
Proof. exact (eq_refl (term27 x y p')). Qed.
Lemma lem1386624 (x : real) (y : real) (p' : Prop) : term28 x y p'.
Proof. exact (EQ_MP (@lem1386623 x y p') (@lem1386622 x y p')). Qed.
Lemma lem1386625 (x : real) (y : real) (p' : Prop) (q' : Prop) : term29 x y p' q'.
Proof. exact (@lem1386624 x y p' q'). Qed.
Lemma lem1386626 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term29 x y p' q') = (term30 x y p' q').
Proof. exact (eq_refl (term29 x y p' q')). Qed.
Lemma lem1386627 (x : real) (y : real) (p' : Prop) (q' : Prop) : term30 x y p' q'.
Proof. exact (EQ_MP (@lem1386626 x y p' q') (@lem1386625 x y p' q')). Qed.
Lemma lem1386634 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1386635 (x : real) (y : real) (q' : Prop) : term31 x y q'.
Proof. exact (@lem1386627 x y (term25 x y) q'). Qed.
Lemma lem1386636 (x : real) (y : real) (q' : Prop) : term32 x y q'.
Proof. exact (@lem1386635 x y q' (@lem1386634 x y)). Qed.
Lemma lem1386637 (x : real) (y : real) (h1 : term25 x y) : term25 x y.
Proof. exact (h1). Qed.
Lemma lem1386643 (x : real) (y : real) (h1 : term25 x y) : x = term26.
Proof. exact (proj1 (@lem1386637 x y h1)). Qed.
Lemma lem1386644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1386645 (x : real) (y : real) (h1 : term25 x y) : (real_add x) = term33.
Proof. exact (MK_COMB (@lem1386644) (@lem1386643 x y h1)). Qed.
Lemma lem1386647 (x : real) (y : real) (h1 : term25 x y) : y = term26.
Proof. exact (proj2 (@lem1386637 x y h1)). Qed.
Lemma lem1386648 (x : real) (y : real) (h1 : term25 x y) : (real_add x y) = term34.
Proof. exact (MK_COMB (@lem1386645 x y h1) (@lem1386647 x y h1)). Qed.
Lemma lem1386650 (x : real) : (term20 x) = x.
Proof. exact (EQ_MP (@lem1386611 x) (@lem1386610 x)). Qed.
Lemma lem1386651 : term34 = term26.
Proof. exact (@lem1386650 term26). Qed.
Lemma lem1386652 (x : real) (y : real) (h1 : term25 x y) : (real_add x y) = term26.
Proof. exact (TRANS (@lem1386648 x y h1) (@lem1386651)). Qed.
Lemma lem1386653 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1386654 (x : real) (y : real) (h1 : term25 x y) : (term35 x y) = term36.
Proof. exact (MK_COMB (@lem1386653) (@lem1386652 x y h1)). Qed.
Lemma lem1386655 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem1386656 (x : real) (y : real) (h1 : term25 x y) : ((real_add x y) = term26) = (term26 = term26).
Proof. exact (MK_COMB (@lem1386654 x y h1) (@lem1386655)). Qed.
Lemma lem1386658 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1386659 (x : real) : (x = x) = True.
Proof. exact (@lem1386658 real x). Qed.
Lemma lem1386660 : (term26 = term26) = True.
Proof. exact (@lem1386659 term26). Qed.
Lemma lem1386661 (x : real) (y : real) (h1 : term25 x y) : ((real_add x y) = term26) = True.
Proof. exact (TRANS (@lem1386656 x y h1) (@lem1386660)). Qed.
Lemma lem1386662 (x : real) (y : real) : term37 x y.
Proof. exact (fun h0 : term25 x y => @lem1386661 x y h0). Qed.
Lemma lem1386663 (x : real) (y : real) : term38 x y.
Proof. exact (@lem1386636 x y True). Qed.
Lemma lem1386664 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (@lem1386663 x y (@lem1386662 x y)). Qed.
Lemma lem1386666 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1386667 (x : real) (y : real) : (term40 x y) = True.
Proof. exact (@lem1386666 (term25 x y)). Qed.
Lemma lem1386668 (x : real) (y : real) : (term39 x y) = True.
Proof. exact (TRANS (@lem1386664 x y) (@lem1386667 x y)). Qed.
Lemma lem1386669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386670 (x : real) (y : real) : (term41 x y) = (and True).
Proof. exact (MK_COMB (@lem1386669) (@lem1386668 x y)). Qed.
Lemma lem1386676 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386677 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386676 p q p' q'). Qed.
Lemma lem1386678 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386677 p q p'). Qed.
Lemma lem1386679 (x : real) (y : real) : term42 x y.
Proof. exact (@lem1386678 (term43 x y) (term44 x y)). Qed.
Lemma lem1386680 (x : real) (y : real) (p' : Prop) : term45 x y p'.
Proof. exact (@lem1386679 x y p'). Qed.
Lemma lem1386681 (x : real) (y : real) (p' : Prop) : (term45 x y p') = (term46 x y p').
Proof. exact (eq_refl (term45 x y p')). Qed.
Lemma lem1386682 (x : real) (y : real) (p' : Prop) : term46 x y p'.
Proof. exact (EQ_MP (@lem1386681 x y p') (@lem1386680 x y p')). Qed.
Lemma lem1386683 (x : real) (y : real) (p' : Prop) (q' : Prop) : term47 x y p' q'.
Proof. exact (@lem1386682 x y p' q'). Qed.
Lemma lem1386684 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term47 x y p' q') = (term48 x y p' q').
Proof. exact (eq_refl (term47 x y p' q')). Qed.
Lemma lem1386685 (x : real) (y : real) (p' : Prop) (q' : Prop) : term48 x y p' q'.
Proof. exact (EQ_MP (@lem1386684 x y p' q') (@lem1386683 x y p' q')). Qed.
Lemma lem1386691 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386692 (y : real) : (term49 y) = (term50 y).
Proof. exact (@lem1386691 term26 y). Qed.
Lemma lem1386693 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1386694 (x : real) (y : real) : (term43 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1386693 x) (@lem1386692 y)). Qed.
Lemma lem1386699 (x : real) (y : real) (q' : Prop) : term53 x y q'.
Proof. exact (@lem1386685 x y (term52 x y) q'). Qed.
Lemma lem1386700 (x : real) (y : real) (q' : Prop) : term54 x y q'.
Proof. exact (@lem1386699 x y q' (@lem1386694 x y)). Qed.
Lemma lem1386701 (x : real) (y : real) (h1 : term52 x y) : term52 x y.
Proof. exact (h1). Qed.
Lemma lem1386702 (x : real) (y : real) (h1 : term52 x y) : term50 y.
Proof. exact (proj2 (@lem1386701 x y h1)). Qed.
Lemma lem1386703 (y : real) : (term50 y) = ((term50 y) = True).
Proof. exact (@lem7 (term50 y)). Qed.
Lemma lem1386707 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386708 (x : real) (y : real) : (term44 x y) = (term55 x y).
Proof. exact (@lem1386707 term26 (real_add x y)). Qed.
Lemma lem1386710 (x : real) (y : real) (h1 : term52 x y) : x = term26.
Proof. exact (proj1 (@lem1386701 x y h1)). Qed.
Lemma lem1386711 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1386712 (x : real) (y : real) (h1 : term52 x y) : (real_add x) = term33.
Proof. exact (MK_COMB (@lem1386711) (@lem1386710 x y h1)). Qed.
Lemma lem1386713 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1386714 (x : real) (y : real) (h1 : term52 x y) : (real_add x y) = (term20 y).
Proof. exact (MK_COMB (@lem1386712 x y h1) (@lem1386713 y)). Qed.
Lemma lem1386716 (x : real) : (term20 x) = x.
Proof. exact (EQ_MP (@lem1386611 x) (@lem1386610 x)). Qed.
Lemma lem1386717 (y : real) : (term20 y) = y.
Proof. exact (@lem1386716 y). Qed.
Lemma lem1386718 (x : real) (y : real) (h1 : term52 x y) : (real_add x y) = y.
Proof. exact (TRANS (@lem1386714 x y h1) (@lem1386717 y)). Qed.
Lemma lem1386719 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem1386720 (x : real) (y : real) (h1 : term52 x y) : (term55 x y) = (term50 y).
Proof. exact (MK_COMB (@lem1386719) (@lem1386718 x y h1)). Qed.
Lemma lem1386722 (x : real) (y : real) (h1 : term52 x y) : (term50 y) = True.
Proof. exact (EQ_MP (@lem1386703 y) (@lem1386702 x y h1)). Qed.
Lemma lem1386723 (x : real) (y : real) (h1 : term52 x y) : (term55 x y) = True.
Proof. exact (TRANS (@lem1386720 x y h1) (@lem1386722 x y h1)). Qed.
Lemma lem1386724 (x : real) (y : real) (h1 : term52 x y) : (term44 x y) = True.
Proof. exact (TRANS (@lem1386708 x y) (@lem1386723 x y h1)). Qed.
Lemma lem1386725 (x : real) (y : real) : term57 x y.
Proof. exact (fun h0 : term52 x y => @lem1386724 x y h0). Qed.
Lemma lem1386726 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1386700 x y True). Qed.
Lemma lem1386727 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (@lem1386726 x y (@lem1386725 x y)). Qed.
Lemma lem1386729 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1386730 (x : real) (y : real) : (term60 x y) = True.
Proof. exact (@lem1386729 (term52 x y)). Qed.
Lemma lem1386731 (x : real) (y : real) : (term59 x y) = True.
Proof. exact (TRANS (@lem1386727 x y) (@lem1386730 x y)). Qed.
Lemma lem1386732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386733 (x : real) (y : real) : (term61 x y) = (and True).
Proof. exact (MK_COMB (@lem1386732) (@lem1386731 x y)). Qed.
Lemma lem1386739 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386740 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386739 p q p' q'). Qed.
Lemma lem1386741 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386740 p q p'). Qed.
Lemma lem1386742 (x : real) (y : real) : term62 x y.
Proof. exact (@lem1386741 (term63 x y) (term64 x y)). Qed.
Lemma lem1386743 (x : real) (y : real) (p' : Prop) : term65 x y p'.
Proof. exact (@lem1386742 x y p'). Qed.
Lemma lem1386744 (x : real) (y : real) (p' : Prop) : (term65 x y p') = (term66 x y p').
Proof. exact (eq_refl (term65 x y p')). Qed.
Lemma lem1386745 (x : real) (y : real) (p' : Prop) : term66 x y p'.
Proof. exact (EQ_MP (@lem1386744 x y p') (@lem1386743 x y p')). Qed.
Lemma lem1386746 (x : real) (y : real) (p' : Prop) (q' : Prop) : term67 x y p' q'.
Proof. exact (@lem1386745 x y p' q'). Qed.
Lemma lem1386747 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term67 x y p' q') = (term68 x y p' q').
Proof. exact (eq_refl (term67 x y p' q')). Qed.
Lemma lem1386748 (x : real) (y : real) (p' : Prop) (q' : Prop) : term68 x y p' q'.
Proof. exact (EQ_MP (@lem1386747 x y p' q') (@lem1386746 x y p' q')). Qed.
Lemma lem1386754 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1386755 (y : real) : (term69 y) = (term70 y).
Proof. exact (@lem1386754 term26 y). Qed.
Lemma lem1386756 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1386757 (x : real) (y : real) : (term63 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1386756 x) (@lem1386755 y)). Qed.
Lemma lem1386762 (x : real) (y : real) (q' : Prop) : term72 x y q'.
Proof. exact (@lem1386748 x y (term71 x y) q'). Qed.
Lemma lem1386763 (x : real) (y : real) (q' : Prop) : term73 x y q'.
Proof. exact (@lem1386762 x y q' (@lem1386757 x y)). Qed.
Lemma lem1386764 (x : real) (y : real) (h1 : term71 x y) : term71 x y.
Proof. exact (h1). Qed.
Lemma lem1386765 (x : real) (y : real) (h1 : term71 x y) : term70 y.
Proof. exact (proj2 (@lem1386764 x y h1)). Qed.
Lemma lem1386766 (y : real) : (term70 y) = ((term70 y) = True).
Proof. exact (@lem7 (term70 y)). Qed.
Lemma lem1386770 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1386771 (x : real) (y : real) : (term64 x y) = (term74 x y).
Proof. exact (@lem1386770 term26 (real_add x y)). Qed.
Lemma lem1386773 (x : real) (y : real) (h1 : term71 x y) : x = term26.
Proof. exact (proj1 (@lem1386764 x y h1)). Qed.
Lemma lem1386774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1386775 (x : real) (y : real) (h1 : term71 x y) : (real_add x) = term33.
Proof. exact (MK_COMB (@lem1386774) (@lem1386773 x y h1)). Qed.
Lemma lem1386776 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1386777 (x : real) (y : real) (h1 : term71 x y) : (real_add x y) = (term20 y).
Proof. exact (MK_COMB (@lem1386775 x y h1) (@lem1386776 y)). Qed.
Lemma lem1386779 (x : real) : (term20 x) = x.
Proof. exact (EQ_MP (@lem1386611 x) (@lem1386610 x)). Qed.
Lemma lem1386780 (y : real) : (term20 y) = y.
Proof. exact (@lem1386779 y). Qed.
Lemma lem1386781 (x : real) (y : real) (h1 : term71 x y) : (real_add x y) = y.
Proof. exact (TRANS (@lem1386777 x y h1) (@lem1386780 y)). Qed.
Lemma lem1386782 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1386783 (x : real) (y : real) (h1 : term71 x y) : (term74 x y) = (term70 y).
Proof. exact (MK_COMB (@lem1386782) (@lem1386781 x y h1)). Qed.
Lemma lem1386785 (x : real) (y : real) (h1 : term71 x y) : (term70 y) = True.
Proof. exact (EQ_MP (@lem1386766 y) (@lem1386765 x y h1)). Qed.
Lemma lem1386786 (x : real) (y : real) (h1 : term71 x y) : (term74 x y) = True.
Proof. exact (TRANS (@lem1386783 x y h1) (@lem1386785 x y h1)). Qed.
Lemma lem1386787 (x : real) (y : real) (h1 : term71 x y) : (term64 x y) = True.
Proof. exact (TRANS (@lem1386771 x y) (@lem1386786 x y h1)). Qed.
Lemma lem1386788 (x : real) (y : real) : term76 x y.
Proof. exact (fun h0 : term71 x y => @lem1386787 x y h0). Qed.
Lemma lem1386789 (x : real) (y : real) : term77 x y.
Proof. exact (@lem1386763 x y True). Qed.
Lemma lem1386790 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (@lem1386789 x y (@lem1386788 x y)). Qed.
Lemma lem1386792 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1386793 (x : real) (y : real) : (term79 x y) = True.
Proof. exact (@lem1386792 (term71 x y)). Qed.
Lemma lem1386794 (x : real) (y : real) : (term78 x y) = True.
Proof. exact (TRANS (@lem1386790 x y) (@lem1386793 x y)). Qed.
Lemma lem1386795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386796 (x : real) (y : real) : (term80 x y) = (and True).
Proof. exact (MK_COMB (@lem1386795) (@lem1386794 x y)). Qed.
Lemma lem1386802 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386803 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386802 p q p' q'). Qed.
Lemma lem1386804 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386803 p q p'). Qed.
Lemma lem1386805 (x : real) (y : real) : term81 x y.
Proof. exact (@lem1386804 (term82 x y) (term44 x y)). Qed.
Lemma lem1386806 (x : real) (y : real) (p' : Prop) : term83 x y p'.
Proof. exact (@lem1386805 x y p'). Qed.
Lemma lem1386807 (x : real) (y : real) (p' : Prop) : (term83 x y p') = (term84 x y p').
Proof. exact (eq_refl (term83 x y p')). Qed.
Lemma lem1386808 (x : real) (y : real) (p' : Prop) : term84 x y p'.
Proof. exact (EQ_MP (@lem1386807 x y p') (@lem1386806 x y p')). Qed.
Lemma lem1386809 (x : real) (y : real) (p' : Prop) (q' : Prop) : term85 x y p' q'.
Proof. exact (@lem1386808 x y p' q'). Qed.
Lemma lem1386810 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term85 x y p' q') = (term86 x y p' q').
Proof. exact (eq_refl (term85 x y p' q')). Qed.
Lemma lem1386811 (x : real) (y : real) (p' : Prop) (q' : Prop) : term86 x y p' q'.
Proof. exact (EQ_MP (@lem1386810 x y p' q') (@lem1386809 x y p' q')). Qed.
Lemma lem1386815 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386816 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1386815 term26 x). Qed.
Lemma lem1386817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386818 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1386817) (@lem1386816 x)). Qed.
Lemma lem1386821 (y : real) : (y = term26) = (y = term26).
Proof. exact (eq_refl (y = term26)). Qed.
Lemma lem1386822 (x : real) (y : real) : (term82 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1386818 x) (@lem1386821 y)). Qed.
Lemma lem1386827 (x : real) (y : real) (q' : Prop) : term90 x y q'.
Proof. exact (@lem1386811 x y (term89 x y) q'). Qed.
Lemma lem1386828 (x : real) (y : real) (q' : Prop) : term91 x y q'.
Proof. exact (@lem1386827 x y q' (@lem1386822 x y)). Qed.
Lemma lem1386829 (x : real) (y : real) (h1 : term89 x y) : term89 x y.
Proof. exact (h1). Qed.
Lemma lem1386831 (x : real) (y : real) (h1 : term89 x y) : term50 x.
Proof. exact (proj1 (@lem1386829 x y h1)). Qed.
Lemma lem1386832 (x : real) : (term50 x) = ((term50 x) = True).
Proof. exact (@lem7 (term50 x)). Qed.
Lemma lem1386835 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386836 (x : real) (y : real) : (term44 x y) = (term55 x y).
Proof. exact (@lem1386835 term26 (real_add x y)). Qed.
Lemma lem1386838 (x : real) (y : real) (h1 : term89 x y) : y = term26.
Proof. exact (proj2 (@lem1386829 x y h1)). Qed.
Lemma lem1386839 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1386840 (x : real) (y : real) (h1 : term89 x y) : (real_add x y) = (term18 x).
Proof. exact (MK_COMB (@lem1386839 x) (@lem1386838 x y h1)). Qed.
Lemma lem1386842 (x : real) : (term18 x) = x.
Proof. exact (EQ_MP (@lem1386608 x) (@lem1386607 x)). Qed.
Lemma lem1386843 (x : real) (y : real) (h1 : term89 x y) : (real_add x y) = x.
Proof. exact (TRANS (@lem1386840 x y h1) (@lem1386842 x)). Qed.
Lemma lem1386844 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem1386845 (x : real) (y : real) (h1 : term89 x y) : (term55 x y) = (term50 x).
Proof. exact (MK_COMB (@lem1386844) (@lem1386843 x y h1)). Qed.
Lemma lem1386847 (x : real) (y : real) (h1 : term89 x y) : (term50 x) = True.
Proof. exact (EQ_MP (@lem1386832 x) (@lem1386831 x y h1)). Qed.
Lemma lem1386848 (x : real) (y : real) (h1 : term89 x y) : (term55 x y) = True.
Proof. exact (TRANS (@lem1386845 x y h1) (@lem1386847 x y h1)). Qed.
Lemma lem1386849 (x : real) (y : real) (h1 : term89 x y) : (term44 x y) = True.
Proof. exact (TRANS (@lem1386836 x y) (@lem1386848 x y h1)). Qed.
Lemma lem1386850 (x : real) (y : real) : term92 x y.
Proof. exact (fun h0 : term89 x y => @lem1386849 x y h0). Qed.
Lemma lem1386851 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1386828 x y True). Qed.
Lemma lem1386852 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (@lem1386851 x y (@lem1386850 x y)). Qed.
Lemma lem1386854 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1386855 (x : real) (y : real) : (term95 x y) = True.
Proof. exact (@lem1386854 (term89 x y)). Qed.
Lemma lem1386856 (x : real) (y : real) : (term94 x y) = True.
Proof. exact (TRANS (@lem1386852 x y) (@lem1386855 x y)). Qed.
Lemma lem1386857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386858 (x : real) (y : real) : (term96 x y) = (and True).
Proof. exact (MK_COMB (@lem1386857) (@lem1386856 x y)). Qed.
Lemma lem1386864 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386865 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386864 p q p' q'). Qed.
Lemma lem1386866 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386865 p q p'). Qed.
Lemma lem1386867 (x : real) (y : real) : term97 x y.
Proof. exact (@lem1386866 (term98 x y) (term44 x y)). Qed.
Lemma lem1386868 (x : real) (y : real) (p' : Prop) : term99 x y p'.
Proof. exact (@lem1386867 x y p'). Qed.
Lemma lem1386869 (x : real) (y : real) (p' : Prop) : (term99 x y p') = (term100 x y p').
Proof. exact (eq_refl (term99 x y p')). Qed.
Lemma lem1386870 (x : real) (y : real) (p' : Prop) : term100 x y p'.
Proof. exact (EQ_MP (@lem1386869 x y p') (@lem1386868 x y p')). Qed.
Lemma lem1386871 (x : real) (y : real) (p' : Prop) (q' : Prop) : term101 x y p' q'.
Proof. exact (@lem1386870 x y p' q'). Qed.
Lemma lem1386872 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term101 x y p' q') = (term102 x y p' q').
Proof. exact (eq_refl (term101 x y p' q')). Qed.
Lemma lem1386873 (x : real) (y : real) (p' : Prop) (q' : Prop) : term102 x y p' q'.
Proof. exact (EQ_MP (@lem1386872 x y p' q') (@lem1386871 x y p' q')). Qed.
Lemma lem1386877 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386878 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1386877 term26 x). Qed.
Lemma lem1386879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386880 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1386879) (@lem1386878 x)). Qed.
Lemma lem1386882 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386883 (y : real) : (term49 y) = (term50 y).
Proof. exact (@lem1386882 term26 y). Qed.
Lemma lem1386884 (x : real) (y : real) : (term98 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1386880 x) (@lem1386883 y)). Qed.
Lemma lem1386887 (x : real) (y : real) (q' : Prop) : term104 x y q'.
Proof. exact (@lem1386873 x y (term103 x y) q'). Qed.
Lemma lem1386888 (x : real) (y : real) (q' : Prop) : term105 x y q'.
Proof. exact (@lem1386887 x y q' (@lem1386884 x y)). Qed.
Lemma lem1386897 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386898 (x : real) (y : real) : (term44 x y) = (term55 x y).
Proof. exact (@lem1386897 term26 (real_add x y)). Qed.
Lemma lem1386899 (x : real) (y : real) : term106 x y.
Proof. exact (fun h0 : term103 x y => @lem1386898 x y). Qed.
Lemma lem1386900 (x : real) (y : real) : term107 x y.
Proof. exact (@lem1386888 x y (term55 x y)). Qed.
Lemma lem1386901 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (@lem1386900 x y (@lem1386899 x y)). Qed.
Lemma lem1386933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386934 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1386933) (@lem1386901 x y)). Qed.
Lemma lem1386971 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1386972 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1386971 p q p' q'). Qed.
Lemma lem1386973 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1386972 p q p'). Qed.
Lemma lem1386974 (x : real) (y : real) : term112 x y.
Proof. exact (@lem1386973 (term113 x y) (term64 x y)). Qed.
Lemma lem1386975 (x : real) (y : real) (p' : Prop) : term114 x y p'.
Proof. exact (@lem1386974 x y p'). Qed.
Lemma lem1386976 (x : real) (y : real) (p' : Prop) : (term114 x y p') = (term115 x y p').
Proof. exact (eq_refl (term114 x y p')). Qed.
Lemma lem1386977 (x : real) (y : real) (p' : Prop) : term115 x y p'.
Proof. exact (EQ_MP (@lem1386976 x y p') (@lem1386975 x y p')). Qed.
Lemma lem1386978 (x : real) (y : real) (p' : Prop) (q' : Prop) : term116 x y p' q'.
Proof. exact (@lem1386977 x y p' q'). Qed.
Lemma lem1386979 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term116 x y p' q') = (term117 x y p' q').
Proof. exact (eq_refl (term116 x y p' q')). Qed.
Lemma lem1386980 (x : real) (y : real) (p' : Prop) (q' : Prop) : term117 x y p' q'.
Proof. exact (EQ_MP (@lem1386979 x y p' q') (@lem1386978 x y p' q')). Qed.
Lemma lem1386984 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1386985 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1386984 term26 x). Qed.
Lemma lem1386986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1386987 (x : real) : (term87 x) = (term88 x).
Proof. exact (MK_COMB (@lem1386986) (@lem1386985 x)). Qed.
Lemma lem1386989 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1386990 (y : real) : (term69 y) = (term70 y).
Proof. exact (@lem1386989 term26 y). Qed.
Lemma lem1386991 (x : real) (y : real) : (term113 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1386987 x) (@lem1386990 y)). Qed.
Lemma lem1386994 (x : real) (y : real) (q' : Prop) : term119 x y q'.
Proof. exact (@lem1386980 x y (term118 x y) q'). Qed.
Lemma lem1386995 (x : real) (y : real) (q' : Prop) : term120 x y q'.
Proof. exact (@lem1386994 x y q' (@lem1386991 x y)). Qed.
Lemma lem1387004 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387005 (x : real) (y : real) : (term64 x y) = (term74 x y).
Proof. exact (@lem1387004 term26 (real_add x y)). Qed.
Lemma lem1387006 (x : real) (y : real) : term121 x y.
Proof. exact (fun h0 : term118 x y => @lem1387005 x y). Qed.
Lemma lem1387007 (x : real) (y : real) : term122 x y.
Proof. exact (@lem1386995 x y (term74 x y)). Qed.
Lemma lem1387008 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (@lem1387007 x y (@lem1387006 x y)). Qed.
Lemma lem1387040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387041 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1387040) (@lem1387008 x y)). Qed.
Lemma lem1387078 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1387079 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1387078 p q p' q'). Qed.
Lemma lem1387080 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1387079 p q p'). Qed.
Lemma lem1387081 (x : real) (y : real) : term127 x y.
Proof. exact (@lem1387080 (term128 x y) (term64 x y)). Qed.
Lemma lem1387082 (x : real) (y : real) (p' : Prop) : term129 x y p'.
Proof. exact (@lem1387081 x y p'). Qed.
Lemma lem1387083 (x : real) (y : real) (p' : Prop) : (term129 x y p') = (term130 x y p').
Proof. exact (eq_refl (term129 x y p')). Qed.
Lemma lem1387084 (x : real) (y : real) (p' : Prop) : term130 x y p'.
Proof. exact (EQ_MP (@lem1387083 x y p') (@lem1387082 x y p')). Qed.
Lemma lem1387085 (x : real) (y : real) (p' : Prop) (q' : Prop) : term131 x y p' q'.
Proof. exact (@lem1387084 x y p' q'). Qed.
Lemma lem1387086 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term131 x y p' q') = (term132 x y p' q').
Proof. exact (eq_refl (term131 x y p' q')). Qed.
Lemma lem1387087 (x : real) (y : real) (p' : Prop) (q' : Prop) : term132 x y p' q'.
Proof. exact (EQ_MP (@lem1387086 x y p' q') (@lem1387085 x y p' q')). Qed.
Lemma lem1387091 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387092 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1387091 term26 x). Qed.
Lemma lem1387093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387094 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1387093) (@lem1387092 x)). Qed.
Lemma lem1387097 (y : real) : (y = term26) = (y = term26).
Proof. exact (eq_refl (y = term26)). Qed.
Lemma lem1387098 (x : real) (y : real) : (term128 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1387094 x) (@lem1387097 y)). Qed.
Lemma lem1387103 (x : real) (y : real) (q' : Prop) : term136 x y q'.
Proof. exact (@lem1387087 x y (term135 x y) q'). Qed.
Lemma lem1387104 (x : real) (y : real) (q' : Prop) : term137 x y q'.
Proof. exact (@lem1387103 x y q' (@lem1387098 x y)). Qed.
Lemma lem1387105 (x : real) (y : real) (h1 : term135 x y) : term135 x y.
Proof. exact (h1). Qed.
Lemma lem1387107 (x : real) (y : real) (h1 : term135 x y) : term70 x.
Proof. exact (proj1 (@lem1387105 x y h1)). Qed.
Lemma lem1387108 (x : real) : (term70 x) = ((term70 x) = True).
Proof. exact (@lem7 (term70 x)). Qed.
Lemma lem1387111 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387112 (x : real) (y : real) : (term64 x y) = (term74 x y).
Proof. exact (@lem1387111 term26 (real_add x y)). Qed.
Lemma lem1387114 (x : real) (y : real) (h1 : term135 x y) : y = term26.
Proof. exact (proj2 (@lem1387105 x y h1)). Qed.
Lemma lem1387115 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1387116 (x : real) (y : real) (h1 : term135 x y) : (real_add x y) = (term18 x).
Proof. exact (MK_COMB (@lem1387115 x) (@lem1387114 x y h1)). Qed.
Lemma lem1387118 (x : real) : (term18 x) = x.
Proof. exact (EQ_MP (@lem1386608 x) (@lem1386607 x)). Qed.
Lemma lem1387119 (x : real) (y : real) (h1 : term135 x y) : (real_add x y) = x.
Proof. exact (TRANS (@lem1387116 x y h1) (@lem1387118 x)). Qed.
Lemma lem1387120 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1387121 (x : real) (y : real) (h1 : term135 x y) : (term74 x y) = (term70 x).
Proof. exact (MK_COMB (@lem1387120) (@lem1387119 x y h1)). Qed.
Lemma lem1387123 (x : real) (y : real) (h1 : term135 x y) : (term70 x) = True.
Proof. exact (EQ_MP (@lem1387108 x) (@lem1387107 x y h1)). Qed.
Lemma lem1387124 (x : real) (y : real) (h1 : term135 x y) : (term74 x y) = True.
Proof. exact (TRANS (@lem1387121 x y h1) (@lem1387123 x y h1)). Qed.
Lemma lem1387125 (x : real) (y : real) (h1 : term135 x y) : (term64 x y) = True.
Proof. exact (TRANS (@lem1387112 x y) (@lem1387124 x y h1)). Qed.
Lemma lem1387126 (x : real) (y : real) : term138 x y.
Proof. exact (fun h0 : term135 x y => @lem1387125 x y h0). Qed.
Lemma lem1387127 (x : real) (y : real) : term139 x y.
Proof. exact (@lem1387104 x y True). Qed.
Lemma lem1387128 (x : real) (y : real) : (term140 x y) = (term141 x y).
Proof. exact (@lem1387127 x y (@lem1387126 x y)). Qed.
Lemma lem1387130 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1387131 (x : real) (y : real) : (term141 x y) = True.
Proof. exact (@lem1387130 (term135 x y)). Qed.
Lemma lem1387132 (x : real) (y : real) : (term140 x y) = True.
Proof. exact (TRANS (@lem1387128 x y) (@lem1387131 x y)). Qed.
Lemma lem1387133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387134 (x : real) (y : real) : (term142 x y) = (and True).
Proof. exact (MK_COMB (@lem1387133) (@lem1387132 x y)). Qed.
Lemma lem1387140 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1387141 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1387140 p q p' q'). Qed.
Lemma lem1387142 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1387141 p q p'). Qed.
Lemma lem1387143 (x : real) (y : real) : term143 x y.
Proof. exact (@lem1387142 (term144 x y) (term64 x y)). Qed.
Lemma lem1387144 (x : real) (y : real) (p' : Prop) : term145 x y p'.
Proof. exact (@lem1387143 x y p'). Qed.
Lemma lem1387145 (x : real) (y : real) (p' : Prop) : (term145 x y p') = (term146 x y p').
Proof. exact (eq_refl (term145 x y p')). Qed.
Lemma lem1387146 (x : real) (y : real) (p' : Prop) : term146 x y p'.
Proof. exact (EQ_MP (@lem1387145 x y p') (@lem1387144 x y p')). Qed.
Lemma lem1387147 (x : real) (y : real) (p' : Prop) (q' : Prop) : term147 x y p' q'.
Proof. exact (@lem1387146 x y p' q'). Qed.
Lemma lem1387148 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term147 x y p' q') = (term148 x y p' q').
Proof. exact (eq_refl (term147 x y p' q')). Qed.
Lemma lem1387149 (x : real) (y : real) (p' : Prop) (q' : Prop) : term148 x y p' q'.
Proof. exact (EQ_MP (@lem1387148 x y p' q') (@lem1387147 x y p' q')). Qed.
Lemma lem1387153 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387154 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1387153 term26 x). Qed.
Lemma lem1387155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387156 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1387155) (@lem1387154 x)). Qed.
Lemma lem1387158 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1386605 y x) (@lem1386604 y x)). Qed.
Lemma lem1387159 (y : real) : (term49 y) = (term50 y).
Proof. exact (@lem1387158 term26 y). Qed.
Lemma lem1387160 (x : real) (y : real) : (term144 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1387156 x) (@lem1387159 y)). Qed.
Lemma lem1387163 (x : real) (y : real) (q' : Prop) : term150 x y q'.
Proof. exact (@lem1387149 x y (term149 x y) q'). Qed.
Lemma lem1387164 (x : real) (y : real) (q' : Prop) : term151 x y q'.
Proof. exact (@lem1387163 x y q' (@lem1387160 x y)). Qed.
Lemma lem1387173 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387174 (x : real) (y : real) : (term64 x y) = (term74 x y).
Proof. exact (@lem1387173 term26 (real_add x y)). Qed.
Lemma lem1387175 (x : real) (y : real) : term152 x y.
Proof. exact (fun h0 : term149 x y => @lem1387174 x y). Qed.
Lemma lem1387176 (x : real) (y : real) : term153 x y.
Proof. exact (@lem1387164 x y (term74 x y)). Qed.
Lemma lem1387177 (x : real) (y : real) : (term154 x y) = (term155 x y).
Proof. exact (@lem1387176 x y (@lem1387175 x y)). Qed.
Lemma lem1387209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387210 (x : real) (y : real) : (term156 x y) = (term157 x y).
Proof. exact (MK_COMB (@lem1387209) (@lem1387177 x y)). Qed.
Lemma lem1387245 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1387246 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1387245 p q p' q'). Qed.
Lemma lem1387247 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1387246 p q p'). Qed.
Lemma lem1387248 (x : real) (y : real) : term158 x y.
Proof. exact (@lem1387247 (term159 x y) (term64 x y)). Qed.
Lemma lem1387249 (x : real) (y : real) (p' : Prop) : term160 x y p'.
Proof. exact (@lem1387248 x y p'). Qed.
Lemma lem1387250 (x : real) (y : real) (p' : Prop) : (term160 x y p') = (term161 x y p').
Proof. exact (eq_refl (term160 x y p')). Qed.
Lemma lem1387251 (x : real) (y : real) (p' : Prop) : term161 x y p'.
Proof. exact (EQ_MP (@lem1387250 x y p') (@lem1387249 x y p')). Qed.
Lemma lem1387252 (x : real) (y : real) (p' : Prop) (q' : Prop) : term162 x y p' q'.
Proof. exact (@lem1387251 x y p' q'). Qed.
Lemma lem1387253 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term162 x y p' q') = (term163 x y p' q').
Proof. exact (eq_refl (term162 x y p' q')). Qed.
Lemma lem1387254 (x : real) (y : real) (p' : Prop) (q' : Prop) : term163 x y p' q'.
Proof. exact (EQ_MP (@lem1387253 x y p' q') (@lem1387252 x y p' q')). Qed.
Lemma lem1387258 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387259 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1387258 term26 x). Qed.
Lemma lem1387260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1387261 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1387260) (@lem1387259 x)). Qed.
Lemma lem1387263 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387264 (y : real) : (term69 y) = (term70 y).
Proof. exact (@lem1387263 term26 y). Qed.
Lemma lem1387265 (x : real) (y : real) : (term159 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1387261 x) (@lem1387264 y)). Qed.
Lemma lem1387268 (x : real) (y : real) (q' : Prop) : term165 x y q'.
Proof. exact (@lem1387254 x y (term164 x y) q'). Qed.
Lemma lem1387269 (x : real) (y : real) (q' : Prop) : term166 x y q'.
Proof. exact (@lem1387268 x y q' (@lem1387265 x y)). Qed.
Lemma lem1387278 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1386599 y x) (@lem1386598 y x)). Qed.
Lemma lem1387279 (x : real) (y : real) : (term64 x y) = (term74 x y).
Proof. exact (@lem1387278 term26 (real_add x y)). Qed.
Lemma lem1387280 (x : real) (y : real) : term167 x y.
Proof. exact (fun h0 : term164 x y => @lem1387279 x y). Qed.
Lemma lem1387281 (x : real) (y : real) : term168 x y.
Proof. exact (@lem1387269 x y (term74 x y)). Qed.
Lemma lem1387282 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (@lem1387281 x y (@lem1387280 x y)). Qed.
Lemma lem1387314 (x : real) (y : real) : (term171 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1387210 x y) (@lem1387282 x y)). Qed.
Lemma lem1387379 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1387134 x y) (@lem1387314 x y)). Qed.
Lemma lem1387381 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1387382 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem1387381 (term172 x y)). Qed.
Lemma lem1387447 (x : real) (y : real) : (term173 x y) = (term172 x y).
Proof. exact (TRANS (@lem1387379 x y) (@lem1387382 x y)). Qed.
Lemma lem1387448 (x : real) (y : real) : (term175 x y) = (term176 x y).
Proof. exact (MK_COMB (@lem1387041 x y) (@lem1387447 x y)). Qed.
Lemma lem1387546 (x : real) (y : real) : (term177 x y) = (term178 x y).
Proof. exact (MK_COMB (@lem1386934 x y) (@lem1387448 x y)). Qed.
Lemma lem1387677 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1386858 x y) (@lem1387546 x y)). Qed.
Lemma lem1387679 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1387680 (x : real) (y : real) : (term180 x y) = (term178 x y).
Proof. exact (@lem1387679 (term178 x y)). Qed.
Lemma lem1387811 (x : real) (y : real) : (term179 x y) = (term178 x y).
Proof. exact (TRANS (@lem1387677 x y) (@lem1387680 x y)). Qed.
Lemma lem1387812 (x : real) (y : real) : (term181 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1386796 x y) (@lem1387811 x y)). Qed.
Lemma lem1387814 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1387815 (x : real) (y : real) : (term180 x y) = (term178 x y).
Proof. exact (@lem1387814 (term178 x y)). Qed.
Lemma lem1387946 (x : real) (y : real) : (term181 x y) = (term178 x y).
Proof. exact (TRANS (@lem1387812 x y) (@lem1387815 x y)). Qed.
Lemma lem1387947 (x : real) (y : real) : (term182 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1386733 x y) (@lem1387946 x y)). Qed.
Lemma lem1387949 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1387950 (x : real) (y : real) : (term180 x y) = (term178 x y).
Proof. exact (@lem1387949 (term178 x y)). Qed.
Lemma lem1388081 (x : real) (y : real) : (term182 x y) = (term178 x y).
Proof. exact (TRANS (@lem1387947 x y) (@lem1387950 x y)). Qed.
Lemma lem1388082 (x : real) (y : real) : (term183 x y) = (term180 x y).
Proof. exact (MK_COMB (@lem1386670 x y) (@lem1388081 x y)). Qed.
Lemma lem1388084 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1388085 (x : real) (y : real) : (term180 x y) = (term178 x y).
Proof. exact (@lem1388084 (term178 x y)). Qed.
Lemma lem1388216 (x : real) (y : real) : (term183 x y) = (term178 x y).
Proof. exact (TRANS (@lem1388082 x y) (@lem1388085 x y)). Qed.
Lemma lem1388217 (x : real) (y : real) : (term178 x y) = (term183 x y).
Proof. exact (SYM (@lem1388216 x y)). Qed.
Lemma lem1388225 (x : real) (y : real) : (real_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1386593 x y) (@lem1386592 x y)). Qed.
Lemma lem1388226 (x : real) : (term50 x) = (term184 x).
Proof. exact (@lem1388225 term26 x). Qed.
Lemma lem1388231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1388232 (x : real) : (term88 x) = (term185 x).
Proof. exact (MK_COMB (@lem1388231) (@lem1388226 x)). Qed.
Lemma lem1388234 (x : real) (y : real) : (real_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1386593 x y) (@lem1386592 x y)). Qed.
Lemma lem1388235 (y : real) : (term50 y) = (term184 y).
Proof. exact (@lem1388234 term26 y). Qed.
Lemma lem1388240 (x : real) (y : real) : (term103 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1388232 x) (@lem1388235 y)). Qed.
Lemma lem1388243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1388244 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1388243) (@lem1388240 x y)). Qed.
Lemma lem1388246 (x : real) (y : real) : (real_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1386593 x y) (@lem1386592 x y)). Qed.
Lemma lem1388247 (x : real) (y : real) : (term55 x y) = (term189 x y).
Proof. exact (@lem1388246 term26 (real_add x y)). Qed.
Lemma lem1388252 (x : real) (y : real) : (term109 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1388244 x y) (@lem1388247 x y)). Qed.
Lemma lem1388255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1388256 (x : real) (y : real) : (term111 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem1388255) (@lem1388252 x y)). Qed.
Lemma lem1388264 (x : real) (y : real) : (real_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1386593 x y) (@lem1386592 x y)). Qed.
Lemma lem1388265 (x : real) : (term50 x) = (term184 x).
Proof. exact (@lem1388264 term26 x). Qed.
Lemma lem1388270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1388271 (x : real) : (term88 x) = (term185 x).
Proof. exact (MK_COMB (@lem1388270) (@lem1388265 x)). Qed.
Lemma lem1388272 (y : real) : (term70 y) = (term70 y).
Proof. exact (eq_refl (term70 y)). Qed.
Lemma lem1388273 (x : real) (y : real) : (term118 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1388271 x) (@lem1388272 y)). Qed.
Lemma lem1388276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1388277 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem1388276) (@lem1388273 x y)). Qed.
Lemma lem1388278 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1388279 (x : real) (y : real) : (term124 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1388277 x y) (@lem1388278 x y)). Qed.
Lemma lem1388282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1388283 (x : real) (y : real) : (term126 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1388282) (@lem1388279 x y)). Qed.
Lemma lem1388291 (x : real) (y : real) : (real_le x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1386593 x y) (@lem1386592 x y)). Qed.
Lemma lem1388292 (y : real) : (term50 y) = (term184 y).
Proof. exact (@lem1388291 term26 y). Qed.
Lemma lem1388297 (x : real) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1388298 (x : real) (y : real) : (term149 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1388297 x) (@lem1388292 y)). Qed.
Lemma lem1388301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1388302 (x : real) (y : real) : (term198 x y) = (term199 x y).
Proof. exact (MK_COMB (@lem1388301) (@lem1388298 x y)). Qed.
Lemma lem1388303 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1388304 (x : real) (y : real) : (term155 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1388302 x y) (@lem1388303 x y)). Qed.
Lemma lem1388307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1388308 (x : real) (y : real) : (term157 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1388307) (@lem1388304 x y)). Qed.
Lemma lem1388313 (x : real) (y : real) : (term170 x y) = (term170 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1388314 (x : real) (y : real) : (term172 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem1388308 x y) (@lem1388313 x y)). Qed.
Lemma lem1388317 (x : real) (y : real) : (term176 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1388283 x y) (@lem1388314 x y)). Qed.
Lemma lem1388320 (x : real) (y : real) : (term178 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1388256 x y) (@lem1388317 x y)). Qed.
Lemma lem1388323 (x : real) (y : real) : (term204 x y) = (term178 x y).
Proof. exact (SYM (@lem1388320 x y)). Qed.
Lemma lem1388325 (p : Prop) : p = (term205 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1388326 (x : real) (y : real) : (term204 x y) = (term206 x y).
Proof. exact (@lem1388325 (term204 x y)). Qed.
Lemma lem1388327 (x : real) (y : real) : (term206 x y) = (term204 x y).
Proof. exact (SYM (@lem1388326 x y)). Qed.
Lemma lem1388328 (x : real) (y : real) (h1 : term207 x y) : term207 x y.
Proof. exact (h1). Qed.
Lemma lem1388331 (x : real) (y : real) (h1 : term208 x y) : term208 x y.
Proof. exact (h1). Qed.
Lemma lem1388332 (x : real) (y : real) : term209 x y.
Proof. exact (fun h0 : term208 x y => @lem1388331 x y h0). Qed.
Lemma lem1388333 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (h1). Qed.
Lemma lem1388334 (x : real) (y : real) (h1 : term208 x y) : term208 x y.
Proof. exact (h1). Qed.
Lemma lem1388335 (x : real) (y : real) (h1 : term208 x y) (h2 : term209 x y) : term208 x y.
Proof. exact (@lem1388333 x y h2 (@lem1388334 x y h1)). Qed.
Lemma lem1388336 (x : real) (y : real) (h1 : term208 x y) : term210 x y.
Proof. exact (fun h0 : term209 x y => @lem1388335 x y h1 h0). Qed.
Lemma lem1388337 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (h1). Qed.
Lemma lem1388338 (x : real) (y : real) (h1 : term208 x y) (h2 : term209 x y) : term208 x y.
Proof. exact (@lem1388336 x y h1 (@lem1388337 x y h2)). Qed.
Lemma lem1388339 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (fun h0 : term208 x y => @lem1388338 x y h0 h1). Qed.
Lemma lem1388340 (x : real) (y : real) : term211 x y.
Proof. exact (fun h0 : term209 x y => @lem1388339 x y h0). Qed.
Lemma lem1388343 (x : real) (y : real) : term209 x y.
Proof. exact (@lem1388340 x y (@lem1388332 x y)). Qed.
Lemma lem1388407 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1388408 : term212 = term213.
Proof. exact (@lem1388407 term214). Qed.
Lemma lem1388413 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem1388414 : term216 = term217.
Proof. exact (MK_COMB (@lem1388413) (@lem1388408)). Qed.
Lemma lem1388417 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem1388418 : term219 = term220.
Proof. exact (MK_COMB (@lem1388417) (@lem1388414)). Qed.
Lemma lem1388421 (x : real) (y : real) : (term221 x y) = (term221 x y).
Proof. exact (eq_refl (term221 x y)). Qed.
Lemma lem1388422 (x : real) (y : real) : (term208 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1388421 x y) (@lem1388418)). Qed.
Lemma lem1388425 (y : real) : (term223 y) = (term224 y).
Proof. exact (fun_ext (fun x : real => @lem1388422 x y)). Qed.
Lemma lem1388426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388427 (y : real) : (term225 y) = (term226 y).
Proof. exact (MK_COMB (@lem1388426) (@lem1388425 y)). Qed.
Lemma lem1388432 : term227 = term228.
Proof. exact (fun_ext (fun y : real => @lem1388427 y)). Qed.
Lemma lem1388433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388442 : term229 = term230.
Proof. exact (MK_COMB (@lem1388433) (@lem1388432)). Qed.
Lemma lem1388443 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1388444 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1388443 x)). Qed.
Lemma lem1388445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388446 : term214 = term214.
Proof. exact (MK_COMB (@lem1388445) (@lem1388444)). Qed.
Lemma lem1388447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1388448 : term213 = term213.
Proof. exact (MK_COMB (@lem1388447) (@lem1388446)). Qed.
Lemma lem1388449 (x : real) : ((term18 x) = x) = ((term18 x) = x).
Proof. exact (eq_refl ((term18 x) = x)). Qed.
Lemma lem1388450 : term232 = term232.
Proof. exact (fun_ext (fun x : real => @lem1388449 x)). Qed.
Lemma lem1388451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388452 : term233 = term233.
Proof. exact (MK_COMB (@lem1388451) (@lem1388450)). Qed.
Lemma lem1388453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1388454 : term215 = term215.
Proof. exact (MK_COMB (@lem1388453) (@lem1388452)). Qed.
Lemma lem1388455 : term217 = term217.
Proof. exact (MK_COMB (@lem1388454) (@lem1388448)). Qed.
Lemma lem1388464 (x : real) (y : real) : (term170 x y) = (term170 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1388465 (x : real) : (term234 x) = (term234 x).
Proof. exact (fun_ext (fun y : real => @lem1388464 x y)). Qed.
Lemma lem1388466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388467 (x : real) : (term235 x) = (term235 x).
Proof. exact (MK_COMB (@lem1388466) (@lem1388465 x)). Qed.
Lemma lem1388468 : term236 = term236.
Proof. exact (fun_ext (fun x : real => @lem1388467 x)). Qed.
Lemma lem1388469 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388470 : term237 = term237.
Proof. exact (MK_COMB (@lem1388469) (@lem1388468)). Qed.
Lemma lem1388471 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1388472 : term218 = term218.
Proof. exact (MK_COMB (@lem1388471) (@lem1388470)). Qed.
Lemma lem1388473 : term220 = term220.
Proof. exact (MK_COMB (@lem1388472) (@lem1388455)). Qed.
Lemma lem1388542 (x : real) (y : real) : (term221 x y) = (term221 x y).
Proof. exact (eq_refl (term221 x y)). Qed.
Lemma lem1388543 (x : real) (y : real) : (term222 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1388542 x y) (@lem1388473)). Qed.
Lemma lem1388544 (y : real) : (term224 y) = (term224 y).
Proof. exact (fun_ext (fun x : real => @lem1388543 x y)). Qed.
Lemma lem1388545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388546 (y : real) : (term226 y) = (term226 y).
Proof. exact (MK_COMB (@lem1388545) (@lem1388544 y)). Qed.
Lemma lem1388547 : term228 = term228.
Proof. exact (fun_ext (fun y : real => @lem1388546 y)). Qed.
Lemma lem1388548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388549 : term230 = term230.
Proof. exact (MK_COMB (@lem1388548) (@lem1388547)). Qed.
Lemma lem1388630 : term229 = term230.
Proof. exact (TRANS (@lem1388442) (@lem1388549)). Qed.
Lemma lem1388631 : term230 = term229.
Proof. exact (SYM (@lem1388630)). Qed.
Lemma lem1388632 (x : real) (y : real) (h1 : term207 x y) : term207 x y.
Proof. exact (h1). Qed.
Lemma lem1388633 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem1388634 (h1 : term233) : term233.
Proof. exact (h1). Qed.
Lemma lem1388635 (h1 : term214) : term214.
Proof. exact (h1). Qed.
Lemma lem1388655 (x : real) (y : real) : (term238 x y) = (term239 x y).
Proof. exact (@lem17160 (term74 x y) (term26 = (real_add x y))). Qed.
Lemma lem1388657 (x : real) (y : real) : (term240 x y) = (term240 x y).
Proof. exact (eq_refl (term240 x y)). Qed.
Lemma lem1388658 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1388657 x y) (@lem1388655 x y)). Qed.
Lemma lem1388659 (x : real) (y : real) : (term243 x y) = (term241 x y).
Proof. exact (@lem17362 (term186 x y) (term189 x y)). Qed.
Lemma lem1388660 (x : real) (y : real) : (term243 x y) = (term242 x y).
Proof. exact (TRANS (@lem1388659 x y) (@lem1388658 x y)). Qed.
Lemma lem1388675 (x : real) (y : real) : (term244 x y) = (term245 x y).
Proof. exact (@lem17362 (term192 x y) (term74 x y)). Qed.
Lemma lem1388690 (x : real) (y : real) : (term246 x y) = (term247 x y).
Proof. exact (@lem17362 (term197 x y) (term74 x y)). Qed.
Lemma lem1388701 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (@lem17362 (term164 x y) (term74 x y)). Qed.
Lemma lem1388702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1388703 (x : real) (y : real) : (term250 x y) = (term251 x y).
Proof. exact (MK_COMB (@lem1388702) (@lem1388690 x y)). Qed.
Lemma lem1388704 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (MK_COMB (@lem1388703 x y) (@lem1388701 x y)). Qed.
Lemma lem1388705 (x : real) (y : real) : (term254 x y) = (term252 x y).
Proof. exact (@lem17045 (term200 x y) (term170 x y)). Qed.
Lemma lem1388706 (x : real) (y : real) : (term254 x y) = (term253 x y).
Proof. exact (TRANS (@lem1388705 x y) (@lem1388704 x y)). Qed.
Lemma lem1388707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1388708 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem1388707) (@lem1388675 x y)). Qed.
Lemma lem1388709 (x : real) (y : real) : (term257 x y) = (term258 x y).
Proof. exact (MK_COMB (@lem1388708 x y) (@lem1388706 x y)). Qed.
Lemma lem1388710 (x : real) (y : real) : (term259 x y) = (term257 x y).
Proof. exact (@lem17045 (term195 x y) (term202 x y)). Qed.
Lemma lem1388711 (x : real) (y : real) : (term259 x y) = (term258 x y).
Proof. exact (TRANS (@lem1388710 x y) (@lem1388709 x y)). Qed.
Lemma lem1388712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1388713 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1388712) (@lem1388660 x y)). Qed.
Lemma lem1388714 (x : real) (y : real) : (term262 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1388713 x y) (@lem1388711 x y)). Qed.
Lemma lem1388715 (x : real) (y : real) : (term207 x y) = (term262 x y).
Proof. exact (@lem17045 (term190 x y) (term203 x y)). Qed.
Lemma lem1388720 (x : real) (y : real) : (term207 x y) = (term263 x y).
Proof. exact (TRANS (@lem1388715 x y) (@lem1388714 x y)). Qed.
Lemma lem1388728 (x : real) (y : real) : (term264 x y) = (term265 x y).
Proof. exact (@lem17045 (term70 x) (term70 y)). Qed.
Lemma lem1388729 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1388730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1388731 (x : real) (y : real) : (term266 x y) = (term267 x y).
Proof. exact (MK_COMB (@lem1388730) (@lem1388728 x y)). Qed.
Lemma lem1388732 (x : real) (y : real) : (term268 x y) = (term269 x y).
Proof. exact (MK_COMB (@lem1388731 x y) (@lem1388729 x y)). Qed.
Lemma lem1388733 (x : real) (y : real) : (term170 x y) = (term268 x y).
Proof. exact (@lem17265 (term164 x y) (term74 x y)). Qed.
Lemma lem1388734 (x : real) (y : real) : (term170 x y) = (term269 x y).
Proof. exact (TRANS (@lem1388733 x y) (@lem1388732 x y)). Qed.
Lemma lem1388735 (x : real) : (term234 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1388734 x y)). Qed.
Lemma lem1388736 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388737 (x : real) : (term235 x) = (term271 x).
Proof. exact (MK_COMB (@lem1388736) (@lem1388735 x)). Qed.
Lemma lem1388738 : term236 = term272.
Proof. exact (fun_ext (fun x : real => @lem1388737 x)). Qed.
Lemma lem1388739 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388796 : term237 = term273.
Proof. exact (MK_COMB (@lem1388739) (@lem1388738)). Qed.
Lemma lem1388797 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1388796) (@lem1388633 h1)). Qed.
Lemma lem1388798 (x : real) : ((term18 x) = x) = ((term18 x) = x).
Proof. exact (eq_refl ((term18 x) = x)). Qed.
Lemma lem1388799 : term232 = term232.
Proof. exact (fun_ext (fun x : real => @lem1388798 x)). Qed.
Lemma lem1388800 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388809 : term233 = term233.
Proof. exact (MK_COMB (@lem1388800) (@lem1388799)). Qed.
Lemma lem1388810 (h1 : term233) : term233.
Proof. exact (EQ_MP (@lem1388809) (@lem1388634 h1)). Qed.
Lemma lem1388811 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1388812 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1388811 x)). Qed.
Lemma lem1388813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1388822 : term214 = term214.
Proof. exact (MK_COMB (@lem1388813) (@lem1388812)). Qed.
Lemma lem1388823 (h1 : term214) : term214.
Proof. exact (EQ_MP (@lem1388822) (@lem1388635 h1)). Qed.
Lemma lem1389055 (x : real) (y : real) (h1 : term207 x y) : term263 x y.
Proof. exact (EQ_MP (@lem1388720 x y) (@lem1388632 x y h1)). Qed.
Lemma lem1389096 (x : real) (y : real) : (term269 x y) = (term269 x y).
Proof. exact (eq_refl (term269 x y)). Qed.
Lemma lem1389097 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1389096 x y)). Qed.
Lemma lem1389098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389099 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1389098) (@lem1389097 x)). Qed.
Lemma lem1389100 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem1389099 x)). Qed.
Lemma lem1389101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389102 : term273 = term273.
Proof. exact (MK_COMB (@lem1389101) (@lem1389100)). Qed.
Lemma lem1389103 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1389102) (@lem1388797 h1)). Qed.
Lemma lem1389116 (x : real) : ((term18 x) = x) = ((term18 x) = x).
Proof. exact (eq_refl ((term18 x) = x)). Qed.
Lemma lem1389117 : term232 = term232.
Proof. exact (fun_ext (fun x : real => @lem1389116 x)). Qed.
Lemma lem1389118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389119 : term233 = term233.
Proof. exact (MK_COMB (@lem1389118) (@lem1389117)). Qed.
Lemma lem1389120 (h1 : term233) : term233.
Proof. exact (EQ_MP (@lem1389119) (@lem1388810 h1)). Qed.
Lemma lem1389133 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1389134 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1389133 x)). Qed.
Lemma lem1389135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389136 : term214 = term214.
Proof. exact (MK_COMB (@lem1389135) (@lem1389134)). Qed.
Lemma lem1389137 (h1 : term214) : term214.
Proof. exact (EQ_MP (@lem1389136) (@lem1388823 h1)). Qed.
Lemma lem1389138 (x : real) (y : real) (h1 : term242 x y) : term242 x y.
Proof. exact (h1). Qed.
Lemma lem1389139 (x : real) (y : real) (h1 : term258 x y) : term258 x y.
Proof. exact (h1). Qed.
Lemma lem1389140 (x : real) (y : real) (h1 : term242 x y) : term239 x y.
Proof. exact (proj2 (@lem1389138 x y h1)). Qed.
Lemma lem1389141 (x : real) (y : real) (h1 : term242 x y) : term186 x y.
Proof. exact (proj1 (@lem1389138 x y h1)). Qed.
Lemma lem1389144 (x : real) (y : real) (h1 : term242 x y) : term184 y.
Proof. exact (proj2 (@lem1389141 x y h1)). Qed.
Lemma lem1389145 (x : real) (y : real) (h1 : term242 x y) : term184 x.
Proof. exact (proj1 (@lem1389141 x y h1)). Qed.
Lemma lem1389152 (x : real) (y : real) (h1 : term245 x y) : term245 x y.
Proof. exact (h1). Qed.
Lemma lem1389153 (x : real) (y : real) (h1 : term253 x y) : term253 x y.
Proof. exact (h1). Qed.
Lemma lem1389155 (x : real) (y : real) (h1 : term245 x y) : term192 x y.
Proof. exact (proj1 (@lem1389152 x y h1)). Qed.
Lemma lem1389157 (x : real) (y : real) (h1 : term245 x y) : term184 x.
Proof. exact (proj1 (@lem1389155 x y h1)). Qed.
Lemma lem1389160 (x : real) (y : real) (h1 : term247 x y) : term247 x y.
Proof. exact (h1). Qed.
Lemma lem1389161 (x : real) (y : real) (h1 : term249 x y) : term249 x y.
Proof. exact (h1). Qed.
Lemma lem1389163 (x : real) (y : real) (h1 : term247 x y) : term197 x y.
Proof. exact (proj1 (@lem1389160 x y h1)). Qed.
Lemma lem1389164 (x : real) (y : real) (h1 : term247 x y) : term184 y.
Proof. exact (proj2 (@lem1389163 x y h1)). Qed.
Lemma lem1389169 (x : real) (y : real) (h1 : term249 x y) : term164 x y.
Proof. exact (proj1 (@lem1389161 x y h1)). Qed.
Lemma lem1389185 (x : real) (y : real) : (term269 x y) = (term269 x y).
Proof. exact (eq_refl (term269 x y)). Qed.
Lemma lem1389186 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1389185 x y)). Qed.
Lemma lem1389187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389188 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1389187) (@lem1389186 x)). Qed.
Lemma lem1389189 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem1389188 x)). Qed.
Lemma lem1389190 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389192 : term273 = term273.
Proof. exact (MK_COMB (@lem1389190) (@lem1389189)). Qed.
Lemma lem1389193 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1389192) (@lem1389103 h1)). Qed.
Lemma lem1389219 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389223 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389254 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1389255 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1389254 x)). Qed.
Lemma lem1389256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389258 : term214 = term214.
Proof. exact (MK_COMB (@lem1389256) (@lem1389255)). Qed.
Lemma lem1389259 (h1 : term214) : term214.
Proof. exact (EQ_MP (@lem1389258) (@lem1389137 h1)). Qed.
Lemma lem1389271 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389275 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389299 (x : real) : ((term18 x) = x) = ((term18 x) = x).
Proof. exact (eq_refl ((term18 x) = x)). Qed.
Lemma lem1389300 : term232 = term232.
Proof. exact (fun_ext (fun x : real => @lem1389299 x)). Qed.
Lemma lem1389301 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389303 : term233 = term233.
Proof. exact (MK_COMB (@lem1389301) (@lem1389300)). Qed.
Lemma lem1389304 (h1 : term233) : term233.
Proof. exact (EQ_MP (@lem1389303) (@lem1389120 h1)). Qed.
Lemma lem1389323 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389327 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389358 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1389359 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1389358 x)). Qed.
Lemma lem1389360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389362 : term214 = term214.
Proof. exact (MK_COMB (@lem1389360) (@lem1389359)). Qed.
Lemma lem1389363 (h1 : term214) : term214.
Proof. exact (EQ_MP (@lem1389362) (@lem1389137 h1)). Qed.
Lemma lem1389375 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389379 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389393 (x : real) (y : real) : (term269 x y) = (term269 x y).
Proof. exact (eq_refl (term269 x y)). Qed.
Lemma lem1389394 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1389393 x y)). Qed.
Lemma lem1389395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389396 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1389395) (@lem1389394 x)). Qed.
Lemma lem1389397 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem1389396 x)). Qed.
Lemma lem1389398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389400 : term273 = term273.
Proof. exact (MK_COMB (@lem1389398) (@lem1389397)). Qed.
Lemma lem1389401 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1389400) (@lem1389103 h1)). Qed.
Lemma lem1389427 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389458 (x : real) : ((term20 x) = x) = ((term20 x) = x).
Proof. exact (eq_refl ((term20 x) = x)). Qed.
Lemma lem1389459 : term231 = term231.
Proof. exact (fun_ext (fun x : real => @lem1389458 x)). Qed.
Lemma lem1389460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389462 : term214 = term214.
Proof. exact (MK_COMB (@lem1389460) (@lem1389459)). Qed.
Lemma lem1389463 (h1 : term214) : term214.
Proof. exact (EQ_MP (@lem1389462) (@lem1389137 h1)). Qed.
Lemma lem1389475 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389489 (x : real) (y : real) : (term269 x y) = (term269 x y).
Proof. exact (eq_refl (term269 x y)). Qed.
Lemma lem1389490 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1389489 x y)). Qed.
Lemma lem1389491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389492 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1389491) (@lem1389490 x)). Qed.
Lemma lem1389493 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem1389492 x)). Qed.
Lemma lem1389494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389496 : term273 = term273.
Proof. exact (MK_COMB (@lem1389494) (@lem1389493)). Qed.
Lemma lem1389497 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1389496) (@lem1389103 h1)). Qed.
Lemma lem1389523 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389547 (x : real) : ((term18 x) = x) = ((term18 x) = x).
Proof. exact (eq_refl ((term18 x) = x)). Qed.
Lemma lem1389548 : term232 = term232.
Proof. exact (fun_ext (fun x : real => @lem1389547 x)). Qed.
Lemma lem1389549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389551 : term233 = term233.
Proof. exact (MK_COMB (@lem1389549) (@lem1389548)). Qed.
Lemma lem1389552 (h1 : term233) : term233.
Proof. exact (EQ_MP (@lem1389551) (@lem1389120 h1)). Qed.
Lemma lem1389571 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389585 (x : real) (y : real) : (term269 x y) = (term269 x y).
Proof. exact (eq_refl (term269 x y)). Qed.
Lemma lem1389586 (x : real) : (term270 x) = (term270 x).
Proof. exact (fun_ext (fun y : real => @lem1389585 x y)). Qed.
Lemma lem1389587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389588 (x : real) : (term271 x) = (term271 x).
Proof. exact (MK_COMB (@lem1389587) (@lem1389586 x)). Qed.
Lemma lem1389589 : term272 = term272.
Proof. exact (fun_ext (fun x : real => @lem1389588 x)). Qed.
Lemma lem1389590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1389592 : term273 = term273.
Proof. exact (MK_COMB (@lem1389590) (@lem1389589)). Qed.
Lemma lem1389593 (h1 : term237) : term273.
Proof. exact (EQ_MP (@lem1389592) (@lem1389103 h1)). Qed.
Lemma lem1389620 (_24552 : real) (h1 : term237) : term274 _24552.
Proof. exact (@lem1389193 h1 _24552). Qed.
Lemma lem1389621 (_24552 : real) : (term274 _24552) = (term271 _24552).
Proof. exact (eq_refl (term274 _24552)). Qed.
Lemma lem1389622 (_24552 : real) (h1 : term237) : term271 _24552.
Proof. exact (EQ_MP (@lem1389621 _24552) (@lem1389620 _24552 h1)). Qed.
Lemma lem1389623 (_24552 : real) (_24553 : real) (h1 : term237) : term275 _24552 _24553.
Proof. exact (@lem1389622 _24552 h1 _24553). Qed.
Lemma lem1389624 (_24552 : real) (_24553 : real) : (term275 _24552 _24553) = (term269 _24552 _24553).
Proof. exact (eq_refl (term275 _24552 _24553)). Qed.
Lemma lem1389625 (_24552 : real) (_24553 : real) (h1 : term237) : term269 _24552 _24553.
Proof. exact (EQ_MP (@lem1389624 _24552 _24553) (@lem1389623 _24552 _24553 h1)). Qed.
Lemma lem1389641 (_24559 : real) (h1 : term214) : term19 _24559.
Proof. exact (@lem1389259 h1 _24559). Qed.
Lemma lem1389642 (_24559 : real) : (term19 _24559) = ((term20 _24559) = _24559).
Proof. exact (eq_refl (term19 _24559)). Qed.
Lemma lem1389650 (_24562 : real) (h1 : term233) : term17 _24562.
Proof. exact (@lem1389304 h1 _24562). Qed.
Lemma lem1389651 (_24562 : real) : (term17 _24562) = ((term18 _24562) = _24562).
Proof. exact (eq_refl (term17 _24562)). Qed.
Lemma lem1389665 (_24567 : real) (h1 : term214) : term19 _24567.
Proof. exact (@lem1389363 h1 _24567). Qed.
Lemma lem1389666 (_24567 : real) : (term19 _24567) = ((term20 _24567) = _24567).
Proof. exact (eq_refl (term19 _24567)). Qed.
Lemma lem1389668 (_24568 : real) (h1 : term237) : term274 _24568.
Proof. exact (@lem1389401 h1 _24568). Qed.
Lemma lem1389669 (_24568 : real) : (term274 _24568) = (term271 _24568).
Proof. exact (eq_refl (term274 _24568)). Qed.
Lemma lem1389670 (_24568 : real) (h1 : term237) : term271 _24568.
Proof. exact (EQ_MP (@lem1389669 _24568) (@lem1389668 _24568 h1)). Qed.
Lemma lem1389671 (_24568 : real) (_24569 : real) (h1 : term237) : term275 _24568 _24569.
Proof. exact (@lem1389670 _24568 h1 _24569). Qed.
Lemma lem1389672 (_24568 : real) (_24569 : real) : (term275 _24568 _24569) = (term269 _24568 _24569).
Proof. exact (eq_refl (term275 _24568 _24569)). Qed.
Lemma lem1389673 (_24568 : real) (_24569 : real) (h1 : term237) : term269 _24568 _24569.
Proof. exact (EQ_MP (@lem1389672 _24568 _24569) (@lem1389671 _24568 _24569 h1)). Qed.
Lemma lem1389689 (_24575 : real) (h1 : term214) : term19 _24575.
Proof. exact (@lem1389463 h1 _24575). Qed.
Lemma lem1389690 (_24575 : real) : (term19 _24575) = ((term20 _24575) = _24575).
Proof. exact (eq_refl (term19 _24575)). Qed.
Lemma lem1389692 (_24576 : real) (h1 : term237) : term274 _24576.
Proof. exact (@lem1389497 h1 _24576). Qed.
Lemma lem1389693 (_24576 : real) : (term274 _24576) = (term271 _24576).
Proof. exact (eq_refl (term274 _24576)). Qed.
Lemma lem1389694 (_24576 : real) (h1 : term237) : term271 _24576.
Proof. exact (EQ_MP (@lem1389693 _24576) (@lem1389692 _24576 h1)). Qed.
Lemma lem1389695 (_24576 : real) (_24577 : real) (h1 : term237) : term275 _24576 _24577.
Proof. exact (@lem1389694 _24576 h1 _24577). Qed.
Lemma lem1389696 (_24576 : real) (_24577 : real) : (term275 _24576 _24577) = (term269 _24576 _24577).
Proof. exact (eq_refl (term275 _24576 _24577)). Qed.
Lemma lem1389697 (_24576 : real) (_24577 : real) (h1 : term237) : term269 _24576 _24577.
Proof. exact (EQ_MP (@lem1389696 _24576 _24577) (@lem1389695 _24576 _24577 h1)). Qed.
Lemma lem1389710 (_24582 : real) (h1 : term233) : term17 _24582.
Proof. exact (@lem1389552 h1 _24582). Qed.
Lemma lem1389711 (_24582 : real) : (term17 _24582) = ((term18 _24582) = _24582).
Proof. exact (eq_refl (term17 _24582)). Qed.
Lemma lem1389716 (_24584 : real) (h1 : term237) : term274 _24584.
Proof. exact (@lem1389593 h1 _24584). Qed.
Lemma lem1389717 (_24584 : real) : (term274 _24584) = (term271 _24584).
Proof. exact (eq_refl (term274 _24584)). Qed.
Lemma lem1389718 (_24584 : real) (h1 : term237) : term271 _24584.
Proof. exact (EQ_MP (@lem1389717 _24584) (@lem1389716 _24584 h1)). Qed.
Lemma lem1389719 (_24584 : real) (_24585 : real) (h1 : term237) : term275 _24584 _24585.
Proof. exact (@lem1389718 _24584 h1 _24585). Qed.
Lemma lem1389720 (_24584 : real) (_24585 : real) : (term275 _24584 _24585) = (term269 _24584 _24585).
Proof. exact (eq_refl (term275 _24584 _24585)). Qed.
Lemma lem1389721 (_24584 : real) (_24585 : real) (h1 : term237) : term269 _24584 _24585.
Proof. exact (EQ_MP (@lem1389720 _24584 _24585) (@lem1389719 _24584 _24585 h1)). Qed.
Lemma lem1389738 (_24552 : real) (_24553 : real) : (term269 _24552 _24553) = (term276 _24552 _24553).
Proof. exact (@lem1386588 (term277 _24552) (term277 _24553) (term74 _24552 _24553)). Qed.
Lemma lem1389739 (_24552 : real) (_24553 : real) (h1 : term237) : term276 _24552 _24553.
Proof. exact (EQ_MP (@lem1389738 _24552 _24553) (@lem1389625 _24552 _24553 h1)). Qed.
Lemma lem1389745 (x : real) (y : real) (h1 : term242 x y) : term278 x y.
Proof. exact (proj1 (@lem1389140 x y h1)). Qed.
Lemma lem1389749 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389751 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389769 (x : real) (y : real) (h1 : term242 x y) : term278 x y.
Proof. exact (proj1 (@lem1389140 x y h1)). Qed.
Lemma lem1389773 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389775 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389793 (x : real) (y : real) (h1 : term242 x y) : term278 x y.
Proof. exact (proj1 (@lem1389140 x y h1)). Qed.
Lemma lem1389797 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389799 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389819 (x : real) (y : real) (h1 : term242 x y) : term279 x y.
Proof. exact (proj2 (@lem1389140 x y h1)). Qed.
Lemma lem1389821 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389823 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389834 (_24568 : real) (_24569 : real) : (term269 _24568 _24569) = (term276 _24568 _24569).
Proof. exact (@lem1386588 (term277 _24568) (term277 _24569) (term74 _24568 _24569)). Qed.
Lemma lem1389835 (_24568 : real) (_24569 : real) (h1 : term237) : term276 _24568 _24569.
Proof. exact (EQ_MP (@lem1389834 _24568 _24569) (@lem1389673 _24568 _24569 h1)). Qed.
Lemma lem1389841 (x : real) (y : real) (h1 : term245 x y) : term278 x y.
Proof. exact (proj2 (@lem1389152 x y h1)). Qed.
Lemma lem1389845 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1389863 (x : real) (y : real) (h1 : term245 x y) : term278 x y.
Proof. exact (proj2 (@lem1389152 x y h1)). Qed.
Lemma lem1389867 (x : real) (h1 : term26 = x) : term26 = x.
Proof. exact (h1). Qed.
Lemma lem1389878 (_24576 : real) (_24577 : real) : (term269 _24576 _24577) = (term276 _24576 _24577).
Proof. exact (@lem1386588 (term277 _24576) (term277 _24577) (term74 _24576 _24577)). Qed.
Lemma lem1389879 (_24576 : real) (_24577 : real) (h1 : term237) : term276 _24576 _24577.
Proof. exact (EQ_MP (@lem1389878 _24576 _24577) (@lem1389697 _24576 _24577 h1)). Qed.
Lemma lem1389885 (x : real) (y : real) (h1 : term247 x y) : term278 x y.
Proof. exact (proj2 (@lem1389160 x y h1)). Qed.
Lemma lem1389889 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1389907 (x : real) (y : real) (h1 : term247 x y) : term278 x y.
Proof. exact (proj2 (@lem1389160 x y h1)). Qed.
Lemma lem1389911 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1389922 (_24584 : real) (_24585 : real) : (term269 _24584 _24585) = (term276 _24584 _24585).
Proof. exact (@lem1386588 (term277 _24584) (term277 _24585) (term74 _24584 _24585)). Qed.
Lemma lem1389923 (_24584 : real) (_24585 : real) (h1 : term237) : term276 _24584 _24585.
Proof. exact (EQ_MP (@lem1389922 _24584 _24585) (@lem1389721 _24584 _24585 h1)). Qed.
Lemma lem1389929 (x : real) (y : real) (h1 : term249 x y) : term278 x y.
Proof. exact (proj2 (@lem1389161 x y h1)). Qed.
Lemma lem1389934 (x : real) (h1 : term26 = x) : x = term26.
Proof. exact (SYM (@lem1389775 x h1)). Qed.
Lemma lem1389991 (y : real) : (term280 y) = (term280 y).
Proof. exact (eq_refl (term280 y)). Qed.
Lemma lem1389992 (y : real) (x : real) (h1 : term26 = x) : (term281 y x) = (term282 y).
Proof. exact (MK_COMB (@lem1389991 y) (@lem1389934 x h1)). Qed.
Lemma lem1389993 (y : real) : (term282 y) = (term283 y).
Proof. exact (eq_refl (term282 y)). Qed.
Lemma lem1389994 (y : real) (x : real) : (term284 y x) = (term284 y x).
Proof. exact (eq_refl (term284 y x)). Qed.
Lemma lem1389995 (x : real) (y : real) : ((term281 y x) = (term282 y)) = ((term281 y x) = (term283 y)).
Proof. exact (MK_COMB (@lem1389994 y x) (@lem1389993 y)). Qed.
Lemma lem1389996 (x : real) (y : real) : (term281 y x) = (term278 x y).
Proof. exact (eq_refl (term281 y x)). Qed.
Lemma lem1389997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1389998 (x : real) (y : real) : (term284 y x) = (term285 x y).
Proof. exact (MK_COMB (@lem1389997) (@lem1389996 x y)). Qed.
Lemma lem1389999 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1390000 (x : real) (y : real) : ((term281 y x) = (term283 y)) = ((term278 x y) = (term283 y)).
Proof. exact (MK_COMB (@lem1389998 x y) (@lem1389999 y)). Qed.
Lemma lem1390001 (x : real) (y : real) : ((term281 y x) = (term282 y)) = ((term278 x y) = (term283 y)).
Proof. exact (TRANS (@lem1389995 x y) (@lem1390000 x y)). Qed.
Lemma lem1390002 (y : real) (x : real) (h1 : term26 = x) : (term278 x y) = (term283 y).
Proof. exact (EQ_MP (@lem1390001 x y) (@lem1389992 y x h1)). Qed.
Lemma lem1390003 (y : real) (x : real) (h1 : term242 x y) (h2 : term26 = x) : term283 y.
Proof. exact (EQ_MP (@lem1390002 y x h2) (@lem1389769 x y h1)). Qed.
Lemma lem1390030 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1390031 (y : real) (h1 : term26 = y) : y = term26.
Proof. exact (SYM (@lem1389797 y h1)). Qed.
Lemma lem1390088 (x : real) : (term286 x) = (term286 x).
Proof. exact (eq_refl (term286 x)). Qed.
Lemma lem1390089 (x : real) (y : real) (h1 : term26 = y) : (term287 x y) = (term288 x).
Proof. exact (MK_COMB (@lem1390088 x) (@lem1390031 y h1)). Qed.
Lemma lem1390090 (x : real) : (term288 x) = (term289 x).
Proof. exact (eq_refl (term288 x)). Qed.
Lemma lem1390091 (x : real) (y : real) : (term290 x y) = (term290 x y).
Proof. exact (eq_refl (term290 x y)). Qed.
Lemma lem1390092 (y : real) (x : real) : ((term287 x y) = (term288 x)) = ((term287 x y) = (term289 x)).
Proof. exact (MK_COMB (@lem1390091 x y) (@lem1390090 x)). Qed.
Lemma lem1390093 (x : real) (y : real) : (term287 x y) = (term278 x y).
Proof. exact (eq_refl (term287 x y)). Qed.
Lemma lem1390094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390095 (x : real) (y : real) : (term290 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1390094) (@lem1390093 x y)). Qed.
Lemma lem1390096 (x : real) : (term289 x) = (term289 x).
Proof. exact (eq_refl (term289 x)). Qed.
Lemma lem1390097 (y : real) (x : real) : ((term287 x y) = (term289 x)) = ((term278 x y) = (term289 x)).
Proof. exact (MK_COMB (@lem1390095 x y) (@lem1390096 x)). Qed.
Lemma lem1390098 (y : real) (x : real) : ((term287 x y) = (term288 x)) = ((term278 x y) = (term289 x)).
Proof. exact (TRANS (@lem1390092 y x) (@lem1390097 y x)). Qed.
Lemma lem1390099 (x : real) (y : real) (h1 : term26 = y) : (term278 x y) = (term289 x).
Proof. exact (EQ_MP (@lem1390098 y x) (@lem1390089 x y h1)). Qed.
Lemma lem1390100 (x : real) (y : real) (h1 : term242 x y) (h2 : term26 = y) : term289 x.
Proof. exact (EQ_MP (@lem1390099 x y h2) (@lem1389793 x y h1)). Qed.
Lemma lem1390127 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1390128 (x : real) (h1 : term26 = x) : x = term26.
Proof. exact (SYM (@lem1389823 x h1)). Qed.
Lemma lem1390198 (y : real) : (term291 y) = (term291 y).
Proof. exact (eq_refl (term291 y)). Qed.
Lemma lem1390199 (y : real) (x : real) (h1 : term26 = x) : (term292 y x) = (term293 y).
Proof. exact (MK_COMB (@lem1390198 y) (@lem1390128 x h1)). Qed.
Lemma lem1390200 (y : real) : (term293 y) = (term294 y).
Proof. exact (eq_refl (term293 y)). Qed.
Lemma lem1390201 (y : real) (x : real) : (term295 y x) = (term295 y x).
Proof. exact (eq_refl (term295 y x)). Qed.
Lemma lem1390202 (x : real) (y : real) : ((term292 y x) = (term293 y)) = ((term292 y x) = (term294 y)).
Proof. exact (MK_COMB (@lem1390201 y x) (@lem1390200 y)). Qed.
Lemma lem1390203 (x : real) (y : real) : (term292 y x) = (term279 x y).
Proof. exact (eq_refl (term292 y x)). Qed.
Lemma lem1390204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390205 (x : real) (y : real) : (term295 y x) = (term296 x y).
Proof. exact (MK_COMB (@lem1390204) (@lem1390203 x y)). Qed.
Lemma lem1390206 (y : real) : (term294 y) = (term294 y).
Proof. exact (eq_refl (term294 y)). Qed.
Lemma lem1390207 (x : real) (y : real) : ((term292 y x) = (term294 y)) = ((term279 x y) = (term294 y)).
Proof. exact (MK_COMB (@lem1390205 x y) (@lem1390206 y)). Qed.
Lemma lem1390208 (x : real) (y : real) : ((term292 y x) = (term293 y)) = ((term279 x y) = (term294 y)).
Proof. exact (TRANS (@lem1390202 x y) (@lem1390207 x y)). Qed.
Lemma lem1390209 (y : real) (x : real) (h1 : term26 = x) : (term279 x y) = (term294 y).
Proof. exact (EQ_MP (@lem1390208 x y) (@lem1390199 y x h1)). Qed.
Lemma lem1390210 (y : real) (x : real) (h1 : term242 x y) (h2 : term26 = x) : term294 y.
Proof. exact (EQ_MP (@lem1390209 y x h2) (@lem1389819 x y h1)). Qed.
Lemma lem1390224 (y : real) (h1 : term26 = y) : term26 = y.
Proof. exact (h1). Qed.
Lemma lem1390225 (y : real) (h1 : term26 = y) : y = term26.
Proof. exact (SYM (@lem1390224 y h1)). Qed.
Lemma lem1390295 : term297 = term297.
Proof. exact (eq_refl term297). Qed.
Lemma lem1390296 (y : real) (h1 : term26 = y) : (term298 y) = term299.
Proof. exact (MK_COMB (@lem1390295) (@lem1390225 y h1)). Qed.
Lemma lem1390297 : term299 = term300.
Proof. exact (eq_refl term299). Qed.
Lemma lem1390298 (y : real) : (term301 y) = (term301 y).
Proof. exact (eq_refl (term301 y)). Qed.
Lemma lem1390299 (y : real) : ((term298 y) = term299) = ((term298 y) = term300).
Proof. exact (MK_COMB (@lem1390298 y) (@lem1390297)). Qed.
Lemma lem1390300 (y : real) : (term298 y) = (term294 y).
Proof. exact (eq_refl (term298 y)). Qed.
Lemma lem1390301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390302 (y : real) : (term301 y) = (term302 y).
Proof. exact (MK_COMB (@lem1390301) (@lem1390300 y)). Qed.
Lemma lem1390303 : term300 = term300.
Proof. exact (eq_refl term300). Qed.
Lemma lem1390304 (y : real) : ((term298 y) = term300) = ((term294 y) = term300).
Proof. exact (MK_COMB (@lem1390302 y) (@lem1390303)). Qed.
Lemma lem1390305 (y : real) : ((term298 y) = term299) = ((term294 y) = term300).
Proof. exact (TRANS (@lem1390299 y) (@lem1390304 y)). Qed.
Lemma lem1390306 (y : real) (h1 : term26 = y) : (term294 y) = term300.
Proof. exact (EQ_MP (@lem1390305 y) (@lem1390296 y h1)). Qed.
Lemma lem1390307 (x : real) (y : real) (h1 : term242 x y) (h2 : term26 = x) (h3 : term26 = y) : term300.
Proof. exact (EQ_MP (@lem1390306 y h3) (@lem1390210 y x h1 h2)). Qed.
Lemma lem1390308 (x : real) (h1 : term26 = x) : x = term26.
Proof. exact (SYM (@lem1389867 x h1)). Qed.
Lemma lem1390365 (y : real) : (term280 y) = (term280 y).
Proof. exact (eq_refl (term280 y)). Qed.
Lemma lem1390366 (y : real) (x : real) (h1 : term26 = x) : (term281 y x) = (term282 y).
Proof. exact (MK_COMB (@lem1390365 y) (@lem1390308 x h1)). Qed.
Lemma lem1390367 (y : real) : (term282 y) = (term283 y).
Proof. exact (eq_refl (term282 y)). Qed.
Lemma lem1390368 (y : real) (x : real) : (term284 y x) = (term284 y x).
Proof. exact (eq_refl (term284 y x)). Qed.
Lemma lem1390369 (x : real) (y : real) : ((term281 y x) = (term282 y)) = ((term281 y x) = (term283 y)).
Proof. exact (MK_COMB (@lem1390368 y x) (@lem1390367 y)). Qed.
Lemma lem1390370 (x : real) (y : real) : (term281 y x) = (term278 x y).
Proof. exact (eq_refl (term281 y x)). Qed.
Lemma lem1390371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390372 (x : real) (y : real) : (term284 y x) = (term285 x y).
Proof. exact (MK_COMB (@lem1390371) (@lem1390370 x y)). Qed.
Lemma lem1390373 (y : real) : (term283 y) = (term283 y).
Proof. exact (eq_refl (term283 y)). Qed.
Lemma lem1390374 (x : real) (y : real) : ((term281 y x) = (term283 y)) = ((term278 x y) = (term283 y)).
Proof. exact (MK_COMB (@lem1390372 x y) (@lem1390373 y)). Qed.
Lemma lem1390375 (x : real) (y : real) : ((term281 y x) = (term282 y)) = ((term278 x y) = (term283 y)).
Proof. exact (TRANS (@lem1390369 x y) (@lem1390374 x y)). Qed.
Lemma lem1390376 (y : real) (x : real) (h1 : term26 = x) : (term278 x y) = (term283 y).
Proof. exact (EQ_MP (@lem1390375 x y) (@lem1390366 y x h1)). Qed.
Lemma lem1390377 (y : real) (x : real) (h1 : term245 x y) (h2 : term26 = x) : term283 y.
Proof. exact (EQ_MP (@lem1390376 y x h2) (@lem1389863 x y h1)). Qed.
Lemma lem1390392 (y : real) (h1 : term26 = y) : y = term26.
Proof. exact (SYM (@lem1389911 y h1)). Qed.
Lemma lem1390449 (x : real) : (term286 x) = (term286 x).
Proof. exact (eq_refl (term286 x)). Qed.
Lemma lem1390450 (x : real) (y : real) (h1 : term26 = y) : (term287 x y) = (term288 x).
Proof. exact (MK_COMB (@lem1390449 x) (@lem1390392 y h1)). Qed.
Lemma lem1390451 (x : real) : (term288 x) = (term289 x).
Proof. exact (eq_refl (term288 x)). Qed.
Lemma lem1390452 (x : real) (y : real) : (term290 x y) = (term290 x y).
Proof. exact (eq_refl (term290 x y)). Qed.
Lemma lem1390453 (y : real) (x : real) : ((term287 x y) = (term288 x)) = ((term287 x y) = (term289 x)).
Proof. exact (MK_COMB (@lem1390452 x y) (@lem1390451 x)). Qed.
Lemma lem1390454 (x : real) (y : real) : (term287 x y) = (term278 x y).
Proof. exact (eq_refl (term287 x y)). Qed.
Lemma lem1390455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390456 (x : real) (y : real) : (term290 x y) = (term285 x y).
Proof. exact (MK_COMB (@lem1390455) (@lem1390454 x y)). Qed.
Lemma lem1390457 (x : real) : (term289 x) = (term289 x).
Proof. exact (eq_refl (term289 x)). Qed.
Lemma lem1390458 (y : real) (x : real) : ((term287 x y) = (term289 x)) = ((term278 x y) = (term289 x)).
Proof. exact (MK_COMB (@lem1390456 x y) (@lem1390457 x)). Qed.
Lemma lem1390459 (y : real) (x : real) : ((term287 x y) = (term288 x)) = ((term278 x y) = (term289 x)).
Proof. exact (TRANS (@lem1390453 y x) (@lem1390458 y x)). Qed.
Lemma lem1390460 (x : real) (y : real) (h1 : term26 = y) : (term278 x y) = (term289 x).
Proof. exact (EQ_MP (@lem1390459 y x) (@lem1390450 x y h1)). Qed.
Lemma lem1390461 (x : real) (y : real) (h1 : term247 x y) (h2 : term26 = y) : term289 x.
Proof. exact (EQ_MP (@lem1390460 x y h2) (@lem1389907 x y h1)). Qed.
Lemma lem1390531 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1390532 (x : real) (h1 : term70 x) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1390531 x h1). Qed.
Lemma lem1390534 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390535 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1390534 (term70 x)). Qed.
Lemma lem1390536 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (EQ_MP (@lem1390535 x) (@lem1390532 x h1)). Qed.
Lemma lem1390538 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1390539 (y : real) (h1 : term70 y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1390538 y h1). Qed.
Lemma lem1390541 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390542 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1390541 (term70 y)). Qed.
Lemma lem1390543 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (EQ_MP (@lem1390542 y) (@lem1390539 y h1)). Qed.
Lemma lem1390559 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1390560 (_24552 : real) (_24553 : real) : (term305 _24552 _24553) = (term306 _24552 _24553).
Proof. exact (@lem1390559 (term74 _24552 _24553) (term277 _24553)). Qed.
Lemma lem1390566 (_24552 : real) : (term307 _24552) = (term307 _24552).
Proof. exact (eq_refl (term307 _24552)). Qed.
Lemma lem1390567 (_24552 : real) (_24553 : real) : (term276 _24552 _24553) = (term308 _24552 _24553).
Proof. exact (MK_COMB (@lem1390566 _24552) (@lem1390560 _24552 _24553)). Qed.
Lemma lem1390571 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1390572 (_24552 : real) (_24553 : real) : (term308 _24552 _24553) = (term309 _24552 _24553).
Proof. exact (@lem1390571 (term74 _24552 _24553) (term277 _24552) (term277 _24553)). Qed.
Lemma lem1390588 (_24552 : real) (_24553 : real) : (term276 _24552 _24553) = (term309 _24552 _24553).
Proof. exact (TRANS (@lem1390567 _24552 _24553) (@lem1390572 _24552 _24553)). Qed.
Lemma lem1390589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390590 (_24552 : real) (_24553 : real) : (term310 _24552 _24553) = (term311 _24552 _24553).
Proof. exact (MK_COMB (@lem1390589) (@lem1390588 _24552 _24553)). Qed.
Lemma lem1390606 (_24552 : real) (_24553 : real) : (term309 _24552 _24553) = (term309 _24552 _24553).
Proof. exact (eq_refl (term309 _24552 _24553)). Qed.
Lemma lem1390607 (_24552 : real) (_24553 : real) : ((term276 _24552 _24553) = (term309 _24552 _24553)) = ((term309 _24552 _24553) = (term309 _24552 _24553)).
Proof. exact (MK_COMB (@lem1390590 _24552 _24553) (@lem1390606 _24552 _24553)). Qed.
Lemma lem1390609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1390610 (x : Prop) : (x = x) = True.
Proof. exact (@lem1390609 Prop x). Qed.
Lemma lem1390611 (_24552 : real) (_24553 : real) : ((term309 _24552 _24553) = (term309 _24552 _24553)) = True.
Proof. exact (@lem1390610 (term309 _24552 _24553)). Qed.
Lemma lem1390612 (_24552 : real) (_24553 : real) : ((term276 _24552 _24553) = (term309 _24552 _24553)) = True.
Proof. exact (TRANS (@lem1390607 _24552 _24553) (@lem1390611 _24552 _24553)). Qed.
Lemma lem1390613 (_24552 : real) (_24553 : real) : True = ((term276 _24552 _24553) = (term309 _24552 _24553)).
Proof. exact (SYM (@lem1390612 _24552 _24553)). Qed.
Lemma lem1390614 (_24552 : real) (_24553 : real) : (term276 _24552 _24553) = (term309 _24552 _24553).
Proof. exact (EQ_MP (@lem1390613 _24552 _24553) (@lem0)). Qed.
Lemma lem1390615 (_24552 : real) (_24553 : real) (h1 : term237) : term309 _24552 _24553.
Proof. exact (EQ_MP (@lem1390614 _24552 _24553) (@lem1389739 _24552 _24553 h1)). Qed.
Lemma lem1390617 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1390618 (_24552 : real) (_24553 : real) : (term309 _24552 _24553) = (term313 _24552 _24553).
Proof. exact (@lem1390617 (term265 _24552 _24553) (term74 _24552 _24553)). Qed.
Lemma lem1390620 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1390621 (_24552 : real) (_24553 : real) : (term316 _24552 _24553) = (term317 _24552 _24553).
Proof. exact (@lem1390620 (term277 _24552) (term277 _24553)). Qed.
Lemma lem1390623 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1390624 (_24552 : real) : (term319 _24552) = (term70 _24552).
Proof. exact (@lem1390623 (term70 _24552)). Qed.
Lemma lem1390625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1390626 (_24552 : real) : (term320 _24552) = (term134 _24552).
Proof. exact (MK_COMB (@lem1390625) (@lem1390624 _24552)). Qed.
Lemma lem1390628 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1390629 (_24553 : real) : (term319 _24553) = (term70 _24553).
Proof. exact (@lem1390628 (term70 _24553)). Qed.
Lemma lem1390630 (_24552 : real) (_24553 : real) : (term317 _24552 _24553) = (term164 _24552 _24553).
Proof. exact (MK_COMB (@lem1390626 _24552) (@lem1390629 _24553)). Qed.
Lemma lem1390631 (_24552 : real) (_24553 : real) : (term316 _24552 _24553) = (term164 _24552 _24553).
Proof. exact (TRANS (@lem1390621 _24552 _24553) (@lem1390630 _24552 _24553)). Qed.
Lemma lem1390632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1390633 (_24552 : real) (_24553 : real) : (term321 _24552 _24553) = (term322 _24552 _24553).
Proof. exact (MK_COMB (@lem1390632) (@lem1390631 _24552 _24553)). Qed.
Lemma lem1390634 (_24552 : real) (_24553 : real) : (term74 _24552 _24553) = (term74 _24552 _24553).
Proof. exact (eq_refl (term74 _24552 _24553)). Qed.
Lemma lem1390635 (_24552 : real) (_24553 : real) : (term313 _24552 _24553) = (term170 _24552 _24553).
Proof. exact (MK_COMB (@lem1390633 _24552 _24553) (@lem1390634 _24552 _24553)). Qed.
Lemma lem1390636 (_24552 : real) (_24553 : real) : (term309 _24552 _24553) = (term170 _24552 _24553).
Proof. exact (TRANS (@lem1390618 _24552 _24553) (@lem1390635 _24552 _24553)). Qed.
Lemma lem1390638 (x : real) (y : real) (h1 : term70 x) (h2 : term70 y) : term164 x y.
Proof. exact (conj (@lem1390536 x h1) (@lem1390543 y h2)). Qed.
Lemma lem1390640 (_24552 : real) (_24553 : real) (h1 : term237) : term170 _24552 _24553.
Proof. exact (EQ_MP (@lem1390636 _24552 _24553) (@lem1390615 _24552 _24553 h1)). Qed.
Lemma lem1390641 (x : real) (y : real) (h1 : term237) : term170 x y.
Proof. exact (@lem1390640 x y h1). Qed.
Lemma lem1390644 (x : real) (y : real) (h1 : term237) (h2 : term70 x) (h3 : term70 y) : term74 x y.
Proof. exact (@lem1390641 x y h1 (@lem1390638 x y h2 h3)). Qed.
Lemma lem1390645 (x : real) (y : real) (h1 : term237) (h2 : term70 x) (h3 : term70 y) : term323 x y.
Proof. exact (fun h0 : term278 x y => @lem1390644 x y h1 h2 h3). Qed.
Lemma lem1390647 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390648 (x : real) (y : real) : (term323 x y) = (term74 x y).
Proof. exact (@lem1390647 (term74 x y)). Qed.
Lemma lem1390649 (x : real) (y : real) (h1 : term237) (h2 : term70 x) (h3 : term70 y) : term74 x y.
Proof. exact (EQ_MP (@lem1390648 x y) (@lem1390645 x y h1 h2 h3)). Qed.
Lemma lem1390652 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1390654 (x : real) (y : real) : (term278 x y) = (term324 x y).
Proof. exact (@lem1390652 (term74 x y)). Qed.
Lemma lem1390657 (x : real) (y : real) (h1 : term242 x y) : term324 x y.
Proof. exact (EQ_MP (@lem1390654 x y) (@lem1389745 x y h1)). Qed.
Lemma lem1390660 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (@lem1390657 x y h2 (@lem1390649 x y h1 h3 h4)). Qed.
Lemma lem1390661 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : term325.
Proof. exact (fun h0 : ~ False => @lem1390660 x y h1 h2 h3 h4). Qed.
Lemma lem1390663 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390664 : term325 = False.
Proof. exact (@lem1390663 False). Qed.
Lemma lem1390665 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1390664) (@lem1390661 x y h1 h2 h3 h4)). Qed.
Lemma lem1390666 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1390667 (_24678 : real) (_24680 : real) (h1 : _24678 = _24680) : _24678 = _24680.
Proof. exact (h1). Qed.
Lemma lem1390668 (_24679 : real) (_24681 : real) (h1 : _24679 = _24681) : _24679 = _24681.
Proof. exact (h1). Qed.
Lemma lem1390669 (_24678 : real) (_24680 : real) (h1 : _24678 = _24680) : (real_lt _24678) = (real_lt _24680).
Proof. exact (MK_COMB (@lem1390666) (@lem1390667 _24678 _24680 h1)). Qed.
Lemma lem1390670 (_24678 : real) (_24680 : real) (_24679 : real) (_24681 : real) (h1 : _24678 = _24680) (h2 : _24679 = _24681) : (real_lt _24678 _24679) = (real_lt _24680 _24681).
Proof. exact (MK_COMB (@lem1390669 _24678 _24680 h1) (@lem1390668 _24679 _24681 h2)). Qed.
Lemma lem1390672 (b : Prop) (a : Prop) : term326 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1390673 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : term327 _24680 _24681 _24678 _24679.
Proof. exact (@lem1390672 (real_lt _24680 _24681) (real_lt _24678 _24679)). Qed.
Lemma lem1390674 (_24678 : real) (_24680 : real) (_24679 : real) (_24681 : real) (h1 : _24678 = _24680) (h2 : _24679 = _24681) : term328 _24680 _24681 _24678 _24679.
Proof. exact (@lem1390673 _24680 _24681 _24678 _24679 (@lem1390670 _24678 _24680 _24679 _24681 h1 h2)). Qed.
Lemma lem1390675 (_24681 : real) (_24679 : real) (_24678 : real) (_24680 : real) (h1 : _24678 = _24680) : term329 _24680 _24681 _24678 _24679.
Proof. exact (fun h0 : _24679 = _24681 => @lem1390674 _24678 _24680 _24679 _24681 h1 h0). Qed.
Lemma lem1390677 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1390678 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term329 _24680 _24681 _24678 _24679) = (term331 _24680 _24681 _24678 _24679).
Proof. exact (@lem1390677 (_24679 = _24681) (term328 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390679 (_24681 : real) (_24679 : real) (_24678 : real) (_24680 : real) (h1 : _24678 = _24680) : term331 _24680 _24681 _24678 _24679.
Proof. exact (EQ_MP (@lem1390678 _24680 _24681 _24678 _24679) (@lem1390675 _24681 _24679 _24678 _24680 h1)). Qed.
Lemma lem1390680 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : term332 _24680 _24681 _24678 _24679.
Proof. exact (fun h0 : _24678 = _24680 => @lem1390679 _24681 _24679 _24678 _24680 h0). Qed.
Lemma lem1390682 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1390683 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term332 _24680 _24681 _24678 _24679) = (term333 _24680 _24681 _24678 _24679).
Proof. exact (@lem1390682 (_24678 = _24680) (term331 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390684 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : term333 _24680 _24681 _24678 _24679.
Proof. exact (EQ_MP (@lem1390683 _24680 _24681 _24678 _24679) (@lem1390680 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390717 (x : real) (y : real) (z : real) : term334 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1390721 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1390722 : term26 = term26.
Proof. exact (@lem1390721 term26). Qed.
Lemma lem1390723 : term335.
Proof. exact (fun h0 : term336 => @lem1390722). Qed.
Lemma lem1390725 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390726 : term335 = (term26 = term26).
Proof. exact (@lem1390725 (term26 = term26)). Qed.
Lemma lem1390727 : term26 = term26.
Proof. exact (EQ_MP (@lem1390726) (@lem1390723)). Qed.
Lemma lem1390729 (_24559 : real) (h1 : term214) : (term20 _24559) = _24559.
Proof. exact (EQ_MP (@lem1389642 _24559) (@lem1389641 _24559 h1)). Qed.
Lemma lem1390730 (y : real) (h1 : term214) : (term20 y) = y.
Proof. exact (@lem1390729 y h1). Qed.
Lemma lem1390731 (y : real) (h1 : term214) : term337 y.
Proof. exact (fun h0 : term338 y => @lem1390730 y h1). Qed.
Lemma lem1390733 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390734 (y : real) : (term337 y) = ((term20 y) = y).
Proof. exact (@lem1390733 ((term20 y) = y)). Qed.
Lemma lem1390735 (y : real) (h1 : term214) : (term20 y) = y.
Proof. exact (EQ_MP (@lem1390734 y) (@lem1390731 y h1)). Qed.
Lemma lem1390737 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1390738 (y : real) : (term20 y) = (term20 y).
Proof. exact (@lem1390737 (term20 y)). Qed.
Lemma lem1390739 (y : real) : term339 y.
Proof. exact (fun h0 : term340 y => @lem1390738 y). Qed.
Lemma lem1390741 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390742 (y : real) : (term339 y) = ((term20 y) = (term20 y)).
Proof. exact (@lem1390741 ((term20 y) = (term20 y))). Qed.
Lemma lem1390743 (y : real) : (term20 y) = (term20 y).
Proof. exact (EQ_MP (@lem1390742 y) (@lem1390739 y)). Qed.
Lemma lem1390761 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1390762 (y : real) (x : real) (z : real) : (term341 x y z) = (term342 y x z).
Proof. exact (@lem1390761 (y = z) (term343 x z)). Qed.
Lemma lem1390772 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1390773 (y : real) (x : real) (z : real) : (term334 x y z) = (term345 y x z).
Proof. exact (MK_COMB (@lem1390772 x y) (@lem1390762 y x z)). Qed.
Lemma lem1390777 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1390778 (y : real) (x : real) (z : real) : (term345 y x z) = (term346 y x z).
Proof. exact (@lem1390777 (y = z) (term343 x y) (term343 x z)). Qed.
Lemma lem1390800 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (TRANS (@lem1390773 y x z) (@lem1390778 y x z)). Qed.
Lemma lem1390801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390802 (y : real) (x : real) (z : real) : (term347 x y z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1390801) (@lem1390800 y x z)). Qed.
Lemma lem1390824 (y : real) (x : real) (z : real) : (term346 y x z) = (term346 y x z).
Proof. exact (eq_refl (term346 y x z)). Qed.
Lemma lem1390825 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = ((term346 y x z) = (term346 y x z)).
Proof. exact (MK_COMB (@lem1390802 y x z) (@lem1390824 y x z)). Qed.
Lemma lem1390827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1390828 (x : Prop) : (x = x) = True.
Proof. exact (@lem1390827 Prop x). Qed.
Lemma lem1390829 (y : real) (x : real) (z : real) : ((term346 y x z) = (term346 y x z)) = True.
Proof. exact (@lem1390828 (term346 y x z)). Qed.
Lemma lem1390830 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = True.
Proof. exact (TRANS (@lem1390825 y x z) (@lem1390829 y x z)). Qed.
Lemma lem1390831 (y : real) (x : real) (z : real) : True = ((term334 x y z) = (term346 y x z)).
Proof. exact (SYM (@lem1390830 y x z)). Qed.
Lemma lem1390832 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (EQ_MP (@lem1390831 y x z) (@lem0)). Qed.
Lemma lem1390833 (y : real) (x : real) (z : real) : term346 y x z.
Proof. exact (EQ_MP (@lem1390832 y x z) (@lem1390717 x y z)). Qed.
Lemma lem1390835 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1390836 (x : real) (y : real) (z : real) : (term346 y x z) = (term349 x y z).
Proof. exact (@lem1390835 (term350 y x z) (y = z)). Qed.
Lemma lem1390838 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1390839 (y : real) (x : real) (z : real) : (term351 y x z) = (term352 y x z).
Proof. exact (@lem1390838 (term343 x y) (term343 x z)). Qed.
Lemma lem1390841 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1390842 (x : real) (y : real) : (term353 x y) = (x = y).
Proof. exact (@lem1390841 (x = y)). Qed.
Lemma lem1390843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1390844 (x : real) (y : real) : (term354 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1390843) (@lem1390842 x y)). Qed.
Lemma lem1390846 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1390847 (x : real) (z : real) : (term353 x z) = (x = z).
Proof. exact (@lem1390846 (x = z)). Qed.
Lemma lem1390848 (y : real) (x : real) (z : real) : (term352 y x z) = (term356 y x z).
Proof. exact (MK_COMB (@lem1390844 x y) (@lem1390847 x z)). Qed.
Lemma lem1390849 (y : real) (x : real) (z : real) : (term351 y x z) = (term356 y x z).
Proof. exact (TRANS (@lem1390839 y x z) (@lem1390848 y x z)). Qed.
Lemma lem1390850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1390851 (y : real) (x : real) (z : real) : (term357 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1390850) (@lem1390849 y x z)). Qed.
Lemma lem1390852 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1390853 (x : real) (y : real) (z : real) : (term349 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1390851 y x z) (@lem1390852 y z)). Qed.
Lemma lem1390854 (x : real) (y : real) (z : real) : (term346 y x z) = (term359 x y z).
Proof. exact (TRANS (@lem1390836 x y z) (@lem1390853 x y z)). Qed.
Lemma lem1390856 (y : real) (h1 : term214) : term360 y.
Proof. exact (conj (@lem1390735 y h1) (@lem1390743 y)). Qed.
Lemma lem1390858 (x : real) (y : real) (z : real) : term359 x y z.
Proof. exact (EQ_MP (@lem1390854 x y z) (@lem1390833 y x z)). Qed.
Lemma lem1390859 (y : real) : term361 y.
Proof. exact (@lem1390858 (term20 y) y (term20 y)). Qed.
Lemma lem1390862 (y : real) (h1 : term214) : y = (term20 y).
Proof. exact (@lem1390859 y (@lem1390856 y h1)). Qed.
Lemma lem1390863 (y : real) (h1 : term214) : term362 y.
Proof. exact (fun h0 : term363 y => @lem1390862 y h1). Qed.
Lemma lem1390865 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390866 (y : real) : (term362 y) = (y = (term20 y)).
Proof. exact (@lem1390865 (y = (term20 y))). Qed.
Lemma lem1390867 (y : real) (h1 : term214) : y = (term20 y).
Proof. exact (EQ_MP (@lem1390866 y) (@lem1390863 y h1)). Qed.
Lemma lem1390869 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1390870 (y : real) (h1 : term70 y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1390869 y h1). Qed.
Lemma lem1390872 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1390873 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1390872 (term70 y)). Qed.
Lemma lem1390874 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (EQ_MP (@lem1390873 y) (@lem1390870 y h1)). Qed.
Lemma lem1390892 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1390893 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term331 _24680 _24681 _24678 _24679) = (term364 _24680 _24681 _24678 _24679).
Proof. exact (@lem1390892 (real_lt _24680 _24681) (term343 _24679 _24681) (term365 _24678 _24679)). Qed.
Lemma lem1390911 (_24678 : real) (_24680 : real) : (term344 _24678 _24680) = (term344 _24678 _24680).
Proof. exact (eq_refl (term344 _24678 _24680)). Qed.
Lemma lem1390912 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term333 _24680 _24681 _24678 _24679) = (term366 _24680 _24681 _24678 _24679).
Proof. exact (MK_COMB (@lem1390911 _24678 _24680) (@lem1390893 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390916 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1390917 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term366 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679).
Proof. exact (@lem1390916 (real_lt _24680 _24681) (term343 _24678 _24680) (term368 _24681 _24678 _24679)). Qed.
Lemma lem1390947 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term333 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679).
Proof. exact (TRANS (@lem1390912 _24680 _24681 _24678 _24679) (@lem1390917 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1390949 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term369 _24680 _24681 _24678 _24679) = (term370 _24680 _24681 _24678 _24679).
Proof. exact (MK_COMB (@lem1390948) (@lem1390947 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390979 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term367 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679).
Proof. exact (eq_refl (term367 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390980 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : ((term333 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679)) = ((term367 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679)).
Proof. exact (MK_COMB (@lem1390949 _24680 _24681 _24678 _24679) (@lem1390979 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1390983 (x : Prop) : (x = x) = True.
Proof. exact (@lem1390982 Prop x). Qed.
Lemma lem1390984 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : ((term367 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679)) = True.
Proof. exact (@lem1390983 (term367 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390985 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : ((term333 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679)) = True.
Proof. exact (TRANS (@lem1390980 _24680 _24681 _24678 _24679) (@lem1390984 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390986 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : True = ((term333 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679)).
Proof. exact (SYM (@lem1390985 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390987 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term333 _24680 _24681 _24678 _24679) = (term367 _24680 _24681 _24678 _24679).
Proof. exact (EQ_MP (@lem1390986 _24680 _24681 _24678 _24679) (@lem0)). Qed.
Lemma lem1390988 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : term367 _24680 _24681 _24678 _24679.
Proof. exact (EQ_MP (@lem1390987 _24680 _24681 _24678 _24679) (@lem1390684 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1390990 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1390991 (_24678 : real) (_24679 : real) (_24680 : real) (_24681 : real) : (term367 _24680 _24681 _24678 _24679) = (term371 _24678 _24679 _24680 _24681).
Proof. exact (@lem1390990 (term372 _24680 _24681 _24678 _24679) (real_lt _24680 _24681)). Qed.
Lemma lem1390993 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1390994 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term373 _24680 _24681 _24678 _24679) = (term374 _24680 _24681 _24678 _24679).
Proof. exact (@lem1390993 (term343 _24678 _24680) (term368 _24681 _24678 _24679)). Qed.
Lemma lem1390996 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1390997 (_24678 : real) (_24680 : real) : (term353 _24678 _24680) = (_24678 = _24680).
Proof. exact (@lem1390996 (_24678 = _24680)). Qed.
Lemma lem1390998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1390999 (_24678 : real) (_24680 : real) : (term354 _24678 _24680) = (term355 _24678 _24680).
Proof. exact (MK_COMB (@lem1390998) (@lem1390997 _24678 _24680)). Qed.
Lemma lem1391001 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391002 (_24681 : real) (_24678 : real) (_24679 : real) : (term375 _24681 _24678 _24679) = (term376 _24681 _24678 _24679).
Proof. exact (@lem1391001 (term343 _24679 _24681) (term365 _24678 _24679)). Qed.
Lemma lem1391004 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391005 (_24679 : real) (_24681 : real) : (term353 _24679 _24681) = (_24679 = _24681).
Proof. exact (@lem1391004 (_24679 = _24681)). Qed.
Lemma lem1391006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391007 (_24679 : real) (_24681 : real) : (term354 _24679 _24681) = (term355 _24679 _24681).
Proof. exact (MK_COMB (@lem1391006) (@lem1391005 _24679 _24681)). Qed.
Lemma lem1391009 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391010 (_24678 : real) (_24679 : real) : (term377 _24678 _24679) = (real_lt _24678 _24679).
Proof. exact (@lem1391009 (real_lt _24678 _24679)). Qed.
Lemma lem1391011 (_24681 : real) (_24678 : real) (_24679 : real) : (term376 _24681 _24678 _24679) = (term378 _24681 _24678 _24679).
Proof. exact (MK_COMB (@lem1391007 _24679 _24681) (@lem1391010 _24678 _24679)). Qed.
Lemma lem1391012 (_24681 : real) (_24678 : real) (_24679 : real) : (term375 _24681 _24678 _24679) = (term378 _24681 _24678 _24679).
Proof. exact (TRANS (@lem1391002 _24681 _24678 _24679) (@lem1391011 _24681 _24678 _24679)). Qed.
Lemma lem1391013 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term374 _24680 _24681 _24678 _24679) = (term379 _24680 _24681 _24678 _24679).
Proof. exact (MK_COMB (@lem1390999 _24678 _24680) (@lem1391012 _24681 _24678 _24679)). Qed.
Lemma lem1391014 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term373 _24680 _24681 _24678 _24679) = (term379 _24680 _24681 _24678 _24679).
Proof. exact (TRANS (@lem1390994 _24680 _24681 _24678 _24679) (@lem1391013 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1391015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1391016 (_24680 : real) (_24681 : real) (_24678 : real) (_24679 : real) : (term380 _24680 _24681 _24678 _24679) = (term381 _24680 _24681 _24678 _24679).
Proof. exact (MK_COMB (@lem1391015) (@lem1391014 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1391017 (_24680 : real) (_24681 : real) : (real_lt _24680 _24681) = (real_lt _24680 _24681).
Proof. exact (eq_refl (real_lt _24680 _24681)). Qed.
Lemma lem1391018 (_24678 : real) (_24679 : real) (_24680 : real) (_24681 : real) : (term371 _24678 _24679 _24680 _24681) = (term382 _24678 _24679 _24680 _24681).
Proof. exact (MK_COMB (@lem1391016 _24680 _24681 _24678 _24679) (@lem1391017 _24680 _24681)). Qed.
Lemma lem1391019 (_24678 : real) (_24679 : real) (_24680 : real) (_24681 : real) : (term367 _24680 _24681 _24678 _24679) = (term382 _24678 _24679 _24680 _24681).
Proof. exact (TRANS (@lem1390991 _24678 _24679 _24680 _24681) (@lem1391018 _24678 _24679 _24680 _24681)). Qed.
Lemma lem1391021 (y : real) (h1 : term214) (h2 : term70 y) : term383 y.
Proof. exact (conj (@lem1390867 y h1) (@lem1390874 y h2)). Qed.
Lemma lem1391022 (y : real) (h1 : term214) (h2 : term70 y) : term384 y.
Proof. exact (conj (@lem1390727) (@lem1391021 y h1 h2)). Qed.
Lemma lem1391024 (_24678 : real) (_24679 : real) (_24680 : real) (_24681 : real) : term382 _24678 _24679 _24680 _24681.
Proof. exact (EQ_MP (@lem1391019 _24678 _24679 _24680 _24681) (@lem1390988 _24680 _24681 _24678 _24679)). Qed.
Lemma lem1391025 (y : real) : term385 y.
Proof. exact (@lem1391024 term26 y term26 (term20 y)). Qed.
Lemma lem1391028 (y : real) (h1 : term214) (h2 : term70 y) : term386 y.
Proof. exact (@lem1391025 y (@lem1391022 y h1 h2)). Qed.
Lemma lem1391029 (y : real) (h1 : term214) (h2 : term70 y) : term387 y.
Proof. exact (fun h0 : term283 y => @lem1391028 y h1 h2). Qed.
Lemma lem1391031 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391032 (y : real) : (term387 y) = (term386 y).
Proof. exact (@lem1391031 (term386 y)). Qed.
Lemma lem1391033 (y : real) (h1 : term214) (h2 : term70 y) : term386 y.
Proof. exact (EQ_MP (@lem1391032 y) (@lem1391029 y h1 h2)). Qed.
Lemma lem1391036 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1391038 (y : real) : (term283 y) = (term388 y).
Proof. exact (@lem1391036 (term386 y)). Qed.
Lemma lem1391041 (y : real) (x : real) (h1 : term242 x y) (h2 : term26 = x) : term388 y.
Proof. exact (EQ_MP (@lem1391038 y) (@lem1390003 y x h1 h2)). Qed.
Lemma lem1391044 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (@lem1391041 y x h2 h3 (@lem1391033 y h1 h4)). Qed.
Lemma lem1391045 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : term325.
Proof. exact (fun h0 : ~ False => @lem1391044 x y h1 h2 h3 h4). Qed.
Lemma lem1391047 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391048 : term325 = False.
Proof. exact (@lem1391047 False). Qed.
Lemma lem1391049 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1391048) (@lem1391045 x y h1 h2 h3 h4)). Qed.
Lemma lem1391050 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1391051 (_24690 : real) (_24692 : real) (h1 : _24690 = _24692) : _24690 = _24692.
Proof. exact (h1). Qed.
Lemma lem1391052 (_24691 : real) (_24693 : real) (h1 : _24691 = _24693) : _24691 = _24693.
Proof. exact (h1). Qed.
Lemma lem1391053 (_24690 : real) (_24692 : real) (h1 : _24690 = _24692) : (real_lt _24690) = (real_lt _24692).
Proof. exact (MK_COMB (@lem1391050) (@lem1391051 _24690 _24692 h1)). Qed.
Lemma lem1391054 (_24690 : real) (_24692 : real) (_24691 : real) (_24693 : real) (h1 : _24690 = _24692) (h2 : _24691 = _24693) : (real_lt _24690 _24691) = (real_lt _24692 _24693).
Proof. exact (MK_COMB (@lem1391053 _24690 _24692 h1) (@lem1391052 _24691 _24693 h2)). Qed.
Lemma lem1391056 (b : Prop) (a : Prop) : term326 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1391057 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : term327 _24692 _24693 _24690 _24691.
Proof. exact (@lem1391056 (real_lt _24692 _24693) (real_lt _24690 _24691)). Qed.
Lemma lem1391058 (_24690 : real) (_24692 : real) (_24691 : real) (_24693 : real) (h1 : _24690 = _24692) (h2 : _24691 = _24693) : term328 _24692 _24693 _24690 _24691.
Proof. exact (@lem1391057 _24692 _24693 _24690 _24691 (@lem1391054 _24690 _24692 _24691 _24693 h1 h2)). Qed.
Lemma lem1391059 (_24693 : real) (_24691 : real) (_24690 : real) (_24692 : real) (h1 : _24690 = _24692) : term329 _24692 _24693 _24690 _24691.
Proof. exact (fun h0 : _24691 = _24693 => @lem1391058 _24690 _24692 _24691 _24693 h1 h0). Qed.
Lemma lem1391061 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1391062 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term329 _24692 _24693 _24690 _24691) = (term331 _24692 _24693 _24690 _24691).
Proof. exact (@lem1391061 (_24691 = _24693) (term328 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391063 (_24693 : real) (_24691 : real) (_24690 : real) (_24692 : real) (h1 : _24690 = _24692) : term331 _24692 _24693 _24690 _24691.
Proof. exact (EQ_MP (@lem1391062 _24692 _24693 _24690 _24691) (@lem1391059 _24693 _24691 _24690 _24692 h1)). Qed.
Lemma lem1391064 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : term332 _24692 _24693 _24690 _24691.
Proof. exact (fun h0 : _24690 = _24692 => @lem1391063 _24693 _24691 _24690 _24692 h0). Qed.
Lemma lem1391066 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1391067 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term332 _24692 _24693 _24690 _24691) = (term333 _24692 _24693 _24690 _24691).
Proof. exact (@lem1391066 (_24690 = _24692) (term331 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391068 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : term333 _24692 _24693 _24690 _24691.
Proof. exact (EQ_MP (@lem1391067 _24692 _24693 _24690 _24691) (@lem1391064 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391101 (x : real) (y : real) (z : real) : term334 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1391105 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1391106 : term26 = term26.
Proof. exact (@lem1391105 term26). Qed.
Lemma lem1391107 : term335.
Proof. exact (fun h0 : term336 => @lem1391106). Qed.
Lemma lem1391109 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391110 : term335 = (term26 = term26).
Proof. exact (@lem1391109 (term26 = term26)). Qed.
Lemma lem1391111 : term26 = term26.
Proof. exact (EQ_MP (@lem1391110) (@lem1391107)). Qed.
Lemma lem1391113 (_24562 : real) (h1 : term233) : (term18 _24562) = _24562.
Proof. exact (EQ_MP (@lem1389651 _24562) (@lem1389650 _24562 h1)). Qed.
Lemma lem1391114 (x : real) (h1 : term233) : (term18 x) = x.
Proof. exact (@lem1391113 x h1). Qed.
Lemma lem1391115 (x : real) (h1 : term233) : term389 x.
Proof. exact (fun h0 : term390 x => @lem1391114 x h1). Qed.
Lemma lem1391117 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391118 (x : real) : (term389 x) = ((term18 x) = x).
Proof. exact (@lem1391117 ((term18 x) = x)). Qed.
Lemma lem1391119 (x : real) (h1 : term233) : (term18 x) = x.
Proof. exact (EQ_MP (@lem1391118 x) (@lem1391115 x h1)). Qed.
Lemma lem1391121 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1391122 (x : real) : (term18 x) = (term18 x).
Proof. exact (@lem1391121 (term18 x)). Qed.
Lemma lem1391123 (x : real) : term391 x.
Proof. exact (fun h0 : term392 x => @lem1391122 x). Qed.
Lemma lem1391125 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391126 (x : real) : (term391 x) = ((term18 x) = (term18 x)).
Proof. exact (@lem1391125 ((term18 x) = (term18 x))). Qed.
Lemma lem1391127 (x : real) : (term18 x) = (term18 x).
Proof. exact (EQ_MP (@lem1391126 x) (@lem1391123 x)). Qed.
Lemma lem1391145 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1391146 (y : real) (x : real) (z : real) : (term341 x y z) = (term342 y x z).
Proof. exact (@lem1391145 (y = z) (term343 x z)). Qed.
Lemma lem1391156 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1391157 (y : real) (x : real) (z : real) : (term334 x y z) = (term345 y x z).
Proof. exact (MK_COMB (@lem1391156 x y) (@lem1391146 y x z)). Qed.
Lemma lem1391161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391162 (y : real) (x : real) (z : real) : (term345 y x z) = (term346 y x z).
Proof. exact (@lem1391161 (y = z) (term343 x y) (term343 x z)). Qed.
Lemma lem1391184 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (TRANS (@lem1391157 y x z) (@lem1391162 y x z)). Qed.
Lemma lem1391185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1391186 (y : real) (x : real) (z : real) : (term347 x y z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1391185) (@lem1391184 y x z)). Qed.
Lemma lem1391208 (y : real) (x : real) (z : real) : (term346 y x z) = (term346 y x z).
Proof. exact (eq_refl (term346 y x z)). Qed.
Lemma lem1391209 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = ((term346 y x z) = (term346 y x z)).
Proof. exact (MK_COMB (@lem1391186 y x z) (@lem1391208 y x z)). Qed.
Lemma lem1391211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1391212 (x : Prop) : (x = x) = True.
Proof. exact (@lem1391211 Prop x). Qed.
Lemma lem1391213 (y : real) (x : real) (z : real) : ((term346 y x z) = (term346 y x z)) = True.
Proof. exact (@lem1391212 (term346 y x z)). Qed.
Lemma lem1391214 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = True.
Proof. exact (TRANS (@lem1391209 y x z) (@lem1391213 y x z)). Qed.
Lemma lem1391215 (y : real) (x : real) (z : real) : True = ((term334 x y z) = (term346 y x z)).
Proof. exact (SYM (@lem1391214 y x z)). Qed.
Lemma lem1391216 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (EQ_MP (@lem1391215 y x z) (@lem0)). Qed.
Lemma lem1391217 (y : real) (x : real) (z : real) : term346 y x z.
Proof. exact (EQ_MP (@lem1391216 y x z) (@lem1391101 x y z)). Qed.
Lemma lem1391219 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1391220 (x : real) (y : real) (z : real) : (term346 y x z) = (term349 x y z).
Proof. exact (@lem1391219 (term350 y x z) (y = z)). Qed.
Lemma lem1391222 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391223 (y : real) (x : real) (z : real) : (term351 y x z) = (term352 y x z).
Proof. exact (@lem1391222 (term343 x y) (term343 x z)). Qed.
Lemma lem1391225 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391226 (x : real) (y : real) : (term353 x y) = (x = y).
Proof. exact (@lem1391225 (x = y)). Qed.
Lemma lem1391227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391228 (x : real) (y : real) : (term354 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1391227) (@lem1391226 x y)). Qed.
Lemma lem1391230 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391231 (x : real) (z : real) : (term353 x z) = (x = z).
Proof. exact (@lem1391230 (x = z)). Qed.
Lemma lem1391232 (y : real) (x : real) (z : real) : (term352 y x z) = (term356 y x z).
Proof. exact (MK_COMB (@lem1391228 x y) (@lem1391231 x z)). Qed.
Lemma lem1391233 (y : real) (x : real) (z : real) : (term351 y x z) = (term356 y x z).
Proof. exact (TRANS (@lem1391223 y x z) (@lem1391232 y x z)). Qed.
Lemma lem1391234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1391235 (y : real) (x : real) (z : real) : (term357 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1391234) (@lem1391233 y x z)). Qed.
Lemma lem1391236 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1391237 (x : real) (y : real) (z : real) : (term349 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1391235 y x z) (@lem1391236 y z)). Qed.
Lemma lem1391238 (x : real) (y : real) (z : real) : (term346 y x z) = (term359 x y z).
Proof. exact (TRANS (@lem1391220 x y z) (@lem1391237 x y z)). Qed.
Lemma lem1391240 (x : real) (h1 : term233) : term393 x.
Proof. exact (conj (@lem1391119 x h1) (@lem1391127 x)). Qed.
Lemma lem1391242 (x : real) (y : real) (z : real) : term359 x y z.
Proof. exact (EQ_MP (@lem1391238 x y z) (@lem1391217 y x z)). Qed.
Lemma lem1391243 (x : real) : term394 x.
Proof. exact (@lem1391242 (term18 x) x (term18 x)). Qed.
Lemma lem1391246 (x : real) (h1 : term233) : x = (term18 x).
Proof. exact (@lem1391243 x (@lem1391240 x h1)). Qed.
Lemma lem1391247 (x : real) (h1 : term233) : term395 x.
Proof. exact (fun h0 : term396 x => @lem1391246 x h1). Qed.
Lemma lem1391249 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391250 (x : real) : (term395 x) = (x = (term18 x)).
Proof. exact (@lem1391249 (x = (term18 x))). Qed.
Lemma lem1391251 (x : real) (h1 : term233) : x = (term18 x).
Proof. exact (EQ_MP (@lem1391250 x) (@lem1391247 x h1)). Qed.
Lemma lem1391253 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1391254 (x : real) (h1 : term70 x) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1391253 x h1). Qed.
Lemma lem1391256 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391257 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1391256 (term70 x)). Qed.
Lemma lem1391258 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (EQ_MP (@lem1391257 x) (@lem1391254 x h1)). Qed.
Lemma lem1391276 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391277 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term331 _24692 _24693 _24690 _24691) = (term364 _24692 _24693 _24690 _24691).
Proof. exact (@lem1391276 (real_lt _24692 _24693) (term343 _24691 _24693) (term365 _24690 _24691)). Qed.
Lemma lem1391295 (_24690 : real) (_24692 : real) : (term344 _24690 _24692) = (term344 _24690 _24692).
Proof. exact (eq_refl (term344 _24690 _24692)). Qed.
Lemma lem1391296 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term333 _24692 _24693 _24690 _24691) = (term366 _24692 _24693 _24690 _24691).
Proof. exact (MK_COMB (@lem1391295 _24690 _24692) (@lem1391277 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391300 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391301 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term366 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691).
Proof. exact (@lem1391300 (real_lt _24692 _24693) (term343 _24690 _24692) (term368 _24693 _24690 _24691)). Qed.
Lemma lem1391331 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term333 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691).
Proof. exact (TRANS (@lem1391296 _24692 _24693 _24690 _24691) (@lem1391301 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1391333 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term369 _24692 _24693 _24690 _24691) = (term370 _24692 _24693 _24690 _24691).
Proof. exact (MK_COMB (@lem1391332) (@lem1391331 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391363 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term367 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691).
Proof. exact (eq_refl (term367 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391364 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : ((term333 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691)) = ((term367 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691)).
Proof. exact (MK_COMB (@lem1391333 _24692 _24693 _24690 _24691) (@lem1391363 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391366 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1391367 (x : Prop) : (x = x) = True.
Proof. exact (@lem1391366 Prop x). Qed.
Lemma lem1391368 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : ((term367 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691)) = True.
Proof. exact (@lem1391367 (term367 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391369 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : ((term333 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691)) = True.
Proof. exact (TRANS (@lem1391364 _24692 _24693 _24690 _24691) (@lem1391368 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391370 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : True = ((term333 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691)).
Proof. exact (SYM (@lem1391369 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391371 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term333 _24692 _24693 _24690 _24691) = (term367 _24692 _24693 _24690 _24691).
Proof. exact (EQ_MP (@lem1391370 _24692 _24693 _24690 _24691) (@lem0)). Qed.
Lemma lem1391372 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : term367 _24692 _24693 _24690 _24691.
Proof. exact (EQ_MP (@lem1391371 _24692 _24693 _24690 _24691) (@lem1391068 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391374 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1391375 (_24690 : real) (_24691 : real) (_24692 : real) (_24693 : real) : (term367 _24692 _24693 _24690 _24691) = (term371 _24690 _24691 _24692 _24693).
Proof. exact (@lem1391374 (term372 _24692 _24693 _24690 _24691) (real_lt _24692 _24693)). Qed.
Lemma lem1391377 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391378 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term373 _24692 _24693 _24690 _24691) = (term374 _24692 _24693 _24690 _24691).
Proof. exact (@lem1391377 (term343 _24690 _24692) (term368 _24693 _24690 _24691)). Qed.
Lemma lem1391380 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391381 (_24690 : real) (_24692 : real) : (term353 _24690 _24692) = (_24690 = _24692).
Proof. exact (@lem1391380 (_24690 = _24692)). Qed.
Lemma lem1391382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391383 (_24690 : real) (_24692 : real) : (term354 _24690 _24692) = (term355 _24690 _24692).
Proof. exact (MK_COMB (@lem1391382) (@lem1391381 _24690 _24692)). Qed.
Lemma lem1391385 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391386 (_24693 : real) (_24690 : real) (_24691 : real) : (term375 _24693 _24690 _24691) = (term376 _24693 _24690 _24691).
Proof. exact (@lem1391385 (term343 _24691 _24693) (term365 _24690 _24691)). Qed.
Lemma lem1391388 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391389 (_24691 : real) (_24693 : real) : (term353 _24691 _24693) = (_24691 = _24693).
Proof. exact (@lem1391388 (_24691 = _24693)). Qed.
Lemma lem1391390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391391 (_24691 : real) (_24693 : real) : (term354 _24691 _24693) = (term355 _24691 _24693).
Proof. exact (MK_COMB (@lem1391390) (@lem1391389 _24691 _24693)). Qed.
Lemma lem1391393 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391394 (_24690 : real) (_24691 : real) : (term377 _24690 _24691) = (real_lt _24690 _24691).
Proof. exact (@lem1391393 (real_lt _24690 _24691)). Qed.
Lemma lem1391395 (_24693 : real) (_24690 : real) (_24691 : real) : (term376 _24693 _24690 _24691) = (term378 _24693 _24690 _24691).
Proof. exact (MK_COMB (@lem1391391 _24691 _24693) (@lem1391394 _24690 _24691)). Qed.
Lemma lem1391396 (_24693 : real) (_24690 : real) (_24691 : real) : (term375 _24693 _24690 _24691) = (term378 _24693 _24690 _24691).
Proof. exact (TRANS (@lem1391386 _24693 _24690 _24691) (@lem1391395 _24693 _24690 _24691)). Qed.
Lemma lem1391397 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term374 _24692 _24693 _24690 _24691) = (term379 _24692 _24693 _24690 _24691).
Proof. exact (MK_COMB (@lem1391383 _24690 _24692) (@lem1391396 _24693 _24690 _24691)). Qed.
Lemma lem1391398 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term373 _24692 _24693 _24690 _24691) = (term379 _24692 _24693 _24690 _24691).
Proof. exact (TRANS (@lem1391378 _24692 _24693 _24690 _24691) (@lem1391397 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391399 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1391400 (_24692 : real) (_24693 : real) (_24690 : real) (_24691 : real) : (term380 _24692 _24693 _24690 _24691) = (term381 _24692 _24693 _24690 _24691).
Proof. exact (MK_COMB (@lem1391399) (@lem1391398 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391401 (_24692 : real) (_24693 : real) : (real_lt _24692 _24693) = (real_lt _24692 _24693).
Proof. exact (eq_refl (real_lt _24692 _24693)). Qed.
Lemma lem1391402 (_24690 : real) (_24691 : real) (_24692 : real) (_24693 : real) : (term371 _24690 _24691 _24692 _24693) = (term382 _24690 _24691 _24692 _24693).
Proof. exact (MK_COMB (@lem1391400 _24692 _24693 _24690 _24691) (@lem1391401 _24692 _24693)). Qed.
Lemma lem1391403 (_24690 : real) (_24691 : real) (_24692 : real) (_24693 : real) : (term367 _24692 _24693 _24690 _24691) = (term382 _24690 _24691 _24692 _24693).
Proof. exact (TRANS (@lem1391375 _24690 _24691 _24692 _24693) (@lem1391402 _24690 _24691 _24692 _24693)). Qed.
Lemma lem1391405 (x : real) (h1 : term233) (h2 : term70 x) : term397 x.
Proof. exact (conj (@lem1391251 x h1) (@lem1391258 x h2)). Qed.
Lemma lem1391406 (x : real) (h1 : term233) (h2 : term70 x) : term398 x.
Proof. exact (conj (@lem1391111) (@lem1391405 x h1 h2)). Qed.
Lemma lem1391408 (_24690 : real) (_24691 : real) (_24692 : real) (_24693 : real) : term382 _24690 _24691 _24692 _24693.
Proof. exact (EQ_MP (@lem1391403 _24690 _24691 _24692 _24693) (@lem1391372 _24692 _24693 _24690 _24691)). Qed.
Lemma lem1391409 (x : real) : term399 x.
Proof. exact (@lem1391408 term26 x term26 (term18 x)). Qed.
Lemma lem1391412 (x : real) (h1 : term233) (h2 : term70 x) : term400 x.
Proof. exact (@lem1391409 x (@lem1391406 x h1 h2)). Qed.
Lemma lem1391413 (x : real) (h1 : term233) (h2 : term70 x) : term401 x.
Proof. exact (fun h0 : term289 x => @lem1391412 x h1 h2). Qed.
Lemma lem1391415 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391416 (x : real) : (term401 x) = (term400 x).
Proof. exact (@lem1391415 (term400 x)). Qed.
Lemma lem1391417 (x : real) (h1 : term233) (h2 : term70 x) : term400 x.
Proof. exact (EQ_MP (@lem1391416 x) (@lem1391413 x h1 h2)). Qed.
Lemma lem1391420 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1391422 (x : real) : (term289 x) = (term402 x).
Proof. exact (@lem1391420 (term400 x)). Qed.
Lemma lem1391425 (x : real) (y : real) (h1 : term242 x y) (h2 : term26 = y) : term402 x.
Proof. exact (EQ_MP (@lem1391422 x) (@lem1390100 x y h1 h2)). Qed.
Lemma lem1391428 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (@lem1391425 x y h2 h3 (@lem1391417 x h1 h4)). Qed.
Lemma lem1391429 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : term325.
Proof. exact (fun h0 : ~ False => @lem1391428 y x h1 h2 h3 h4). Qed.
Lemma lem1391431 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391432 : term325 = False.
Proof. exact (@lem1391431 False). Qed.
Lemma lem1391433 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1391432) (@lem1391429 y x h1 h2 h3 h4)). Qed.
Lemma lem1391485 (x : real) (y : real) (z : real) : term334 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1391489 (_24567 : real) (h1 : term214) : (term20 _24567) = _24567.
Proof. exact (EQ_MP (@lem1389666 _24567) (@lem1389665 _24567 h1)). Qed.
Lemma lem1391490 (h1 : term214) : term34 = term26.
Proof. exact (@lem1391489 term26 h1). Qed.
Lemma lem1391491 (h1 : term214) : term403.
Proof. exact (fun h0 : term404 => @lem1391490 h1). Qed.
Lemma lem1391493 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391494 : term403 = (term34 = term26).
Proof. exact (@lem1391493 (term34 = term26)). Qed.
Lemma lem1391495 (h1 : term214) : term34 = term26.
Proof. exact (EQ_MP (@lem1391494) (@lem1391491 h1)). Qed.
Lemma lem1391497 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1391498 : term34 = term34.
Proof. exact (@lem1391497 term34). Qed.
Lemma lem1391499 : term405.
Proof. exact (fun h0 : term406 => @lem1391498). Qed.
Lemma lem1391501 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391502 : term405 = (term34 = term34).
Proof. exact (@lem1391501 (term34 = term34)). Qed.
Lemma lem1391503 : term34 = term34.
Proof. exact (EQ_MP (@lem1391502) (@lem1391499)). Qed.
Lemma lem1391521 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1391522 (y : real) (x : real) (z : real) : (term341 x y z) = (term342 y x z).
Proof. exact (@lem1391521 (y = z) (term343 x z)). Qed.
Lemma lem1391532 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1391533 (y : real) (x : real) (z : real) : (term334 x y z) = (term345 y x z).
Proof. exact (MK_COMB (@lem1391532 x y) (@lem1391522 y x z)). Qed.
Lemma lem1391537 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391538 (y : real) (x : real) (z : real) : (term345 y x z) = (term346 y x z).
Proof. exact (@lem1391537 (y = z) (term343 x y) (term343 x z)). Qed.
Lemma lem1391560 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (TRANS (@lem1391533 y x z) (@lem1391538 y x z)). Qed.
Lemma lem1391561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1391562 (y : real) (x : real) (z : real) : (term347 x y z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1391561) (@lem1391560 y x z)). Qed.
Lemma lem1391584 (y : real) (x : real) (z : real) : (term346 y x z) = (term346 y x z).
Proof. exact (eq_refl (term346 y x z)). Qed.
Lemma lem1391585 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = ((term346 y x z) = (term346 y x z)).
Proof. exact (MK_COMB (@lem1391562 y x z) (@lem1391584 y x z)). Qed.
Lemma lem1391587 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1391588 (x : Prop) : (x = x) = True.
Proof. exact (@lem1391587 Prop x). Qed.
Lemma lem1391589 (y : real) (x : real) (z : real) : ((term346 y x z) = (term346 y x z)) = True.
Proof. exact (@lem1391588 (term346 y x z)). Qed.
Lemma lem1391590 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = True.
Proof. exact (TRANS (@lem1391585 y x z) (@lem1391589 y x z)). Qed.
Lemma lem1391591 (y : real) (x : real) (z : real) : True = ((term334 x y z) = (term346 y x z)).
Proof. exact (SYM (@lem1391590 y x z)). Qed.
Lemma lem1391592 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (EQ_MP (@lem1391591 y x z) (@lem0)). Qed.
Lemma lem1391593 (y : real) (x : real) (z : real) : term346 y x z.
Proof. exact (EQ_MP (@lem1391592 y x z) (@lem1391485 x y z)). Qed.
Lemma lem1391595 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1391596 (x : real) (y : real) (z : real) : (term346 y x z) = (term349 x y z).
Proof. exact (@lem1391595 (term350 y x z) (y = z)). Qed.
Lemma lem1391598 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391599 (y : real) (x : real) (z : real) : (term351 y x z) = (term352 y x z).
Proof. exact (@lem1391598 (term343 x y) (term343 x z)). Qed.
Lemma lem1391601 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391602 (x : real) (y : real) : (term353 x y) = (x = y).
Proof. exact (@lem1391601 (x = y)). Qed.
Lemma lem1391603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391604 (x : real) (y : real) : (term354 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1391603) (@lem1391602 x y)). Qed.
Lemma lem1391606 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391607 (x : real) (z : real) : (term353 x z) = (x = z).
Proof. exact (@lem1391606 (x = z)). Qed.
Lemma lem1391608 (y : real) (x : real) (z : real) : (term352 y x z) = (term356 y x z).
Proof. exact (MK_COMB (@lem1391604 x y) (@lem1391607 x z)). Qed.
Lemma lem1391609 (y : real) (x : real) (z : real) : (term351 y x z) = (term356 y x z).
Proof. exact (TRANS (@lem1391599 y x z) (@lem1391608 y x z)). Qed.
Lemma lem1391610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1391611 (y : real) (x : real) (z : real) : (term357 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1391610) (@lem1391609 y x z)). Qed.
Lemma lem1391612 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1391613 (x : real) (y : real) (z : real) : (term349 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1391611 y x z) (@lem1391612 y z)). Qed.
Lemma lem1391614 (x : real) (y : real) (z : real) : (term346 y x z) = (term359 x y z).
Proof. exact (TRANS (@lem1391596 x y z) (@lem1391613 x y z)). Qed.
Lemma lem1391616 (h1 : term214) : term407.
Proof. exact (conj (@lem1391495 h1) (@lem1391503)). Qed.
Lemma lem1391618 (x : real) (y : real) (z : real) : term359 x y z.
Proof. exact (EQ_MP (@lem1391614 x y z) (@lem1391593 y x z)). Qed.
Lemma lem1391619 : term408.
Proof. exact (@lem1391618 term34 term26 term34). Qed.
Lemma lem1391622 (h1 : term214) : term26 = term34.
Proof. exact (@lem1391619 (@lem1391616 h1)). Qed.
Lemma lem1391623 (h1 : term214) : term409.
Proof. exact (fun h0 : term300 => @lem1391622 h1). Qed.
Lemma lem1391625 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391626 : term409 = (term26 = term34).
Proof. exact (@lem1391625 (term26 = term34)). Qed.
Lemma lem1391627 (h1 : term214) : term26 = term34.
Proof. exact (EQ_MP (@lem1391626) (@lem1391623 h1)). Qed.
Lemma lem1391630 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1391632 : term300 = term410.
Proof. exact (@lem1391630 (term26 = term34)). Qed.
Lemma lem1391635 (x : real) (y : real) (h1 : term242 x y) (h2 : term26 = x) (h3 : term26 = y) : term410.
Proof. exact (EQ_MP (@lem1391632) (@lem1390307 x y h1 h2 h3)). Qed.
Lemma lem1391638 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (@lem1391635 x y h2 h3 h4 (@lem1391627 h1)). Qed.
Lemma lem1391639 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : term325.
Proof. exact (fun h0 : ~ False => @lem1391638 x y h1 h2 h3 h4). Qed.
Lemma lem1391641 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391642 : term325 = False.
Proof. exact (@lem1391641 False). Qed.
Lemma lem1391699 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1391700 (x : real) (h1 : term70 x) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1391699 x h1). Qed.
Lemma lem1391702 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391703 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1391702 (term70 x)). Qed.
Lemma lem1391704 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (EQ_MP (@lem1391703 x) (@lem1391700 x h1)). Qed.
Lemma lem1391706 (x : real) (y : real) (h1 : term245 x y) : term70 y.
Proof. exact (proj2 (@lem1389155 x y h1)). Qed.
Lemma lem1391707 (x : real) (y : real) (h1 : term245 x y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1391706 x y h1). Qed.
Lemma lem1391709 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391710 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1391709 (term70 y)). Qed.
Lemma lem1391711 (x : real) (y : real) (h1 : term245 x y) : term70 y.
Proof. exact (EQ_MP (@lem1391710 y) (@lem1391707 x y h1)). Qed.
Lemma lem1391727 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1391728 (_24568 : real) (_24569 : real) : (term305 _24568 _24569) = (term306 _24568 _24569).
Proof. exact (@lem1391727 (term74 _24568 _24569) (term277 _24569)). Qed.
Lemma lem1391734 (_24568 : real) : (term307 _24568) = (term307 _24568).
Proof. exact (eq_refl (term307 _24568)). Qed.
Lemma lem1391735 (_24568 : real) (_24569 : real) : (term276 _24568 _24569) = (term308 _24568 _24569).
Proof. exact (MK_COMB (@lem1391734 _24568) (@lem1391728 _24568 _24569)). Qed.
Lemma lem1391739 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391740 (_24568 : real) (_24569 : real) : (term308 _24568 _24569) = (term309 _24568 _24569).
Proof. exact (@lem1391739 (term74 _24568 _24569) (term277 _24568) (term277 _24569)). Qed.
Lemma lem1391756 (_24568 : real) (_24569 : real) : (term276 _24568 _24569) = (term309 _24568 _24569).
Proof. exact (TRANS (@lem1391735 _24568 _24569) (@lem1391740 _24568 _24569)). Qed.
Lemma lem1391757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1391758 (_24568 : real) (_24569 : real) : (term310 _24568 _24569) = (term311 _24568 _24569).
Proof. exact (MK_COMB (@lem1391757) (@lem1391756 _24568 _24569)). Qed.
Lemma lem1391774 (_24568 : real) (_24569 : real) : (term309 _24568 _24569) = (term309 _24568 _24569).
Proof. exact (eq_refl (term309 _24568 _24569)). Qed.
Lemma lem1391775 (_24568 : real) (_24569 : real) : ((term276 _24568 _24569) = (term309 _24568 _24569)) = ((term309 _24568 _24569) = (term309 _24568 _24569)).
Proof. exact (MK_COMB (@lem1391758 _24568 _24569) (@lem1391774 _24568 _24569)). Qed.
Lemma lem1391777 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1391778 (x : Prop) : (x = x) = True.
Proof. exact (@lem1391777 Prop x). Qed.
Lemma lem1391779 (_24568 : real) (_24569 : real) : ((term309 _24568 _24569) = (term309 _24568 _24569)) = True.
Proof. exact (@lem1391778 (term309 _24568 _24569)). Qed.
Lemma lem1391780 (_24568 : real) (_24569 : real) : ((term276 _24568 _24569) = (term309 _24568 _24569)) = True.
Proof. exact (TRANS (@lem1391775 _24568 _24569) (@lem1391779 _24568 _24569)). Qed.
Lemma lem1391781 (_24568 : real) (_24569 : real) : True = ((term276 _24568 _24569) = (term309 _24568 _24569)).
Proof. exact (SYM (@lem1391780 _24568 _24569)). Qed.
Lemma lem1391782 (_24568 : real) (_24569 : real) : (term276 _24568 _24569) = (term309 _24568 _24569).
Proof. exact (EQ_MP (@lem1391781 _24568 _24569) (@lem0)). Qed.
Lemma lem1391783 (_24568 : real) (_24569 : real) (h1 : term237) : term309 _24568 _24569.
Proof. exact (EQ_MP (@lem1391782 _24568 _24569) (@lem1389835 _24568 _24569 h1)). Qed.
Lemma lem1391785 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1391786 (_24568 : real) (_24569 : real) : (term309 _24568 _24569) = (term313 _24568 _24569).
Proof. exact (@lem1391785 (term265 _24568 _24569) (term74 _24568 _24569)). Qed.
Lemma lem1391788 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1391789 (_24568 : real) (_24569 : real) : (term316 _24568 _24569) = (term317 _24568 _24569).
Proof. exact (@lem1391788 (term277 _24568) (term277 _24569)). Qed.
Lemma lem1391791 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391792 (_24568 : real) : (term319 _24568) = (term70 _24568).
Proof. exact (@lem1391791 (term70 _24568)). Qed.
Lemma lem1391793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1391794 (_24568 : real) : (term320 _24568) = (term134 _24568).
Proof. exact (MK_COMB (@lem1391793) (@lem1391792 _24568)). Qed.
Lemma lem1391796 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1391797 (_24569 : real) : (term319 _24569) = (term70 _24569).
Proof. exact (@lem1391796 (term70 _24569)). Qed.
Lemma lem1391798 (_24568 : real) (_24569 : real) : (term317 _24568 _24569) = (term164 _24568 _24569).
Proof. exact (MK_COMB (@lem1391794 _24568) (@lem1391797 _24569)). Qed.
Lemma lem1391799 (_24568 : real) (_24569 : real) : (term316 _24568 _24569) = (term164 _24568 _24569).
Proof. exact (TRANS (@lem1391789 _24568 _24569) (@lem1391798 _24568 _24569)). Qed.
Lemma lem1391800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1391801 (_24568 : real) (_24569 : real) : (term321 _24568 _24569) = (term322 _24568 _24569).
Proof. exact (MK_COMB (@lem1391800) (@lem1391799 _24568 _24569)). Qed.
Lemma lem1391802 (_24568 : real) (_24569 : real) : (term74 _24568 _24569) = (term74 _24568 _24569).
Proof. exact (eq_refl (term74 _24568 _24569)). Qed.
Lemma lem1391803 (_24568 : real) (_24569 : real) : (term313 _24568 _24569) = (term170 _24568 _24569).
Proof. exact (MK_COMB (@lem1391801 _24568 _24569) (@lem1391802 _24568 _24569)). Qed.
Lemma lem1391804 (_24568 : real) (_24569 : real) : (term309 _24568 _24569) = (term170 _24568 _24569).
Proof. exact (TRANS (@lem1391786 _24568 _24569) (@lem1391803 _24568 _24569)). Qed.
Lemma lem1391806 (y : real) (x : real) (h1 : term245 x y) (h2 : term70 x) : term164 x y.
Proof. exact (conj (@lem1391704 x h2) (@lem1391711 x y h1)). Qed.
Lemma lem1391808 (_24568 : real) (_24569 : real) (h1 : term237) : term170 _24568 _24569.
Proof. exact (EQ_MP (@lem1391804 _24568 _24569) (@lem1391783 _24568 _24569 h1)). Qed.
Lemma lem1391809 (x : real) (y : real) (h1 : term237) : term170 x y.
Proof. exact (@lem1391808 x y h1). Qed.
Lemma lem1391812 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : term74 x y.
Proof. exact (@lem1391809 x y h1 (@lem1391806 y x h2 h3)). Qed.
Lemma lem1391813 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : term323 x y.
Proof. exact (fun h0 : term278 x y => @lem1391812 y x h1 h2 h3). Qed.
Lemma lem1391815 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391816 (x : real) (y : real) : (term323 x y) = (term74 x y).
Proof. exact (@lem1391815 (term74 x y)). Qed.
Lemma lem1391817 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : term74 x y.
Proof. exact (EQ_MP (@lem1391816 x y) (@lem1391813 y x h1 h2 h3)). Qed.
Lemma lem1391820 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1391822 (x : real) (y : real) : (term278 x y) = (term324 x y).
Proof. exact (@lem1391820 (term74 x y)). Qed.
Lemma lem1391825 (x : real) (y : real) (h1 : term245 x y) : term324 x y.
Proof. exact (EQ_MP (@lem1391822 x y) (@lem1389841 x y h1)). Qed.
Lemma lem1391828 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : False.
Proof. exact (@lem1391825 x y h2 (@lem1391817 y x h1 h2 h3)). Qed.
Lemma lem1391829 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : term325.
Proof. exact (fun h0 : ~ False => @lem1391828 y x h1 h2 h3). Qed.
Lemma lem1391831 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391832 : term325 = False.
Proof. exact (@lem1391831 False). Qed.
Lemma lem1391833 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : False.
Proof. exact (EQ_MP (@lem1391832) (@lem1391829 y x h1 h2 h3)). Qed.
Lemma lem1391834 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1391835 (_24726 : real) (_24728 : real) (h1 : _24726 = _24728) : _24726 = _24728.
Proof. exact (h1). Qed.
Lemma lem1391836 (_24727 : real) (_24729 : real) (h1 : _24727 = _24729) : _24727 = _24729.
Proof. exact (h1). Qed.
Lemma lem1391837 (_24726 : real) (_24728 : real) (h1 : _24726 = _24728) : (real_lt _24726) = (real_lt _24728).
Proof. exact (MK_COMB (@lem1391834) (@lem1391835 _24726 _24728 h1)). Qed.
Lemma lem1391838 (_24726 : real) (_24728 : real) (_24727 : real) (_24729 : real) (h1 : _24726 = _24728) (h2 : _24727 = _24729) : (real_lt _24726 _24727) = (real_lt _24728 _24729).
Proof. exact (MK_COMB (@lem1391837 _24726 _24728 h1) (@lem1391836 _24727 _24729 h2)). Qed.
Lemma lem1391840 (b : Prop) (a : Prop) : term326 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1391841 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : term327 _24728 _24729 _24726 _24727.
Proof. exact (@lem1391840 (real_lt _24728 _24729) (real_lt _24726 _24727)). Qed.
Lemma lem1391842 (_24726 : real) (_24728 : real) (_24727 : real) (_24729 : real) (h1 : _24726 = _24728) (h2 : _24727 = _24729) : term328 _24728 _24729 _24726 _24727.
Proof. exact (@lem1391841 _24728 _24729 _24726 _24727 (@lem1391838 _24726 _24728 _24727 _24729 h1 h2)). Qed.
Lemma lem1391843 (_24729 : real) (_24727 : real) (_24726 : real) (_24728 : real) (h1 : _24726 = _24728) : term329 _24728 _24729 _24726 _24727.
Proof. exact (fun h0 : _24727 = _24729 => @lem1391842 _24726 _24728 _24727 _24729 h1 h0). Qed.
Lemma lem1391845 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1391846 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term329 _24728 _24729 _24726 _24727) = (term331 _24728 _24729 _24726 _24727).
Proof. exact (@lem1391845 (_24727 = _24729) (term328 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1391847 (_24729 : real) (_24727 : real) (_24726 : real) (_24728 : real) (h1 : _24726 = _24728) : term331 _24728 _24729 _24726 _24727.
Proof. exact (EQ_MP (@lem1391846 _24728 _24729 _24726 _24727) (@lem1391843 _24729 _24727 _24726 _24728 h1)). Qed.
Lemma lem1391848 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : term332 _24728 _24729 _24726 _24727.
Proof. exact (fun h0 : _24726 = _24728 => @lem1391847 _24729 _24727 _24726 _24728 h0). Qed.
Lemma lem1391850 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1391851 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term332 _24728 _24729 _24726 _24727) = (term333 _24728 _24729 _24726 _24727).
Proof. exact (@lem1391850 (_24726 = _24728) (term331 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1391852 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : term333 _24728 _24729 _24726 _24727.
Proof. exact (EQ_MP (@lem1391851 _24728 _24729 _24726 _24727) (@lem1391848 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1391885 (x : real) (y : real) (z : real) : term334 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1391889 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1391890 : term26 = term26.
Proof. exact (@lem1391889 term26). Qed.
Lemma lem1391891 : term335.
Proof. exact (fun h0 : term336 => @lem1391890). Qed.
Lemma lem1391893 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391894 : term335 = (term26 = term26).
Proof. exact (@lem1391893 (term26 = term26)). Qed.
Lemma lem1391895 : term26 = term26.
Proof. exact (EQ_MP (@lem1391894) (@lem1391891)). Qed.
Lemma lem1391897 (_24575 : real) (h1 : term214) : (term20 _24575) = _24575.
Proof. exact (EQ_MP (@lem1389690 _24575) (@lem1389689 _24575 h1)). Qed.
Lemma lem1391898 (y : real) (h1 : term214) : (term20 y) = y.
Proof. exact (@lem1391897 y h1). Qed.
Lemma lem1391899 (y : real) (h1 : term214) : term337 y.
Proof. exact (fun h0 : term338 y => @lem1391898 y h1). Qed.
Lemma lem1391901 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391902 (y : real) : (term337 y) = ((term20 y) = y).
Proof. exact (@lem1391901 ((term20 y) = y)). Qed.
Lemma lem1391903 (y : real) (h1 : term214) : (term20 y) = y.
Proof. exact (EQ_MP (@lem1391902 y) (@lem1391899 y h1)). Qed.
Lemma lem1391905 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1391906 (y : real) : (term20 y) = (term20 y).
Proof. exact (@lem1391905 (term20 y)). Qed.
Lemma lem1391907 (y : real) : term339 y.
Proof. exact (fun h0 : term340 y => @lem1391906 y). Qed.
Lemma lem1391909 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1391910 (y : real) : (term339 y) = ((term20 y) = (term20 y)).
Proof. exact (@lem1391909 ((term20 y) = (term20 y))). Qed.
Lemma lem1391911 (y : real) : (term20 y) = (term20 y).
Proof. exact (EQ_MP (@lem1391910 y) (@lem1391907 y)). Qed.
Lemma lem1391929 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1391930 (y : real) (x : real) (z : real) : (term341 x y z) = (term342 y x z).
Proof. exact (@lem1391929 (y = z) (term343 x z)). Qed.
Lemma lem1391940 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1391941 (y : real) (x : real) (z : real) : (term334 x y z) = (term345 y x z).
Proof. exact (MK_COMB (@lem1391940 x y) (@lem1391930 y x z)). Qed.
Lemma lem1391945 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1391946 (y : real) (x : real) (z : real) : (term345 y x z) = (term346 y x z).
Proof. exact (@lem1391945 (y = z) (term343 x y) (term343 x z)). Qed.
Lemma lem1391968 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (TRANS (@lem1391941 y x z) (@lem1391946 y x z)). Qed.
Lemma lem1391969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1391970 (y : real) (x : real) (z : real) : (term347 x y z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1391969) (@lem1391968 y x z)). Qed.
Lemma lem1391992 (y : real) (x : real) (z : real) : (term346 y x z) = (term346 y x z).
Proof. exact (eq_refl (term346 y x z)). Qed.
Lemma lem1391993 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = ((term346 y x z) = (term346 y x z)).
Proof. exact (MK_COMB (@lem1391970 y x z) (@lem1391992 y x z)). Qed.
Lemma lem1391995 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1391996 (x : Prop) : (x = x) = True.
Proof. exact (@lem1391995 Prop x). Qed.
Lemma lem1391997 (y : real) (x : real) (z : real) : ((term346 y x z) = (term346 y x z)) = True.
Proof. exact (@lem1391996 (term346 y x z)). Qed.
Lemma lem1391998 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = True.
Proof. exact (TRANS (@lem1391993 y x z) (@lem1391997 y x z)). Qed.
Lemma lem1391999 (y : real) (x : real) (z : real) : True = ((term334 x y z) = (term346 y x z)).
Proof. exact (SYM (@lem1391998 y x z)). Qed.
Lemma lem1392000 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (EQ_MP (@lem1391999 y x z) (@lem0)). Qed.
Lemma lem1392001 (y : real) (x : real) (z : real) : term346 y x z.
Proof. exact (EQ_MP (@lem1392000 y x z) (@lem1391885 x y z)). Qed.
Lemma lem1392003 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392004 (x : real) (y : real) (z : real) : (term346 y x z) = (term349 x y z).
Proof. exact (@lem1392003 (term350 y x z) (y = z)). Qed.
Lemma lem1392006 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392007 (y : real) (x : real) (z : real) : (term351 y x z) = (term352 y x z).
Proof. exact (@lem1392006 (term343 x y) (term343 x z)). Qed.
Lemma lem1392009 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392010 (x : real) (y : real) : (term353 x y) = (x = y).
Proof. exact (@lem1392009 (x = y)). Qed.
Lemma lem1392011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392012 (x : real) (y : real) : (term354 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1392011) (@lem1392010 x y)). Qed.
Lemma lem1392014 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392015 (x : real) (z : real) : (term353 x z) = (x = z).
Proof. exact (@lem1392014 (x = z)). Qed.
Lemma lem1392016 (y : real) (x : real) (z : real) : (term352 y x z) = (term356 y x z).
Proof. exact (MK_COMB (@lem1392012 x y) (@lem1392015 x z)). Qed.
Lemma lem1392017 (y : real) (x : real) (z : real) : (term351 y x z) = (term356 y x z).
Proof. exact (TRANS (@lem1392007 y x z) (@lem1392016 y x z)). Qed.
Lemma lem1392018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392019 (y : real) (x : real) (z : real) : (term357 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1392018) (@lem1392017 y x z)). Qed.
Lemma lem1392020 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1392021 (x : real) (y : real) (z : real) : (term349 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1392019 y x z) (@lem1392020 y z)). Qed.
Lemma lem1392022 (x : real) (y : real) (z : real) : (term346 y x z) = (term359 x y z).
Proof. exact (TRANS (@lem1392004 x y z) (@lem1392021 x y z)). Qed.
Lemma lem1392024 (y : real) (h1 : term214) : term360 y.
Proof. exact (conj (@lem1391903 y h1) (@lem1391911 y)). Qed.
Lemma lem1392026 (x : real) (y : real) (z : real) : term359 x y z.
Proof. exact (EQ_MP (@lem1392022 x y z) (@lem1392001 y x z)). Qed.
Lemma lem1392027 (y : real) : term361 y.
Proof. exact (@lem1392026 (term20 y) y (term20 y)). Qed.
Lemma lem1392030 (y : real) (h1 : term214) : y = (term20 y).
Proof. exact (@lem1392027 y (@lem1392024 y h1)). Qed.
Lemma lem1392031 (y : real) (h1 : term214) : term362 y.
Proof. exact (fun h0 : term363 y => @lem1392030 y h1). Qed.
Lemma lem1392033 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392034 (y : real) : (term362 y) = (y = (term20 y)).
Proof. exact (@lem1392033 (y = (term20 y))). Qed.
Lemma lem1392035 (y : real) (h1 : term214) : y = (term20 y).
Proof. exact (EQ_MP (@lem1392034 y) (@lem1392031 y h1)). Qed.
Lemma lem1392037 (x : real) (y : real) (h1 : term245 x y) : term70 y.
Proof. exact (proj2 (@lem1389155 x y h1)). Qed.
Lemma lem1392038 (x : real) (y : real) (h1 : term245 x y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1392037 x y h1). Qed.
Lemma lem1392040 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392041 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1392040 (term70 y)). Qed.
Lemma lem1392042 (x : real) (y : real) (h1 : term245 x y) : term70 y.
Proof. exact (EQ_MP (@lem1392041 y) (@lem1392038 x y h1)). Qed.
Lemma lem1392060 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392061 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term331 _24728 _24729 _24726 _24727) = (term364 _24728 _24729 _24726 _24727).
Proof. exact (@lem1392060 (real_lt _24728 _24729) (term343 _24727 _24729) (term365 _24726 _24727)). Qed.
Lemma lem1392079 (_24726 : real) (_24728 : real) : (term344 _24726 _24728) = (term344 _24726 _24728).
Proof. exact (eq_refl (term344 _24726 _24728)). Qed.
Lemma lem1392080 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term333 _24728 _24729 _24726 _24727) = (term366 _24728 _24729 _24726 _24727).
Proof. exact (MK_COMB (@lem1392079 _24726 _24728) (@lem1392061 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392084 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392085 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term366 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727).
Proof. exact (@lem1392084 (real_lt _24728 _24729) (term343 _24726 _24728) (term368 _24729 _24726 _24727)). Qed.
Lemma lem1392115 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term333 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727).
Proof. exact (TRANS (@lem1392080 _24728 _24729 _24726 _24727) (@lem1392085 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1392117 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term369 _24728 _24729 _24726 _24727) = (term370 _24728 _24729 _24726 _24727).
Proof. exact (MK_COMB (@lem1392116) (@lem1392115 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392147 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term367 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727).
Proof. exact (eq_refl (term367 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392148 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : ((term333 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727)) = ((term367 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727)).
Proof. exact (MK_COMB (@lem1392117 _24728 _24729 _24726 _24727) (@lem1392147 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1392151 (x : Prop) : (x = x) = True.
Proof. exact (@lem1392150 Prop x). Qed.
Lemma lem1392152 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : ((term367 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727)) = True.
Proof. exact (@lem1392151 (term367 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392153 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : ((term333 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727)) = True.
Proof. exact (TRANS (@lem1392148 _24728 _24729 _24726 _24727) (@lem1392152 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392154 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : True = ((term333 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727)).
Proof. exact (SYM (@lem1392153 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392155 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term333 _24728 _24729 _24726 _24727) = (term367 _24728 _24729 _24726 _24727).
Proof. exact (EQ_MP (@lem1392154 _24728 _24729 _24726 _24727) (@lem0)). Qed.
Lemma lem1392156 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : term367 _24728 _24729 _24726 _24727.
Proof. exact (EQ_MP (@lem1392155 _24728 _24729 _24726 _24727) (@lem1391852 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392158 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392159 (_24726 : real) (_24727 : real) (_24728 : real) (_24729 : real) : (term367 _24728 _24729 _24726 _24727) = (term371 _24726 _24727 _24728 _24729).
Proof. exact (@lem1392158 (term372 _24728 _24729 _24726 _24727) (real_lt _24728 _24729)). Qed.
Lemma lem1392161 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392162 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term373 _24728 _24729 _24726 _24727) = (term374 _24728 _24729 _24726 _24727).
Proof. exact (@lem1392161 (term343 _24726 _24728) (term368 _24729 _24726 _24727)). Qed.
Lemma lem1392164 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392165 (_24726 : real) (_24728 : real) : (term353 _24726 _24728) = (_24726 = _24728).
Proof. exact (@lem1392164 (_24726 = _24728)). Qed.
Lemma lem1392166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392167 (_24726 : real) (_24728 : real) : (term354 _24726 _24728) = (term355 _24726 _24728).
Proof. exact (MK_COMB (@lem1392166) (@lem1392165 _24726 _24728)). Qed.
Lemma lem1392169 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392170 (_24729 : real) (_24726 : real) (_24727 : real) : (term375 _24729 _24726 _24727) = (term376 _24729 _24726 _24727).
Proof. exact (@lem1392169 (term343 _24727 _24729) (term365 _24726 _24727)). Qed.
Lemma lem1392172 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392173 (_24727 : real) (_24729 : real) : (term353 _24727 _24729) = (_24727 = _24729).
Proof. exact (@lem1392172 (_24727 = _24729)). Qed.
Lemma lem1392174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392175 (_24727 : real) (_24729 : real) : (term354 _24727 _24729) = (term355 _24727 _24729).
Proof. exact (MK_COMB (@lem1392174) (@lem1392173 _24727 _24729)). Qed.
Lemma lem1392177 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392178 (_24726 : real) (_24727 : real) : (term377 _24726 _24727) = (real_lt _24726 _24727).
Proof. exact (@lem1392177 (real_lt _24726 _24727)). Qed.
Lemma lem1392179 (_24729 : real) (_24726 : real) (_24727 : real) : (term376 _24729 _24726 _24727) = (term378 _24729 _24726 _24727).
Proof. exact (MK_COMB (@lem1392175 _24727 _24729) (@lem1392178 _24726 _24727)). Qed.
Lemma lem1392180 (_24729 : real) (_24726 : real) (_24727 : real) : (term375 _24729 _24726 _24727) = (term378 _24729 _24726 _24727).
Proof. exact (TRANS (@lem1392170 _24729 _24726 _24727) (@lem1392179 _24729 _24726 _24727)). Qed.
Lemma lem1392181 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term374 _24728 _24729 _24726 _24727) = (term379 _24728 _24729 _24726 _24727).
Proof. exact (MK_COMB (@lem1392167 _24726 _24728) (@lem1392180 _24729 _24726 _24727)). Qed.
Lemma lem1392182 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term373 _24728 _24729 _24726 _24727) = (term379 _24728 _24729 _24726 _24727).
Proof. exact (TRANS (@lem1392162 _24728 _24729 _24726 _24727) (@lem1392181 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392184 (_24728 : real) (_24729 : real) (_24726 : real) (_24727 : real) : (term380 _24728 _24729 _24726 _24727) = (term381 _24728 _24729 _24726 _24727).
Proof. exact (MK_COMB (@lem1392183) (@lem1392182 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392185 (_24728 : real) (_24729 : real) : (real_lt _24728 _24729) = (real_lt _24728 _24729).
Proof. exact (eq_refl (real_lt _24728 _24729)). Qed.
Lemma lem1392186 (_24726 : real) (_24727 : real) (_24728 : real) (_24729 : real) : (term371 _24726 _24727 _24728 _24729) = (term382 _24726 _24727 _24728 _24729).
Proof. exact (MK_COMB (@lem1392184 _24728 _24729 _24726 _24727) (@lem1392185 _24728 _24729)). Qed.
Lemma lem1392187 (_24726 : real) (_24727 : real) (_24728 : real) (_24729 : real) : (term367 _24728 _24729 _24726 _24727) = (term382 _24726 _24727 _24728 _24729).
Proof. exact (TRANS (@lem1392159 _24726 _24727 _24728 _24729) (@lem1392186 _24726 _24727 _24728 _24729)). Qed.
Lemma lem1392189 (x : real) (y : real) (h1 : term214) (h2 : term245 x y) : term383 y.
Proof. exact (conj (@lem1392035 y h1) (@lem1392042 x y h2)). Qed.
Lemma lem1392190 (x : real) (y : real) (h1 : term214) (h2 : term245 x y) : term384 y.
Proof. exact (conj (@lem1391895) (@lem1392189 x y h1 h2)). Qed.
Lemma lem1392192 (_24726 : real) (_24727 : real) (_24728 : real) (_24729 : real) : term382 _24726 _24727 _24728 _24729.
Proof. exact (EQ_MP (@lem1392187 _24726 _24727 _24728 _24729) (@lem1392156 _24728 _24729 _24726 _24727)). Qed.
Lemma lem1392193 (y : real) : term385 y.
Proof. exact (@lem1392192 term26 y term26 (term20 y)). Qed.
Lemma lem1392196 (x : real) (y : real) (h1 : term214) (h2 : term245 x y) : term386 y.
Proof. exact (@lem1392193 y (@lem1392190 x y h1 h2)). Qed.
Lemma lem1392197 (x : real) (y : real) (h1 : term214) (h2 : term245 x y) : term387 y.
Proof. exact (fun h0 : term283 y => @lem1392196 x y h1 h2). Qed.
Lemma lem1392199 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392200 (y : real) : (term387 y) = (term386 y).
Proof. exact (@lem1392199 (term386 y)). Qed.
Lemma lem1392201 (x : real) (y : real) (h1 : term214) (h2 : term245 x y) : term386 y.
Proof. exact (EQ_MP (@lem1392200 y) (@lem1392197 x y h1 h2)). Qed.
Lemma lem1392204 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1392206 (y : real) : (term283 y) = (term388 y).
Proof. exact (@lem1392204 (term386 y)). Qed.
Lemma lem1392209 (y : real) (x : real) (h1 : term245 x y) (h2 : term26 = x) : term388 y.
Proof. exact (EQ_MP (@lem1392206 y) (@lem1390377 y x h1 h2)). Qed.
Lemma lem1392212 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (@lem1392209 y x h2 h3 (@lem1392201 x y h1 h2)). Qed.
Lemma lem1392213 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : term325.
Proof. exact (fun h0 : ~ False => @lem1392212 y x h1 h2 h3). Qed.
Lemma lem1392215 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392216 : term325 = False.
Proof. exact (@lem1392215 False). Qed.
Lemma lem1392273 (x : real) (y : real) (h1 : term247 x y) : term70 x.
Proof. exact (proj1 (@lem1389163 x y h1)). Qed.
Lemma lem1392274 (x : real) (y : real) (h1 : term247 x y) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1392273 x y h1). Qed.
Lemma lem1392276 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392277 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1392276 (term70 x)). Qed.
Lemma lem1392278 (x : real) (y : real) (h1 : term247 x y) : term70 x.
Proof. exact (EQ_MP (@lem1392277 x) (@lem1392274 x y h1)). Qed.
Lemma lem1392280 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (h1). Qed.
Lemma lem1392281 (y : real) (h1 : term70 y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1392280 y h1). Qed.
Lemma lem1392283 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392284 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1392283 (term70 y)). Qed.
Lemma lem1392285 (y : real) (h1 : term70 y) : term70 y.
Proof. exact (EQ_MP (@lem1392284 y) (@lem1392281 y h1)). Qed.
Lemma lem1392301 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1392302 (_24576 : real) (_24577 : real) : (term305 _24576 _24577) = (term306 _24576 _24577).
Proof. exact (@lem1392301 (term74 _24576 _24577) (term277 _24577)). Qed.
Lemma lem1392308 (_24576 : real) : (term307 _24576) = (term307 _24576).
Proof. exact (eq_refl (term307 _24576)). Qed.
Lemma lem1392309 (_24576 : real) (_24577 : real) : (term276 _24576 _24577) = (term308 _24576 _24577).
Proof. exact (MK_COMB (@lem1392308 _24576) (@lem1392302 _24576 _24577)). Qed.
Lemma lem1392313 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392314 (_24576 : real) (_24577 : real) : (term308 _24576 _24577) = (term309 _24576 _24577).
Proof. exact (@lem1392313 (term74 _24576 _24577) (term277 _24576) (term277 _24577)). Qed.
Lemma lem1392330 (_24576 : real) (_24577 : real) : (term276 _24576 _24577) = (term309 _24576 _24577).
Proof. exact (TRANS (@lem1392309 _24576 _24577) (@lem1392314 _24576 _24577)). Qed.
Lemma lem1392331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1392332 (_24576 : real) (_24577 : real) : (term310 _24576 _24577) = (term311 _24576 _24577).
Proof. exact (MK_COMB (@lem1392331) (@lem1392330 _24576 _24577)). Qed.
Lemma lem1392348 (_24576 : real) (_24577 : real) : (term309 _24576 _24577) = (term309 _24576 _24577).
Proof. exact (eq_refl (term309 _24576 _24577)). Qed.
Lemma lem1392349 (_24576 : real) (_24577 : real) : ((term276 _24576 _24577) = (term309 _24576 _24577)) = ((term309 _24576 _24577) = (term309 _24576 _24577)).
Proof. exact (MK_COMB (@lem1392332 _24576 _24577) (@lem1392348 _24576 _24577)). Qed.
Lemma lem1392351 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1392352 (x : Prop) : (x = x) = True.
Proof. exact (@lem1392351 Prop x). Qed.
Lemma lem1392353 (_24576 : real) (_24577 : real) : ((term309 _24576 _24577) = (term309 _24576 _24577)) = True.
Proof. exact (@lem1392352 (term309 _24576 _24577)). Qed.
Lemma lem1392354 (_24576 : real) (_24577 : real) : ((term276 _24576 _24577) = (term309 _24576 _24577)) = True.
Proof. exact (TRANS (@lem1392349 _24576 _24577) (@lem1392353 _24576 _24577)). Qed.
Lemma lem1392355 (_24576 : real) (_24577 : real) : True = ((term276 _24576 _24577) = (term309 _24576 _24577)).
Proof. exact (SYM (@lem1392354 _24576 _24577)). Qed.
Lemma lem1392356 (_24576 : real) (_24577 : real) : (term276 _24576 _24577) = (term309 _24576 _24577).
Proof. exact (EQ_MP (@lem1392355 _24576 _24577) (@lem0)). Qed.
Lemma lem1392357 (_24576 : real) (_24577 : real) (h1 : term237) : term309 _24576 _24577.
Proof. exact (EQ_MP (@lem1392356 _24576 _24577) (@lem1389879 _24576 _24577 h1)). Qed.
Lemma lem1392359 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392360 (_24576 : real) (_24577 : real) : (term309 _24576 _24577) = (term313 _24576 _24577).
Proof. exact (@lem1392359 (term265 _24576 _24577) (term74 _24576 _24577)). Qed.
Lemma lem1392362 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392363 (_24576 : real) (_24577 : real) : (term316 _24576 _24577) = (term317 _24576 _24577).
Proof. exact (@lem1392362 (term277 _24576) (term277 _24577)). Qed.
Lemma lem1392365 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392366 (_24576 : real) : (term319 _24576) = (term70 _24576).
Proof. exact (@lem1392365 (term70 _24576)). Qed.
Lemma lem1392367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392368 (_24576 : real) : (term320 _24576) = (term134 _24576).
Proof. exact (MK_COMB (@lem1392367) (@lem1392366 _24576)). Qed.
Lemma lem1392370 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392371 (_24577 : real) : (term319 _24577) = (term70 _24577).
Proof. exact (@lem1392370 (term70 _24577)). Qed.
Lemma lem1392372 (_24576 : real) (_24577 : real) : (term317 _24576 _24577) = (term164 _24576 _24577).
Proof. exact (MK_COMB (@lem1392368 _24576) (@lem1392371 _24577)). Qed.
Lemma lem1392373 (_24576 : real) (_24577 : real) : (term316 _24576 _24577) = (term164 _24576 _24577).
Proof. exact (TRANS (@lem1392363 _24576 _24577) (@lem1392372 _24576 _24577)). Qed.
Lemma lem1392374 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392375 (_24576 : real) (_24577 : real) : (term321 _24576 _24577) = (term322 _24576 _24577).
Proof. exact (MK_COMB (@lem1392374) (@lem1392373 _24576 _24577)). Qed.
Lemma lem1392376 (_24576 : real) (_24577 : real) : (term74 _24576 _24577) = (term74 _24576 _24577).
Proof. exact (eq_refl (term74 _24576 _24577)). Qed.
Lemma lem1392377 (_24576 : real) (_24577 : real) : (term313 _24576 _24577) = (term170 _24576 _24577).
Proof. exact (MK_COMB (@lem1392375 _24576 _24577) (@lem1392376 _24576 _24577)). Qed.
Lemma lem1392378 (_24576 : real) (_24577 : real) : (term309 _24576 _24577) = (term170 _24576 _24577).
Proof. exact (TRANS (@lem1392360 _24576 _24577) (@lem1392377 _24576 _24577)). Qed.
Lemma lem1392380 (x : real) (y : real) (h1 : term247 x y) (h2 : term70 y) : term164 x y.
Proof. exact (conj (@lem1392278 x y h1) (@lem1392285 y h2)). Qed.
Lemma lem1392382 (_24576 : real) (_24577 : real) (h1 : term237) : term170 _24576 _24577.
Proof. exact (EQ_MP (@lem1392378 _24576 _24577) (@lem1392357 _24576 _24577 h1)). Qed.
Lemma lem1392383 (x : real) (y : real) (h1 : term237) : term170 x y.
Proof. exact (@lem1392382 x y h1). Qed.
Lemma lem1392386 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : term74 x y.
Proof. exact (@lem1392383 x y h1 (@lem1392380 x y h2 h3)). Qed.
Lemma lem1392387 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : term323 x y.
Proof. exact (fun h0 : term278 x y => @lem1392386 x y h1 h2 h3). Qed.
Lemma lem1392389 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392390 (x : real) (y : real) : (term323 x y) = (term74 x y).
Proof. exact (@lem1392389 (term74 x y)). Qed.
Lemma lem1392391 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : term74 x y.
Proof. exact (EQ_MP (@lem1392390 x y) (@lem1392387 x y h1 h2 h3)). Qed.
Lemma lem1392394 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1392396 (x : real) (y : real) : (term278 x y) = (term324 x y).
Proof. exact (@lem1392394 (term74 x y)). Qed.
Lemma lem1392399 (x : real) (y : real) (h1 : term247 x y) : term324 x y.
Proof. exact (EQ_MP (@lem1392396 x y) (@lem1389885 x y h1)). Qed.
Lemma lem1392402 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : False.
Proof. exact (@lem1392399 x y h2 (@lem1392391 x y h1 h2 h3)). Qed.
Lemma lem1392403 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : term325.
Proof. exact (fun h0 : ~ False => @lem1392402 x y h1 h2 h3). Qed.
Lemma lem1392405 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392406 : term325 = False.
Proof. exact (@lem1392405 False). Qed.
Lemma lem1392407 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : False.
Proof. exact (EQ_MP (@lem1392406) (@lem1392403 x y h1 h2 h3)). Qed.
Lemma lem1392408 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1392409 (_24750 : real) (_24752 : real) (h1 : _24750 = _24752) : _24750 = _24752.
Proof. exact (h1). Qed.
Lemma lem1392410 (_24751 : real) (_24753 : real) (h1 : _24751 = _24753) : _24751 = _24753.
Proof. exact (h1). Qed.
Lemma lem1392411 (_24750 : real) (_24752 : real) (h1 : _24750 = _24752) : (real_lt _24750) = (real_lt _24752).
Proof. exact (MK_COMB (@lem1392408) (@lem1392409 _24750 _24752 h1)). Qed.
Lemma lem1392412 (_24750 : real) (_24752 : real) (_24751 : real) (_24753 : real) (h1 : _24750 = _24752) (h2 : _24751 = _24753) : (real_lt _24750 _24751) = (real_lt _24752 _24753).
Proof. exact (MK_COMB (@lem1392411 _24750 _24752 h1) (@lem1392410 _24751 _24753 h2)). Qed.
Lemma lem1392414 (b : Prop) (a : Prop) : term326 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1392415 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : term327 _24752 _24753 _24750 _24751.
Proof. exact (@lem1392414 (real_lt _24752 _24753) (real_lt _24750 _24751)). Qed.
Lemma lem1392416 (_24750 : real) (_24752 : real) (_24751 : real) (_24753 : real) (h1 : _24750 = _24752) (h2 : _24751 = _24753) : term328 _24752 _24753 _24750 _24751.
Proof. exact (@lem1392415 _24752 _24753 _24750 _24751 (@lem1392412 _24750 _24752 _24751 _24753 h1 h2)). Qed.
Lemma lem1392417 (_24753 : real) (_24751 : real) (_24750 : real) (_24752 : real) (h1 : _24750 = _24752) : term329 _24752 _24753 _24750 _24751.
Proof. exact (fun h0 : _24751 = _24753 => @lem1392416 _24750 _24752 _24751 _24753 h1 h0). Qed.
Lemma lem1392419 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1392420 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term329 _24752 _24753 _24750 _24751) = (term331 _24752 _24753 _24750 _24751).
Proof. exact (@lem1392419 (_24751 = _24753) (term328 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392421 (_24753 : real) (_24751 : real) (_24750 : real) (_24752 : real) (h1 : _24750 = _24752) : term331 _24752 _24753 _24750 _24751.
Proof. exact (EQ_MP (@lem1392420 _24752 _24753 _24750 _24751) (@lem1392417 _24753 _24751 _24750 _24752 h1)). Qed.
Lemma lem1392422 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : term332 _24752 _24753 _24750 _24751.
Proof. exact (fun h0 : _24750 = _24752 => @lem1392421 _24753 _24751 _24750 _24752 h0). Qed.
Lemma lem1392424 (a : Prop) (b : Prop) : (a -> b) = (term330 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1392425 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term332 _24752 _24753 _24750 _24751) = (term333 _24752 _24753 _24750 _24751).
Proof. exact (@lem1392424 (_24750 = _24752) (term331 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392426 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : term333 _24752 _24753 _24750 _24751.
Proof. exact (EQ_MP (@lem1392425 _24752 _24753 _24750 _24751) (@lem1392422 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392459 (x : real) (y : real) (z : real) : term334 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1392463 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1392464 : term26 = term26.
Proof. exact (@lem1392463 term26). Qed.
Lemma lem1392465 : term335.
Proof. exact (fun h0 : term336 => @lem1392464). Qed.
Lemma lem1392467 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392468 : term335 = (term26 = term26).
Proof. exact (@lem1392467 (term26 = term26)). Qed.
Lemma lem1392469 : term26 = term26.
Proof. exact (EQ_MP (@lem1392468) (@lem1392465)). Qed.
Lemma lem1392471 (_24582 : real) (h1 : term233) : (term18 _24582) = _24582.
Proof. exact (EQ_MP (@lem1389711 _24582) (@lem1389710 _24582 h1)). Qed.
Lemma lem1392472 (x : real) (h1 : term233) : (term18 x) = x.
Proof. exact (@lem1392471 x h1). Qed.
Lemma lem1392473 (x : real) (h1 : term233) : term389 x.
Proof. exact (fun h0 : term390 x => @lem1392472 x h1). Qed.
Lemma lem1392475 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392476 (x : real) : (term389 x) = ((term18 x) = x).
Proof. exact (@lem1392475 ((term18 x) = x)). Qed.
Lemma lem1392477 (x : real) (h1 : term233) : (term18 x) = x.
Proof. exact (EQ_MP (@lem1392476 x) (@lem1392473 x h1)). Qed.
Lemma lem1392479 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1392480 (x : real) : (term18 x) = (term18 x).
Proof. exact (@lem1392479 (term18 x)). Qed.
Lemma lem1392481 (x : real) : term391 x.
Proof. exact (fun h0 : term392 x => @lem1392480 x). Qed.
Lemma lem1392483 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392484 (x : real) : (term391 x) = ((term18 x) = (term18 x)).
Proof. exact (@lem1392483 ((term18 x) = (term18 x))). Qed.
Lemma lem1392485 (x : real) : (term18 x) = (term18 x).
Proof. exact (EQ_MP (@lem1392484 x) (@lem1392481 x)). Qed.
Lemma lem1392503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1392504 (y : real) (x : real) (z : real) : (term341 x y z) = (term342 y x z).
Proof. exact (@lem1392503 (y = z) (term343 x z)). Qed.
Lemma lem1392514 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1392515 (y : real) (x : real) (z : real) : (term334 x y z) = (term345 y x z).
Proof. exact (MK_COMB (@lem1392514 x y) (@lem1392504 y x z)). Qed.
Lemma lem1392519 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392520 (y : real) (x : real) (z : real) : (term345 y x z) = (term346 y x z).
Proof. exact (@lem1392519 (y = z) (term343 x y) (term343 x z)). Qed.
Lemma lem1392542 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (TRANS (@lem1392515 y x z) (@lem1392520 y x z)). Qed.
Lemma lem1392543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1392544 (y : real) (x : real) (z : real) : (term347 x y z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1392543) (@lem1392542 y x z)). Qed.
Lemma lem1392566 (y : real) (x : real) (z : real) : (term346 y x z) = (term346 y x z).
Proof. exact (eq_refl (term346 y x z)). Qed.
Lemma lem1392567 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = ((term346 y x z) = (term346 y x z)).
Proof. exact (MK_COMB (@lem1392544 y x z) (@lem1392566 y x z)). Qed.
Lemma lem1392569 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1392570 (x : Prop) : (x = x) = True.
Proof. exact (@lem1392569 Prop x). Qed.
Lemma lem1392571 (y : real) (x : real) (z : real) : ((term346 y x z) = (term346 y x z)) = True.
Proof. exact (@lem1392570 (term346 y x z)). Qed.
Lemma lem1392572 (y : real) (x : real) (z : real) : ((term334 x y z) = (term346 y x z)) = True.
Proof. exact (TRANS (@lem1392567 y x z) (@lem1392571 y x z)). Qed.
Lemma lem1392573 (y : real) (x : real) (z : real) : True = ((term334 x y z) = (term346 y x z)).
Proof. exact (SYM (@lem1392572 y x z)). Qed.
Lemma lem1392574 (y : real) (x : real) (z : real) : (term334 x y z) = (term346 y x z).
Proof. exact (EQ_MP (@lem1392573 y x z) (@lem0)). Qed.
Lemma lem1392575 (y : real) (x : real) (z : real) : term346 y x z.
Proof. exact (EQ_MP (@lem1392574 y x z) (@lem1392459 x y z)). Qed.
Lemma lem1392577 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392578 (x : real) (y : real) (z : real) : (term346 y x z) = (term349 x y z).
Proof. exact (@lem1392577 (term350 y x z) (y = z)). Qed.
Lemma lem1392580 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392581 (y : real) (x : real) (z : real) : (term351 y x z) = (term352 y x z).
Proof. exact (@lem1392580 (term343 x y) (term343 x z)). Qed.
Lemma lem1392583 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392584 (x : real) (y : real) : (term353 x y) = (x = y).
Proof. exact (@lem1392583 (x = y)). Qed.
Lemma lem1392585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392586 (x : real) (y : real) : (term354 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem1392585) (@lem1392584 x y)). Qed.
Lemma lem1392588 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392589 (x : real) (z : real) : (term353 x z) = (x = z).
Proof. exact (@lem1392588 (x = z)). Qed.
Lemma lem1392590 (y : real) (x : real) (z : real) : (term352 y x z) = (term356 y x z).
Proof. exact (MK_COMB (@lem1392586 x y) (@lem1392589 x z)). Qed.
Lemma lem1392591 (y : real) (x : real) (z : real) : (term351 y x z) = (term356 y x z).
Proof. exact (TRANS (@lem1392581 y x z) (@lem1392590 y x z)). Qed.
Lemma lem1392592 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392593 (y : real) (x : real) (z : real) : (term357 y x z) = (term358 y x z).
Proof. exact (MK_COMB (@lem1392592) (@lem1392591 y x z)). Qed.
Lemma lem1392594 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1392595 (x : real) (y : real) (z : real) : (term349 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1392593 y x z) (@lem1392594 y z)). Qed.
Lemma lem1392596 (x : real) (y : real) (z : real) : (term346 y x z) = (term359 x y z).
Proof. exact (TRANS (@lem1392578 x y z) (@lem1392595 x y z)). Qed.
Lemma lem1392598 (x : real) (h1 : term233) : term393 x.
Proof. exact (conj (@lem1392477 x h1) (@lem1392485 x)). Qed.
Lemma lem1392600 (x : real) (y : real) (z : real) : term359 x y z.
Proof. exact (EQ_MP (@lem1392596 x y z) (@lem1392575 y x z)). Qed.
Lemma lem1392601 (x : real) : term394 x.
Proof. exact (@lem1392600 (term18 x) x (term18 x)). Qed.
Lemma lem1392604 (x : real) (h1 : term233) : x = (term18 x).
Proof. exact (@lem1392601 x (@lem1392598 x h1)). Qed.
Lemma lem1392605 (x : real) (h1 : term233) : term395 x.
Proof. exact (fun h0 : term396 x => @lem1392604 x h1). Qed.
Lemma lem1392607 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392608 (x : real) : (term395 x) = (x = (term18 x)).
Proof. exact (@lem1392607 (x = (term18 x))). Qed.
Lemma lem1392609 (x : real) (h1 : term233) : x = (term18 x).
Proof. exact (EQ_MP (@lem1392608 x) (@lem1392605 x h1)). Qed.
Lemma lem1392611 (x : real) (y : real) (h1 : term247 x y) : term70 x.
Proof. exact (proj1 (@lem1389163 x y h1)). Qed.
Lemma lem1392612 (x : real) (y : real) (h1 : term247 x y) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1392611 x y h1). Qed.
Lemma lem1392614 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392615 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1392614 (term70 x)). Qed.
Lemma lem1392616 (x : real) (y : real) (h1 : term247 x y) : term70 x.
Proof. exact (EQ_MP (@lem1392615 x) (@lem1392612 x y h1)). Qed.
Lemma lem1392634 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392635 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term331 _24752 _24753 _24750 _24751) = (term364 _24752 _24753 _24750 _24751).
Proof. exact (@lem1392634 (real_lt _24752 _24753) (term343 _24751 _24753) (term365 _24750 _24751)). Qed.
Lemma lem1392653 (_24750 : real) (_24752 : real) : (term344 _24750 _24752) = (term344 _24750 _24752).
Proof. exact (eq_refl (term344 _24750 _24752)). Qed.
Lemma lem1392654 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term333 _24752 _24753 _24750 _24751) = (term366 _24752 _24753 _24750 _24751).
Proof. exact (MK_COMB (@lem1392653 _24750 _24752) (@lem1392635 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392658 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392659 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term366 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751).
Proof. exact (@lem1392658 (real_lt _24752 _24753) (term343 _24750 _24752) (term368 _24753 _24750 _24751)). Qed.
Lemma lem1392689 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term333 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751).
Proof. exact (TRANS (@lem1392654 _24752 _24753 _24750 _24751) (@lem1392659 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1392691 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term369 _24752 _24753 _24750 _24751) = (term370 _24752 _24753 _24750 _24751).
Proof. exact (MK_COMB (@lem1392690) (@lem1392689 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392721 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term367 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751).
Proof. exact (eq_refl (term367 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392722 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : ((term333 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751)) = ((term367 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751)).
Proof. exact (MK_COMB (@lem1392691 _24752 _24753 _24750 _24751) (@lem1392721 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1392725 (x : Prop) : (x = x) = True.
Proof. exact (@lem1392724 Prop x). Qed.
Lemma lem1392726 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : ((term367 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751)) = True.
Proof. exact (@lem1392725 (term367 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392727 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : ((term333 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751)) = True.
Proof. exact (TRANS (@lem1392722 _24752 _24753 _24750 _24751) (@lem1392726 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392728 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : True = ((term333 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751)).
Proof. exact (SYM (@lem1392727 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392729 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term333 _24752 _24753 _24750 _24751) = (term367 _24752 _24753 _24750 _24751).
Proof. exact (EQ_MP (@lem1392728 _24752 _24753 _24750 _24751) (@lem0)). Qed.
Lemma lem1392730 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : term367 _24752 _24753 _24750 _24751.
Proof. exact (EQ_MP (@lem1392729 _24752 _24753 _24750 _24751) (@lem1392426 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392732 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392733 (_24750 : real) (_24751 : real) (_24752 : real) (_24753 : real) : (term367 _24752 _24753 _24750 _24751) = (term371 _24750 _24751 _24752 _24753).
Proof. exact (@lem1392732 (term372 _24752 _24753 _24750 _24751) (real_lt _24752 _24753)). Qed.
Lemma lem1392735 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392736 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term373 _24752 _24753 _24750 _24751) = (term374 _24752 _24753 _24750 _24751).
Proof. exact (@lem1392735 (term343 _24750 _24752) (term368 _24753 _24750 _24751)). Qed.
Lemma lem1392738 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392739 (_24750 : real) (_24752 : real) : (term353 _24750 _24752) = (_24750 = _24752).
Proof. exact (@lem1392738 (_24750 = _24752)). Qed.
Lemma lem1392740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392741 (_24750 : real) (_24752 : real) : (term354 _24750 _24752) = (term355 _24750 _24752).
Proof. exact (MK_COMB (@lem1392740) (@lem1392739 _24750 _24752)). Qed.
Lemma lem1392743 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392744 (_24753 : real) (_24750 : real) (_24751 : real) : (term375 _24753 _24750 _24751) = (term376 _24753 _24750 _24751).
Proof. exact (@lem1392743 (term343 _24751 _24753) (term365 _24750 _24751)). Qed.
Lemma lem1392746 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392747 (_24751 : real) (_24753 : real) : (term353 _24751 _24753) = (_24751 = _24753).
Proof. exact (@lem1392746 (_24751 = _24753)). Qed.
Lemma lem1392748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392749 (_24751 : real) (_24753 : real) : (term354 _24751 _24753) = (term355 _24751 _24753).
Proof. exact (MK_COMB (@lem1392748) (@lem1392747 _24751 _24753)). Qed.
Lemma lem1392751 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392752 (_24750 : real) (_24751 : real) : (term377 _24750 _24751) = (real_lt _24750 _24751).
Proof. exact (@lem1392751 (real_lt _24750 _24751)). Qed.
Lemma lem1392753 (_24753 : real) (_24750 : real) (_24751 : real) : (term376 _24753 _24750 _24751) = (term378 _24753 _24750 _24751).
Proof. exact (MK_COMB (@lem1392749 _24751 _24753) (@lem1392752 _24750 _24751)). Qed.
Lemma lem1392754 (_24753 : real) (_24750 : real) (_24751 : real) : (term375 _24753 _24750 _24751) = (term378 _24753 _24750 _24751).
Proof. exact (TRANS (@lem1392744 _24753 _24750 _24751) (@lem1392753 _24753 _24750 _24751)). Qed.
Lemma lem1392755 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term374 _24752 _24753 _24750 _24751) = (term379 _24752 _24753 _24750 _24751).
Proof. exact (MK_COMB (@lem1392741 _24750 _24752) (@lem1392754 _24753 _24750 _24751)). Qed.
Lemma lem1392756 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term373 _24752 _24753 _24750 _24751) = (term379 _24752 _24753 _24750 _24751).
Proof. exact (TRANS (@lem1392736 _24752 _24753 _24750 _24751) (@lem1392755 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392758 (_24752 : real) (_24753 : real) (_24750 : real) (_24751 : real) : (term380 _24752 _24753 _24750 _24751) = (term381 _24752 _24753 _24750 _24751).
Proof. exact (MK_COMB (@lem1392757) (@lem1392756 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392759 (_24752 : real) (_24753 : real) : (real_lt _24752 _24753) = (real_lt _24752 _24753).
Proof. exact (eq_refl (real_lt _24752 _24753)). Qed.
Lemma lem1392760 (_24750 : real) (_24751 : real) (_24752 : real) (_24753 : real) : (term371 _24750 _24751 _24752 _24753) = (term382 _24750 _24751 _24752 _24753).
Proof. exact (MK_COMB (@lem1392758 _24752 _24753 _24750 _24751) (@lem1392759 _24752 _24753)). Qed.
Lemma lem1392761 (_24750 : real) (_24751 : real) (_24752 : real) (_24753 : real) : (term367 _24752 _24753 _24750 _24751) = (term382 _24750 _24751 _24752 _24753).
Proof. exact (TRANS (@lem1392733 _24750 _24751 _24752 _24753) (@lem1392760 _24750 _24751 _24752 _24753)). Qed.
Lemma lem1392763 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) : term397 x.
Proof. exact (conj (@lem1392609 x h1) (@lem1392616 x y h2)). Qed.
Lemma lem1392764 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) : term398 x.
Proof. exact (conj (@lem1392469) (@lem1392763 x y h1 h2)). Qed.
Lemma lem1392766 (_24750 : real) (_24751 : real) (_24752 : real) (_24753 : real) : term382 _24750 _24751 _24752 _24753.
Proof. exact (EQ_MP (@lem1392761 _24750 _24751 _24752 _24753) (@lem1392730 _24752 _24753 _24750 _24751)). Qed.
Lemma lem1392767 (x : real) : term399 x.
Proof. exact (@lem1392766 term26 x term26 (term18 x)). Qed.
Lemma lem1392770 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) : term400 x.
Proof. exact (@lem1392767 x (@lem1392764 x y h1 h2)). Qed.
Lemma lem1392771 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) : term401 x.
Proof. exact (fun h0 : term289 x => @lem1392770 x y h1 h2). Qed.
Lemma lem1392773 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392774 (x : real) : (term401 x) = (term400 x).
Proof. exact (@lem1392773 (term400 x)). Qed.
Lemma lem1392775 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) : term400 x.
Proof. exact (EQ_MP (@lem1392774 x) (@lem1392771 x y h1 h2)). Qed.
Lemma lem1392778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1392780 (x : real) : (term289 x) = (term402 x).
Proof. exact (@lem1392778 (term400 x)). Qed.
Lemma lem1392783 (x : real) (y : real) (h1 : term247 x y) (h2 : term26 = y) : term402 x.
Proof. exact (EQ_MP (@lem1392780 x) (@lem1390461 x y h1 h2)). Qed.
Lemma lem1392786 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (@lem1392783 x y h2 h3 (@lem1392775 x y h1 h2)). Qed.
Lemma lem1392787 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : term325.
Proof. exact (fun h0 : ~ False => @lem1392786 x y h1 h2 h3). Qed.
Lemma lem1392789 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392790 : term325 = False.
Proof. exact (@lem1392789 False). Qed.
Lemma lem1392847 (x : real) (y : real) (h1 : term249 x y) : term70 x.
Proof. exact (proj1 (@lem1389169 x y h1)). Qed.
Lemma lem1392848 (x : real) (y : real) (h1 : term249 x y) : term303 x.
Proof. exact (fun h0 : term277 x => @lem1392847 x y h1). Qed.
Lemma lem1392850 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392851 (x : real) : (term303 x) = (term70 x).
Proof. exact (@lem1392850 (term70 x)). Qed.
Lemma lem1392852 (x : real) (y : real) (h1 : term249 x y) : term70 x.
Proof. exact (EQ_MP (@lem1392851 x) (@lem1392848 x y h1)). Qed.
Lemma lem1392854 (x : real) (y : real) (h1 : term249 x y) : term70 y.
Proof. exact (proj2 (@lem1389169 x y h1)). Qed.
Lemma lem1392855 (x : real) (y : real) (h1 : term249 x y) : term303 y.
Proof. exact (fun h0 : term277 y => @lem1392854 x y h1). Qed.
Lemma lem1392857 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392858 (y : real) : (term303 y) = (term70 y).
Proof. exact (@lem1392857 (term70 y)). Qed.
Lemma lem1392859 (x : real) (y : real) (h1 : term249 x y) : term70 y.
Proof. exact (EQ_MP (@lem1392858 y) (@lem1392855 x y h1)). Qed.
Lemma lem1392875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1392876 (_24584 : real) (_24585 : real) : (term305 _24584 _24585) = (term306 _24584 _24585).
Proof. exact (@lem1392875 (term74 _24584 _24585) (term277 _24585)). Qed.
Lemma lem1392882 (_24584 : real) : (term307 _24584) = (term307 _24584).
Proof. exact (eq_refl (term307 _24584)). Qed.
Lemma lem1392883 (_24584 : real) (_24585 : real) : (term276 _24584 _24585) = (term308 _24584 _24585).
Proof. exact (MK_COMB (@lem1392882 _24584) (@lem1392876 _24584 _24585)). Qed.
Lemma lem1392887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1392888 (_24584 : real) (_24585 : real) : (term308 _24584 _24585) = (term309 _24584 _24585).
Proof. exact (@lem1392887 (term74 _24584 _24585) (term277 _24584) (term277 _24585)). Qed.
Lemma lem1392904 (_24584 : real) (_24585 : real) : (term276 _24584 _24585) = (term309 _24584 _24585).
Proof. exact (TRANS (@lem1392883 _24584 _24585) (@lem1392888 _24584 _24585)). Qed.
Lemma lem1392905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1392906 (_24584 : real) (_24585 : real) : (term310 _24584 _24585) = (term311 _24584 _24585).
Proof. exact (MK_COMB (@lem1392905) (@lem1392904 _24584 _24585)). Qed.
Lemma lem1392922 (_24584 : real) (_24585 : real) : (term309 _24584 _24585) = (term309 _24584 _24585).
Proof. exact (eq_refl (term309 _24584 _24585)). Qed.
Lemma lem1392923 (_24584 : real) (_24585 : real) : ((term276 _24584 _24585) = (term309 _24584 _24585)) = ((term309 _24584 _24585) = (term309 _24584 _24585)).
Proof. exact (MK_COMB (@lem1392906 _24584 _24585) (@lem1392922 _24584 _24585)). Qed.
Lemma lem1392925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1392926 (x : Prop) : (x = x) = True.
Proof. exact (@lem1392925 Prop x). Qed.
Lemma lem1392927 (_24584 : real) (_24585 : real) : ((term309 _24584 _24585) = (term309 _24584 _24585)) = True.
Proof. exact (@lem1392926 (term309 _24584 _24585)). Qed.
Lemma lem1392928 (_24584 : real) (_24585 : real) : ((term276 _24584 _24585) = (term309 _24584 _24585)) = True.
Proof. exact (TRANS (@lem1392923 _24584 _24585) (@lem1392927 _24584 _24585)). Qed.
Lemma lem1392929 (_24584 : real) (_24585 : real) : True = ((term276 _24584 _24585) = (term309 _24584 _24585)).
Proof. exact (SYM (@lem1392928 _24584 _24585)). Qed.
Lemma lem1392930 (_24584 : real) (_24585 : real) : (term276 _24584 _24585) = (term309 _24584 _24585).
Proof. exact (EQ_MP (@lem1392929 _24584 _24585) (@lem0)). Qed.
Lemma lem1392931 (_24584 : real) (_24585 : real) (h1 : term237) : term309 _24584 _24585.
Proof. exact (EQ_MP (@lem1392930 _24584 _24585) (@lem1389923 _24584 _24585 h1)). Qed.
Lemma lem1392933 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1392934 (_24584 : real) (_24585 : real) : (term309 _24584 _24585) = (term313 _24584 _24585).
Proof. exact (@lem1392933 (term265 _24584 _24585) (term74 _24584 _24585)). Qed.
Lemma lem1392936 (a : Prop) (b : Prop) : (term314 a b) = (term315 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1392937 (_24584 : real) (_24585 : real) : (term316 _24584 _24585) = (term317 _24584 _24585).
Proof. exact (@lem1392936 (term277 _24584) (term277 _24585)). Qed.
Lemma lem1392939 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392940 (_24584 : real) : (term319 _24584) = (term70 _24584).
Proof. exact (@lem1392939 (term70 _24584)). Qed.
Lemma lem1392941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1392942 (_24584 : real) : (term320 _24584) = (term134 _24584).
Proof. exact (MK_COMB (@lem1392941) (@lem1392940 _24584)). Qed.
Lemma lem1392944 (a : Prop) : (term318 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1392945 (_24585 : real) : (term319 _24585) = (term70 _24585).
Proof. exact (@lem1392944 (term70 _24585)). Qed.
Lemma lem1392946 (_24584 : real) (_24585 : real) : (term317 _24584 _24585) = (term164 _24584 _24585).
Proof. exact (MK_COMB (@lem1392942 _24584) (@lem1392945 _24585)). Qed.
Lemma lem1392947 (_24584 : real) (_24585 : real) : (term316 _24584 _24585) = (term164 _24584 _24585).
Proof. exact (TRANS (@lem1392937 _24584 _24585) (@lem1392946 _24584 _24585)). Qed.
Lemma lem1392948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1392949 (_24584 : real) (_24585 : real) : (term321 _24584 _24585) = (term322 _24584 _24585).
Proof. exact (MK_COMB (@lem1392948) (@lem1392947 _24584 _24585)). Qed.
Lemma lem1392950 (_24584 : real) (_24585 : real) : (term74 _24584 _24585) = (term74 _24584 _24585).
Proof. exact (eq_refl (term74 _24584 _24585)). Qed.
Lemma lem1392951 (_24584 : real) (_24585 : real) : (term313 _24584 _24585) = (term170 _24584 _24585).
Proof. exact (MK_COMB (@lem1392949 _24584 _24585) (@lem1392950 _24584 _24585)). Qed.
Lemma lem1392952 (_24584 : real) (_24585 : real) : (term309 _24584 _24585) = (term170 _24584 _24585).
Proof. exact (TRANS (@lem1392934 _24584 _24585) (@lem1392951 _24584 _24585)). Qed.
Lemma lem1392954 (x : real) (y : real) (h1 : term249 x y) : term164 x y.
Proof. exact (conj (@lem1392852 x y h1) (@lem1392859 x y h1)). Qed.
Lemma lem1392956 (_24584 : real) (_24585 : real) (h1 : term237) : term170 _24584 _24585.
Proof. exact (EQ_MP (@lem1392952 _24584 _24585) (@lem1392931 _24584 _24585 h1)). Qed.
Lemma lem1392957 (x : real) (y : real) (h1 : term237) : term170 x y.
Proof. exact (@lem1392956 x y h1). Qed.
Lemma lem1392960 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : term74 x y.
Proof. exact (@lem1392957 x y h1 (@lem1392954 x y h2)). Qed.
Lemma lem1392961 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : term323 x y.
Proof. exact (fun h0 : term278 x y => @lem1392960 x y h1 h2). Qed.
Lemma lem1392963 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392964 (x : real) (y : real) : (term323 x y) = (term74 x y).
Proof. exact (@lem1392963 (term74 x y)). Qed.
Lemma lem1392965 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : term74 x y.
Proof. exact (EQ_MP (@lem1392964 x y) (@lem1392961 x y h1 h2)). Qed.
Lemma lem1392968 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1392970 (x : real) (y : real) : (term278 x y) = (term324 x y).
Proof. exact (@lem1392968 (term74 x y)). Qed.
Lemma lem1392973 (x : real) (y : real) (h1 : term249 x y) : term324 x y.
Proof. exact (EQ_MP (@lem1392970 x y) (@lem1389929 x y h1)). Qed.
Lemma lem1392976 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : False.
Proof. exact (@lem1392973 x y h2 (@lem1392965 x y h1 h2)). Qed.
Lemma lem1392977 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : term325.
Proof. exact (fun h0 : ~ False => @lem1392976 x y h1 h2). Qed.
Lemma lem1392979 (p : Prop) : (term304 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1392980 : term325 = False.
Proof. exact (@lem1392979 False). Qed.
Lemma lem1392981 (x : real) (y : real) (h1 : term237) (h2 : term249 x y) : False.
Proof. exact (EQ_MP (@lem1392980) (@lem1392977 x y h1 h2)). Qed.
Lemma lem1392982 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1392790) (@lem1392787 x y h1 h2 h3)). Qed.
Lemma lem1392983 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (EQ_MP (@lem1392216) (@lem1392213 y x h1 h2 h3)). Qed.
Lemma lem1392984 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1391642) (@lem1391639 x y h1 h2 h3 h4)). Qed.
Lemma lem1392985 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1392984 x y h1 h2 h3 h4) (fun h5 : False => @lem1390224 y h4)). Qed.
Lemma lem1392987 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1392985 x y h1 h2 h3 h4) (@lem1390224 y h4)). Qed.
Lemma lem1392988 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1391433 y x h1 h2 h3 h4) (fun h5 : False => @lem1390127 x h4)). Qed.
Lemma lem1392990 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1392988 y x h1 h2 h3 h4) (@lem1390127 x h4)). Qed.
Lemma lem1392991 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1391049 x y h1 h2 h3 h4) (fun h5 : False => @lem1390030 y h4)). Qed.
Lemma lem1392993 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1392991 x y h1 h2 h3 h4) (@lem1390030 y h4)). Qed.
Lemma lem1392994 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h4 : term26 = y => @lem1392982 x y h1 h2 h3) (fun h4 : False => @lem1389911 y h3)). Qed.
Lemma lem1392995 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1392994 x y h1 h2 h3) (@lem1389911 y h3)). Qed.
Lemma lem1392996 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h4 : term70 y => @lem1392407 x y h1 h2 h3) (fun h4 : False => @lem1389889 y h3)). Qed.
Lemma lem1392997 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : False.
Proof. exact (EQ_MP (@lem1392996 x y h1 h2 h3) (@lem1389889 y h3)). Qed.
Lemma lem1392998 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : (term26 = x) = False.
Proof. exact (prop_ext (fun h4 : term26 = x => @lem1392983 y x h1 h2 h3) (fun h4 : False => @lem1389867 x h3)). Qed.
Lemma lem1392999 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (EQ_MP (@lem1392998 y x h1 h2 h3) (@lem1389867 x h3)). Qed.
Lemma lem1393000 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h4 : term70 x => @lem1391833 y x h1 h2 h3) (fun h4 : False => @lem1389845 x h3)). Qed.
Lemma lem1393001 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393000 y x h1 h2 h3) (@lem1389845 x h3)). Qed.
Lemma lem1393002 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1392987 x y h1 h2 h3 h4) (fun h5 : False => @lem1389823 x h3)). Qed.
Lemma lem1393003 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393002 x y h1 h2 h3 h4) (@lem1389823 x h3)). Qed.
Lemma lem1393004 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393003 x y h1 h2 h3 h4) (fun h5 : False => @lem1389821 y h4)). Qed.
Lemma lem1393005 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393004 x y h1 h2 h3 h4) (@lem1389821 y h4)). Qed.
Lemma lem1393006 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1392990 y x h1 h2 h3 h4) (fun h5 : False => @lem1389799 x h4)). Qed.
Lemma lem1393007 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393006 y x h1 h2 h3 h4) (@lem1389799 x h4)). Qed.
Lemma lem1393008 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393007 y x h1 h2 h3 h4) (fun h5 : False => @lem1389797 y h3)). Qed.
Lemma lem1393009 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393008 y x h1 h2 h3 h4) (@lem1389797 y h3)). Qed.
Lemma lem1393010 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1392993 x y h1 h2 h3 h4) (fun h5 : False => @lem1389775 x h3)). Qed.
Lemma lem1393011 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393010 x y h1 h2 h3 h4) (@lem1389775 x h3)). Qed.
Lemma lem1393012 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393011 x y h1 h2 h3 h4) (fun h5 : False => @lem1389773 y h4)). Qed.
Lemma lem1393013 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393012 x y h1 h2 h3 h4) (@lem1389773 y h4)). Qed.
Lemma lem1393014 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1390665 x y h1 h2 h3 h4) (fun h5 : False => @lem1389751 x h3)). Qed.
Lemma lem1393015 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393014 x y h1 h2 h3 h4) (@lem1389751 x h3)). Qed.
Lemma lem1393016 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393015 x y h1 h2 h3 h4) (fun h5 : False => @lem1389749 y h4)). Qed.
Lemma lem1393017 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393016 x y h1 h2 h3 h4) (@lem1389749 y h4)). Qed.
Lemma lem1393018 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h4 : term26 = y => @lem1392995 x y h1 h2 h3) (fun h4 : False => @lem1389571 y h3)). Qed.
Lemma lem1393019 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393018 x y h1 h2 h3) (@lem1389571 y h3)). Qed.
Lemma lem1393020 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h4 : term70 y => @lem1392997 x y h1 h2 h3) (fun h4 : False => @lem1389523 y h3)). Qed.
Lemma lem1393021 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393020 x y h1 h2 h3) (@lem1389523 y h3)). Qed.
Lemma lem1393022 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : (term26 = x) = False.
Proof. exact (prop_ext (fun h4 : term26 = x => @lem1392999 y x h1 h2 h3) (fun h4 : False => @lem1389475 x h3)). Qed.
Lemma lem1393023 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (EQ_MP (@lem1393022 y x h1 h2 h3) (@lem1389475 x h3)). Qed.
Lemma lem1393024 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h4 : term70 x => @lem1393001 y x h1 h2 h3) (fun h4 : False => @lem1389427 x h3)). Qed.
Lemma lem1393025 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393024 y x h1 h2 h3) (@lem1389427 x h3)). Qed.
Lemma lem1393026 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1393005 x y h1 h2 h3 h4) (fun h5 : False => @lem1389379 x h3)). Qed.
Lemma lem1393027 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393026 x y h1 h2 h3 h4) (@lem1389379 x h3)). Qed.
Lemma lem1393028 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393027 x y h1 h2 h3 h4) (fun h5 : False => @lem1389375 y h4)). Qed.
Lemma lem1393029 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393028 x y h1 h2 h3 h4) (@lem1389375 y h4)). Qed.
Lemma lem1393030 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1393009 y x h1 h2 h3 h4) (fun h5 : False => @lem1389327 x h4)). Qed.
Lemma lem1393031 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393030 y x h1 h2 h3 h4) (@lem1389327 x h4)). Qed.
Lemma lem1393032 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393031 y x h1 h2 h3 h4) (fun h5 : False => @lem1389323 y h3)). Qed.
Lemma lem1393033 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393032 y x h1 h2 h3 h4) (@lem1389323 y h3)). Qed.
Lemma lem1393034 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1393013 x y h1 h2 h3 h4) (fun h5 : False => @lem1389275 x h3)). Qed.
Lemma lem1393035 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393034 x y h1 h2 h3 h4) (@lem1389275 x h3)). Qed.
Lemma lem1393036 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393035 x y h1 h2 h3 h4) (fun h5 : False => @lem1389271 y h4)). Qed.
Lemma lem1393037 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393036 x y h1 h2 h3 h4) (@lem1389271 y h4)). Qed.
Lemma lem1393038 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1393017 x y h1 h2 h3 h4) (fun h5 : False => @lem1389223 x h3)). Qed.
Lemma lem1393039 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393038 x y h1 h2 h3 h4) (@lem1389223 x h3)). Qed.
Lemma lem1393040 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393039 x y h1 h2 h3 h4) (fun h5 : False => @lem1389219 y h4)). Qed.
Lemma lem1393041 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393040 x y h1 h2 h3 h4) (@lem1389219 y h4)). Qed.
Lemma lem1393042 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h4 : term26 = y => @lem1393019 x y h1 h2 h3) (fun h4 : False => @lem1389571 y h3)). Qed.
Lemma lem1393043 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393042 x y h1 h2 h3) (@lem1389571 y h3)). Qed.
Lemma lem1393044 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : term233 = False.
Proof. exact (prop_ext (fun h4 : term233 => @lem1393043 x y h1 h2 h3) (fun h4 : False => @lem1389552 h1)). Qed.
Lemma lem1393045 (x : real) (y : real) (h1 : term233) (h2 : term247 x y) (h3 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393044 x y h1 h2 h3) (@lem1389552 h1)). Qed.
Lemma lem1393046 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h4 : term70 y => @lem1393021 x y h1 h2 h3) (fun h4 : False => @lem1389523 y h3)). Qed.
Lemma lem1393047 (x : real) (y : real) (h1 : term237) (h2 : term247 x y) (h3 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393046 x y h1 h2 h3) (@lem1389523 y h3)). Qed.
Lemma lem1393048 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : (term26 = x) = False.
Proof. exact (prop_ext (fun h4 : term26 = x => @lem1393023 y x h1 h2 h3) (fun h4 : False => @lem1389475 x h3)). Qed.
Lemma lem1393049 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (EQ_MP (@lem1393048 y x h1 h2 h3) (@lem1389475 x h3)). Qed.
Lemma lem1393050 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : term214 = False.
Proof. exact (prop_ext (fun h4 : term214 => @lem1393049 y x h1 h2 h3) (fun h4 : False => @lem1389463 h1)). Qed.
Lemma lem1393051 (y : real) (x : real) (h1 : term214) (h2 : term245 x y) (h3 : term26 = x) : False.
Proof. exact (EQ_MP (@lem1393050 y x h1 h2 h3) (@lem1389463 h1)). Qed.
Lemma lem1393052 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h4 : term70 x => @lem1393025 y x h1 h2 h3) (fun h4 : False => @lem1389427 x h3)). Qed.
Lemma lem1393053 (y : real) (x : real) (h1 : term237) (h2 : term245 x y) (h3 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393052 y x h1 h2 h3) (@lem1389427 x h3)). Qed.
Lemma lem1393054 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1393029 x y h1 h2 h3 h4) (fun h5 : False => @lem1389379 x h3)). Qed.
Lemma lem1393055 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393054 x y h1 h2 h3 h4) (@lem1389379 x h3)). Qed.
Lemma lem1393056 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393055 x y h1 h2 h3 h4) (fun h5 : False => @lem1389375 y h4)). Qed.
Lemma lem1393057 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393056 x y h1 h2 h3 h4) (@lem1389375 y h4)). Qed.
Lemma lem1393058 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : term214 = False.
Proof. exact (prop_ext (fun h5 : term214 => @lem1393057 x y h1 h2 h3 h4) (fun h5 : False => @lem1389363 h1)). Qed.
Lemma lem1393059 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term26 = y) : False.
Proof. exact (EQ_MP (@lem1393058 x y h1 h2 h3 h4) (@lem1389363 h1)). Qed.
Lemma lem1393060 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1393033 y x h1 h2 h3 h4) (fun h5 : False => @lem1389327 x h4)). Qed.
Lemma lem1393061 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393060 y x h1 h2 h3 h4) (@lem1389327 x h4)). Qed.
Lemma lem1393062 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : (term26 = y) = False.
Proof. exact (prop_ext (fun h5 : term26 = y => @lem1393061 y x h1 h2 h3 h4) (fun h5 : False => @lem1389323 y h3)). Qed.
Lemma lem1393063 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393062 y x h1 h2 h3 h4) (@lem1389323 y h3)). Qed.
Lemma lem1393064 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : term233 = False.
Proof. exact (prop_ext (fun h5 : term233 => @lem1393063 y x h1 h2 h3 h4) (fun h5 : False => @lem1389304 h1)). Qed.
Lemma lem1393065 (y : real) (x : real) (h1 : term233) (h2 : term242 x y) (h3 : term26 = y) (h4 : term70 x) : False.
Proof. exact (EQ_MP (@lem1393064 y x h1 h2 h3 h4) (@lem1389304 h1)). Qed.
Lemma lem1393066 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term26 = x) = False.
Proof. exact (prop_ext (fun h5 : term26 = x => @lem1393037 x y h1 h2 h3 h4) (fun h5 : False => @lem1389275 x h3)). Qed.
Lemma lem1393067 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393066 x y h1 h2 h3 h4) (@lem1389275 x h3)). Qed.
Lemma lem1393068 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393067 x y h1 h2 h3 h4) (fun h5 : False => @lem1389271 y h4)). Qed.
Lemma lem1393069 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393068 x y h1 h2 h3 h4) (@lem1389271 y h4)). Qed.
Lemma lem1393070 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : term214 = False.
Proof. exact (prop_ext (fun h5 : term214 => @lem1393069 x y h1 h2 h3 h4) (fun h5 : False => @lem1389259 h1)). Qed.
Lemma lem1393071 (x : real) (y : real) (h1 : term214) (h2 : term242 x y) (h3 : term26 = x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393070 x y h1 h2 h3 h4) (@lem1389259 h1)). Qed.
Lemma lem1393072 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 x) = False.
Proof. exact (prop_ext (fun h5 : term70 x => @lem1393041 x y h1 h2 h3 h4) (fun h5 : False => @lem1389223 x h3)). Qed.
Lemma lem1393073 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393072 x y h1 h2 h3 h4) (@lem1389223 x h3)). Qed.
Lemma lem1393074 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : (term70 y) = False.
Proof. exact (prop_ext (fun h5 : term70 y => @lem1393073 x y h1 h2 h3 h4) (fun h5 : False => @lem1389219 y h4)). Qed.
Lemma lem1393075 (x : real) (y : real) (h1 : term237) (h2 : term242 x y) (h3 : term70 x) (h4 : term70 y) : False.
Proof. exact (EQ_MP (@lem1393074 x y h1 h2 h3 h4) (@lem1389219 y h4)). Qed.
Lemma lem1393076 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term247 x y) : False.
Proof. exact (or_elim (@lem1389164 x y h3) (fun h0 : term70 y => @lem1393047 x y h1 h3 h0) (fun h0 : term26 = y => @lem1393045 x y h2 h3 h0)). Qed.
Lemma lem1393077 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term253 x y) : False.
Proof. exact (or_elim (@lem1389153 x y h3) (fun h0 : term247 x y => @lem1393076 x y h1 h2 h0) (fun h0 : term249 x y => @lem1392981 x y h1 h0)). Qed.
Lemma lem1393078 (x : real) (y : real) (h1 : term237) (h2 : term214) (h3 : term245 x y) : False.
Proof. exact (or_elim (@lem1389157 x y h3) (fun h0 : term70 x => @lem1393053 y x h1 h3 h0) (fun h0 : term26 = x => @lem1393051 y x h2 h3 h0)). Qed.
Lemma lem1393079 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term258 x y) : False.
Proof. exact (or_elim (@lem1389139 x y h4) (fun h0 : term245 x y => @lem1393078 x y h1 h3 h0) (fun h0 : term253 x y => @lem1393077 x y h1 h2 h0)). Qed.
Lemma lem1393080 (x : real) (y : real) (h1 : term233) (h2 : term214) (h3 : term242 x y) (h4 : term26 = y) : False.
Proof. exact (or_elim (@lem1389145 x y h3) (fun h0 : term70 x => @lem1393065 y x h1 h3 h4 h0) (fun h0 : term26 = x => @lem1393059 x y h2 h3 h0 h4)). Qed.
Lemma lem1393081 (x : real) (y : real) (h1 : term237) (h2 : term214) (h3 : term242 x y) (h4 : term70 y) : False.
Proof. exact (or_elim (@lem1389145 x y h3) (fun h0 : term70 x => @lem1393075 x y h1 h3 h0 h4) (fun h0 : term26 = x => @lem1393071 x y h2 h3 h0 h4)). Qed.
Lemma lem1393082 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term242 x y) : False.
Proof. exact (or_elim (@lem1389144 x y h4) (fun h0 : term70 y => @lem1393081 x y h1 h3 h4 h0) (fun h0 : term26 = y => @lem1393080 x y h2 h3 h4 h0)). Qed.
Lemma lem1393083 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : False.
Proof. exact (or_elim (@lem1389055 x y h4) (fun h0 : term242 x y => @lem1393082 x y h1 h2 h3 h0) (fun h0 : term258 x y => @lem1393079 x y h1 h2 h3 h0)). Qed.
Lemma lem1393084 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : term214 = False.
Proof. exact (prop_ext (fun h5 : term214 => @lem1393083 x y h1 h2 h3 h4) (fun h5 : False => @lem1389137 h3)). Qed.
Lemma lem1393085 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1393084 x y h1 h2 h3 h4) (@lem1389137 h3)). Qed.
Lemma lem1393086 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : term233 = False.
Proof. exact (prop_ext (fun h5 : term233 => @lem1393085 x y h1 h2 h3 h4) (fun h5 : False => @lem1389120 h2)). Qed.
Lemma lem1393087 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1393086 x y h1 h2 h3 h4) (@lem1389120 h2)). Qed.
Lemma lem1393088 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : term214 = False.
Proof. exact (prop_ext (fun h5 : term214 => @lem1393087 x y h1 h2 h3 h4) (fun h5 : False => @lem1388823 h3)). Qed.
Lemma lem1393089 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1393088 x y h1 h2 h3 h4) (@lem1388823 h3)). Qed.
Lemma lem1393090 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : term233 = False.
Proof. exact (prop_ext (fun h5 : term233 => @lem1393089 x y h1 h2 h3 h4) (fun h5 : False => @lem1388810 h2)). Qed.
Lemma lem1393091 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term214) (h4 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1393090 x y h1 h2 h3 h4) (@lem1388810 h2)). Qed.
Lemma lem1393092 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term207 x y) : term212.
Proof. exact (fun h0 : term214 => @lem1393091 x y h1 h2 h0 h3). Qed.
Lemma lem1393093 : term212 = term213.
Proof. exact (@lem69 term214). Qed.
Lemma lem1393094 (x : real) (y : real) (h1 : term237) (h2 : term233) (h3 : term207 x y) : term213.
Proof. exact (EQ_MP (@lem1393093) (@lem1393092 x y h1 h2 h3)). Qed.
Lemma lem1393095 (x : real) (y : real) (h1 : term237) (h2 : term207 x y) : term217.
Proof. exact (fun h0 : term233 => @lem1393094 x y h1 h0 h2). Qed.
Lemma lem1393096 (x : real) (y : real) (h1 : term207 x y) : term220.
Proof. exact (fun h0 : term237 => @lem1393095 x y h0 h1). Qed.
Lemma lem1393097 (x : real) (y : real) : term222 x y.
Proof. exact (fun h0 : term207 x y => @lem1393096 x y h0). Qed.
Lemma lem1393102 (y : real) : term226 y.
Proof. exact (fun x : real => @lem1393097 x y). Qed.
Lemma lem1393107 : term230.
Proof. exact (fun y : real => @lem1393102 y). Qed.
Lemma lem1393108 : term229.
Proof. exact (EQ_MP (@lem1388631) (@lem1393107)). Qed.
Lemma lem1393109 (y : real) : term411 y.
Proof. exact (@lem1393108 y). Qed.
Lemma lem1393110 (y : real) : (term411 y) = (term225 y).
Proof. exact (eq_refl (term411 y)). Qed.
Lemma lem1393111 (y : real) : term225 y.
Proof. exact (EQ_MP (@lem1393110 y) (@lem1393109 y)). Qed.
Lemma lem1393112 (y : real) (x : real) : term412 y x.
Proof. exact (@lem1393111 y x). Qed.
Lemma lem1393113 (x : real) (y : real) : (term412 y x) = (term208 x y).
Proof. exact (eq_refl (term412 y x)). Qed.
Lemma lem1393114 (x : real) (y : real) : term208 x y.
Proof. exact (EQ_MP (@lem1393113 x y) (@lem1393112 y x)). Qed.
Lemma lem1393116 (x : real) (y : real) : term208 x y.
Proof. exact (@lem1388343 x y (@lem1393114 x y)). Qed.
Lemma lem1393117 (x : real) (y : real) (h1 : term207 x y) : term219.
Proof. exact (@lem1393116 x y (@lem1388328 x y h1)). Qed.
Lemma lem1393118 (x : real) (y : real) (h1 : term207 x y) : term216.
Proof. exact (@lem1393117 x y h1 (@lem1382497)). Qed.
Lemma lem1393119 (x : real) (y : real) (h1 : term207 x y) : term212.
Proof. exact (@lem1393118 x y h1 (@lem1361590)). Qed.
Lemma lem1393120 (x : real) (y : real) (h1 : term207 x y) : False.
Proof. exact (@lem1393119 x y h1 (@lem1338512)). Qed.
Lemma lem1393121 (x : real) (y : real) (h1 : term207 x y) : (term207 x y) = False.
Proof. exact (prop_ext (fun h2 : term207 x y => @lem1393120 x y h1) (fun h2 : False => @lem1388328 x y h1)). Qed.
Lemma lem1393122 (x : real) (y : real) (h1 : term207 x y) : False.
Proof. exact (EQ_MP (@lem1393121 x y h1) (@lem1388328 x y h1)). Qed.
Lemma lem1393123 (x : real) (y : real) : term206 x y.
Proof. exact (fun h0 : term207 x y => @lem1393122 x y h0). Qed.
Lemma lem1393124 (x : real) (y : real) : term204 x y.
Proof. exact (EQ_MP (@lem1388327 x y) (@lem1393123 x y)). Qed.
Lemma lem1393125 (x : real) (y : real) : term178 x y.
Proof. exact (EQ_MP (@lem1388323 x y) (@lem1393124 x y)). Qed.
Lemma lem1393126 (x : real) (y : real) : term183 x y.
Proof. exact (EQ_MP (@lem1388217 x y) (@lem1393125 x y)). Qed.

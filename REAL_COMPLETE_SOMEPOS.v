Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_COMPLETE_SOMEPOS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_HREAL_LEMMA2_spec.
Require Import thm0_spec.
Require Import thm1157_spec.
Require Import thm1318736_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm7_spec.
Lemma lem1347549 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347550 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1347549 h1 x). Qed.
Lemma lem1347551 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1347552 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1347551 x) (@lem1347550 x h1)). Qed.
Lemma lem1347553 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1347552 x h1 y). Qed.
Lemma lem1347554 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1347555 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1347554 y x) (@lem1347553 x y h1)). Qed.
Lemma lem1347556 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1347555 y x h1 z). Qed.
Lemma lem1347557 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1347558 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1347557 y x z) (@lem1347556 y x z h1)). Qed.
Lemma lem1347559 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1347560 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem1347558 y x z h1 (@lem1347559 x y z h2)). Qed.
Lemma lem1347561 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1347560 x y z h0 h1). Qed.
Lemma lem1347562 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1347563 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1347562 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1347561 x y z h0)). Qed.
Lemma lem1347564 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347565 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem1347563 x z h2 (@lem1347564 h1)). Qed.
Lemma lem1347566 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1347565 x z h1 h0). Qed.
Lemma lem1347567 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1347566 x z h1). Qed.
Lemma lem1347568 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1347567 x h1). Qed.
Lemma lem1347569 : term14.
Proof. exact (fun h0 : term0 => @lem1347568 h0). Qed.
Lemma lem1347570 : term13.
Proof. exact (@lem1347569 (@lem1339577)). Qed.
Lemma lem1347571 (x : real) : term15 x.
Proof. exact (@lem1347570 x). Qed.
Lemma lem1347572 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1347573 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1347572 x) (@lem1347571 x)). Qed.
Lemma lem1347574 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1347573 x z). Qed.
Lemma lem1347575 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1347577 (a : Prop) (b : Prop) (h1 : term17 a b) : term17 a b.
Proof. exact (h1). Qed.
Lemma lem1347578 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1347579 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term17 a b) : a -> b.
Proof. exact (@lem1347577 a b h2 (@lem1347578 a b h1)). Qed.
Lemma lem1347580 (a : Prop) (b : Prop) (h1 : a = b) : term18 a b.
Proof. exact (fun h0 : term17 a b => @lem1347579 a b h1 h0). Qed.
Lemma lem1347581 (a : Prop) (b : Prop) (h1 : term17 a b) : term17 a b.
Proof. exact (h1). Qed.
Lemma lem1347582 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term17 a b) : a -> b.
Proof. exact (@lem1347580 a b h1 (@lem1347581 a b h2)). Qed.
Lemma lem1347583 (a : Prop) (b : Prop) (h1 : term17 a b) : term17 a b.
Proof. exact (fun h0 : a = b => @lem1347582 a b h0 h1). Qed.
Lemma lem1347584 (a : Prop) (b : Prop) : term19 a b.
Proof. exact (fun h0 : term17 a b => @lem1347583 a b h0). Qed.
Lemma lem1347586 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347587 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1347586 h1 x). Qed.
Lemma lem1347588 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1347589 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1347588 x) (@lem1347587 x h1)). Qed.
Lemma lem1347590 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1347589 x h1 y). Qed.
Lemma lem1347591 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1347592 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1347591 y x) (@lem1347590 x y h1)). Qed.
Lemma lem1347593 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1347592 y x h1 z). Qed.
Lemma lem1347594 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1347595 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1347594 y x z) (@lem1347593 y x z h1)). Qed.
Lemma lem1347596 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1347597 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem1347595 y x z h1 (@lem1347596 x y z h2)). Qed.
Lemma lem1347598 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1347597 x y z h0 h1). Qed.
Lemma lem1347599 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1347600 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1347599 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1347598 x y z h0)). Qed.
Lemma lem1347601 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347602 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem1347600 x z h2 (@lem1347601 h1)). Qed.
Lemma lem1347603 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1347602 x z h1 h0). Qed.
Lemma lem1347604 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1347603 x z h1). Qed.
Lemma lem1347605 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1347604 x h1). Qed.
Lemma lem1347606 : term14.
Proof. exact (fun h0 : term0 => @lem1347605 h0). Qed.
Lemma lem1347607 : term13.
Proof. exact (@lem1347606 (@lem1339577)). Qed.
Lemma lem1347608 (x : real) : term15 x.
Proof. exact (@lem1347607 x). Qed.
Lemma lem1347609 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1347610 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1347609 x) (@lem1347608 x)). Qed.
Lemma lem1347611 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1347610 x z). Qed.
Lemma lem1347612 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1347624 (b : Prop) : term20 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem1347625 (b : Prop) : (term20 b) = (term21 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem1347626 (b : Prop) : term21 b.
Proof. exact (EQ_MP (@lem1347625 b) (@lem1347624 b)). Qed.
Lemma lem1347627 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem1347628 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem1347639 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1347640 (a : Prop) (b : Prop) (h1 : b = True) : (term23 a b) = (term24 a).
Proof. exact (MK_COMB (@lem1347639 a) (@lem1347627 b h1)). Qed.
Lemma lem1347641 (a : Prop) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem1347642 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1347643 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term23 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1347642 a b) (@lem1347641 a)). Qed.
Lemma lem1347644 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1347645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347646 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1347645) (@lem1347644 a b)). Qed.
Lemma lem1347647 (a : Prop) : (term25 a) = (term25 a).
Proof. exact (eq_refl (term25 a)). Qed.
Lemma lem1347648 (b : Prop) (a : Prop) : ((term23 a b) = (term25 a)) = ((term27 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1347646 a b) (@lem1347647 a)). Qed.
Lemma lem1347649 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term27 a b) = (term25 a)).
Proof. exact (TRANS (@lem1347643 b a) (@lem1347648 b a)). Qed.
Lemma lem1347650 (a : Prop) (b : Prop) (h1 : b = True) : (term27 a b) = (term25 a).
Proof. exact (EQ_MP (@lem1347649 b a) (@lem1347640 a b h1)). Qed.
Lemma lem1347651 (a : Prop) (b : Prop) (h1 : b = True) : (term25 a) = (term27 a b).
Proof. exact (SYM (@lem1347650 a b h1)). Qed.
Lemma lem1347652 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1347653 (a : Prop) (b : Prop) (h1 : b = False) : (term23 a b) = (term29 a).
Proof. exact (MK_COMB (@lem1347652 a) (@lem1347628 b h1)). Qed.
Lemma lem1347654 (a : Prop) : (term29 a) = (term30 a).
Proof. exact (eq_refl (term29 a)). Qed.
Lemma lem1347655 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1347656 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term23 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1347655 a b) (@lem1347654 a)). Qed.
Lemma lem1347657 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1347658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347659 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1347658) (@lem1347657 a b)). Qed.
Lemma lem1347660 (a : Prop) : (term30 a) = (term30 a).
Proof. exact (eq_refl (term30 a)). Qed.
Lemma lem1347661 (b : Prop) (a : Prop) : ((term23 a b) = (term30 a)) = ((term27 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1347659 a b) (@lem1347660 a)). Qed.
Lemma lem1347662 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term27 a b) = (term30 a)).
Proof. exact (TRANS (@lem1347656 b a) (@lem1347661 b a)). Qed.
Lemma lem1347663 (a : Prop) (b : Prop) (h1 : b = False) : (term27 a b) = (term30 a).
Proof. exact (EQ_MP (@lem1347662 b a) (@lem1347653 a b h1)). Qed.
Lemma lem1347664 (a : Prop) (b : Prop) (h1 : b = False) : (term30 a) = (term27 a b).
Proof. exact (SYM (@lem1347663 a b h1)). Qed.
Lemma lem1347670 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1347671 (a : Prop) : (True = a) = a.
Proof. exact (@lem1347670 a). Qed.
Lemma lem1347672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347673 (a : Prop) : (term31 a) = (imp a).
Proof. exact (MK_COMB (@lem1347672) (@lem1347671 a)). Qed.
Lemma lem1347675 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1347676 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1347675 a). Qed.
Lemma lem1347677 (a : Prop) : (term25 a) = (a -> True).
Proof. exact (MK_COMB (@lem1347673 a) (@lem1347676 a)). Qed.
Lemma lem1347679 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1347680 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1347679 a). Qed.
Lemma lem1347681 (a : Prop) : (term25 a) = True.
Proof. exact (TRANS (@lem1347677 a) (@lem1347680 a)). Qed.
Lemma lem1347682 (a : Prop) : True = (term25 a).
Proof. exact (SYM (@lem1347681 a)). Qed.
Lemma lem1347683 (a : Prop) : term25 a.
Proof. exact (EQ_MP (@lem1347682 a) (@lem0)). Qed.
Lemma lem1347689 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1347690 (a : Prop) : (False = a) = (~ a).
Proof. exact (@lem1347689 a). Qed.
Lemma lem1347691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347692 (a : Prop) : (term32 a) = (term33 a).
Proof. exact (MK_COMB (@lem1347691) (@lem1347690 a)). Qed.
Lemma lem1347694 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1347695 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1347694 a). Qed.
Lemma lem1347696 (a : Prop) : (term30 a) = (term34 a).
Proof. exact (MK_COMB (@lem1347692 a) (@lem1347695 a)). Qed.
Lemma lem1347698 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1347699 (a : Prop) : (term34 a) = True.
Proof. exact (@lem1347698 (~ a)). Qed.
Lemma lem1347700 (a : Prop) : (term30 a) = True.
Proof. exact (TRANS (@lem1347696 a) (@lem1347699 a)). Qed.
Lemma lem1347701 (a : Prop) : True = (term30 a).
Proof. exact (SYM (@lem1347700 a)). Qed.
Lemma lem1347702 (a : Prop) : term30 a.
Proof. exact (EQ_MP (@lem1347701 a) (@lem0)). Qed.
Lemma lem1347703 (a : Prop) (b : Prop) (h1 : b = False) : term27 a b.
Proof. exact (EQ_MP (@lem1347664 a b h1) (@lem1347702 a)). Qed.
Lemma lem1347704 (a : Prop) (b : Prop) (h1 : b = True) : term27 a b.
Proof. exact (EQ_MP (@lem1347651 a b h1) (@lem1347683 a)). Qed.
Lemma lem1347707 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (or_elim (@lem1347626 b) (fun h0 : b = True => @lem1347704 a b h0) (fun h0 : b = False => @lem1347703 a b h0)). Qed.
Lemma lem1347708 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1347709 (b : Prop) (a : Prop) (h1 : b = a) : b = a.
Proof. exact (h1). Qed.
Lemma lem1347710 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1347708 a b h2 (@lem1347709 b a h1)). Qed.
Lemma lem1347711 (b : Prop) (a : Prop) (h1 : b = a) : term35 a b.
Proof. exact (fun h0 : term27 a b => @lem1347710 a b h1 h0). Qed.
Lemma lem1347712 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1347713 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1347711 b a h1 (@lem1347712 a b h2)). Qed.
Lemma lem1347714 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (fun h0 : b = a => @lem1347713 a b h0 h1). Qed.
Lemma lem1347715 (a : Prop) (b : Prop) : term36 a b.
Proof. exact (fun h0 : term27 a b => @lem1347714 a b h0). Qed.
Lemma lem1347717 (z : real) (h1 : term37 z) : term37 z.
Proof. exact (h1). Qed.
Lemma lem1347718 : term38.
Proof. exact (@lem1339697 term39). Qed.
Lemma lem1347719 : term38 = term40.
Proof. exact (eq_refl term38). Qed.
Lemma lem1347720 : term40.
Proof. exact (EQ_MP (@lem1347719) (@lem1347718)). Qed.
Lemma lem1347721 (z : real) : term41 z.
Proof. exact (@lem1347720 z). Qed.
Lemma lem1347722 (z : real) : (term41 z) = (term42 z).
Proof. exact (eq_refl (term41 z)). Qed.
Lemma lem1347723 (z : real) : term42 z.
Proof. exact (EQ_MP (@lem1347722 z) (@lem1347721 z)). Qed.
Lemma lem1347724 (z : real) (h1 : term37 z) : term37 z.
Proof. exact (h1). Qed.
Lemma lem1347725 (z : real) (h1 : term43 z) : term43 z.
Proof. exact (h1). Qed.
Lemma lem1347738 (b : Prop) : term20 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem1347739 (b : Prop) : (term20 b) = (term21 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem1347740 (b : Prop) : term21 b.
Proof. exact (EQ_MP (@lem1347739 b) (@lem1347738 b)). Qed.
Lemma lem1347741 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem1347742 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem1347755 (a : Prop) (c : Prop) : (term44 a c) = (term44 a c).
Proof. exact (eq_refl (term44 a c)). Qed.
Lemma lem1347756 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term45 a c b) = (term46 a c).
Proof. exact (MK_COMB (@lem1347755 a c) (@lem1347741 b h1)). Qed.
Lemma lem1347757 (a : Prop) (c : Prop) : (term46 a c) = (term47 a c).
Proof. exact (eq_refl (term46 a c)). Qed.
Lemma lem1347758 (a : Prop) (c : Prop) (b : Prop) : (term48 a c b) = (term48 a c b).
Proof. exact (eq_refl (term48 a c b)). Qed.
Lemma lem1347759 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term46 a c)) = ((term45 a c b) = (term47 a c)).
Proof. exact (MK_COMB (@lem1347758 a c b) (@lem1347757 a c)). Qed.
Lemma lem1347760 (a : Prop) (b : Prop) (c : Prop) : (term45 a c b) = (term49 a b c).
Proof. exact (eq_refl (term45 a c b)). Qed.
Lemma lem1347761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347762 (a : Prop) (b : Prop) (c : Prop) : (term48 a c b) = (term50 a b c).
Proof. exact (MK_COMB (@lem1347761) (@lem1347760 a b c)). Qed.
Lemma lem1347763 (a : Prop) (c : Prop) : (term47 a c) = (term47 a c).
Proof. exact (eq_refl (term47 a c)). Qed.
Lemma lem1347764 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term47 a c)) = ((term49 a b c) = (term47 a c)).
Proof. exact (MK_COMB (@lem1347762 a b c) (@lem1347763 a c)). Qed.
Lemma lem1347765 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term46 a c)) = ((term49 a b c) = (term47 a c)).
Proof. exact (TRANS (@lem1347759 b a c) (@lem1347764 b a c)). Qed.
Lemma lem1347766 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term49 a b c) = (term47 a c).
Proof. exact (EQ_MP (@lem1347765 b a c) (@lem1347756 a c b h1)). Qed.
Lemma lem1347767 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term47 a c) = (term49 a b c).
Proof. exact (SYM (@lem1347766 a c b h1)). Qed.
Lemma lem1347768 (a : Prop) (c : Prop) : (term44 a c) = (term44 a c).
Proof. exact (eq_refl (term44 a c)). Qed.
Lemma lem1347769 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term45 a c b) = (term51 a c).
Proof. exact (MK_COMB (@lem1347768 a c) (@lem1347742 b h1)). Qed.
Lemma lem1347770 (a : Prop) (c : Prop) : (term51 a c) = (term52 a c).
Proof. exact (eq_refl (term51 a c)). Qed.
Lemma lem1347771 (a : Prop) (c : Prop) (b : Prop) : (term48 a c b) = (term48 a c b).
Proof. exact (eq_refl (term48 a c b)). Qed.
Lemma lem1347772 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term51 a c)) = ((term45 a c b) = (term52 a c)).
Proof. exact (MK_COMB (@lem1347771 a c b) (@lem1347770 a c)). Qed.
Lemma lem1347773 (a : Prop) (b : Prop) (c : Prop) : (term45 a c b) = (term49 a b c).
Proof. exact (eq_refl (term45 a c b)). Qed.
Lemma lem1347774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347775 (a : Prop) (b : Prop) (c : Prop) : (term48 a c b) = (term50 a b c).
Proof. exact (MK_COMB (@lem1347774) (@lem1347773 a b c)). Qed.
Lemma lem1347776 (a : Prop) (c : Prop) : (term52 a c) = (term52 a c).
Proof. exact (eq_refl (term52 a c)). Qed.
Lemma lem1347777 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term52 a c)) = ((term49 a b c) = (term52 a c)).
Proof. exact (MK_COMB (@lem1347775 a b c) (@lem1347776 a c)). Qed.
Lemma lem1347778 (b : Prop) (a : Prop) (c : Prop) : ((term45 a c b) = (term51 a c)) = ((term49 a b c) = (term52 a c)).
Proof. exact (TRANS (@lem1347772 b a c) (@lem1347777 b a c)). Qed.
Lemma lem1347779 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term49 a b c) = (term52 a c).
Proof. exact (EQ_MP (@lem1347778 b a c) (@lem1347769 a c b h1)). Qed.
Lemma lem1347780 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term52 a c) = (term49 a b c).
Proof. exact (SYM (@lem1347779 a c b h1)). Qed.
Lemma lem1347784 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1347785 (c : Prop) : (True -> c) = c.
Proof. exact (@lem1347784 c). Qed.
Lemma lem1347786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347787 (c : Prop) : (term53 c) = (imp c).
Proof. exact (MK_COMB (@lem1347786) (@lem1347785 c)). Qed.
Lemma lem1347793 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1347794 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1347793 a). Qed.
Lemma lem1347795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347796 (a : Prop) : (term54 a) = (imp True).
Proof. exact (MK_COMB (@lem1347795) (@lem1347794 a)). Qed.
Lemma lem1347797 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1347798 (a : Prop) (c : Prop) : (term55 a c) = (True -> c).
Proof. exact (MK_COMB (@lem1347796 a) (@lem1347797 c)). Qed.
Lemma lem1347800 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1347801 (c : Prop) : (True -> c) = c.
Proof. exact (@lem1347800 c). Qed.
Lemma lem1347802 (a : Prop) (c : Prop) : (term55 a c) = c.
Proof. exact (TRANS (@lem1347798 a c) (@lem1347801 c)). Qed.
Lemma lem1347803 (a : Prop) : (imp a) = (imp a).
Proof. exact (eq_refl (imp a)). Qed.
Lemma lem1347804 (a : Prop) (c : Prop) : (term56 a c) = (a -> c).
Proof. exact (MK_COMB (@lem1347803 a) (@lem1347802 a c)). Qed.
Lemma lem1347807 (a : Prop) (c : Prop) : (term47 a c) = (term57 a c).
Proof. exact (MK_COMB (@lem1347787 c) (@lem1347804 a c)). Qed.
Lemma lem1347810 (a : Prop) (c : Prop) : (term57 a c) = (term47 a c).
Proof. exact (SYM (@lem1347807 a c)). Qed.
Lemma lem1347811 (c : Prop) : term20 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem1347812 (c : Prop) : (term20 c) = (term21 c).
Proof. exact (eq_refl (term20 c)). Qed.
Lemma lem1347813 (c : Prop) : term21 c.
Proof. exact (EQ_MP (@lem1347812 c) (@lem1347811 c)). Qed.
Lemma lem1347814 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem1347815 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem1347822 (a : Prop) : (term58 a) = (term58 a).
Proof. exact (eq_refl (term58 a)). Qed.
Lemma lem1347823 (a : Prop) (c : Prop) (h1 : c = True) : (term59 a c) = (term60 a).
Proof. exact (MK_COMB (@lem1347822 a) (@lem1347814 c h1)). Qed.
Lemma lem1347824 (a : Prop) : (term60 a) = (term61 a).
Proof. exact (eq_refl (term60 a)). Qed.
Lemma lem1347825 (a : Prop) (c : Prop) : (term62 a c) = (term62 a c).
Proof. exact (eq_refl (term62 a c)). Qed.
Lemma lem1347826 (c : Prop) (a : Prop) : ((term59 a c) = (term60 a)) = ((term59 a c) = (term61 a)).
Proof. exact (MK_COMB (@lem1347825 a c) (@lem1347824 a)). Qed.
Lemma lem1347827 (a : Prop) (c : Prop) : (term59 a c) = (term57 a c).
Proof. exact (eq_refl (term59 a c)). Qed.
Lemma lem1347828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347829 (a : Prop) (c : Prop) : (term62 a c) = (term63 a c).
Proof. exact (MK_COMB (@lem1347828) (@lem1347827 a c)). Qed.
Lemma lem1347830 (a : Prop) : (term61 a) = (term61 a).
Proof. exact (eq_refl (term61 a)). Qed.
Lemma lem1347831 (c : Prop) (a : Prop) : ((term59 a c) = (term61 a)) = ((term57 a c) = (term61 a)).
Proof. exact (MK_COMB (@lem1347829 a c) (@lem1347830 a)). Qed.
Lemma lem1347832 (c : Prop) (a : Prop) : ((term59 a c) = (term60 a)) = ((term57 a c) = (term61 a)).
Proof. exact (TRANS (@lem1347826 c a) (@lem1347831 c a)). Qed.
Lemma lem1347833 (a : Prop) (c : Prop) (h1 : c = True) : (term57 a c) = (term61 a).
Proof. exact (EQ_MP (@lem1347832 c a) (@lem1347823 a c h1)). Qed.
Lemma lem1347834 (a : Prop) (c : Prop) (h1 : c = True) : (term61 a) = (term57 a c).
Proof. exact (SYM (@lem1347833 a c h1)). Qed.
Lemma lem1347835 (a : Prop) : (term58 a) = (term58 a).
Proof. exact (eq_refl (term58 a)). Qed.
Lemma lem1347836 (a : Prop) (c : Prop) (h1 : c = False) : (term59 a c) = (term64 a).
Proof. exact (MK_COMB (@lem1347835 a) (@lem1347815 c h1)). Qed.
Lemma lem1347837 (a : Prop) : (term64 a) = (term65 a).
Proof. exact (eq_refl (term64 a)). Qed.
Lemma lem1347838 (a : Prop) (c : Prop) : (term62 a c) = (term62 a c).
Proof. exact (eq_refl (term62 a c)). Qed.
Lemma lem1347839 (c : Prop) (a : Prop) : ((term59 a c) = (term64 a)) = ((term59 a c) = (term65 a)).
Proof. exact (MK_COMB (@lem1347838 a c) (@lem1347837 a)). Qed.
Lemma lem1347840 (a : Prop) (c : Prop) : (term59 a c) = (term57 a c).
Proof. exact (eq_refl (term59 a c)). Qed.
Lemma lem1347841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347842 (a : Prop) (c : Prop) : (term62 a c) = (term63 a c).
Proof. exact (MK_COMB (@lem1347841) (@lem1347840 a c)). Qed.
Lemma lem1347843 (a : Prop) : (term65 a) = (term65 a).
Proof. exact (eq_refl (term65 a)). Qed.
Lemma lem1347844 (c : Prop) (a : Prop) : ((term59 a c) = (term65 a)) = ((term57 a c) = (term65 a)).
Proof. exact (MK_COMB (@lem1347842 a c) (@lem1347843 a)). Qed.
Lemma lem1347845 (c : Prop) (a : Prop) : ((term59 a c) = (term64 a)) = ((term57 a c) = (term65 a)).
Proof. exact (TRANS (@lem1347839 c a) (@lem1347844 c a)). Qed.
Lemma lem1347846 (a : Prop) (c : Prop) (h1 : c = False) : (term57 a c) = (term65 a).
Proof. exact (EQ_MP (@lem1347845 c a) (@lem1347836 a c h1)). Qed.
Lemma lem1347847 (a : Prop) (c : Prop) (h1 : c = False) : (term65 a) = (term57 a c).
Proof. exact (SYM (@lem1347846 a c h1)). Qed.
Lemma lem1347849 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1347850 (a : Prop) : (term61 a) = (a -> True).
Proof. exact (@lem1347849 (a -> True)). Qed.
Lemma lem1347852 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1347853 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1347852 a). Qed.
Lemma lem1347854 (a : Prop) : (term61 a) = True.
Proof. exact (TRANS (@lem1347850 a) (@lem1347853 a)). Qed.
Lemma lem1347855 (a : Prop) : True = (term61 a).
Proof. exact (SYM (@lem1347854 a)). Qed.
Lemma lem1347856 (a : Prop) : term61 a.
Proof. exact (EQ_MP (@lem1347855 a) (@lem0)). Qed.
Lemma lem1347858 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1347859 (a : Prop) : (term65 a) = True.
Proof. exact (@lem1347858 (a -> False)). Qed.
Lemma lem1347860 (a : Prop) : True = (term65 a).
Proof. exact (SYM (@lem1347859 a)). Qed.
Lemma lem1347861 (a : Prop) : term65 a.
Proof. exact (EQ_MP (@lem1347860 a) (@lem0)). Qed.
Lemma lem1347862 (a : Prop) (c : Prop) (h1 : c = False) : term57 a c.
Proof. exact (EQ_MP (@lem1347847 a c h1) (@lem1347861 a)). Qed.
Lemma lem1347863 (a : Prop) (c : Prop) (h1 : c = True) : term57 a c.
Proof. exact (EQ_MP (@lem1347834 a c h1) (@lem1347856 a)). Qed.
Lemma lem1347865 (a : Prop) (c : Prop) : term57 a c.
Proof. exact (or_elim (@lem1347813 c) (fun h0 : c = True => @lem1347863 a c h0) (fun h0 : c = False => @lem1347862 a c h0)). Qed.
Lemma lem1347866 (a : Prop) (c : Prop) : term47 a c.
Proof. exact (EQ_MP (@lem1347810 a c) (@lem1347865 a c)). Qed.
Lemma lem1347870 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1347871 (c : Prop) : (False -> c) = True.
Proof. exact (@lem1347870 c). Qed.
Lemma lem1347872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347873 (c : Prop) : (term66 c) = (imp True).
Proof. exact (MK_COMB (@lem1347872) (@lem1347871 c)). Qed.
Lemma lem1347879 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1347880 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1347879 a). Qed.
Lemma lem1347881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347882 (a : Prop) : (term67 a) = (term33 a).
Proof. exact (MK_COMB (@lem1347881) (@lem1347880 a)). Qed.
Lemma lem1347883 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1347884 (a : Prop) (c : Prop) : (term68 a c) = (term69 a c).
Proof. exact (MK_COMB (@lem1347882 a) (@lem1347883 c)). Qed.
Lemma lem1347887 (a : Prop) : (imp a) = (imp a).
Proof. exact (eq_refl (imp a)). Qed.
Lemma lem1347888 (a : Prop) (c : Prop) : (term70 a c) = (term71 a c).
Proof. exact (MK_COMB (@lem1347887 a) (@lem1347884 a c)). Qed.
Lemma lem1347891 (a : Prop) (c : Prop) : (term52 a c) = (term72 a c).
Proof. exact (MK_COMB (@lem1347873 c) (@lem1347888 a c)). Qed.
Lemma lem1347893 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1347894 (a : Prop) (c : Prop) : (term72 a c) = (term71 a c).
Proof. exact (@lem1347893 (term71 a c)). Qed.
Lemma lem1347899 (a : Prop) (c : Prop) : (term52 a c) = (term71 a c).
Proof. exact (TRANS (@lem1347891 a c) (@lem1347894 a c)). Qed.
Lemma lem1347900 (a : Prop) (c : Prop) : (term71 a c) = (term52 a c).
Proof. exact (SYM (@lem1347899 a c)). Qed.
Lemma lem1347901 (a : Prop) : term20 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1347902 (a : Prop) : (term20 a) = (term21 a).
Proof. exact (eq_refl (term20 a)). Qed.
Lemma lem1347903 (a : Prop) : term21 a.
Proof. exact (EQ_MP (@lem1347902 a) (@lem1347901 a)). Qed.
Lemma lem1347904 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1347905 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1347912 (c : Prop) : (term73 c) = (term73 c).
Proof. exact (eq_refl (term73 c)). Qed.
Lemma lem1347913 (c : Prop) (a : Prop) (h1 : a = True) : (term74 c a) = (term75 c).
Proof. exact (MK_COMB (@lem1347912 c) (@lem1347904 a h1)). Qed.
Lemma lem1347914 (c : Prop) : (term75 c) = (term76 c).
Proof. exact (eq_refl (term75 c)). Qed.
Lemma lem1347915 (c : Prop) (a : Prop) : (term77 c a) = (term77 c a).
Proof. exact (eq_refl (term77 c a)). Qed.
Lemma lem1347916 (a : Prop) (c : Prop) : ((term74 c a) = (term75 c)) = ((term74 c a) = (term76 c)).
Proof. exact (MK_COMB (@lem1347915 c a) (@lem1347914 c)). Qed.
Lemma lem1347917 (a : Prop) (c : Prop) : (term74 c a) = (term71 a c).
Proof. exact (eq_refl (term74 c a)). Qed.
Lemma lem1347918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347919 (a : Prop) (c : Prop) : (term77 c a) = (term78 a c).
Proof. exact (MK_COMB (@lem1347918) (@lem1347917 a c)). Qed.
Lemma lem1347920 (c : Prop) : (term76 c) = (term76 c).
Proof. exact (eq_refl (term76 c)). Qed.
Lemma lem1347921 (a : Prop) (c : Prop) : ((term74 c a) = (term76 c)) = ((term71 a c) = (term76 c)).
Proof. exact (MK_COMB (@lem1347919 a c) (@lem1347920 c)). Qed.
Lemma lem1347922 (a : Prop) (c : Prop) : ((term74 c a) = (term75 c)) = ((term71 a c) = (term76 c)).
Proof. exact (TRANS (@lem1347916 a c) (@lem1347921 a c)). Qed.
Lemma lem1347923 (c : Prop) (a : Prop) (h1 : a = True) : (term71 a c) = (term76 c).
Proof. exact (EQ_MP (@lem1347922 a c) (@lem1347913 c a h1)). Qed.
Lemma lem1347924 (c : Prop) (a : Prop) (h1 : a = True) : (term76 c) = (term71 a c).
Proof. exact (SYM (@lem1347923 c a h1)). Qed.
Lemma lem1347925 (c : Prop) : (term73 c) = (term73 c).
Proof. exact (eq_refl (term73 c)). Qed.
Lemma lem1347926 (c : Prop) (a : Prop) (h1 : a = False) : (term74 c a) = (term79 c).
Proof. exact (MK_COMB (@lem1347925 c) (@lem1347905 a h1)). Qed.
Lemma lem1347927 (c : Prop) : (term79 c) = (term80 c).
Proof. exact (eq_refl (term79 c)). Qed.
Lemma lem1347928 (c : Prop) (a : Prop) : (term77 c a) = (term77 c a).
Proof. exact (eq_refl (term77 c a)). Qed.
Lemma lem1347929 (a : Prop) (c : Prop) : ((term74 c a) = (term79 c)) = ((term74 c a) = (term80 c)).
Proof. exact (MK_COMB (@lem1347928 c a) (@lem1347927 c)). Qed.
Lemma lem1347930 (a : Prop) (c : Prop) : (term74 c a) = (term71 a c).
Proof. exact (eq_refl (term74 c a)). Qed.
Lemma lem1347931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347932 (a : Prop) (c : Prop) : (term77 c a) = (term78 a c).
Proof. exact (MK_COMB (@lem1347931) (@lem1347930 a c)). Qed.
Lemma lem1347933 (c : Prop) : (term80 c) = (term80 c).
Proof. exact (eq_refl (term80 c)). Qed.
Lemma lem1347934 (a : Prop) (c : Prop) : ((term74 c a) = (term80 c)) = ((term71 a c) = (term80 c)).
Proof. exact (MK_COMB (@lem1347932 a c) (@lem1347933 c)). Qed.
Lemma lem1347935 (a : Prop) (c : Prop) : ((term74 c a) = (term79 c)) = ((term71 a c) = (term80 c)).
Proof. exact (TRANS (@lem1347929 a c) (@lem1347934 a c)). Qed.
Lemma lem1347936 (c : Prop) (a : Prop) (h1 : a = False) : (term71 a c) = (term80 c).
Proof. exact (EQ_MP (@lem1347935 a c) (@lem1347926 c a h1)). Qed.
Lemma lem1347937 (c : Prop) (a : Prop) (h1 : a = False) : (term80 c) = (term71 a c).
Proof. exact (SYM (@lem1347936 c a h1)). Qed.
Lemma lem1347939 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1347940 (c : Prop) : (term76 c) = (term81 c).
Proof. exact (@lem1347939 (term81 c)). Qed.
Lemma lem1347944 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1347945 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347946 : term82 = (imp False).
Proof. exact (MK_COMB (@lem1347945) (@lem1347944)). Qed.
Lemma lem1347947 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1347948 (c : Prop) : (term81 c) = (False -> c).
Proof. exact (MK_COMB (@lem1347946) (@lem1347947 c)). Qed.
Lemma lem1347950 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1347951 (c : Prop) : (False -> c) = True.
Proof. exact (@lem1347950 c). Qed.
Lemma lem1347952 (c : Prop) : (term81 c) = True.
Proof. exact (TRANS (@lem1347948 c) (@lem1347951 c)). Qed.
Lemma lem1347953 (c : Prop) : (term76 c) = True.
Proof. exact (TRANS (@lem1347940 c) (@lem1347952 c)). Qed.
Lemma lem1347954 (c : Prop) : True = (term76 c).
Proof. exact (SYM (@lem1347953 c)). Qed.
Lemma lem1347955 (c : Prop) : term76 c.
Proof. exact (EQ_MP (@lem1347954 c) (@lem0)). Qed.
Lemma lem1347957 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1347958 (c : Prop) : (term80 c) = True.
Proof. exact (@lem1347957 (term83 c)). Qed.
Lemma lem1347959 (c : Prop) : True = (term80 c).
Proof. exact (SYM (@lem1347958 c)). Qed.
Lemma lem1347960 (c : Prop) : term80 c.
Proof. exact (EQ_MP (@lem1347959 c) (@lem0)). Qed.
Lemma lem1347961 (c : Prop) (a : Prop) (h1 : a = False) : term71 a c.
Proof. exact (EQ_MP (@lem1347937 c a h1) (@lem1347960 c)). Qed.
Lemma lem1347962 (c : Prop) (a : Prop) (h1 : a = True) : term71 a c.
Proof. exact (EQ_MP (@lem1347924 c a h1) (@lem1347955 c)). Qed.
Lemma lem1347964 (a : Prop) (c : Prop) : term71 a c.
Proof. exact (or_elim (@lem1347903 a) (fun h0 : a = True => @lem1347962 c a h0) (fun h0 : a = False => @lem1347961 c a h0)). Qed.
Lemma lem1347965 (a : Prop) (c : Prop) : term52 a c.
Proof. exact (EQ_MP (@lem1347900 a c) (@lem1347964 a c)). Qed.
Lemma lem1347966 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : term49 a b c.
Proof. exact (EQ_MP (@lem1347780 a c b h1) (@lem1347965 a c)). Qed.
Lemma lem1347967 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : term49 a b c.
Proof. exact (EQ_MP (@lem1347767 a c b h1) (@lem1347866 a c)). Qed.
Lemma lem1347970 (a : Prop) (b : Prop) (c : Prop) : term49 a b c.
Proof. exact (or_elim (@lem1347740 b) (fun h0 : b = True => @lem1347967 a c b h0) (fun h0 : b = False => @lem1347966 a c b h0)). Qed.
Lemma lem1347971 (a : Prop) (b : Prop) (c : Prop) (h1 : term49 a b c) : term49 a b c.
Proof. exact (h1). Qed.
Lemma lem1347972 (b : Prop) (c : Prop) (h1 : b -> c) : b -> c.
Proof. exact (h1). Qed.
Lemma lem1347973 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) (h2 : term49 a b c) : term84 a b c.
Proof. exact (@lem1347971 a b c h2 (@lem1347972 b c h1)). Qed.
Lemma lem1347974 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) : term85 a b c.
Proof. exact (fun h0 : term49 a b c => @lem1347973 a b c h1 h0). Qed.
Lemma lem1347975 (a : Prop) (b : Prop) (c : Prop) (h1 : term49 a b c) : term49 a b c.
Proof. exact (h1). Qed.
Lemma lem1347976 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) (h2 : term49 a b c) : term84 a b c.
Proof. exact (@lem1347974 a b c h1 (@lem1347975 a b c h2)). Qed.
Lemma lem1347977 (a : Prop) (b : Prop) (c : Prop) (h1 : term49 a b c) : term49 a b c.
Proof. exact (fun h0 : b -> c => @lem1347976 a b c h0 h1). Qed.
Lemma lem1347978 (a : Prop) (b : Prop) (c : Prop) : term86 a b c.
Proof. exact (fun h0 : term49 a b c => @lem1347977 a b c h0). Qed.
Lemma lem1347980 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347981 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1347980 h1 x). Qed.
Lemma lem1347982 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1347983 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1347982 x) (@lem1347981 x h1)). Qed.
Lemma lem1347984 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1347983 x h1 y). Qed.
Lemma lem1347985 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1347986 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1347985 y x) (@lem1347984 x y h1)). Qed.
Lemma lem1347987 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1347986 y x h1 z). Qed.
Lemma lem1347988 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1347989 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1347988 y x z) (@lem1347987 y x z h1)). Qed.
Lemma lem1347990 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1347991 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem1347989 y x z h1 (@lem1347990 x y z h2)). Qed.
Lemma lem1347992 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1347991 x y z h0 h1). Qed.
Lemma lem1347993 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1347994 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1347993 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1347992 x y z h0)). Qed.
Lemma lem1347995 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1347996 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem1347994 x z h2 (@lem1347995 h1)). Qed.
Lemma lem1347997 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1347996 x z h1 h0). Qed.
Lemma lem1347998 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1347997 x z h1). Qed.
Lemma lem1347999 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1347998 x h1). Qed.
Lemma lem1348000 : term14.
Proof. exact (fun h0 : term0 => @lem1347999 h0). Qed.
Lemma lem1348001 : term13.
Proof. exact (@lem1348000 (@lem1339577)). Qed.
Lemma lem1348002 (x : real) : term15 x.
Proof. exact (@lem1348001 x). Qed.
Lemma lem1348003 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1348004 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1348003 x) (@lem1348002 x)). Qed.
Lemma lem1348005 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1348004 x z). Qed.
Lemma lem1348006 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1348018 (b : Prop) : term20 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem1348019 (b : Prop) : (term20 b) = (term21 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem1348020 (b : Prop) : term21 b.
Proof. exact (EQ_MP (@lem1348019 b) (@lem1348018 b)). Qed.
Lemma lem1348021 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem1348022 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem1348033 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1348034 (a : Prop) (b : Prop) (h1 : b = True) : (term23 a b) = (term24 a).
Proof. exact (MK_COMB (@lem1348033 a) (@lem1348021 b h1)). Qed.
Lemma lem1348035 (a : Prop) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem1348036 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1348037 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term23 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1348036 a b) (@lem1348035 a)). Qed.
Lemma lem1348038 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1348039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1348040 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1348039) (@lem1348038 a b)). Qed.
Lemma lem1348041 (a : Prop) : (term25 a) = (term25 a).
Proof. exact (eq_refl (term25 a)). Qed.
Lemma lem1348042 (b : Prop) (a : Prop) : ((term23 a b) = (term25 a)) = ((term27 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1348040 a b) (@lem1348041 a)). Qed.
Lemma lem1348043 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term27 a b) = (term25 a)).
Proof. exact (TRANS (@lem1348037 b a) (@lem1348042 b a)). Qed.
Lemma lem1348044 (a : Prop) (b : Prop) (h1 : b = True) : (term27 a b) = (term25 a).
Proof. exact (EQ_MP (@lem1348043 b a) (@lem1348034 a b h1)). Qed.
Lemma lem1348045 (a : Prop) (b : Prop) (h1 : b = True) : (term25 a) = (term27 a b).
Proof. exact (SYM (@lem1348044 a b h1)). Qed.
Lemma lem1348046 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1348047 (a : Prop) (b : Prop) (h1 : b = False) : (term23 a b) = (term29 a).
Proof. exact (MK_COMB (@lem1348046 a) (@lem1348022 b h1)). Qed.
Lemma lem1348048 (a : Prop) : (term29 a) = (term30 a).
Proof. exact (eq_refl (term29 a)). Qed.
Lemma lem1348049 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1348050 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term23 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1348049 a b) (@lem1348048 a)). Qed.
Lemma lem1348051 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1348052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1348053 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1348052) (@lem1348051 a b)). Qed.
Lemma lem1348054 (a : Prop) : (term30 a) = (term30 a).
Proof. exact (eq_refl (term30 a)). Qed.
Lemma lem1348055 (b : Prop) (a : Prop) : ((term23 a b) = (term30 a)) = ((term27 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1348053 a b) (@lem1348054 a)). Qed.
Lemma lem1348056 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term27 a b) = (term30 a)).
Proof. exact (TRANS (@lem1348050 b a) (@lem1348055 b a)). Qed.
Lemma lem1348057 (a : Prop) (b : Prop) (h1 : b = False) : (term27 a b) = (term30 a).
Proof. exact (EQ_MP (@lem1348056 b a) (@lem1348047 a b h1)). Qed.
Lemma lem1348058 (a : Prop) (b : Prop) (h1 : b = False) : (term30 a) = (term27 a b).
Proof. exact (SYM (@lem1348057 a b h1)). Qed.
Lemma lem1348064 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1348065 (a : Prop) : (True = a) = a.
Proof. exact (@lem1348064 a). Qed.
Lemma lem1348066 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348067 (a : Prop) : (term31 a) = (imp a).
Proof. exact (MK_COMB (@lem1348066) (@lem1348065 a)). Qed.
Lemma lem1348069 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1348070 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1348069 a). Qed.
Lemma lem1348071 (a : Prop) : (term25 a) = (a -> True).
Proof. exact (MK_COMB (@lem1348067 a) (@lem1348070 a)). Qed.
Lemma lem1348073 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1348074 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1348073 a). Qed.
Lemma lem1348075 (a : Prop) : (term25 a) = True.
Proof. exact (TRANS (@lem1348071 a) (@lem1348074 a)). Qed.
Lemma lem1348076 (a : Prop) : True = (term25 a).
Proof. exact (SYM (@lem1348075 a)). Qed.
Lemma lem1348077 (a : Prop) : term25 a.
Proof. exact (EQ_MP (@lem1348076 a) (@lem0)). Qed.
Lemma lem1348083 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1348084 (a : Prop) : (False = a) = (~ a).
Proof. exact (@lem1348083 a). Qed.
Lemma lem1348085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348086 (a : Prop) : (term32 a) = (term33 a).
Proof. exact (MK_COMB (@lem1348085) (@lem1348084 a)). Qed.
Lemma lem1348088 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1348089 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1348088 a). Qed.
Lemma lem1348090 (a : Prop) : (term30 a) = (term34 a).
Proof. exact (MK_COMB (@lem1348086 a) (@lem1348089 a)). Qed.
Lemma lem1348092 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1348093 (a : Prop) : (term34 a) = True.
Proof. exact (@lem1348092 (~ a)). Qed.
Lemma lem1348094 (a : Prop) : (term30 a) = True.
Proof. exact (TRANS (@lem1348090 a) (@lem1348093 a)). Qed.
Lemma lem1348095 (a : Prop) : True = (term30 a).
Proof. exact (SYM (@lem1348094 a)). Qed.
Lemma lem1348096 (a : Prop) : term30 a.
Proof. exact (EQ_MP (@lem1348095 a) (@lem0)). Qed.
Lemma lem1348097 (a : Prop) (b : Prop) (h1 : b = False) : term27 a b.
Proof. exact (EQ_MP (@lem1348058 a b h1) (@lem1348096 a)). Qed.
Lemma lem1348098 (a : Prop) (b : Prop) (h1 : b = True) : term27 a b.
Proof. exact (EQ_MP (@lem1348045 a b h1) (@lem1348077 a)). Qed.
Lemma lem1348101 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (or_elim (@lem1348020 b) (fun h0 : b = True => @lem1348098 a b h0) (fun h0 : b = False => @lem1348097 a b h0)). Qed.
Lemma lem1348102 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1348103 (b : Prop) (a : Prop) (h1 : b = a) : b = a.
Proof. exact (h1). Qed.
Lemma lem1348104 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1348102 a b h2 (@lem1348103 b a h1)). Qed.
Lemma lem1348105 (b : Prop) (a : Prop) (h1 : b = a) : term35 a b.
Proof. exact (fun h0 : term27 a b => @lem1348104 a b h1 h0). Qed.
Lemma lem1348106 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1348107 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1348105 b a h1 (@lem1348106 a b h2)). Qed.
Lemma lem1348108 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (fun h0 : b = a => @lem1348107 a b h0 h1). Qed.
Lemma lem1348109 (a : Prop) (b : Prop) : term36 a b.
Proof. exact (fun h0 : term27 a b => @lem1348108 a b h0). Qed.
Lemma lem1348121 (b : Prop) : term20 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem1348122 (b : Prop) : (term20 b) = (term21 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem1348123 (b : Prop) : term21 b.
Proof. exact (EQ_MP (@lem1348122 b) (@lem1348121 b)). Qed.
Lemma lem1348124 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem1348125 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem1348136 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1348137 (a : Prop) (b : Prop) (h1 : b = True) : (term23 a b) = (term24 a).
Proof. exact (MK_COMB (@lem1348136 a) (@lem1348124 b h1)). Qed.
Lemma lem1348138 (a : Prop) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem1348139 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1348140 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term23 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1348139 a b) (@lem1348138 a)). Qed.
Lemma lem1348141 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1348142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1348143 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1348142) (@lem1348141 a b)). Qed.
Lemma lem1348144 (a : Prop) : (term25 a) = (term25 a).
Proof. exact (eq_refl (term25 a)). Qed.
Lemma lem1348145 (b : Prop) (a : Prop) : ((term23 a b) = (term25 a)) = ((term27 a b) = (term25 a)).
Proof. exact (MK_COMB (@lem1348143 a b) (@lem1348144 a)). Qed.
Lemma lem1348146 (b : Prop) (a : Prop) : ((term23 a b) = (term24 a)) = ((term27 a b) = (term25 a)).
Proof. exact (TRANS (@lem1348140 b a) (@lem1348145 b a)). Qed.
Lemma lem1348147 (a : Prop) (b : Prop) (h1 : b = True) : (term27 a b) = (term25 a).
Proof. exact (EQ_MP (@lem1348146 b a) (@lem1348137 a b h1)). Qed.
Lemma lem1348148 (a : Prop) (b : Prop) (h1 : b = True) : (term25 a) = (term27 a b).
Proof. exact (SYM (@lem1348147 a b h1)). Qed.
Lemma lem1348149 (a : Prop) : (term22 a) = (term22 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem1348150 (a : Prop) (b : Prop) (h1 : b = False) : (term23 a b) = (term29 a).
Proof. exact (MK_COMB (@lem1348149 a) (@lem1348125 b h1)). Qed.
Lemma lem1348151 (a : Prop) : (term29 a) = (term30 a).
Proof. exact (eq_refl (term29 a)). Qed.
Lemma lem1348152 (a : Prop) (b : Prop) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem1348153 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term23 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1348152 a b) (@lem1348151 a)). Qed.
Lemma lem1348154 (a : Prop) (b : Prop) : (term23 a b) = (term27 a b).
Proof. exact (eq_refl (term23 a b)). Qed.
Lemma lem1348155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1348156 (a : Prop) (b : Prop) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem1348155) (@lem1348154 a b)). Qed.
Lemma lem1348157 (a : Prop) : (term30 a) = (term30 a).
Proof. exact (eq_refl (term30 a)). Qed.
Lemma lem1348158 (b : Prop) (a : Prop) : ((term23 a b) = (term30 a)) = ((term27 a b) = (term30 a)).
Proof. exact (MK_COMB (@lem1348156 a b) (@lem1348157 a)). Qed.
Lemma lem1348159 (b : Prop) (a : Prop) : ((term23 a b) = (term29 a)) = ((term27 a b) = (term30 a)).
Proof. exact (TRANS (@lem1348153 b a) (@lem1348158 b a)). Qed.
Lemma lem1348160 (a : Prop) (b : Prop) (h1 : b = False) : (term27 a b) = (term30 a).
Proof. exact (EQ_MP (@lem1348159 b a) (@lem1348150 a b h1)). Qed.
Lemma lem1348161 (a : Prop) (b : Prop) (h1 : b = False) : (term30 a) = (term27 a b).
Proof. exact (SYM (@lem1348160 a b h1)). Qed.
Lemma lem1348167 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1348168 (a : Prop) : (True = a) = a.
Proof. exact (@lem1348167 a). Qed.
Lemma lem1348169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348170 (a : Prop) : (term31 a) = (imp a).
Proof. exact (MK_COMB (@lem1348169) (@lem1348168 a)). Qed.
Lemma lem1348172 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1348173 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1348172 a). Qed.
Lemma lem1348174 (a : Prop) : (term25 a) = (a -> True).
Proof. exact (MK_COMB (@lem1348170 a) (@lem1348173 a)). Qed.
Lemma lem1348176 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1348177 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1348176 a). Qed.
Lemma lem1348178 (a : Prop) : (term25 a) = True.
Proof. exact (TRANS (@lem1348174 a) (@lem1348177 a)). Qed.
Lemma lem1348179 (a : Prop) : True = (term25 a).
Proof. exact (SYM (@lem1348178 a)). Qed.
Lemma lem1348180 (a : Prop) : term25 a.
Proof. exact (EQ_MP (@lem1348179 a) (@lem0)). Qed.
Lemma lem1348186 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1348187 (a : Prop) : (False = a) = (~ a).
Proof. exact (@lem1348186 a). Qed.
Lemma lem1348188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348189 (a : Prop) : (term32 a) = (term33 a).
Proof. exact (MK_COMB (@lem1348188) (@lem1348187 a)). Qed.
Lemma lem1348191 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1348192 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1348191 a). Qed.
Lemma lem1348193 (a : Prop) : (term30 a) = (term34 a).
Proof. exact (MK_COMB (@lem1348189 a) (@lem1348192 a)). Qed.
Lemma lem1348195 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1348196 (a : Prop) : (term34 a) = True.
Proof. exact (@lem1348195 (~ a)). Qed.
Lemma lem1348197 (a : Prop) : (term30 a) = True.
Proof. exact (TRANS (@lem1348193 a) (@lem1348196 a)). Qed.
Lemma lem1348198 (a : Prop) : True = (term30 a).
Proof. exact (SYM (@lem1348197 a)). Qed.
Lemma lem1348199 (a : Prop) : term30 a.
Proof. exact (EQ_MP (@lem1348198 a) (@lem0)). Qed.
Lemma lem1348200 (a : Prop) (b : Prop) (h1 : b = False) : term27 a b.
Proof. exact (EQ_MP (@lem1348161 a b h1) (@lem1348199 a)). Qed.
Lemma lem1348201 (a : Prop) (b : Prop) (h1 : b = True) : term27 a b.
Proof. exact (EQ_MP (@lem1348148 a b h1) (@lem1348180 a)). Qed.
Lemma lem1348204 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (or_elim (@lem1348123 b) (fun h0 : b = True => @lem1348201 a b h0) (fun h0 : b = False => @lem1348200 a b h0)). Qed.
Lemma lem1348205 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1348206 (b : Prop) (a : Prop) (h1 : b = a) : b = a.
Proof. exact (h1). Qed.
Lemma lem1348207 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1348205 a b h2 (@lem1348206 b a h1)). Qed.
Lemma lem1348208 (b : Prop) (a : Prop) (h1 : b = a) : term35 a b.
Proof. exact (fun h0 : term27 a b => @lem1348207 a b h1 h0). Qed.
Lemma lem1348209 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (h1). Qed.
Lemma lem1348210 (a : Prop) (b : Prop) (h1 : b = a) (h2 : term27 a b) : a -> b.
Proof. exact (@lem1348208 b a h1 (@lem1348209 a b h2)). Qed.
Lemma lem1348211 (a : Prop) (b : Prop) (h1 : term27 a b) : term27 a b.
Proof. exact (fun h0 : b = a => @lem1348210 a b h0 h1). Qed.
Lemma lem1348212 (a : Prop) (b : Prop) : term36 a b.
Proof. exact (fun h0 : term27 a b => @lem1348211 a b h0). Qed.
Lemma lem1348214 (P : real -> Prop) (r : hreal -> real) : term87 P r.
Proof. exact (@lem1318736 (term88 P r)). Qed.
Lemma lem1348215 (P : real -> Prop) (r : hreal -> real) : (term87 P r) = (term89 P r).
Proof. exact (eq_refl (term87 P r)). Qed.
Lemma lem1348216 (P : real -> Prop) (r : hreal -> real) : term89 P r.
Proof. exact (EQ_MP (@lem1348215 P r) (@lem1348214 P r)). Qed.
Lemma lem1348217 (P : real -> Prop) (h1 : term90 P) : term90 P.
Proof. exact (h1). Qed.
Lemma lem1348218 (P : real -> Prop) (h1 : term91 P) : term91 P.
Proof. exact (h1). Qed.
Lemma lem1348219 (P : real -> Prop) (h1 : term92 P) : term92 P.
Proof. exact (h1). Qed.
Lemma lem1348220 (P : real -> Prop) (x : real) (h1 : term93 P x) : term93 P x.
Proof. exact (h1). Qed.
Lemma lem1348221 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1348222 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1348223 (P : real -> Prop) (M : real) (h1 : term94 P M) : term94 P M.
Proof. exact (h1). Qed.
Lemma lem1348224 (h : real -> hreal) (h1 : term95 h) : term95 h.
Proof. exact (h1). Qed.
Lemma lem1348225 (h : real -> hreal) (r : hreal -> real) (h1 : term96 h r) : term96 h r.
Proof. exact (h1). Qed.
Lemma lem1348226 (h : real -> hreal) (r : hreal -> real) (h1 : term97 h r) : term97 h r.
Proof. exact (h1). Qed.
Lemma lem1348228 (r : hreal -> real) (h1 : term98 r) : term98 r.
Proof. exact (h1). Qed.
Lemma lem1348229 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348230 (r : hreal -> real) (h1 : term100 r) : term100 r.
Proof. exact (h1). Qed.
Lemma lem1348231 (r : hreal -> real) (h1 : term101 r) : term101 r.
Proof. exact (h1). Qed.
Lemma lem1348232 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term102 P r x) = (term103 P r x).
Proof. exact (eq_refl (term102 P r x)). Qed.
Lemma lem1348233 (P : real -> Prop) (r : hreal -> real) : (term104 P r) = (term88 P r).
Proof. exact (fun_ext (fun x : hreal => @lem1348232 P r x)). Qed.
Lemma lem1348234 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1348235 (P : real -> Prop) (r : hreal -> real) : (term105 P r) = (term106 P r).
Proof. exact (MK_COMB (@lem1348234) (@lem1348233 P r)). Qed.
Lemma lem1348236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1348237 (P : real -> Prop) (r : hreal -> real) : (term107 P r) = (term108 P r).
Proof. exact (MK_COMB (@lem1348236) (@lem1348235 P r)). Qed.
Lemma lem1348238 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term102 P r x) = (term103 P r x).
Proof. exact (eq_refl (term102 P r x)). Qed.
Lemma lem1348239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348240 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term109 P r x) = (term110 P r x).
Proof. exact (MK_COMB (@lem1348239) (@lem1348238 P r x)). Qed.
Lemma lem1348241 (x : hreal) (M : hreal) : (hreal_le x M) = (hreal_le x M).
Proof. exact (eq_refl (hreal_le x M)). Qed.
Lemma lem1348242 (P : real -> Prop) (r : hreal -> real) (x : hreal) (M : hreal) : (term111 P r x M) = (term112 P r x M).
Proof. exact (MK_COMB (@lem1348240 P r x) (@lem1348241 x M)). Qed.
Lemma lem1348243 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term113 P r M) = (term114 P r M).
Proof. exact (fun_ext (fun x : hreal => @lem1348242 P r x M)). Qed.
Lemma lem1348244 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348245 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term115 P r M) = (term116 P r M).
Proof. exact (MK_COMB (@lem1348244) (@lem1348243 P r M)). Qed.
Lemma lem1348246 (P : real -> Prop) (r : hreal -> real) : (term117 P r) = (term118 P r).
Proof. exact (fun_ext (fun M : hreal => @lem1348245 P r M)). Qed.
Lemma lem1348247 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1348248 (P : real -> Prop) (r : hreal -> real) : (term119 P r) = (term120 P r).
Proof. exact (MK_COMB (@lem1348247) (@lem1348246 P r)). Qed.
Lemma lem1348249 (P : real -> Prop) (r : hreal -> real) : (term121 P r) = (term122 P r).
Proof. exact (MK_COMB (@lem1348237 P r) (@lem1348248 P r)). Qed.
Lemma lem1348250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348251 (P : real -> Prop) (r : hreal -> real) : (term123 P r) = (term124 P r).
Proof. exact (MK_COMB (@lem1348250) (@lem1348249 P r)). Qed.
Lemma lem1348252 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term102 P r x) = (term103 P r x).
Proof. exact (eq_refl (term102 P r x)). Qed.
Lemma lem1348253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348254 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term109 P r x) = (term110 P r x).
Proof. exact (MK_COMB (@lem1348253) (@lem1348252 P r x)). Qed.
Lemma lem1348255 (x : hreal) (M : hreal) : (hreal_le x M) = (hreal_le x M).
Proof. exact (eq_refl (hreal_le x M)). Qed.
Lemma lem1348256 (P : real -> Prop) (r : hreal -> real) (x : hreal) (M : hreal) : (term111 P r x M) = (term112 P r x M).
Proof. exact (MK_COMB (@lem1348254 P r x) (@lem1348255 x M)). Qed.
Lemma lem1348257 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term113 P r M) = (term114 P r M).
Proof. exact (fun_ext (fun x : hreal => @lem1348256 P r x M)). Qed.
Lemma lem1348258 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348259 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term115 P r M) = (term116 P r M).
Proof. exact (MK_COMB (@lem1348258) (@lem1348257 P r M)). Qed.
Lemma lem1348260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1348261 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term125 P r M) = (term126 P r M).
Proof. exact (MK_COMB (@lem1348260) (@lem1348259 P r M)). Qed.
Lemma lem1348262 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term102 P r x) = (term103 P r x).
Proof. exact (eq_refl (term102 P r x)). Qed.
Lemma lem1348263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348264 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term109 P r x) = (term110 P r x).
Proof. exact (MK_COMB (@lem1348263) (@lem1348262 P r x)). Qed.
Lemma lem1348265 (x : hreal) (M' : hreal) : (hreal_le x M') = (hreal_le x M').
Proof. exact (eq_refl (hreal_le x M')). Qed.
Lemma lem1348266 (P : real -> Prop) (r : hreal -> real) (x : hreal) (M' : hreal) : (term111 P r x M') = (term112 P r x M').
Proof. exact (MK_COMB (@lem1348264 P r x) (@lem1348265 x M')). Qed.
Lemma lem1348267 (P : real -> Prop) (r : hreal -> real) (M' : hreal) : (term113 P r M') = (term114 P r M').
Proof. exact (fun_ext (fun x : hreal => @lem1348266 P r x M')). Qed.
Lemma lem1348268 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348269 (P : real -> Prop) (r : hreal -> real) (M' : hreal) : (term115 P r M') = (term116 P r M').
Proof. exact (MK_COMB (@lem1348268) (@lem1348267 P r M')). Qed.
Lemma lem1348270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348271 (P : real -> Prop) (r : hreal -> real) (M' : hreal) : (term127 P r M') = (term128 P r M').
Proof. exact (MK_COMB (@lem1348270) (@lem1348269 P r M')). Qed.
Lemma lem1348272 (M : hreal) (M' : hreal) : (hreal_le M M') = (hreal_le M M').
Proof. exact (eq_refl (hreal_le M M')). Qed.
Lemma lem1348273 (P : real -> Prop) (r : hreal -> real) (M : hreal) (M' : hreal) : (term129 P r M M') = (term130 P r M M').
Proof. exact (MK_COMB (@lem1348271 P r M') (@lem1348272 M M')). Qed.
Lemma lem1348274 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term131 P r M) = (term132 P r M).
Proof. exact (fun_ext (fun M' : hreal => @lem1348273 P r M M')). Qed.
Lemma lem1348275 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348276 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term133 P r M) = (term134 P r M).
Proof. exact (MK_COMB (@lem1348275) (@lem1348274 P r M)). Qed.
Lemma lem1348277 (P : real -> Prop) (r : hreal -> real) (M : hreal) : (term135 P r M) = (term136 P r M).
Proof. exact (MK_COMB (@lem1348261 P r M) (@lem1348276 P r M)). Qed.
Lemma lem1348278 (P : real -> Prop) (r : hreal -> real) : (term137 P r) = (term138 P r).
Proof. exact (fun_ext (fun M : hreal => @lem1348277 P r M)). Qed.
Lemma lem1348279 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1348280 (P : real -> Prop) (r : hreal -> real) : (term139 P r) = (term140 P r).
Proof. exact (MK_COMB (@lem1348279) (@lem1348278 P r)). Qed.
Lemma lem1348281 (P : real -> Prop) (r : hreal -> real) : (term89 P r) = (term141 P r).
Proof. exact (MK_COMB (@lem1348251 P r) (@lem1348280 P r)). Qed.
Lemma lem1348282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1348283 (P : real -> Prop) (r : hreal -> real) : (term142 P r) = (term143 P r).
Proof. exact (MK_COMB (@lem1348282) (@lem1348281 P r)). Qed.
Lemma lem1348284 (P : real -> Prop) : (term144 P) = (term144 P).
Proof. exact (eq_refl (term144 P)). Qed.
Lemma lem1348285 (r : hreal -> real) (P : real -> Prop) : (term145 r P) = (term146 r P).
Proof. exact (MK_COMB (@lem1348283 P r) (@lem1348284 P)). Qed.
Lemma lem1348286 (r : hreal -> real) (P : real -> Prop) : (term146 r P) = (term145 r P).
Proof. exact (SYM (@lem1348285 r P)). Qed.
Lemma lem1348287 (P : real -> Prop) (r : hreal -> real) (h1 : term122 P r) : term122 P r.
Proof. exact (h1). Qed.
Lemma lem1348289 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (@lem1348212 a b (@lem1348204 a b)). Qed.
Lemma lem1348290 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (x : real) : term147 P r h x.
Proof. exact (@lem1348289 (P x) (term148 P r h x)). Qed.
Lemma lem1348291 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1348292 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348293 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348292 r h h1 x). Qed.
Lemma lem1348294 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348295 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348294 r h x) (@lem1348293 x r h h1)). Qed.
Lemma lem1348296 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1348297 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348295 x r h h1 (@lem1348296 x h2)). Qed.
Lemma lem1348298 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term37 x) : term152 r h x.
Proof. exact (fun h0 : term99 r h => @lem1348297 r h x h0 h1). Qed.
Lemma lem1348299 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348300 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348298 r h x h2 (@lem1348299 r h h1)). Qed.
Lemma lem1348301 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (fun h0 : term37 x => @lem1348300 r h x h1 h0). Qed.
Lemma lem1348302 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (fun x : real => @lem1348301 x r h h1). Qed.
Lemma lem1348303 (r : hreal -> real) (h : real -> hreal) : term153 r h.
Proof. exact (fun h0 : term99 r h => @lem1348302 r h h0). Qed.
Lemma lem1348304 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (@lem1348303 r h (@lem1348229 r h h1)). Qed.
Lemma lem1348305 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348304 r h h1 x). Qed.
Lemma lem1348306 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348309 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348306 r h x) (@lem1348305 x r h h1)). Qed.
Lemma lem1348310 (x : real) : (term37 x) = ((term37 x) = True).
Proof. exact (@lem7 (term37 x)). Qed.
Lemma lem1348337 (x : real) (h1 : term37 x) : (term37 x) = True.
Proof. exact (EQ_MP (@lem1348310 x) (@lem1348221 x h1)). Qed.
Lemma lem1348338 (x : real) (h1 : term37 x) : True = (term37 x).
Proof. exact (SYM (@lem1348337 x h1)). Qed.
Lemma lem1348339 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (EQ_MP (@lem1348338 x h1) (@lem0)). Qed.
Lemma lem1348340 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348309 x r h h1 (@lem1348339 x h2)). Qed.
Lemma lem1348341 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term148 P r h x) = (P x).
Proof. exact (MK_COMB (@lem1348291 P) (@lem1348340 r h x h1 h2)). Qed.
Lemma lem1348342 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : term154 P r h x.
Proof. exact (@lem1348290 P r h x (@lem1348341 P r h x h1 h2)). Qed.
Lemma lem1348343 (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term99 r h) (h2 : P x) (h3 : term37 x) : term148 P r h x.
Proof. exact (@lem1348342 P r h x h1 h3 (@lem1348222 P x h2)). Qed.
Lemma lem1348344 (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term99 r h) (h2 : P x) (h3 : term37 x) : term106 P r.
Proof. exact (ex_intro (term88 P r) (h x) (@lem1348343 r h P x h1 h2 h3)). Qed.
Lemma lem1348345 (P : real -> Prop) (r : hreal -> real) (y : hreal) (h1 : term103 P r y) : term103 P r y.
Proof. exact (h1). Qed.
Lemma lem1348346 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term155 P M x.
Proof. exact (@lem1348223 P M h1 x). Qed.
Lemma lem1348347 (P : real -> Prop) (x : real) (M : real) : (term155 P M x) = (term156 P x M).
Proof. exact (eq_refl (term155 P M x)). Qed.
Lemma lem1348350 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term156 P x M.
Proof. exact (EQ_MP (@lem1348347 P x M) (@lem1348346 x P M h1)). Qed.
Lemma lem1348351 (r : hreal -> real) (y : hreal) (P : real -> Prop) (M : real) (h1 : term94 P M) : term157 P r y M.
Proof. exact (@lem1348350 (r y) P M h1). Qed.
Lemma lem1348352 (M : real) (P : real -> Prop) (r : hreal -> real) (y : hreal) (h1 : term94 P M) (h2 : term103 P r y) : term158 r y M.
Proof. exact (@lem1348351 r y P M h1 (@lem1348345 P r y h2)). Qed.
Lemma lem1348380 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term159 r x.
Proof. exact (@lem1348230 r h1 x). Qed.
Lemma lem1348381 (x : hreal) (r : hreal -> real) : (term159 r x) = (term160 x r).
Proof. exact (eq_refl (term159 r x)). Qed.
Lemma lem1348382 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term160 x r.
Proof. exact (EQ_MP (@lem1348381 x r) (@lem1348380 x r h1)). Qed.
Lemma lem1348383 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : term161 x r y.
Proof. exact (@lem1348382 x r h1 y). Qed.
Lemma lem1348384 (x : hreal) (r : hreal -> real) (y : hreal) : (term161 x r y) = ((hreal_le x y) = (term162 x r y)).
Proof. exact (eq_refl (term161 x r y)). Qed.
Lemma lem1348389 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : (hreal_le x y) = (term162 x r y).
Proof. exact (EQ_MP (@lem1348384 x r y) (@lem1348383 x y r h1)). Qed.
Lemma lem1348390 (y : hreal) (h : real -> hreal) (M : real) (r : hreal -> real) (h1 : term100 r) : (term163 y h M) = (term164 y r h M).
Proof. exact (@lem1348389 y (h M) r h1). Qed.
Lemma lem1348391 (r : hreal -> real) (y : hreal) (M : real) : (term165 r y M) = (term165 r y M).
Proof. exact (eq_refl (term165 r y M)). Qed.
Lemma lem1348392 (y : hreal) (h : real -> hreal) (M : real) (r : hreal -> real) (h1 : term100 r) : (term166 r y h M) = (term167 y r h M).
Proof. exact (MK_COMB (@lem1348391 r y M) (@lem1348390 y h M r h1)). Qed.
Lemma lem1348395 (y : hreal) (h : real -> hreal) (M : real) (r : hreal -> real) (h1 : term100 r) : (term167 y r h M) = (term166 r y h M).
Proof. exact (SYM (@lem1348392 y h M r h1)). Qed.
Lemma lem1348397 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (@lem1348109 a b (@lem1348101 a b)). Qed.
Lemma lem1348398 (y : hreal) (r : hreal -> real) (h : real -> hreal) (M : real) : term168 y r h M.
Proof. exact (@lem1348397 (term158 r y M) (term164 y r h M)). Qed.
Lemma lem1348399 (r : hreal -> real) (y : hreal) : (term169 r y) = (term169 r y).
Proof. exact (eq_refl (term169 r y)). Qed.
Lemma lem1348400 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348401 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348400 r h h1 x). Qed.
Lemma lem1348402 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348403 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348402 r h x) (@lem1348401 x r h h1)). Qed.
Lemma lem1348404 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1348405 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348403 x r h h1 (@lem1348404 x h2)). Qed.
Lemma lem1348406 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term37 x) : term152 r h x.
Proof. exact (fun h0 : term99 r h => @lem1348405 r h x h0 h1). Qed.
Lemma lem1348407 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348408 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348406 r h x h2 (@lem1348407 r h h1)). Qed.
Lemma lem1348409 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (fun h0 : term37 x => @lem1348408 r h x h1 h0). Qed.
Lemma lem1348410 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (fun x : real => @lem1348409 x r h h1). Qed.
Lemma lem1348411 (r : hreal -> real) (h : real -> hreal) : term153 r h.
Proof. exact (fun h0 : term99 r h => @lem1348410 r h h0). Qed.
Lemma lem1348412 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (@lem1348411 r h (@lem1348229 r h h1)). Qed.
Lemma lem1348413 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348412 r h h1 x). Qed.
Lemma lem1348414 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348417 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348414 r h x) (@lem1348413 x r h h1)). Qed.
Lemma lem1348418 (M : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h M.
Proof. exact (@lem1348417 M r h h1). Qed.
Lemma lem1348420 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1348006 x z) (@lem1348005 x z)). Qed.
Lemma lem1348421 (M : real) : term170 M.
Proof. exact (@lem1348420 term39 M). Qed.
Lemma lem1348424 (x : real) : (term37 x) = ((term37 x) = True).
Proof. exact (@lem7 (term37 x)). Qed.
Lemma lem1348453 (x : real) (h1 : term37 x) : (term37 x) = True.
Proof. exact (EQ_MP (@lem1348424 x) (@lem1348221 x h1)). Qed.
Lemma lem1348454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1348455 (x : real) (h1 : term37 x) : (term171 x) = (and True).
Proof. exact (MK_COMB (@lem1348454) (@lem1348453 x h1)). Qed.
Lemma lem1348456 (x : real) (M : real) : (real_le x M) = (real_le x M).
Proof. exact (eq_refl (real_le x M)). Qed.
Lemma lem1348457 (M : real) (x : real) (h1 : term37 x) : (term172 x M) = (term173 x M).
Proof. exact (MK_COMB (@lem1348455 x h1) (@lem1348456 x M)). Qed.
Lemma lem1348459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1348460 (x : real) (M : real) : (term173 x M) = (real_le x M).
Proof. exact (@lem1348459 (real_le x M)). Qed.
Lemma lem1348461 (M : real) (x : real) (h1 : term37 x) : (term172 x M) = (real_le x M).
Proof. exact (TRANS (@lem1348457 M x h1) (@lem1348460 x M)). Qed.
Lemma lem1348462 (M : real) (x : real) (h1 : term37 x) : (real_le x M) = (term172 x M).
Proof. exact (SYM (@lem1348461 M x h1)). Qed.
Lemma lem1348481 (P : real -> Prop) (M : real) (h1 : term94 P M) : term94 P M.
Proof. exact (h1). Qed.
Lemma lem1348482 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term155 P M x.
Proof. exact (@lem1348481 P M h1 x). Qed.
Lemma lem1348483 (P : real -> Prop) (x : real) (M : real) : (term155 P M x) = (term156 P x M).
Proof. exact (eq_refl (term155 P M x)). Qed.
Lemma lem1348484 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term156 P x M.
Proof. exact (EQ_MP (@lem1348483 P x M) (@lem1348482 x P M h1)). Qed.
Lemma lem1348485 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1348486 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) : real_le x M.
Proof. exact (@lem1348484 x P M h1 (@lem1348485 P x h2)). Qed.
Lemma lem1348487 (M : real) (P : real -> Prop) (x : real) (h1 : P x) : term174 P x M.
Proof. exact (fun h0 : term94 P M => @lem1348486 M P x h0 h1). Qed.
Lemma lem1348488 (P : real -> Prop) (M : real) (h1 : term94 P M) : term94 P M.
Proof. exact (h1). Qed.
Lemma lem1348489 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) : real_le x M.
Proof. exact (@lem1348487 M P x h2 (@lem1348488 P M h1)). Qed.
Lemma lem1348490 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term156 P x M.
Proof. exact (fun h0 : P x => @lem1348489 M P x h1 h0). Qed.
Lemma lem1348491 (P : real -> Prop) (M : real) (h1 : term94 P M) : term94 P M.
Proof. exact (fun x : real => @lem1348490 x P M h1). Qed.
Lemma lem1348492 (P : real -> Prop) (M : real) : term175 P M.
Proof. exact (fun h0 : term94 P M => @lem1348491 P M h0). Qed.
Lemma lem1348493 (P : real -> Prop) (M : real) (h1 : term94 P M) : term94 P M.
Proof. exact (@lem1348492 P M (@lem1348223 P M h1)). Qed.
Lemma lem1348494 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term155 P M x.
Proof. exact (@lem1348493 P M h1 x). Qed.
Lemma lem1348495 (P : real -> Prop) (x : real) (M : real) : (term155 P M x) = (term156 P x M).
Proof. exact (eq_refl (term155 P M x)). Qed.
Lemma lem1348498 (x : real) (P : real -> Prop) (M : real) (h1 : term94 P M) : term156 P x M.
Proof. exact (EQ_MP (@lem1348495 P x M) (@lem1348494 x P M h1)). Qed.
Lemma lem1348499 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1348528 (P : real -> Prop) (x : real) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1348499 P x) (@lem1348222 P x h1)). Qed.
Lemma lem1348529 (P : real -> Prop) (x : real) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1348528 P x h1)). Qed.
Lemma lem1348530 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1348529 P x h1) (@lem0)). Qed.
Lemma lem1348531 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) : real_le x M.
Proof. exact (@lem1348498 x P M h1 (@lem1348530 P x h2)). Qed.
Lemma lem1348532 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : term172 x M.
Proof. exact (EQ_MP (@lem1348462 M x h3) (@lem1348531 M P x h1 h2)). Qed.
Lemma lem1348533 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : term176 M.
Proof. exact (ex_intro (term177 M) x (@lem1348532 M P x h1 h2 h3)). Qed.
Lemma lem1348534 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : term37 M.
Proof. exact (@lem1348421 M (@lem1348533 M P x h1 h2 h3)). Qed.
Lemma lem1348535 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : (term151 r h M) = M.
Proof. exact (@lem1348418 M r h h2 (@lem1348534 M P x h1 h3 h4)). Qed.
Lemma lem1348536 (y : hreal) (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : (term164 y r h M) = (term158 r y M).
Proof. exact (MK_COMB (@lem1348399 r y) (@lem1348535 M r h P x h1 h2 h3 h4)). Qed.
Lemma lem1348537 (y : hreal) (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : term167 y r h M.
Proof. exact (@lem1348398 y r h M (@lem1348536 y M r h P x h1 h2 h3 h4)). Qed.
Lemma lem1348538 (y : hreal) (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term166 r y h M.
Proof. exact (EQ_MP (@lem1348395 y h M r h1) (@lem1348537 y M r h P x h2 h3 h4 h5)). Qed.
Lemma lem1348539 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (y : hreal) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term103 P r y) (h6 : term37 x) : term163 y h M.
Proof. exact (@lem1348538 y M r h P x h1 h2 h3 h4 h6 (@lem1348352 M P r y h2 h5)). Qed.
Lemma lem1348540 (y : hreal) (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term178 P r y h M.
Proof. exact (fun h0 : term103 P r y => @lem1348539 M h P r y x h1 h2 h3 h4 h0 h5). Qed.
Lemma lem1348545 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term179 P r h M.
Proof. exact (fun y : hreal => @lem1348540 y M r h P x h1 h2 h3 h4 h5). Qed.
Lemma lem1348546 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term120 P r.
Proof. exact (ex_intro (term118 P r) (h M) (@lem1348545 M r h P x h1 h2 h3 h4 h5)). Qed.
Lemma lem1348547 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term122 P r.
Proof. exact (conj (@lem1348344 r h P x h3 h4 h5) (@lem1348546 M r h P x h1 h2 h3 h4 h5)). Qed.
Lemma lem1348549 (a : Prop) (b : Prop) (c : Prop) : term49 a b c.
Proof. exact (@lem1347978 a b c (@lem1347970 a b c)). Qed.
Lemma lem1348550 (r : hreal -> real) (P : real -> Prop) : term180 r P.
Proof. exact (@lem1348549 (term122 P r) (term140 P r) (term144 P)). Qed.
Lemma lem1348551 (P : real -> Prop) (r : hreal -> real) (h1 : term140 P r) : term140 P r.
Proof. exact (h1). Qed.
Lemma lem1348552 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term136 P r B) : term136 P r B.
Proof. exact (h1). Qed.
Lemma lem1348553 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term134 P r B.
Proof. exact (h1). Qed.
Lemma lem1348554 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term116 P r B.
Proof. exact (h1). Qed.
Lemma lem1348555 (P : real -> Prop) (z : real) (h1 : P z) : P z.
Proof. exact (h1). Qed.
Lemma lem1348561 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348229 r h h1 x). Qed.
Lemma lem1348562 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348565 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348562 r h x) (@lem1348561 x r h h1)). Qed.
Lemma lem1348566 (z : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h z.
Proof. exact (@lem1348565 z r h h1). Qed.
Lemma lem1348567 (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term151 r h z) = z.
Proof. exact (@lem1348566 z r h h1 (@lem1347717 z h2)). Qed.
Lemma lem1348568 (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : z = (term151 r h z).
Proof. exact (SYM (@lem1348567 r h z h1 h2)). Qed.
Lemma lem1348579 (r : hreal -> real) (B : hreal) : (term181 r B) = (term181 r B).
Proof. exact (eq_refl (term181 r B)). Qed.
Lemma lem1348580 (B : hreal) (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term182 r B z) = (term183 B r h z).
Proof. exact (MK_COMB (@lem1348579 r B) (@lem1348568 r h z h1 h2)). Qed.
Lemma lem1348581 (h : real -> hreal) (z : real) (r : hreal -> real) (B : hreal) : (term183 B r h z) = (term184 h z r B).
Proof. exact (eq_refl (term183 B r h z)). Qed.
Lemma lem1348582 (r : hreal -> real) (B : hreal) (z : real) : (term185 r B z) = (term185 r B z).
Proof. exact (eq_refl (term185 r B z)). Qed.
Lemma lem1348583 (h : real -> hreal) (z : real) (r : hreal -> real) (B : hreal) : ((term182 r B z) = (term183 B r h z)) = ((term182 r B z) = (term184 h z r B)).
Proof. exact (MK_COMB (@lem1348582 r B z) (@lem1348581 h z r B)). Qed.
Lemma lem1348584 (z : real) (r : hreal -> real) (B : hreal) : (term182 r B z) = (term186 z r B).
Proof. exact (eq_refl (term182 r B z)). Qed.
Lemma lem1348585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1348586 (z : real) (r : hreal -> real) (B : hreal) : (term185 r B z) = (term187 z r B).
Proof. exact (MK_COMB (@lem1348585) (@lem1348584 z r B)). Qed.
Lemma lem1348587 (h : real -> hreal) (z : real) (r : hreal -> real) (B : hreal) : (term184 h z r B) = (term184 h z r B).
Proof. exact (eq_refl (term184 h z r B)). Qed.
Lemma lem1348588 (h : real -> hreal) (z : real) (r : hreal -> real) (B : hreal) : ((term182 r B z) = (term184 h z r B)) = ((term186 z r B) = (term184 h z r B)).
Proof. exact (MK_COMB (@lem1348586 z r B) (@lem1348587 h z r B)). Qed.
Lemma lem1348589 (h : real -> hreal) (z : real) (r : hreal -> real) (B : hreal) : ((term182 r B z) = (term183 B r h z)) = ((term186 z r B) = (term184 h z r B)).
Proof. exact (TRANS (@lem1348583 h z r B) (@lem1348588 h z r B)). Qed.
Lemma lem1348590 (B : hreal) (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term186 z r B) = (term184 h z r B).
Proof. exact (EQ_MP (@lem1348589 h z r B) (@lem1348580 B r h z h1 h2)). Qed.
Lemma lem1348591 (B : hreal) (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term184 h z r B) = (term186 z r B).
Proof. exact (SYM (@lem1348590 B r h z h1 h2)). Qed.
Lemma lem1348629 (x : hreal) (r : hreal -> real) (y : hreal) (h1 : (hreal_le x y) = (term162 x r y)) : (hreal_le x y) = (term162 x r y).
Proof. exact (h1). Qed.
Lemma lem1348630 (x : hreal) (r : hreal -> real) (y : hreal) (h1 : (hreal_le x y) = (term162 x r y)) : (term162 x r y) = (hreal_le x y).
Proof. exact (SYM (@lem1348629 x r y h1)). Qed.
Lemma lem1348631 (r : hreal -> real) (x : hreal) (y : hreal) (h1 : (term162 x r y) = (hreal_le x y)) : (term162 x r y) = (hreal_le x y).
Proof. exact (h1). Qed.
Lemma lem1348632 (r : hreal -> real) (x : hreal) (y : hreal) (h1 : (term162 x r y) = (hreal_le x y)) : (hreal_le x y) = (term162 x r y).
Proof. exact (SYM (@lem1348631 r x y h1)). Qed.
Lemma lem1348633 (r : hreal -> real) (x : hreal) (y : hreal) : ((hreal_le x y) = (term162 x r y)) = ((term162 x r y) = (hreal_le x y)).
Proof. exact (prop_ext (fun h1 : (hreal_le x y) = (term162 x r y) => @lem1348630 x r y h1) (fun h1 : (term162 x r y) = (hreal_le x y) => @lem1348632 r x y h1)). Qed.
Lemma lem1348634 (r : hreal -> real) (x : hreal) : (term188 x r) = (term189 r x).
Proof. exact (fun_ext (fun y : hreal => @lem1348633 r x y)). Qed.
Lemma lem1348635 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348636 (r : hreal -> real) (x : hreal) : (term160 x r) = (term190 r x).
Proof. exact (MK_COMB (@lem1348635) (@lem1348634 r x)). Qed.
Lemma lem1348637 (r : hreal -> real) : (term191 r) = (term192 r).
Proof. exact (fun_ext (fun x : hreal => @lem1348636 r x)). Qed.
Lemma lem1348638 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348639 (r : hreal -> real) : (term100 r) = (term193 r).
Proof. exact (MK_COMB (@lem1348638) (@lem1348637 r)). Qed.
Lemma lem1348640 (r : hreal -> real) (h1 : term100 r) : term193 r.
Proof. exact (EQ_MP (@lem1348639 r) (@lem1348230 r h1)). Qed.
Lemma lem1348641 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term194 r x.
Proof. exact (@lem1348640 r h1 x). Qed.
Lemma lem1348642 (r : hreal -> real) (x : hreal) : (term194 r x) = (term190 r x).
Proof. exact (eq_refl (term194 r x)). Qed.
Lemma lem1348643 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term190 r x.
Proof. exact (EQ_MP (@lem1348642 r x) (@lem1348641 x r h1)). Qed.
Lemma lem1348644 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : term195 r x y.
Proof. exact (@lem1348643 x r h1 y). Qed.
Lemma lem1348645 (r : hreal -> real) (x : hreal) (y : hreal) : (term195 r x y) = ((term162 x r y) = (hreal_le x y)).
Proof. exact (eq_refl (term195 r x y)). Qed.
Lemma lem1348648 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : (term162 x r y) = (hreal_le x y).
Proof. exact (EQ_MP (@lem1348645 r x y) (@lem1348644 x y r h1)). Qed.
Lemma lem1348649 (h : real -> hreal) (z : real) (B : hreal) (r : hreal -> real) (h1 : term100 r) : (term184 h z r B) = (term196 h z B).
Proof. exact (@lem1348648 (h z) B r h1). Qed.
Lemma lem1348650 (h : real -> hreal) (z : real) (B : hreal) (r : hreal -> real) (h1 : term100 r) : (term196 h z B) = (term184 h z r B).
Proof. exact (SYM (@lem1348649 h z B r h1)). Qed.
Lemma lem1348669 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term116 P r B.
Proof. exact (h1). Qed.
Lemma lem1348670 (x : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term197 P r B x.
Proof. exact (@lem1348669 P r B h1 x). Qed.
Lemma lem1348671 (P : real -> Prop) (r : hreal -> real) (x : hreal) (B : hreal) : (term197 P r B x) = (term112 P r x B).
Proof. exact (eq_refl (term197 P r B x)). Qed.
Lemma lem1348672 (x : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term112 P r x B.
Proof. exact (EQ_MP (@lem1348671 P r x B) (@lem1348670 x P r B h1)). Qed.
Lemma lem1348673 (P : real -> Prop) (r : hreal -> real) (x : hreal) (h1 : term103 P r x) : term103 P r x.
Proof. exact (h1). Qed.
Lemma lem1348674 (B : hreal) (P : real -> Prop) (r : hreal -> real) (x : hreal) (h1 : term116 P r B) (h2 : term103 P r x) : hreal_le x B.
Proof. exact (@lem1348672 x P r B h1 (@lem1348673 P r x h2)). Qed.
Lemma lem1348675 (B : hreal) (P : real -> Prop) (r : hreal -> real) (x : hreal) (h1 : term103 P r x) : term130 P r x B.
Proof. exact (fun h0 : term116 P r B => @lem1348674 B P r x h0 h1). Qed.
Lemma lem1348676 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term116 P r B.
Proof. exact (h1). Qed.
Lemma lem1348677 (B : hreal) (P : real -> Prop) (r : hreal -> real) (x : hreal) (h1 : term116 P r B) (h2 : term103 P r x) : hreal_le x B.
Proof. exact (@lem1348675 B P r x h2 (@lem1348676 P r B h1)). Qed.
Lemma lem1348678 (x : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term112 P r x B.
Proof. exact (fun h0 : term103 P r x => @lem1348677 B P r x h1 h0). Qed.
Lemma lem1348679 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term116 P r B.
Proof. exact (fun x : hreal => @lem1348678 x P r B h1). Qed.
Lemma lem1348680 (P : real -> Prop) (r : hreal -> real) (B : hreal) : term198 P r B.
Proof. exact (fun h0 : term116 P r B => @lem1348679 P r B h0). Qed.
Lemma lem1348681 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term116 P r B.
Proof. exact (@lem1348680 P r B (@lem1348554 P r B h1)). Qed.
Lemma lem1348682 (x : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term197 P r B x.
Proof. exact (@lem1348681 P r B h1 x). Qed.
Lemma lem1348683 (P : real -> Prop) (r : hreal -> real) (x : hreal) (B : hreal) : (term197 P r B x) = (term112 P r x B).
Proof. exact (eq_refl (term197 P r B x)). Qed.
Lemma lem1348686 (x : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term112 P r x B.
Proof. exact (EQ_MP (@lem1348683 P r x B) (@lem1348682 x P r B h1)). Qed.
Lemma lem1348687 (h : real -> hreal) (z : real) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term116 P r B) : term199 P r h z B.
Proof. exact (@lem1348686 (h z) P r B h1). Qed.
Lemma lem1348689 (a : Prop) (b : Prop) : term27 a b.
Proof. exact (@lem1347715 a b (@lem1347707 a b)). Qed.
Lemma lem1348690 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (z : real) : term147 P r h z.
Proof. exact (@lem1348689 (P z) (term148 P r h z)). Qed.
Lemma lem1348691 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1348728 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348729 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348728 r h h1 x). Qed.
Lemma lem1348730 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348731 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348730 r h x) (@lem1348729 x r h h1)). Qed.
Lemma lem1348732 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1348733 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348731 x r h h1 (@lem1348732 x h2)). Qed.
Lemma lem1348734 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term37 x) : term152 r h x.
Proof. exact (fun h0 : term99 r h => @lem1348733 r h x h0 h1). Qed.
Lemma lem1348735 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1348736 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1348734 r h x h2 (@lem1348735 r h h1)). Qed.
Lemma lem1348737 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (fun h0 : term37 x => @lem1348736 r h x h1 h0). Qed.
Lemma lem1348738 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (fun x : real => @lem1348737 x r h h1). Qed.
Lemma lem1348739 (r : hreal -> real) (h : real -> hreal) : term153 r h.
Proof. exact (fun h0 : term99 r h => @lem1348738 r h h0). Qed.
Lemma lem1348740 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (@lem1348739 r h (@lem1348229 r h h1)). Qed.
Lemma lem1348741 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1348740 r h h1 x). Qed.
Lemma lem1348742 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1348745 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1348742 r h x) (@lem1348741 x r h h1)). Qed.
Lemma lem1348746 (z : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h z.
Proof. exact (@lem1348745 z r h h1). Qed.
Lemma lem1348785 (z : real) : (term37 z) = ((term37 z) = True).
Proof. exact (@lem7 (term37 z)). Qed.
Lemma lem1348788 (z : real) (h1 : term37 z) : (term37 z) = True.
Proof. exact (EQ_MP (@lem1348785 z) (@lem1347724 z h1)). Qed.
Lemma lem1348789 (z : real) (h1 : term37 z) : True = (term37 z).
Proof. exact (SYM (@lem1348788 z h1)). Qed.
Lemma lem1348790 (z : real) (h1 : term37 z) : term37 z.
Proof. exact (EQ_MP (@lem1348789 z h1) (@lem0)). Qed.
Lemma lem1348791 (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term151 r h z) = z.
Proof. exact (@lem1348746 z r h h1 (@lem1348790 z h2)). Qed.
Lemma lem1348792 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : (term148 P r h z) = (P z).
Proof. exact (MK_COMB (@lem1348691 P) (@lem1348791 r h z h1 h2)). Qed.
Lemma lem1348793 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (z : real) (h1 : term99 r h) (h2 : term37 z) : term154 P r h z.
Proof. exact (@lem1348690 P r h z (@lem1348792 P r h z h1 h2)). Qed.
Lemma lem1348794 (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (z : real) (h1 : term99 r h) (h2 : P z) (h3 : term37 z) : term148 P r h z.
Proof. exact (@lem1348793 P r h z h1 h3 (@lem1348555 P z h2)). Qed.
Lemma lem1348795 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (z : real) (h1 : term116 P r B) (h2 : term99 r h) (h3 : P z) (h4 : term37 z) : term196 h z B.
Proof. exact (@lem1348687 h z P r B h1 (@lem1348794 r h P z h2 h3 h4)). Qed.
Lemma lem1348796 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (z : real) (h1 : term100 r) (h2 : term116 P r B) (h3 : term99 r h) (h4 : P z) (h5 : term37 z) : term184 h z r B.
Proof. exact (EQ_MP (@lem1348650 h z B r h1) (@lem1348795 B r h P z h2 h3 h4 h5)). Qed.
Lemma lem1348797 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (z : real) (h1 : term100 r) (h2 : term116 P r B) (h3 : term99 r h) (h4 : P z) (h5 : term37 z) : term186 z r B.
Proof. exact (EQ_MP (@lem1348591 B r h z h3 h5) (@lem1348796 B r h P z h1 h2 h3 h4 h5)). Qed.
Lemma lem1348799 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1347612 x z) (@lem1347611 x z)). Qed.
Lemma lem1348800 (z : real) (r : hreal -> real) (B : hreal) : term200 z r B.
Proof. exact (@lem1348799 z (r B)). Qed.
Lemma lem1348818 (x : hreal) (r : hreal -> real) (h1 : term101 r) : term201 r x.
Proof. exact (@lem1348231 r h1 x). Qed.
Lemma lem1348819 (r : hreal -> real) (x : hreal) : (term201 r x) = (term202 r x).
Proof. exact (eq_refl (term201 r x)). Qed.
Lemma lem1348820 (x : hreal) (r : hreal -> real) (h1 : term101 r) : term202 r x.
Proof. exact (EQ_MP (@lem1348819 r x) (@lem1348818 x r h1)). Qed.
Lemma lem1348821 (r : hreal -> real) (x : hreal) : (term202 r x) = ((term202 r x) = True).
Proof. exact (@lem7 (term202 r x)). Qed.
Lemma lem1348841 (z : real) : (term43 z) = ((term43 z) = True).
Proof. exact (@lem7 (term43 z)). Qed.
Lemma lem1348846 (z : real) (h1 : term43 z) : (term43 z) = True.
Proof. exact (EQ_MP (@lem1348841 z) (@lem1347725 z h1)). Qed.
Lemma lem1348847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1348848 (z : real) (h1 : term43 z) : (term203 z) = (and True).
Proof. exact (MK_COMB (@lem1348847) (@lem1348846 z h1)). Qed.
Lemma lem1348850 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term202 r x) = True.
Proof. exact (EQ_MP (@lem1348821 r x) (@lem1348820 x r h1)). Qed.
Lemma lem1348851 (B : hreal) (r : hreal -> real) (h1 : term101 r) : (term202 r B) = True.
Proof. exact (@lem1348850 B r h1). Qed.
Lemma lem1348852 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : (term204 z r B) = (True /\ True).
Proof. exact (MK_COMB (@lem1348848 z h2) (@lem1348851 B r h1)). Qed.
Lemma lem1348854 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1348855 : (True /\ True) = True.
Proof. exact (@lem1348854 True). Qed.
Lemma lem1348856 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : (term204 z r B) = True.
Proof. exact (TRANS (@lem1348852 B r z h1 h2) (@lem1348855)). Qed.
Lemma lem1348857 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : True = (term204 z r B).
Proof. exact (SYM (@lem1348856 B r z h1 h2)). Qed.
Lemma lem1348858 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : term204 z r B.
Proof. exact (EQ_MP (@lem1348857 B r z h1 h2) (@lem0)). Qed.
Lemma lem1348859 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : term205 z r B.
Proof. exact (ex_intro (term206 z r B) term39 (@lem1348858 B r z h1 h2)). Qed.
Lemma lem1348860 (B : hreal) (r : hreal -> real) (z : real) (h1 : term101 r) (h2 : term43 z) : term186 z r B.
Proof. exact (@lem1348800 z r B (@lem1348859 B r z h1 h2)). Qed.
Lemma lem1348861 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (z : real) (h1 : term100 r) (h2 : term116 P r B) (h3 : term101 r) (h4 : term99 r h) (h5 : P z) : term186 z r B.
Proof. exact (or_elim (@lem1347723 z) (fun h0 : term37 z => @lem1348797 B r h P z h1 h2 h4 h5 h0) (fun h0 : term43 z => @lem1348860 B r z h3 h0)). Qed.
Lemma lem1348862 (z : real) (P : real -> Prop) (B : hreal) (r : hreal -> real) (h : real -> hreal) (h1 : term100 r) (h2 : term116 P r B) (h3 : term101 r) (h4 : term99 r h) : term207 P z r B.
Proof. exact (fun h0 : P z => @lem1348861 B r h P z h1 h2 h3 h4 h0). Qed.
Lemma lem1348867 (P : real -> Prop) (B : hreal) (r : hreal -> real) (h : real -> hreal) (h1 : term100 r) (h2 : term116 P r B) (h3 : term101 r) (h4 : term99 r h) : term208 P r B.
Proof. exact (fun z : real => @lem1348862 z P B r h h1 h2 h3 h4). Qed.
Lemma lem1348868 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (h1). Qed.
Lemma lem1348869 (B : hreal) (h : real -> hreal) (C : real) (h1 : term163 B h C) : term163 B h C.
Proof. exact (h1). Qed.
Lemma lem1348888 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term134 P r B.
Proof. exact (h1). Qed.
Lemma lem1348889 (M' : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term209 P r B M'.
Proof. exact (@lem1348888 P r B h1 M'). Qed.
Lemma lem1348890 (P : real -> Prop) (r : hreal -> real) (B : hreal) (M' : hreal) : (term209 P r B M') = (term130 P r B M').
Proof. exact (eq_refl (term209 P r B M')). Qed.
Lemma lem1348891 (M' : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term130 P r B M'.
Proof. exact (EQ_MP (@lem1348890 P r B M') (@lem1348889 M' P r B h1)). Qed.
Lemma lem1348892 (P : real -> Prop) (r : hreal -> real) (M' : hreal) (h1 : term116 P r M') : term116 P r M'.
Proof. exact (h1). Qed.
Lemma lem1348893 (B : hreal) (P : real -> Prop) (r : hreal -> real) (M' : hreal) (h1 : term134 P r B) (h2 : term116 P r M') : hreal_le B M'.
Proof. exact (@lem1348891 M' P r B h1 (@lem1348892 P r M' h2)). Qed.
Lemma lem1348894 (B : hreal) (P : real -> Prop) (r : hreal -> real) (M' : hreal) (h1 : term116 P r M') : term210 P r B M'.
Proof. exact (fun h0 : term134 P r B => @lem1348893 B P r M' h0 h1). Qed.
Lemma lem1348895 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term134 P r B.
Proof. exact (h1). Qed.
Lemma lem1348896 (B : hreal) (P : real -> Prop) (r : hreal -> real) (M' : hreal) (h1 : term134 P r B) (h2 : term116 P r M') : hreal_le B M'.
Proof. exact (@lem1348894 B P r M' h2 (@lem1348895 P r B h1)). Qed.
Lemma lem1348897 (M' : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term130 P r B M'.
Proof. exact (fun h0 : term116 P r M' => @lem1348896 B P r M' h1 h0). Qed.
Lemma lem1348898 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term134 P r B.
Proof. exact (fun M' : hreal => @lem1348897 M' P r B h1). Qed.
Lemma lem1348899 (P : real -> Prop) (r : hreal -> real) (B : hreal) : term211 P r B.
Proof. exact (fun h0 : term134 P r B => @lem1348898 P r B h0). Qed.
Lemma lem1348900 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term134 P r B.
Proof. exact (@lem1348899 P r B (@lem1348553 P r B h1)). Qed.
Lemma lem1348901 (M' : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term209 P r B M'.
Proof. exact (@lem1348900 P r B h1 M'). Qed.
Lemma lem1348902 (P : real -> Prop) (r : hreal -> real) (B : hreal) (M' : hreal) : (term209 P r B M') = (term130 P r B M').
Proof. exact (eq_refl (term209 P r B M')). Qed.
Lemma lem1348905 (M' : hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term130 P r B M'.
Proof. exact (EQ_MP (@lem1348902 P r B M') (@lem1348901 M' P r B h1)). Qed.
Lemma lem1348906 (h : real -> hreal) (C : real) (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term134 P r B) : term212 P r B h C.
Proof. exact (@lem1348905 (h C) P r B h1). Qed.
Lemma lem1348929 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term159 r x.
Proof. exact (@lem1348230 r h1 x). Qed.
Lemma lem1348930 (x : hreal) (r : hreal -> real) : (term159 r x) = (term160 x r).
Proof. exact (eq_refl (term159 r x)). Qed.
Lemma lem1348931 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term160 x r.
Proof. exact (EQ_MP (@lem1348930 x r) (@lem1348929 x r h1)). Qed.
Lemma lem1348932 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : term161 x r y.
Proof. exact (@lem1348931 x r h1 y). Qed.
Lemma lem1348933 (x : hreal) (r : hreal -> real) (y : hreal) : (term161 x r y) = ((hreal_le x y) = (term162 x r y)).
Proof. exact (eq_refl (term161 x r y)). Qed.
Lemma lem1348957 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : (hreal_le x y) = (term162 x r y).
Proof. exact (EQ_MP (@lem1348933 x r y) (@lem1348932 x y r h1)). Qed.
Lemma lem1348958 (x : hreal) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term163 x h C) = (term164 x r h C).
Proof. exact (@lem1348957 x (h C) r h1). Qed.
Lemma lem1348959 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term110 P r x) = (term110 P r x).
Proof. exact (eq_refl (term110 P r x)). Qed.
Lemma lem1348960 (P : real -> Prop) (x : hreal) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term178 P r x h C) = (term213 P x r h C).
Proof. exact (MK_COMB (@lem1348959 P r x) (@lem1348958 x h C r h1)). Qed.
Lemma lem1348963 (P : real -> Prop) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term214 P r h C) = (term215 P r h C).
Proof. exact (fun_ext (fun x : hreal => @lem1348960 P x h C r h1)). Qed.
Lemma lem1348964 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1348965 (P : real -> Prop) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term179 P r h C) = (term216 P r h C).
Proof. exact (MK_COMB (@lem1348964) (@lem1348963 P h C r h1)). Qed.
Lemma lem1348970 (P : real -> Prop) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term216 P r h C) = (term179 P r h C).
Proof. exact (SYM (@lem1348965 P h C r h1)). Qed.
Lemma lem1349010 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term155 P C x.
Proof. exact (@lem1348868 P C h1 x). Qed.
Lemma lem1349011 (P : real -> Prop) (x : real) (C : real) : (term155 P C x) = (term156 P x C).
Proof. exact (eq_refl (term155 P C x)). Qed.
Lemma lem1349012 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (EQ_MP (@lem1349011 P x C) (@lem1349010 x P C h1)). Qed.
Lemma lem1349013 (P : real -> Prop) (x : real) (C : real) : (term156 P x C) = ((term156 P x C) = True).
Proof. exact (@lem7 (term156 P x C)). Qed.
Lemma lem1349022 (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : (term151 r h C) = C) : (term151 r h C) = C.
Proof. exact (h1). Qed.
Lemma lem1349023 (r : hreal -> real) (x : hreal) : (term169 r x) = (term169 r x).
Proof. exact (eq_refl (term169 r x)). Qed.
Lemma lem1349024 (x : hreal) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : (term151 r h C) = C) : (term164 x r h C) = (term158 r x C).
Proof. exact (MK_COMB (@lem1349023 r x) (@lem1349022 r h C h1)). Qed.
Lemma lem1349025 (P : real -> Prop) (r : hreal -> real) (x : hreal) : (term110 P r x) = (term110 P r x).
Proof. exact (eq_refl (term110 P r x)). Qed.
Lemma lem1349026 (P : real -> Prop) (x : hreal) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : (term151 r h C) = C) : (term213 P x r h C) = (term157 P r x C).
Proof. exact (MK_COMB (@lem1349025 P r x) (@lem1349024 x r h C h1)). Qed.
Lemma lem1349028 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : (term156 P x C) = True.
Proof. exact (EQ_MP (@lem1349013 P x C) (@lem1349012 x P C h1)). Qed.
Lemma lem1349029 (r : hreal -> real) (x : hreal) (P : real -> Prop) (C : real) (h1 : term94 P C) : (term157 P r x C) = True.
Proof. exact (@lem1349028 (r x) P C h1). Qed.
Lemma lem1349030 (x : hreal) (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : (term213 P x r h C) = True.
Proof. exact (TRANS (@lem1349026 P x r h C h2) (@lem1349029 r x P C h1)). Qed.
Lemma lem1349031 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : (term215 P r h C) = term217.
Proof. exact (fun_ext (fun x : hreal => @lem1349030 x P r h C h1 h2)). Qed.
Lemma lem1349032 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1349033 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : (term216 P r h C) = term218.
Proof. exact (MK_COMB (@lem1349032) (@lem1349031 P r h C h1 h2)). Qed.
Lemma lem1349035 {A : Type'} (t : Prop) : (term219 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1349036 (t : Prop) : (term220 t) = t.
Proof. exact (@lem1349035 hreal t). Qed.
Lemma lem1349037 : term218 = True.
Proof. exact (@lem1349036 True). Qed.
Lemma lem1349038 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : (term216 P r h C) = True.
Proof. exact (TRANS (@lem1349033 P r h C h1 h2) (@lem1349037)). Qed.
Lemma lem1349039 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : True = (term216 P r h C).
Proof. exact (SYM (@lem1349038 P r h C h1 h2)). Qed.
Lemma lem1349040 (P : real -> Prop) (r : hreal -> real) (h : real -> hreal) (C : real) (h1 : term94 P C) (h2 : (term151 r h C) = C) : term216 P r h C.
Proof. exact (EQ_MP (@lem1349039 P r h C h1 h2) (@lem0)). Qed.
Lemma lem1349063 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term159 r x.
Proof. exact (@lem1348230 r h1 x). Qed.
Lemma lem1349064 (x : hreal) (r : hreal -> real) : (term159 r x) = (term160 x r).
Proof. exact (eq_refl (term159 r x)). Qed.
Lemma lem1349065 (x : hreal) (r : hreal -> real) (h1 : term100 r) : term160 x r.
Proof. exact (EQ_MP (@lem1349064 x r) (@lem1349063 x r h1)). Qed.
Lemma lem1349066 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : term161 x r y.
Proof. exact (@lem1349065 x r h1 y). Qed.
Lemma lem1349067 (x : hreal) (r : hreal -> real) (y : hreal) : (term161 x r y) = ((hreal_le x y) = (term162 x r y)).
Proof. exact (eq_refl (term161 x r y)). Qed.
Lemma lem1349087 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term100 r) : (hreal_le x y) = (term162 x r y).
Proof. exact (EQ_MP (@lem1349067 x r y) (@lem1349066 x y r h1)). Qed.
Lemma lem1349088 (B : hreal) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term163 B h C) = (term164 B r h C).
Proof. exact (@lem1349087 B (h C) r h1). Qed.
Lemma lem1349089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1349090 (B : hreal) (h : real -> hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term221 B h C) = (term222 B r h C).
Proof. exact (MK_COMB (@lem1349089) (@lem1349088 B h C r h1)). Qed.
Lemma lem1349091 (r : hreal -> real) (B : hreal) (C : real) : (term158 r B C) = (term158 r B C).
Proof. exact (eq_refl (term158 r B C)). Qed.
Lemma lem1349092 (h : real -> hreal) (B : hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term223 h r B C) = (term224 h r B C).
Proof. exact (MK_COMB (@lem1349090 B h C r h1) (@lem1349091 r B C)). Qed.
Lemma lem1349095 (h : real -> hreal) (B : hreal) (C : real) (r : hreal -> real) (h1 : term100 r) : (term224 h r B C) = (term223 h r B C).
Proof. exact (SYM (@lem1349092 h B C r h1)). Qed.
Lemma lem1349097 (a : Prop) (b : Prop) : term17 a b.
Proof. exact (@lem1347584 a b (@lem1157 a b)). Qed.
Lemma lem1349098 (h : real -> hreal) (r : hreal -> real) (B : hreal) (C : real) : term225 h r B C.
Proof. exact (@lem1349097 (term164 B r h C) (term158 r B C)). Qed.
Lemma lem1349099 (r : hreal -> real) (B : hreal) : (term169 r B) = (term169 r B).
Proof. exact (eq_refl (term169 r B)). Qed.
Lemma lem1349154 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1349155 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1349154 r h h1 x). Qed.
Lemma lem1349156 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1349157 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1349156 r h x) (@lem1349155 x r h h1)). Qed.
Lemma lem1349158 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1349159 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1349157 x r h h1 (@lem1349158 x h2)). Qed.
Lemma lem1349160 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term37 x) : term152 r h x.
Proof. exact (fun h0 : term99 r h => @lem1349159 r h x h0 h1). Qed.
Lemma lem1349161 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1349162 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1349160 r h x h2 (@lem1349161 r h h1)). Qed.
Lemma lem1349163 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (fun h0 : term37 x => @lem1349162 r h x h1 h0). Qed.
Lemma lem1349164 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (fun x : real => @lem1349163 x r h h1). Qed.
Lemma lem1349165 (r : hreal -> real) (h : real -> hreal) : term153 r h.
Proof. exact (fun h0 : term99 r h => @lem1349164 r h h0). Qed.
Lemma lem1349166 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (@lem1349165 r h (@lem1348229 r h h1)). Qed.
Lemma lem1349167 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1349166 r h h1 x). Qed.
Lemma lem1349168 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1349171 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1349168 r h x) (@lem1349167 x r h h1)). Qed.
Lemma lem1349172 (C : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h C.
Proof. exact (@lem1349171 C r h h1). Qed.
Lemma lem1349227 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1349228 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1349227 r h h1 x). Qed.
Lemma lem1349229 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1349230 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1349229 r h x) (@lem1349228 x r h h1)). Qed.
Lemma lem1349231 (x : real) (h1 : term37 x) : term37 x.
Proof. exact (h1). Qed.
Lemma lem1349232 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1349230 x r h h1 (@lem1349231 x h2)). Qed.
Lemma lem1349233 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term37 x) : term152 r h x.
Proof. exact (fun h0 : term99 r h => @lem1349232 r h x h0 h1). Qed.
Lemma lem1349234 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (h1). Qed.
Lemma lem1349235 (r : hreal -> real) (h : real -> hreal) (x : real) (h1 : term99 r h) (h2 : term37 x) : (term151 r h x) = x.
Proof. exact (@lem1349233 r h x h2 (@lem1349234 r h h1)). Qed.
Lemma lem1349236 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (fun h0 : term37 x => @lem1349235 r h x h1 h0). Qed.
Lemma lem1349237 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (fun x : real => @lem1349236 x r h h1). Qed.
Lemma lem1349238 (r : hreal -> real) (h : real -> hreal) : term153 r h.
Proof. exact (fun h0 : term99 r h => @lem1349237 r h h0). Qed.
Lemma lem1349239 (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term99 r h.
Proof. exact (@lem1349238 r h (@lem1348229 r h h1)). Qed.
Lemma lem1349240 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term149 r h x.
Proof. exact (@lem1349239 r h h1 x). Qed.
Lemma lem1349241 (r : hreal -> real) (h : real -> hreal) (x : real) : (term149 r h x) = (term150 r h x).
Proof. exact (eq_refl (term149 r h x)). Qed.
Lemma lem1349244 (x : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h x.
Proof. exact (EQ_MP (@lem1349241 r h x) (@lem1349240 x r h h1)). Qed.
Lemma lem1349245 (C : real) (r : hreal -> real) (h : real -> hreal) (h1 : term99 r h) : term150 r h C.
Proof. exact (@lem1349244 C r h h1). Qed.
Lemma lem1349247 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1347575 x z) (@lem1347574 x z)). Qed.
Lemma lem1349248 (C : real) : term170 C.
Proof. exact (@lem1349247 term39 C). Qed.
Lemma lem1349250 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1347575 x z) (@lem1347574 x z)). Qed.
Lemma lem1349251 (C : real) : term170 C.
Proof. exact (@lem1349250 term39 C). Qed.
Lemma lem1349254 (x : real) : (term37 x) = ((term37 x) = True).
Proof. exact (@lem7 (term37 x)). Qed.
Lemma lem1349298 (x : real) (h1 : term37 x) : (term37 x) = True.
Proof. exact (EQ_MP (@lem1349254 x) (@lem1348221 x h1)). Qed.
Lemma lem1349299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1349300 (x : real) (h1 : term37 x) : (term171 x) = (and True).
Proof. exact (MK_COMB (@lem1349299) (@lem1349298 x h1)). Qed.
Lemma lem1349301 (x : real) (C : real) : (real_le x C) = (real_le x C).
Proof. exact (eq_refl (real_le x C)). Qed.
Lemma lem1349302 (C : real) (x : real) (h1 : term37 x) : (term172 x C) = (term173 x C).
Proof. exact (MK_COMB (@lem1349300 x h1) (@lem1349301 x C)). Qed.
Lemma lem1349304 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1349305 (x : real) (C : real) : (term173 x C) = (real_le x C).
Proof. exact (@lem1349304 (real_le x C)). Qed.
Lemma lem1349306 (C : real) (x : real) (h1 : term37 x) : (term172 x C) = (real_le x C).
Proof. exact (TRANS (@lem1349302 C x h1) (@lem1349305 x C)). Qed.
Lemma lem1349307 (C : real) (x : real) (h1 : term37 x) : (real_le x C) = (term172 x C).
Proof. exact (SYM (@lem1349306 C x h1)). Qed.
Lemma lem1349310 (x : real) : (term37 x) = ((term37 x) = True).
Proof. exact (@lem7 (term37 x)). Qed.
Lemma lem1349354 (x : real) (h1 : term37 x) : (term37 x) = True.
Proof. exact (EQ_MP (@lem1349310 x) (@lem1348221 x h1)). Qed.
Lemma lem1349355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1349356 (x : real) (h1 : term37 x) : (term171 x) = (and True).
Proof. exact (MK_COMB (@lem1349355) (@lem1349354 x h1)). Qed.
Lemma lem1349357 (x : real) (C : real) : (real_le x C) = (real_le x C).
Proof. exact (eq_refl (real_le x C)). Qed.
Lemma lem1349358 (C : real) (x : real) (h1 : term37 x) : (term172 x C) = (term173 x C).
Proof. exact (MK_COMB (@lem1349356 x h1) (@lem1349357 x C)). Qed.
Lemma lem1349360 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1349361 (x : real) (C : real) : (term173 x C) = (real_le x C).
Proof. exact (@lem1349360 (real_le x C)). Qed.
Lemma lem1349362 (C : real) (x : real) (h1 : term37 x) : (term172 x C) = (real_le x C).
Proof. exact (TRANS (@lem1349358 C x h1) (@lem1349361 x C)). Qed.
Lemma lem1349363 (C : real) (x : real) (h1 : term37 x) : (real_le x C) = (term172 x C).
Proof. exact (SYM (@lem1349362 C x h1)). Qed.
Lemma lem1349364 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (h1). Qed.
Lemma lem1349365 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term155 P C x.
Proof. exact (@lem1349364 P C h1 x). Qed.
Lemma lem1349366 (P : real -> Prop) (x : real) (C : real) : (term155 P C x) = (term156 P x C).
Proof. exact (eq_refl (term155 P C x)). Qed.
Lemma lem1349367 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (EQ_MP (@lem1349366 P x C) (@lem1349365 x P C h1)). Qed.
Lemma lem1349368 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1349369 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349367 x P C h1 (@lem1349368 P x h2)). Qed.
Lemma lem1349370 (C : real) (P : real -> Prop) (x : real) (h1 : P x) : term174 P x C.
Proof. exact (fun h0 : term94 P C => @lem1349369 C P x h0 h1). Qed.
Lemma lem1349371 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (h1). Qed.
Lemma lem1349372 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349370 C P x h2 (@lem1349371 P C h1)). Qed.
Lemma lem1349373 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (fun h0 : P x => @lem1349372 C P x h1 h0). Qed.
Lemma lem1349374 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (fun x : real => @lem1349373 x P C h1). Qed.
Lemma lem1349375 (P : real -> Prop) (C : real) : term175 P C.
Proof. exact (fun h0 : term94 P C => @lem1349374 P C h0). Qed.
Lemma lem1349376 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (@lem1349375 P C (@lem1348868 P C h1)). Qed.
Lemma lem1349377 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term155 P C x.
Proof. exact (@lem1349376 P C h1 x). Qed.
Lemma lem1349378 (P : real -> Prop) (x : real) (C : real) : (term155 P C x) = (term156 P x C).
Proof. exact (eq_refl (term155 P C x)). Qed.
Lemma lem1349381 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (EQ_MP (@lem1349378 P x C) (@lem1349377 x P C h1)). Qed.
Lemma lem1349382 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (h1). Qed.
Lemma lem1349383 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term155 P C x.
Proof. exact (@lem1349382 P C h1 x). Qed.
Lemma lem1349384 (P : real -> Prop) (x : real) (C : real) : (term155 P C x) = (term156 P x C).
Proof. exact (eq_refl (term155 P C x)). Qed.
Lemma lem1349385 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (EQ_MP (@lem1349384 P x C) (@lem1349383 x P C h1)). Qed.
Lemma lem1349386 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1349387 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349385 x P C h1 (@lem1349386 P x h2)). Qed.
Lemma lem1349388 (C : real) (P : real -> Prop) (x : real) (h1 : P x) : term174 P x C.
Proof. exact (fun h0 : term94 P C => @lem1349387 C P x h0 h1). Qed.
Lemma lem1349389 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (h1). Qed.
Lemma lem1349390 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349388 C P x h2 (@lem1349389 P C h1)). Qed.
Lemma lem1349391 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (fun h0 : P x => @lem1349390 C P x h1 h0). Qed.
Lemma lem1349392 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (fun x : real => @lem1349391 x P C h1). Qed.
Lemma lem1349393 (P : real -> Prop) (C : real) : term175 P C.
Proof. exact (fun h0 : term94 P C => @lem1349392 P C h0). Qed.
Lemma lem1349394 (P : real -> Prop) (C : real) (h1 : term94 P C) : term94 P C.
Proof. exact (@lem1349393 P C (@lem1348868 P C h1)). Qed.
Lemma lem1349395 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term155 P C x.
Proof. exact (@lem1349394 P C h1 x). Qed.
Lemma lem1349396 (P : real -> Prop) (x : real) (C : real) : (term155 P C x) = (term156 P x C).
Proof. exact (eq_refl (term155 P C x)). Qed.
Lemma lem1349399 (x : real) (P : real -> Prop) (C : real) (h1 : term94 P C) : term156 P x C.
Proof. exact (EQ_MP (@lem1349396 P x C) (@lem1349395 x P C h1)). Qed.
Lemma lem1349400 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1349444 (P : real -> Prop) (x : real) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1349400 P x) (@lem1348222 P x h1)). Qed.
Lemma lem1349445 (P : real -> Prop) (x : real) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1349444 P x h1)). Qed.
Lemma lem1349446 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1349445 P x h1) (@lem0)). Qed.
Lemma lem1349447 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1349491 (P : real -> Prop) (x : real) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1349447 P x) (@lem1348222 P x h1)). Qed.
Lemma lem1349492 (P : real -> Prop) (x : real) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1349491 P x h1)). Qed.
Lemma lem1349493 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1349492 P x h1) (@lem0)). Qed.
Lemma lem1349494 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349399 x P C h1 (@lem1349493 P x h2)). Qed.
Lemma lem1349495 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) : real_le x C.
Proof. exact (@lem1349381 x P C h1 (@lem1349446 P x h2)). Qed.
Lemma lem1349496 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term172 x C.
Proof. exact (EQ_MP (@lem1349363 C x h3) (@lem1349494 C P x h1 h2)). Qed.
Lemma lem1349497 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term172 x C.
Proof. exact (EQ_MP (@lem1349307 C x h3) (@lem1349495 C P x h1 h2)). Qed.
Lemma lem1349498 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term176 C.
Proof. exact (ex_intro (term177 C) x (@lem1349496 C P x h1 h2 h3)). Qed.
Lemma lem1349499 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term176 C.
Proof. exact (ex_intro (term177 C) x (@lem1349497 C P x h1 h2 h3)). Qed.
Lemma lem1349500 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term37 C.
Proof. exact (@lem1349251 C (@lem1349498 C P x h1 h2 h3)). Qed.
Lemma lem1349501 (C : real) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : P x) (h3 : term37 x) : term37 C.
Proof. exact (@lem1349248 C (@lem1349499 C P x h1 h2 h3)). Qed.
Lemma lem1349502 (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : (term151 r h C) = C.
Proof. exact (@lem1349245 C r h h2 (@lem1349500 C P x h1 h3 h4)). Qed.
Lemma lem1349503 (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : (term151 r h C) = C.
Proof. exact (@lem1349172 C r h h2 (@lem1349501 C P x h1 h3 h4)). Qed.
Lemma lem1349504 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : (term164 B r h C) = (term158 r B C).
Proof. exact (MK_COMB (@lem1349099 r B) (@lem1349502 C r h P x h1 h2 h3 h4)). Qed.
Lemma lem1349505 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : term224 h r B C.
Proof. exact (@lem1349098 h r B C (@lem1349504 B C r h P x h1 h2 h3 h4)). Qed.
Lemma lem1349506 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P C) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term223 h r B C.
Proof. exact (EQ_MP (@lem1349095 h B C r h1) (@lem1349505 B C r h P x h2 h3 h4 h5)). Qed.
Lemma lem1349507 (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : ((term151 r h C) = C) = (term216 P r h C).
Proof. exact (prop_ext (fun h5 : (term151 r h C) = C => @lem1349040 P r h C h1 h5) (fun h5 : term216 P r h C => @lem1349503 C r h P x h1 h2 h3 h4)). Qed.
Lemma lem1349508 (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P C) (h2 : term99 r h) (h3 : P x) (h4 : term37 x) : term216 P r h C.
Proof. exact (EQ_MP (@lem1349507 C r h P x h1 h2 h3 h4) (@lem1349503 C r h P x h1 h2 h3 h4)). Qed.
Lemma lem1349509 (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term94 P C) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term179 P r h C.
Proof. exact (EQ_MP (@lem1348970 P h C r h1) (@lem1349508 C r h P x h2 h3 h4 h5)). Qed.
Lemma lem1349510 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term94 P C) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term163 B h C.
Proof. exact (@lem1348906 h C P r B h2 (@lem1349509 C r h P x h1 h3 h4 h5 h6)). Qed.
Lemma lem1349511 (r : hreal -> real) (P : real -> Prop) (B : hreal) (h : real -> hreal) (C : real) (x : real) (h1 : term100 r) (h2 : term94 P C) (h3 : term99 r h) (h4 : P x) (h5 : term163 B h C) (h6 : term37 x) : term158 r B C.
Proof. exact (@lem1349506 B C r h P x h1 h2 h3 h4 h6 (@lem1348869 B h C h5)). Qed.
Lemma lem1349512 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term94 P C) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : (term163 B h C) = (term158 r B C).
Proof. exact (prop_ext (fun h7 : term163 B h C => @lem1349511 r P B h C x h1 h3 h4 h5 h7 h6) (fun h7 : term158 r B C => @lem1349510 B C r h P x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1349513 (B : hreal) (C : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term94 P C) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term158 r B C.
Proof. exact (EQ_MP (@lem1349512 B C r h P x h1 h2 h3 h4 h5 h6) (@lem1349510 B C r h P x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1349514 (C : real) (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term226 P r B C.
Proof. exact (fun h0 : term94 P C => @lem1349513 B C r h P x h1 h2 h0 h3 h4 h5). Qed.
Lemma lem1349519 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term227 P r B.
Proof. exact (fun C : real => @lem1349514 C B r h P x h1 h2 h3 h4 h5). Qed.
Lemma lem1349520 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : term228 P r B.
Proof. exact (conj (@lem1348867 P B r h h1 h3 h4 h5) (@lem1349519 B r h P x h1 h2 h5 h6 h7)). Qed.
Lemma lem1349521 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : term144 P.
Proof. exact (ex_intro (term229 P) (r B) (@lem1349520 B r h P x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1349522 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term136 P r B) : term134 P r B.
Proof. exact (proj2 (@lem1348552 P r B h1)). Qed.
Lemma lem1349523 (P : real -> Prop) (r : hreal -> real) (B : hreal) (h1 : term136 P r B) : term116 P r B.
Proof. exact (proj1 (@lem1348552 P r B h1)). Qed.
Lemma lem1349524 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : (term134 P r B) = (term144 P).
Proof. exact (prop_ext (fun h8 : term134 P r B => @lem1349521 B r h P x h1 h2 h3 h4 h5 h6 h7) (fun h8 : term144 P => @lem1348553 P r B h2)). Qed.
Lemma lem1349525 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349524 B r h P x h1 h2 h3 h4 h5 h6 h7) (@lem1348553 P r B h2)). Qed.
Lemma lem1349526 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : (term116 P r B) = (term144 P).
Proof. exact (prop_ext (fun h8 : term116 P r B => @lem1349525 B r h P x h1 h2 h3 h4 h5 h6 h7) (fun h8 : term144 P => @lem1348554 P r B h3)). Qed.
Lemma lem1349527 (B : hreal) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term134 P r B) (h3 : term116 P r B) (h4 : term101 r) (h5 : term99 r h) (h6 : P x) (h7 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349526 B r h P x h1 h2 h3 h4 h5 h6 h7) (@lem1348554 P r B h3)). Qed.
Lemma lem1349528 (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (x : real) (h1 : term100 r) (h2 : term116 P r B) (h3 : term101 r) (h4 : term99 r h) (h5 : P x) (h6 : term136 P r B) (h7 : term37 x) : (term134 P r B) = (term144 P).
Proof. exact (prop_ext (fun h8 : term134 P r B => @lem1349527 B r h P x h1 h8 h2 h3 h4 h5 h7) (fun h8 : term144 P => @lem1349522 P r B h6)). Qed.
Lemma lem1349529 (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (x : real) (h1 : term100 r) (h2 : term116 P r B) (h3 : term101 r) (h4 : term99 r h) (h5 : P x) (h6 : term136 P r B) (h7 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349528 h P r B x h1 h2 h3 h4 h5 h6 h7) (@lem1349522 P r B h6)). Qed.
Lemma lem1349530 (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : P x) (h5 : term136 P r B) (h6 : term37 x) : (term116 P r B) = (term144 P).
Proof. exact (prop_ext (fun h7 : term116 P r B => @lem1349529 h P r B x h1 h7 h2 h3 h4 h5 h6) (fun h7 : term144 P => @lem1349523 P r B h5)). Qed.
Lemma lem1349531 (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (B : hreal) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : P x) (h5 : term136 P r B) (h6 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349530 h P r B x h1 h2 h3 h4 h5 h6) (@lem1349523 P r B h5)). Qed.
Lemma lem1349532 (h : real -> hreal) (r : hreal -> real) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : term140 P r) (h5 : P x) (h6 : term37 x) : term144 P.
Proof. exact (ex_elim (@lem1348551 P r h4) (fun B : hreal => fun h0 : term138 P r B => @lem1349531 h P r B x h1 h2 h3 h5 h0 h6)). Qed.
Lemma lem1349533 (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term230 r P.
Proof. exact (fun h0 : term140 P r => @lem1349532 h r P x h1 h2 h3 h0 h4 h5). Qed.
Lemma lem1349534 (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : P x) (h5 : term37 x) : term231 r P.
Proof. exact (@lem1348550 r P (@lem1349533 r h P x h1 h2 h3 h4 h5)). Qed.
Lemma lem1349535 (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term99 r h) (h4 : P x) (h5 : term122 P r) (h6 : term37 x) : term146 r P.
Proof. exact (@lem1349534 r h P x h1 h2 h3 h4 h6 (@lem1348287 P r h5)). Qed.
Lemma lem1349536 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : (term122 P r) = (term146 r P).
Proof. exact (prop_ext (fun h7 : term122 P r => @lem1349535 h P r x h1 h2 h4 h5 h7 h6) (fun h7 : term146 r P => @lem1348547 M r h P x h1 h3 h4 h5 h6)). Qed.
Lemma lem1349537 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term146 r P.
Proof. exact (EQ_MP (@lem1349536 M r h P x h1 h2 h3 h4 h5 h6) (@lem1348547 M r h P x h1 h3 h4 h5 h6)). Qed.
Lemma lem1349538 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term145 r P.
Proof. exact (EQ_MP (@lem1348286 r P) (@lem1349537 M r h P x h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1349539 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term144 P.
Proof. exact (@lem1349538 M r h P x h1 h2 h3 h4 h5 h6 (@lem1348216 P r)). Qed.
Lemma lem1349540 (h : real -> hreal) (r : hreal -> real) (h1 : term96 h r) : term97 h r.
Proof. exact (proj2 (@lem1348225 h r h1)). Qed.
Lemma lem1349542 (h : real -> hreal) (r : hreal -> real) (h1 : term97 h r) : term98 r.
Proof. exact (proj2 (@lem1348226 h r h1)). Qed.
Lemma lem1349543 (h : real -> hreal) (r : hreal -> real) (h1 : term97 h r) : term99 r h.
Proof. exact (proj1 (@lem1348226 h r h1)). Qed.
Lemma lem1349544 (r : hreal -> real) (h1 : term98 r) : term100 r.
Proof. exact (proj2 (@lem1348228 r h1)). Qed.
Lemma lem1349545 (r : hreal -> real) (h1 : term98 r) : term101 r.
Proof. exact (proj1 (@lem1348228 r h1)). Qed.
Lemma lem1349546 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : (term100 r) = (term144 P).
Proof. exact (prop_ext (fun h7 : term100 r => @lem1349539 M r h P x h1 h2 h3 h4 h5 h6) (fun h7 : term144 P => @lem1348230 r h1)). Qed.
Lemma lem1349547 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349546 M r h P x h1 h2 h3 h4 h5 h6) (@lem1348230 r h1)). Qed.
Lemma lem1349548 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : (term101 r) = (term144 P).
Proof. exact (prop_ext (fun h7 : term101 r => @lem1349547 M r h P x h1 h2 h3 h4 h5 h6) (fun h7 : term144 P => @lem1348231 r h2)). Qed.
Lemma lem1349549 (M : real) (r : hreal -> real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term100 r) (h2 : term101 r) (h3 : term94 P M) (h4 : term99 r h) (h5 : P x) (h6 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349548 M r h P x h1 h2 h3 h4 h5 h6) (@lem1348231 r h2)). Qed.
Lemma lem1349550 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term101 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term98 r) (h6 : term37 x) : (term100 r) = (term144 P).
Proof. exact (prop_ext (fun h7 : term100 r => @lem1349549 M r h P x h7 h1 h2 h3 h4 h6) (fun h7 : term144 P => @lem1349544 r h5)). Qed.
Lemma lem1349551 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term101 r) (h2 : term94 P M) (h3 : term99 r h) (h4 : P x) (h5 : term98 r) (h6 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349550 M h P r x h1 h2 h3 h4 h5 h6) (@lem1349544 r h5)). Qed.
Lemma lem1349552 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term98 r) (h5 : term37 x) : (term101 r) = (term144 P).
Proof. exact (prop_ext (fun h6 : term101 r => @lem1349551 M h P r x h6 h1 h2 h3 h4 h5) (fun h6 : term144 P => @lem1349545 r h4)). Qed.
Lemma lem1349553 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term98 r) (h5 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349552 M h P r x h1 h2 h3 h4 h5) (@lem1349545 r h4)). Qed.
Lemma lem1349554 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term98 r) (h5 : term37 x) : (term99 r h) = (term144 P).
Proof. exact (prop_ext (fun h6 : term99 r h => @lem1349553 M h P r x h1 h2 h3 h4 h5) (fun h6 : term144 P => @lem1348229 r h h2)). Qed.
Lemma lem1349555 (M : real) (h : real -> hreal) (P : real -> Prop) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term98 r) (h5 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349554 M h P r x h1 h2 h3 h4 h5) (@lem1348229 r h h2)). Qed.
Lemma lem1349556 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term97 h r) (h5 : term37 x) : (term98 r) = (term144 P).
Proof. exact (prop_ext (fun h6 : term98 r => @lem1349555 M h P r x h1 h2 h3 h6 h5) (fun h6 : term144 P => @lem1349542 h r h4)). Qed.
Lemma lem1349557 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : term99 r h) (h3 : P x) (h4 : term97 h r) (h5 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349556 M P h r x h1 h2 h3 h4 h5) (@lem1349542 h r h4)). Qed.
Lemma lem1349558 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term97 h r) (h4 : term37 x) : (term99 r h) = (term144 P).
Proof. exact (prop_ext (fun h5 : term99 r h => @lem1349557 M P h r x h1 h5 h2 h3 h4) (fun h5 : term144 P => @lem1349543 h r h3)). Qed.
Lemma lem1349559 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term97 h r) (h4 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349558 M P h r x h1 h2 h3 h4) (@lem1349543 h r h3)). Qed.
Lemma lem1349560 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term96 h r) (h4 : term37 x) : (term97 h r) = (term144 P).
Proof. exact (prop_ext (fun h5 : term97 h r => @lem1349559 M P h r x h1 h2 h5 h4) (fun h5 : term144 P => @lem1349540 h r h3)). Qed.
Lemma lem1349561 (M : real) (P : real -> Prop) (h : real -> hreal) (r : hreal -> real) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term96 h r) (h4 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349560 M P h r x h1 h2 h3 h4) (@lem1349540 h r h3)). Qed.
Lemma lem1349562 (M : real) (h : real -> hreal) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : term95 h) (h3 : P x) (h4 : term37 x) : term144 P.
Proof. exact (ex_elim (@lem1348224 h h2) (fun r : hreal -> real => fun h0 : term232 h r => @lem1349561 M P h r x h1 h3 h0 h4)). Qed.
Lemma lem1349563 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : term144 P.
Proof. exact (ex_elim (@lem1347548) (fun h : real -> hreal => fun h0 : term233 h => @lem1349562 M h P x h1 h0 h2 h3)). Qed.
Lemma lem1349564 (P : real -> Prop) (h1 : term90 P) : term91 P.
Proof. exact (proj2 (@lem1348217 P h1)). Qed.
Lemma lem1349565 (P : real -> Prop) (h1 : term90 P) : term92 P.
Proof. exact (proj1 (@lem1348217 P h1)). Qed.
Lemma lem1349566 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : (term94 P M) = (term144 P).
Proof. exact (prop_ext (fun h4 : term94 P M => @lem1349563 M P x h1 h2 h3) (fun h4 : term144 P => @lem1348223 P M h1)). Qed.
Lemma lem1349567 (M : real) (P : real -> Prop) (x : real) (h1 : term94 P M) (h2 : P x) (h3 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349566 M P x h1 h2 h3) (@lem1348223 P M h1)). Qed.
Lemma lem1349568 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term37 x) : term144 P.
Proof. exact (ex_elim (@lem1348218 P h1) (fun M : real => fun h0 : term234 P M => @lem1349567 M P x h0 h2 h3)). Qed.
Lemma lem1349569 (P : real -> Prop) (x : real) (h1 : term93 P x) : term37 x.
Proof. exact (proj2 (@lem1348220 P x h1)). Qed.
Lemma lem1349570 (P : real -> Prop) (x : real) (h1 : term93 P x) : P x.
Proof. exact (proj1 (@lem1348220 P x h1)). Qed.
Lemma lem1349571 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term37 x) : (term37 x) = (term144 P).
Proof. exact (prop_ext (fun h4 : term37 x => @lem1349568 P x h1 h2 h3) (fun h4 : term144 P => @lem1348221 x h3)). Qed.
Lemma lem1349572 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349571 P x h1 h2 h3) (@lem1348221 x h3)). Qed.
Lemma lem1349573 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term37 x) : (P x) = (term144 P).
Proof. exact (prop_ext (fun h4 : P x => @lem1349572 P x h1 h2 h3) (fun h4 : term144 P => @lem1348222 P x h2)). Qed.
Lemma lem1349574 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term37 x) : term144 P.
Proof. exact (EQ_MP (@lem1349573 P x h1 h2 h3) (@lem1348222 P x h2)). Qed.
Lemma lem1349575 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term93 P x) : (term37 x) = (term144 P).
Proof. exact (prop_ext (fun h4 : term37 x => @lem1349574 P x h1 h2 h4) (fun h4 : term144 P => @lem1349569 P x h3)). Qed.
Lemma lem1349576 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : P x) (h3 : term93 P x) : term144 P.
Proof. exact (EQ_MP (@lem1349575 P x h1 h2 h3) (@lem1349569 P x h3)). Qed.
Lemma lem1349577 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : term93 P x) : (P x) = (term144 P).
Proof. exact (prop_ext (fun h3 : P x => @lem1349576 P x h1 h3 h2) (fun h3 : term144 P => @lem1349570 P x h2)). Qed.
Lemma lem1349578 (P : real -> Prop) (x : real) (h1 : term91 P) (h2 : term93 P x) : term144 P.
Proof. exact (EQ_MP (@lem1349577 P x h1 h2) (@lem1349570 P x h2)). Qed.
Lemma lem1349579 (P : real -> Prop) (h1 : term91 P) (h2 : term92 P) : term144 P.
Proof. exact (ex_elim (@lem1348219 P h2) (fun x : real => fun h0 : term235 P x => @lem1349578 P x h1 h0)). Qed.
Lemma lem1349580 (P : real -> Prop) (h1 : term92 P) (h2 : term90 P) : (term91 P) = (term144 P).
Proof. exact (prop_ext (fun h3 : term91 P => @lem1349579 P h3 h1) (fun h3 : term144 P => @lem1349564 P h2)). Qed.
Lemma lem1349581 (P : real -> Prop) (h1 : term92 P) (h2 : term90 P) : term144 P.
Proof. exact (EQ_MP (@lem1349580 P h1 h2) (@lem1349564 P h2)). Qed.
Lemma lem1349582 (P : real -> Prop) (h1 : term90 P) : (term92 P) = (term144 P).
Proof. exact (prop_ext (fun h2 : term92 P => @lem1349581 P h2 h1) (fun h2 : term144 P => @lem1349565 P h1)). Qed.
Lemma lem1349583 (P : real -> Prop) (h1 : term90 P) : term144 P.
Proof. exact (EQ_MP (@lem1349582 P h1) (@lem1349565 P h1)). Qed.
Lemma lem1349584 (P : real -> Prop) : term236 P.
Proof. exact (fun h0 : term90 P => @lem1349583 P h0). Qed.
Lemma lem1349589 : term237.
Proof. exact (fun P : real -> Prop => @lem1349584 P). Qed.

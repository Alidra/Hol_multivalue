Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_DIV2_EQ_term_abbrevs.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1629612 (x : real) : term0 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1629613 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1629615 (x : real) : term3 x.
Proof. exact (@lem1600741 x). Qed.
Lemma lem1629616 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1629617 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1629616 x) (@lem1629615 x)). Qed.
Lemma lem1629618 (x : real) (y : real) : term5 x y.
Proof. exact (@lem1629617 x y). Qed.
Lemma lem1629619 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1629620 (x : real) (y : real) : term6 x y.
Proof. exact (EQ_MP (@lem1629619 x y) (@lem1629618 x y)). Qed.
Lemma lem1629621 (x : real) (y : real) (z : real) : term7 x y z.
Proof. exact (@lem1629620 x y z). Qed.
Lemma lem1629622 (z : real) (x : real) (y : real) : (term7 x y z) = (term8 z x y).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1629623 (z : real) (x : real) (y : real) : term8 z x y.
Proof. exact (EQ_MP (@lem1629622 z x y) (@lem1629621 x y z)). Qed.
Lemma lem1629624 (z : real) (h1 : term2 z) : term2 z.
Proof. exact (h1). Qed.
Lemma lem1629625 (x : real) (y : real) (z : real) (h1 : term2 z) : (term9 x y z) = (real_le x y).
Proof. exact (@lem1629623 z x y (@lem1629624 z h1)). Qed.
Lemma lem1629631 (x : real) : term10 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1629632 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1629633 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1629632 x) (@lem1629631 x)). Qed.
Lemma lem1629634 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1629633 x y). Qed.
Lemma lem1629635 (x : real) (y : real) : (term12 x y) = ((real_div x y) = (term13 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1629652 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1629653 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem1629652 p q p' q'). Qed.
Lemma lem1629654 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem1629653 p q p'). Qed.
Lemma lem1629655 (z : real) (x : real) (y : real) : term17 z x y.
Proof. exact (@lem1629654 (term2 z) ((term18 x y z) = (real_le x y))). Qed.
Lemma lem1629656 (z : real) (x : real) (y : real) (p' : Prop) : term19 z x y p'.
Proof. exact (@lem1629655 z x y p'). Qed.
Lemma lem1629657 (z : real) (x : real) (y : real) (p' : Prop) : (term19 z x y p') = (term20 z x y p').
Proof. exact (eq_refl (term19 z x y p')). Qed.
Lemma lem1629658 (z : real) (x : real) (y : real) (p' : Prop) : term20 z x y p'.
Proof. exact (EQ_MP (@lem1629657 z x y p') (@lem1629656 z x y p')). Qed.
Lemma lem1629659 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term21 z x y p' q'.
Proof. exact (@lem1629658 z x y p' q'). Qed.
Lemma lem1629660 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : (term21 z x y p' q') = (term22 z x y p' q').
Proof. exact (eq_refl (term21 z x y p' q')). Qed.
Lemma lem1629661 (z : real) (x : real) (y : real) (p' : Prop) (q' : Prop) : term22 z x y p' q'.
Proof. exact (EQ_MP (@lem1629660 z x y p' q') (@lem1629659 z x y p' q')). Qed.
Lemma lem1629662 (z : real) : (term2 z) = (term2 z).
Proof. exact (eq_refl (term2 z)). Qed.
Lemma lem1629663 (x : real) (y : real) (z : real) (q' : Prop) : term23 x y z q'.
Proof. exact (@lem1629661 z x y (term2 z) q'). Qed.
Lemma lem1629664 (x : real) (y : real) (z : real) (q' : Prop) : term24 x y z q'.
Proof. exact (@lem1629663 x y z q' (@lem1629662 z)). Qed.
Lemma lem1629665 (z : real) (h1 : term2 z) : term2 z.
Proof. exact (h1). Qed.
Lemma lem1629666 (z : real) : (term2 z) = ((term2 z) = True).
Proof. exact (@lem7 (term2 z)). Qed.
Lemma lem1629671 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1629635 x y) (@lem1629634 x y)). Qed.
Lemma lem1629672 (x : real) (z : real) : (real_div x z) = (term13 x z).
Proof. exact (@lem1629671 x z). Qed.
Lemma lem1629673 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1629674 (x : real) (z : real) : (term25 x z) = (term26 x z).
Proof. exact (MK_COMB (@lem1629673) (@lem1629672 x z)). Qed.
Lemma lem1629676 (x : real) (y : real) : (real_div x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1629635 x y) (@lem1629634 x y)). Qed.
Lemma lem1629677 (y : real) (z : real) : (real_div y z) = (term13 y z).
Proof. exact (@lem1629676 y z). Qed.
Lemma lem1629678 (x : real) (y : real) (z : real) : (term18 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem1629674 x z) (@lem1629677 y z)). Qed.
Lemma lem1629680 (z : real) (x : real) (y : real) : term8 z x y.
Proof. exact (fun h0 : term2 z => @lem1629625 x y z h0). Qed.
Lemma lem1629681 (z : real) (x : real) (y : real) : term28 z x y.
Proof. exact (@lem1629680 (real_inv z) x y). Qed.
Lemma lem1629683 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1629613 x) (@lem1629612 x)). Qed.
Lemma lem1629684 (z : real) : (term1 z) = (term2 z).
Proof. exact (@lem1629683 z). Qed.
Lemma lem1629686 (z : real) (h1 : term2 z) : (term2 z) = True.
Proof. exact (EQ_MP (@lem1629666 z) (@lem1629665 z h1)). Qed.
Lemma lem1629687 (z : real) (h1 : term2 z) : (term1 z) = True.
Proof. exact (TRANS (@lem1629684 z) (@lem1629686 z h1)). Qed.
Lemma lem1629688 (z : real) (h1 : term2 z) : True = (term1 z).
Proof. exact (SYM (@lem1629687 z h1)). Qed.
Lemma lem1629689 (z : real) (h1 : term2 z) : term1 z.
Proof. exact (EQ_MP (@lem1629688 z h1) (@lem0)). Qed.
Lemma lem1629690 (x : real) (y : real) (z : real) (h1 : term2 z) : (term27 x y z) = (real_le x y).
Proof. exact (@lem1629681 z x y (@lem1629689 z h1)). Qed.
Lemma lem1629691 (x : real) (y : real) (z : real) (h1 : term2 z) : (term18 x y z) = (real_le x y).
Proof. exact (TRANS (@lem1629678 x y z) (@lem1629690 x y z h1)). Qed.
Lemma lem1629692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629693 (x : real) (y : real) (z : real) (h1 : term2 z) : (term29 x y z) = (term30 x y).
Proof. exact (MK_COMB (@lem1629692) (@lem1629691 x y z h1)). Qed.
Lemma lem1629694 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1629695 (x : real) (y : real) (z : real) (h1 : term2 z) : ((term18 x y z) = (real_le x y)) = ((real_le x y) = (real_le x y)).
Proof. exact (MK_COMB (@lem1629693 x y z h1) (@lem1629694 x y)). Qed.
Lemma lem1629697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1629698 (x : Prop) : (x = x) = True.
Proof. exact (@lem1629697 Prop x). Qed.
Lemma lem1629699 (x : real) (y : real) : ((real_le x y) = (real_le x y)) = True.
Proof. exact (@lem1629698 (real_le x y)). Qed.
Lemma lem1629700 (x : real) (y : real) (z : real) (h1 : term2 z) : ((term18 x y z) = (real_le x y)) = True.
Proof. exact (TRANS (@lem1629695 x y z h1) (@lem1629699 x y)). Qed.
Lemma lem1629701 (z : real) (x : real) (y : real) : term31 z x y.
Proof. exact (fun h0 : term2 z => @lem1629700 x y z h0). Qed.
Lemma lem1629702 (x : real) (y : real) (z : real) : term32 x y z.
Proof. exact (@lem1629664 x y z True). Qed.
Lemma lem1629703 (x : real) (y : real) (z : real) : (term33 z x y) = (term34 z).
Proof. exact (@lem1629702 x y z (@lem1629701 z x y)). Qed.
Lemma lem1629705 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1629706 (z : real) : (term34 z) = True.
Proof. exact (@lem1629705 (term2 z)). Qed.
Lemma lem1629707 (z : real) (x : real) (y : real) : (term33 z x y) = True.
Proof. exact (TRANS (@lem1629703 x y z) (@lem1629706 z)). Qed.
Lemma lem1629708 (x : real) (y : real) : (term35 x y) = term36.
Proof. exact (fun_ext (fun z : real => @lem1629707 z x y)). Qed.
Lemma lem1629709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629710 (x : real) (y : real) : (term37 x y) = term38.
Proof. exact (MK_COMB (@lem1629709) (@lem1629708 x y)). Qed.
Lemma lem1629712 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629713 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629712 real t). Qed.
Lemma lem1629714 : term38 = True.
Proof. exact (@lem1629713 True). Qed.
Lemma lem1629715 (x : real) (y : real) : (term37 x y) = True.
Proof. exact (TRANS (@lem1629710 x y) (@lem1629714)). Qed.
Lemma lem1629716 (x : real) : (term41 x) = term36.
Proof. exact (fun_ext (fun y : real => @lem1629715 x y)). Qed.
Lemma lem1629717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629718 (x : real) : (term42 x) = term38.
Proof. exact (MK_COMB (@lem1629717) (@lem1629716 x)). Qed.
Lemma lem1629720 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629721 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629720 real t). Qed.
Lemma lem1629722 : term38 = True.
Proof. exact (@lem1629721 True). Qed.
Lemma lem1629723 (x : real) : (term42 x) = True.
Proof. exact (TRANS (@lem1629718 x) (@lem1629722)). Qed.
Lemma lem1629724 : term43 = term36.
Proof. exact (fun_ext (fun x : real => @lem1629723 x)). Qed.
Lemma lem1629725 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629726 : term44 = term38.
Proof. exact (MK_COMB (@lem1629725) (@lem1629724)). Qed.
Lemma lem1629728 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629729 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1629728 real t). Qed.
Lemma lem1629730 : term38 = True.
Proof. exact (@lem1629729 True). Qed.
Lemma lem1629731 : term44 = True.
Proof. exact (TRANS (@lem1629726) (@lem1629730)). Qed.
Lemma lem1629732 : True = term44.
Proof. exact (SYM (@lem1629731)). Qed.
Lemma lem1629733 : term44.
Proof. exact (EQ_MP (@lem1629732) (@lem0)). Qed.

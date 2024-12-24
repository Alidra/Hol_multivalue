Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LE_INCLUDED_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_RESTRICT_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import REAL_EQ_IMP_LE_spec.
Require Import SUM_IMAGE_GEN_spec.
Require Import SUM_LE_spec.
Require Import SUM_POS_LE_spec.
Require Import SUM_SING_spec.
Require Import SUM_SUBSET_SIMPLE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7190624 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7190625 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term1 A u.
Proof. exact (@lem7190624 A h1 u). Qed.
Lemma lem7190626 {A : Type'} (u : A -> Prop) : (term1 A u) = (term2 A u).
Proof. exact (eq_refl (term1 A u)). Qed.
Lemma lem7190627 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term2 A u.
Proof. exact (EQ_MP (@lem7190626 A u) (@lem7190625 A u h1)). Qed.
Lemma lem7190628 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term3 A u v.
Proof. exact (@lem7190627 A u h1 v). Qed.
Lemma lem7190629 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term3 A u v) = (term4 A u v).
Proof. exact (eq_refl (term3 A u v)). Qed.
Lemma lem7190630 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term4 A u v.
Proof. exact (EQ_MP (@lem7190629 A u v) (@lem7190628 A u v h1)). Qed.
Lemma lem7190631 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term5 A u v f.
Proof. exact (@lem7190630 A u v h1 f). Qed.
Lemma lem7190632 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term5 A u v f) = (term6 A u v f).
Proof. exact (eq_refl (term5 A u v f)). Qed.
Lemma lem7190633 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term6 A u v f.
Proof. exact (EQ_MP (@lem7190632 A u v f) (@lem7190631 A u v f h1)). Qed.
Lemma lem7190634 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A v u f) : term7 A v u f.
Proof. exact (h1). Qed.
Lemma lem7190635 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term7 A v u f) : term8 A u v f.
Proof. exact (@lem7190633 A u v f h1 (@lem7190634 A v u f h2)). Qed.
Lemma lem7190636 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term7 A v u f) : term9 A u v f.
Proof. exact (fun h0 : term0 A => @lem7190635 A v u f h0 h1). Qed.
Lemma lem7190637 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7190638 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term7 A v u f) : term8 A u v f.
Proof. exact (@lem7190636 A v u f h2 (@lem7190637 A h1)). Qed.
Lemma lem7190639 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term0 A) : term6 A u v f.
Proof. exact (fun h0 : term7 A v u f => @lem7190638 A v u f h1 h0). Qed.
Lemma lem7190640 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term0 A) : term4 A u v.
Proof. exact (fun f : A -> real => @lem7190639 A u v f h1). Qed.
Lemma lem7190641 {A : Type'} (u : A -> Prop) (h1 : term0 A) : term2 A u.
Proof. exact (fun v : A -> Prop => @lem7190640 A u v h1). Qed.
Lemma lem7190642 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun u : A -> Prop => @lem7190641 A u h1). Qed.
Lemma lem7190643 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem7190642 A h0). Qed.
Lemma lem7190644 {A : Type'} : term0 A.
Proof. exact (@lem7190643 A (@lem7177445 A)). Qed.
Lemma lem7190645 {A : Type'} (u : A -> Prop) : term1 A u.
Proof. exact (@lem7190644 A u). Qed.
Lemma lem7190646 {A : Type'} (u : A -> Prop) : (term1 A u) = (term2 A u).
Proof. exact (eq_refl (term1 A u)). Qed.
Lemma lem7190647 {A : Type'} (u : A -> Prop) : term2 A u.
Proof. exact (EQ_MP (@lem7190646 A u) (@lem7190645 A u)). Qed.
Lemma lem7190648 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term3 A u v.
Proof. exact (@lem7190647 A u v). Qed.
Lemma lem7190649 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term3 A u v) = (term4 A u v).
Proof. exact (eq_refl (term3 A u v)). Qed.
Lemma lem7190650 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term4 A u v.
Proof. exact (EQ_MP (@lem7190649 A u v) (@lem7190648 A u v)). Qed.
Lemma lem7190651 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term5 A u v f.
Proof. exact (@lem7190650 A u v f). Qed.
Lemma lem7190652 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term5 A u v f) = (term6 A u v f).
Proof. exact (eq_refl (term5 A u v f)). Qed.
Lemma lem7190654 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190655 (x : real) (h1 : term11) : term12 x.
Proof. exact (@lem7190654 h1 x). Qed.
Lemma lem7190656 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem7190657 (x : real) (h1 : term11) : term13 x.
Proof. exact (EQ_MP (@lem7190656 x) (@lem7190655 x h1)). Qed.
Lemma lem7190658 (x : real) (y : real) (h1 : term11) : term14 x y.
Proof. exact (@lem7190657 x h1 y). Qed.
Lemma lem7190659 (y : real) (x : real) : (term14 x y) = (term15 y x).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem7190660 (y : real) (x : real) (h1 : term11) : term15 y x.
Proof. exact (EQ_MP (@lem7190659 y x) (@lem7190658 x y h1)). Qed.
Lemma lem7190661 (y : real) (x : real) (z : real) (h1 : term11) : term16 y x z.
Proof. exact (@lem7190660 y x h1 z). Qed.
Lemma lem7190662 (y : real) (x : real) (z : real) : (term16 y x z) = (term17 y x z).
Proof. exact (eq_refl (term16 y x z)). Qed.
Lemma lem7190663 (y : real) (x : real) (z : real) (h1 : term11) : term17 y x z.
Proof. exact (EQ_MP (@lem7190662 y x z) (@lem7190661 y x z h1)). Qed.
Lemma lem7190664 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term18 x y z.
Proof. exact (h1). Qed.
Lemma lem7190665 (x : real) (y : real) (z : real) (h1 : term11) (h2 : term18 x y z) : real_le x z.
Proof. exact (@lem7190663 y x z h1 (@lem7190664 x y z h2)). Qed.
Lemma lem7190666 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term19 x z.
Proof. exact (fun h0 : term11 => @lem7190665 x y z h0 h1). Qed.
Lemma lem7190667 (x : real) (z : real) (h1 : term20 x z) : term20 x z.
Proof. exact (h1). Qed.
Lemma lem7190668 (x : real) (z : real) (h1 : term20 x z) : term19 x z.
Proof. exact (ex_elim (@lem7190667 x z h1) (fun y : real => fun h0 : term21 x z y => @lem7190666 x y z h0)). Qed.
Lemma lem7190669 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190670 (x : real) (z : real) (h1 : term11) (h2 : term20 x z) : real_le x z.
Proof. exact (@lem7190668 x z h2 (@lem7190669 h1)). Qed.
Lemma lem7190671 (x : real) (z : real) (h1 : term11) : term22 x z.
Proof. exact (fun h0 : term20 x z => @lem7190670 x z h1 h0). Qed.
Lemma lem7190672 (x : real) (h1 : term11) : term23 x.
Proof. exact (fun z : real => @lem7190671 x z h1). Qed.
Lemma lem7190673 (h1 : term11) : term24.
Proof. exact (fun x : real => @lem7190672 x h1). Qed.
Lemma lem7190674 : term25.
Proof. exact (fun h0 : term11 => @lem7190673 h0). Qed.
Lemma lem7190675 : term24.
Proof. exact (@lem7190674 (@lem1339577)). Qed.
Lemma lem7190676 (x : real) : term26 x.
Proof. exact (@lem7190675 x). Qed.
Lemma lem7190677 (x : real) : (term26 x) = (term23 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem7190678 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem7190677 x) (@lem7190676 x)). Qed.
Lemma lem7190679 (x : real) (z : real) : term27 x z.
Proof. exact (@lem7190678 x z). Qed.
Lemma lem7190680 (x : real) (z : real) : (term27 x z) = (term22 x z).
Proof. exact (eq_refl (term27 x z)). Qed.
Lemma lem7190682 {_132081 : Type'} (h1 : term28 _132081) : term28 _132081.
Proof. exact (h1). Qed.
Lemma lem7190683 {_132081 : Type'} (f : _132081 -> real) (h1 : term28 _132081) : term29 _132081 f.
Proof. exact (@lem7190682 _132081 h1 f). Qed.
Lemma lem7190684 {_132081 : Type'} (f : _132081 -> real) : (term29 _132081 f) = (term30 _132081 f).
Proof. exact (eq_refl (term29 _132081 f)). Qed.
Lemma lem7190685 {_132081 : Type'} (f : _132081 -> real) (h1 : term28 _132081) : term30 _132081 f.
Proof. exact (EQ_MP (@lem7190684 _132081 f) (@lem7190683 _132081 f h1)). Qed.
Lemma lem7190686 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term28 _132081) : term31 _132081 f g.
Proof. exact (@lem7190685 _132081 f h1 g). Qed.
Lemma lem7190687 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) : (term31 _132081 f g) = (term32 _132081 f g).
Proof. exact (eq_refl (term31 _132081 f g)). Qed.
Lemma lem7190688 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (h1 : term28 _132081) : term32 _132081 f g.
Proof. exact (EQ_MP (@lem7190687 _132081 f g) (@lem7190686 _132081 f g h1)). Qed.
Lemma lem7190689 {_132081 : Type'} (f : _132081 -> real) (g : _132081 -> real) (s : _132081 -> Prop) (h1 : term28 _132081) : term33 _132081 f g s.
Proof. exact (@lem7190688 _132081 f g h1 s). Qed.
Lemma lem7190690 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term33 _132081 f g s) = (term34 _132081 f s g).
Proof. exact (eq_refl (term33 _132081 f g s)). Qed.
Lemma lem7190691 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term28 _132081) : term34 _132081 f s g.
Proof. exact (EQ_MP (@lem7190690 _132081 f s g) (@lem7190689 _132081 f g s h1)). Qed.
Lemma lem7190692 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term35 _132081 s f g) : term35 _132081 s f g.
Proof. exact (h1). Qed.
Lemma lem7190693 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term28 _132081) (h2 : term35 _132081 s f g) : term36 _132081 f s g.
Proof. exact (@lem7190691 _132081 f s g h1 (@lem7190692 _132081 s f g h2)). Qed.
Lemma lem7190694 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term35 _132081 s f g) : term37 _132081 f s g.
Proof. exact (fun h0 : term28 _132081 => @lem7190693 _132081 s f g h0 h1). Qed.
Lemma lem7190695 {_132081 : Type'} (h1 : term28 _132081) : term28 _132081.
Proof. exact (h1). Qed.
Lemma lem7190696 {_132081 : Type'} (s : _132081 -> Prop) (f : _132081 -> real) (g : _132081 -> real) (h1 : term28 _132081) (h2 : term35 _132081 s f g) : term36 _132081 f s g.
Proof. exact (@lem7190694 _132081 s f g h2 (@lem7190695 _132081 h1)). Qed.
Lemma lem7190697 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) (h1 : term28 _132081) : term34 _132081 f s g.
Proof. exact (fun h0 : term35 _132081 s f g => @lem7190696 _132081 s f g h1 h0). Qed.
Lemma lem7190698 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (h1 : term28 _132081) : term38 _132081 f s.
Proof. exact (fun g : _132081 -> real => @lem7190697 _132081 f s g h1). Qed.
Lemma lem7190699 {_132081 : Type'} (f : _132081 -> real) (h1 : term28 _132081) : term39 _132081 f.
Proof. exact (fun s : _132081 -> Prop => @lem7190698 _132081 f s h1). Qed.
Lemma lem7190700 {_132081 : Type'} (h1 : term28 _132081) : term40 _132081.
Proof. exact (fun f : _132081 -> real => @lem7190699 _132081 f h1). Qed.
Lemma lem7190701 {_132081 : Type'} : term41 _132081.
Proof. exact (fun h0 : term28 _132081 => @lem7190700 _132081 h0). Qed.
Lemma lem7190702 {_132081 : Type'} : term40 _132081.
Proof. exact (@lem7190701 _132081 (@lem7071845 _132081)). Qed.
Lemma lem7190703 {_132081 : Type'} (f : _132081 -> real) : term42 _132081 f.
Proof. exact (@lem7190702 _132081 f). Qed.
Lemma lem7190704 {_132081 : Type'} (f : _132081 -> real) : (term42 _132081 f) = (term39 _132081 f).
Proof. exact (eq_refl (term42 _132081 f)). Qed.
Lemma lem7190705 {_132081 : Type'} (f : _132081 -> real) : term39 _132081 f.
Proof. exact (EQ_MP (@lem7190704 _132081 f) (@lem7190703 _132081 f)). Qed.
Lemma lem7190706 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term43 _132081 f s.
Proof. exact (@lem7190705 _132081 f s). Qed.
Lemma lem7190707 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : (term43 _132081 f s) = (term38 _132081 f s).
Proof. exact (eq_refl (term43 _132081 f s)). Qed.
Lemma lem7190708 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) : term38 _132081 f s.
Proof. exact (EQ_MP (@lem7190707 _132081 f s) (@lem7190706 _132081 f s)). Qed.
Lemma lem7190709 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term44 _132081 f s g.
Proof. exact (@lem7190708 _132081 f s g). Qed.
Lemma lem7190710 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : (term44 _132081 f s g) = (term34 _132081 f s g).
Proof. exact (eq_refl (term44 _132081 f s g)). Qed.
Lemma lem7190712 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190713 (x : real) (h1 : term11) : term12 x.
Proof. exact (@lem7190712 h1 x). Qed.
Lemma lem7190714 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem7190715 (x : real) (h1 : term11) : term13 x.
Proof. exact (EQ_MP (@lem7190714 x) (@lem7190713 x h1)). Qed.
Lemma lem7190716 (x : real) (y : real) (h1 : term11) : term14 x y.
Proof. exact (@lem7190715 x h1 y). Qed.
Lemma lem7190717 (y : real) (x : real) : (term14 x y) = (term15 y x).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem7190718 (y : real) (x : real) (h1 : term11) : term15 y x.
Proof. exact (EQ_MP (@lem7190717 y x) (@lem7190716 x y h1)). Qed.
Lemma lem7190719 (y : real) (x : real) (z : real) (h1 : term11) : term16 y x z.
Proof. exact (@lem7190718 y x h1 z). Qed.
Lemma lem7190720 (y : real) (x : real) (z : real) : (term16 y x z) = (term17 y x z).
Proof. exact (eq_refl (term16 y x z)). Qed.
Lemma lem7190721 (y : real) (x : real) (z : real) (h1 : term11) : term17 y x z.
Proof. exact (EQ_MP (@lem7190720 y x z) (@lem7190719 y x z h1)). Qed.
Lemma lem7190722 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term18 x y z.
Proof. exact (h1). Qed.
Lemma lem7190723 (x : real) (y : real) (z : real) (h1 : term11) (h2 : term18 x y z) : real_le x z.
Proof. exact (@lem7190721 y x z h1 (@lem7190722 x y z h2)). Qed.
Lemma lem7190724 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term19 x z.
Proof. exact (fun h0 : term11 => @lem7190723 x y z h0 h1). Qed.
Lemma lem7190725 (x : real) (z : real) (h1 : term20 x z) : term20 x z.
Proof. exact (h1). Qed.
Lemma lem7190726 (x : real) (z : real) (h1 : term20 x z) : term19 x z.
Proof. exact (ex_elim (@lem7190725 x z h1) (fun y : real => fun h0 : term21 x z y => @lem7190724 x y z h0)). Qed.
Lemma lem7190727 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190728 (x : real) (z : real) (h1 : term11) (h2 : term20 x z) : real_le x z.
Proof. exact (@lem7190726 x z h2 (@lem7190727 h1)). Qed.
Lemma lem7190729 (x : real) (z : real) (h1 : term11) : term22 x z.
Proof. exact (fun h0 : term20 x z => @lem7190728 x z h1 h0). Qed.
Lemma lem7190730 (x : real) (h1 : term11) : term23 x.
Proof. exact (fun z : real => @lem7190729 x z h1). Qed.
Lemma lem7190731 (h1 : term11) : term24.
Proof. exact (fun x : real => @lem7190730 x h1). Qed.
Lemma lem7190732 : term25.
Proof. exact (fun h0 : term11 => @lem7190731 h0). Qed.
Lemma lem7190733 : term24.
Proof. exact (@lem7190732 (@lem1339577)). Qed.
Lemma lem7190734 (x : real) : term26 x.
Proof. exact (@lem7190733 x). Qed.
Lemma lem7190735 (x : real) : (term26 x) = (term23 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem7190736 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem7190735 x) (@lem7190734 x)). Qed.
Lemma lem7190737 (x : real) (z : real) : term27 x z.
Proof. exact (@lem7190736 x z). Qed.
Lemma lem7190738 (x : real) (z : real) : (term27 x z) = (term22 x z).
Proof. exact (eq_refl (term27 x z)). Qed.
Lemma lem7190745 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term45 A B s f g)) : (@sum A s g) = (term45 A B s f g).
Proof. exact (h1). Qed.
Lemma lem7190746 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term45 A B s f g)) : (term45 A B s f g) = (@sum A s g).
Proof. exact (SYM (@lem7190745 A B s f g h1)). Qed.
Lemma lem7190747 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) (h1 : (term45 A B s f g) = (@sum A s g)) : (term45 A B s f g) = (@sum A s g).
Proof. exact (h1). Qed.
Lemma lem7190748 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) (h1 : (term45 A B s f g) = (@sum A s g)) : (@sum A s g) = (term45 A B s f g).
Proof. exact (SYM (@lem7190747 A B f s g h1)). Qed.
Lemma lem7190749 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : ((@sum A s g) = (term45 A B s f g)) = ((term45 A B s f g) = (@sum A s g)).
Proof. exact (prop_ext (fun h1 : (@sum A s g) = (term45 A B s f g) => @lem7190746 A B s f g h1) (fun h1 : (term45 A B s f g) = (@sum A s g) => @lem7190748 A B f s g h1)). Qed.
Lemma lem7190750 {A : Type'} (s : A -> Prop) : (term46 A s) = (term46 A s).
Proof. exact (eq_refl (term46 A s)). Qed.
Lemma lem7190751 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : (term47 A B s f g) = (term48 A B f s g).
Proof. exact (MK_COMB (@lem7190750 A s) (@lem7190749 A B f s g)). Qed.
Lemma lem7190752 {A B : Type'} (f : A -> B) (g : A -> real) : (term49 A B f g) = (term50 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7190751 A B f s g)). Qed.
Lemma lem7190753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7190754 {A B : Type'} (f : A -> B) (g : A -> real) : (term51 A B f g) = (term52 A B f g).
Proof. exact (MK_COMB (@lem7190753 A) (@lem7190752 A B f g)). Qed.
Lemma lem7190755 {A B : Type'} (f : A -> B) : (term53 A B f) = (term54 A B f).
Proof. exact (fun_ext (fun g : A -> real => @lem7190754 A B f g)). Qed.
Lemma lem7190756 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7190757 {A B : Type'} (f : A -> B) : (term55 A B f) = (term56 A B f).
Proof. exact (MK_COMB (@lem7190756 A) (@lem7190755 A B f)). Qed.
Lemma lem7190758 {A B : Type'} : (term57 A B) = (term58 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7190757 A B f)). Qed.
Lemma lem7190759 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7190760 {A B : Type'} : (term59 A B) = (term60 A B).
Proof. exact (MK_COMB (@lem7190759 A B) (@lem7190758 A B)). Qed.
Lemma lem7190761 {A B : Type'} : term60 A B.
Proof. exact (EQ_MP (@lem7190760 A B) (@lem7159247 A B)). Qed.
Lemma lem7190762 {A B : Type'} (h1 : term60 A B) : term60 A B.
Proof. exact (h1). Qed.
Lemma lem7190763 {A B : Type'} (f : A -> B) (h1 : term60 A B) : term61 A B f.
Proof. exact (@lem7190762 A B h1 f). Qed.
Lemma lem7190764 {A B : Type'} (f : A -> B) : (term61 A B f) = (term56 A B f).
Proof. exact (eq_refl (term61 A B f)). Qed.
Lemma lem7190765 {A B : Type'} (f : A -> B) (h1 : term60 A B) : term56 A B f.
Proof. exact (EQ_MP (@lem7190764 A B f) (@lem7190763 A B f h1)). Qed.
Lemma lem7190766 {A B : Type'} (f : A -> B) (g : A -> real) (h1 : term60 A B) : term62 A B f g.
Proof. exact (@lem7190765 A B f h1 g). Qed.
Lemma lem7190767 {A B : Type'} (f : A -> B) (g : A -> real) : (term62 A B f g) = (term52 A B f g).
Proof. exact (eq_refl (term62 A B f g)). Qed.
Lemma lem7190768 {A B : Type'} (f : A -> B) (g : A -> real) (h1 : term60 A B) : term52 A B f g.
Proof. exact (EQ_MP (@lem7190767 A B f g) (@lem7190766 A B f g h1)). Qed.
Lemma lem7190769 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : term60 A B) : term63 A B f g s.
Proof. exact (@lem7190768 A B f g h1 s). Qed.
Lemma lem7190770 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : (term63 A B f g s) = (term48 A B f s g).
Proof. exact (eq_refl (term63 A B f g s)). Qed.
Lemma lem7190771 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) (h1 : term60 A B) : term48 A B f s g.
Proof. exact (EQ_MP (@lem7190770 A B f s g) (@lem7190769 A B f g s h1)). Qed.
Lemma lem7190772 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7190773 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : term60 A B) (h2 : @FINITE A s) : (term45 A B s f g) = (@sum A s g).
Proof. exact (@lem7190771 A B f s g h1 (@lem7190772 A s h2)). Qed.
Lemma lem7190774 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term64 A B f s g.
Proof. exact (fun h0 : term60 A B => @lem7190773 A B f g s h0 h1). Qed.
Lemma lem7190775 {A B : Type'} (h1 : term60 A B) : term60 A B.
Proof. exact (h1). Qed.
Lemma lem7190776 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : term60 A B) (h2 : @FINITE A s) : (term45 A B s f g) = (@sum A s g).
Proof. exact (@lem7190774 A B f g s h2 (@lem7190775 A B h1)). Qed.
Lemma lem7190777 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) (h1 : term60 A B) : term48 A B f s g.
Proof. exact (fun h0 : @FINITE A s => @lem7190776 A B f g s h1 h0). Qed.
Lemma lem7190778 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term60 A B) : term65 A B f s.
Proof. exact (fun g : A -> real => @lem7190777 A B f s g h1). Qed.
Lemma lem7190779 {A B : Type'} (f : A -> B) (h1 : term60 A B) : term66 A B f.
Proof. exact (fun s : A -> Prop => @lem7190778 A B f s h1). Qed.
Lemma lem7190780 {A B : Type'} (h1 : term60 A B) : term67 A B.
Proof. exact (fun f : A -> B => @lem7190779 A B f h1). Qed.
Lemma lem7190781 {A B : Type'} : term68 A B.
Proof. exact (fun h0 : term60 A B => @lem7190780 A B h0). Qed.
Lemma lem7190782 {A B : Type'} : term67 A B.
Proof. exact (@lem7190781 A B (@lem7190761 A B)). Qed.
Lemma lem7190783 {A B : Type'} (f : A -> B) : term69 A B f.
Proof. exact (@lem7190782 A B f). Qed.
Lemma lem7190784 {A B : Type'} (f : A -> B) : (term69 A B f) = (term66 A B f).
Proof. exact (eq_refl (term69 A B f)). Qed.
Lemma lem7190785 {A B : Type'} (f : A -> B) : term66 A B f.
Proof. exact (EQ_MP (@lem7190784 A B f) (@lem7190783 A B f)). Qed.
Lemma lem7190786 {A B : Type'} (f : A -> B) (s : A -> Prop) : term70 A B f s.
Proof. exact (@lem7190785 A B f s). Qed.
Lemma lem7190787 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term70 A B f s) = (term65 A B f s).
Proof. exact (eq_refl (term70 A B f s)). Qed.
Lemma lem7190788 {A B : Type'} (f : A -> B) (s : A -> Prop) : term65 A B f s.
Proof. exact (EQ_MP (@lem7190787 A B f s) (@lem7190786 A B f s)). Qed.
Lemma lem7190789 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : term71 A B f s g.
Proof. exact (@lem7190788 A B f s g). Qed.
Lemma lem7190790 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : (term71 A B f s g) = (term48 A B f s g).
Proof. exact (eq_refl (term71 A B f s g)). Qed.
Lemma lem7190792 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem7190793 (x : real) (h1 : term72) : term73 x.
Proof. exact (@lem7190792 h1 x). Qed.
Lemma lem7190794 (x : real) : (term73 x) = (term74 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem7190795 (x : real) (h1 : term72) : term74 x.
Proof. exact (EQ_MP (@lem7190794 x) (@lem7190793 x h1)). Qed.
Lemma lem7190796 (x : real) (y : real) (h1 : term72) : term75 x y.
Proof. exact (@lem7190795 x h1 y). Qed.
Lemma lem7190797 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem7190798 (x : real) (y : real) (h1 : term72) : term76 x y.
Proof. exact (EQ_MP (@lem7190797 x y) (@lem7190796 x y h1)). Qed.
Lemma lem7190799 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem7190800 (x : real) (y : real) (h1 : term72) (h2 : x = y) : real_le x y.
Proof. exact (@lem7190798 x y h1 (@lem7190799 x y h2)). Qed.
Lemma lem7190801 (x : real) (y : real) (h1 : x = y) : term77 x y.
Proof. exact (fun h0 : term72 => @lem7190800 x y h0 h1). Qed.
Lemma lem7190802 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem7190803 (x : real) (y : real) (h1 : term72) (h2 : x = y) : real_le x y.
Proof. exact (@lem7190801 x y h2 (@lem7190802 h1)). Qed.
Lemma lem7190804 (x : real) (y : real) (h1 : term72) : term76 x y.
Proof. exact (fun h0 : x = y => @lem7190803 x y h1 h0). Qed.
Lemma lem7190805 (x : real) (h1 : term72) : term74 x.
Proof. exact (fun y : real => @lem7190804 x y h1). Qed.
Lemma lem7190806 (h1 : term72) : term72.
Proof. exact (fun x : real => @lem7190805 x h1). Qed.
Lemma lem7190807 : term78.
Proof. exact (fun h0 : term72 => @lem7190806 h0). Qed.
Lemma lem7190808 : term72.
Proof. exact (@lem7190807 (@lem1523745)). Qed.
Lemma lem7190809 (x : real) : term73 x.
Proof. exact (@lem7190808 x). Qed.
Lemma lem7190810 (x : real) : (term73 x) = (term74 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem7190811 (x : real) : term74 x.
Proof. exact (EQ_MP (@lem7190810 x) (@lem7190809 x)). Qed.
Lemma lem7190812 (x : real) (y : real) : term75 x y.
Proof. exact (@lem7190811 x y). Qed.
Lemma lem7190813 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem7190815 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190816 (x : real) (h1 : term11) : term12 x.
Proof. exact (@lem7190815 h1 x). Qed.
Lemma lem7190817 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem7190818 (x : real) (h1 : term11) : term13 x.
Proof. exact (EQ_MP (@lem7190817 x) (@lem7190816 x h1)). Qed.
Lemma lem7190819 (x : real) (y : real) (h1 : term11) : term14 x y.
Proof. exact (@lem7190818 x h1 y). Qed.
Lemma lem7190820 (y : real) (x : real) : (term14 x y) = (term15 y x).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem7190821 (y : real) (x : real) (h1 : term11) : term15 y x.
Proof. exact (EQ_MP (@lem7190820 y x) (@lem7190819 x y h1)). Qed.
Lemma lem7190822 (y : real) (x : real) (z : real) (h1 : term11) : term16 y x z.
Proof. exact (@lem7190821 y x h1 z). Qed.
Lemma lem7190823 (y : real) (x : real) (z : real) : (term16 y x z) = (term17 y x z).
Proof. exact (eq_refl (term16 y x z)). Qed.
Lemma lem7190824 (y : real) (x : real) (z : real) (h1 : term11) : term17 y x z.
Proof. exact (EQ_MP (@lem7190823 y x z) (@lem7190822 y x z h1)). Qed.
Lemma lem7190825 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term18 x y z.
Proof. exact (h1). Qed.
Lemma lem7190826 (x : real) (y : real) (z : real) (h1 : term11) (h2 : term18 x y z) : real_le x z.
Proof. exact (@lem7190824 y x z h1 (@lem7190825 x y z h2)). Qed.
Lemma lem7190827 (x : real) (y : real) (z : real) (h1 : term18 x y z) : term19 x z.
Proof. exact (fun h0 : term11 => @lem7190826 x y z h0 h1). Qed.
Lemma lem7190828 (x : real) (z : real) (h1 : term20 x z) : term20 x z.
Proof. exact (h1). Qed.
Lemma lem7190829 (x : real) (z : real) (h1 : term20 x z) : term19 x z.
Proof. exact (ex_elim (@lem7190828 x z h1) (fun y : real => fun h0 : term21 x z y => @lem7190827 x y z h0)). Qed.
Lemma lem7190830 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7190831 (x : real) (z : real) (h1 : term11) (h2 : term20 x z) : real_le x z.
Proof. exact (@lem7190829 x z h2 (@lem7190830 h1)). Qed.
Lemma lem7190832 (x : real) (z : real) (h1 : term11) : term22 x z.
Proof. exact (fun h0 : term20 x z => @lem7190831 x z h1 h0). Qed.
Lemma lem7190833 (x : real) (h1 : term11) : term23 x.
Proof. exact (fun z : real => @lem7190832 x z h1). Qed.
Lemma lem7190834 (h1 : term11) : term24.
Proof. exact (fun x : real => @lem7190833 x h1). Qed.
Lemma lem7190835 : term25.
Proof. exact (fun h0 : term11 => @lem7190834 h0). Qed.
Lemma lem7190836 : term24.
Proof. exact (@lem7190835 (@lem1339577)). Qed.
Lemma lem7190837 (x : real) : term26 x.
Proof. exact (@lem7190836 x). Qed.
Lemma lem7190838 (x : real) : (term26 x) = (term23 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem7190839 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem7190838 x) (@lem7190837 x)). Qed.
Lemma lem7190840 (x : real) (z : real) : term27 x z.
Proof. exact (@lem7190839 x z). Qed.
Lemma lem7190841 (x : real) (z : real) : (term27 x z) = (term22 x z).
Proof. exact (eq_refl (term27 x z)). Qed.
Lemma lem7190843 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term79 A B s t i f g) : term79 A B s t i f g.
Proof. exact (h1). Qed.
Lemma lem7190844 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term80 A B s t i f g) : term80 A B s t i f g.
Proof. exact (h1). Qed.
Lemma lem7190845 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7190846 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term81 A B s t i f g) : term81 A B s t i f g.
Proof. exact (h1). Qed.
Lemma lem7190847 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem7190848 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term82 A B s t i f g) : term82 A B s t i f g.
Proof. exact (h1). Qed.
Lemma lem7190849 {B : Type'} (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term83 B t g.
Proof. exact (h1). Qed.
Lemma lem7190851 (x : real) (z : real) : term22 x z.
Proof. exact (EQ_MP (@lem7190841 x z) (@lem7190840 x z)). Qed.
Lemma lem7190852 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : term84 A B s f t g.
Proof. exact (@lem7190851 (@sum A s f) (@sum B t g)). Qed.
Lemma lem7190854 (x : real) (y : real) : term76 x y.
Proof. exact (EQ_MP (@lem7190813 x y) (@lem7190812 x y)). Qed.
Lemma lem7190855 {A B : Type'} (i : B -> A) (t : B -> Prop) (g : B -> real) : term85 A B i t g.
Proof. exact (@lem7190854 (term86 A B t i g) (@sum B t g)). Qed.
Lemma lem7190857 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : term48 A B f s g.
Proof. exact (EQ_MP (@lem7190790 A B f s g) (@lem7190789 A B f s g)). Qed.
Lemma lem7190858 {A B : Type'} (f : B -> A) (s : B -> Prop) (g : B -> real) : term87 A B f s g.
Proof. exact (@lem7190857 B A f s g). Qed.
Lemma lem7190859 {A B : Type'} (i : B -> A) (t : B -> Prop) (g : B -> real) : term87 A B i t g.
Proof. exact (@lem7190858 A B i t g). Qed.
Lemma lem7190862 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7190875 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7190862 B t) (@lem7190847 B t h1)). Qed.
Lemma lem7190876 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7190875 B t h1)). Qed.
Lemma lem7190877 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7190876 B t h1) (@lem0)). Qed.
Lemma lem7190878 {A B : Type'} (i : B -> A) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term86 A B t i g) = (@sum B t g).
Proof. exact (@lem7190859 A B i t g (@lem7190877 B t h1)). Qed.
Lemma lem7190879 {A B : Type'} (i : B -> A) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : term88 A B i t g.
Proof. exact (@lem7190855 A B i t g (@lem7190878 A B i g t h1)). Qed.
Lemma lem7190881 (x : real) (z : real) : term22 x z.
Proof. exact (EQ_MP (@lem7190738 x z) (@lem7190737 x z)). Qed.
Lemma lem7190882 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) : term89 A B s f t i g.
Proof. exact (@lem7190881 (@sum A s f) (term86 A B t i g)). Qed.
Lemma lem7190884 {_132081 : Type'} (f : _132081 -> real) (s : _132081 -> Prop) (g : _132081 -> real) : term34 _132081 f s g.
Proof. exact (EQ_MP (@lem7190710 _132081 f s g) (@lem7190709 _132081 f s g)). Qed.
Lemma lem7190885 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term34 A f s g.
Proof. exact (@lem7190884 A f s g). Qed.
Lemma lem7190886 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : term90 A B f s t i g.
Proof. exact (@lem7190885 A f s (term91 A B t i g)). Qed.
Lemma lem7190887 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7190904 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7190887 A s) (@lem7190845 A s h1)). Qed.
Lemma lem7190905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7190906 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term92 A s) = (and True).
Proof. exact (MK_COMB (@lem7190905) (@lem7190904 A s h1)). Qed.
Lemma lem7190914 {A B : Type'} (f : A -> B) (y : A) : (term93 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7190915 {A : Type'} (f : A -> real) (y : A) : (term94 A f y) = (f y).
Proof. exact (@lem7190914 A real f y). Qed.
Lemma lem7190916 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term95 A B t i g x) = (term96 A B t i g x).
Proof. exact (@lem7190915 A (term91 A B t i g) x). Qed.
Lemma lem7190917 {A B : Type'} (t : B -> Prop) (i : B -> A) (y : A) (g : B -> real) : (term96 A B t i g y) = (term97 A B t i y g).
Proof. exact (eq_refl (term96 A B t i g y)). Qed.
Lemma lem7190918 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) : (term98 A B t i g) = (term91 A B t i g).
Proof. exact (fun_ext (fun y : A => @lem7190917 A B t i y g)). Qed.
Lemma lem7190919 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7190920 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term95 A B t i g x) = (term96 A B t i g x).
Proof. exact (MK_COMB (@lem7190918 A B t i g) (@lem7190919 A x)). Qed.
Lemma lem7190921 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7190922 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term99 A B t i g x) = (term100 A B t i g x).
Proof. exact (MK_COMB (@lem7190921) (@lem7190920 A B t i g x)). Qed.
Lemma lem7190923 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term96 A B t i g x) = (term97 A B t i x g).
Proof. exact (eq_refl (term96 A B t i g x)). Qed.
Lemma lem7190924 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : ((term95 A B t i g x) = (term96 A B t i g x)) = ((term96 A B t i g x) = (term97 A B t i x g)).
Proof. exact (MK_COMB (@lem7190922 A B t i g x) (@lem7190923 A B t i x g)). Qed.
Lemma lem7190925 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term96 A B t i g x) = (term97 A B t i x g).
Proof. exact (EQ_MP (@lem7190924 A B t i x g) (@lem7190916 A B t i g x)). Qed.
Lemma lem7190934 {A : Type'} (f : A -> real) (x : A) : (term101 A f x) = (term101 A f x).
Proof. exact (eq_refl (term101 A f x)). Qed.
Lemma lem7190935 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term102 A B f t i g x) = (term103 A B f t i x g).
Proof. exact (MK_COMB (@lem7190934 A f x) (@lem7190925 A B t i x g)). Qed.
Lemma lem7190936 {A : Type'} (x : A) (s : A -> Prop) : (term104 A x s) = (term104 A x s).
Proof. exact (eq_refl (term104 A x s)). Qed.
Lemma lem7190937 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term105 A B s f t i g x) = (term106 A B s f t i x g).
Proof. exact (MK_COMB (@lem7190936 A x s) (@lem7190935 A B f t i x g)). Qed.
Lemma lem7190940 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term107 A B s f t i g) = (term108 A B s f t i g).
Proof. exact (fun_ext (fun x : A => @lem7190937 A B s f t i x g)). Qed.
Lemma lem7190941 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7190942 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term109 A B s f t i g) = (term110 A B s f t i g).
Proof. exact (MK_COMB (@lem7190941 A) (@lem7190940 A B s f t i g)). Qed.
Lemma lem7190947 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term111 A B s f t i g) = (term112 A B s f t i g).
Proof. exact (MK_COMB (@lem7190906 A s h1) (@lem7190942 A B s f t i g)). Qed.
Lemma lem7190949 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7190950 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term112 A B s f t i g) = (term110 A B s f t i g).
Proof. exact (@lem7190949 (term110 A B s f t i g)). Qed.
Lemma lem7190965 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term111 A B s f t i g) = (term110 A B s f t i g).
Proof. exact (TRANS (@lem7190947 A B f t i g s h1) (@lem7190950 A B s f t i g)). Qed.
Lemma lem7190966 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term110 A B s f t i g) = (term111 A B s f t i g).
Proof. exact (SYM (@lem7190965 A B f t i g s h1)). Qed.
Lemma lem7190967 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7190968 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term82 A B s t i f g) : term113 A B s t i f g x.
Proof. exact (@lem7190848 A B s t i f g h1 x). Qed.
Lemma lem7190969 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term113 A B s t i f g x) = (term114 A B s t i f x g).
Proof. exact (eq_refl (term113 A B s t i f g x)). Qed.
Lemma lem7190970 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term82 A B s t i f g) : term114 A B s t i f x g.
Proof. exact (EQ_MP (@lem7190969 A B s t i f x g) (@lem7190968 A B x s t i f g h1)). Qed.
Lemma lem7190971 {A : Type'} (P : A -> Prop) : term115 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7190972 {A : Type'} (P : A -> Prop) : (term115 A P) = (term116 A P).
Proof. exact (eq_refl (term115 A P)). Qed.
Lemma lem7190973 {A : Type'} (P : A -> Prop) : term116 A P.
Proof. exact (EQ_MP (@lem7190972 A P) (@lem7190971 A P)). Qed.
Lemma lem7190974 {A : Type'} (P : A -> Prop) (Q : Prop) : term117 A P Q.
Proof. exact (@lem7190973 A P Q). Qed.
Lemma lem7190975 {A : Type'} (P : A -> Prop) (Q : Prop) : (term117 A P Q) = ((term118 A P Q) = (term119 A P Q)).
Proof. exact (eq_refl (term117 A P Q)). Qed.
Lemma lem7190986 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7190993 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7190986 A x s) (@lem7190967 A x s h1)). Qed.
Lemma lem7190994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7190995 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term104 A x s) = (imp True).
Proof. exact (MK_COMB (@lem7190994) (@lem7190993 A x s h1)). Qed.
Lemma lem7191006 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term120 A B t i f x g) = (term120 A B t i f x g).
Proof. exact (eq_refl (term120 A B t i f x g)). Qed.
Lemma lem7191007 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term114 A B s t i f x g) = (term121 A B t i f x g).
Proof. exact (MK_COMB (@lem7190995 A x s h1) (@lem7191006 A B t i f x g)). Qed.
Lemma lem7191009 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7191010 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term121 A B t i f x g) = (term120 A B t i f x g).
Proof. exact (@lem7191009 (term120 A B t i f x g)). Qed.
Lemma lem7191021 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term114 A B s t i f x g) = (term120 A B t i f x g).
Proof. exact (TRANS (@lem7191007 A B t i f g x s h1) (@lem7191010 A B t i f x g)). Qed.
Lemma lem7191022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7191023 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term122 A B s t i f x g) = (term123 A B t i f x g).
Proof. exact (MK_COMB (@lem7191022) (@lem7191021 A B t i f g x s h1)). Qed.
Lemma lem7191032 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term103 A B f t i x g) = (term103 A B f t i x g).
Proof. exact (eq_refl (term103 A B f t i x g)). Qed.
Lemma lem7191033 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term124 A B s f t i x g) = (term125 A B f t i x g).
Proof. exact (MK_COMB (@lem7191023 A B t i f g x s h1) (@lem7191032 A B f t i x g)). Qed.
Lemma lem7191035 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem7190975 A P Q) (@lem7190974 A P Q)). Qed.
Lemma lem7191036 {B : Type'} (P : B -> Prop) (Q : Prop) : (term118 B P Q) = (term119 B P Q).
Proof. exact (@lem7191035 B P Q). Qed.
Lemma lem7191037 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term126 A B f t i x g) = (term127 A B f t i x g).
Proof. exact (@lem7191036 B (term128 A B t i f x g) (term103 A B f t i x g)). Qed.
Lemma lem7191038 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term129 A B t i f x g y) = (term130 A B t i f x g y).
Proof. exact (eq_refl (term129 A B t i f x g y)). Qed.
Lemma lem7191039 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term131 A B t i f x g) = (term128 A B t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7191038 A B t i f x g y)). Qed.
Lemma lem7191040 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7191041 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term132 A B t i f x g) = (term120 A B t i f x g).
Proof. exact (MK_COMB (@lem7191040 B) (@lem7191039 A B t i f x g)). Qed.
Lemma lem7191042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7191043 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term133 A B t i f x g) = (term123 A B t i f x g).
Proof. exact (MK_COMB (@lem7191042) (@lem7191041 A B t i f x g)). Qed.
Lemma lem7191044 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term103 A B f t i x g) = (term103 A B f t i x g).
Proof. exact (eq_refl (term103 A B f t i x g)). Qed.
Lemma lem7191045 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term126 A B f t i x g) = (term125 A B f t i x g).
Proof. exact (MK_COMB (@lem7191043 A B t i f x g) (@lem7191044 A B f t i x g)). Qed.
Lemma lem7191046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7191047 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term134 A B f t i x g) = (term135 A B f t i x g).
Proof. exact (MK_COMB (@lem7191046) (@lem7191045 A B f t i x g)). Qed.
Lemma lem7191048 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term129 A B t i f x g y) = (term130 A B t i f x g y).
Proof. exact (eq_refl (term129 A B t i f x g y)). Qed.
Lemma lem7191049 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7191050 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term136 A B t i f x g y) = (term137 A B t i f x g y).
Proof. exact (MK_COMB (@lem7191049) (@lem7191048 A B t i f x g y)). Qed.
Lemma lem7191051 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term103 A B f t i x g) = (term103 A B f t i x g).
Proof. exact (eq_refl (term103 A B f t i x g)). Qed.
Lemma lem7191052 {A B : Type'} (y : B) (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term138 A B y f t i x g) = (term139 A B y f t i x g).
Proof. exact (MK_COMB (@lem7191050 A B t i f x g y) (@lem7191051 A B f t i x g)). Qed.
Lemma lem7191053 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term140 A B f t i x g) = (term141 A B f t i x g).
Proof. exact (fun_ext (fun y : B => @lem7191052 A B y f t i x g)). Qed.
Lemma lem7191054 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7191055 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term127 A B f t i x g) = (term142 A B f t i x g).
Proof. exact (MK_COMB (@lem7191054 B) (@lem7191053 A B f t i x g)). Qed.
Lemma lem7191056 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : ((term126 A B f t i x g) = (term127 A B f t i x g)) = ((term125 A B f t i x g) = (term142 A B f t i x g)).
Proof. exact (MK_COMB (@lem7191047 A B f t i x g) (@lem7191055 A B f t i x g)). Qed.
Lemma lem7191057 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term125 A B f t i x g) = (term142 A B f t i x g).
Proof. exact (EQ_MP (@lem7191056 A B f t i x g) (@lem7191037 A B f t i x g)). Qed.
Lemma lem7191078 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term124 A B s f t i x g) = (term142 A B f t i x g).
Proof. exact (TRANS (@lem7191033 A B f t i g x s h1) (@lem7191057 A B f t i x g)). Qed.
Lemma lem7191079 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term142 A B f t i x g) = (term124 A B s f t i x g).
Proof. exact (SYM (@lem7191078 A B f t i g x s h1)). Qed.
Lemma lem7191080 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term130 A B t i f x g y) : term130 A B t i f x g y.
Proof. exact (h1). Qed.
Lemma lem7191081 {A B : Type'} (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term143 A B i f x g y) : term143 A B i f x g y.
Proof. exact (h1). Qed.
Lemma lem7191082 {B : Type'} (y : B) (t : B -> Prop) (h1 : @IN B y t) : @IN B y t.
Proof. exact (h1). Qed.
Lemma lem7191083 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term144 A B f x g y) : term144 A B f x g y.
Proof. exact (h1). Qed.
Lemma lem7191084 {A B : Type'} (i : B -> A) (y : B) (x : A) (h1 : (i y) = x) : (i y) = x.
Proof. exact (h1). Qed.
Lemma lem7191086 (x : real) (z : real) : term22 x z.
Proof. exact (EQ_MP (@lem7190680 x z) (@lem7190679 x z)). Qed.
Lemma lem7191087 {A B : Type'} (f : A -> real) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term145 A B f t i x g.
Proof. exact (@lem7191086 (f x) (term97 A B t i x g)). Qed.
Lemma lem7191088 {_133036 : Type'} (f : _133036 -> real) : term146 _133036 f.
Proof. exact (@lem7123532 _133036 f). Qed.
Lemma lem7191089 {_133036 : Type'} (f : _133036 -> real) : (term146 _133036 f) = (term147 _133036 f).
Proof. exact (eq_refl (term146 _133036 f)). Qed.
Lemma lem7191090 {_133036 : Type'} (f : _133036 -> real) : term147 _133036 f.
Proof. exact (EQ_MP (@lem7191089 _133036 f) (@lem7191088 _133036 f)). Qed.
Lemma lem7191091 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term148 _133036 f x.
Proof. exact (@lem7191090 _133036 f x). Qed.
Lemma lem7191092 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term148 _133036 f x) = ((term149 _133036 x f) = (f x)).
Proof. exact (eq_refl (term148 _133036 f x)). Qed.
Lemma lem7191107 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term144 A B f x g y) = ((term144 A B f x g y) = True).
Proof. exact (@lem7 (term144 A B f x g y)). Qed.
Lemma lem7191110 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term149 _133036 x f) = (f x).
Proof. exact (EQ_MP (@lem7191092 _133036 f x) (@lem7191091 _133036 f x)). Qed.
Lemma lem7191111 {B : Type'} (f : B -> real) (x : B) : (term149 B x f) = (f x).
Proof. exact (@lem7191110 B f x). Qed.
Lemma lem7191112 {B : Type'} (g : B -> real) (y : B) : (term149 B y g) = (g y).
Proof. exact (@lem7191111 B g y). Qed.
Lemma lem7191113 {A : Type'} (f : A -> real) (x : A) : (term101 A f x) = (term101 A f x).
Proof. exact (eq_refl (term101 A f x)). Qed.
Lemma lem7191114 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term150 A B f x y g) = (term144 A B f x g y).
Proof. exact (MK_COMB (@lem7191113 A f x) (@lem7191112 B g y)). Qed.
Lemma lem7191116 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term144 A B f x g y) : (term144 A B f x g y) = True.
Proof. exact (EQ_MP (@lem7191107 A B f x g y) (@lem7191083 A B f x g y h1)). Qed.
Lemma lem7191117 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term144 A B f x g y) : (term150 A B f x y g) = True.
Proof. exact (TRANS (@lem7191114 A B f x g y) (@lem7191116 A B f x g y h1)). Qed.
Lemma lem7191118 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term144 A B f x g y) : True = (term150 A B f x y g).
Proof. exact (SYM (@lem7191117 A B f x g y h1)). Qed.
Lemma lem7191119 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term144 A B f x g y) : term150 A B f x y g.
Proof. exact (EQ_MP (@lem7191118 A B f x g y h1) (@lem0)). Qed.
Lemma lem7191121 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term6 A u v f.
Proof. exact (EQ_MP (@lem7190652 A u v f) (@lem7190651 A u v f)). Qed.
Lemma lem7191122 {B : Type'} (u : B -> Prop) (v : B -> Prop) (f : B -> real) : term6 B u v f.
Proof. exact (@lem7191121 B u v f). Qed.
Lemma lem7191123 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term151 A B y t i x g.
Proof. exact (@lem7191122 B (@INSERT B y (@EMPTY B)) (term152 A B t i x) g). Qed.
Lemma lem7191125 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term6 A u v f.
Proof. exact (EQ_MP (@lem7190652 A u v f) (@lem7190651 A u v f)). Qed.
Lemma lem7191126 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term6 A u v f.
Proof. exact (@lem7191125 A u v f). Qed.
Lemma lem7191127 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : term153 A B s t i g.
Proof. exact (@lem7191126 A s (@IMAGE B A i t) (term91 A B t i g)). Qed.
Lemma lem7191130 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term154 A B s t i g) = (term154 A B s t i g).
Proof. exact (eq_refl (term154 A B s t i g)). Qed.
Lemma lem7191131 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term154 A B s t i g) = (term153 A B s t i g).
Proof. exact (eq_refl (term154 A B s t i g)). Qed.
Lemma lem7191132 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term155 A B s t i g) = (term155 A B s t i g).
Proof. exact (eq_refl (term155 A B s t i g)). Qed.
Lemma lem7191133 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : ((term154 A B s t i g) = (term154 A B s t i g)) = ((term154 A B s t i g) = (term153 A B s t i g)).
Proof. exact (MK_COMB (@lem7191132 A B s t i g) (@lem7191131 A B s t i g)). Qed.
Lemma lem7191134 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term154 A B s t i g) = (term153 A B s t i g).
Proof. exact (eq_refl (term154 A B s t i g)). Qed.
Lemma lem7191135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7191136 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term155 A B s t i g) = (term156 A B s t i g).
Proof. exact (MK_COMB (@lem7191135) (@lem7191134 A B s t i g)). Qed.
Lemma lem7191137 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term153 A B s t i g) = (term153 A B s t i g).
Proof. exact (eq_refl (term153 A B s t i g)). Qed.
Lemma lem7191138 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : ((term154 A B s t i g) = (term153 A B s t i g)) = ((term153 A B s t i g) = (term153 A B s t i g)).
Proof. exact (MK_COMB (@lem7191136 A B s t i g) (@lem7191137 A B s t i g)). Qed.
Lemma lem7191139 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : ((term154 A B s t i g) = (term154 A B s t i g)) = ((term153 A B s t i g) = (term153 A B s t i g)).
Proof. exact (TRANS (@lem7191133 A B s t i g) (@lem7191138 A B s t i g)). Qed.
Lemma lem7191140 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term153 A B s t i g) = (term153 A B s t i g).
Proof. exact (EQ_MP (@lem7191139 A B s t i g) (@lem7191130 A B s t i g)). Qed.
Lemma lem7191141 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : term153 A B s t i g.
Proof. exact (EQ_MP (@lem7191140 A B s t i g) (@lem7191127 A B s t i g)). Qed.
Lemma lem7191256 {A B : Type'} (f : A -> B) : term157 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem7191257 {A B : Type'} (f : A -> B) : (term157 A B f) = (term158 A B f).
Proof. exact (eq_refl (term157 A B f)). Qed.
Lemma lem7191258 {A B : Type'} (f : A -> B) : term158 A B f.
Proof. exact (EQ_MP (@lem7191257 A B f) (@lem7191256 A B f)). Qed.
Lemma lem7191259 {A B : Type'} (f : A -> B) (s : A -> Prop) : term159 A B f s.
Proof. exact (@lem7191258 A B f s). Qed.
Lemma lem7191260 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term159 A B f s) = (term160 A B f s).
Proof. exact (eq_refl (term159 A B f s)). Qed.
Lemma lem7191261 {A B : Type'} (f : A -> B) (s : A -> Prop) : term160 A B f s.
Proof. exact (EQ_MP (@lem7191260 A B f s) (@lem7191259 A B f s)). Qed.
Lemma lem7191262 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7191263 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term161 A B f s.
Proof. exact (@lem7191261 A B f s (@lem7191262 A s h1)). Qed.
Lemma lem7191264 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term161 A B f s) = ((term161 A B f s) = True).
Proof. exact (@lem7 (term161 A B f s)). Qed.
Lemma lem7191265 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term161 A B f s) = True.
Proof. exact (EQ_MP (@lem7191264 A B f s) (@lem7191263 A B f s h1)). Qed.
Lemma lem7191273 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7191302 {A B : Type'} (f : A -> B) (s : A -> Prop) : term162 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem7191265 A B f s h0). Qed.
Lemma lem7191303 {A B : Type'} (f : B -> A) (s : B -> Prop) : term163 A B f s.
Proof. exact (@lem7191302 B A f s). Qed.
Lemma lem7191304 {A B : Type'} (i : B -> A) (t : B -> Prop) : term163 A B i t.
Proof. exact (@lem7191303 A B i t). Qed.
Lemma lem7191306 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7191273 B t) (@lem7190847 B t h1)). Qed.
Lemma lem7191307 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7191306 B t h1)). Qed.
Lemma lem7191308 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7191307 B t h1) (@lem0)). Qed.
Lemma lem7191309 {A B : Type'} (i : B -> A) (t : B -> Prop) (h1 : @FINITE B t) : (term164 A B i t) = True.
Proof. exact (@lem7191304 A B i t (@lem7191308 B t h1)). Qed.
Lemma lem7191310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7191311 {A B : Type'} (i : B -> A) (t : B -> Prop) (h1 : @FINITE B t) : (term165 A B i t) = (and True).
Proof. exact (MK_COMB (@lem7191310) (@lem7191309 A B i t h1)). Qed.
Lemma lem7191321 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7191322 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7191321 p q p' q'). Qed.
Lemma lem7191323 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7191322 p q p'). Qed.
Lemma lem7191324 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : term169 A B s t i g x.
Proof. exact (@lem7191323 (term170 A B x i t s) (term171 A B t i g x)). Qed.
Lemma lem7191325 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) : term172 A B s t i g x p'.
Proof. exact (@lem7191324 A B s t i g x p'). Qed.
Lemma lem7191326 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) : (term172 A B s t i g x p') = (term173 A B s t i g x p').
Proof. exact (eq_refl (term172 A B s t i g x p')). Qed.
Lemma lem7191327 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) : term173 A B s t i g x p'.
Proof. exact (EQ_MP (@lem7191326 A B s t i g x p') (@lem7191325 A B s t i g x p')). Qed.
Lemma lem7191328 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) (q' : Prop) : term174 A B s t i g x p' q'.
Proof. exact (@lem7191327 A B s t i g x p' q'). Qed.
Lemma lem7191329 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) (q' : Prop) : (term174 A B s t i g x p' q') = (term175 A B s t i g x p' q').
Proof. exact (eq_refl (term174 A B s t i g x p' q')). Qed.
Lemma lem7191330 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) (p' : Prop) (q' : Prop) : term175 A B s t i g x p' q'.
Proof. exact (EQ_MP (@lem7191329 A B s t i g x p' q') (@lem7191328 A B s t i g x p' q')). Qed.
Lemma lem7191331 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) : (term170 A B x i t s) = (term170 A B x i t s).
Proof. exact (eq_refl (term170 A B x i t s)). Qed.
Lemma lem7191332 {A B : Type'} (g : B -> real) (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) (q' : Prop) : term176 A B g x i t s q'.
Proof. exact (@lem7191330 A B s t i g x (term170 A B x i t s) q'). Qed.
Lemma lem7191333 {A B : Type'} (g : B -> real) (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) (q' : Prop) : term177 A B g x i t s q'.
Proof. exact (@lem7191332 A B g x i t s q' (@lem7191331 A B x i t s)). Qed.
Lemma lem7191338 {A B : Type'} (f : A -> B) (y : A) : (term93 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7191339 {A : Type'} (f : A -> real) (y : A) : (term94 A f y) = (f y).
Proof. exact (@lem7191338 A real f y). Qed.
Lemma lem7191340 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term95 A B t i g x) = (term96 A B t i g x).
Proof. exact (@lem7191339 A (term91 A B t i g) x). Qed.
Lemma lem7191341 {A B : Type'} (t : B -> Prop) (i : B -> A) (y : A) (g : B -> real) : (term96 A B t i g y) = (term97 A B t i y g).
Proof. exact (eq_refl (term96 A B t i g y)). Qed.
Lemma lem7191342 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) : (term98 A B t i g) = (term91 A B t i g).
Proof. exact (fun_ext (fun y : A => @lem7191341 A B t i y g)). Qed.
Lemma lem7191343 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7191344 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term95 A B t i g x) = (term96 A B t i g x).
Proof. exact (MK_COMB (@lem7191342 A B t i g) (@lem7191343 A x)). Qed.
Lemma lem7191345 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7191346 {A B : Type'} (t : B -> Prop) (i : B -> A) (g : B -> real) (x : A) : (term99 A B t i g x) = (term100 A B t i g x).
Proof. exact (MK_COMB (@lem7191345) (@lem7191344 A B t i g x)). Qed.
Lemma lem7191347 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term96 A B t i g x) = (term97 A B t i x g).
Proof. exact (eq_refl (term96 A B t i g x)). Qed.
Lemma lem7191348 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : ((term95 A B t i g x) = (term96 A B t i g x)) = ((term96 A B t i g x) = (term97 A B t i x g)).
Proof. exact (MK_COMB (@lem7191346 A B t i g x) (@lem7191347 A B t i x g)). Qed.
Lemma lem7191349 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term96 A B t i g x) = (term97 A B t i x g).
Proof. exact (EQ_MP (@lem7191348 A B t i x g) (@lem7191340 A B t i g x)). Qed.
Lemma lem7191358 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem7191359 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term171 A B t i g x) = (term179 A B t i x g).
Proof. exact (MK_COMB (@lem7191358) (@lem7191349 A B t i x g)). Qed.
Lemma lem7191368 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term180 A B s t i x g.
Proof. exact (fun h0 : term170 A B x i t s => @lem7191359 A B t i x g). Qed.
Lemma lem7191369 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term181 A B s t i x g.
Proof. exact (@lem7191333 A B g x i t s (term179 A B t i x g)). Qed.
Lemma lem7191370 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : (term182 A B s t i g x) = (term183 A B s t i x g).
Proof. exact (@lem7191369 A B s t i x g (@lem7191368 A B s t i x g)). Qed.
Lemma lem7191410 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term184 A B s t i g) = (term185 A B s t i g).
Proof. exact (fun_ext (fun x : A => @lem7191370 A B s t i x g)). Qed.
Lemma lem7191450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7191451 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term186 A B s t i g) = (term187 A B s t i g).
Proof. exact (MK_COMB (@lem7191450 A) (@lem7191410 A B s t i g)). Qed.
Lemma lem7191495 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term188 A B s i t) = (term188 A B s i t).
Proof. exact (eq_refl (term188 A B s i t)). Qed.
Lemma lem7191496 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term189 A B s t i g) = (term190 A B s t i g).
Proof. exact (MK_COMB (@lem7191495 A B s i t) (@lem7191451 A B s t i g)). Qed.
Lemma lem7191542 {A B : Type'} (s : A -> Prop) (i : B -> A) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term191 A B s t i g) = (term192 A B s t i g).
Proof. exact (MK_COMB (@lem7191311 A B i t h1) (@lem7191496 A B s t i g)). Qed.
Lemma lem7191544 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7191545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (g : B -> real) : (term192 A B s t i g) = (term190 A B s t i g).
Proof. exact (@lem7191544 (term190 A B s t i g)). Qed.
Lemma lem7191591 {A B : Type'} (s : A -> Prop) (i : B -> A) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term191 A B s t i g) = (term190 A B s t i g).
Proof. exact (TRANS (@lem7191542 A B s i g t h1) (@lem7191545 A B s t i g)). Qed.
Lemma lem7191592 {A B : Type'} (s : A -> Prop) (i : B -> A) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term190 A B s t i g) = (term191 A B s t i g).
Proof. exact (SYM (@lem7191591 A B s i g t h1)). Qed.
Lemma lem7191631 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem7191632 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem7191633 {A : Type'} (s : A -> Prop) : term194 A s.
Proof. exact (EQ_MP (@lem7191632 A s) (@lem7191631 A s)). Qed.
Lemma lem7191634 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term195 A s P.
Proof. exact (@lem7191633 A s P). Qed.
Lemma lem7191635 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term195 A s P) = (term196 A s P).
Proof. exact (eq_refl (term195 A s P)). Qed.
Lemma lem7191636 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term196 A s P.
Proof. exact (EQ_MP (@lem7191635 A s P) (@lem7191634 A s P)). Qed.
Lemma lem7191637 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7191638 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term197 A s P.
Proof. exact (@lem7191636 A s P (@lem7191637 A s h1)). Qed.
Lemma lem7191639 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term197 A s P) = ((term197 A s P) = True).
Proof. exact (@lem7 (term197 A s P)). Qed.
Lemma lem7191640 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term197 A s P) = True.
Proof. exact (EQ_MP (@lem7191639 A s P) (@lem7191638 A P s h1)). Qed.
Lemma lem7191660 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7191683 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term198 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem7191640 A P s h0). Qed.
Lemma lem7191684 {B : Type'} (s : B -> Prop) (P : B -> Prop) : term198 B s P.
Proof. exact (@lem7191683 B s P). Qed.
Lemma lem7191685 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : term199 A B t i x.
Proof. exact (@lem7191684 B t (term200 A B i x)). Qed.
Lemma lem7191686 {A B : Type'} (i : B -> A) (x : B) (x' : A) : (term201 A B i x' x) = ((i x) = x').
Proof. exact (eq_refl (term201 A B i x' x)). Qed.
Lemma lem7191687 {B : Type'} (x : B) (t : B -> Prop) : (term202 B x t) = (term202 B x t).
Proof. exact (eq_refl (term202 B x t)). Qed.
Lemma lem7191688 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term203 A B t i x' x) = (term204 A B t i x x').
Proof. exact (MK_COMB (@lem7191687 B x t) (@lem7191686 A B i x x')). Qed.
Lemma lem7191689 {B : Type'} (GEN_PVAR_331 : B) : (@SETSPEC B GEN_PVAR_331) = (@SETSPEC B GEN_PVAR_331).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_331)). Qed.
Lemma lem7191690 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term205 A B GEN_PVAR_331 t i x' x) = (term206 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7191689 B GEN_PVAR_331) (@lem7191688 A B t i x x')). Qed.
Lemma lem7191691 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7191692 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term207 A B GEN_PVAR_331 t i x x') = (term208 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7191690 A B GEN_PVAR_331 t i x' x) (@lem7191691 B x')). Qed.
Lemma lem7191693 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term209 A B GEN_PVAR_331 t i x) = (term210 A B GEN_PVAR_331 t i x).
Proof. exact (fun_ext (fun x' : B => @lem7191692 A B GEN_PVAR_331 t i x x')). Qed.
Lemma lem7191694 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7191695 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term211 A B GEN_PVAR_331 t i x) = (term212 A B GEN_PVAR_331 t i x).
Proof. exact (MK_COMB (@lem7191694 B) (@lem7191693 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7191696 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term213 A B t i x) = (term214 A B t i x).
Proof. exact (fun_ext (fun GEN_PVAR_331 : B => @lem7191695 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7191697 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem7191698 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term215 A B t i x) = (term152 A B t i x).
Proof. exact (MK_COMB (@lem7191697 B) (@lem7191696 A B t i x)). Qed.
Lemma lem7191699 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem7191700 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term216 A B t i x) = (term217 A B t i x).
Proof. exact (MK_COMB (@lem7191699 B) (@lem7191698 A B t i x)). Qed.
Lemma lem7191701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7191702 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term218 A B t i x) = (term219 A B t i x).
Proof. exact (MK_COMB (@lem7191701) (@lem7191700 A B t i x)). Qed.
Lemma lem7191703 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7191704 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : ((term216 A B t i x) = True) = ((term217 A B t i x) = True).
Proof. exact (MK_COMB (@lem7191702 A B t i x) (@lem7191703)). Qed.
Lemma lem7191705 {B : Type'} (t : B -> Prop) : (term46 B t) = (term46 B t).
Proof. exact (eq_refl (term46 B t)). Qed.
Lemma lem7191706 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term199 A B t i x) = (term220 A B t i x).
Proof. exact (MK_COMB (@lem7191705 B t) (@lem7191704 A B t i x)). Qed.
Lemma lem7191707 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : term220 A B t i x.
Proof. exact (EQ_MP (@lem7191706 A B t i x) (@lem7191685 A B t i x)). Qed.
Lemma lem7191709 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7191660 B t) (@lem7190847 B t h1)). Qed.
Lemma lem7191710 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7191709 B t h1)). Qed.
Lemma lem7191711 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7191710 B t h1) (@lem0)). Qed.
Lemma lem7191712 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term217 A B t i x) = True.
Proof. exact (@lem7191707 A B t i x (@lem7191711 B t h1)). Qed.
Lemma lem7191713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7191714 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term221 A B t i x) = (and True).
Proof. exact (MK_COMB (@lem7191713) (@lem7191712 A B i x t h1)). Qed.
Lemma lem7191780 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term222 A B t i x y g) = (term222 A B t i x y g).
Proof. exact (eq_refl (term222 A B t i x y g)). Qed.
Lemma lem7191781 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term223 A B t i x y g) = (term224 A B t i x y g).
Proof. exact (MK_COMB (@lem7191714 A B i x t h1) (@lem7191780 A B t i x y g)). Qed.
Lemma lem7191783 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7191784 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term224 A B t i x y g) = (term222 A B t i x y g).
Proof. exact (@lem7191783 (term222 A B t i x y g)). Qed.
Lemma lem7191850 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term223 A B t i x y g) = (term222 A B t i x y g).
Proof. exact (TRANS (@lem7191781 A B i x y g t h1) (@lem7191784 A B t i x y g)). Qed.
Lemma lem7191851 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) (t : B -> Prop) (h1 : @FINITE B t) : (term222 A B t i x y g) = (term223 A B t i x y g).
Proof. exact (SYM (@lem7191850 A B i x y g t h1)). Qed.
Lemma lem7191876 {_83095 : Type'} : term225 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7191877 {_83095 : Type'} (p : _83095 -> Prop) : term226 _83095 p.
Proof. exact (@lem7191876 _83095 p). Qed.
Lemma lem7191878 {_83095 : Type'} (p : _83095 -> Prop) : (term226 _83095 p) = (term227 _83095 p).
Proof. exact (eq_refl (term226 _83095 p)). Qed.
Lemma lem7191879 {_83095 : Type'} (p : _83095 -> Prop) : term227 _83095 p.
Proof. exact (EQ_MP (@lem7191878 _83095 p) (@lem7191877 _83095 p)). Qed.
Lemma lem7191880 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term228 _83095 p x.
Proof. exact (@lem7191879 _83095 p x). Qed.
Lemma lem7191881 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term228 _83095 p x) = ((term229 _83095 x p) = (p x)).
Proof. exact (eq_refl (term228 _83095 p x)). Qed.
Lemma lem7191905 {A : Type'} (f : A -> real) (s : A -> Prop) : term230 A f s.
Proof. exact (@lem7085797 A f s). Qed.
Lemma lem7191906 {A : Type'} (s : A -> Prop) (f : A -> real) : (term230 A f s) = (term231 A s f).
Proof. exact (eq_refl (term230 A f s)). Qed.
Lemma lem7191907 {A : Type'} (s : A -> Prop) (f : A -> real) : term231 A s f.
Proof. exact (EQ_MP (@lem7191906 A s f) (@lem7191905 A f s)). Qed.
Lemma lem7191908 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term83 A s f) : term83 A s f.
Proof. exact (h1). Qed.
Lemma lem7191909 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term83 A s f) : term232 A s f.
Proof. exact (@lem7191907 A s f (@lem7191908 A s f h1)). Qed.
Lemma lem7191910 {A : Type'} (s : A -> Prop) (f : A -> real) : (term232 A s f) = ((term232 A s f) = True).
Proof. exact (@lem7 (term232 A s f)). Qed.
Lemma lem7191911 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term83 A s f) : (term232 A s f) = True.
Proof. exact (EQ_MP (@lem7191910 A s f) (@lem7191909 A s f h1)). Qed.
Lemma lem7191921 {B : Type'} (y : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term233 B t g y.
Proof. exact (@lem7190849 B t g h1 y). Qed.
Lemma lem7191922 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term233 B t g y) = (term234 B t g y).
Proof. exact (eq_refl (term233 B t g y)). Qed.
Lemma lem7191923 {B : Type'} (y : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term234 B t g y.
Proof. exact (EQ_MP (@lem7191922 B t g y) (@lem7191921 B y t g h1)). Qed.
Lemma lem7191924 {B : Type'} (y : B) (t : B -> Prop) (h1 : @IN B y t) : @IN B y t.
Proof. exact (h1). Qed.
Lemma lem7191925 {B : Type'} (g : B -> real) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @IN B y t) : term235 B g y.
Proof. exact (@lem7191923 B y t g h1 (@lem7191924 B y t h2)). Qed.
Lemma lem7191926 {B : Type'} (g : B -> real) (y : B) : (term235 B g y) = ((term235 B g y) = True).
Proof. exact (@lem7 (term235 B g y)). Qed.
Lemma lem7191927 {B : Type'} (g : B -> real) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @IN B y t) : (term235 B g y) = True.
Proof. exact (EQ_MP (@lem7191926 B g y) (@lem7191925 B g y t h1 h2)). Qed.
Lemma lem7191954 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7191955 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7191954 p q p' q'). Qed.
Lemma lem7191956 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7191955 p q p'). Qed.
Lemma lem7191957 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term236 A B s t i x g.
Proof. exact (@lem7191956 (term170 A B x i t s) (term179 A B t i x g)). Qed.
Lemma lem7191958 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) : term237 A B s t i x g p'.
Proof. exact (@lem7191957 A B s t i x g p'). Qed.
Lemma lem7191959 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) : (term237 A B s t i x g p') = (term238 A B s t i x g p').
Proof. exact (eq_refl (term237 A B s t i x g p')). Qed.
Lemma lem7191960 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) : term238 A B s t i x g p'.
Proof. exact (EQ_MP (@lem7191959 A B s t i x g p') (@lem7191958 A B s t i x g p')). Qed.
Lemma lem7191961 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) (q' : Prop) : term239 A B s t i x g p' q'.
Proof. exact (@lem7191960 A B s t i x g p' q'). Qed.
Lemma lem7191962 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) (q' : Prop) : (term239 A B s t i x g p' q') = (term240 A B s t i x g p' q').
Proof. exact (eq_refl (term239 A B s t i x g p' q')). Qed.
Lemma lem7191963 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (p' : Prop) (q' : Prop) : term240 A B s t i x g p' q'.
Proof. exact (EQ_MP (@lem7191962 A B s t i x g p' q') (@lem7191961 A B s t i x g p' q')). Qed.
Lemma lem7191964 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) : (term170 A B x i t s) = (term170 A B x i t s).
Proof. exact (eq_refl (term170 A B x i t s)). Qed.
Lemma lem7191965 {A B : Type'} (g : B -> real) (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) (q' : Prop) : term241 A B g x i t s q'.
Proof. exact (@lem7191963 A B s t i x g (term170 A B x i t s) q'). Qed.
Lemma lem7191966 {A B : Type'} (g : B -> real) (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) (q' : Prop) : term242 A B g x i t s q'.
Proof. exact (@lem7191965 A B g x i t s q' (@lem7191964 A B x i t s)). Qed.
Lemma lem7191971 {A : Type'} (s : A -> Prop) (f : A -> real) : term243 A s f.
Proof. exact (fun h0 : term83 A s f => @lem7191911 A s f h0). Qed.
Lemma lem7191972 {B : Type'} (s : B -> Prop) (f : B -> real) : term243 B s f.
Proof. exact (@lem7191971 B s f). Qed.
Lemma lem7191973 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) : term244 A B t i x g.
Proof. exact (@lem7191972 B (term152 A B t i x) g). Qed.
Lemma lem7191981 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7191982 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7191981 p q p' q'). Qed.
Lemma lem7191983 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7191982 p q p'). Qed.
Lemma lem7191984 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) : term245 A B t i x g x'.
Proof. exact (@lem7191983 (term246 A B x' t i x) (term235 B g x')). Qed.
Lemma lem7191985 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) : term247 A B t i x g x' p'.
Proof. exact (@lem7191984 A B t i x g x' p'). Qed.
Lemma lem7191986 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) : (term247 A B t i x g x' p') = (term248 A B t i x g x' p').
Proof. exact (eq_refl (term247 A B t i x g x' p')). Qed.
Lemma lem7191987 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) : term248 A B t i x g x' p'.
Proof. exact (EQ_MP (@lem7191986 A B t i x g x' p') (@lem7191985 A B t i x g x' p')). Qed.
Lemma lem7191988 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) (q' : Prop) : term249 A B t i x g x' p' q'.
Proof. exact (@lem7191987 A B t i x g x' p' q'). Qed.
Lemma lem7191989 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) (q' : Prop) : (term249 A B t i x g x' p' q') = (term250 A B t i x g x' p' q').
Proof. exact (eq_refl (term249 A B t i x g x' p' q')). Qed.
Lemma lem7191990 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (g : B -> real) (x' : B) (p' : Prop) (q' : Prop) : term250 A B t i x g x' p' q'.
Proof. exact (EQ_MP (@lem7191989 A B t i x g x' p' q') (@lem7191988 A B t i x g x' p' q')). Qed.
Lemma lem7191992 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term229 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7191881 _83095 p x) (@lem7191880 _83095 p x)). Qed.
Lemma lem7191993 {B : Type'} (p : B -> Prop) (x : B) : (term229 B x p) = (p x).
Proof. exact (@lem7191992 B p x). Qed.
Lemma lem7191994 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term251 A B x' t i x) = (term252 A B t i x x').
Proof. exact (@lem7191993 B (term253 A B t i x) x'). Qed.
Lemma lem7191995 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7191996 {B : Type'} (GEN_PVAR_331 : B) : (@SETSPEC B GEN_PVAR_331) = (@SETSPEC B GEN_PVAR_331).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_331)). Qed.
Lemma lem7191997 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term254 A B GEN_PVAR_331 t i x' x) = (term206 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7191996 B GEN_PVAR_331) (@lem7191995 A B t i x x')). Qed.
Lemma lem7191998 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7191999 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term255 A B GEN_PVAR_331 t i x x') = (term208 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7191997 A B GEN_PVAR_331 t i x' x) (@lem7191998 B x')). Qed.
Lemma lem7192000 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term256 A B GEN_PVAR_331 t i x) = (term210 A B GEN_PVAR_331 t i x).
Proof. exact (fun_ext (fun x' : B => @lem7191999 A B GEN_PVAR_331 t i x x')). Qed.
Lemma lem7192001 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192002 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term257 A B GEN_PVAR_331 t i x) = (term212 A B GEN_PVAR_331 t i x).
Proof. exact (MK_COMB (@lem7192001 B) (@lem7192000 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192003 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term258 A B t i x) = (term214 A B t i x).
Proof. exact (fun_ext (fun GEN_PVAR_331 : B => @lem7192002 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192004 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem7192005 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term259 A B t i x) = (term152 A B t i x).
Proof. exact (MK_COMB (@lem7192004 B) (@lem7192003 A B t i x)). Qed.
Lemma lem7192006 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem7192007 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term251 A B x t i x') = (term246 A B x t i x').
Proof. exact (MK_COMB (@lem7192006 B x) (@lem7192005 A B t i x')). Qed.
Lemma lem7192008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7192009 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term260 A B x t i x') = (term261 A B x t i x').
Proof. exact (MK_COMB (@lem7192008) (@lem7192007 A B x t i x')). Qed.
Lemma lem7192010 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7192011 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : ((term251 A B x t i x') = (term252 A B t i x' x)) = ((term246 A B x t i x') = (term204 A B t i x x')).
Proof. exact (MK_COMB (@lem7192009 A B x t i x') (@lem7192010 A B t i x x')). Qed.
Lemma lem7192012 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term246 A B x t i x') = (term204 A B t i x x').
Proof. exact (EQ_MP (@lem7192011 A B t i x x') (@lem7191994 A B t i x' x)). Qed.
Lemma lem7192017 {A B : Type'} (g : B -> real) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (q' : Prop) : term262 A B g t i x x' q'.
Proof. exact (@lem7191990 A B t i x' g x (term204 A B t i x x') q'). Qed.
Lemma lem7192018 {A B : Type'} (g : B -> real) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (q' : Prop) : term263 A B g t i x x' q'.
Proof. exact (@lem7192017 A B g t i x x' q' (@lem7192012 A B t i x x')). Qed.
Lemma lem7192019 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term204 A B t i x x') : term204 A B t i x x'.
Proof. exact (h1). Qed.
Lemma lem7192021 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term204 A B t i x x') : @IN B x t.
Proof. exact (proj1 (@lem7192019 A B t i x x' h1)). Qed.
Lemma lem7192022 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = ((@IN B x t) = True).
Proof. exact (@lem7 (@IN B x t)). Qed.
Lemma lem7192025 {B : Type'} (y : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term264 B t g y.
Proof. exact (fun h0 : @IN B y t => @lem7191927 B g y t h1 h0). Qed.
Lemma lem7192026 {B : Type'} (y : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term264 B t g y.
Proof. exact (@lem7192025 B y t g h1). Qed.
Lemma lem7192027 {B : Type'} (x : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term264 B t g x.
Proof. exact (@lem7192026 B x t g h1). Qed.
Lemma lem7192029 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term204 A B t i x x') : (@IN B x t) = True.
Proof. exact (EQ_MP (@lem7192022 B x t) (@lem7192021 A B t i x x' h1)). Qed.
Lemma lem7192030 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term204 A B t i x x') : True = (@IN B x t).
Proof. exact (SYM (@lem7192029 A B t i x x' h1)). Qed.
Lemma lem7192031 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term204 A B t i x x') : @IN B x t.
Proof. exact (EQ_MP (@lem7192030 A B t i x x' h1) (@lem0)). Qed.
Lemma lem7192032 {A B : Type'} (g : B -> real) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) (h1 : term83 B t g) (h2 : term204 A B t i x x') : (term235 B g x) = True.
Proof. exact (@lem7192027 B x t g h1 (@lem7192031 A B t i x x' h2)). Qed.
Lemma lem7192033 {A B : Type'} (i : B -> A) (x : A) (x' : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term265 A B t i x g x'.
Proof. exact (fun h0 : term204 A B t i x' x => @lem7192032 A B g t i x' x h1 h0). Qed.
Lemma lem7192034 {A B : Type'} (g : B -> real) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : term266 A B g t i x x'.
Proof. exact (@lem7192018 A B g t i x x' True). Qed.
Lemma lem7192035 {A B : Type'} (i : B -> A) (x : B) (x' : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term267 A B t i x' g x) = (term268 A B t i x x').
Proof. exact (@lem7192034 A B g t i x x' (@lem7192033 A B i x' x t g h1)). Qed.
Lemma lem7192037 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7192038 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term268 A B t i x x') = True.
Proof. exact (@lem7192037 (term204 A B t i x x')). Qed.
Lemma lem7192039 {A B : Type'} (i : B -> A) (x : A) (x' : B) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term267 A B t i x g x') = True.
Proof. exact (TRANS (@lem7192035 A B i x' x t g h1) (@lem7192038 A B t i x' x)). Qed.
Lemma lem7192040 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term269 A B t i x g) = (term270 B).
Proof. exact (fun_ext (fun x' : B => @lem7192039 A B i x x' t g h1)). Qed.
Lemma lem7192041 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192042 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term271 A B t i x g) = (term272 B).
Proof. exact (MK_COMB (@lem7192041 B) (@lem7192040 A B i x t g h1)). Qed.
Lemma lem7192044 {A : Type'} (t : Prop) : (term273 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7192045 {B : Type'} (t : Prop) : (term273 B t) = t.
Proof. exact (@lem7192044 B t). Qed.
Lemma lem7192046 {B : Type'} : (term272 B) = True.
Proof. exact (@lem7192045 B True). Qed.
Lemma lem7192047 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term271 A B t i x g) = True.
Proof. exact (TRANS (@lem7192042 A B i x t g h1) (@lem7192046 B)). Qed.
Lemma lem7192048 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : True = (term271 A B t i x g).
Proof. exact (SYM (@lem7192047 A B i x t g h1)). Qed.
Lemma lem7192049 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term271 A B t i x g.
Proof. exact (EQ_MP (@lem7192048 A B i x t g h1) (@lem0)). Qed.
Lemma lem7192050 {A B : Type'} (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term179 A B t i x g) = True.
Proof. exact (@lem7191973 A B t i x g (@lem7192049 A B i x t g h1)). Qed.
Lemma lem7192051 {A B : Type'} (s : A -> Prop) (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : term274 A B s t i x g.
Proof. exact (fun h0 : term170 A B x i t s => @lem7192050 A B i x t g h1). Qed.
Lemma lem7192052 {A B : Type'} (g : B -> real) (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) : term275 A B g x i t s.
Proof. exact (@lem7191966 A B g x i t s True). Qed.
Lemma lem7192053 {A B : Type'} (x : A) (i : B -> A) (s : A -> Prop) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term183 A B s t i x g) = (term276 A B x i t s).
Proof. exact (@lem7192052 A B g x i t s (@lem7192051 A B s i x t g h1)). Qed.
Lemma lem7192055 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7192056 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (s : A -> Prop) : (term276 A B x i t s) = True.
Proof. exact (@lem7192055 (term170 A B x i t s)). Qed.
Lemma lem7192057 {A B : Type'} (s : A -> Prop) (i : B -> A) (x : A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term183 A B s t i x g) = True.
Proof. exact (TRANS (@lem7192053 A B x i s t g h1) (@lem7192056 A B x i t s)). Qed.
Lemma lem7192058 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term185 A B s t i g) = (term270 A).
Proof. exact (fun_ext (fun x : A => @lem7192057 A B s i x t g h1)). Qed.
Lemma lem7192059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7192060 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term187 A B s t i g) = (term272 A).
Proof. exact (MK_COMB (@lem7192059 A) (@lem7192058 A B s i t g h1)). Qed.
Lemma lem7192062 {A : Type'} (t : Prop) : (term273 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7192063 {A : Type'} (t : Prop) : (term273 A t) = t.
Proof. exact (@lem7192062 A t). Qed.
Lemma lem7192064 {A : Type'} : (term272 A) = True.
Proof. exact (@lem7192063 A True). Qed.
Lemma lem7192065 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term187 A B s t i g) = True.
Proof. exact (TRANS (@lem7192060 A B s i t g h1) (@lem7192064 A)). Qed.
Lemma lem7192066 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term188 A B s i t) = (term188 A B s i t).
Proof. exact (eq_refl (term188 A B s i t)). Qed.
Lemma lem7192067 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term190 A B s t i g) = (term277 A B s i t).
Proof. exact (MK_COMB (@lem7192066 A B s i t) (@lem7192065 A B s i t g h1)). Qed.
Lemma lem7192069 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7192070 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term277 A B s i t) = (term278 A B s i t).
Proof. exact (@lem7192069 (term278 A B s i t)). Qed.
Lemma lem7192071 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term190 A B s t i g) = (term278 A B s i t).
Proof. exact (TRANS (@lem7192067 A B s i t g h1) (@lem7192070 A B s i t)). Qed.
Lemma lem7192072 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) (h1 : term83 B t g) : (term278 A B s i t) = (term190 A B s t i g).
Proof. exact (SYM (@lem7192071 A B s i t g h1)). Qed.
Lemma lem7192083 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term279 A B t s.
Proof. exact (conj (@lem7190847 B t h2) (@lem7190845 A s h1)). Qed.
Lemma lem7192084 {A B : Type'} (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) : term280 A B g t s.
Proof. exact (conj (@lem7190849 B t g h1) (@lem7192083 A B s t h2 h3)). Qed.
Lemma lem7192085 {A B : Type'} (g : B -> real) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : @IN A x s) : term281 A B x g t s.
Proof. exact (conj (@lem7190967 A x s h4) (@lem7192084 A B g s t h1 h2 h3)). Qed.
Lemma lem7192086 {A B : Type'} (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : @IN A x s) (h5 : @IN B y t) : term282 A B y x g t s.
Proof. exact (conj (@lem7191082 B y t h5) (@lem7192085 A B g t x s h1 h2 h3 h4)). Qed.
Lemma lem7192087 {A B : Type'} (g : B -> real) (i : B -> A) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) : term283 A B i y x g t s.
Proof. exact (conj (@lem7191084 A B i y x h4) (@lem7192086 A B g x s y t h1 h2 h3 h5 h6)). Qed.
Lemma lem7192088 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term284 A B f i y x g t s.
Proof. exact (conj (@lem7191083 A B f x g y h7) (@lem7192087 A B g i x s y t h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem7192116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term285 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem7192117 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term285 B s t).
Proof. exact (@lem7192116 B s t). Qed.
Lemma lem7192118 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term286 A B y t i x) = (term287 A B y t i x).
Proof. exact (@lem7192117 B (@INSERT B y (@EMPTY B)) (term152 A B t i x)). Qed.
Lemma lem7192135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192136 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term288 A B y t i x) = (term289 A B y t i x).
Proof. exact (MK_COMB (@lem7192135) (@lem7192118 A B y t i x)). Qed.
Lemma lem7192153 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term290 A B t i x y g) = (term290 A B t i x y g).
Proof. exact (eq_refl (term290 A B t i x y g)). Qed.
Lemma lem7192154 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term222 A B t i x y g) = (term291 A B t i x y g).
Proof. exact (MK_COMB (@lem7192136 A B y t i x) (@lem7192153 A B t i x y g)). Qed.
Lemma lem7192157 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term292 A B f i y x g t s) = (term292 A B f i y x g t s).
Proof. exact (eq_refl (term292 A B f i y x g t s)). Qed.
Lemma lem7192158 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term293 A B f s t i x y g) = (term294 A B f s t i x y g).
Proof. exact (MK_COMB (@lem7192157 A B f i y x g t s) (@lem7192154 A B t i x y g)). Qed.
Lemma lem7192161 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term294 A B f s t i x y g) = (term293 A B f s t i x y g).
Proof. exact (SYM (@lem7192158 A B f s t i x y g)). Qed.
Lemma lem7192173 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7192174 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7192173 B P x). Qed.
Lemma lem7192175 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7192174 B t y). Qed.
Lemma lem7192176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192177 {B : Type'} (t : B -> Prop) (y : B) : (term202 B y t) = (term295 B t y).
Proof. exact (MK_COMB (@lem7192176) (@lem7192175 B t y)). Qed.
Lemma lem7192181 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7192182 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7192181 A P x). Qed.
Lemma lem7192183 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7192182 A s x). Qed.
Lemma lem7192184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192185 {A : Type'} (s : A -> Prop) (x : A) : (term202 A x s) = (term295 A s x).
Proof. exact (MK_COMB (@lem7192184) (@lem7192183 A s x)). Qed.
Lemma lem7192195 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7192196 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7192195 B P x). Qed.
Lemma lem7192197 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7192196 B t y). Qed.
Lemma lem7192198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7192199 {B : Type'} (t : B -> Prop) (y : B) : (term104 B y t) = (term296 B t y).
Proof. exact (MK_COMB (@lem7192198) (@lem7192197 B t y)). Qed.
Lemma lem7192200 {B : Type'} (g : B -> real) (y : B) : (term235 B g y) = (term235 B g y).
Proof. exact (eq_refl (term235 B g y)). Qed.
Lemma lem7192201 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term234 B t g y) = (term297 B t g y).
Proof. exact (MK_COMB (@lem7192199 B t y) (@lem7192200 B g y)). Qed.
Lemma lem7192204 {B : Type'} (t : B -> Prop) (g : B -> real) : (term298 B t g) = (term299 B t g).
Proof. exact (fun_ext (fun y : B => @lem7192201 B t g y)). Qed.
Lemma lem7192205 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192206 {B : Type'} (t : B -> Prop) (g : B -> real) : (term83 B t g) = (term300 B t g).
Proof. exact (MK_COMB (@lem7192205 B) (@lem7192204 B t g)). Qed.
Lemma lem7192211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192212 {B : Type'} (t : B -> Prop) (g : B -> real) : (term301 B t g) = (term302 B t g).
Proof. exact (MK_COMB (@lem7192211) (@lem7192206 B t g)). Qed.
Lemma lem7192215 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7192216 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term280 A B g t s) = (term303 A B g t s).
Proof. exact (MK_COMB (@lem7192212 B t g) (@lem7192215 A B t s)). Qed.
Lemma lem7192219 {A B : Type'} (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term281 A B x g t s) = (term304 A B x g t s).
Proof. exact (MK_COMB (@lem7192185 A s x) (@lem7192216 A B g t s)). Qed.
Lemma lem7192222 {A B : Type'} (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term282 A B y x g t s) = (term305 A B y x g t s).
Proof. exact (MK_COMB (@lem7192177 B t y) (@lem7192219 A B x g t s)). Qed.
Lemma lem7192225 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term306 A B i y x) = (term306 A B i y x).
Proof. exact (eq_refl (term306 A B i y x)). Qed.
Lemma lem7192226 {A B : Type'} (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term283 A B i y x g t s) = (term307 A B i y x g t s).
Proof. exact (MK_COMB (@lem7192225 A B i y x) (@lem7192222 A B y x g t s)). Qed.
Lemma lem7192229 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term308 A B f x g y) = (term308 A B f x g y).
Proof. exact (eq_refl (term308 A B f x g y)). Qed.
Lemma lem7192230 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term284 A B f i y x g t s) = (term309 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7192229 A B f x g y) (@lem7192226 A B i y x g t s)). Qed.
Lemma lem7192233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7192234 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term292 A B f i y x g t s) = (term310 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7192233) (@lem7192230 A B f i y x g t s)). Qed.
Lemma lem7192244 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term311 A x y s) = (term312 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem7192245 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term311 B x y s) = (term312 B y x s).
Proof. exact (@lem7192244 B y x s). Qed.
Lemma lem7192246 {B : Type'} (y : B) (x : B) : (term313 B x y) = (term314 B y x).
Proof. exact (@lem7192245 B y x (@EMPTY B)). Qed.
Lemma lem7192252 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7192253 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem7192252 B x). Qed.
Lemma lem7192254 {B : Type'} (x : B) (y : B) : (term315 B x y) = (term315 B x y).
Proof. exact (eq_refl (term315 B x y)). Qed.
Lemma lem7192255 {B : Type'} (x : B) (y : B) : (term314 B y x) = (term316 B x y).
Proof. exact (MK_COMB (@lem7192254 B x y) (@lem7192253 B x)). Qed.
Lemma lem7192257 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem7192258 {B : Type'} (x : B) (y : B) : (term316 B x y) = (x = y).
Proof. exact (@lem7192257 (x = y)). Qed.
Lemma lem7192261 {B : Type'} (x : B) (y : B) : (term314 B y x) = (x = y).
Proof. exact (TRANS (@lem7192255 B x y) (@lem7192258 B x y)). Qed.
Lemma lem7192262 {B : Type'} (x : B) (y : B) : (term313 B x y) = (x = y).
Proof. exact (TRANS (@lem7192246 B y x) (@lem7192261 B x y)). Qed.
Lemma lem7192263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7192264 {B : Type'} (x : B) (y : B) : (term317 B x y) = (term318 B x y).
Proof. exact (MK_COMB (@lem7192263) (@lem7192262 B x y)). Qed.
Lemma lem7192266 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term229 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7192267 {B : Type'} (p : B -> Prop) (x : B) : (term229 B x p) = (p x).
Proof. exact (@lem7192266 B p x). Qed.
Lemma lem7192268 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term251 A B x' t i x) = (term252 A B t i x x').
Proof. exact (@lem7192267 B (term253 A B t i x) x'). Qed.
Lemma lem7192269 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7192270 {B : Type'} (GEN_PVAR_331 : B) : (@SETSPEC B GEN_PVAR_331) = (@SETSPEC B GEN_PVAR_331).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_331)). Qed.
Lemma lem7192271 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term254 A B GEN_PVAR_331 t i x' x) = (term206 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7192270 B GEN_PVAR_331) (@lem7192269 A B t i x x')). Qed.
Lemma lem7192272 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7192273 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term255 A B GEN_PVAR_331 t i x x') = (term208 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7192271 A B GEN_PVAR_331 t i x' x) (@lem7192272 B x')). Qed.
Lemma lem7192274 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term256 A B GEN_PVAR_331 t i x) = (term210 A B GEN_PVAR_331 t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192273 A B GEN_PVAR_331 t i x x')). Qed.
Lemma lem7192275 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192276 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term257 A B GEN_PVAR_331 t i x) = (term212 A B GEN_PVAR_331 t i x).
Proof. exact (MK_COMB (@lem7192275 B) (@lem7192274 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192277 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term258 A B t i x) = (term214 A B t i x).
Proof. exact (fun_ext (fun GEN_PVAR_331 : B => @lem7192276 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192278 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem7192279 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term259 A B t i x) = (term152 A B t i x).
Proof. exact (MK_COMB (@lem7192278 B) (@lem7192277 A B t i x)). Qed.
Lemma lem7192280 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem7192281 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term251 A B x t i x') = (term246 A B x t i x').
Proof. exact (MK_COMB (@lem7192280 B x) (@lem7192279 A B t i x')). Qed.
Lemma lem7192282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7192283 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term260 A B x t i x') = (term261 A B x t i x').
Proof. exact (MK_COMB (@lem7192282) (@lem7192281 A B x t i x')). Qed.
Lemma lem7192284 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7192285 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : ((term251 A B x t i x') = (term252 A B t i x' x)) = ((term246 A B x t i x') = (term204 A B t i x x')).
Proof. exact (MK_COMB (@lem7192283 A B x t i x') (@lem7192284 A B t i x x')). Qed.
Lemma lem7192286 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term246 A B x t i x') = (term204 A B t i x x').
Proof. exact (EQ_MP (@lem7192285 A B t i x x') (@lem7192268 A B t i x' x)). Qed.
Lemma lem7192290 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7192291 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7192290 B P x). Qed.
Lemma lem7192292 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7192291 B t x). Qed.
Lemma lem7192293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192294 {B : Type'} (t : B -> Prop) (x : B) : (term202 B x t) = (term295 B t x).
Proof. exact (MK_COMB (@lem7192293) (@lem7192292 B t x)). Qed.
Lemma lem7192297 {A B : Type'} (i : B -> A) (x : B) (x' : A) : ((i x) = x') = ((i x) = x').
Proof. exact (eq_refl ((i x) = x')). Qed.
Lemma lem7192298 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term204 A B t i x x') = (term319 A B t i x x').
Proof. exact (MK_COMB (@lem7192294 B t x) (@lem7192297 A B i x x')). Qed.
Lemma lem7192301 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term246 A B x t i x') = (term319 A B t i x x').
Proof. exact (TRANS (@lem7192286 A B t i x x') (@lem7192298 A B t i x x')). Qed.
Lemma lem7192302 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term320 A B y x t i x') = (term321 A B y t i x x').
Proof. exact (MK_COMB (@lem7192264 B x y) (@lem7192301 A B t i x x')). Qed.
Lemma lem7192307 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term322 A B y t i x) = (term323 A B y t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192302 A B y t i x' x)). Qed.
Lemma lem7192308 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192309 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term287 A B y t i x) = (term324 A B y t i x).
Proof. exact (MK_COMB (@lem7192308 B) (@lem7192307 A B y t i x)). Qed.
Lemma lem7192314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192315 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term289 A B y t i x) = (term325 A B y t i x).
Proof. exact (MK_COMB (@lem7192314) (@lem7192309 A B y t i x)). Qed.
Lemma lem7192323 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term326 A x s t) = (term327 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7192324 {B : Type'} (s : B -> Prop) (x : B) (t : B -> Prop) : (term326 B x s t) = (term327 B s x t).
Proof. exact (@lem7192323 B s x t). Qed.
Lemma lem7192325 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term328 A B x' t i x y) = (term329 A B t i x x' y).
Proof. exact (@lem7192324 B (term152 A B t i x) x' (@INSERT B y (@EMPTY B))). Qed.
Lemma lem7192329 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term229 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7192330 {B : Type'} (p : B -> Prop) (x : B) : (term229 B x p) = (p x).
Proof. exact (@lem7192329 B p x). Qed.
Lemma lem7192331 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term251 A B x' t i x) = (term252 A B t i x x').
Proof. exact (@lem7192330 B (term253 A B t i x) x'). Qed.
Lemma lem7192332 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7192333 {B : Type'} (GEN_PVAR_331 : B) : (@SETSPEC B GEN_PVAR_331) = (@SETSPEC B GEN_PVAR_331).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_331)). Qed.
Lemma lem7192334 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term254 A B GEN_PVAR_331 t i x' x) = (term206 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7192333 B GEN_PVAR_331) (@lem7192332 A B t i x x')). Qed.
Lemma lem7192335 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7192336 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) (x' : B) : (term255 A B GEN_PVAR_331 t i x x') = (term208 A B GEN_PVAR_331 t i x x').
Proof. exact (MK_COMB (@lem7192334 A B GEN_PVAR_331 t i x' x) (@lem7192335 B x')). Qed.
Lemma lem7192337 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term256 A B GEN_PVAR_331 t i x) = (term210 A B GEN_PVAR_331 t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192336 A B GEN_PVAR_331 t i x x')). Qed.
Lemma lem7192338 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192339 {A B : Type'} (GEN_PVAR_331 : B) (t : B -> Prop) (i : B -> A) (x : A) : (term257 A B GEN_PVAR_331 t i x) = (term212 A B GEN_PVAR_331 t i x).
Proof. exact (MK_COMB (@lem7192338 B) (@lem7192337 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192340 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term258 A B t i x) = (term214 A B t i x).
Proof. exact (fun_ext (fun GEN_PVAR_331 : B => @lem7192339 A B GEN_PVAR_331 t i x)). Qed.
Lemma lem7192341 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem7192342 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) : (term259 A B t i x) = (term152 A B t i x).
Proof. exact (MK_COMB (@lem7192341 B) (@lem7192340 A B t i x)). Qed.
Lemma lem7192343 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem7192344 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term251 A B x t i x') = (term246 A B x t i x').
Proof. exact (MK_COMB (@lem7192343 B x) (@lem7192342 A B t i x')). Qed.
Lemma lem7192345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7192346 {A B : Type'} (x : B) (t : B -> Prop) (i : B -> A) (x' : A) : (term260 A B x t i x') = (term261 A B x t i x').
Proof. exact (MK_COMB (@lem7192345) (@lem7192344 A B x t i x')). Qed.
Lemma lem7192347 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term252 A B t i x' x) = (term204 A B t i x x').
Proof. exact (eq_refl (term252 A B t i x' x)). Qed.
Lemma lem7192348 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : ((term251 A B x t i x') = (term252 A B t i x' x)) = ((term246 A B x t i x') = (term204 A B t i x x')).
Proof. exact (MK_COMB (@lem7192346 A B x t i x') (@lem7192347 A B t i x x')). Qed.
Lemma lem7192349 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term246 A B x t i x') = (term204 A B t i x x').
Proof. exact (EQ_MP (@lem7192348 A B t i x x') (@lem7192331 A B t i x' x)). Qed.
Lemma lem7192353 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7192354 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7192353 B P x). Qed.
Lemma lem7192355 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7192354 B t x). Qed.
Lemma lem7192356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192357 {B : Type'} (t : B -> Prop) (x : B) : (term202 B x t) = (term295 B t x).
Proof. exact (MK_COMB (@lem7192356) (@lem7192355 B t x)). Qed.
Lemma lem7192360 {A B : Type'} (i : B -> A) (x : B) (x' : A) : ((i x) = x') = ((i x) = x').
Proof. exact (eq_refl ((i x) = x')). Qed.
Lemma lem7192361 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term204 A B t i x x') = (term319 A B t i x x').
Proof. exact (MK_COMB (@lem7192357 B t x) (@lem7192360 A B i x x')). Qed.
Lemma lem7192364 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term246 A B x t i x') = (term319 A B t i x x').
Proof. exact (TRANS (@lem7192349 A B t i x x') (@lem7192361 A B t i x x')). Qed.
Lemma lem7192365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192366 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term330 A B x t i x') = (term331 A B t i x x').
Proof. exact (MK_COMB (@lem7192365) (@lem7192364 A B t i x x')). Qed.
Lemma lem7192368 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term311 A x y s) = (term312 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem7192369 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term311 B x y s) = (term312 B y x s).
Proof. exact (@lem7192368 B y x s). Qed.
Lemma lem7192370 {B : Type'} (y : B) (x : B) : (term313 B x y) = (term314 B y x).
Proof. exact (@lem7192369 B y x (@EMPTY B)). Qed.
Lemma lem7192376 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7192377 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem7192376 B x). Qed.
Lemma lem7192378 {B : Type'} (x : B) (y : B) : (term315 B x y) = (term315 B x y).
Proof. exact (eq_refl (term315 B x y)). Qed.
Lemma lem7192379 {B : Type'} (x : B) (y : B) : (term314 B y x) = (term316 B x y).
Proof. exact (MK_COMB (@lem7192378 B x y) (@lem7192377 B x)). Qed.
Lemma lem7192381 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem7192382 {B : Type'} (x : B) (y : B) : (term316 B x y) = (x = y).
Proof. exact (@lem7192381 (x = y)). Qed.
Lemma lem7192385 {B : Type'} (x : B) (y : B) : (term314 B y x) = (x = y).
Proof. exact (TRANS (@lem7192379 B x y) (@lem7192382 B x y)). Qed.
Lemma lem7192386 {B : Type'} (x : B) (y : B) : (term313 B x y) = (x = y).
Proof. exact (TRANS (@lem7192370 B y x) (@lem7192385 B x y)). Qed.
Lemma lem7192387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7192388 {B : Type'} (x : B) (y : B) : (term332 B x y) = (term333 B x y).
Proof. exact (MK_COMB (@lem7192387) (@lem7192386 B x y)). Qed.
Lemma lem7192389 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term329 A B t i x x' y) = (term334 A B t i x x' y).
Proof. exact (MK_COMB (@lem7192366 A B t i x' x) (@lem7192388 B x' y)). Qed.
Lemma lem7192392 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term328 A B x' t i x y) = (term334 A B t i x x' y).
Proof. exact (TRANS (@lem7192325 A B t i x x' y) (@lem7192389 A B t i x x' y)). Qed.
Lemma lem7192393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7192394 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term335 A B x' t i x y) = (term336 A B t i x x' y).
Proof. exact (MK_COMB (@lem7192393) (@lem7192392 A B t i x x' y)). Qed.
Lemma lem7192395 {B : Type'} (g : B -> real) (x : B) : (term235 B g x) = (term235 B g x).
Proof. exact (eq_refl (term235 B g x)). Qed.
Lemma lem7192396 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term337 A B t i x y g x') = (term338 A B t i x y g x').
Proof. exact (MK_COMB (@lem7192394 A B t i x x' y) (@lem7192395 B g x')). Qed.
Lemma lem7192399 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term339 A B t i x y g) = (term340 A B t i x y g).
Proof. exact (fun_ext (fun x' : B => @lem7192396 A B t i x y g x')). Qed.
Lemma lem7192400 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192401 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term290 A B t i x y g) = (term341 A B t i x y g).
Proof. exact (MK_COMB (@lem7192400 B) (@lem7192399 A B t i x y g)). Qed.
Lemma lem7192406 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term291 A B t i x y g) = (term342 A B t i x y g).
Proof. exact (MK_COMB (@lem7192315 A B y t i x) (@lem7192401 A B t i x y g)). Qed.
Lemma lem7192409 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term294 A B f s t i x y g) = (term343 A B f s t i x y g).
Proof. exact (MK_COMB (@lem7192234 A B f i y x g t s) (@lem7192406 A B t i x y g)). Qed.
Lemma lem7192412 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term343 A B f s t i x y g) = (term294 A B f s t i x y g).
Proof. exact (SYM (@lem7192409 A B f s t i x y g)). Qed.
Lemma lem7192414 (p : Prop) : p = (term344 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7192415 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term343 A B f s t i x y g) = (term345 A B f s t i x y g).
Proof. exact (@lem7192414 (term343 A B f s t i x y g)). Qed.
Lemma lem7192416 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term345 A B f s t i x y g) = (term343 A B f s t i x y g).
Proof. exact (SYM (@lem7192415 A B f s t i x y g)). Qed.
Lemma lem7192417 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term346 A B f s t i x y g) : term346 A B f s t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192420 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term345 A B f s t i x y g) : term345 A B f s t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192421 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term347 A B f s t i x y g.
Proof. exact (fun h0 : term345 A B f s t i x y g => @lem7192420 A B f s t i x y g h0). Qed.
Lemma lem7192422 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term347 A B f s t i x y g) : term347 A B f s t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192423 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term345 A B f s t i x y g) : term345 A B f s t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192424 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term345 A B f s t i x y g) (h2 : term347 A B f s t i x y g) : term345 A B f s t i x y g.
Proof. exact (@lem7192422 A B f s t i x y g h2 (@lem7192423 A B f s t i x y g h1)). Qed.
Lemma lem7192425 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term345 A B f s t i x y g) : term348 A B f s t i x y g.
Proof. exact (fun h0 : term347 A B f s t i x y g => @lem7192424 A B f s t i x y g h1 h0). Qed.
Lemma lem7192426 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term347 A B f s t i x y g) : term347 A B f s t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192427 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term345 A B f s t i x y g) (h2 : term347 A B f s t i x y g) : term345 A B f s t i x y g.
Proof. exact (@lem7192425 A B f s t i x y g h1 (@lem7192426 A B f s t i x y g h2)). Qed.
Lemma lem7192428 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term347 A B f s t i x y g) : term347 A B f s t i x y g.
Proof. exact (fun h0 : term345 A B f s t i x y g => @lem7192427 A B f s t i x y g h0 h1). Qed.
Lemma lem7192429 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term349 A B f s t i x y g.
Proof. exact (fun h0 : term347 A B f s t i x y g => @lem7192428 A B f s t i x y g h0). Qed.
Lemma lem7192432 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term347 A B f s t i x y g.
Proof. exact (@lem7192429 A B f s t i x y g (@lem7192421 A B f s t i x y g)). Qed.
Lemma lem7192433 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term347 A B f s t i x y g.
Proof. exact (@lem7192432 A B f s t i x y g). Qed.
Lemma lem7192463 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7192464 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term345 A B f s t i x y g) = (term350 A B f s t i x y g).
Proof. exact (@lem7192463 (term346 A B f s t i x y g)). Qed.
Lemma lem7192466 (t : Prop) : (term351 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7192467 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term350 A B f s t i x y g) = (term343 A B f s t i x y g).
Proof. exact (@lem7192466 (term343 A B f s t i x y g)). Qed.
Lemma lem7192470 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term345 A B f s t i x y g) = (term343 A B f s t i x y g).
Proof. exact (TRANS (@lem7192464 A B f s t i x y g) (@lem7192467 A B f s t i x y g)). Qed.
Lemma lem7192509 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term352 A B s t i x y g) = (term353 A B s t i x y g).
Proof. exact (fun_ext (fun f : A -> real => @lem7192470 A B f s t i x y g)). Qed.
Lemma lem7192510 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7192511 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term354 A B s t i x y g) = (term355 A B s t i x y g).
Proof. exact (MK_COMB (@lem7192510 A) (@lem7192509 A B s t i x y g)). Qed.
Lemma lem7192516 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term356 A B t i x y g) = (term357 A B t i x y g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7192511 A B s t i x y g)). Qed.
Lemma lem7192517 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7192518 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term358 A B t i x y g) = (term359 A B t i x y g).
Proof. exact (MK_COMB (@lem7192517 A) (@lem7192516 A B t i x y g)). Qed.
Lemma lem7192523 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : (term360 A B i x y g) = (term361 A B i x y g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7192518 A B t i x y g)). Qed.
Lemma lem7192524 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7192525 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : (term362 A B i x y g) = (term363 A B i x y g).
Proof. exact (MK_COMB (@lem7192524 B) (@lem7192523 A B i x y g)). Qed.
Lemma lem7192530 {A B : Type'} (x : A) (y : B) (g : B -> real) : (term364 A B x y g) = (term365 A B x y g).
Proof. exact (fun_ext (fun i : B -> A => @lem7192525 A B i x y g)). Qed.
Lemma lem7192531 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7192532 {A B : Type'} (x : A) (y : B) (g : B -> real) : (term366 A B x y g) = (term367 A B x y g).
Proof. exact (MK_COMB (@lem7192531 A B) (@lem7192530 A B x y g)). Qed.
Lemma lem7192537 {A B : Type'} (y : B) (g : B -> real) : (term368 A B y g) = (term369 A B y g).
Proof. exact (fun_ext (fun x : A => @lem7192532 A B x y g)). Qed.
Lemma lem7192538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7192539 {A B : Type'} (y : B) (g : B -> real) : (term370 A B y g) = (term371 A B y g).
Proof. exact (MK_COMB (@lem7192538 A) (@lem7192537 A B y g)). Qed.
Lemma lem7192544 {A B : Type'} (g : B -> real) : (term372 A B g) = (term373 A B g).
Proof. exact (fun_ext (fun y : B => @lem7192539 A B y g)). Qed.
Lemma lem7192545 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192546 {A B : Type'} (g : B -> real) : (term374 A B g) = (term375 A B g).
Proof. exact (MK_COMB (@lem7192545 B) (@lem7192544 A B g)). Qed.
Lemma lem7192551 {A B : Type'} : (term376 A B) = (term377 A B).
Proof. exact (fun_ext (fun g : B -> real => @lem7192546 A B g)). Qed.
Lemma lem7192552 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7192561 {A B : Type'} : (term378 A B) = (term379 A B).
Proof. exact (MK_COMB (@lem7192552 B) (@lem7192551 A B)). Qed.
Lemma lem7192576 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term338 A B t i x y g x') = (term338 A B t i x y g x').
Proof. exact (eq_refl (term338 A B t i x y g x')). Qed.
Lemma lem7192577 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term340 A B t i x y g) = (term340 A B t i x y g).
Proof. exact (fun_ext (fun x' : B => @lem7192576 A B t i x y g x')). Qed.
Lemma lem7192578 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192579 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term341 A B t i x y g) = (term341 A B t i x y g).
Proof. exact (MK_COMB (@lem7192578 B) (@lem7192577 A B t i x y g)). Qed.
Lemma lem7192588 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term321 A B y t i x x') = (term321 A B y t i x x').
Proof. exact (eq_refl (term321 A B y t i x x')). Qed.
Lemma lem7192589 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term323 A B y t i x) = (term323 A B y t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192588 A B y t i x' x)). Qed.
Lemma lem7192590 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192591 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term324 A B y t i x) = (term324 A B y t i x).
Proof. exact (MK_COMB (@lem7192590 B) (@lem7192589 A B y t i x)). Qed.
Lemma lem7192592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192593 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term325 A B y t i x) = (term325 A B y t i x).
Proof. exact (MK_COMB (@lem7192592) (@lem7192591 A B y t i x)). Qed.
Lemma lem7192594 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term342 A B t i x y g) = (term342 A B t i x y g).
Proof. exact (MK_COMB (@lem7192593 A B y t i x) (@lem7192579 A B t i x y g)). Qed.
Lemma lem7192599 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7192604 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term297 B t g y) = (term297 B t g y).
Proof. exact (eq_refl (term297 B t g y)). Qed.
Lemma lem7192605 {B : Type'} (t : B -> Prop) (g : B -> real) : (term299 B t g) = (term299 B t g).
Proof. exact (fun_ext (fun y : B => @lem7192604 B t g y)). Qed.
Lemma lem7192606 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192607 {B : Type'} (t : B -> Prop) (g : B -> real) : (term300 B t g) = (term300 B t g).
Proof. exact (MK_COMB (@lem7192606 B) (@lem7192605 B t g)). Qed.
Lemma lem7192608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192609 {B : Type'} (t : B -> Prop) (g : B -> real) : (term302 B t g) = (term302 B t g).
Proof. exact (MK_COMB (@lem7192608) (@lem7192607 B t g)). Qed.
Lemma lem7192610 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term303 A B g t s) = (term303 A B g t s).
Proof. exact (MK_COMB (@lem7192609 B t g) (@lem7192599 A B t s)). Qed.
Lemma lem7192613 {A : Type'} (s : A -> Prop) (x : A) : (term295 A s x) = (term295 A s x).
Proof. exact (eq_refl (term295 A s x)). Qed.
Lemma lem7192614 {A B : Type'} (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term304 A B x g t s) = (term304 A B x g t s).
Proof. exact (MK_COMB (@lem7192613 A s x) (@lem7192610 A B g t s)). Qed.
Lemma lem7192617 {B : Type'} (t : B -> Prop) (y : B) : (term295 B t y) = (term295 B t y).
Proof. exact (eq_refl (term295 B t y)). Qed.
Lemma lem7192618 {A B : Type'} (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term305 A B y x g t s) = (term305 A B y x g t s).
Proof. exact (MK_COMB (@lem7192617 B t y) (@lem7192614 A B x g t s)). Qed.
Lemma lem7192621 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term306 A B i y x) = (term306 A B i y x).
Proof. exact (eq_refl (term306 A B i y x)). Qed.
Lemma lem7192622 {A B : Type'} (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term307 A B i y x g t s) = (term307 A B i y x g t s).
Proof. exact (MK_COMB (@lem7192621 A B i y x) (@lem7192618 A B y x g t s)). Qed.
Lemma lem7192625 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term308 A B f x g y) = (term308 A B f x g y).
Proof. exact (eq_refl (term308 A B f x g y)). Qed.
Lemma lem7192626 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term309 A B f i y x g t s) = (term309 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7192625 A B f x g y) (@lem7192622 A B i y x g t s)). Qed.
Lemma lem7192627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7192628 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term310 A B f i y x g t s) = (term310 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7192627) (@lem7192626 A B f i y x g t s)). Qed.
Lemma lem7192629 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term343 A B f s t i x y g) = (term343 A B f s t i x y g).
Proof. exact (MK_COMB (@lem7192628 A B f i y x g t s) (@lem7192594 A B t i x y g)). Qed.
Lemma lem7192630 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term353 A B s t i x y g) = (term353 A B s t i x y g).
Proof. exact (fun_ext (fun f : A -> real => @lem7192629 A B f s t i x y g)). Qed.
Lemma lem7192631 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7192632 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term355 A B s t i x y g) = (term355 A B s t i x y g).
Proof. exact (MK_COMB (@lem7192631 A) (@lem7192630 A B s t i x y g)). Qed.
Lemma lem7192633 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term357 A B t i x y g) = (term357 A B t i x y g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7192632 A B s t i x y g)). Qed.
Lemma lem7192634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7192635 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term359 A B t i x y g) = (term359 A B t i x y g).
Proof. exact (MK_COMB (@lem7192634 A) (@lem7192633 A B t i x y g)). Qed.
Lemma lem7192636 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : (term361 A B i x y g) = (term361 A B i x y g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7192635 A B t i x y g)). Qed.
Lemma lem7192637 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7192638 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : (term363 A B i x y g) = (term363 A B i x y g).
Proof. exact (MK_COMB (@lem7192637 B) (@lem7192636 A B i x y g)). Qed.
Lemma lem7192639 {A B : Type'} (x : A) (y : B) (g : B -> real) : (term365 A B x y g) = (term365 A B x y g).
Proof. exact (fun_ext (fun i : B -> A => @lem7192638 A B i x y g)). Qed.
Lemma lem7192640 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7192641 {A B : Type'} (x : A) (y : B) (g : B -> real) : (term367 A B x y g) = (term367 A B x y g).
Proof. exact (MK_COMB (@lem7192640 A B) (@lem7192639 A B x y g)). Qed.
Lemma lem7192642 {A B : Type'} (y : B) (g : B -> real) : (term369 A B y g) = (term369 A B y g).
Proof. exact (fun_ext (fun x : A => @lem7192641 A B x y g)). Qed.
Lemma lem7192643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7192644 {A B : Type'} (y : B) (g : B -> real) : (term371 A B y g) = (term371 A B y g).
Proof. exact (MK_COMB (@lem7192643 A) (@lem7192642 A B y g)). Qed.
Lemma lem7192645 {A B : Type'} (g : B -> real) : (term373 A B g) = (term373 A B g).
Proof. exact (fun_ext (fun y : B => @lem7192644 A B y g)). Qed.
Lemma lem7192646 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192647 {A B : Type'} (g : B -> real) : (term375 A B g) = (term375 A B g).
Proof. exact (MK_COMB (@lem7192646 B) (@lem7192645 A B g)). Qed.
Lemma lem7192648 {A B : Type'} : (term377 A B) = (term377 A B).
Proof. exact (fun_ext (fun g : B -> real => @lem7192647 A B g)). Qed.
Lemma lem7192649 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7192650 {A B : Type'} : (term379 A B) = (term379 A B).
Proof. exact (MK_COMB (@lem7192649 B) (@lem7192648 A B)). Qed.
Lemma lem7192741 {A B : Type'} : (term378 A B) = (term379 A B).
Proof. exact (TRANS (@lem7192561 A B) (@lem7192650 A B)). Qed.
Lemma lem7192742 {A B : Type'} : (term379 A B) = (term378 A B).
Proof. exact (SYM (@lem7192741 A B)). Qed.
Lemma lem7192743 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term309 A B f i y x g t s.
Proof. exact (h1). Qed.
Lemma lem7192745 (p : Prop) : p = (term344 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7192746 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term342 A B t i x y g) = (term380 A B t i x y g).
Proof. exact (@lem7192745 (term342 A B t i x y g)). Qed.
Lemma lem7192747 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term380 A B t i x y g) = (term342 A B t i x y g).
Proof. exact (SYM (@lem7192746 A B t i x y g)). Qed.
Lemma lem7192748 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term381 A B t i x y g) : term381 A B t i x y g.
Proof. exact (h1). Qed.
Lemma lem7192759 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term297 B t g y) = (term382 B t g y).
Proof. exact (@lem17265 (t y) (term235 B g y)). Qed.
Lemma lem7192760 {B : Type'} (t : B -> Prop) (g : B -> real) : (term299 B t g) = (term383 B t g).
Proof. exact (fun_ext (fun y : B => @lem7192759 B t g y)). Qed.
Lemma lem7192761 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7192762 {B : Type'} (t : B -> Prop) (g : B -> real) : (term300 B t g) = (term384 B t g).
Proof. exact (MK_COMB (@lem7192761 B) (@lem7192760 B t g)). Qed.
Lemma lem7192767 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7192768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7192769 {B : Type'} (t : B -> Prop) (g : B -> real) : (term302 B t g) = (term385 B t g).
Proof. exact (MK_COMB (@lem7192768) (@lem7192762 B t g)). Qed.
Lemma lem7192770 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term303 A B g t s) = (term386 A B g t s).
Proof. exact (MK_COMB (@lem7192769 B t g) (@lem7192767 A B t s)). Qed.
Lemma lem7192772 {A : Type'} (s : A -> Prop) (x : A) : (term295 A s x) = (term295 A s x).
Proof. exact (eq_refl (term295 A s x)). Qed.
Lemma lem7192773 {A B : Type'} (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term304 A B x g t s) = (term387 A B x g t s).
Proof. exact (MK_COMB (@lem7192772 A s x) (@lem7192770 A B g t s)). Qed.
Lemma lem7192775 {B : Type'} (t : B -> Prop) (y : B) : (term295 B t y) = (term295 B t y).
Proof. exact (eq_refl (term295 B t y)). Qed.
Lemma lem7192776 {A B : Type'} (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term305 A B y x g t s) = (term388 A B y x g t s).
Proof. exact (MK_COMB (@lem7192775 B t y) (@lem7192773 A B x g t s)). Qed.
Lemma lem7192778 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term306 A B i y x) = (term306 A B i y x).
Proof. exact (eq_refl (term306 A B i y x)). Qed.
Lemma lem7192779 {A B : Type'} (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term307 A B i y x g t s) = (term389 A B i y x g t s).
Proof. exact (MK_COMB (@lem7192778 A B i y x) (@lem7192776 A B y x g t s)). Qed.
Lemma lem7192781 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term308 A B f x g y) = (term308 A B f x g y).
Proof. exact (eq_refl (term308 A B f x g y)). Qed.
Lemma lem7192834 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term309 A B f i y x g t s) = (term390 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7192781 A B f x g y) (@lem7192779 A B i y x g t s)). Qed.
Lemma lem7192835 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term390 A B f i y x g t s.
Proof. exact (EQ_MP (@lem7192834 A B f i y x g t s) (@lem7192743 A B f i y x g t s h1)). Qed.
Lemma lem7192843 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term391 A B t i x x') = (term392 A B t i x x').
Proof. exact (@lem17045 (t x) ((i x) = x')). Qed.
Lemma lem7192845 {B : Type'} (x : B) (y : B) : (term393 B x y) = (term393 B x y).
Proof. exact (eq_refl (term393 B x y)). Qed.
Lemma lem7192846 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term394 A B y t i x x') = (term395 A B y t i x x').
Proof. exact (MK_COMB (@lem7192845 B x y) (@lem7192843 A B t i x x')). Qed.
Lemma lem7192847 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term396 A B y t i x x') = (term394 A B y t i x x').
Proof. exact (@lem17362 (x = y) (term319 A B t i x x')). Qed.
Lemma lem7192848 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term396 A B y t i x x') = (term395 A B y t i x x').
Proof. exact (TRANS (@lem7192847 A B y t i x x') (@lem7192846 A B y t i x x')). Qed.
Lemma lem7192849 {B : Type'} (P : B -> Prop) : (term397 B P) = (term398 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem7192850 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term399 A B y t i x) = (term400 A B y t i x).
Proof. exact (@lem7192849 B (term323 A B y t i x)). Qed.
Lemma lem7192851 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term401 A B y t i x' x) = (term321 A B y t i x x').
Proof. exact (eq_refl (term401 A B y t i x' x)). Qed.
Lemma lem7192852 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7192853 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term402 A B y t i x' x) = (term396 A B y t i x x').
Proof. exact (MK_COMB (@lem7192852) (@lem7192851 A B y t i x x')). Qed.
Lemma lem7192854 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term402 A B y t i x' x) = (term395 A B y t i x x').
Proof. exact (TRANS (@lem7192853 A B y t i x x') (@lem7192848 A B y t i x x')). Qed.
Lemma lem7192855 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term403 A B y t i x) = (term404 A B y t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192854 A B y t i x' x)). Qed.
Lemma lem7192856 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192857 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term400 A B y t i x) = (term405 A B y t i x).
Proof. exact (MK_COMB (@lem7192856 B) (@lem7192855 A B y t i x)). Qed.
Lemma lem7192858 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term399 A B y t i x) = (term405 A B y t i x).
Proof. exact (TRANS (@lem7192850 A B y t i x) (@lem7192857 A B y t i x)). Qed.
Lemma lem7192873 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term406 A B t i x y g x') = (term407 A B t i x y g x').
Proof. exact (@lem17362 (term334 A B t i x x' y) (term235 B g x')). Qed.
Lemma lem7192874 {B : Type'} (P : B -> Prop) : (term397 B P) = (term398 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem7192875 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term408 A B t i x y g) = (term409 A B t i x y g).
Proof. exact (@lem7192874 B (term340 A B t i x y g)). Qed.
Lemma lem7192876 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term410 A B t i x y g x') = (term338 A B t i x y g x').
Proof. exact (eq_refl (term410 A B t i x y g x')). Qed.
Lemma lem7192877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7192878 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term411 A B t i x y g x') = (term406 A B t i x y g x').
Proof. exact (MK_COMB (@lem7192877) (@lem7192876 A B t i x y g x')). Qed.
Lemma lem7192879 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term411 A B t i x y g x') = (term407 A B t i x y g x').
Proof. exact (TRANS (@lem7192878 A B t i x y g x') (@lem7192873 A B t i x y g x')). Qed.
Lemma lem7192880 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term412 A B t i x y g) = (term413 A B t i x y g).
Proof. exact (fun_ext (fun x' : B => @lem7192879 A B t i x y g x')). Qed.
Lemma lem7192881 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192882 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term409 A B t i x y g) = (term414 A B t i x y g).
Proof. exact (MK_COMB (@lem7192881 B) (@lem7192880 A B t i x y g)). Qed.
Lemma lem7192883 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term408 A B t i x y g) = (term414 A B t i x y g).
Proof. exact (TRANS (@lem7192875 A B t i x y g) (@lem7192882 A B t i x y g)). Qed.
Lemma lem7192884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7192885 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term415 A B y t i x) = (term416 A B y t i x).
Proof. exact (MK_COMB (@lem7192884) (@lem7192858 A B y t i x)). Qed.
Lemma lem7192886 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term417 A B t i x y g) = (term418 A B t i x y g).
Proof. exact (MK_COMB (@lem7192885 A B y t i x) (@lem7192883 A B t i x y g)). Qed.
Lemma lem7192887 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term381 A B t i x y g) = (term417 A B t i x y g).
Proof. exact (@lem17045 (term324 A B y t i x) (term341 A B t i x y g)). Qed.
Lemma lem7192888 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term381 A B t i x y g) = (term418 A B t i x y g).
Proof. exact (TRANS (@lem7192887 A B t i x y g) (@lem7192886 A B t i x y g)). Qed.
Lemma lem7192987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term419 A P Q) = (term420 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7192988 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term419 B P Q) = (term420 B P Q).
Proof. exact (@lem7192987 B P Q). Qed.
Lemma lem7192989 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term421 A B t i x y g) = (term422 A B t i x y g).
Proof. exact (@lem7192988 B (term404 A B y t i x) (term413 A B t i x y g)). Qed.
Lemma lem7192990 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term423 A B y t i x' x) = (term395 A B y t i x x').
Proof. exact (eq_refl (term423 A B y t i x' x)). Qed.
Lemma lem7192991 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term424 A B y t i x) = (term404 A B y t i x).
Proof. exact (fun_ext (fun x' : B => @lem7192990 A B y t i x' x)). Qed.
Lemma lem7192992 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192993 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term425 A B y t i x) = (term405 A B y t i x).
Proof. exact (MK_COMB (@lem7192992 B) (@lem7192991 A B y t i x)). Qed.
Lemma lem7192994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7192995 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : A) : (term426 A B y t i x) = (term416 A B y t i x).
Proof. exact (MK_COMB (@lem7192994) (@lem7192993 A B y t i x)). Qed.
Lemma lem7192996 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term427 A B t i x y g x') = (term407 A B t i x y g x').
Proof. exact (eq_refl (term427 A B t i x y g x')). Qed.
Lemma lem7192997 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term428 A B t i x y g) = (term413 A B t i x y g).
Proof. exact (fun_ext (fun x' : B => @lem7192996 A B t i x y g x')). Qed.
Lemma lem7192998 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7192999 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term429 A B t i x y g) = (term414 A B t i x y g).
Proof. exact (MK_COMB (@lem7192998 B) (@lem7192997 A B t i x y g)). Qed.
Lemma lem7193000 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term421 A B t i x y g) = (term418 A B t i x y g).
Proof. exact (MK_COMB (@lem7192995 A B y t i x) (@lem7192999 A B t i x y g)). Qed.
Lemma lem7193001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7193002 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term430 A B t i x y g) = (term431 A B t i x y g).
Proof. exact (MK_COMB (@lem7193001) (@lem7193000 A B t i x y g)). Qed.
Lemma lem7193003 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term423 A B y t i x' x) = (term395 A B y t i x x').
Proof. exact (eq_refl (term423 A B y t i x' x)). Qed.
Lemma lem7193004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7193005 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x : B) (x' : A) : (term432 A B y t i x' x) = (term433 A B y t i x x').
Proof. exact (MK_COMB (@lem7193004) (@lem7193003 A B y t i x x')). Qed.
Lemma lem7193006 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term427 A B t i x y g x') = (term407 A B t i x y g x').
Proof. exact (eq_refl (term427 A B t i x y g x')). Qed.
Lemma lem7193007 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term434 A B t i x y g x') = (term435 A B t i x y g x').
Proof. exact (MK_COMB (@lem7193005 A B y t i x' x) (@lem7193006 A B t i x y g x')). Qed.
Lemma lem7193008 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term436 A B t i x y g) = (term437 A B t i x y g).
Proof. exact (fun_ext (fun x' : B => @lem7193007 A B t i x y g x')). Qed.
Lemma lem7193009 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7193010 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term422 A B t i x y g) = (term438 A B t i x y g).
Proof. exact (MK_COMB (@lem7193009 B) (@lem7193008 A B t i x y g)). Qed.
Lemma lem7193011 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : ((term421 A B t i x y g) = (term422 A B t i x y g)) = ((term418 A B t i x y g) = (term438 A B t i x y g)).
Proof. exact (MK_COMB (@lem7193002 A B t i x y g) (@lem7193010 A B t i x y g)). Qed.
Lemma lem7193013 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term418 A B t i x y g) = (term438 A B t i x y g).
Proof. exact (EQ_MP (@lem7193011 A B t i x y g) (@lem7192989 A B t i x y g)). Qed.
Lemma lem7193014 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term381 A B t i x y g) = (term438 A B t i x y g).
Proof. exact (TRANS (@lem7192888 A B t i x y g) (@lem7193013 A B t i x y g)). Qed.
Lemma lem7193015 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term381 A B t i x y g) : term438 A B t i x y g.
Proof. exact (EQ_MP (@lem7193014 A B t i x y g) (@lem7192748 A B t i x y g h1)). Qed.
Lemma lem7193016 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term435 A B t i x y g x') : term435 A B t i x y g x'.
Proof. exact (h1). Qed.
Lemma lem7193025 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7193036 {B : Type'} (g : B -> real) (y : B) : (term235 B g y) = (term235 B g y).
Proof. exact (eq_refl (term235 B g y)). Qed.
Lemma lem7193037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7193042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7193043 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7193042 B Prop f x). Qed.
Lemma lem7193045 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem7193043 B t y). Qed.
Lemma lem7193046 {B : Type'} (t : B -> Prop) (y : B) : (term439 B t y) = (term440 B t y).
Proof. exact (MK_COMB (@lem7193037) (@lem7193045 B t y)). Qed.
Lemma lem7193047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7193048 {B : Type'} (t : B -> Prop) (y : B) : (term441 B t y) = (term442 B t y).
Proof. exact (MK_COMB (@lem7193047) (@lem7193046 B t y)). Qed.
Lemma lem7193049 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term382 B t g y) = (term443 B t g y).
Proof. exact (MK_COMB (@lem7193048 B t y) (@lem7193036 B g y)). Qed.
Lemma lem7193050 {B : Type'} (t : B -> Prop) (g : B -> real) : (term383 B t g) = (term444 B t g).
Proof. exact (fun_ext (fun y : B => @lem7193049 B t g y)). Qed.
Lemma lem7193051 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7193052 {B : Type'} (t : B -> Prop) (g : B -> real) : (term384 B t g) = (term445 B t g).
Proof. exact (MK_COMB (@lem7193051 B) (@lem7193050 B t g)). Qed.
Lemma lem7193053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193054 {B : Type'} (t : B -> Prop) (g : B -> real) : (term385 B t g) = (term446 B t g).
Proof. exact (MK_COMB (@lem7193053) (@lem7193052 B t g)). Qed.
Lemma lem7193055 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term386 A B g t s) = (term447 A B g t s).
Proof. exact (MK_COMB (@lem7193054 B t g) (@lem7193025 A B t s)). Qed.
Lemma lem7193060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7193061 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7193060 A Prop f x). Qed.
Lemma lem7193063 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7193061 A s x). Qed.
Lemma lem7193064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193065 {A : Type'} (s : A -> Prop) (x : A) : (term295 A s x) = (term448 A s x).
Proof. exact (MK_COMB (@lem7193064) (@lem7193063 A s x)). Qed.
Lemma lem7193066 {A B : Type'} (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term387 A B x g t s) = (term449 A B x g t s).
Proof. exact (MK_COMB (@lem7193065 A s x) (@lem7193055 A B g t s)). Qed.
Lemma lem7193071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7193072 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7193071 B Prop f x). Qed.
Lemma lem7193074 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem7193072 B t y). Qed.
Lemma lem7193075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193076 {B : Type'} (t : B -> Prop) (y : B) : (term295 B t y) = (term448 B t y).
Proof. exact (MK_COMB (@lem7193075) (@lem7193074 B t y)). Qed.
Lemma lem7193077 {A B : Type'} (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term388 A B y x g t s) = (term450 A B y x g t s).
Proof. exact (MK_COMB (@lem7193076 B t y) (@lem7193066 A B x g t s)). Qed.
Lemma lem7193086 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term306 A B i y x) = (term306 A B i y x).
Proof. exact (eq_refl (term306 A B i y x)). Qed.
Lemma lem7193087 {A B : Type'} (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term389 A B i y x g t s) = (term451 A B i y x g t s).
Proof. exact (MK_COMB (@lem7193086 A B i y x) (@lem7193077 A B y x g t s)). Qed.
Lemma lem7193098 {A B : Type'} (f : A -> real) (x : A) (g : B -> real) (y : B) : (term308 A B f x g y) = (term308 A B f x g y).
Proof. exact (eq_refl (term308 A B f x g y)). Qed.
Lemma lem7193099 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term390 A B f i y x g t s) = (term452 A B f i y x g t s).
Proof. exact (MK_COMB (@lem7193098 A B f x g y) (@lem7193087 A B i y x g t s)). Qed.
Lemma lem7193100 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term452 A B f i y x g t s.
Proof. exact (EQ_MP (@lem7193099 A B f i y x g t s) (@lem7192835 A B f i y x g t s h1)). Qed.
Lemma lem7193113 {B : Type'} (g : B -> real) (x' : B) : (term453 B g x') = (term453 B g x').
Proof. exact (eq_refl (term453 B g x')). Qed.
Lemma lem7193120 {B : Type'} (x' : B) (y : B) : (term333 B x' y) = (term333 B x' y).
Proof. exact (eq_refl (term333 B x' y)). Qed.
Lemma lem7193127 {A B : Type'} (i : B -> A) (x' : B) (x : A) : ((i x') = x) = ((i x') = x).
Proof. exact (eq_refl ((i x') = x)). Qed.
Lemma lem7193132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7193133 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7193132 B Prop f x). Qed.
Lemma lem7193135 {B : Type'} (t : B -> Prop) (x' : B) : (t x') = (@I (B -> Prop) t x').
Proof. exact (@lem7193133 B t x'). Qed.
Lemma lem7193136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193137 {B : Type'} (t : B -> Prop) (x' : B) : (term295 B t x') = (term448 B t x').
Proof. exact (MK_COMB (@lem7193136) (@lem7193135 B t x')). Qed.
Lemma lem7193138 {A B : Type'} (t : B -> Prop) (i : B -> A) (x' : B) (x : A) : (term319 A B t i x' x) = (term454 A B t i x' x).
Proof. exact (MK_COMB (@lem7193137 B t x') (@lem7193127 A B i x' x)). Qed.
Lemma lem7193139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193140 {A B : Type'} (t : B -> Prop) (i : B -> A) (x' : B) (x : A) : (term331 A B t i x' x) = (term455 A B t i x' x).
Proof. exact (MK_COMB (@lem7193139) (@lem7193138 A B t i x' x)). Qed.
Lemma lem7193141 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term334 A B t i x x' y) = (term456 A B t i x x' y).
Proof. exact (MK_COMB (@lem7193140 A B t i x' x) (@lem7193120 B x' y)). Qed.
Lemma lem7193142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7193143 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (x' : B) (y : B) : (term457 A B t i x x' y) = (term458 A B t i x x' y).
Proof. exact (MK_COMB (@lem7193142) (@lem7193141 A B t i x x' y)). Qed.
Lemma lem7193144 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term407 A B t i x y g x') = (term459 A B t i x y g x').
Proof. exact (MK_COMB (@lem7193143 A B t i x x' y) (@lem7193113 B g x')). Qed.
Lemma lem7193153 {A B : Type'} (i : B -> A) (x' : B) (x : A) : (term460 A B i x' x) = (term460 A B i x' x).
Proof. exact (eq_refl (term460 A B i x' x)). Qed.
Lemma lem7193154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7193159 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7193160 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7193159 B Prop f x). Qed.
Lemma lem7193162 {B : Type'} (t : B -> Prop) (x' : B) : (t x') = (@I (B -> Prop) t x').
Proof. exact (@lem7193160 B t x'). Qed.
Lemma lem7193163 {B : Type'} (t : B -> Prop) (x' : B) : (term439 B t x') = (term440 B t x').
Proof. exact (MK_COMB (@lem7193154) (@lem7193162 B t x')). Qed.
Lemma lem7193164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7193165 {B : Type'} (t : B -> Prop) (x' : B) : (term441 B t x') = (term442 B t x').
Proof. exact (MK_COMB (@lem7193164) (@lem7193163 B t x')). Qed.
Lemma lem7193166 {A B : Type'} (t : B -> Prop) (i : B -> A) (x' : B) (x : A) : (term392 A B t i x' x) = (term461 A B t i x' x).
Proof. exact (MK_COMB (@lem7193165 B t x') (@lem7193153 A B i x' x)). Qed.
Lemma lem7193173 {B : Type'} (x' : B) (y : B) : (term393 B x' y) = (term393 B x' y).
Proof. exact (eq_refl (term393 B x' y)). Qed.
Lemma lem7193174 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) : (term395 A B y t i x' x) = (term462 A B y t i x' x).
Proof. exact (MK_COMB (@lem7193173 B x' y) (@lem7193166 A B t i x' x)). Qed.
Lemma lem7193175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7193176 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) : (term433 A B y t i x' x) = (term463 A B y t i x' x).
Proof. exact (MK_COMB (@lem7193175) (@lem7193174 A B y t i x' x)). Qed.
Lemma lem7193177 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) : (term435 A B t i x y g x') = (term464 A B t i x y g x').
Proof. exact (MK_COMB (@lem7193176 A B y t i x' x) (@lem7193144 A B t i x y g x')). Qed.
Lemma lem7193178 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term435 A B t i x y g x') : term464 A B t i x y g x'.
Proof. exact (EQ_MP (@lem7193177 A B t i x y g x') (@lem7193016 A B t i x y g x' h1)). Qed.
Lemma lem7193179 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term451 A B i y x g t s.
Proof. exact (proj2 (@lem7193100 A B f i y x g t s h1)). Qed.
Lemma lem7193181 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term450 A B y x g t s.
Proof. exact (proj2 (@lem7193179 A B f i y x g t s h1)). Qed.
Lemma lem7193183 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term449 A B x g t s.
Proof. exact (proj2 (@lem7193181 A B f i y x g t s h1)). Qed.
Lemma lem7193185 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term447 A B g t s.
Proof. exact (proj2 (@lem7193183 A B f i y x g t s h1)). Qed.
Lemma lem7193188 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term445 B t g.
Proof. exact (proj1 (@lem7193185 A B f i y x g t s h1)). Qed.
Lemma lem7193191 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : term462 A B y t i x' x.
Proof. exact (h1). Qed.
Lemma lem7193192 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term459 A B t i x y g x'.
Proof. exact (h1). Qed.
Lemma lem7193193 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : term461 A B t i x' x.
Proof. exact (proj2 (@lem7193191 A B y t i x' x h1)). Qed.
Lemma lem7193198 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term456 A B t i x x' y.
Proof. exact (proj1 (@lem7193192 A B t i x y g x' h1)). Qed.
Lemma lem7193200 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term454 A B t i x' x.
Proof. exact (proj1 (@lem7193198 A B t i x y g x' h1)). Qed.
Lemma lem7193247 {B : Type'} (t : B -> Prop) (x' : B) (h1 : term440 B t x') : term440 B t x'.
Proof. exact (h1). Qed.
Lemma lem7193292 {A B : Type'} (i : B -> A) (x' : B) (x : A) (h1 : term460 A B i x' x) : term460 A B i x' x.
Proof. exact (h1). Qed.
Lemma lem7193316 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term443 B t g y) = (term443 B t g y).
Proof. exact (eq_refl (term443 B t g y)). Qed.
Lemma lem7193317 {B : Type'} (t : B -> Prop) (g : B -> real) : (term444 B t g) = (term444 B t g).
Proof. exact (fun_ext (fun y : B => @lem7193316 B t g y)). Qed.
Lemma lem7193318 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7193320 {B : Type'} (t : B -> Prop) (g : B -> real) : (term445 B t g) = (term445 B t g).
Proof. exact (MK_COMB (@lem7193318 B) (@lem7193317 B t g)). Qed.
Lemma lem7193321 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term445 B t g.
Proof. exact (EQ_MP (@lem7193320 B t g) (@lem7193188 A B f i y x g t s h1)). Qed.
Lemma lem7193352 {A B : Type'} (_96295 : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term465 B t g _96295.
Proof. exact (@lem7193321 A B f i y x g t s h1 _96295). Qed.
Lemma lem7193353 {B : Type'} (t : B -> Prop) (g : B -> real) (_96295 : B) : (term465 B t g _96295) = (term443 B t g _96295).
Proof. exact (eq_refl (term465 B t g _96295)). Qed.
Lemma lem7193374 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : x' = y.
Proof. exact (proj1 (@lem7193191 A B y t i x' x h1)). Qed.
Lemma lem7193376 {B : Type'} (t : B -> Prop) (x' : B) (h1 : term440 B t x') : term440 B t x'.
Proof. exact (h1). Qed.
Lemma lem7193396 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : x' = y.
Proof. exact (proj1 (@lem7193191 A B y t i x' x h1)). Qed.
Lemma lem7193398 {A B : Type'} (i : B -> A) (x' : B) (x : A) (h1 : term460 A B i x' x) : term460 A B i x' x.
Proof. exact (h1). Qed.
Lemma lem7193537 {B : Type'} (t : B -> Prop) : (term466 B t) = (term466 B t).
Proof. exact (eq_refl (term466 B t)). Qed.
Lemma lem7193538 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : (term467 B t x') = (term467 B t y).
Proof. exact (MK_COMB (@lem7193537 B t) (@lem7193374 A B y t i x' x h1)). Qed.
Lemma lem7193539 {B : Type'} (t : B -> Prop) (y : B) : (term467 B t y) = (term440 B t y).
Proof. exact (eq_refl (term467 B t y)). Qed.
Lemma lem7193540 {B : Type'} (t : B -> Prop) (x' : B) : (term468 B t x') = (term468 B t x').
Proof. exact (eq_refl (term468 B t x')). Qed.
Lemma lem7193541 {B : Type'} (x' : B) (t : B -> Prop) (y : B) : ((term467 B t x') = (term467 B t y)) = ((term467 B t x') = (term440 B t y)).
Proof. exact (MK_COMB (@lem7193540 B t x') (@lem7193539 B t y)). Qed.
Lemma lem7193542 {B : Type'} (t : B -> Prop) (x' : B) : (term467 B t x') = (term440 B t x').
Proof. exact (eq_refl (term467 B t x')). Qed.
Lemma lem7193543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7193544 {B : Type'} (t : B -> Prop) (x' : B) : (term468 B t x') = (term469 B t x').
Proof. exact (MK_COMB (@lem7193543) (@lem7193542 B t x')). Qed.
Lemma lem7193545 {B : Type'} (t : B -> Prop) (y : B) : (term440 B t y) = (term440 B t y).
Proof. exact (eq_refl (term440 B t y)). Qed.
Lemma lem7193546 {B : Type'} (x' : B) (t : B -> Prop) (y : B) : ((term467 B t x') = (term440 B t y)) = ((term440 B t x') = (term440 B t y)).
Proof. exact (MK_COMB (@lem7193544 B t x') (@lem7193545 B t y)). Qed.
Lemma lem7193547 {B : Type'} (x' : B) (t : B -> Prop) (y : B) : ((term467 B t x') = (term467 B t y)) = ((term440 B t x') = (term440 B t y)).
Proof. exact (TRANS (@lem7193541 B x' t y) (@lem7193546 B x' t y)). Qed.
Lemma lem7193548 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : (term440 B t x') = (term440 B t y).
Proof. exact (EQ_MP (@lem7193547 B x' t y) (@lem7193538 A B y t i x' x h1)). Qed.
Lemma lem7193660 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) : term440 B t y.
Proof. exact (EQ_MP (@lem7193548 A B y t i x' x h2) (@lem7193376 B t x' h1)). Qed.
Lemma lem7193702 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : (i y) = x.
Proof. exact (proj1 (@lem7193179 A B f i y x g t s h1)). Qed.
Lemma lem7193773 {A B : Type'} (i : B -> A) (x : A) : (term470 A B i x) = (term470 A B i x).
Proof. exact (eq_refl (term470 A B i x)). Qed.
Lemma lem7193774 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : (term471 A B i x x') = (term471 A B i x y).
Proof. exact (MK_COMB (@lem7193773 A B i x) (@lem7193396 A B y t i x' x h1)). Qed.
Lemma lem7193775 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term471 A B i x y) = (term460 A B i y x).
Proof. exact (eq_refl (term471 A B i x y)). Qed.
Lemma lem7193776 {A B : Type'} (i : B -> A) (x : A) (x' : B) : (term472 A B i x x') = (term472 A B i x x').
Proof. exact (eq_refl (term472 A B i x x')). Qed.
Lemma lem7193777 {A B : Type'} (x' : B) (i : B -> A) (y : B) (x : A) : ((term471 A B i x x') = (term471 A B i x y)) = ((term471 A B i x x') = (term460 A B i y x)).
Proof. exact (MK_COMB (@lem7193776 A B i x x') (@lem7193775 A B i y x)). Qed.
Lemma lem7193778 {A B : Type'} (i : B -> A) (x' : B) (x : A) : (term471 A B i x x') = (term460 A B i x' x).
Proof. exact (eq_refl (term471 A B i x x')). Qed.
Lemma lem7193779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7193780 {A B : Type'} (i : B -> A) (x' : B) (x : A) : (term472 A B i x x') = (term473 A B i x' x).
Proof. exact (MK_COMB (@lem7193779) (@lem7193778 A B i x' x)). Qed.
Lemma lem7193781 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term460 A B i y x) = (term460 A B i y x).
Proof. exact (eq_refl (term460 A B i y x)). Qed.
Lemma lem7193782 {A B : Type'} (x' : B) (i : B -> A) (y : B) (x : A) : ((term471 A B i x x') = (term460 A B i y x)) = ((term460 A B i x' x) = (term460 A B i y x)).
Proof. exact (MK_COMB (@lem7193780 A B i x' x) (@lem7193781 A B i y x)). Qed.
Lemma lem7193783 {A B : Type'} (x' : B) (i : B -> A) (y : B) (x : A) : ((term471 A B i x x') = (term471 A B i x y)) = ((term460 A B i x' x) = (term460 A B i y x)).
Proof. exact (TRANS (@lem7193777 A B x' i y x) (@lem7193782 A B x' i y x)). Qed.
Lemma lem7193784 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term462 A B y t i x' x) : (term460 A B i x' x) = (term460 A B i y x).
Proof. exact (EQ_MP (@lem7193783 A B x' i y x) (@lem7193774 A B y t i x' x h1)). Qed.
Lemma lem7193785 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) : term460 A B i y x.
Proof. exact (EQ_MP (@lem7193784 A B y t i x' x h2) (@lem7193398 A B i x' x h1)). Qed.
Lemma lem7193786 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : x = (i y).
Proof. exact (SYM (@lem7193702 A B f i y x g t s h1)). Qed.
Lemma lem7193883 {A B : Type'} (i : B -> A) (y : B) : (term474 A B i y) = (term474 A B i y).
Proof. exact (eq_refl (term474 A B i y)). Qed.
Lemma lem7193884 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : (term475 A B i y x) = (term476 A B i y).
Proof. exact (MK_COMB (@lem7193883 A B i y) (@lem7193786 A B f i y x g t s h1)). Qed.
Lemma lem7193885 {A B : Type'} (i : B -> A) (y : B) : (term476 A B i y) = (term477 A B i y).
Proof. exact (eq_refl (term476 A B i y)). Qed.
Lemma lem7193886 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term478 A B i y x) = (term478 A B i y x).
Proof. exact (eq_refl (term478 A B i y x)). Qed.
Lemma lem7193887 {A B : Type'} (x : A) (i : B -> A) (y : B) : ((term475 A B i y x) = (term476 A B i y)) = ((term475 A B i y x) = (term477 A B i y)).
Proof. exact (MK_COMB (@lem7193886 A B i y x) (@lem7193885 A B i y)). Qed.
Lemma lem7193888 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term475 A B i y x) = (term460 A B i y x).
Proof. exact (eq_refl (term475 A B i y x)). Qed.
Lemma lem7193889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7193890 {A B : Type'} (i : B -> A) (y : B) (x : A) : (term478 A B i y x) = (term473 A B i y x).
Proof. exact (MK_COMB (@lem7193889) (@lem7193888 A B i y x)). Qed.
Lemma lem7193891 {A B : Type'} (i : B -> A) (y : B) : (term477 A B i y) = (term477 A B i y).
Proof. exact (eq_refl (term477 A B i y)). Qed.
Lemma lem7193892 {A B : Type'} (x : A) (i : B -> A) (y : B) : ((term475 A B i y x) = (term477 A B i y)) = ((term460 A B i y x) = (term477 A B i y)).
Proof. exact (MK_COMB (@lem7193890 A B i y x) (@lem7193891 A B i y)). Qed.
Lemma lem7193893 {A B : Type'} (x : A) (i : B -> A) (y : B) : ((term475 A B i y x) = (term476 A B i y)) = ((term460 A B i y x) = (term477 A B i y)).
Proof. exact (TRANS (@lem7193887 A B x i y) (@lem7193892 A B x i y)). Qed.
Lemma lem7193894 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : (term460 A B i y x) = (term477 A B i y).
Proof. exact (EQ_MP (@lem7193893 A B x i y) (@lem7193884 A B f i y x g t s h1)). Qed.
Lemma lem7193895 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : term477 A B i y.
Proof. exact (EQ_MP (@lem7193894 A B f i y x g t s h3) (@lem7193785 A B y t i x' x h1 h2)). Qed.
Lemma lem7193977 {A B : Type'} (_96295 : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term443 B t g _96295.
Proof. exact (EQ_MP (@lem7193353 B t g _96295) (@lem7193352 A B _96295 f i y x g t s h1)). Qed.
Lemma lem7194019 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term453 B g x'.
Proof. exact (proj2 (@lem7193192 A B t i x y g x' h1)). Qed.
Lemma lem7194049 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : @I (B -> Prop) t y.
Proof. exact (proj1 (@lem7193181 A B f i y x g t s h1)). Qed.
Lemma lem7194050 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term479 B t y.
Proof. exact (fun h0 : term440 B t y => @lem7194049 A B f i y x g t s h1). Qed.
Lemma lem7194052 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194053 {B : Type'} (t : B -> Prop) (y : B) : (term479 B t y) = (@I (B -> Prop) t y).
Proof. exact (@lem7194052 (@I (B -> Prop) t y)). Qed.
Lemma lem7194054 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : @I (B -> Prop) t y.
Proof. exact (EQ_MP (@lem7194053 B t y) (@lem7194050 A B f i y x g t s h1)). Qed.
Lemma lem7194057 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7194059 {B : Type'} (t : B -> Prop) (y : B) : (term440 B t y) = (term481 B t y).
Proof. exact (@lem7194057 (@I (B -> Prop) t y)). Qed.
Lemma lem7194062 {A B : Type'} (y : B) (t : B -> Prop) (i : B -> A) (x' : B) (x : A) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) : term481 B t y.
Proof. exact (EQ_MP (@lem7194059 B t y) (@lem7193660 A B y t i x' x h1 h2)). Qed.
Lemma lem7194065 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (@lem7194062 A B y t i x' x h1 h2 (@lem7194054 A B f i y x g t s h3)). Qed.
Lemma lem7194066 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : term482.
Proof. exact (fun h0 : ~ False => @lem7194065 A B x' f i y x g t s h1 h2 h3). Qed.
Lemma lem7194068 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194069 : term482 = False.
Proof. exact (@lem7194068 False). Qed.
Lemma lem7194205 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7194206 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7194205 A x). Qed.
Lemma lem7194207 {A B : Type'} (i : B -> A) (y : B) : (i y) = (i y).
Proof. exact (@lem7194206 A (i y)). Qed.
Lemma lem7194208 {A B : Type'} (i : B -> A) (y : B) : term483 A B i y.
Proof. exact (fun h0 : term477 A B i y => @lem7194207 A B i y). Qed.
Lemma lem7194210 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194211 {A B : Type'} (i : B -> A) (y : B) : (term483 A B i y) = ((i y) = (i y)).
Proof. exact (@lem7194210 ((i y) = (i y))). Qed.
Lemma lem7194212 {A B : Type'} (i : B -> A) (y : B) : (i y) = (i y).
Proof. exact (EQ_MP (@lem7194211 A B i y) (@lem7194208 A B i y)). Qed.
Lemma lem7194215 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7194217 {A B : Type'} (i : B -> A) (y : B) : (term477 A B i y) = (term484 A B i y).
Proof. exact (@lem7194215 ((i y) = (i y))). Qed.
Lemma lem7194220 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : term484 A B i y.
Proof. exact (EQ_MP (@lem7194217 A B i y) (@lem7193895 A B x' f i y x g t s h1 h2 h3)). Qed.
Lemma lem7194223 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (@lem7194220 A B x' f i y x g t s h1 h2 h3 (@lem7194212 A B i y)). Qed.
Lemma lem7194224 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : term482.
Proof. exact (fun h0 : ~ False => @lem7194223 A B x' f i y x g t s h1 h2 h3). Qed.
Lemma lem7194226 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194227 : term482 = False.
Proof. exact (@lem7194226 False). Qed.
Lemma lem7194363 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : @I (B -> Prop) t x'.
Proof. exact (proj1 (@lem7193200 A B t i x y g x' h1)). Qed.
Lemma lem7194364 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term479 B t x'.
Proof. exact (fun h0 : term440 B t x' => @lem7194363 A B t i x y g x' h1). Qed.
Lemma lem7194366 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194367 {B : Type'} (t : B -> Prop) (x' : B) : (term479 B t x') = (@I (B -> Prop) t x').
Proof. exact (@lem7194366 (@I (B -> Prop) t x')). Qed.
Lemma lem7194368 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : @I (B -> Prop) t x'.
Proof. exact (EQ_MP (@lem7194367 B t x') (@lem7194364 A B t i x y g x' h1)). Qed.
Lemma lem7194374 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7194375 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : (term443 B t g _96295) = (term485 B g t _96295).
Proof. exact (@lem7194374 (term235 B g _96295) (term440 B t _96295)). Qed.
Lemma lem7194381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7194382 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : (term486 B t g _96295) = (term487 B g t _96295).
Proof. exact (MK_COMB (@lem7194381) (@lem7194375 B g t _96295)). Qed.
Lemma lem7194388 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : (term485 B g t _96295) = (term485 B g t _96295).
Proof. exact (eq_refl (term485 B g t _96295)). Qed.
Lemma lem7194389 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : ((term443 B t g _96295) = (term485 B g t _96295)) = ((term485 B g t _96295) = (term485 B g t _96295)).
Proof. exact (MK_COMB (@lem7194382 B g t _96295) (@lem7194388 B g t _96295)). Qed.
Lemma lem7194391 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7194392 (x : Prop) : (x = x) = True.
Proof. exact (@lem7194391 Prop x). Qed.
Lemma lem7194393 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : ((term485 B g t _96295) = (term485 B g t _96295)) = True.
Proof. exact (@lem7194392 (term485 B g t _96295)). Qed.
Lemma lem7194394 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : ((term443 B t g _96295) = (term485 B g t _96295)) = True.
Proof. exact (TRANS (@lem7194389 B g t _96295) (@lem7194393 B g t _96295)). Qed.
Lemma lem7194395 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : True = ((term443 B t g _96295) = (term485 B g t _96295)).
Proof. exact (SYM (@lem7194394 B g t _96295)). Qed.
Lemma lem7194396 {B : Type'} (g : B -> real) (t : B -> Prop) (_96295 : B) : (term443 B t g _96295) = (term485 B g t _96295).
Proof. exact (EQ_MP (@lem7194395 B g t _96295) (@lem0)). Qed.
Lemma lem7194397 {A B : Type'} (_96295 : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term485 B g t _96295.
Proof. exact (EQ_MP (@lem7194396 B g t _96295) (@lem7193977 A B _96295 f i y x g t s h1)). Qed.
Lemma lem7194399 (b : Prop) (a : Prop) : (a \/ b) = (term488 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7194400 {B : Type'} (t : B -> Prop) (g : B -> real) (_96295 : B) : (term485 B g t _96295) = (term489 B t g _96295).
Proof. exact (@lem7194399 (term440 B t _96295) (term235 B g _96295)). Qed.
Lemma lem7194402 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7194403 {B : Type'} (t : B -> Prop) (_96295 : B) : (term490 B t _96295) = (@I (B -> Prop) t _96295).
Proof. exact (@lem7194402 (@I (B -> Prop) t _96295)). Qed.
Lemma lem7194404 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194405 {B : Type'} (t : B -> Prop) (_96295 : B) : (term491 B t _96295) = (term492 B t _96295).
Proof. exact (MK_COMB (@lem7194404) (@lem7194403 B t _96295)). Qed.
Lemma lem7194406 {B : Type'} (g : B -> real) (_96295 : B) : (term235 B g _96295) = (term235 B g _96295).
Proof. exact (eq_refl (term235 B g _96295)). Qed.
Lemma lem7194407 {B : Type'} (t : B -> Prop) (g : B -> real) (_96295 : B) : (term489 B t g _96295) = (term493 B t g _96295).
Proof. exact (MK_COMB (@lem7194405 B t _96295) (@lem7194406 B g _96295)). Qed.
Lemma lem7194408 {B : Type'} (t : B -> Prop) (g : B -> real) (_96295 : B) : (term485 B g t _96295) = (term493 B t g _96295).
Proof. exact (TRANS (@lem7194400 B t g _96295) (@lem7194407 B t g _96295)). Qed.
Lemma lem7194411 {A B : Type'} (_96295 : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term493 B t g _96295.
Proof. exact (EQ_MP (@lem7194408 B t g _96295) (@lem7194397 A B _96295 f i y x g t s h1)). Qed.
Lemma lem7194412 {A B : Type'} (_96295 : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term493 B t g _96295.
Proof. exact (@lem7194411 A B _96295 f i y x g t s h1). Qed.
Lemma lem7194413 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term493 B t g x'.
Proof. exact (@lem7194412 A B x' f i y x g t s h1). Qed.
Lemma lem7194416 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : term235 B g x'.
Proof. exact (@lem7194413 A B x' f i y x g t s h2 (@lem7194368 A B t i x y g x' h1)). Qed.
Lemma lem7194417 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : term494 B g x'.
Proof. exact (fun h0 : term453 B g x' => @lem7194416 A B x' f i y x g t s h1 h2). Qed.
Lemma lem7194419 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194420 {B : Type'} (g : B -> real) (x' : B) : (term494 B g x') = (term235 B g x').
Proof. exact (@lem7194419 (term235 B g x')). Qed.
Lemma lem7194421 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : term235 B g x'.
Proof. exact (EQ_MP (@lem7194420 B g x') (@lem7194417 A B x' f i y x g t s h1 h2)). Qed.
Lemma lem7194424 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7194426 {B : Type'} (g : B -> real) (x' : B) : (term453 B g x') = (term495 B g x').
Proof. exact (@lem7194424 (term235 B g x')). Qed.
Lemma lem7194429 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term459 A B t i x y g x') : term495 B g x'.
Proof. exact (EQ_MP (@lem7194426 B g x') (@lem7194019 A B t i x y g x' h1)). Qed.
Lemma lem7194432 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : False.
Proof. exact (@lem7194429 A B t i x y g x' h1 (@lem7194421 A B x' f i y x g t s h1 h2)). Qed.
Lemma lem7194433 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : term482.
Proof. exact (fun h0 : ~ False => @lem7194432 A B x' f i y x g t s h1 h2). Qed.
Lemma lem7194435 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7194436 : term482 = False.
Proof. exact (@lem7194435 False). Qed.
Lemma lem7194438 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term459 A B t i x y g x') (h2 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194436) (@lem7194433 A B x' f i y x g t s h1 h2)). Qed.
Lemma lem7194440 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194227) (@lem7194224 A B x' f i y x g t s h1 h2 h3)). Qed.
Lemma lem7194442 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194069) (@lem7194066 A B x' f i y x g t s h1 h2 h3)). Qed.
Lemma lem7194443 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term460 A B i x' x) = False.
Proof. exact (prop_ext (fun h4 : term460 A B i x' x => @lem7194440 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193398 A B i x' x h1)). Qed.
Lemma lem7194444 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194443 A B x' f i y x g t s h1 h2 h3) (@lem7193398 A B i x' x h1)). Qed.
Lemma lem7194445 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term440 B t x') = False.
Proof. exact (prop_ext (fun h4 : term440 B t x' => @lem7194442 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193376 B t x' h1)). Qed.
Lemma lem7194446 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194445 A B x' f i y x g t s h1 h2 h3) (@lem7193376 B t x' h1)). Qed.
Lemma lem7194447 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term460 A B i x' x) = False.
Proof. exact (prop_ext (fun h4 : term460 A B i x' x => @lem7194444 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193292 A B i x' x h1)). Qed.
Lemma lem7194448 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194447 A B x' f i y x g t s h1 h2 h3) (@lem7193292 A B i x' x h1)). Qed.
Lemma lem7194449 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term440 B t x') = False.
Proof. exact (prop_ext (fun h4 : term440 B t x' => @lem7194446 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193247 B t x' h1)). Qed.
Lemma lem7194450 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194449 A B x' f i y x g t s h1 h2 h3) (@lem7193247 B t x' h1)). Qed.
Lemma lem7194451 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term460 A B i x' x) = False.
Proof. exact (prop_ext (fun h4 : term460 A B i x' x => @lem7194448 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193292 A B i x' x h1)). Qed.
Lemma lem7194452 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term460 A B i x' x) (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194451 A B x' f i y x g t s h1 h2 h3) (@lem7193292 A B i x' x h1)). Qed.
Lemma lem7194453 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : (term440 B t x') = False.
Proof. exact (prop_ext (fun h4 : term440 B t x' => @lem7194450 A B x' f i y x g t s h1 h2 h3) (fun h4 : False => @lem7193247 B t x' h1)). Qed.
Lemma lem7194454 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term440 B t x') (h2 : term462 A B y t i x' x) (h3 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194453 A B x' f i y x g t s h1 h2 h3) (@lem7193247 B t x' h1)). Qed.
Lemma lem7194455 {A B : Type'} (x' : B) (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term462 A B y t i x' x) (h2 : term309 A B f i y x g t s) : False.
Proof. exact (or_elim (@lem7193193 A B y t i x' x h1) (fun h0 : term440 B t x' => @lem7194454 A B x' f i y x g t s h0 h1 h2) (fun h0 : term460 A B i x' x => @lem7194452 A B x' f i y x g t s h0 h1 h2)). Qed.
Lemma lem7194456 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (x' : B) (h1 : term309 A B f i y x g t s) (h2 : term435 A B t i x y g x') : False.
Proof. exact (or_elim (@lem7193178 A B t i x y g x' h2) (fun h0 : term462 A B y t i x' x => @lem7194455 A B x' f i y x g t s h0 h1) (fun h0 : term459 A B t i x y g x' => @lem7194438 A B x' f i y x g t s h0 h1)). Qed.
Lemma lem7194457 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term381 A B t i x y g) (h2 : term309 A B f i y x g t s) : False.
Proof. exact (ex_elim (@lem7193015 A B t i x y g h1) (fun x' : B => fun h0 : term437 A B t i x y g x' => @lem7194456 A B f s t i x y g x' h2 h0)). Qed.
Lemma lem7194458 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term381 A B t i x y g) (h2 : term309 A B f i y x g t s) : (term381 A B t i x y g) = False.
Proof. exact (prop_ext (fun h3 : term381 A B t i x y g => @lem7194457 A B f i y x g t s h1 h2) (fun h3 : False => @lem7192748 A B t i x y g h1)). Qed.
Lemma lem7194459 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term381 A B t i x y g) (h2 : term309 A B f i y x g t s) : False.
Proof. exact (EQ_MP (@lem7194458 A B f i y x g t s h1 h2) (@lem7192748 A B t i x y g h1)). Qed.
Lemma lem7194460 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term380 A B t i x y g.
Proof. exact (fun h0 : term381 A B t i x y g => @lem7194459 A B f i y x g t s h0 h1). Qed.
Lemma lem7194461 {A B : Type'} (f : A -> real) (i : B -> A) (y : B) (x : A) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term309 A B f i y x g t s) : term342 A B t i x y g.
Proof. exact (EQ_MP (@lem7192747 A B t i x y g) (@lem7194460 A B f i y x g t s h1)). Qed.
Lemma lem7194462 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term343 A B f s t i x y g.
Proof. exact (fun h0 : term309 A B f i y x g t s => @lem7194461 A B f i y x g t s h0). Qed.
Lemma lem7194467 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term355 A B s t i x y g.
Proof. exact (fun f : A -> real => @lem7194462 A B f s t i x y g). Qed.
Lemma lem7194472 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term359 A B t i x y g.
Proof. exact (fun s : A -> Prop => @lem7194467 A B s t i x y g). Qed.
Lemma lem7194477 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : term363 A B i x y g.
Proof. exact (fun t : B -> Prop => @lem7194472 A B t i x y g). Qed.
Lemma lem7194482 {A B : Type'} (x : A) (y : B) (g : B -> real) : term367 A B x y g.
Proof. exact (fun i : B -> A => @lem7194477 A B i x y g). Qed.
Lemma lem7194487 {A B : Type'} (y : B) (g : B -> real) : term371 A B y g.
Proof. exact (fun x : A => @lem7194482 A B x y g). Qed.
Lemma lem7194492 {A B : Type'} (g : B -> real) : term375 A B g.
Proof. exact (fun y : B => @lem7194487 A B y g). Qed.
Lemma lem7194497 {A B : Type'} : term379 A B.
Proof. exact (fun g : B -> real => @lem7194492 A B g). Qed.
Lemma lem7194498 {A B : Type'} : term378 A B.
Proof. exact (EQ_MP (@lem7192742 A B) (@lem7194497 A B)). Qed.
Lemma lem7194499 {A B : Type'} (g : B -> real) : term496 A B g.
Proof. exact (@lem7194498 A B g). Qed.
Lemma lem7194500 {A B : Type'} (g : B -> real) : (term496 A B g) = (term374 A B g).
Proof. exact (eq_refl (term496 A B g)). Qed.
Lemma lem7194501 {A B : Type'} (g : B -> real) : term374 A B g.
Proof. exact (EQ_MP (@lem7194500 A B g) (@lem7194499 A B g)). Qed.
Lemma lem7194502 {A B : Type'} (g : B -> real) (y : B) : term497 A B g y.
Proof. exact (@lem7194501 A B g y). Qed.
Lemma lem7194503 {A B : Type'} (y : B) (g : B -> real) : (term497 A B g y) = (term370 A B y g).
Proof. exact (eq_refl (term497 A B g y)). Qed.
Lemma lem7194504 {A B : Type'} (y : B) (g : B -> real) : term370 A B y g.
Proof. exact (EQ_MP (@lem7194503 A B y g) (@lem7194502 A B g y)). Qed.
Lemma lem7194505 {A B : Type'} (y : B) (g : B -> real) (x : A) : term498 A B y g x.
Proof. exact (@lem7194504 A B y g x). Qed.
Lemma lem7194506 {A B : Type'} (x : A) (y : B) (g : B -> real) : (term498 A B y g x) = (term366 A B x y g).
Proof. exact (eq_refl (term498 A B y g x)). Qed.
Lemma lem7194507 {A B : Type'} (x : A) (y : B) (g : B -> real) : term366 A B x y g.
Proof. exact (EQ_MP (@lem7194506 A B x y g) (@lem7194505 A B y g x)). Qed.
Lemma lem7194508 {A B : Type'} (x : A) (y : B) (g : B -> real) (i : B -> A) : term499 A B x y g i.
Proof. exact (@lem7194507 A B x y g i). Qed.
Lemma lem7194509 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : (term499 A B x y g i) = (term362 A B i x y g).
Proof. exact (eq_refl (term499 A B x y g i)). Qed.
Lemma lem7194510 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) : term362 A B i x y g.
Proof. exact (EQ_MP (@lem7194509 A B i x y g) (@lem7194508 A B x y g i)). Qed.
Lemma lem7194511 {A B : Type'} (i : B -> A) (x : A) (y : B) (g : B -> real) (t : B -> Prop) : term500 A B i x y g t.
Proof. exact (@lem7194510 A B i x y g t). Qed.
Lemma lem7194512 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term500 A B i x y g t) = (term358 A B t i x y g).
Proof. exact (eq_refl (term500 A B i x y g t)). Qed.
Lemma lem7194513 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term358 A B t i x y g.
Proof. exact (EQ_MP (@lem7194512 A B t i x y g) (@lem7194511 A B i x y g t)). Qed.
Lemma lem7194514 {A B : Type'} (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (s : A -> Prop) : term501 A B t i x y g s.
Proof. exact (@lem7194513 A B t i x y g s). Qed.
Lemma lem7194515 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term501 A B t i x y g s) = (term354 A B s t i x y g).
Proof. exact (eq_refl (term501 A B t i x y g s)). Qed.
Lemma lem7194516 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term354 A B s t i x y g.
Proof. exact (EQ_MP (@lem7194515 A B s t i x y g) (@lem7194514 A B t i x y g s)). Qed.
Lemma lem7194517 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (f : A -> real) : term502 A B s t i x y g f.
Proof. exact (@lem7194516 A B s t i x y g f). Qed.
Lemma lem7194518 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : (term502 A B s t i x y g f) = (term345 A B f s t i x y g).
Proof. exact (eq_refl (term502 A B s t i x y g f)). Qed.
Lemma lem7194519 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term345 A B f s t i x y g.
Proof. exact (EQ_MP (@lem7194518 A B f s t i x y g) (@lem7194517 A B s t i x y g f)). Qed.
Lemma lem7194521 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term345 A B f s t i x y g.
Proof. exact (@lem7192433 A B f s t i x y g (@lem7194519 A B f s t i x y g)). Qed.
Lemma lem7194522 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term346 A B f s t i x y g) : False.
Proof. exact (@lem7194521 A B f s t i x y g (@lem7192417 A B f s t i x y g h1)). Qed.
Lemma lem7194523 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term346 A B f s t i x y g) : (term346 A B f s t i x y g) = False.
Proof. exact (prop_ext (fun h2 : term346 A B f s t i x y g => @lem7194522 A B f s t i x y g h1) (fun h2 : False => @lem7192417 A B f s t i x y g h1)). Qed.
Lemma lem7194524 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) (h1 : term346 A B f s t i x y g) : False.
Proof. exact (EQ_MP (@lem7194523 A B f s t i x y g h1) (@lem7192417 A B f s t i x y g h1)). Qed.
Lemma lem7194525 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term345 A B f s t i x y g.
Proof. exact (fun h0 : term346 A B f s t i x y g => @lem7194524 A B f s t i x y g h0). Qed.
Lemma lem7194526 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term343 A B f s t i x y g.
Proof. exact (EQ_MP (@lem7192416 A B f s t i x y g) (@lem7194525 A B f s t i x y g)). Qed.
Lemma lem7194527 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term294 A B f s t i x y g.
Proof. exact (EQ_MP (@lem7192412 A B f s t i x y g) (@lem7194526 A B f s t i x y g)). Qed.
Lemma lem7194528 {A B : Type'} (f : A -> real) (s : A -> Prop) (t : B -> Prop) (i : B -> A) (x : A) (y : B) (g : B -> real) : term293 A B f s t i x y g.
Proof. exact (EQ_MP (@lem7192161 A B f s t i x y g) (@lem7194527 A B f s t i x y g)). Qed.
Lemma lem7194529 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term222 A B t i x y g.
Proof. exact (@lem7194528 A B f s t i x y g (@lem7192088 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7194540 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term279 A B t s.
Proof. exact (conj (@lem7190847 B t h2) (@lem7190845 A s h1)). Qed.
Lemma lem7194541 {A B : Type'} (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) : term280 A B g t s.
Proof. exact (conj (@lem7190849 B t g h1) (@lem7194540 A B s t h2 h3)). Qed.
Lemma lem7194542 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term503 A B i f g t s.
Proof. exact (conj (@lem7190848 A B s t i f g h1) (@lem7194541 A B g s t h2 h3 h4)). Qed.
Lemma lem7194576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term285 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem7194577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term285 A s t).
Proof. exact (@lem7194576 A s t). Qed.
Lemma lem7194578 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term278 A B s i t) = (term504 A B s i t).
Proof. exact (@lem7194577 A s (@IMAGE B A i t)). Qed.
Lemma lem7194585 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term505 A B i f g t s) = (term505 A B i f g t s).
Proof. exact (eq_refl (term505 A B i f g t s)). Qed.
Lemma lem7194586 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term506 A B f g s i t) = (term507 A B f g s i t).
Proof. exact (MK_COMB (@lem7194585 A B i f g t s) (@lem7194578 A B s i t)). Qed.
Lemma lem7194589 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term507 A B f g s i t) = (term506 A B f g s i t).
Proof. exact (SYM (@lem7194586 A B f g s i t)). Qed.
Lemma lem7194601 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7194602 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7194601 A P x). Qed.
Lemma lem7194603 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7194602 A s x). Qed.
Lemma lem7194604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194605 {A : Type'} (s : A -> Prop) (x : A) : (term104 A x s) = (term296 A s x).
Proof. exact (MK_COMB (@lem7194604) (@lem7194603 A s x)). Qed.
Lemma lem7194613 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7194614 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7194613 B P x). Qed.
Lemma lem7194615 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7194614 B t y). Qed.
Lemma lem7194616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7194617 {B : Type'} (t : B -> Prop) (y : B) : (term202 B y t) = (term295 B t y).
Proof. exact (MK_COMB (@lem7194616) (@lem7194615 B t y)). Qed.
Lemma lem7194622 {A B : Type'} (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term143 A B i f x g y) = (term143 A B i f x g y).
Proof. exact (eq_refl (term143 A B i f x g y)). Qed.
Lemma lem7194623 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term130 A B t i f x g y) = (term508 A B t i f x g y).
Proof. exact (MK_COMB (@lem7194617 B t y) (@lem7194622 A B i f x g y)). Qed.
Lemma lem7194626 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term128 A B t i f x g) = (term509 A B t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7194623 A B t i f x g y)). Qed.
Lemma lem7194627 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7194628 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term120 A B t i f x g) = (term510 A B t i f x g).
Proof. exact (MK_COMB (@lem7194627 B) (@lem7194626 A B t i f x g)). Qed.
Lemma lem7194633 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term114 A B s t i f x g) = (term511 A B s t i f x g).
Proof. exact (MK_COMB (@lem7194605 A s x) (@lem7194628 A B t i f x g)). Qed.
Lemma lem7194636 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term512 A B s t i f g) = (term513 A B s t i f g).
Proof. exact (fun_ext (fun x : A => @lem7194633 A B s t i f x g)). Qed.
Lemma lem7194637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7194638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term82 A B s t i f g) = (term514 A B s t i f g).
Proof. exact (MK_COMB (@lem7194637 A) (@lem7194636 A B s t i f g)). Qed.
Lemma lem7194643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7194644 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term515 A B s t i f g) = (term516 A B s t i f g).
Proof. exact (MK_COMB (@lem7194643) (@lem7194638 A B s t i f g)). Qed.
Lemma lem7194654 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7194655 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7194654 B P x). Qed.
Lemma lem7194656 {B : Type'} (t : B -> Prop) (y : B) : (@IN B y t) = (t y).
Proof. exact (@lem7194655 B t y). Qed.
Lemma lem7194657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194658 {B : Type'} (t : B -> Prop) (y : B) : (term104 B y t) = (term296 B t y).
Proof. exact (MK_COMB (@lem7194657) (@lem7194656 B t y)). Qed.
Lemma lem7194659 {B : Type'} (g : B -> real) (y : B) : (term235 B g y) = (term235 B g y).
Proof. exact (eq_refl (term235 B g y)). Qed.
Lemma lem7194660 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term234 B t g y) = (term297 B t g y).
Proof. exact (MK_COMB (@lem7194658 B t y) (@lem7194659 B g y)). Qed.
Lemma lem7194663 {B : Type'} (t : B -> Prop) (g : B -> real) : (term298 B t g) = (term299 B t g).
Proof. exact (fun_ext (fun y : B => @lem7194660 B t g y)). Qed.
Lemma lem7194664 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7194665 {B : Type'} (t : B -> Prop) (g : B -> real) : (term83 B t g) = (term300 B t g).
Proof. exact (MK_COMB (@lem7194664 B) (@lem7194663 B t g)). Qed.
Lemma lem7194670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7194671 {B : Type'} (t : B -> Prop) (g : B -> real) : (term301 B t g) = (term302 B t g).
Proof. exact (MK_COMB (@lem7194670) (@lem7194665 B t g)). Qed.
Lemma lem7194674 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7194675 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term280 A B g t s) = (term303 A B g t s).
Proof. exact (MK_COMB (@lem7194671 B t g) (@lem7194674 A B t s)). Qed.
Lemma lem7194678 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term503 A B i f g t s) = (term517 A B i f g t s).
Proof. exact (MK_COMB (@lem7194644 A B s t i f g) (@lem7194675 A B g t s)). Qed.
Lemma lem7194681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194682 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term505 A B i f g t s) = (term518 A B i f g t s).
Proof. exact (MK_COMB (@lem7194681) (@lem7194678 A B i f g t s)). Qed.
Lemma lem7194690 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7194691 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7194690 A P x). Qed.
Lemma lem7194692 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7194691 A s x). Qed.
Lemma lem7194693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194694 {A : Type'} (s : A -> Prop) (x : A) : (term104 A x s) = (term296 A s x).
Proof. exact (MK_COMB (@lem7194693) (@lem7194692 A s x)). Qed.
Lemma lem7194696 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term519 A B y f s) = (term520 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem7194697 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term521 A B y f s) = (term522 A B y f s).
Proof. exact (@lem7194696 B A y f s). Qed.
Lemma lem7194698 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term521 A B x i t) = (term522 A B x i t).
Proof. exact (@lem7194697 A B x i t). Qed.
Lemma lem7194708 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7194709 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7194708 B P x). Qed.
Lemma lem7194710 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7194709 B t x). Qed.
Lemma lem7194711 {A B : Type'} (x : A) (i : B -> A) (x' : B) : (term523 A B x i x') = (term523 A B x i x').
Proof. exact (eq_refl (term523 A B x i x')). Qed.
Lemma lem7194712 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term524 A B x i x' t) = (term525 A B x i t x').
Proof. exact (MK_COMB (@lem7194711 A B x i x') (@lem7194710 B t x')). Qed.
Lemma lem7194715 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term526 A B x i t) = (term527 A B x i t).
Proof. exact (fun_ext (fun x' : B => @lem7194712 A B x i t x')). Qed.
Lemma lem7194716 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7194717 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term522 A B x i t) = (term528 A B x i t).
Proof. exact (MK_COMB (@lem7194716 B) (@lem7194715 A B x i t)). Qed.
Lemma lem7194722 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term521 A B x i t) = (term528 A B x i t).
Proof. exact (TRANS (@lem7194698 A B x i t) (@lem7194717 A B x i t)). Qed.
Lemma lem7194723 {A B : Type'} (s : A -> Prop) (x : A) (i : B -> A) (t : B -> Prop) : (term529 A B s x i t) = (term530 A B s x i t).
Proof. exact (MK_COMB (@lem7194694 A s x) (@lem7194722 A B x i t)). Qed.
Lemma lem7194726 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term531 A B s i t) = (term532 A B s i t).
Proof. exact (fun_ext (fun x : A => @lem7194723 A B s x i t)). Qed.
Lemma lem7194727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7194728 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term504 A B s i t) = (term533 A B s i t).
Proof. exact (MK_COMB (@lem7194727 A) (@lem7194726 A B s i t)). Qed.
Lemma lem7194733 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term507 A B f g s i t) = (term534 A B f g s i t).
Proof. exact (MK_COMB (@lem7194682 A B i f g t s) (@lem7194728 A B s i t)). Qed.
Lemma lem7194736 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term534 A B f g s i t) = (term507 A B f g s i t).
Proof. exact (SYM (@lem7194733 A B f g s i t)). Qed.
Lemma lem7194738 (p : Prop) : p = (term344 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7194739 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term534 A B f g s i t) = (term535 A B f g s i t).
Proof. exact (@lem7194738 (term534 A B f g s i t)). Qed.
Lemma lem7194740 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term535 A B f g s i t) = (term534 A B f g s i t).
Proof. exact (SYM (@lem7194739 A B f g s i t)). Qed.
Lemma lem7194741 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term536 A B f g s i t) : term536 A B f g s i t.
Proof. exact (h1). Qed.
Lemma lem7194744 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term535 A B f g s i t) : term535 A B f g s i t.
Proof. exact (h1). Qed.
Lemma lem7194745 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term537 A B f g s i t.
Proof. exact (fun h0 : term535 A B f g s i t => @lem7194744 A B f g s i t h0). Qed.
Lemma lem7194746 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term537 A B f g s i t) : term537 A B f g s i t.
Proof. exact (h1). Qed.
Lemma lem7194747 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term535 A B f g s i t) : term535 A B f g s i t.
Proof. exact (h1). Qed.
Lemma lem7194748 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term535 A B f g s i t) (h2 : term537 A B f g s i t) : term535 A B f g s i t.
Proof. exact (@lem7194746 A B f g s i t h2 (@lem7194747 A B f g s i t h1)). Qed.
Lemma lem7194749 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term535 A B f g s i t) : term538 A B f g s i t.
Proof. exact (fun h0 : term537 A B f g s i t => @lem7194748 A B f g s i t h1 h0). Qed.
Lemma lem7194750 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term537 A B f g s i t) : term537 A B f g s i t.
Proof. exact (h1). Qed.
Lemma lem7194751 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term535 A B f g s i t) (h2 : term537 A B f g s i t) : term535 A B f g s i t.
Proof. exact (@lem7194749 A B f g s i t h1 (@lem7194750 A B f g s i t h2)). Qed.
Lemma lem7194752 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term537 A B f g s i t) : term537 A B f g s i t.
Proof. exact (fun h0 : term535 A B f g s i t => @lem7194751 A B f g s i t h0 h1). Qed.
Lemma lem7194753 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term539 A B f g s i t.
Proof. exact (fun h0 : term537 A B f g s i t => @lem7194752 A B f g s i t h0). Qed.
Lemma lem7194756 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term537 A B f g s i t.
Proof. exact (@lem7194753 A B f g s i t (@lem7194745 A B f g s i t)). Qed.
Lemma lem7194757 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term537 A B f g s i t.
Proof. exact (@lem7194756 A B f g s i t). Qed.
Lemma lem7194779 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7194780 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term535 A B f g s i t) = (term540 A B f g s i t).
Proof. exact (@lem7194779 (term536 A B f g s i t)). Qed.
Lemma lem7194782 (t : Prop) : (term351 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7194783 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term540 A B f g s i t) = (term534 A B f g s i t).
Proof. exact (@lem7194782 (term534 A B f g s i t)). Qed.
Lemma lem7194786 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term535 A B f g s i t) = (term534 A B f g s i t).
Proof. exact (TRANS (@lem7194780 A B f g s i t) (@lem7194783 A B f g s i t)). Qed.
Lemma lem7194877 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term541 A B g s i t) = (term542 A B g s i t).
Proof. exact (fun_ext (fun f : A -> real => @lem7194786 A B f g s i t)). Qed.
Lemma lem7194878 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7194879 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term543 A B g s i t) = (term544 A B g s i t).
Proof. exact (MK_COMB (@lem7194878 A) (@lem7194877 A B g s i t)). Qed.
Lemma lem7194884 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term545 A B s i t) = (term546 A B s i t).
Proof. exact (fun_ext (fun g : B -> real => @lem7194879 A B g s i t)). Qed.
Lemma lem7194885 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7194886 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term547 A B s i t) = (term548 A B s i t).
Proof. exact (MK_COMB (@lem7194885 B) (@lem7194884 A B s i t)). Qed.
Lemma lem7194891 {A B : Type'} (i : B -> A) (t : B -> Prop) : (term549 A B i t) = (term550 A B i t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7194886 A B s i t)). Qed.
Lemma lem7194892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7194893 {A B : Type'} (i : B -> A) (t : B -> Prop) : (term551 A B i t) = (term552 A B i t).
Proof. exact (MK_COMB (@lem7194892 A) (@lem7194891 A B i t)). Qed.
Lemma lem7194898 {A B : Type'} (t : B -> Prop) : (term553 A B t) = (term554 A B t).
Proof. exact (fun_ext (fun i : B -> A => @lem7194893 A B i t)). Qed.
Lemma lem7194899 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7194900 {A B : Type'} (t : B -> Prop) : (term555 A B t) = (term556 A B t).
Proof. exact (MK_COMB (@lem7194899 A B) (@lem7194898 A B t)). Qed.
Lemma lem7194905 {A B : Type'} : (term557 A B) = (term558 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7194900 A B t)). Qed.
Lemma lem7194906 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7194915 {A B : Type'} : (term559 A B) = (term560 A B).
Proof. exact (MK_COMB (@lem7194906 B) (@lem7194905 A B)). Qed.
Lemma lem7194920 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term525 A B x i t x') = (term525 A B x i t x').
Proof. exact (eq_refl (term525 A B x i t x')). Qed.
Lemma lem7194921 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term527 A B x i t) = (term527 A B x i t).
Proof. exact (fun_ext (fun x' : B => @lem7194920 A B x i t x')). Qed.
Lemma lem7194922 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7194923 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term528 A B x i t) = (term528 A B x i t).
Proof. exact (MK_COMB (@lem7194922 B) (@lem7194921 A B x i t)). Qed.
Lemma lem7194926 {A : Type'} (s : A -> Prop) (x : A) : (term296 A s x) = (term296 A s x).
Proof. exact (eq_refl (term296 A s x)). Qed.
Lemma lem7194927 {A B : Type'} (s : A -> Prop) (x : A) (i : B -> A) (t : B -> Prop) : (term530 A B s x i t) = (term530 A B s x i t).
Proof. exact (MK_COMB (@lem7194926 A s x) (@lem7194923 A B x i t)). Qed.
Lemma lem7194928 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term532 A B s i t) = (term532 A B s i t).
Proof. exact (fun_ext (fun x : A => @lem7194927 A B s x i t)). Qed.
Lemma lem7194929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7194930 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term533 A B s i t) = (term533 A B s i t).
Proof. exact (MK_COMB (@lem7194929 A) (@lem7194928 A B s i t)). Qed.
Lemma lem7194935 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7194940 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term297 B t g y) = (term297 B t g y).
Proof. exact (eq_refl (term297 B t g y)). Qed.
Lemma lem7194941 {B : Type'} (t : B -> Prop) (g : B -> real) : (term299 B t g) = (term299 B t g).
Proof. exact (fun_ext (fun y : B => @lem7194940 B t g y)). Qed.
Lemma lem7194942 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7194943 {B : Type'} (t : B -> Prop) (g : B -> real) : (term300 B t g) = (term300 B t g).
Proof. exact (MK_COMB (@lem7194942 B) (@lem7194941 B t g)). Qed.
Lemma lem7194944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7194945 {B : Type'} (t : B -> Prop) (g : B -> real) : (term302 B t g) = (term302 B t g).
Proof. exact (MK_COMB (@lem7194944) (@lem7194943 B t g)). Qed.
Lemma lem7194946 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term303 A B g t s) = (term303 A B g t s).
Proof. exact (MK_COMB (@lem7194945 B t g) (@lem7194935 A B t s)). Qed.
Lemma lem7194955 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term508 A B t i f x g y) = (term508 A B t i f x g y).
Proof. exact (eq_refl (term508 A B t i f x g y)). Qed.
Lemma lem7194956 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term509 A B t i f x g) = (term509 A B t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7194955 A B t i f x g y)). Qed.
Lemma lem7194957 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7194958 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term510 A B t i f x g) = (term510 A B t i f x g).
Proof. exact (MK_COMB (@lem7194957 B) (@lem7194956 A B t i f x g)). Qed.
Lemma lem7194961 {A : Type'} (s : A -> Prop) (x : A) : (term296 A s x) = (term296 A s x).
Proof. exact (eq_refl (term296 A s x)). Qed.
Lemma lem7194962 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term511 A B s t i f x g) = (term511 A B s t i f x g).
Proof. exact (MK_COMB (@lem7194961 A s x) (@lem7194958 A B t i f x g)). Qed.
Lemma lem7194963 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term513 A B s t i f g) = (term513 A B s t i f g).
Proof. exact (fun_ext (fun x : A => @lem7194962 A B s t i f x g)). Qed.
Lemma lem7194964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7194965 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term514 A B s t i f g) = (term514 A B s t i f g).
Proof. exact (MK_COMB (@lem7194964 A) (@lem7194963 A B s t i f g)). Qed.
Lemma lem7194966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7194967 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term516 A B s t i f g) = (term516 A B s t i f g).
Proof. exact (MK_COMB (@lem7194966) (@lem7194965 A B s t i f g)). Qed.
Lemma lem7194968 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term517 A B i f g t s) = (term517 A B i f g t s).
Proof. exact (MK_COMB (@lem7194967 A B s t i f g) (@lem7194946 A B g t s)). Qed.
Lemma lem7194969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7194970 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term518 A B i f g t s) = (term518 A B i f g t s).
Proof. exact (MK_COMB (@lem7194969) (@lem7194968 A B i f g t s)). Qed.
Lemma lem7194971 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term534 A B f g s i t) = (term534 A B f g s i t).
Proof. exact (MK_COMB (@lem7194970 A B i f g t s) (@lem7194930 A B s i t)). Qed.
Lemma lem7194972 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term542 A B g s i t) = (term542 A B g s i t).
Proof. exact (fun_ext (fun f : A -> real => @lem7194971 A B f g s i t)). Qed.
Lemma lem7194973 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7194974 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term544 A B g s i t) = (term544 A B g s i t).
Proof. exact (MK_COMB (@lem7194973 A) (@lem7194972 A B g s i t)). Qed.
Lemma lem7194975 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term546 A B s i t) = (term546 A B s i t).
Proof. exact (fun_ext (fun g : B -> real => @lem7194974 A B g s i t)). Qed.
Lemma lem7194976 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7194977 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term548 A B s i t) = (term548 A B s i t).
Proof. exact (MK_COMB (@lem7194976 B) (@lem7194975 A B s i t)). Qed.
Lemma lem7194978 {A B : Type'} (i : B -> A) (t : B -> Prop) : (term550 A B i t) = (term550 A B i t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7194977 A B s i t)). Qed.
Lemma lem7194979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7194980 {A B : Type'} (i : B -> A) (t : B -> Prop) : (term552 A B i t) = (term552 A B i t).
Proof. exact (MK_COMB (@lem7194979 A) (@lem7194978 A B i t)). Qed.
Lemma lem7194981 {A B : Type'} (t : B -> Prop) : (term554 A B t) = (term554 A B t).
Proof. exact (fun_ext (fun i : B -> A => @lem7194980 A B i t)). Qed.
Lemma lem7194982 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7194983 {A B : Type'} (t : B -> Prop) : (term556 A B t) = (term556 A B t).
Proof. exact (MK_COMB (@lem7194982 A B) (@lem7194981 A B t)). Qed.
Lemma lem7194984 {A B : Type'} : (term558 A B) = (term558 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7194983 A B t)). Qed.
Lemma lem7194985 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7194986 {A B : Type'} : (term560 A B) = (term560 A B).
Proof. exact (MK_COMB (@lem7194985 B) (@lem7194984 A B)). Qed.
Lemma lem7195069 {A B : Type'} : (term559 A B) = (term560 A B).
Proof. exact (TRANS (@lem7194915 A B) (@lem7194986 A B)). Qed.
Lemma lem7195070 {A B : Type'} : (term560 A B) = (term559 A B).
Proof. exact (SYM (@lem7195069 A B)). Qed.
Lemma lem7195071 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term517 A B i f g t s) : term517 A B i f g t s.
Proof. exact (h1). Qed.
Lemma lem7195074 (p : Prop) : p = (term344 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7195075 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term528 A B x i t) = (term561 A B x i t).
Proof. exact (@lem7195074 (term528 A B x i t)). Qed.
Lemma lem7195076 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term561 A B x i t) = (term528 A B x i t).
Proof. exact (SYM (@lem7195075 A B x i t)). Qed.
Lemma lem7195077 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term562 A B x i t.
Proof. exact (h1). Qed.
Lemma lem7195087 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term508 A B t i f x g y) = (term508 A B t i f x g y).
Proof. exact (eq_refl (term508 A B t i f x g y)). Qed.
Lemma lem7195088 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term509 A B t i f x g) = (term509 A B t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7195087 A B t i f x g y)). Qed.
Lemma lem7195089 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7195090 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term510 A B t i f x g) = (term510 A B t i f x g).
Proof. exact (MK_COMB (@lem7195089 B) (@lem7195088 A B t i f x g)). Qed.
Lemma lem7195092 {A : Type'} (s : A -> Prop) (x : A) : (term441 A s x) = (term441 A s x).
Proof. exact (eq_refl (term441 A s x)). Qed.
Lemma lem7195093 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term563 A B s t i f x g) = (term563 A B s t i f x g).
Proof. exact (MK_COMB (@lem7195092 A s x) (@lem7195090 A B t i f x g)). Qed.
Lemma lem7195094 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term511 A B s t i f x g) = (term563 A B s t i f x g).
Proof. exact (@lem17265 (s x) (term510 A B t i f x g)). Qed.
Lemma lem7195095 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term511 A B s t i f x g) = (term563 A B s t i f x g).
Proof. exact (TRANS (@lem7195094 A B s t i f x g) (@lem7195093 A B s t i f x g)). Qed.
Lemma lem7195096 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term513 A B s t i f g) = (term564 A B s t i f g).
Proof. exact (fun_ext (fun x : A => @lem7195095 A B s t i f x g)). Qed.
Lemma lem7195097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195098 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term514 A B s t i f g) = (term565 A B s t i f g).
Proof. exact (MK_COMB (@lem7195097 A) (@lem7195096 A B s t i f g)). Qed.
Lemma lem7195105 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term297 B t g y) = (term382 B t g y).
Proof. exact (@lem17265 (t y) (term235 B g y)). Qed.
Lemma lem7195106 {B : Type'} (t : B -> Prop) (g : B -> real) : (term299 B t g) = (term383 B t g).
Proof. exact (fun_ext (fun y : B => @lem7195105 B t g y)). Qed.
Lemma lem7195107 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7195108 {B : Type'} (t : B -> Prop) (g : B -> real) : (term300 B t g) = (term384 B t g).
Proof. exact (MK_COMB (@lem7195107 B) (@lem7195106 B t g)). Qed.
Lemma lem7195113 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7195114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195115 {B : Type'} (t : B -> Prop) (g : B -> real) : (term302 B t g) = (term385 B t g).
Proof. exact (MK_COMB (@lem7195114) (@lem7195108 B t g)). Qed.
Lemma lem7195116 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term303 A B g t s) = (term386 A B g t s).
Proof. exact (MK_COMB (@lem7195115 B t g) (@lem7195113 A B t s)). Qed.
Lemma lem7195117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195118 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term516 A B s t i f g) = (term566 A B s t i f g).
Proof. exact (MK_COMB (@lem7195117) (@lem7195098 A B s t i f g)). Qed.
Lemma lem7195119 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term517 A B i f g t s) = (term567 A B i f g t s).
Proof. exact (MK_COMB (@lem7195118 A B s t i f g) (@lem7195116 A B g t s)). Qed.
Lemma lem7195246 {A : Type'} (P : Prop) (Q : A -> Prop) : (term568 A P Q) = (term569 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7195247 {B : Type'} (P : Prop) (Q : B -> Prop) : (term568 B P Q) = (term569 B P Q).
Proof. exact (@lem7195246 B P Q). Qed.
Lemma lem7195248 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term570 A B s t i f x g) = (term571 A B s t i f x g).
Proof. exact (@lem7195247 B (term439 A s x) (term509 A B t i f x g)). Qed.
Lemma lem7195249 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term572 A B t i f x g y) = (term508 A B t i f x g y).
Proof. exact (eq_refl (term572 A B t i f x g y)). Qed.
Lemma lem7195250 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term573 A B t i f x g) = (term509 A B t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7195249 A B t i f x g y)). Qed.
Lemma lem7195251 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7195252 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term574 A B t i f x g) = (term510 A B t i f x g).
Proof. exact (MK_COMB (@lem7195251 B) (@lem7195250 A B t i f x g)). Qed.
Lemma lem7195253 {A : Type'} (s : A -> Prop) (x : A) : (term441 A s x) = (term441 A s x).
Proof. exact (eq_refl (term441 A s x)). Qed.
Lemma lem7195254 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term570 A B s t i f x g) = (term563 A B s t i f x g).
Proof. exact (MK_COMB (@lem7195253 A s x) (@lem7195252 A B t i f x g)). Qed.
Lemma lem7195255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7195256 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term575 A B s t i f x g) = (term576 A B s t i f x g).
Proof. exact (MK_COMB (@lem7195255) (@lem7195254 A B s t i f x g)). Qed.
Lemma lem7195257 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term572 A B t i f x g y) = (term508 A B t i f x g y).
Proof. exact (eq_refl (term572 A B t i f x g y)). Qed.
Lemma lem7195258 {A : Type'} (s : A -> Prop) (x : A) : (term441 A s x) = (term441 A s x).
Proof. exact (eq_refl (term441 A s x)). Qed.
Lemma lem7195259 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term577 A B s t i f x g y) = (term578 A B s t i f x g y).
Proof. exact (MK_COMB (@lem7195258 A s x) (@lem7195257 A B t i f x g y)). Qed.
Lemma lem7195260 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term579 A B s t i f x g) = (term580 A B s t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7195259 A B s t i f x g y)). Qed.
Lemma lem7195261 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7195262 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term571 A B s t i f x g) = (term581 A B s t i f x g).
Proof. exact (MK_COMB (@lem7195261 B) (@lem7195260 A B s t i f x g)). Qed.
Lemma lem7195263 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : ((term570 A B s t i f x g) = (term571 A B s t i f x g)) = ((term563 A B s t i f x g) = (term581 A B s t i f x g)).
Proof. exact (MK_COMB (@lem7195256 A B s t i f x g) (@lem7195262 A B s t i f x g)). Qed.
Lemma lem7195264 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term563 A B s t i f x g) = (term581 A B s t i f x g).
Proof. exact (EQ_MP (@lem7195263 A B s t i f x g) (@lem7195248 A B s t i f x g)). Qed.
Lemma lem7195265 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term564 A B s t i f g) = (term582 A B s t i f g).
Proof. exact (fun_ext (fun x : A => @lem7195264 A B s t i f x g)). Qed.
Lemma lem7195266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195267 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term565 A B s t i f g) = (term583 A B s t i f g).
Proof. exact (MK_COMB (@lem7195266 A) (@lem7195265 A B s t i f g)). Qed.
Lemma lem7195269 {A B : Type'} (P : type1413 A B) : (term584 A B P) = (term585 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7195270 {A B : Type'} (P : type1413 A B) : (term584 A B P) = (term585 A B P).
Proof. exact (@lem7195269 A B P). Qed.
Lemma lem7195271 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term586 A B s t i f g) = (term587 A B s t i f g).
Proof. exact (@lem7195270 A B (term588 A B s t i f g)). Qed.
Lemma lem7195272 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term589 A B s t i f g x) = (term580 A B s t i f x g).
Proof. exact (eq_refl (term589 A B s t i f g x)). Qed.
Lemma lem7195273 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7195274 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term590 A B s t i f g x y) = (term591 A B s t i f x g y).
Proof. exact (MK_COMB (@lem7195272 A B s t i f x g) (@lem7195273 B y)). Qed.
Lemma lem7195275 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term591 A B s t i f x g y) = (term578 A B s t i f x g y).
Proof. exact (eq_refl (term591 A B s t i f x g y)). Qed.
Lemma lem7195276 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) : (term590 A B s t i f g x y) = (term578 A B s t i f x g y).
Proof. exact (TRANS (@lem7195274 A B s t i f x g y) (@lem7195275 A B s t i f x g y)). Qed.
Lemma lem7195277 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term592 A B s t i f g x) = (term580 A B s t i f x g).
Proof. exact (fun_ext (fun y : B => @lem7195276 A B s t i f x g y)). Qed.
Lemma lem7195278 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem7195279 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term593 A B s t i f g x) = (term581 A B s t i f x g).
Proof. exact (MK_COMB (@lem7195278 B) (@lem7195277 A B s t i f x g)). Qed.
Lemma lem7195280 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term594 A B s t i f g) = (term582 A B s t i f g).
Proof. exact (fun_ext (fun x : A => @lem7195279 A B s t i f x g)). Qed.
Lemma lem7195281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195282 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term586 A B s t i f g) = (term583 A B s t i f g).
Proof. exact (MK_COMB (@lem7195281 A) (@lem7195280 A B s t i f g)). Qed.
Lemma lem7195283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7195284 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term595 A B s t i f g) = (term596 A B s t i f g).
Proof. exact (MK_COMB (@lem7195283) (@lem7195282 A B s t i f g)). Qed.
Lemma lem7195285 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) : (term589 A B s t i f g x) = (term580 A B s t i f x g).
Proof. exact (eq_refl (term589 A B s t i f g x)). Qed.
Lemma lem7195286 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem7195287 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term597 A B s t i f g y x) = (term598 A B s t i f g y x).
Proof. exact (MK_COMB (@lem7195285 A B s t i f x g) (@lem7195286 A B y x)). Qed.
Lemma lem7195288 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term598 A B s t i f g y x) = (term599 A B s t i f g y x).
Proof. exact (eq_refl (term598 A B s t i f g y x)). Qed.
Lemma lem7195289 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term597 A B s t i f g y x) = (term599 A B s t i f g y x).
Proof. exact (TRANS (@lem7195287 A B s t i f g y x) (@lem7195288 A B s t i f g y x)). Qed.
Lemma lem7195290 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term600 A B s t i f g y) = (term601 A B s t i f g y).
Proof. exact (fun_ext (fun x : A => @lem7195289 A B s t i f g y x)). Qed.
Lemma lem7195291 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195292 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term602 A B s t i f g y) = (term603 A B s t i f g y).
Proof. exact (MK_COMB (@lem7195291 A) (@lem7195290 A B s t i f g y)). Qed.
Lemma lem7195293 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term604 A B s t i f g) = (term605 A B s t i f g).
Proof. exact (fun_ext (fun y : A -> B => @lem7195292 A B s t i f g y)). Qed.
Lemma lem7195294 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7195295 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term587 A B s t i f g) = (term606 A B s t i f g).
Proof. exact (MK_COMB (@lem7195294 A B) (@lem7195293 A B s t i f g)). Qed.
Lemma lem7195296 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : ((term586 A B s t i f g) = (term587 A B s t i f g)) = ((term583 A B s t i f g) = (term606 A B s t i f g)).
Proof. exact (MK_COMB (@lem7195284 A B s t i f g) (@lem7195295 A B s t i f g)). Qed.
Lemma lem7195297 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term583 A B s t i f g) = (term606 A B s t i f g).
Proof. exact (EQ_MP (@lem7195296 A B s t i f g) (@lem7195271 A B s t i f g)). Qed.
Lemma lem7195298 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term565 A B s t i f g) = (term606 A B s t i f g).
Proof. exact (TRANS (@lem7195267 A B s t i f g) (@lem7195297 A B s t i f g)). Qed.
Lemma lem7195299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195300 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term566 A B s t i f g) = (term607 A B s t i f g).
Proof. exact (MK_COMB (@lem7195299) (@lem7195298 A B s t i f g)). Qed.
Lemma lem7195301 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term386 A B g t s) = (term386 A B g t s).
Proof. exact (eq_refl (term386 A B g t s)). Qed.
Lemma lem7195302 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term567 A B i f g t s) = (term608 A B i f g t s).
Proof. exact (MK_COMB (@lem7195300 A B s t i f g) (@lem7195301 A B g t s)). Qed.
Lemma lem7195304 {A : Type'} (P : A -> Prop) (Q : Prop) : (term609 A P Q) = (term610 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7195305 {A B : Type'} (P : type572 A B) (Q : Prop) : (term611 A B P Q) = (term612 A B P Q).
Proof. exact (@lem7195304 (A -> B) P Q). Qed.
Lemma lem7195306 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term613 A B i f g t s) = (term614 A B i f g t s).
Proof. exact (@lem7195305 A B (term605 A B s t i f g) (term386 A B g t s)). Qed.
Lemma lem7195307 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term615 A B s t i f g y) = (term603 A B s t i f g y).
Proof. exact (eq_refl (term615 A B s t i f g y)). Qed.
Lemma lem7195308 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term616 A B s t i f g) = (term605 A B s t i f g).
Proof. exact (fun_ext (fun y : A -> B => @lem7195307 A B s t i f g y)). Qed.
Lemma lem7195309 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7195310 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term617 A B s t i f g) = (term606 A B s t i f g).
Proof. exact (MK_COMB (@lem7195309 A B) (@lem7195308 A B s t i f g)). Qed.
Lemma lem7195311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195312 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) : (term618 A B s t i f g) = (term607 A B s t i f g).
Proof. exact (MK_COMB (@lem7195311) (@lem7195310 A B s t i f g)). Qed.
Lemma lem7195313 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term386 A B g t s) = (term386 A B g t s).
Proof. exact (eq_refl (term386 A B g t s)). Qed.
Lemma lem7195314 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term613 A B i f g t s) = (term608 A B i f g t s).
Proof. exact (MK_COMB (@lem7195312 A B s t i f g) (@lem7195313 A B g t s)). Qed.
Lemma lem7195315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7195316 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term619 A B i f g t s) = (term620 A B i f g t s).
Proof. exact (MK_COMB (@lem7195315) (@lem7195314 A B i f g t s)). Qed.
Lemma lem7195317 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term615 A B s t i f g y) = (term603 A B s t i f g y).
Proof. exact (eq_refl (term615 A B s t i f g y)). Qed.
Lemma lem7195318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195319 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term621 A B s t i f g y) = (term622 A B s t i f g y).
Proof. exact (MK_COMB (@lem7195318) (@lem7195317 A B s t i f g y)). Qed.
Lemma lem7195320 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term386 A B g t s) = (term386 A B g t s).
Proof. exact (eq_refl (term386 A B g t s)). Qed.
Lemma lem7195321 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term623 A B i f y g t s) = (term624 A B i f y g t s).
Proof. exact (MK_COMB (@lem7195319 A B s t i f g y) (@lem7195320 A B g t s)). Qed.
Lemma lem7195322 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term625 A B i f g t s) = (term626 A B i f g t s).
Proof. exact (fun_ext (fun y : A -> B => @lem7195321 A B i f y g t s)). Qed.
Lemma lem7195323 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem7195324 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term614 A B i f g t s) = (term627 A B i f g t s).
Proof. exact (MK_COMB (@lem7195323 A B) (@lem7195322 A B i f g t s)). Qed.
Lemma lem7195325 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : ((term613 A B i f g t s) = (term614 A B i f g t s)) = ((term608 A B i f g t s) = (term627 A B i f g t s)).
Proof. exact (MK_COMB (@lem7195316 A B i f g t s) (@lem7195324 A B i f g t s)). Qed.
Lemma lem7195326 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term608 A B i f g t s) = (term627 A B i f g t s).
Proof. exact (EQ_MP (@lem7195325 A B i f g t s) (@lem7195306 A B i f g t s)). Qed.
Lemma lem7195328 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term567 A B i f g t s) = (term627 A B i f g t s).
Proof. exact (TRANS (@lem7195302 A B i f g t s) (@lem7195326 A B i f g t s)). Qed.
Lemma lem7195329 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term517 A B i f g t s) = (term627 A B i f g t s).
Proof. exact (TRANS (@lem7195119 A B i f g t s) (@lem7195328 A B i f g t s)). Qed.
Lemma lem7195330 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term517 A B i f g t s) : term627 A B i f g t s.
Proof. exact (EQ_MP (@lem7195329 A B i f g t s) (@lem7195071 A B i f g t s h1)). Qed.
Lemma lem7195336 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem7195343 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term628 A B x i t x') = (term629 A B x i t x').
Proof. exact (@lem17045 (x = (i x')) (t x')). Qed.
Lemma lem7195344 {B : Type'} (P : B -> Prop) : (term630 B P) = (term631 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem7195345 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term562 A B x i t) = (term632 A B x i t).
Proof. exact (@lem7195344 B (term527 A B x i t)). Qed.
Lemma lem7195346 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term633 A B x i t x') = (term525 A B x i t x').
Proof. exact (eq_refl (term633 A B x i t x')). Qed.
Lemma lem7195347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7195348 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term634 A B x i t x') = (term628 A B x i t x').
Proof. exact (MK_COMB (@lem7195347) (@lem7195346 A B x i t x')). Qed.
Lemma lem7195349 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term634 A B x i t x') = (term629 A B x i t x').
Proof. exact (TRANS (@lem7195348 A B x i t x') (@lem7195343 A B x i t x')). Qed.
Lemma lem7195350 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term635 A B x i t) = (term636 A B x i t).
Proof. exact (fun_ext (fun x' : B => @lem7195349 A B x i t x')). Qed.
Lemma lem7195351 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7195352 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term632 A B x i t) = (term637 A B x i t).
Proof. exact (MK_COMB (@lem7195351 B) (@lem7195350 A B x i t)). Qed.
Lemma lem7195405 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term562 A B x i t) = (term637 A B x i t).
Proof. exact (TRANS (@lem7195345 A B x i t) (@lem7195352 A B x i t)). Qed.
Lemma lem7195406 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term637 A B x i t.
Proof. exact (EQ_MP (@lem7195405 A B x i t) (@lem7195077 A B x i t h1)). Qed.
Lemma lem7195407 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term624 A B i f y g t s.
Proof. exact (h1). Qed.
Lemma lem7195412 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7195413 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7195412 A Prop f x). Qed.
Lemma lem7195415 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7195413 A s x). Qed.
Lemma lem7195417 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7195422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7195423 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7195422 B Prop f x). Qed.
Lemma lem7195425 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem7195423 B t x). Qed.
Lemma lem7195426 {B : Type'} (t : B -> Prop) (x : B) : (term439 B t x) = (term440 B t x).
Proof. exact (MK_COMB (@lem7195417) (@lem7195425 B t x)). Qed.
Lemma lem7195437 {A B : Type'} (x : A) (i : B -> A) (x' : B) : (term638 A B x i x') = (term638 A B x i x').
Proof. exact (eq_refl (term638 A B x i x')). Qed.
Lemma lem7195438 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term629 A B x i t x') = (term639 A B x i t x').
Proof. exact (MK_COMB (@lem7195437 A B x i x') (@lem7195426 B t x')). Qed.
Lemma lem7195439 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term636 A B x i t) = (term640 A B x i t).
Proof. exact (fun_ext (fun x' : B => @lem7195438 A B x i t x')). Qed.
Lemma lem7195440 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7195441 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term637 A B x i t) = (term641 A B x i t).
Proof. exact (MK_COMB (@lem7195440 B) (@lem7195439 A B x i t)). Qed.
Lemma lem7195442 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term641 A B x i t.
Proof. exact (EQ_MP (@lem7195441 A B x i t) (@lem7195406 A B x i t h1)). Qed.
Lemma lem7195451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term279 A B t s) = (term279 A B t s).
Proof. exact (eq_refl (term279 A B t s)). Qed.
Lemma lem7195462 {B : Type'} (g : B -> real) (y : B) : (term235 B g y) = (term235 B g y).
Proof. exact (eq_refl (term235 B g y)). Qed.
Lemma lem7195463 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7195468 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7195469 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7195468 B Prop f x). Qed.
Lemma lem7195471 {B : Type'} (t : B -> Prop) (y : B) : (t y) = (@I (B -> Prop) t y).
Proof. exact (@lem7195469 B t y). Qed.
Lemma lem7195472 {B : Type'} (t : B -> Prop) (y : B) : (term439 B t y) = (term440 B t y).
Proof. exact (MK_COMB (@lem7195463) (@lem7195471 B t y)). Qed.
Lemma lem7195473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7195474 {B : Type'} (t : B -> Prop) (y : B) : (term441 B t y) = (term442 B t y).
Proof. exact (MK_COMB (@lem7195473) (@lem7195472 B t y)). Qed.
Lemma lem7195475 {B : Type'} (t : B -> Prop) (g : B -> real) (y : B) : (term382 B t g y) = (term443 B t g y).
Proof. exact (MK_COMB (@lem7195474 B t y) (@lem7195462 B g y)). Qed.
Lemma lem7195476 {B : Type'} (t : B -> Prop) (g : B -> real) : (term383 B t g) = (term444 B t g).
Proof. exact (fun_ext (fun y : B => @lem7195475 B t g y)). Qed.
Lemma lem7195477 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7195478 {B : Type'} (t : B -> Prop) (g : B -> real) : (term384 B t g) = (term445 B t g).
Proof. exact (MK_COMB (@lem7195477 B) (@lem7195476 B t g)). Qed.
Lemma lem7195479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195480 {B : Type'} (t : B -> Prop) (g : B -> real) : (term385 B t g) = (term446 B t g).
Proof. exact (MK_COMB (@lem7195479) (@lem7195478 B t g)). Qed.
Lemma lem7195481 {A B : Type'} (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term386 A B g t s) = (term447 A B g t s).
Proof. exact (MK_COMB (@lem7195480 B t g) (@lem7195451 A B t s)). Qed.
Lemma lem7195504 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term642 A B i f g y x) = (term642 A B i f g y x).
Proof. exact (eq_refl (term642 A B i f g y x)). Qed.
Lemma lem7195511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7195512 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem7195511 B Prop f x). Qed.
Lemma lem7195514 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term643 A B t y x) = (term644 A B t y x).
Proof. exact (@lem7195512 B t (y x)). Qed.
Lemma lem7195515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195516 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term645 A B t y x) = (term646 A B t y x).
Proof. exact (MK_COMB (@lem7195515) (@lem7195514 A B t y x)). Qed.
Lemma lem7195517 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term647 A B t i f g y x) = (term648 A B t i f g y x).
Proof. exact (MK_COMB (@lem7195516 A B t y x) (@lem7195504 A B i f g y x)). Qed.
Lemma lem7195518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7195523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7195524 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7195523 A Prop f x). Qed.
Lemma lem7195526 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7195524 A s x). Qed.
Lemma lem7195527 {A : Type'} (s : A -> Prop) (x : A) : (term439 A s x) = (term440 A s x).
Proof. exact (MK_COMB (@lem7195518) (@lem7195526 A s x)). Qed.
Lemma lem7195528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7195529 {A : Type'} (s : A -> Prop) (x : A) : (term441 A s x) = (term442 A s x).
Proof. exact (MK_COMB (@lem7195528) (@lem7195527 A s x)). Qed.
Lemma lem7195530 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term599 A B s t i f g y x) = (term649 A B s t i f g y x).
Proof. exact (MK_COMB (@lem7195529 A s x) (@lem7195517 A B t i f g y x)). Qed.
Lemma lem7195531 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term601 A B s t i f g y) = (term650 A B s t i f g y).
Proof. exact (fun_ext (fun x : A => @lem7195530 A B s t i f g y x)). Qed.
Lemma lem7195532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term603 A B s t i f g y) = (term651 A B s t i f g y).
Proof. exact (MK_COMB (@lem7195532 A) (@lem7195531 A B s t i f g y)). Qed.
Lemma lem7195534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195535 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) : (term622 A B s t i f g y) = (term652 A B s t i f g y).
Proof. exact (MK_COMB (@lem7195534) (@lem7195533 A B s t i f g y)). Qed.
Lemma lem7195536 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) : (term624 A B i f y g t s) = (term653 A B i f y g t s).
Proof. exact (MK_COMB (@lem7195535 A B s t i f g y) (@lem7195481 A B g t s)). Qed.
Lemma lem7195537 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term653 A B i f y g t s.
Proof. exact (EQ_MP (@lem7195536 A B i f y g t s) (@lem7195407 A B i f y g t s h1)). Qed.
Lemma lem7195539 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term651 A B s t i f g y.
Proof. exact (proj1 (@lem7195537 A B i f y g t s h1)). Qed.
Lemma lem7195555 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (x' : B) : (term639 A B x i t x') = (term639 A B x i t x').
Proof. exact (eq_refl (term639 A B x i t x')). Qed.
Lemma lem7195556 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term640 A B x i t) = (term640 A B x i t).
Proof. exact (fun_ext (fun x' : B => @lem7195555 A B x i t x')). Qed.
Lemma lem7195557 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7195559 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) : (term641 A B x i t) = (term641 A B x i t).
Proof. exact (MK_COMB (@lem7195557 B) (@lem7195556 A B x i t)). Qed.
Lemma lem7195560 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term641 A B x i t.
Proof. exact (EQ_MP (@lem7195559 A B x i t) (@lem7195442 A B x i t h1)). Qed.
Lemma lem7195575 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term649 A B s t i f g y x) = (term654 A B t s i f g y x).
Proof. exact (@lem19490 (term644 A B t y x) (term440 A s x) (term642 A B i f g y x)). Qed.
Lemma lem7195582 {A B : Type'} (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term655 A B s i f g y x) = (term656 A B i s f g y x).
Proof. exact (@lem19490 ((term657 A B i y x) = x) (term440 A s x) (term658 A B f g y x)). Qed.
Lemma lem7195585 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (x : A) : (term659 A B s t y x) = (term659 A B s t y x).
Proof. exact (eq_refl (term659 A B s t y x)). Qed.
Lemma lem7195586 {A B : Type'} (t : B -> Prop) (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term654 A B t s i f g y x) = (term660 A B t i s f g y x).
Proof. exact (MK_COMB (@lem7195585 A B s t y x) (@lem7195582 A B i s f g y x)). Qed.
Lemma lem7195588 {A B : Type'} (t : B -> Prop) (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) (x : A) : (term649 A B s t i f g y x) = (term660 A B t i s f g y x).
Proof. exact (TRANS (@lem7195575 A B t s i f g y x) (@lem7195586 A B t i s f g y x)). Qed.
Lemma lem7195589 {A B : Type'} (t : B -> Prop) (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) : (term650 A B s t i f g y) = (term661 A B t i s f g y).
Proof. exact (fun_ext (fun x : A => @lem7195588 A B t i s f g y x)). Qed.
Lemma lem7195590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7195592 {A B : Type'} (t : B -> Prop) (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) : (term651 A B s t i f g y) = (term662 A B t i s f g y).
Proof. exact (MK_COMB (@lem7195590 A) (@lem7195589 A B t i s f g y)). Qed.
Lemma lem7195593 {A B : Type'} (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term662 A B t i s f g y.
Proof. exact (EQ_MP (@lem7195592 A B t i s f g y) (@lem7195539 A B i f y g t s h1)). Qed.
Lemma lem7195615 {A B : Type'} (_96438 : B) (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term663 A B x i t _96438.
Proof. exact (@lem7195560 A B x i t h1 _96438). Qed.
Lemma lem7195616 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (_96438 : B) : (term663 A B x i t _96438) = (term639 A B x i t _96438).
Proof. exact (eq_refl (term663 A B x i t _96438)). Qed.
Lemma lem7195618 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term664 A B t i s f g y _96439.
Proof. exact (@lem7195593 A B i f y g t s h1 _96439). Qed.
Lemma lem7195619 {A B : Type'} (t : B -> Prop) (i : B -> A) (s : A -> Prop) (f : A -> real) (g : B -> real) (y : A -> B) (_96439 : A) : (term664 A B t i s f g y _96439) = (term660 A B t i s f g y _96439).
Proof. exact (eq_refl (term664 A B t i s f g y _96439)). Qed.
Lemma lem7195620 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term660 A B t i s f g y _96439.
Proof. exact (EQ_MP (@lem7195619 A B t i s f g y _96439) (@lem7195618 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195624 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term656 A B i s f g y _96439.
Proof. exact (proj2 (@lem7195620 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195635 {A B : Type'} (_96438 : B) (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term639 A B x i t _96438.
Proof. exact (EQ_MP (@lem7195616 A B x i t _96438) (@lem7195615 A B _96438 x i t h1)). Qed.
Lemma lem7195651 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term665 A B s t y _96439.
Proof. exact (proj1 (@lem7195620 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195657 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term666 A B s i y _96439.
Proof. exact (proj1 (@lem7195624 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195794 {A : Type'} (x : A) (y : A) (z : A) : term667 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem7195806 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem7195415 A s x) (@lem7195336 A s x h1)). Qed.
Lemma lem7195807 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term479 A s x.
Proof. exact (fun h0 : term440 A s x => @lem7195806 A s x h1). Qed.
Lemma lem7195809 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7195810 {A : Type'} (s : A -> Prop) (x : A) : (term479 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7195809 (@I (A -> Prop) s x)). Qed.
Lemma lem7195811 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem7195810 A s x) (@lem7195807 A s x h1)). Qed.
Lemma lem7195817 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7195818 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term666 A B s i y _96439) = (term668 A B i y s _96439).
Proof. exact (@lem7195817 ((term657 A B i y _96439) = _96439) (term440 A s _96439)). Qed.
Lemma lem7195826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7195827 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term669 A B s i y _96439) = (term670 A B i y s _96439).
Proof. exact (MK_COMB (@lem7195826) (@lem7195818 A B i y s _96439)). Qed.
Lemma lem7195835 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term668 A B i y s _96439) = (term668 A B i y s _96439).
Proof. exact (eq_refl (term668 A B i y s _96439)). Qed.
Lemma lem7195836 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term666 A B s i y _96439) = (term668 A B i y s _96439)) = ((term668 A B i y s _96439) = (term668 A B i y s _96439)).
Proof. exact (MK_COMB (@lem7195827 A B i y s _96439) (@lem7195835 A B i y s _96439)). Qed.
Lemma lem7195838 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7195839 (x : Prop) : (x = x) = True.
Proof. exact (@lem7195838 Prop x). Qed.
Lemma lem7195840 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term668 A B i y s _96439) = (term668 A B i y s _96439)) = True.
Proof. exact (@lem7195839 (term668 A B i y s _96439)). Qed.
Lemma lem7195841 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term666 A B s i y _96439) = (term668 A B i y s _96439)) = True.
Proof. exact (TRANS (@lem7195836 A B i y s _96439) (@lem7195840 A B i y s _96439)). Qed.
Lemma lem7195842 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : True = ((term666 A B s i y _96439) = (term668 A B i y s _96439)).
Proof. exact (SYM (@lem7195841 A B i y s _96439)). Qed.
Lemma lem7195843 {A B : Type'} (i : B -> A) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term666 A B s i y _96439) = (term668 A B i y s _96439).
Proof. exact (EQ_MP (@lem7195842 A B i y s _96439) (@lem0)). Qed.
Lemma lem7195844 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term668 A B i y s _96439.
Proof. exact (EQ_MP (@lem7195843 A B i y s _96439) (@lem7195657 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195846 (b : Prop) (a : Prop) : (a \/ b) = (term488 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7195847 {A B : Type'} (s : A -> Prop) (i : B -> A) (y : A -> B) (_96439 : A) : (term668 A B i y s _96439) = (term671 A B s i y _96439).
Proof. exact (@lem7195846 (term440 A s _96439) ((term657 A B i y _96439) = _96439)). Qed.
Lemma lem7195849 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7195850 {A : Type'} (s : A -> Prop) (_96439 : A) : (term490 A s _96439) = (@I (A -> Prop) s _96439).
Proof. exact (@lem7195849 (@I (A -> Prop) s _96439)). Qed.
Lemma lem7195851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7195852 {A : Type'} (s : A -> Prop) (_96439 : A) : (term491 A s _96439) = (term492 A s _96439).
Proof. exact (MK_COMB (@lem7195851) (@lem7195850 A s _96439)). Qed.
Lemma lem7195853 {A B : Type'} (i : B -> A) (y : A -> B) (_96439 : A) : ((term657 A B i y _96439) = _96439) = ((term657 A B i y _96439) = _96439).
Proof. exact (eq_refl ((term657 A B i y _96439) = _96439)). Qed.
Lemma lem7195854 {A B : Type'} (s : A -> Prop) (i : B -> A) (y : A -> B) (_96439 : A) : (term671 A B s i y _96439) = (term672 A B s i y _96439).
Proof. exact (MK_COMB (@lem7195852 A s _96439) (@lem7195853 A B i y _96439)). Qed.
Lemma lem7195855 {A B : Type'} (s : A -> Prop) (i : B -> A) (y : A -> B) (_96439 : A) : (term668 A B i y s _96439) = (term672 A B s i y _96439).
Proof. exact (TRANS (@lem7195847 A B s i y _96439) (@lem7195854 A B s i y _96439)). Qed.
Lemma lem7195858 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term672 A B s i y _96439.
Proof. exact (EQ_MP (@lem7195855 A B s i y _96439) (@lem7195844 A B _96439 i f y g t s h1)). Qed.
Lemma lem7195859 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term672 A B s i y _96439.
Proof. exact (@lem7195858 A B _96439 i f y g t s h1). Qed.
Lemma lem7195860 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term672 A B s i y x.
Proof. exact (@lem7195859 A B x i f y g t s h1). Qed.
Lemma lem7195863 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : (term657 A B i y x) = x.
Proof. exact (@lem7195860 A B x i f y g t s h2 (@lem7195811 A s x h1)). Qed.
Lemma lem7195864 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term673 A B i y x.
Proof. exact (fun h0 : term674 A B i y x => @lem7195863 A B x i f y g t s h1 h2). Qed.
Lemma lem7195866 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7195867 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : (term673 A B i y x) = ((term657 A B i y x) = x).
Proof. exact (@lem7195866 ((term657 A B i y x) = x)). Qed.
Lemma lem7195868 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : (term657 A B i y x) = x.
Proof. exact (EQ_MP (@lem7195867 A B i y x) (@lem7195864 A B x i f y g t s h1 h2)). Qed.
Lemma lem7195870 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem7195871 {A : Type'} (x : A) : x = x.
Proof. exact (@lem7195870 A x). Qed.
Lemma lem7195872 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : (term657 A B i y x) = (term657 A B i y x).
Proof. exact (@lem7195871 A (term657 A B i y x)). Qed.
Lemma lem7195873 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : term675 A B i y x.
Proof. exact (fun h0 : term676 A B i y x => @lem7195872 A B i y x). Qed.
Lemma lem7195875 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7195876 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : (term675 A B i y x) = ((term657 A B i y x) = (term657 A B i y x)).
Proof. exact (@lem7195875 ((term657 A B i y x) = (term657 A B i y x))). Qed.
Lemma lem7195877 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : (term657 A B i y x) = (term657 A B i y x).
Proof. exact (EQ_MP (@lem7195876 A B i y x) (@lem7195873 A B i y x)). Qed.
Lemma lem7195895 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7195896 {A : Type'} (y : A) (x : A) (z : A) : (term677 A x y z) = (term678 A y x z).
Proof. exact (@lem7195895 (y = z) (term333 A x z)). Qed.
Lemma lem7195906 {A : Type'} (x : A) (y : A) : (term679 A x y) = (term679 A x y).
Proof. exact (eq_refl (term679 A x y)). Qed.
Lemma lem7195907 {A : Type'} (y : A) (x : A) (z : A) : (term667 A x y z) = (term680 A y x z).
Proof. exact (MK_COMB (@lem7195906 A x y) (@lem7195896 A y x z)). Qed.
Lemma lem7195911 (q : Prop) (p : Prop) (r : Prop) : (term681 p q r) = (term681 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7195912 {A : Type'} (y : A) (x : A) (z : A) : (term680 A y x z) = (term682 A y x z).
Proof. exact (@lem7195911 (y = z) (term333 A x y) (term333 A x z)). Qed.
Lemma lem7195934 {A : Type'} (y : A) (x : A) (z : A) : (term667 A x y z) = (term682 A y x z).
Proof. exact (TRANS (@lem7195907 A y x z) (@lem7195912 A y x z)). Qed.
Lemma lem7195935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7195936 {A : Type'} (y : A) (x : A) (z : A) : (term683 A x y z) = (term684 A y x z).
Proof. exact (MK_COMB (@lem7195935) (@lem7195934 A y x z)). Qed.
Lemma lem7195958 {A : Type'} (y : A) (x : A) (z : A) : (term682 A y x z) = (term682 A y x z).
Proof. exact (eq_refl (term682 A y x z)). Qed.
Lemma lem7195959 {A : Type'} (y : A) (x : A) (z : A) : ((term667 A x y z) = (term682 A y x z)) = ((term682 A y x z) = (term682 A y x z)).
Proof. exact (MK_COMB (@lem7195936 A y x z) (@lem7195958 A y x z)). Qed.
Lemma lem7195961 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7195962 (x : Prop) : (x = x) = True.
Proof. exact (@lem7195961 Prop x). Qed.
Lemma lem7195963 {A : Type'} (y : A) (x : A) (z : A) : ((term682 A y x z) = (term682 A y x z)) = True.
Proof. exact (@lem7195962 (term682 A y x z)). Qed.
Lemma lem7195964 {A : Type'} (y : A) (x : A) (z : A) : ((term667 A x y z) = (term682 A y x z)) = True.
Proof. exact (TRANS (@lem7195959 A y x z) (@lem7195963 A y x z)). Qed.
Lemma lem7195965 {A : Type'} (y : A) (x : A) (z : A) : True = ((term667 A x y z) = (term682 A y x z)).
Proof. exact (SYM (@lem7195964 A y x z)). Qed.
Lemma lem7195966 {A : Type'} (y : A) (x : A) (z : A) : (term667 A x y z) = (term682 A y x z).
Proof. exact (EQ_MP (@lem7195965 A y x z) (@lem0)). Qed.
Lemma lem7195967 {A : Type'} (y : A) (x : A) (z : A) : term682 A y x z.
Proof. exact (EQ_MP (@lem7195966 A y x z) (@lem7195794 A x y z)). Qed.
Lemma lem7195969 (b : Prop) (a : Prop) : (a \/ b) = (term488 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7195970 {A : Type'} (x : A) (y : A) (z : A) : (term682 A y x z) = (term685 A x y z).
Proof. exact (@lem7195969 (term686 A y x z) (y = z)). Qed.
Lemma lem7195972 (a : Prop) (b : Prop) : (term687 a b) = (term688 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7195973 {A : Type'} (y : A) (x : A) (z : A) : (term689 A y x z) = (term690 A y x z).
Proof. exact (@lem7195972 (term333 A x y) (term333 A x z)). Qed.
Lemma lem7195975 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7195976 {A : Type'} (x : A) (y : A) : (term691 A x y) = (x = y).
Proof. exact (@lem7195975 (x = y)). Qed.
Lemma lem7195977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7195978 {A : Type'} (x : A) (y : A) : (term692 A x y) = (term393 A x y).
Proof. exact (MK_COMB (@lem7195977) (@lem7195976 A x y)). Qed.
Lemma lem7195980 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7195981 {A : Type'} (x : A) (z : A) : (term691 A x z) = (x = z).
Proof. exact (@lem7195980 (x = z)). Qed.
Lemma lem7195982 {A : Type'} (y : A) (x : A) (z : A) : (term690 A y x z) = (term693 A y x z).
Proof. exact (MK_COMB (@lem7195978 A x y) (@lem7195981 A x z)). Qed.
Lemma lem7195983 {A : Type'} (y : A) (x : A) (z : A) : (term689 A y x z) = (term693 A y x z).
Proof. exact (TRANS (@lem7195973 A y x z) (@lem7195982 A y x z)). Qed.
Lemma lem7195984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7195985 {A : Type'} (y : A) (x : A) (z : A) : (term694 A y x z) = (term695 A y x z).
Proof. exact (MK_COMB (@lem7195984) (@lem7195983 A y x z)). Qed.
Lemma lem7195986 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7195987 {A : Type'} (x : A) (y : A) (z : A) : (term685 A x y z) = (term696 A x y z).
Proof. exact (MK_COMB (@lem7195985 A y x z) (@lem7195986 A y z)). Qed.
Lemma lem7195988 {A : Type'} (x : A) (y : A) (z : A) : (term682 A y x z) = (term696 A x y z).
Proof. exact (TRANS (@lem7195970 A x y z) (@lem7195987 A x y z)). Qed.
Lemma lem7195990 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term697 A B i y x.
Proof. exact (conj (@lem7195868 A B x i f y g t s h1 h2) (@lem7195877 A B i y x)). Qed.
Lemma lem7195992 {A : Type'} (x : A) (y : A) (z : A) : term696 A x y z.
Proof. exact (EQ_MP (@lem7195988 A x y z) (@lem7195967 A y x z)). Qed.
Lemma lem7195993 {A : Type'} (x : A) (y : A) (z : A) : term696 A x y z.
Proof. exact (@lem7195992 A x y z). Qed.
Lemma lem7195994 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : term698 A B i y x.
Proof. exact (@lem7195993 A (term657 A B i y x) x (term657 A B i y x)). Qed.
Lemma lem7195997 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : x = (term657 A B i y x).
Proof. exact (@lem7195994 A B i y x (@lem7195990 A B x i f y g t s h1 h2)). Qed.
Lemma lem7195998 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term699 A B i y x.
Proof. exact (fun h0 : term700 A B i y x => @lem7195997 A B x i f y g t s h1 h2). Qed.
Lemma lem7196000 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7196001 {A B : Type'} (i : B -> A) (y : A -> B) (x : A) : (term699 A B i y x) = (x = (term657 A B i y x)).
Proof. exact (@lem7196000 (x = (term657 A B i y x))). Qed.
Lemma lem7196002 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : x = (term657 A B i y x).
Proof. exact (EQ_MP (@lem7196001 A B i y x) (@lem7195998 A B x i f y g t s h1 h2)). Qed.
Lemma lem7196004 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem7195415 A s x) (@lem7195336 A s x h1)). Qed.
Lemma lem7196005 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term479 A s x.
Proof. exact (fun h0 : term440 A s x => @lem7196004 A s x h1). Qed.
Lemma lem7196007 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7196008 {A : Type'} (s : A -> Prop) (x : A) : (term479 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7196007 (@I (A -> Prop) s x)). Qed.
Lemma lem7196009 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem7196008 A s x) (@lem7196005 A s x h1)). Qed.
Lemma lem7196015 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7196016 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term665 A B s t y _96439) = (term701 A B t y s _96439).
Proof. exact (@lem7196015 (term644 A B t y _96439) (term440 A s _96439)). Qed.
Lemma lem7196022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7196023 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term702 A B s t y _96439) = (term703 A B t y s _96439).
Proof. exact (MK_COMB (@lem7196022) (@lem7196016 A B t y s _96439)). Qed.
Lemma lem7196029 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term701 A B t y s _96439) = (term701 A B t y s _96439).
Proof. exact (eq_refl (term701 A B t y s _96439)). Qed.
Lemma lem7196030 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term665 A B s t y _96439) = (term701 A B t y s _96439)) = ((term701 A B t y s _96439) = (term701 A B t y s _96439)).
Proof. exact (MK_COMB (@lem7196023 A B t y s _96439) (@lem7196029 A B t y s _96439)). Qed.
Lemma lem7196032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7196033 (x : Prop) : (x = x) = True.
Proof. exact (@lem7196032 Prop x). Qed.
Lemma lem7196034 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term701 A B t y s _96439) = (term701 A B t y s _96439)) = True.
Proof. exact (@lem7196033 (term701 A B t y s _96439)). Qed.
Lemma lem7196035 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : ((term665 A B s t y _96439) = (term701 A B t y s _96439)) = True.
Proof. exact (TRANS (@lem7196030 A B t y s _96439) (@lem7196034 A B t y s _96439)). Qed.
Lemma lem7196036 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : True = ((term665 A B s t y _96439) = (term701 A B t y s _96439)).
Proof. exact (SYM (@lem7196035 A B t y s _96439)). Qed.
Lemma lem7196037 {A B : Type'} (t : B -> Prop) (y : A -> B) (s : A -> Prop) (_96439 : A) : (term665 A B s t y _96439) = (term701 A B t y s _96439).
Proof. exact (EQ_MP (@lem7196036 A B t y s _96439) (@lem0)). Qed.
Lemma lem7196038 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term701 A B t y s _96439.
Proof. exact (EQ_MP (@lem7196037 A B t y s _96439) (@lem7195651 A B _96439 i f y g t s h1)). Qed.
Lemma lem7196040 (b : Prop) (a : Prop) : (a \/ b) = (term488 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7196041 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_96439 : A) : (term701 A B t y s _96439) = (term704 A B s t y _96439).
Proof. exact (@lem7196040 (term440 A s _96439) (term644 A B t y _96439)). Qed.
Lemma lem7196043 (a : Prop) : (term351 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7196044 {A : Type'} (s : A -> Prop) (_96439 : A) : (term490 A s _96439) = (@I (A -> Prop) s _96439).
Proof. exact (@lem7196043 (@I (A -> Prop) s _96439)). Qed.
Lemma lem7196045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7196046 {A : Type'} (s : A -> Prop) (_96439 : A) : (term491 A s _96439) = (term492 A s _96439).
Proof. exact (MK_COMB (@lem7196045) (@lem7196044 A s _96439)). Qed.
Lemma lem7196047 {A B : Type'} (t : B -> Prop) (y : A -> B) (_96439 : A) : (term644 A B t y _96439) = (term644 A B t y _96439).
Proof. exact (eq_refl (term644 A B t y _96439)). Qed.
Lemma lem7196048 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_96439 : A) : (term704 A B s t y _96439) = (term705 A B s t y _96439).
Proof. exact (MK_COMB (@lem7196046 A s _96439) (@lem7196047 A B t y _96439)). Qed.
Lemma lem7196049 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (y : A -> B) (_96439 : A) : (term701 A B t y s _96439) = (term705 A B s t y _96439).
Proof. exact (TRANS (@lem7196041 A B s t y _96439) (@lem7196048 A B s t y _96439)). Qed.
Lemma lem7196052 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term705 A B s t y _96439.
Proof. exact (EQ_MP (@lem7196049 A B s t y _96439) (@lem7196038 A B _96439 i f y g t s h1)). Qed.
Lemma lem7196053 {A B : Type'} (_96439 : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term705 A B s t y _96439.
Proof. exact (@lem7196052 A B _96439 i f y g t s h1). Qed.
Lemma lem7196054 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term624 A B i f y g t s) : term705 A B s t y x.
Proof. exact (@lem7196053 A B x i f y g t s h1). Qed.
Lemma lem7196057 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term644 A B t y x.
Proof. exact (@lem7196054 A B x i f y g t s h2 (@lem7196009 A s x h1)). Qed.
Lemma lem7196058 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term706 A B t y x.
Proof. exact (fun h0 : term707 A B t y x => @lem7196057 A B x i f y g t s h1 h2). Qed.
Lemma lem7196060 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7196061 {A B : Type'} (t : B -> Prop) (y : A -> B) (x : A) : (term706 A B t y x) = (term644 A B t y x).
Proof. exact (@lem7196060 (term644 A B t y x)). Qed.
Lemma lem7196062 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term644 A B t y x.
Proof. exact (EQ_MP (@lem7196061 A B t y x) (@lem7196058 A B x i f y g t s h1 h2)). Qed.
Lemma lem7196064 (a : Prop) (b : Prop) : (term708 a b) = (term709 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7196065 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (_96438 : B) : (term639 A B x i t _96438) = (term710 A B x i t _96438).
Proof. exact (@lem7196064 (x = (i _96438)) (@I (B -> Prop) t _96438)). Qed.
Lemma lem7196067 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7196068 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (_96438 : B) : (term710 A B x i t _96438) = (term711 A B x i t _96438).
Proof. exact (@lem7196067 (term712 A B x i t _96438)). Qed.
Lemma lem7196069 {A B : Type'} (x : A) (i : B -> A) (t : B -> Prop) (_96438 : B) : (term639 A B x i t _96438) = (term711 A B x i t _96438).
Proof. exact (TRANS (@lem7196065 A B x i t _96438) (@lem7196068 A B x i t _96438)). Qed.
Lemma lem7196071 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term624 A B i f y g t s) : term713 A B i t y x.
Proof. exact (conj (@lem7196002 A B x i f y g t s h1 h2) (@lem7196062 A B x i f y g t s h1 h2)). Qed.
Lemma lem7196073 {A B : Type'} (_96438 : B) (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term711 A B x i t _96438.
Proof. exact (EQ_MP (@lem7196069 A B x i t _96438) (@lem7195635 A B _96438 x i t h1)). Qed.
Lemma lem7196074 {A B : Type'} (_96438 : B) (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term711 A B x i t _96438.
Proof. exact (@lem7196073 A B _96438 x i t h1). Qed.
Lemma lem7196075 {A B : Type'} (y : A -> B) (x : A) (i : B -> A) (t : B -> Prop) (h1 : term562 A B x i t) : term714 A B i t y x.
Proof. exact (@lem7196074 A B (y x) x i t h1). Qed.
Lemma lem7196078 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term624 A B i f y g t s) : False.
Proof. exact (@lem7196075 A B y x i t h1 (@lem7196071 A B x i f y g t s h2 h3)). Qed.
Lemma lem7196079 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term624 A B i f y g t s) : term482.
Proof. exact (fun h0 : ~ False => @lem7196078 A B x i f y g t s h1 h2 h3). Qed.
Lemma lem7196081 (p : Prop) : (term480 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7196082 : term482 = False.
Proof. exact (@lem7196081 False). Qed.
Lemma lem7196083 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (y : A -> B) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term624 A B i f y g t s) : False.
Proof. exact (EQ_MP (@lem7196082) (@lem7196079 A B x i f y g t s h1 h2 h3)). Qed.
Lemma lem7196084 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term517 A B i f g t s) : False.
Proof. exact (ex_elim (@lem7195330 A B i f g t s h3) (fun y : A -> B => fun h0 : term626 A B i f g t s y => @lem7196083 A B x i f y g t s h1 h2 h0)). Qed.
Lemma lem7196085 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term517 A B i f g t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem7196084 A B x i f g t s h1 h2 h3) (fun h4 : False => @lem7195336 A s x h2)). Qed.
Lemma lem7196086 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term517 A B i f g t s) : False.
Proof. exact (EQ_MP (@lem7196085 A B x i f g t s h1 h2 h3) (@lem7195336 A s x h2)). Qed.
Lemma lem7196087 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term517 A B i f g t s) : (term562 A B x i t) = False.
Proof. exact (prop_ext (fun h4 : term562 A B x i t => @lem7196086 A B x i f g t s h1 h2 h3) (fun h4 : False => @lem7195077 A B x i t h1)). Qed.
Lemma lem7196088 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term562 A B x i t) (h2 : s x) (h3 : term517 A B i f g t s) : False.
Proof. exact (EQ_MP (@lem7196087 A B x i f g t s h1 h2 h3) (@lem7195077 A B x i t h1)). Qed.
Lemma lem7196089 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term517 A B i f g t s) : term561 A B x i t.
Proof. exact (fun h0 : term562 A B x i t => @lem7196088 A B x i f g t s h0 h1 h2). Qed.
Lemma lem7196090 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term517 A B i f g t s) : term528 A B x i t.
Proof. exact (EQ_MP (@lem7195076 A B x i t) (@lem7196089 A B x i f g t s h1 h2)). Qed.
Lemma lem7196091 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term517 A B i f g t s) : term530 A B s x i t.
Proof. exact (fun h0 : s x => @lem7196090 A B x i f g t s h0 h1). Qed.
Lemma lem7196096 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (s : A -> Prop) (h1 : term517 A B i f g t s) : term533 A B s i t.
Proof. exact (fun x : A => @lem7196091 A B x i f g t s h1). Qed.
Lemma lem7196097 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term534 A B f g s i t.
Proof. exact (fun h0 : term517 A B i f g t s => @lem7196096 A B i f g t s h0). Qed.
Lemma lem7196102 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term544 A B g s i t.
Proof. exact (fun f : A -> real => @lem7196097 A B f g s i t). Qed.
Lemma lem7196107 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term548 A B s i t.
Proof. exact (fun g : B -> real => @lem7196102 A B g s i t). Qed.
Lemma lem7196112 {A B : Type'} (i : B -> A) (t : B -> Prop) : term552 A B i t.
Proof. exact (fun s : A -> Prop => @lem7196107 A B s i t). Qed.
Lemma lem7196117 {A B : Type'} (t : B -> Prop) : term556 A B t.
Proof. exact (fun i : B -> A => @lem7196112 A B i t). Qed.
Lemma lem7196122 {A B : Type'} : term560 A B.
Proof. exact (fun t : B -> Prop => @lem7196117 A B t). Qed.
Lemma lem7196123 {A B : Type'} : term559 A B.
Proof. exact (EQ_MP (@lem7195070 A B) (@lem7196122 A B)). Qed.
Lemma lem7196124 {A B : Type'} (t : B -> Prop) : term715 A B t.
Proof. exact (@lem7196123 A B t). Qed.
Lemma lem7196125 {A B : Type'} (t : B -> Prop) : (term715 A B t) = (term555 A B t).
Proof. exact (eq_refl (term715 A B t)). Qed.
Lemma lem7196126 {A B : Type'} (t : B -> Prop) : term555 A B t.
Proof. exact (EQ_MP (@lem7196125 A B t) (@lem7196124 A B t)). Qed.
Lemma lem7196127 {A B : Type'} (t : B -> Prop) (i : B -> A) : term716 A B t i.
Proof. exact (@lem7196126 A B t i). Qed.
Lemma lem7196128 {A B : Type'} (i : B -> A) (t : B -> Prop) : (term716 A B t i) = (term551 A B i t).
Proof. exact (eq_refl (term716 A B t i)). Qed.
Lemma lem7196129 {A B : Type'} (i : B -> A) (t : B -> Prop) : term551 A B i t.
Proof. exact (EQ_MP (@lem7196128 A B i t) (@lem7196127 A B t i)). Qed.
Lemma lem7196130 {A B : Type'} (i : B -> A) (t : B -> Prop) (s : A -> Prop) : term717 A B i t s.
Proof. exact (@lem7196129 A B i t s). Qed.
Lemma lem7196131 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term717 A B i t s) = (term547 A B s i t).
Proof. exact (eq_refl (term717 A B i t s)). Qed.
Lemma lem7196132 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term547 A B s i t.
Proof. exact (EQ_MP (@lem7196131 A B s i t) (@lem7196130 A B i t s)). Qed.
Lemma lem7196133 {A B : Type'} (s : A -> Prop) (i : B -> A) (t : B -> Prop) (g : B -> real) : term718 A B s i t g.
Proof. exact (@lem7196132 A B s i t g). Qed.
Lemma lem7196134 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term718 A B s i t g) = (term543 A B g s i t).
Proof. exact (eq_refl (term718 A B s i t g)). Qed.
Lemma lem7196135 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term543 A B g s i t.
Proof. exact (EQ_MP (@lem7196134 A B g s i t) (@lem7196133 A B s i t g)). Qed.
Lemma lem7196136 {A B : Type'} (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (f : A -> real) : term719 A B g s i t f.
Proof. exact (@lem7196135 A B g s i t f). Qed.
Lemma lem7196137 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : (term719 A B g s i t f) = (term535 A B f g s i t).
Proof. exact (eq_refl (term719 A B g s i t f)). Qed.
Lemma lem7196138 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term535 A B f g s i t.
Proof. exact (EQ_MP (@lem7196137 A B f g s i t) (@lem7196136 A B g s i t f)). Qed.
Lemma lem7196140 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term535 A B f g s i t.
Proof. exact (@lem7194757 A B f g s i t (@lem7196138 A B f g s i t)). Qed.
Lemma lem7196141 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term536 A B f g s i t) : False.
Proof. exact (@lem7196140 A B f g s i t (@lem7194741 A B f g s i t h1)). Qed.
Lemma lem7196142 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term536 A B f g s i t) : (term536 A B f g s i t) = False.
Proof. exact (prop_ext (fun h2 : term536 A B f g s i t => @lem7196141 A B f g s i t h1) (fun h2 : False => @lem7194741 A B f g s i t h1)). Qed.
Lemma lem7196143 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) (h1 : term536 A B f g s i t) : False.
Proof. exact (EQ_MP (@lem7196142 A B f g s i t h1) (@lem7194741 A B f g s i t h1)). Qed.
Lemma lem7196144 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term535 A B f g s i t.
Proof. exact (fun h0 : term536 A B f g s i t => @lem7196143 A B f g s i t h0). Qed.
Lemma lem7196145 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term534 A B f g s i t.
Proof. exact (EQ_MP (@lem7194740 A B f g s i t) (@lem7196144 A B f g s i t)). Qed.
Lemma lem7196146 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term507 A B f g s i t.
Proof. exact (EQ_MP (@lem7194736 A B f g s i t) (@lem7196145 A B f g s i t)). Qed.
Lemma lem7196147 {A B : Type'} (f : A -> real) (g : B -> real) (s : A -> Prop) (i : B -> A) (t : B -> Prop) : term506 A B f g s i t.
Proof. exact (EQ_MP (@lem7194589 A B f g s i t) (@lem7196146 A B f g s i t)). Qed.
Lemma lem7196148 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term278 A B s i t.
Proof. exact (@lem7196147 A B f g s i t (@lem7194542 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196149 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term190 A B s t i g.
Proof. exact (EQ_MP (@lem7192072 A B s i t g h2) (@lem7196148 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196151 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term191 A B s t i g.
Proof. exact (EQ_MP (@lem7191592 A B s i g t h4) (@lem7196149 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196152 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term223 A B t i x y g.
Proof. exact (EQ_MP (@lem7191851 A B i x y g t h3) (@lem7194529 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7196153 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term720 A B s t i g.
Proof. exact (@lem7191141 A B s t i g (@lem7196151 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196154 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term721 A B y t i x g.
Proof. exact (@lem7191123 A B y t i x g (@lem7196152 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7196155 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term722 A B f y t i x g.
Proof. exact (conj (@lem7191119 A B f x g y h7) (@lem7196154 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7196156 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term723 A B f t i x g.
Proof. exact (ex_intro (term724 A B f t i x g) (term149 B y g) (@lem7196155 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7196157 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term103 A B f t i x g.
Proof. exact (@lem7191087 A B f t i x g (@lem7196156 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem7196158 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term130 A B t i f x g y) : term143 A B i f x g y.
Proof. exact (proj2 (@lem7191080 A B t i f x g y h1)). Qed.
Lemma lem7196159 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term130 A B t i f x g y) : @IN B y t.
Proof. exact (proj1 (@lem7191080 A B t i f x g y h1)). Qed.
Lemma lem7196160 {A B : Type'} (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term143 A B i f x g y) : term144 A B f x g y.
Proof. exact (proj2 (@lem7191081 A B i f x g y h1)). Qed.
Lemma lem7196161 {A B : Type'} (i : B -> A) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term143 A B i f x g y) : (i y) = x.
Proof. exact (proj1 (@lem7191081 A B i f x g y h1)). Qed.
Lemma lem7196162 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : (term144 A B f x g y) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h8 : term144 A B f x g y => @lem7196157 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7) (fun h8 : term103 A B f t i x g => @lem7191083 A B f x g y h7)). Qed.
Lemma lem7196163 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196162 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7) (@lem7191083 A B f x g y h7)). Qed.
Lemma lem7196164 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : ((i y) = x) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h8 : (i y) = x => @lem7196163 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7) (fun h8 : term103 A B f t i x g => @lem7191084 A B i y x h4)). Qed.
Lemma lem7196165 {A B : Type'} (i : B -> A) (s : A -> Prop) (t : B -> Prop) (f : A -> real) (x : A) (g : B -> real) (y : B) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (i y) = x) (h5 : @IN A x s) (h6 : @IN B y t) (h7 : term144 A B f x g y) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196164 A B i s t f x g y h1 h2 h3 h4 h5 h6 h7) (@lem7191084 A B i y x h4)). Qed.
Lemma lem7196166 {A B : Type'} (f : A -> real) (g : B -> real) (i : B -> A) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : (i y) = x) (h6 : @IN A x s) (h7 : @IN B y t) : (term144 A B f x g y) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h8 : term144 A B f x g y => @lem7196165 A B i s t f x g y h1 h2 h3 h5 h6 h7 h8) (fun h8 : term103 A B f t i x g => @lem7196160 A B i f x g y h4)). Qed.
Lemma lem7196167 {A B : Type'} (f : A -> real) (g : B -> real) (i : B -> A) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : (i y) = x) (h6 : @IN A x s) (h7 : @IN B y t) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196166 A B f g i x s y t h1 h2 h3 h4 h5 h6 h7) (@lem7196160 A B i f x g y h4)). Qed.
Lemma lem7196168 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : ((i y) = x) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h7 : (i y) = x => @lem7196167 A B f g i x s y t h1 h2 h3 h4 h7 h5 h6) (fun h7 : term103 A B f t i x g => @lem7196161 A B i f x g y h4)). Qed.
Lemma lem7196169 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196168 A B i f g x s y t h1 h2 h3 h4 h5 h6) (@lem7196161 A B i f x g y h4)). Qed.
Lemma lem7196170 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : (@IN B y t) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h7 : @IN B y t => @lem7196169 A B i f g x s y t h1 h2 h3 h4 h5 h6) (fun h7 : term103 A B f t i x g => @lem7191082 B y t h6)). Qed.
Lemma lem7196171 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term143 A B i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196170 A B i f g x s y t h1 h2 h3 h4 h5 h6) (@lem7191082 B y t h6)). Qed.
Lemma lem7196172 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term130 A B t i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : (term143 A B i f x g y) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h7 : term143 A B i f x g y => @lem7196171 A B i f g x s y t h1 h2 h3 h7 h5 h6) (fun h7 : term103 A B f t i x g => @lem7196158 A B t i f x g y h4)). Qed.
Lemma lem7196173 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term130 A B t i f x g y) (h5 : @IN A x s) (h6 : @IN B y t) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196172 A B i f g x s y t h1 h2 h3 h4 h5 h6) (@lem7196158 A B t i f x g y h4)). Qed.
Lemma lem7196174 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : B) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term130 A B t i f x g y) (h5 : @IN A x s) : (@IN B y t) = (term103 A B f t i x g).
Proof. exact (prop_ext (fun h6 : @IN B y t => @lem7196173 A B i f g x s y t h1 h2 h3 h4 h5 h6) (fun h6 : term103 A B f t i x g => @lem7196159 A B t i f x g y h4)). Qed.
Lemma lem7196175 {A B : Type'} (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (y : B) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term130 A B t i f x g y) (h5 : @IN A x s) : term103 A B f t i x g.
Proof. exact (EQ_MP (@lem7196174 A B t i f g y x s h1 h2 h3 h4 h5) (@lem7196159 A B t i f x g y h4)). Qed.
Lemma lem7196176 {A B : Type'} (y : B) (f : A -> real) (i : B -> A) (g : B -> real) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : @IN A x s) : term139 A B y f t i x g.
Proof. exact (fun h0 : term130 A B t i f x g y => @lem7196175 A B t i f g y x s h1 h2 h3 h0 h4). Qed.
Lemma lem7196181 {A B : Type'} (f : A -> real) (i : B -> A) (g : B -> real) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : @IN A x s) : term142 A B f t i x g.
Proof. exact (fun y : B => @lem7196176 A B y f i g t x s h1 h2 h3 h4). Qed.
Lemma lem7196182 {A B : Type'} (f : A -> real) (i : B -> A) (g : B -> real) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : @IN A x s) : term124 A B s f t i x g.
Proof. exact (EQ_MP (@lem7191079 A B f t i g x s h4) (@lem7196181 A B f i g t x s h1 h2 h3 h4)). Qed.
Lemma lem7196183 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (t : B -> Prop) (x : A) (s : A -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : @IN A x s) : term103 A B f t i x g.
Proof. exact (@lem7196182 A B f i g t x s h2 h3 h4 h5 (@lem7190970 A B x s t i f g h1)). Qed.
Lemma lem7196184 {A B : Type'} (x : A) (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term106 A B s f t i x g.
Proof. exact (fun h0 : @IN A x s => @lem7196183 A B i f g t x s h1 h2 h3 h4 h0). Qed.
Lemma lem7196189 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term110 A B s f t i g.
Proof. exact (fun x : A => @lem7196184 A B x i f g s t h1 h2 h3 h4). Qed.
Lemma lem7196190 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term111 A B s f t i g.
Proof. exact (EQ_MP (@lem7190966 A B f t i g s h3) (@lem7196189 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196191 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term725 A B f s t i g.
Proof. exact (@lem7190886 A B f s t i g (@lem7196190 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196192 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term726 A B f s t i g.
Proof. exact (conj (@lem7196191 A B i f g s t h1 h2 h3 h4) (@lem7196153 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196193 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term727 A B s f t i g.
Proof. exact (ex_intro (term728 A B s f t i g) (term729 A B s t i g) (@lem7196192 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196194 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term730 A B s f t i g.
Proof. exact (@lem7190882 A B s f t i g (@lem7196193 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196195 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term731 A B s f i t g.
Proof. exact (conj (@lem7196194 A B i f g s t h1 h2 h3 h4) (@lem7190879 A B i g t h4)). Qed.
Lemma lem7196196 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term732 A B s f t g.
Proof. exact (ex_intro (term733 A B s f t g) (term86 A B t i g) (@lem7196195 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196197 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term734 A B s f t g.
Proof. exact (@lem7190852 A B s f t g (@lem7196196 A B i f g s t h1 h2 h3 h4)). Qed.
Lemma lem7196198 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term79 A B s t i f g) : term80 A B s t i f g.
Proof. exact (proj2 (@lem7190843 A B s t i f g h1)). Qed.
Lemma lem7196199 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term79 A B s t i f g) : @FINITE A s.
Proof. exact (proj1 (@lem7190843 A B s t i f g h1)). Qed.
Lemma lem7196200 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term80 A B s t i f g) : term81 A B s t i f g.
Proof. exact (proj2 (@lem7190844 A B s t i f g h1)). Qed.
Lemma lem7196201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term80 A B s t i f g) : @FINITE B t.
Proof. exact (proj1 (@lem7190844 A B s t i f g h1)). Qed.
Lemma lem7196202 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term81 A B s t i f g) : term82 A B s t i f g.
Proof. exact (proj2 (@lem7190846 A B s t i f g h1)). Qed.
Lemma lem7196203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term81 A B s t i f g) : term83 B t g.
Proof. exact (proj1 (@lem7190846 A B s t i f g h1)). Qed.
Lemma lem7196204 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : (term82 A B s t i f g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h5 : term82 A B s t i f g => @lem7196197 A B i f g s t h1 h2 h3 h4) (fun h5 : term734 A B s f t g => @lem7190848 A B s t i f g h1)). Qed.
Lemma lem7196205 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196204 A B i f g s t h1 h2 h3 h4) (@lem7190848 A B s t i f g h1)). Qed.
Lemma lem7196206 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : (term83 B t g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h5 : term83 B t g => @lem7196205 A B i f g s t h1 h2 h3 h4) (fun h5 : term734 A B s f t g => @lem7190849 B t g h2)). Qed.
Lemma lem7196207 {A B : Type'} (i : B -> A) (f : A -> real) (g : B -> real) (s : A -> Prop) (t : B -> Prop) (h1 : term82 A B s t i f g) (h2 : term83 B t g) (h3 : @FINITE A s) (h4 : @FINITE B t) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196206 A B i f g s t h1 h2 h3 h4) (@lem7190849 B t g h2)). Qed.
Lemma lem7196208 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term81 A B s t i f g) : (term82 A B s t i f g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h5 : term82 A B s t i f g => @lem7196207 A B i f g s t h5 h1 h2 h3) (fun h5 : term734 A B s f t g => @lem7196202 A B s t i f g h4)). Qed.
Lemma lem7196209 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term83 B t g) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term81 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196208 A B s t i f g h1 h2 h3 h4) (@lem7196202 A B s t i f g h4)). Qed.
Lemma lem7196210 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term81 A B s t i f g) : (term83 B t g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h4 : term83 B t g => @lem7196209 A B s t i f g h4 h1 h2 h3) (fun h4 : term734 A B s f t g => @lem7196203 A B s t i f g h3)). Qed.
Lemma lem7196211 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term81 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196210 A B s t i f g h1 h2 h3) (@lem7196203 A B s t i f g h3)). Qed.
Lemma lem7196212 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term81 A B s t i f g) : (@FINITE B t) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem7196211 A B s t i f g h1 h2 h3) (fun h4 : term734 A B s f t g => @lem7190847 B t h2)). Qed.
Lemma lem7196213 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term81 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196212 A B s t i f g h1 h2 h3) (@lem7190847 B t h2)). Qed.
Lemma lem7196214 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term80 A B s t i f g) : (term81 A B s t i f g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h4 : term81 A B s t i f g => @lem7196213 A B s t i f g h1 h2 h4) (fun h4 : term734 A B s f t g => @lem7196200 A B s t i f g h3)). Qed.
Lemma lem7196215 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term80 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196214 A B s t i f g h1 h2 h3) (@lem7196200 A B s t i f g h3)). Qed.
Lemma lem7196216 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term80 A B s t i f g) : (@FINITE B t) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem7196215 A B s t i f g h1 h3 h2) (fun h3 : term734 A B s f t g => @lem7196201 A B s t i f g h2)). Qed.
Lemma lem7196217 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term80 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196216 A B s t i f g h1 h2) (@lem7196201 A B s t i f g h2)). Qed.
Lemma lem7196218 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term80 A B s t i f g) : (@FINITE A s) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7196217 A B s t i f g h1 h2) (fun h3 : term734 A B s f t g => @lem7190845 A s h1)). Qed.
Lemma lem7196219 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term80 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196218 A B s t i f g h1 h2) (@lem7190845 A s h1)). Qed.
Lemma lem7196220 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term79 A B s t i f g) : (term80 A B s t i f g) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h3 : term80 A B s t i f g => @lem7196219 A B s t i f g h1 h3) (fun h3 : term734 A B s f t g => @lem7196198 A B s t i f g h2)). Qed.
Lemma lem7196221 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : @FINITE A s) (h2 : term79 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196220 A B s t i f g h1 h2) (@lem7196198 A B s t i f g h2)). Qed.
Lemma lem7196222 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term79 A B s t i f g) : (@FINITE A s) = (term734 A B s f t g).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7196221 A B s t i f g h2 h1) (fun h2 : term734 A B s f t g => @lem7196199 A B s t i f g h1)). Qed.
Lemma lem7196223 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (i : B -> A) (f : A -> real) (g : B -> real) (h1 : term79 A B s t i f g) : term734 A B s f t g.
Proof. exact (EQ_MP (@lem7196222 A B s t i f g h1) (@lem7196199 A B s t i f g h1)). Qed.
Lemma lem7196224 {A B : Type'} (i : B -> A) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : term735 A B i s f t g.
Proof. exact (fun h0 : term79 A B s t i f g => @lem7196223 A B s t i f g h0). Qed.
Lemma lem7196229 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : term736 A B s f t g.
Proof. exact (fun i : B -> A => @lem7196224 A B i s f t g). Qed.
Lemma lem7196234 {A B : Type'} (s : A -> Prop) (f : A -> real) (g : B -> real) : term737 A B s f g.
Proof. exact (fun t : B -> Prop => @lem7196229 A B s f t g). Qed.
Lemma lem7196239 {A B : Type'} (f : A -> real) (g : B -> real) : term738 A B f g.
Proof. exact (fun s : A -> Prop => @lem7196234 A B s f g). Qed.
Lemma lem7196244 {A B : Type'} (f : A -> real) : term739 A B f.
Proof. exact (fun g : B -> real => @lem7196239 A B f g). Qed.
Lemma lem7196249 {A B : Type'} : term740 A B.
Proof. exact (fun f : A -> real => @lem7196244 A B f). Qed.

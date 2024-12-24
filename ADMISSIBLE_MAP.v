Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_MAP_term_abbrevs.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import MAP_EQ_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm7_spec.
Lemma lem8225712 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8225713 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8225714 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8225713 t1) (@lem8225712 t1)). Qed.
Lemma lem8225715 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8225714 t1 t2). Qed.
Lemma lem8225716 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8225717 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8225716 t1 t2) (@lem8225715 t1 t2)). Qed.
Lemma lem8225718 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8225717 t1 t2 t3). Qed.
Lemma lem8225719 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8225720 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8225719 t1 t2 t3) (@lem8225718 t1 t2 t3)). Qed.
Lemma lem8225721 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8225720 t1 t2 t3)). Qed.
Lemma lem8225724 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem8225725 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem8225724 _26777 P l h1)). Qed.
Lemma lem8225726 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem8225727 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem8225726 _26777 l P h1)). Qed.
Lemma lem8225728 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem8225725 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem8225727 _26777 l P h1)). Qed.
Lemma lem8225729 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem8225728 _26777 l P)). Qed.
Lemma lem8225730 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem8225731 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem8225730 _26777) (@lem8225729 _26777 P)). Qed.
Lemma lem8225732 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem8225731 _26777 P)). Qed.
Lemma lem8225733 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem8225734 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem8225733 _26777) (@lem8225732 _26777)). Qed.
Lemma lem8225735 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem8225734 _26777) (@lem1138070 _26777)). Qed.
Lemma lem8225736 {_26777 : Type'} (P : _26777 -> Prop) : term16 _26777 P.
Proof. exact (@lem8225735 _26777 P). Qed.
Lemma lem8225737 {_26777 : Type'} (P : _26777 -> Prop) : (term16 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term16 _26777 P)). Qed.
Lemma lem8225738 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem8225737 _26777 P) (@lem8225736 _26777 P)). Qed.
Lemma lem8225739 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term17 _26777 P l.
Proof. exact (@lem8225738 _26777 P l). Qed.
Lemma lem8225740 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term17 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term17 _26777 P l)). Qed.
Lemma lem8225742 {_26299 _26310 : Type'} (h1 : term18 _26299 _26310) : term18 _26299 _26310.
Proof. exact (h1). Qed.
Lemma lem8225743 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h1 : term18 _26299 _26310) : term19 _26299 _26310 f.
Proof. exact (@lem8225742 _26299 _26310 h1 f). Qed.
Lemma lem8225744 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term19 _26299 _26310 f) = (term20 _26299 _26310 f).
Proof. exact (eq_refl (term19 _26299 _26310 f)). Qed.
Lemma lem8225745 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h1 : term18 _26299 _26310) : term20 _26299 _26310 f.
Proof. exact (EQ_MP (@lem8225744 _26299 _26310 f) (@lem8225743 _26299 _26310 f h1)). Qed.
Lemma lem8225746 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h1 : term18 _26299 _26310) : term21 _26299 _26310 f g.
Proof. exact (@lem8225745 _26299 _26310 f h1 g). Qed.
Lemma lem8225747 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term21 _26299 _26310 f g) = (term22 _26299 _26310 f g).
Proof. exact (eq_refl (term21 _26299 _26310 f g)). Qed.
Lemma lem8225748 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h1 : term18 _26299 _26310) : term22 _26299 _26310 f g.
Proof. exact (EQ_MP (@lem8225747 _26299 _26310 f g) (@lem8225746 _26299 _26310 f g h1)). Qed.
Lemma lem8225749 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term18 _26299 _26310) : term23 _26299 _26310 f g l.
Proof. exact (@lem8225748 _26299 _26310 f g h1 l). Qed.
Lemma lem8225750 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) : (term23 _26299 _26310 f g l) = (term24 _26299 _26310 f g l).
Proof. exact (eq_refl (term23 _26299 _26310 f g l)). Qed.
Lemma lem8225751 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term18 _26299 _26310) : term24 _26299 _26310 f g l.
Proof. exact (EQ_MP (@lem8225750 _26299 _26310 f g l) (@lem8225749 _26299 _26310 f g l h1)). Qed.
Lemma lem8225752 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term25 _26299 _26310 f g l) : term25 _26299 _26310 f g l.
Proof. exact (h1). Qed.
Lemma lem8225753 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term18 _26299 _26310) (h2 : term25 _26299 _26310 f g l) : (@List.map _26299 _26310 f l) = (@List.map _26299 _26310 g l).
Proof. exact (@lem8225751 _26299 _26310 f g l h1 (@lem8225752 _26299 _26310 f g l h2)). Qed.
Lemma lem8225754 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term25 _26299 _26310 f g l) : term26 _26299 _26310 f g l.
Proof. exact (fun h0 : term18 _26299 _26310 => @lem8225753 _26299 _26310 f g l h0 h1). Qed.
Lemma lem8225755 {_26299 _26310 : Type'} (h1 : term18 _26299 _26310) : term18 _26299 _26310.
Proof. exact (h1). Qed.
Lemma lem8225756 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term18 _26299 _26310) (h2 : term25 _26299 _26310 f g l) : (@List.map _26299 _26310 f l) = (@List.map _26299 _26310 g l).
Proof. exact (@lem8225754 _26299 _26310 f g l h2 (@lem8225755 _26299 _26310 h1)). Qed.
Lemma lem8225757 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) (h1 : term18 _26299 _26310) : term24 _26299 _26310 f g l.
Proof. exact (fun h0 : term25 _26299 _26310 f g l => @lem8225756 _26299 _26310 f g l h1 h0). Qed.
Lemma lem8225758 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h1 : term18 _26299 _26310) : term22 _26299 _26310 f g.
Proof. exact (fun l : list _26299 => @lem8225757 _26299 _26310 f g l h1). Qed.
Lemma lem8225759 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h1 : term18 _26299 _26310) : term20 _26299 _26310 f.
Proof. exact (fun g : _26299 -> _26310 => @lem8225758 _26299 _26310 f g h1). Qed.
Lemma lem8225760 {_26299 _26310 : Type'} (h1 : term18 _26299 _26310) : term18 _26299 _26310.
Proof. exact (fun f : _26299 -> _26310 => @lem8225759 _26299 _26310 f h1). Qed.
Lemma lem8225761 {_26299 _26310 : Type'} : term27 _26299 _26310.
Proof. exact (fun h0 : term18 _26299 _26310 => @lem8225760 _26299 _26310 h0). Qed.
Lemma lem8225762 {_26299 _26310 : Type'} : term18 _26299 _26310.
Proof. exact (@lem8225761 _26299 _26310 (@lem1120972 _26299 _26310)). Qed.
Lemma lem8225763 {_26299 _26310 : Type'} (f : _26299 -> _26310) : term19 _26299 _26310 f.
Proof. exact (@lem8225762 _26299 _26310 f). Qed.
Lemma lem8225764 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term19 _26299 _26310 f) = (term20 _26299 _26310 f).
Proof. exact (eq_refl (term19 _26299 _26310 f)). Qed.
Lemma lem8225765 {_26299 _26310 : Type'} (f : _26299 -> _26310) : term20 _26299 _26310 f.
Proof. exact (EQ_MP (@lem8225764 _26299 _26310 f) (@lem8225763 _26299 _26310 f)). Qed.
Lemma lem8225766 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term21 _26299 _26310 f g.
Proof. exact (@lem8225765 _26299 _26310 f g). Qed.
Lemma lem8225767 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term21 _26299 _26310 f g) = (term22 _26299 _26310 f g).
Proof. exact (eq_refl (term21 _26299 _26310 f g)). Qed.
Lemma lem8225768 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term22 _26299 _26310 f g.
Proof. exact (EQ_MP (@lem8225767 _26299 _26310 f g) (@lem8225766 _26299 _26310 f g)). Qed.
Lemma lem8225769 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) : term23 _26299 _26310 f g l.
Proof. exact (@lem8225768 _26299 _26310 f g l). Qed.
Lemma lem8225770 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) : (term23 _26299 _26310 f g l) = (term24 _26299 _26310 f g l).
Proof. exact (eq_refl (term23 _26299 _26310 f g l)). Qed.
Lemma lem8225772 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8225773 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8225774 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8225773 t1) (@lem8225772 t1)). Qed.
Lemma lem8225775 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8225774 t1 t2). Qed.
Lemma lem8225776 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8225777 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8225776 t1 t2) (@lem8225775 t1 t2)). Qed.
Lemma lem8225778 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8225777 t1 t2 t3). Qed.
Lemma lem8225779 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8225780 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8225779 t1 t2 t3) (@lem8225778 t1 t2 t3)). Qed.
Lemma lem8225781 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8225780 t1 t2 t3)). Qed.
Lemma lem8225793 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8225794 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term29 _144870 _144886 f x g y) = (term30 _144870 _144886 f x g y).
Proof. exact (@lem8225793 (term29 _144870 _144886 f x g y)). Qed.
Lemma lem8225795 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term30 _144870 _144886 f x g y) = (term29 _144870 _144886 f x g y).
Proof. exact (SYM (@lem8225794 _144870 _144886 f x g y)). Qed.
Lemma lem8225796 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term31 _144870 _144886 f x g y) : term31 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225799 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term30 _144870 _144886 f x g y) : term30 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225800 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term32 _144870 _144886 f x g y.
Proof. exact (fun h0 : term30 _144870 _144886 f x g y => @lem8225799 _144870 _144886 f x g y h0). Qed.
Lemma lem8225801 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term32 _144870 _144886 f x g y) : term32 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225802 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term30 _144870 _144886 f x g y) : term30 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225803 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term30 _144870 _144886 f x g y) (h2 : term32 _144870 _144886 f x g y) : term30 _144870 _144886 f x g y.
Proof. exact (@lem8225801 _144870 _144886 f x g y h2 (@lem8225802 _144870 _144886 f x g y h1)). Qed.
Lemma lem8225804 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term30 _144870 _144886 f x g y) : term33 _144870 _144886 f x g y.
Proof. exact (fun h0 : term32 _144870 _144886 f x g y => @lem8225803 _144870 _144886 f x g y h1 h0). Qed.
Lemma lem8225805 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term32 _144870 _144886 f x g y) : term32 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225806 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term30 _144870 _144886 f x g y) (h2 : term32 _144870 _144886 f x g y) : term30 _144870 _144886 f x g y.
Proof. exact (@lem8225804 _144870 _144886 f x g y h1 (@lem8225805 _144870 _144886 f x g y h2)). Qed.
Lemma lem8225807 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term32 _144870 _144886 f x g y) : term32 _144870 _144886 f x g y.
Proof. exact (fun h0 : term30 _144870 _144886 f x g y => @lem8225806 _144870 _144886 f x g y h0 h1). Qed.
Lemma lem8225808 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term34 _144870 _144886 f x g y.
Proof. exact (fun h0 : term32 _144870 _144886 f x g y => @lem8225807 _144870 _144886 f x g y h0). Qed.
Lemma lem8225811 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term32 _144870 _144886 f x g y.
Proof. exact (@lem8225808 _144870 _144886 f x g y (@lem8225800 _144870 _144886 f x g y)). Qed.
Lemma lem8225812 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term32 _144870 _144886 f x g y.
Proof. exact (@lem8225811 _144870 _144886 f x g y). Qed.
Lemma lem8225830 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8225831 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term30 _144870 _144886 f x g y) = (term35 _144870 _144886 f x g y).
Proof. exact (@lem8225830 (term31 _144870 _144886 f x g y)). Qed.
Lemma lem8225833 (t : Prop) : (term36 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8225834 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term35 _144870 _144886 f x g y) = (term29 _144870 _144886 f x g y).
Proof. exact (@lem8225833 (term29 _144870 _144886 f x g y)). Qed.
Lemma lem8225837 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term30 _144870 _144886 f x g y) = (term29 _144870 _144886 f x g y).
Proof. exact (TRANS (@lem8225831 _144870 _144886 f x g y) (@lem8225834 _144870 _144886 f x g y)). Qed.
Lemma lem8225840 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term37 _144870 _144886 x g y) = (term38 _144870 _144886 x g y).
Proof. exact (fun_ext (fun f : _144870 -> _144886 => @lem8225837 _144870 _144886 f x g y)). Qed.
Lemma lem8225841 {_144870 _144886 : Type'} : (@all (_144870 -> _144886)) = (@all (_144870 -> _144886)).
Proof. exact (eq_refl (@all (_144870 -> _144886))). Qed.
Lemma lem8225842 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term39 _144870 _144886 x g y) = (term40 _144870 _144886 x g y).
Proof. exact (MK_COMB (@lem8225841 _144870 _144886) (@lem8225840 _144870 _144886 x g y)). Qed.
Lemma lem8225847 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : (term41 _144870 _144886 g y) = (term42 _144870 _144886 g y).
Proof. exact (fun_ext (fun x : list _144870 => @lem8225842 _144870 _144886 x g y)). Qed.
Lemma lem8225848 {_144870 : Type'} : (@all (list _144870)) = (@all (list _144870)).
Proof. exact (eq_refl (@all (list _144870))). Qed.
Lemma lem8225849 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : (term43 _144870 _144886 g y) = (term44 _144870 _144886 g y).
Proof. exact (MK_COMB (@lem8225848 _144870) (@lem8225847 _144870 _144886 g y)). Qed.
Lemma lem8225854 {_144870 _144886 : Type'} (y : list _144870) : (term45 _144870 _144886 y) = (term46 _144870 _144886 y).
Proof. exact (fun_ext (fun g : _144870 -> _144886 => @lem8225849 _144870 _144886 g y)). Qed.
Lemma lem8225855 {_144870 _144886 : Type'} : (@all (_144870 -> _144886)) = (@all (_144870 -> _144886)).
Proof. exact (eq_refl (@all (_144870 -> _144886))). Qed.
Lemma lem8225856 {_144870 _144886 : Type'} (y : list _144870) : (term47 _144870 _144886 y) = (term48 _144870 _144886 y).
Proof. exact (MK_COMB (@lem8225855 _144870 _144886) (@lem8225854 _144870 _144886 y)). Qed.
Lemma lem8225861 {_144870 _144886 : Type'} : (term49 _144870 _144886) = (term50 _144870 _144886).
Proof. exact (fun_ext (fun y : list _144870 => @lem8225856 _144870 _144886 y)). Qed.
Lemma lem8225862 {_144870 : Type'} : (@all (list _144870)) = (@all (list _144870)).
Proof. exact (eq_refl (@all (list _144870))). Qed.
Lemma lem8225871 {_144870 _144886 : Type'} : (term51 _144870 _144886) = (term52 _144870 _144886).
Proof. exact (MK_COMB (@lem8225862 _144870) (@lem8225861 _144870 _144886)). Qed.
Lemma lem8225880 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term29 _144870 _144886 f x g y) = (term29 _144870 _144886 f x g y).
Proof. exact (eq_refl (term29 _144870 _144886 f x g y)). Qed.
Lemma lem8225881 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term38 _144870 _144886 x g y) = (term38 _144870 _144886 x g y).
Proof. exact (fun_ext (fun f : _144870 -> _144886 => @lem8225880 _144870 _144886 f x g y)). Qed.
Lemma lem8225882 {_144870 _144886 : Type'} : (@all (_144870 -> _144886)) = (@all (_144870 -> _144886)).
Proof. exact (eq_refl (@all (_144870 -> _144886))). Qed.
Lemma lem8225883 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term40 _144870 _144886 x g y) = (term40 _144870 _144886 x g y).
Proof. exact (MK_COMB (@lem8225882 _144870 _144886) (@lem8225881 _144870 _144886 x g y)). Qed.
Lemma lem8225884 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : (term42 _144870 _144886 g y) = (term42 _144870 _144886 g y).
Proof. exact (fun_ext (fun x : list _144870 => @lem8225883 _144870 _144886 x g y)). Qed.
Lemma lem8225885 {_144870 : Type'} : (@all (list _144870)) = (@all (list _144870)).
Proof. exact (eq_refl (@all (list _144870))). Qed.
Lemma lem8225886 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : (term44 _144870 _144886 g y) = (term44 _144870 _144886 g y).
Proof. exact (MK_COMB (@lem8225885 _144870) (@lem8225884 _144870 _144886 g y)). Qed.
Lemma lem8225887 {_144870 _144886 : Type'} (y : list _144870) : (term46 _144870 _144886 y) = (term46 _144870 _144886 y).
Proof. exact (fun_ext (fun g : _144870 -> _144886 => @lem8225886 _144870 _144886 g y)). Qed.
Lemma lem8225888 {_144870 _144886 : Type'} : (@all (_144870 -> _144886)) = (@all (_144870 -> _144886)).
Proof. exact (eq_refl (@all (_144870 -> _144886))). Qed.
Lemma lem8225889 {_144870 _144886 : Type'} (y : list _144870) : (term48 _144870 _144886 y) = (term48 _144870 _144886 y).
Proof. exact (MK_COMB (@lem8225888 _144870 _144886) (@lem8225887 _144870 _144886 y)). Qed.
Lemma lem8225890 {_144870 _144886 : Type'} : (term50 _144870 _144886) = (term50 _144870 _144886).
Proof. exact (fun_ext (fun y : list _144870 => @lem8225889 _144870 _144886 y)). Qed.
Lemma lem8225891 {_144870 : Type'} : (@all (list _144870)) = (@all (list _144870)).
Proof. exact (eq_refl (@all (list _144870))). Qed.
Lemma lem8225892 {_144870 _144886 : Type'} : (term52 _144870 _144886) = (term52 _144870 _144886).
Proof. exact (MK_COMB (@lem8225891 _144870) (@lem8225890 _144870 _144886)). Qed.
Lemma lem8225923 {_144870 _144886 : Type'} : (term51 _144870 _144886) = (term52 _144870 _144886).
Proof. exact (TRANS (@lem8225871 _144870 _144886) (@lem8225892 _144870 _144886)). Qed.
Lemma lem8225924 {_144870 _144886 : Type'} : (term52 _144870 _144886) = (term51 _144870 _144886).
Proof. exact (SYM (@lem8225923 _144870 _144886)). Qed.
Lemma lem8225927 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8225928 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : ((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y)) = (term53 _144870 _144886 f x g y).
Proof. exact (@lem8225927 ((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y))). Qed.
Lemma lem8225929 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term53 _144870 _144886 f x g y) = ((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y)).
Proof. exact (SYM (@lem8225928 _144870 _144886 f x g y)). Qed.
Lemma lem8225930 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term54 _144870 _144886 f x g y) : term54 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225940 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term55 _144870 _144886 y f g x.
Proof. exact (h1). Qed.
Lemma lem8225946 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term54 _144870 _144886 f x g y) : term54 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225968 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term55 _144870 _144886 y f g x.
Proof. exact (h1). Qed.
Lemma lem8225984 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term54 _144870 _144886 f x g y) : term54 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8225990 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term54 _144870 _144886 f x g y) : term54 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8226000 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term54 _144870 _144886 f x g y) : term54 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8226002 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : x = y.
Proof. exact (proj1 (@lem8225968 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226004 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g x).
Proof. exact (proj2 (@lem8225968 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226019 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term56 _144870 _144886 f g y) = (term56 _144870 _144886 f g y).
Proof. exact (eq_refl (term56 _144870 _144886 f g y)). Qed.
Lemma lem8226020 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (term57 _144870 _144886 f g y x) = (term58 _144870 _144886 f g y).
Proof. exact (MK_COMB (@lem8226019 _144870 _144886 f g y) (@lem8226002 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226021 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term58 _144870 _144886 f g y) = (term59 _144870 _144886 f g y).
Proof. exact (eq_refl (term58 _144870 _144886 f g y)). Qed.
Lemma lem8226022 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) (x : list _144870) : (term60 _144870 _144886 f g y x) = (term60 _144870 _144886 f g y x).
Proof. exact (eq_refl (term60 _144870 _144886 f g y x)). Qed.
Lemma lem8226023 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term57 _144870 _144886 f g y x) = (term58 _144870 _144886 f g y)) = ((term57 _144870 _144886 f g y x) = (term59 _144870 _144886 f g y)).
Proof. exact (MK_COMB (@lem8226022 _144870 _144886 f g y x) (@lem8226021 _144870 _144886 f g y)). Qed.
Lemma lem8226024 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term57 _144870 _144886 f g y x) = (term54 _144870 _144886 f x g y).
Proof. exact (eq_refl (term57 _144870 _144886 f g y x)). Qed.
Lemma lem8226025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8226026 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term60 _144870 _144886 f g y x) = (term61 _144870 _144886 f x g y).
Proof. exact (MK_COMB (@lem8226025) (@lem8226024 _144870 _144886 f x g y)). Qed.
Lemma lem8226027 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term59 _144870 _144886 f g y) = (term59 _144870 _144886 f g y).
Proof. exact (eq_refl (term59 _144870 _144886 f g y)). Qed.
Lemma lem8226028 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term57 _144870 _144886 f g y x) = (term59 _144870 _144886 f g y)) = ((term54 _144870 _144886 f x g y) = (term59 _144870 _144886 f g y)).
Proof. exact (MK_COMB (@lem8226026 _144870 _144886 f x g y) (@lem8226027 _144870 _144886 f g y)). Qed.
Lemma lem8226029 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term57 _144870 _144886 f g y x) = (term58 _144870 _144886 f g y)) = ((term54 _144870 _144886 f x g y) = (term59 _144870 _144886 f g y)).
Proof. exact (TRANS (@lem8226023 _144870 _144886 x f g y) (@lem8226028 _144870 _144886 x f g y)). Qed.
Lemma lem8226030 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = (term59 _144870 _144886 f g y).
Proof. exact (EQ_MP (@lem8226029 _144870 _144886 x f g y) (@lem8226020 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226031 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : term59 _144870 _144886 f g y.
Proof. exact (EQ_MP (@lem8226030 _144870 _144886 y f g x h2) (@lem8226000 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226032 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) : (term62 _144870 _144886 f g) = (term62 _144870 _144886 f g).
Proof. exact (eq_refl (term62 _144870 _144886 f g)). Qed.
Lemma lem8226033 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (term63 _144870 _144886 f g x) = (term63 _144870 _144886 f g y).
Proof. exact (MK_COMB (@lem8226032 _144870 _144886 f g) (@lem8226002 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226034 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term63 _144870 _144886 f g y) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y)).
Proof. exact (eq_refl (term63 _144870 _144886 f g y)). Qed.
Lemma lem8226035 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) : (term64 _144870 _144886 f g x) = (term64 _144870 _144886 f g x).
Proof. exact (eq_refl (term64 _144870 _144886 f g x)). Qed.
Lemma lem8226036 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term63 _144870 _144886 f g x) = (term63 _144870 _144886 f g y)) = ((term63 _144870 _144886 f g x) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))).
Proof. exact (MK_COMB (@lem8226035 _144870 _144886 f g x) (@lem8226034 _144870 _144886 f g y)). Qed.
Lemma lem8226037 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) : (term63 _144870 _144886 f g x) = ((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g x)).
Proof. exact (eq_refl (term63 _144870 _144886 f g x)). Qed.
Lemma lem8226038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8226039 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) : (term64 _144870 _144886 f g x) = (term65 _144870 _144886 f g x).
Proof. exact (MK_COMB (@lem8226038) (@lem8226037 _144870 _144886 f g x)). Qed.
Lemma lem8226040 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y)) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y)).
Proof. exact (eq_refl ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))). Qed.
Lemma lem8226041 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term63 _144870 _144886 f g x) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))) = (((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g x)) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))).
Proof. exact (MK_COMB (@lem8226039 _144870 _144886 f g x) (@lem8226040 _144870 _144886 f g y)). Qed.
Lemma lem8226042 {_144870 _144886 : Type'} (x : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : ((term63 _144870 _144886 f g x) = (term63 _144870 _144886 f g y)) = (((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g x)) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))).
Proof. exact (TRANS (@lem8226036 _144870 _144886 x f g y) (@lem8226041 _144870 _144886 x f g y)). Qed.
Lemma lem8226043 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : ((@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g x)) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y)).
Proof. exact (EQ_MP (@lem8226042 _144870 _144886 x f g y) (@lem8226033 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226067 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y).
Proof. exact (EQ_MP (@lem8226043 _144870 _144886 y f g x h1) (@lem8226004 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226068 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term66 _144870 _144886 f g y.
Proof. exact (fun h0 : term59 _144870 _144886 f g y => @lem8226067 _144870 _144886 y f g x h1). Qed.
Lemma lem8226070 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8226071 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term66 _144870 _144886 f g y) = ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y)).
Proof. exact (@lem8226070 ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))). Qed.
Lemma lem8226072 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y).
Proof. exact (EQ_MP (@lem8226071 _144870 _144886 f g y) (@lem8226068 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226075 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8226077 {_144870 _144886 : Type'} (f : _144870 -> _144886) (g : _144870 -> _144886) (y : list _144870) : (term59 _144870 _144886 f g y) = (term68 _144870 _144886 f g y).
Proof. exact (@lem8226075 ((@List.map _144870 _144886 f y) = (@List.map _144870 _144886 g y))). Qed.
Lemma lem8226080 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : term68 _144870 _144886 f g y.
Proof. exact (EQ_MP (@lem8226077 _144870 _144886 f g y) (@lem8226031 _144870 _144886 y f g x h1 h2)). Qed.
Lemma lem8226083 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (@lem8226080 _144870 _144886 y f g x h1 h2 (@lem8226072 _144870 _144886 y f g x h2)). Qed.
Lemma lem8226084 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : term69.
Proof. exact (fun h0 : ~ False => @lem8226083 _144870 _144886 y f g x h1 h2). Qed.
Lemma lem8226086 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8226087 : term69 = False.
Proof. exact (@lem8226086 False). Qed.
Lemma lem8226089 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226087) (@lem8226084 _144870 _144886 y f g x h1 h2)). Qed.
Lemma lem8226090 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226089 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8226000 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226091 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226090 _144870 _144886 y f g x h1 h2) (@lem8226000 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226092 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226091 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225990 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226093 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226092 _144870 _144886 y f g x h1 h2) (@lem8225990 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226094 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226093 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225990 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226095 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226094 _144870 _144886 y f g x h1 h2) (@lem8225990 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226096 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226095 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225984 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226097 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226096 _144870 _144886 y f g x h1 h2) (@lem8225984 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226098 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term55 _144870 _144886 y f g x) = False.
Proof. exact (prop_ext (fun h3 : term55 _144870 _144886 y f g x => @lem8226097 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225968 _144870 _144886 y f g x h2)). Qed.
Lemma lem8226099 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226098 _144870 _144886 y f g x h1 h2) (@lem8225968 _144870 _144886 y f g x h2)). Qed.
Lemma lem8226100 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226099 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225946 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226101 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226100 _144870 _144886 y f g x h1 h2) (@lem8225946 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226102 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term55 _144870 _144886 y f g x) = False.
Proof. exact (prop_ext (fun h3 : term55 _144870 _144886 y f g x => @lem8226101 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225940 _144870 _144886 y f g x h2)). Qed.
Lemma lem8226103 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226102 _144870 _144886 y f g x h1 h2) (@lem8225940 _144870 _144886 y f g x h2)). Qed.
Lemma lem8226104 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : (term54 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h3 : term54 _144870 _144886 f x g y => @lem8226103 _144870 _144886 y f g x h1 h2) (fun h3 : False => @lem8225930 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226105 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term54 _144870 _144886 f x g y) (h2 : term55 _144870 _144886 y f g x) : False.
Proof. exact (EQ_MP (@lem8226104 _144870 _144886 y f g x h1 h2) (@lem8225930 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226106 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term53 _144870 _144886 f x g y.
Proof. exact (fun h0 : term54 _144870 _144886 f x g y => @lem8226105 _144870 _144886 y f g x h0 h1). Qed.
Lemma lem8226107 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : (@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y).
Proof. exact (EQ_MP (@lem8225929 _144870 _144886 f x g y) (@lem8226106 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226108 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term29 _144870 _144886 f x g y.
Proof. exact (fun h0 : term55 _144870 _144886 y f g x => @lem8226107 _144870 _144886 y f g x h0). Qed.
Lemma lem8226113 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term40 _144870 _144886 x g y.
Proof. exact (fun f : _144870 -> _144886 => @lem8226108 _144870 _144886 f x g y). Qed.
Lemma lem8226118 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : term44 _144870 _144886 g y.
Proof. exact (fun x : list _144870 => @lem8226113 _144870 _144886 x g y). Qed.
Lemma lem8226123 {_144870 _144886 : Type'} (y : list _144870) : term48 _144870 _144886 y.
Proof. exact (fun g : _144870 -> _144886 => @lem8226118 _144870 _144886 g y). Qed.
Lemma lem8226128 {_144870 _144886 : Type'} : term52 _144870 _144886.
Proof. exact (fun y : list _144870 => @lem8226123 _144870 _144886 y). Qed.
Lemma lem8226129 {_144870 _144886 : Type'} : term51 _144870 _144886.
Proof. exact (EQ_MP (@lem8225924 _144870 _144886) (@lem8226128 _144870 _144886)). Qed.
Lemma lem8226130 {_144870 _144886 : Type'} (y : list _144870) : term70 _144870 _144886 y.
Proof. exact (@lem8226129 _144870 _144886 y). Qed.
Lemma lem8226131 {_144870 _144886 : Type'} (y : list _144870) : (term70 _144870 _144886 y) = (term47 _144870 _144886 y).
Proof. exact (eq_refl (term70 _144870 _144886 y)). Qed.
Lemma lem8226132 {_144870 _144886 : Type'} (y : list _144870) : term47 _144870 _144886 y.
Proof. exact (EQ_MP (@lem8226131 _144870 _144886 y) (@lem8226130 _144870 _144886 y)). Qed.
Lemma lem8226133 {_144870 _144886 : Type'} (y : list _144870) (g : _144870 -> _144886) : term71 _144870 _144886 y g.
Proof. exact (@lem8226132 _144870 _144886 y g). Qed.
Lemma lem8226134 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : (term71 _144870 _144886 y g) = (term43 _144870 _144886 g y).
Proof. exact (eq_refl (term71 _144870 _144886 y g)). Qed.
Lemma lem8226135 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) : term43 _144870 _144886 g y.
Proof. exact (EQ_MP (@lem8226134 _144870 _144886 g y) (@lem8226133 _144870 _144886 y g)). Qed.
Lemma lem8226136 {_144870 _144886 : Type'} (g : _144870 -> _144886) (y : list _144870) (x : list _144870) : term72 _144870 _144886 g y x.
Proof. exact (@lem8226135 _144870 _144886 g y x). Qed.
Lemma lem8226137 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term72 _144870 _144886 g y x) = (term39 _144870 _144886 x g y).
Proof. exact (eq_refl (term72 _144870 _144886 g y x)). Qed.
Lemma lem8226138 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term39 _144870 _144886 x g y.
Proof. exact (EQ_MP (@lem8226137 _144870 _144886 x g y) (@lem8226136 _144870 _144886 g y x)). Qed.
Lemma lem8226139 {_144870 _144886 : Type'} (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (f : _144870 -> _144886) : term73 _144870 _144886 x g y f.
Proof. exact (@lem8226138 _144870 _144886 x g y f). Qed.
Lemma lem8226140 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : (term73 _144870 _144886 x g y f) = (term30 _144870 _144886 f x g y).
Proof. exact (eq_refl (term73 _144870 _144886 x g y f)). Qed.
Lemma lem8226141 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term30 _144870 _144886 f x g y.
Proof. exact (EQ_MP (@lem8226140 _144870 _144886 f x g y) (@lem8226139 _144870 _144886 x g y f)). Qed.
Lemma lem8226143 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term30 _144870 _144886 f x g y.
Proof. exact (@lem8225812 _144870 _144886 f x g y (@lem8226141 _144870 _144886 f x g y)). Qed.
Lemma lem8226144 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term31 _144870 _144886 f x g y) : False.
Proof. exact (@lem8226143 _144870 _144886 f x g y (@lem8225796 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226145 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term31 _144870 _144886 f x g y) : (term31 _144870 _144886 f x g y) = False.
Proof. exact (prop_ext (fun h2 : term31 _144870 _144886 f x g y => @lem8226144 _144870 _144886 f x g y h1) (fun h2 : False => @lem8225796 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226146 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term31 _144870 _144886 f x g y) : False.
Proof. exact (EQ_MP (@lem8226145 _144870 _144886 f x g y h1) (@lem8225796 _144870 _144886 f x g y h1)). Qed.
Lemma lem8226147 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term30 _144870 _144886 f x g y.
Proof. exact (fun h0 : term31 _144870 _144886 f x g y => @lem8226146 _144870 _144886 f x g y h0). Qed.
Lemma lem8226148 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term29 _144870 _144886 f x g y.
Proof. exact (EQ_MP (@lem8225795 _144870 _144886 f x g y) (@lem8226147 _144870 _144886 f x g y)). Qed.
Lemma lem8226149 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term29 _144870 _144886 f x g y) : term29 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8226150 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term55 _144870 _144886 y f g x.
Proof. exact (h1). Qed.
Lemma lem8226151 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term55 _144870 _144886 y f g x) (h2 : term29 _144870 _144886 f x g y) : (@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y).
Proof. exact (@lem8226149 _144870 _144886 f x g y h2 (@lem8226150 _144870 _144886 y f g x h1)). Qed.
Lemma lem8226152 {_144870 _144886 : Type'} (y : list _144870) (f : _144870 -> _144886) (g : _144870 -> _144886) (x : list _144870) (h1 : term55 _144870 _144886 y f g x) : term74 _144870 _144886 f x g y.
Proof. exact (fun h0 : term29 _144870 _144886 f x g y => @lem8226151 _144870 _144886 f x g y h1 h0). Qed.
Lemma lem8226153 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term29 _144870 _144886 f x g y) : term29 _144870 _144886 f x g y.
Proof. exact (h1). Qed.
Lemma lem8226154 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term55 _144870 _144886 y f g x) (h2 : term29 _144870 _144886 f x g y) : (@List.map _144870 _144886 f x) = (@List.map _144870 _144886 g y).
Proof. exact (@lem8226152 _144870 _144886 y f g x h1 (@lem8226153 _144870 _144886 f x g y h2)). Qed.
Lemma lem8226155 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) (h1 : term29 _144870 _144886 f x g y) : term29 _144870 _144886 f x g y.
Proof. exact (fun h0 : term55 _144870 _144886 y f g x => @lem8226154 _144870 _144886 f x g y h0 h1). Qed.
Lemma lem8226156 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term75 _144870 _144886 f x g y.
Proof. exact (fun h0 : term29 _144870 _144886 f x g y => @lem8226155 _144870 _144886 f x g y h0). Qed.
Lemma lem8226158 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term76 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem8226159 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term76 _5106 _5107 P) = ((term77 _5106 _5107 P) = (term78 _5106 _5107 P)).
Proof. exact (eq_refl (term76 _5106 _5107 P)). Qed.
Lemma lem8226161 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term79 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8226162 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term79 _143449 _143452 _143456 _143457 _143462 p) = (term80 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term79 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8226163 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term80 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8226162 _143449 _143452 _143456 _143457 _143462 p) (@lem8226161 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8226164 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term81 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8226163 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8226165 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term81 _143449 _143452 _143456 _143457 _143462 p lt2) = (term82 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term81 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8226166 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term82 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8226165 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8226164 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8226167 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term83 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8226166 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8226168 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term83 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term84 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term83 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8226169 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term84 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8226168 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8226167 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8226170 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term85 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8226169 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8226171 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term85 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term86 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term85 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8226208 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term86 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8226171 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8226170 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8226209 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (t : type815 _144962 A B P) : (@admissible _144947 B A (list _144962) P lt2 p s t) = (term87 _144947 _144962 A B P p lt2 s t).
Proof. exact (@lem8226208 _144947 B A (list _144962) P p lt2 s t). Qed.
Lemma lem8226210 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (@admissible _144947 B A (list _144962) P lt2 p s l) = (term87 _144947 _144962 A B P p lt2 s l).
Proof. exact (@lem8226209 _144947 _144962 A B P p lt2 s l). Qed.
Lemma lem8226247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8226248 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term88 _144947 _144962 A B P lt2 p s l) = (term89 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8226247) (@lem8226210 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8226250 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term86 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8226171 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8226170 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8226251 {_144947 _144956 _144962 A B P : Type'} (p : type810 _144962 A B P) (lt2 : type1470 _144947 A) (s : type1224 _144947 _144962 P) (t : type888 _144956 _144962 A B P) : (@admissible _144947 B A _144956 (prod _144962 P) lt2 p s t) = (term90 _144947 _144956 _144962 A B P p lt2 s t).
Proof. exact (@lem8226250 _144947 B A _144956 (prod _144962 P) p lt2 s t). Qed.
Lemma lem8226252 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term91 _144947 _144956 _144962 A B P lt2 p l s h) = (term92 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (@lem8226251 _144947 _144956 _144962 A B P (term93 _144962 A B P p l) lt2 (term94 _144947 _144962 P s) (term95 _144956 _144962 A B P h)). Qed.
Lemma lem8226270 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term77 _5106 _5107 P) = (term78 _5106 _5107 P).
Proof. exact (EQ_MP (@lem8226159 _5106 _5107 P) (@lem8226158 _5106 _5107 P)). Qed.
Lemma lem8226271 {_144962 P : Type'} (P' : type1210 _144962 P) : (term96 _144962 P P') = (term97 _144962 P P').
Proof. exact (@lem8226270 P _144962 P'). Qed.
Lemma lem8226272 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term98 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term99 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (@lem8226271 _144962 P (term100 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226273 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : prod _144962 P) : (term101 _144947 _144956 _144962 A B P p l lt2 s f h g a) = (term102 _144947 _144956 _144962 A B P p l lt2 s f h g a).
Proof. exact (eq_refl (term101 _144947 _144956 _144962 A B P p l lt2 s f h g a)). Qed.
Lemma lem8226274 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term103 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term100 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun a : prod _144962 P => @lem8226273 _144947 _144956 _144962 A B P p l lt2 s f h g a)). Qed.
Lemma lem8226275 {_144962 P : Type'} : (@all (prod _144962 P)) = (@all (prod _144962 P)).
Proof. exact (eq_refl (@all (prod _144962 P))). Qed.
Lemma lem8226276 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term98 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term104 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8226275 _144962 P) (@lem8226274 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8226278 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term105 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term106 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8226277) (@lem8226276 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226279 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) (p2 : P) : (term107 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term108 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2).
Proof. exact (eq_refl (term107 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2)). Qed.
Lemma lem8226280 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term109 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term110 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8226279 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2)). Qed.
Lemma lem8226281 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226282 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term111 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term112 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8226281 P) (@lem8226280 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8226283 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term113 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term114 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8226282 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8226284 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226285 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term99 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term115 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8226284 _144962) (@lem8226283 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226286 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : ((term98 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term99 _144947 _144956 _144962 A B P p l lt2 s f h g)) = ((term104 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term115 _144947 _144956 _144962 A B P p l lt2 s f h g)).
Proof. exact (MK_COMB (@lem8226278 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8226285 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226287 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term104 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term115 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (EQ_MP (@lem8226286 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8226272 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226305 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8226306 {_144962 A B P : Type'} (f : type810 _144962 A B P) (y : A -> B) : (term117 _144962 A B P f y) = (f y).
Proof. exact (@lem8226305 (A -> B) (type1210 _144962 P) f y). Qed.
Lemma lem8226307 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term118 _144962 A B P p l f) = (term119 _144962 A B P p l f).
Proof. exact (@lem8226306 _144962 A B P (term93 _144962 A B P p l) f). Qed.
Lemma lem8226308 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term119 _144962 A B P p l f) = (term120 _144962 A B P p l f).
Proof. exact (eq_refl (term119 _144962 A B P p l f)). Qed.
Lemma lem8226309 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) : (term121 _144962 A B P p l) = (term93 _144962 A B P p l).
Proof. exact (fun_ext (fun f : A -> B => @lem8226308 _144962 A B P p l f)). Qed.
Lemma lem8226310 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8226311 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term118 _144962 A B P p l f) = (term119 _144962 A B P p l f).
Proof. exact (MK_COMB (@lem8226309 _144962 A B P p l) (@lem8226310 A B f)). Qed.
Lemma lem8226312 {_144962 P : Type'} : (@eq ((prod _144962 P) -> Prop)) = (@eq ((prod _144962 P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _144962 P) -> Prop))). Qed.
Lemma lem8226313 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term122 _144962 A B P p l f) = (term123 _144962 A B P p l f).
Proof. exact (MK_COMB (@lem8226312 _144962 P) (@lem8226311 _144962 A B P p l f)). Qed.
Lemma lem8226314 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term119 _144962 A B P p l f) = (term120 _144962 A B P p l f).
Proof. exact (eq_refl (term119 _144962 A B P p l f)). Qed.
Lemma lem8226315 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : ((term118 _144962 A B P p l f) = (term119 _144962 A B P p l f)) = ((term119 _144962 A B P p l f) = (term120 _144962 A B P p l f)).
Proof. exact (MK_COMB (@lem8226313 _144962 A B P p l f) (@lem8226314 _144962 A B P p l f)). Qed.
Lemma lem8226316 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term119 _144962 A B P p l f) = (term120 _144962 A B P p l f).
Proof. exact (EQ_MP (@lem8226315 _144962 A B P p l f) (@lem8226307 _144962 A B P p l f)). Qed.
Lemma lem8226331 {_144962 P : Type'} (p1 : _144962) (p2 : P) : (@pair _144962 P p1 p2) = (@pair _144962 P p1 p2).
Proof. exact (eq_refl (@pair _144962 P p1 p2)). Qed.
Lemma lem8226332 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (p1 : _144962) (p2 : P) : (term124 _144962 A B P p l f p1 p2) = (term125 _144962 A B P p l f p1 p2).
Proof. exact (MK_COMB (@lem8226316 _144962 A B P p l f) (@lem8226331 _144962 P p1 p2)). Qed.
Lemma lem8226333 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a0 = (term126 _144962 P a0 a1).
Proof. exact (@lem51128 _144962 P a0 a1). Qed.
Lemma lem8226334 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (@lem8226333 _144962 P y x). Qed.
Lemma lem8226335 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a1 = (term127 _144962 P a0 a1).
Proof. exact (@lem51159 _144962 P a0 a1). Qed.
Lemma lem8226336 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (@lem8226335 _144962 P y x). Qed.
Lemma lem8226337 {_144962 : Type'} (y : _144962) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8226338 {_144962 : Type'} : (term128 _144962) = (term128 _144962).
Proof. exact (eq_refl (term128 _144962)). Qed.
Lemma lem8226339 {_144962 P : Type'} (y : _144962) (x : P) : (term129 _144962 y) = (term130 _144962 P y x).
Proof. exact (MK_COMB (@lem8226338 _144962) (@lem8226334 _144962 P y x)). Qed.
Lemma lem8226340 {_144962 P : Type'} (y : _144962) (x : P) : (term130 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term130 _144962 P y x)). Qed.
Lemma lem8226341 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (term131 _144962 y).
Proof. exact (eq_refl (term131 _144962 y)). Qed.
Lemma lem8226342 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = ((term129 _144962 y) = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226341 _144962 y) (@lem8226340 _144962 P y x)). Qed.
Lemma lem8226343 {_144962 : Type'} (y : _144962) : (term129 _144962 y) = y.
Proof. exact (eq_refl (term129 _144962 y)). Qed.
Lemma lem8226344 {_144962 : Type'} : (@eq _144962) = (@eq _144962).
Proof. exact (eq_refl (@eq _144962)). Qed.
Lemma lem8226345 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (@eq _144962 y).
Proof. exact (MK_COMB (@lem8226344 _144962) (@lem8226343 _144962 y)). Qed.
Lemma lem8226346 {_144962 P : Type'} (y : _144962) (x : P) : (term126 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term126 _144962 P y x)). Qed.
Lemma lem8226347 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term126 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226345 _144962 y) (@lem8226346 _144962 P y x)). Qed.
Lemma lem8226348 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (TRANS (@lem8226342 _144962 P y x) (@lem8226347 _144962 P y x)). Qed.
Lemma lem8226349 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226348 _144962 P y x) (@lem8226339 _144962 P y x)). Qed.
Lemma lem8226350 {_144962 : Type'} (y : _144962) : (@eq _144962 y) = (@eq _144962 y).
Proof. exact (eq_refl (@eq _144962 y)). Qed.
Lemma lem8226351 {_144962 P : Type'} (y : _144962) (x : P) : (y = y) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226350 _144962 y) (@lem8226349 _144962 P y x)). Qed.
Lemma lem8226352 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226351 _144962 P y x) (@lem8226337 _144962 y)). Qed.
Lemma lem8226353 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8226354 {P : Type'} : (term128 P) = (term128 P).
Proof. exact (eq_refl (term128 P)). Qed.
Lemma lem8226355 {_144962 P : Type'} (y : _144962) (x : P) : (term129 P x) = (term132 _144962 P y x).
Proof. exact (MK_COMB (@lem8226354 P) (@lem8226336 _144962 P y x)). Qed.
Lemma lem8226356 {_144962 P : Type'} (y : _144962) (x : P) : (term132 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term132 _144962 P y x)). Qed.
Lemma lem8226357 {P : Type'} (x : P) : (term131 P x) = (term131 P x).
Proof. exact (eq_refl (term131 P x)). Qed.
Lemma lem8226358 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = ((term129 P x) = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226357 P x) (@lem8226356 _144962 P y x)). Qed.
Lemma lem8226359 {P : Type'} (x : P) : (term129 P x) = x.
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem8226360 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8226361 {P : Type'} (x : P) : (term131 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8226360 P) (@lem8226359 P x)). Qed.
Lemma lem8226362 {_144962 P : Type'} (y : _144962) (x : P) : (term127 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term127 _144962 P y x)). Qed.
Lemma lem8226363 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term127 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226361 P x) (@lem8226362 _144962 P y x)). Qed.
Lemma lem8226364 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (TRANS (@lem8226358 _144962 P y x) (@lem8226363 _144962 P y x)). Qed.
Lemma lem8226365 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226364 _144962 P y x) (@lem8226355 _144962 P y x)). Qed.
Lemma lem8226366 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8226367 {_144962 P : Type'} (y : _144962) (x : P) : (x = x) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226366 P x) (@lem8226365 _144962 P y x)). Qed.
Lemma lem8226368 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226367 _144962 P y x) (@lem8226353 P x)). Qed.
Lemma lem8226369 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term133 _144962 A B P p l f) = (term133 _144962 A B P p l f).
Proof. exact (eq_refl (term133 _144962 A B P p l f)). Qed.
Lemma lem8226370 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term134 _144962 A B P p l f y) = (term135 _144962 A B P p l f y x).
Proof. exact (MK_COMB (@lem8226369 _144962 A B P p l f) (@lem8226352 _144962 P y x)). Qed.
Lemma lem8226371 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : (term135 _144962 A B P p l f y x) = (term136 _144962 A B P p y x l f).
Proof. exact (eq_refl (term135 _144962 A B P p l f y x)). Qed.
Lemma lem8226372 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) : (term137 _144962 A B P p l f y) = (term137 _144962 A B P p l f y).
Proof. exact (eq_refl (term137 _144962 A B P p l f y)). Qed.
Lemma lem8226373 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : ((term134 _144962 A B P p l f y) = (term135 _144962 A B P p l f y x)) = ((term134 _144962 A B P p l f y) = (term136 _144962 A B P p y x l f)).
Proof. exact (MK_COMB (@lem8226372 _144962 A B P p l f y) (@lem8226371 _144962 A B P p y x l f)). Qed.
Lemma lem8226374 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : (term134 _144962 A B P p l f y) = (term138 _144962 A B P p y l f).
Proof. exact (eq_refl (term134 _144962 A B P p l f y)). Qed.
Lemma lem8226375 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8226376 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : (term137 _144962 A B P p l f y) = (term139 _144962 A B P p y l f).
Proof. exact (MK_COMB (@lem8226375 P) (@lem8226374 _144962 A B P p y l f)). Qed.
Lemma lem8226377 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : (term136 _144962 A B P p y x l f) = (term136 _144962 A B P p y x l f).
Proof. exact (eq_refl (term136 _144962 A B P p y x l f)). Qed.
Lemma lem8226378 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : ((term134 _144962 A B P p l f y) = (term136 _144962 A B P p y x l f)) = ((term138 _144962 A B P p y l f) = (term136 _144962 A B P p y x l f)).
Proof. exact (MK_COMB (@lem8226376 _144962 A B P p y l f) (@lem8226377 _144962 A B P p y x l f)). Qed.
Lemma lem8226379 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : ((term134 _144962 A B P p l f y) = (term135 _144962 A B P p l f y x)) = ((term138 _144962 A B P p y l f) = (term136 _144962 A B P p y x l f)).
Proof. exact (TRANS (@lem8226373 _144962 A B P p y x l f) (@lem8226378 _144962 A B P p y x l f)). Qed.
Lemma lem8226380 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (f : A -> B) : (term138 _144962 A B P p y l f) = (term136 _144962 A B P p y x l f).
Proof. exact (EQ_MP (@lem8226379 _144962 A B P p y x l f) (@lem8226370 _144962 A B P p l f y x)). Qed.
Lemma lem8226381 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term140 _144962 A B P p y l f x) = (term141 _144962 A B P p l f y x).
Proof. exact (MK_COMB (@lem8226380 _144962 A B P p y x l f) (@lem8226368 _144962 P y x)). Qed.
Lemma lem8226382 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term141 _144962 A B P p l f y x) = (term142 _144962 A B P p l f y x).
Proof. exact (eq_refl (term141 _144962 A B P p l f y x)). Qed.
Lemma lem8226383 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term143 _144962 A B P p y l f x) = (term143 _144962 A B P p y l f x).
Proof. exact (eq_refl (term143 _144962 A B P p y l f x)). Qed.
Lemma lem8226384 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l f x) = (term141 _144962 A B P p l f y x)) = ((term140 _144962 A B P p y l f x) = (term142 _144962 A B P p l f y x)).
Proof. exact (MK_COMB (@lem8226383 _144962 A B P p y l f x) (@lem8226382 _144962 A B P p l f y x)). Qed.
Lemma lem8226385 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term140 _144962 A B P p y l f x) = (term144 _144962 A B P p y l f x).
Proof. exact (eq_refl (term140 _144962 A B P p y l f x)). Qed.
Lemma lem8226386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8226387 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term143 _144962 A B P p y l f x) = (term145 _144962 A B P p y l f x).
Proof. exact (MK_COMB (@lem8226386) (@lem8226385 _144962 A B P p y l f x)). Qed.
Lemma lem8226388 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term142 _144962 A B P p l f y x) = (term142 _144962 A B P p l f y x).
Proof. exact (eq_refl (term142 _144962 A B P p l f y x)). Qed.
Lemma lem8226389 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l f x) = (term142 _144962 A B P p l f y x)) = ((term144 _144962 A B P p y l f x) = (term142 _144962 A B P p l f y x)).
Proof. exact (MK_COMB (@lem8226387 _144962 A B P p y l f x) (@lem8226388 _144962 A B P p l f y x)). Qed.
Lemma lem8226390 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l f x) = (term141 _144962 A B P p l f y x)) = ((term144 _144962 A B P p y l f x) = (term142 _144962 A B P p l f y x)).
Proof. exact (TRANS (@lem8226384 _144962 A B P p l f y x) (@lem8226389 _144962 A B P p l f y x)). Qed.
Lemma lem8226391 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term144 _144962 A B P p y l f x) = (term142 _144962 A B P p l f y x).
Proof. exact (EQ_MP (@lem8226390 _144962 A B P p l f y x) (@lem8226381 _144962 A B P p l f y x)). Qed.
Lemma lem8226392 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term142 _144962 A B P p l f y x) = (term144 _144962 A B P p y l f x).
Proof. exact (SYM (@lem8226391 _144962 A B P p l f y x)). Qed.
Lemma lem8226393 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term146 _144962 A B P p l f y x) = (term142 _144962 A B P p l f y x).
Proof. exact (eq_refl (term146 _144962 A B P p l f y x)). Qed.
Lemma lem8226394 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term146 _144962 A B P p l f y x) = (term144 _144962 A B P p y l f x).
Proof. exact (TRANS (@lem8226393 _144962 A B P p l f y x) (@lem8226392 _144962 A B P p y l f x)). Qed.
Lemma lem8226395 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : term147 _144962 A B P p y l f.
Proof. exact (fun x : P => @lem8226394 _144962 A B P p y l f x). Qed.
Lemma lem8226396 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term148 _144962 A B P p l f.
Proof. exact (fun y : _144962 => @lem8226395 _144962 A B P p y l f). Qed.
Lemma lem8226397 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term149 _144962 A B P p l f.
Proof. exact (ex_intro (term150 _144962 A B P p l f) (term151 _144962 A B P p l f) (@lem8226396 _144962 A B P p l f)). Qed.
Lemma lem8226399 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8226400 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8226399 Prop a b). Qed.
Lemma lem8226401 {_144962 A B P : Type'} (_109415 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : ((term152 _144962 P _109415 y x) = (term144 _144962 A B P p y l f x)) = (term153 _144962 A B P _109415 p y l f x).
Proof. exact (@lem8226400 (term152 _144962 P _109415 y x) (term144 _144962 A B P p y l f x)). Qed.
Lemma lem8226402 {_144962 A B P : Type'} (_109415 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : (term154 _144962 A B P _109415 p y l f) = (term155 _144962 A B P _109415 p y l f).
Proof. exact (fun_ext (fun x : P => @lem8226401 _144962 A B P _109415 p y l f x)). Qed.
Lemma lem8226403 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226404 {_144962 A B P : Type'} (_109415 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : (term156 _144962 A B P _109415 p y l f) = (term157 _144962 A B P _109415 p y l f).
Proof. exact (MK_COMB (@lem8226403 P) (@lem8226402 _144962 A B P _109415 p y l f)). Qed.
Lemma lem8226405 {_144962 A B P : Type'} (_109415 : type1210 _144962 P) (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term158 _144962 A B P _109415 p l f) = (term159 _144962 A B P _109415 p l f).
Proof. exact (fun_ext (fun y : _144962 => @lem8226404 _144962 A B P _109415 p y l f)). Qed.
Lemma lem8226406 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226407 {_144962 A B P : Type'} (_109415 : type1210 _144962 P) (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term160 _144962 A B P _109415 p l f) = (term161 _144962 A B P _109415 p l f).
Proof. exact (MK_COMB (@lem8226406 _144962) (@lem8226405 _144962 A B P _109415 p l f)). Qed.
Lemma lem8226408 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term150 _144962 A B P p l f) = (term162 _144962 A B P p l f).
Proof. exact (fun_ext (fun _109415 : type1210 _144962 P => @lem8226407 _144962 A B P _109415 p l f)). Qed.
Lemma lem8226409 {_144962 P : Type'} : (@ex ((prod _144962 P) -> Prop)) = (@ex ((prod _144962 P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _144962 P) -> Prop))). Qed.
Lemma lem8226410 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term149 _144962 A B P p l f) = (term163 _144962 A B P p l f).
Proof. exact (MK_COMB (@lem8226409 _144962 P) (@lem8226408 _144962 A B P p l f)). Qed.
Lemma lem8226411 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term163 _144962 A B P p l f.
Proof. exact (EQ_MP (@lem8226410 _144962 A B P p l f) (@lem8226397 _144962 A B P p l f)). Qed.
Lemma lem8226413 {_5076 : Type'} (P : _5076 -> Prop) : term164 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8226414 {_144962 P : Type'} (P' : type324 _144962 P) : term165 _144962 P P'.
Proof. exact (@lem8226413 (type1210 _144962 P) P'). Qed.
Lemma lem8226415 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term166 _144962 A B P p l f.
Proof. exact (@lem8226414 _144962 P (term162 _144962 A B P p l f)). Qed.
Lemma lem8226416 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term167 _144962 A B P p l f.
Proof. exact (@lem8226415 _144962 A B P p l f (@lem8226411 _144962 A B P p l f)). Qed.
Lemma lem8226417 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term167 _144962 A B P p l f) = (term168 _144962 A B P p l f).
Proof. exact (eq_refl (term167 _144962 A B P p l f)). Qed.
Lemma lem8226418 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : term168 _144962 A B P p l f.
Proof. exact (EQ_MP (@lem8226417 _144962 A B P p l f) (@lem8226416 _144962 A B P p l f)). Qed.
Lemma lem8226419 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) (y : _144962) : term169 _144962 A B P p l f y.
Proof. exact (@lem8226418 _144962 A B P p l f y). Qed.
Lemma lem8226420 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : (term169 _144962 A B P p l f y) = (term170 _144962 A B P p y l f).
Proof. exact (eq_refl (term169 _144962 A B P p l f y)). Qed.
Lemma lem8226421 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) : term170 _144962 A B P p y l f.
Proof. exact (EQ_MP (@lem8226420 _144962 A B P p y l f) (@lem8226419 _144962 A B P p l f y)). Qed.
Lemma lem8226422 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : term171 _144962 A B P p y l f x.
Proof. exact (@lem8226421 _144962 A B P p y l f x). Qed.
Lemma lem8226423 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term171 _144962 A B P p y l f x) = (term172 _144962 A B P p y l f x).
Proof. exact (eq_refl (term171 _144962 A B P p y l f x)). Qed.
Lemma lem8226424 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : term172 _144962 A B P p y l f x.
Proof. exact (EQ_MP (@lem8226423 _144962 A B P p y l f x) (@lem8226422 _144962 A B P p y l f x)). Qed.
Lemma lem8226426 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8226427 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8226426 Prop a b). Qed.
Lemma lem8226428 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term172 _144962 A B P p y l f x) = ((term125 _144962 A B P p l f y x) = (term144 _144962 A B P p y l f x)).
Proof. exact (@lem8226427 (term125 _144962 A B P p l f y x) (term144 _144962 A B P p y l f x)). Qed.
Lemma lem8226429 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term125 _144962 A B P p l f y x) = (term144 _144962 A B P p y l f x).
Proof. exact (EQ_MP (@lem8226428 _144962 A B P p y l f x) (@lem8226424 _144962 A B P p y l f x)). Qed.
Lemma lem8226430 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term125 _144962 A B P p l f y x) = (term144 _144962 A B P p y l f x).
Proof. exact (@lem8226429 _144962 A B P p y l f x). Qed.
Lemma lem8226431 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term125 _144962 A B P p l f p1 p2) = (term144 _144962 A B P p p1 l f p2).
Proof. exact (@lem8226430 _144962 A B P p p1 l f p2). Qed.
Lemma lem8226434 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term124 _144962 A B P p l f p1 p2) = (term144 _144962 A B P p p1 l f p2).
Proof. exact (TRANS (@lem8226332 _144962 A B P p l f p1 p2) (@lem8226431 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8226435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8226436 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term173 _144962 A B P p l f p1 p2) = (term174 _144962 A B P p p1 l f p2).
Proof. exact (MK_COMB (@lem8226435) (@lem8226434 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8226440 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8226441 {_144962 A B P : Type'} (f : type810 _144962 A B P) (y : A -> B) : (term117 _144962 A B P f y) = (f y).
Proof. exact (@lem8226440 (A -> B) (type1210 _144962 P) f y). Qed.
Lemma lem8226442 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term118 _144962 A B P p l g) = (term119 _144962 A B P p l g).
Proof. exact (@lem8226441 _144962 A B P (term93 _144962 A B P p l) g). Qed.
Lemma lem8226443 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term119 _144962 A B P p l f) = (term120 _144962 A B P p l f).
Proof. exact (eq_refl (term119 _144962 A B P p l f)). Qed.
Lemma lem8226444 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) : (term121 _144962 A B P p l) = (term93 _144962 A B P p l).
Proof. exact (fun_ext (fun f : A -> B => @lem8226443 _144962 A B P p l f)). Qed.
Lemma lem8226445 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8226446 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term118 _144962 A B P p l g) = (term119 _144962 A B P p l g).
Proof. exact (MK_COMB (@lem8226444 _144962 A B P p l) (@lem8226445 A B g)). Qed.
Lemma lem8226447 {_144962 P : Type'} : (@eq ((prod _144962 P) -> Prop)) = (@eq ((prod _144962 P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _144962 P) -> Prop))). Qed.
Lemma lem8226448 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term122 _144962 A B P p l g) = (term123 _144962 A B P p l g).
Proof. exact (MK_COMB (@lem8226447 _144962 P) (@lem8226446 _144962 A B P p l g)). Qed.
Lemma lem8226449 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term119 _144962 A B P p l g) = (term120 _144962 A B P p l g).
Proof. exact (eq_refl (term119 _144962 A B P p l g)). Qed.
Lemma lem8226450 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : ((term118 _144962 A B P p l g) = (term119 _144962 A B P p l g)) = ((term119 _144962 A B P p l g) = (term120 _144962 A B P p l g)).
Proof. exact (MK_COMB (@lem8226448 _144962 A B P p l g) (@lem8226449 _144962 A B P p l g)). Qed.
Lemma lem8226451 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term119 _144962 A B P p l g) = (term120 _144962 A B P p l g).
Proof. exact (EQ_MP (@lem8226450 _144962 A B P p l g) (@lem8226442 _144962 A B P p l g)). Qed.
Lemma lem8226466 {_144962 P : Type'} (p1 : _144962) (p2 : P) : (@pair _144962 P p1 p2) = (@pair _144962 P p1 p2).
Proof. exact (eq_refl (@pair _144962 P p1 p2)). Qed.
Lemma lem8226467 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (p1 : _144962) (p2 : P) : (term124 _144962 A B P p l g p1 p2) = (term125 _144962 A B P p l g p1 p2).
Proof. exact (MK_COMB (@lem8226451 _144962 A B P p l g) (@lem8226466 _144962 P p1 p2)). Qed.
Lemma lem8226468 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a0 = (term126 _144962 P a0 a1).
Proof. exact (@lem51128 _144962 P a0 a1). Qed.
Lemma lem8226469 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (@lem8226468 _144962 P y x). Qed.
Lemma lem8226470 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a1 = (term127 _144962 P a0 a1).
Proof. exact (@lem51159 _144962 P a0 a1). Qed.
Lemma lem8226471 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (@lem8226470 _144962 P y x). Qed.
Lemma lem8226472 {_144962 : Type'} (y : _144962) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8226473 {_144962 : Type'} : (term128 _144962) = (term128 _144962).
Proof. exact (eq_refl (term128 _144962)). Qed.
Lemma lem8226474 {_144962 P : Type'} (y : _144962) (x : P) : (term129 _144962 y) = (term130 _144962 P y x).
Proof. exact (MK_COMB (@lem8226473 _144962) (@lem8226469 _144962 P y x)). Qed.
Lemma lem8226475 {_144962 P : Type'} (y : _144962) (x : P) : (term130 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term130 _144962 P y x)). Qed.
Lemma lem8226476 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (term131 _144962 y).
Proof. exact (eq_refl (term131 _144962 y)). Qed.
Lemma lem8226477 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = ((term129 _144962 y) = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226476 _144962 y) (@lem8226475 _144962 P y x)). Qed.
Lemma lem8226478 {_144962 : Type'} (y : _144962) : (term129 _144962 y) = y.
Proof. exact (eq_refl (term129 _144962 y)). Qed.
Lemma lem8226479 {_144962 : Type'} : (@eq _144962) = (@eq _144962).
Proof. exact (eq_refl (@eq _144962)). Qed.
Lemma lem8226480 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (@eq _144962 y).
Proof. exact (MK_COMB (@lem8226479 _144962) (@lem8226478 _144962 y)). Qed.
Lemma lem8226481 {_144962 P : Type'} (y : _144962) (x : P) : (term126 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term126 _144962 P y x)). Qed.
Lemma lem8226482 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term126 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226480 _144962 y) (@lem8226481 _144962 P y x)). Qed.
Lemma lem8226483 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (TRANS (@lem8226477 _144962 P y x) (@lem8226482 _144962 P y x)). Qed.
Lemma lem8226484 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226483 _144962 P y x) (@lem8226474 _144962 P y x)). Qed.
Lemma lem8226485 {_144962 : Type'} (y : _144962) : (@eq _144962 y) = (@eq _144962 y).
Proof. exact (eq_refl (@eq _144962 y)). Qed.
Lemma lem8226486 {_144962 P : Type'} (y : _144962) (x : P) : (y = y) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226485 _144962 y) (@lem8226484 _144962 P y x)). Qed.
Lemma lem8226487 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226486 _144962 P y x) (@lem8226472 _144962 y)). Qed.
Lemma lem8226488 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8226489 {P : Type'} : (term128 P) = (term128 P).
Proof. exact (eq_refl (term128 P)). Qed.
Lemma lem8226490 {_144962 P : Type'} (y : _144962) (x : P) : (term129 P x) = (term132 _144962 P y x).
Proof. exact (MK_COMB (@lem8226489 P) (@lem8226471 _144962 P y x)). Qed.
Lemma lem8226491 {_144962 P : Type'} (y : _144962) (x : P) : (term132 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term132 _144962 P y x)). Qed.
Lemma lem8226492 {P : Type'} (x : P) : (term131 P x) = (term131 P x).
Proof. exact (eq_refl (term131 P x)). Qed.
Lemma lem8226493 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = ((term129 P x) = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226492 P x) (@lem8226491 _144962 P y x)). Qed.
Lemma lem8226494 {P : Type'} (x : P) : (term129 P x) = x.
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem8226495 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8226496 {P : Type'} (x : P) : (term131 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8226495 P) (@lem8226494 P x)). Qed.
Lemma lem8226497 {_144962 P : Type'} (y : _144962) (x : P) : (term127 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term127 _144962 P y x)). Qed.
Lemma lem8226498 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term127 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226496 P x) (@lem8226497 _144962 P y x)). Qed.
Lemma lem8226499 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (TRANS (@lem8226493 _144962 P y x) (@lem8226498 _144962 P y x)). Qed.
Lemma lem8226500 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226499 _144962 P y x) (@lem8226490 _144962 P y x)). Qed.
Lemma lem8226501 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8226502 {_144962 P : Type'} (y : _144962) (x : P) : (x = x) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226501 P x) (@lem8226500 _144962 P y x)). Qed.
Lemma lem8226503 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226502 _144962 P y x) (@lem8226488 P x)). Qed.
Lemma lem8226504 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term133 _144962 A B P p l g) = (term133 _144962 A B P p l g).
Proof. exact (eq_refl (term133 _144962 A B P p l g)). Qed.
Lemma lem8226505 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term134 _144962 A B P p l g y) = (term135 _144962 A B P p l g y x).
Proof. exact (MK_COMB (@lem8226504 _144962 A B P p l g) (@lem8226487 _144962 P y x)). Qed.
Lemma lem8226506 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : (term135 _144962 A B P p l g y x) = (term136 _144962 A B P p y x l g).
Proof. exact (eq_refl (term135 _144962 A B P p l g y x)). Qed.
Lemma lem8226507 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) : (term137 _144962 A B P p l g y) = (term137 _144962 A B P p l g y).
Proof. exact (eq_refl (term137 _144962 A B P p l g y)). Qed.
Lemma lem8226508 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : ((term134 _144962 A B P p l g y) = (term135 _144962 A B P p l g y x)) = ((term134 _144962 A B P p l g y) = (term136 _144962 A B P p y x l g)).
Proof. exact (MK_COMB (@lem8226507 _144962 A B P p l g y) (@lem8226506 _144962 A B P p y x l g)). Qed.
Lemma lem8226509 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : (term134 _144962 A B P p l g y) = (term138 _144962 A B P p y l g).
Proof. exact (eq_refl (term134 _144962 A B P p l g y)). Qed.
Lemma lem8226510 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8226511 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : (term137 _144962 A B P p l g y) = (term139 _144962 A B P p y l g).
Proof. exact (MK_COMB (@lem8226510 P) (@lem8226509 _144962 A B P p y l g)). Qed.
Lemma lem8226512 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : (term136 _144962 A B P p y x l g) = (term136 _144962 A B P p y x l g).
Proof. exact (eq_refl (term136 _144962 A B P p y x l g)). Qed.
Lemma lem8226513 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : ((term134 _144962 A B P p l g y) = (term136 _144962 A B P p y x l g)) = ((term138 _144962 A B P p y l g) = (term136 _144962 A B P p y x l g)).
Proof. exact (MK_COMB (@lem8226511 _144962 A B P p y l g) (@lem8226512 _144962 A B P p y x l g)). Qed.
Lemma lem8226514 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : ((term134 _144962 A B P p l g y) = (term135 _144962 A B P p l g y x)) = ((term138 _144962 A B P p y l g) = (term136 _144962 A B P p y x l g)).
Proof. exact (TRANS (@lem8226508 _144962 A B P p y x l g) (@lem8226513 _144962 A B P p y x l g)). Qed.
Lemma lem8226515 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (x : P) (l : type815 _144962 A B P) (g : A -> B) : (term138 _144962 A B P p y l g) = (term136 _144962 A B P p y x l g).
Proof. exact (EQ_MP (@lem8226514 _144962 A B P p y x l g) (@lem8226505 _144962 A B P p l g y x)). Qed.
Lemma lem8226516 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term140 _144962 A B P p y l g x) = (term141 _144962 A B P p l g y x).
Proof. exact (MK_COMB (@lem8226515 _144962 A B P p y x l g) (@lem8226503 _144962 P y x)). Qed.
Lemma lem8226517 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term141 _144962 A B P p l g y x) = (term142 _144962 A B P p l g y x).
Proof. exact (eq_refl (term141 _144962 A B P p l g y x)). Qed.
Lemma lem8226518 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term143 _144962 A B P p y l g x) = (term143 _144962 A B P p y l g x).
Proof. exact (eq_refl (term143 _144962 A B P p y l g x)). Qed.
Lemma lem8226519 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l g x) = (term141 _144962 A B P p l g y x)) = ((term140 _144962 A B P p y l g x) = (term142 _144962 A B P p l g y x)).
Proof. exact (MK_COMB (@lem8226518 _144962 A B P p y l g x) (@lem8226517 _144962 A B P p l g y x)). Qed.
Lemma lem8226520 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term140 _144962 A B P p y l g x) = (term144 _144962 A B P p y l g x).
Proof. exact (eq_refl (term140 _144962 A B P p y l g x)). Qed.
Lemma lem8226521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8226522 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term143 _144962 A B P p y l g x) = (term145 _144962 A B P p y l g x).
Proof. exact (MK_COMB (@lem8226521) (@lem8226520 _144962 A B P p y l g x)). Qed.
Lemma lem8226523 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term142 _144962 A B P p l g y x) = (term142 _144962 A B P p l g y x).
Proof. exact (eq_refl (term142 _144962 A B P p l g y x)). Qed.
Lemma lem8226524 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l g x) = (term142 _144962 A B P p l g y x)) = ((term144 _144962 A B P p y l g x) = (term142 _144962 A B P p l g y x)).
Proof. exact (MK_COMB (@lem8226522 _144962 A B P p y l g x) (@lem8226523 _144962 A B P p l g y x)). Qed.
Lemma lem8226525 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term140 _144962 A B P p y l g x) = (term141 _144962 A B P p l g y x)) = ((term144 _144962 A B P p y l g x) = (term142 _144962 A B P p l g y x)).
Proof. exact (TRANS (@lem8226519 _144962 A B P p l g y x) (@lem8226524 _144962 A B P p l g y x)). Qed.
Lemma lem8226526 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term144 _144962 A B P p y l g x) = (term142 _144962 A B P p l g y x).
Proof. exact (EQ_MP (@lem8226525 _144962 A B P p l g y x) (@lem8226516 _144962 A B P p l g y x)). Qed.
Lemma lem8226527 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term142 _144962 A B P p l g y x) = (term144 _144962 A B P p y l g x).
Proof. exact (SYM (@lem8226526 _144962 A B P p l g y x)). Qed.
Lemma lem8226528 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term146 _144962 A B P p l g y x) = (term142 _144962 A B P p l g y x).
Proof. exact (eq_refl (term146 _144962 A B P p l g y x)). Qed.
Lemma lem8226529 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term146 _144962 A B P p l g y x) = (term144 _144962 A B P p y l g x).
Proof. exact (TRANS (@lem8226528 _144962 A B P p l g y x) (@lem8226527 _144962 A B P p y l g x)). Qed.
Lemma lem8226530 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : term147 _144962 A B P p y l g.
Proof. exact (fun x : P => @lem8226529 _144962 A B P p y l g x). Qed.
Lemma lem8226531 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term148 _144962 A B P p l g.
Proof. exact (fun y : _144962 => @lem8226530 _144962 A B P p y l g). Qed.
Lemma lem8226532 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term149 _144962 A B P p l g.
Proof. exact (ex_intro (term150 _144962 A B P p l g) (term151 _144962 A B P p l g) (@lem8226531 _144962 A B P p l g)). Qed.
Lemma lem8226534 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8226535 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8226534 Prop a b). Qed.
Lemma lem8226536 {_144962 A B P : Type'} (_109427 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : ((term152 _144962 P _109427 y x) = (term144 _144962 A B P p y l g x)) = (term153 _144962 A B P _109427 p y l g x).
Proof. exact (@lem8226535 (term152 _144962 P _109427 y x) (term144 _144962 A B P p y l g x)). Qed.
Lemma lem8226537 {_144962 A B P : Type'} (_109427 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : (term154 _144962 A B P _109427 p y l g) = (term155 _144962 A B P _109427 p y l g).
Proof. exact (fun_ext (fun x : P => @lem8226536 _144962 A B P _109427 p y l g x)). Qed.
Lemma lem8226538 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226539 {_144962 A B P : Type'} (_109427 : type1210 _144962 P) (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : (term156 _144962 A B P _109427 p y l g) = (term157 _144962 A B P _109427 p y l g).
Proof. exact (MK_COMB (@lem8226538 P) (@lem8226537 _144962 A B P _109427 p y l g)). Qed.
Lemma lem8226540 {_144962 A B P : Type'} (_109427 : type1210 _144962 P) (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term158 _144962 A B P _109427 p l g) = (term159 _144962 A B P _109427 p l g).
Proof. exact (fun_ext (fun y : _144962 => @lem8226539 _144962 A B P _109427 p y l g)). Qed.
Lemma lem8226541 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226542 {_144962 A B P : Type'} (_109427 : type1210 _144962 P) (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term160 _144962 A B P _109427 p l g) = (term161 _144962 A B P _109427 p l g).
Proof. exact (MK_COMB (@lem8226541 _144962) (@lem8226540 _144962 A B P _109427 p l g)). Qed.
Lemma lem8226543 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term150 _144962 A B P p l g) = (term162 _144962 A B P p l g).
Proof. exact (fun_ext (fun _109427 : type1210 _144962 P => @lem8226542 _144962 A B P _109427 p l g)). Qed.
Lemma lem8226544 {_144962 P : Type'} : (@ex ((prod _144962 P) -> Prop)) = (@ex ((prod _144962 P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _144962 P) -> Prop))). Qed.
Lemma lem8226545 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term149 _144962 A B P p l g) = (term163 _144962 A B P p l g).
Proof. exact (MK_COMB (@lem8226544 _144962 P) (@lem8226543 _144962 A B P p l g)). Qed.
Lemma lem8226546 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term163 _144962 A B P p l g.
Proof. exact (EQ_MP (@lem8226545 _144962 A B P p l g) (@lem8226532 _144962 A B P p l g)). Qed.
Lemma lem8226548 {_5076 : Type'} (P : _5076 -> Prop) : term164 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8226549 {_144962 P : Type'} (P' : type324 _144962 P) : term165 _144962 P P'.
Proof. exact (@lem8226548 (type1210 _144962 P) P'). Qed.
Lemma lem8226550 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term166 _144962 A B P p l g.
Proof. exact (@lem8226549 _144962 P (term162 _144962 A B P p l g)). Qed.
Lemma lem8226551 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term167 _144962 A B P p l g.
Proof. exact (@lem8226550 _144962 A B P p l g (@lem8226546 _144962 A B P p l g)). Qed.
Lemma lem8226552 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term167 _144962 A B P p l g) = (term168 _144962 A B P p l g).
Proof. exact (eq_refl (term167 _144962 A B P p l g)). Qed.
Lemma lem8226553 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) : term168 _144962 A B P p l g.
Proof. exact (EQ_MP (@lem8226552 _144962 A B P p l g) (@lem8226551 _144962 A B P p l g)). Qed.
Lemma lem8226554 {_144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (g : A -> B) (y : _144962) : term169 _144962 A B P p l g y.
Proof. exact (@lem8226553 _144962 A B P p l g y). Qed.
Lemma lem8226555 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : (term169 _144962 A B P p l g y) = (term170 _144962 A B P p y l g).
Proof. exact (eq_refl (term169 _144962 A B P p l g y)). Qed.
Lemma lem8226556 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) : term170 _144962 A B P p y l g.
Proof. exact (EQ_MP (@lem8226555 _144962 A B P p y l g) (@lem8226554 _144962 A B P p l g y)). Qed.
Lemma lem8226557 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : term171 _144962 A B P p y l g x.
Proof. exact (@lem8226556 _144962 A B P p y l g x). Qed.
Lemma lem8226558 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term171 _144962 A B P p y l g x) = (term172 _144962 A B P p y l g x).
Proof. exact (eq_refl (term171 _144962 A B P p y l g x)). Qed.
Lemma lem8226559 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : term172 _144962 A B P p y l g x.
Proof. exact (EQ_MP (@lem8226558 _144962 A B P p y l g x) (@lem8226557 _144962 A B P p y l g x)). Qed.
Lemma lem8226561 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8226562 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8226561 Prop a b). Qed.
Lemma lem8226563 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term172 _144962 A B P p y l g x) = ((term125 _144962 A B P p l g y x) = (term144 _144962 A B P p y l g x)).
Proof. exact (@lem8226562 (term125 _144962 A B P p l g y x) (term144 _144962 A B P p y l g x)). Qed.
Lemma lem8226564 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term125 _144962 A B P p l g y x) = (term144 _144962 A B P p y l g x).
Proof. exact (EQ_MP (@lem8226563 _144962 A B P p y l g x) (@lem8226559 _144962 A B P p y l g x)). Qed.
Lemma lem8226565 {_144962 A B P : Type'} (p : type560 A B P) (y : _144962) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term125 _144962 A B P p l g y x) = (term144 _144962 A B P p y l g x).
Proof. exact (@lem8226564 _144962 A B P p y l g x). Qed.
Lemma lem8226566 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term125 _144962 A B P p l g p1 p2) = (term144 _144962 A B P p p1 l g p2).
Proof. exact (@lem8226565 _144962 A B P p p1 l g p2). Qed.
Lemma lem8226569 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term124 _144962 A B P p l g p1 p2) = (term144 _144962 A B P p p1 l g p2).
Proof. exact (TRANS (@lem8226467 _144962 A B P p l g p1 p2) (@lem8226566 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8226570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8226571 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term173 _144962 A B P p l g p1 p2) = (term174 _144962 A B P p p1 l g p2).
Proof. exact (MK_COMB (@lem8226570) (@lem8226569 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8226580 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a0 = (term126 _144962 P a0 a1).
Proof. exact (@lem51128 _144962 P a0 a1). Qed.
Lemma lem8226581 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (@lem8226580 _144962 P y x). Qed.
Lemma lem8226582 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a1 = (term127 _144962 P a0 a1).
Proof. exact (@lem51159 _144962 P a0 a1). Qed.
Lemma lem8226583 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (@lem8226582 _144962 P y x). Qed.
Lemma lem8226584 {_144962 : Type'} (y : _144962) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8226585 {_144962 : Type'} : (term128 _144962) = (term128 _144962).
Proof. exact (eq_refl (term128 _144962)). Qed.
Lemma lem8226586 {_144962 P : Type'} (y : _144962) (x : P) : (term129 _144962 y) = (term130 _144962 P y x).
Proof. exact (MK_COMB (@lem8226585 _144962) (@lem8226581 _144962 P y x)). Qed.
Lemma lem8226587 {_144962 P : Type'} (y : _144962) (x : P) : (term130 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term130 _144962 P y x)). Qed.
Lemma lem8226588 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (term131 _144962 y).
Proof. exact (eq_refl (term131 _144962 y)). Qed.
Lemma lem8226589 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = ((term129 _144962 y) = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226588 _144962 y) (@lem8226587 _144962 P y x)). Qed.
Lemma lem8226590 {_144962 : Type'} (y : _144962) : (term129 _144962 y) = y.
Proof. exact (eq_refl (term129 _144962 y)). Qed.
Lemma lem8226591 {_144962 : Type'} : (@eq _144962) = (@eq _144962).
Proof. exact (eq_refl (@eq _144962)). Qed.
Lemma lem8226592 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (@eq _144962 y).
Proof. exact (MK_COMB (@lem8226591 _144962) (@lem8226590 _144962 y)). Qed.
Lemma lem8226593 {_144962 P : Type'} (y : _144962) (x : P) : (term126 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term126 _144962 P y x)). Qed.
Lemma lem8226594 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term126 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226592 _144962 y) (@lem8226593 _144962 P y x)). Qed.
Lemma lem8226595 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (TRANS (@lem8226589 _144962 P y x) (@lem8226594 _144962 P y x)). Qed.
Lemma lem8226596 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226595 _144962 P y x) (@lem8226586 _144962 P y x)). Qed.
Lemma lem8226597 {_144962 : Type'} (y : _144962) : (@eq _144962 y) = (@eq _144962 y).
Proof. exact (eq_refl (@eq _144962 y)). Qed.
Lemma lem8226598 {_144962 P : Type'} (y : _144962) (x : P) : (y = y) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226597 _144962 y) (@lem8226596 _144962 P y x)). Qed.
Lemma lem8226599 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226598 _144962 P y x) (@lem8226584 _144962 y)). Qed.
Lemma lem8226600 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8226601 {P : Type'} : (term128 P) = (term128 P).
Proof. exact (eq_refl (term128 P)). Qed.
Lemma lem8226602 {_144962 P : Type'} (y : _144962) (x : P) : (term129 P x) = (term132 _144962 P y x).
Proof. exact (MK_COMB (@lem8226601 P) (@lem8226583 _144962 P y x)). Qed.
Lemma lem8226603 {_144962 P : Type'} (y : _144962) (x : P) : (term132 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term132 _144962 P y x)). Qed.
Lemma lem8226604 {P : Type'} (x : P) : (term131 P x) = (term131 P x).
Proof. exact (eq_refl (term131 P x)). Qed.
Lemma lem8226605 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = ((term129 P x) = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226604 P x) (@lem8226603 _144962 P y x)). Qed.
Lemma lem8226606 {P : Type'} (x : P) : (term129 P x) = x.
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem8226607 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8226608 {P : Type'} (x : P) : (term131 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8226607 P) (@lem8226606 P x)). Qed.
Lemma lem8226609 {_144962 P : Type'} (y : _144962) (x : P) : (term127 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term127 _144962 P y x)). Qed.
Lemma lem8226610 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term127 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226608 P x) (@lem8226609 _144962 P y x)). Qed.
Lemma lem8226611 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (TRANS (@lem8226605 _144962 P y x) (@lem8226610 _144962 P y x)). Qed.
Lemma lem8226612 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226611 _144962 P y x) (@lem8226602 _144962 P y x)). Qed.
Lemma lem8226613 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8226614 {_144962 P : Type'} (y : _144962) (x : P) : (x = x) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226613 P x) (@lem8226612 _144962 P y x)). Qed.
Lemma lem8226615 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226614 _144962 P y x) (@lem8226600 P x)). Qed.
Lemma lem8226616 {_144947 _144962 P : Type'} (s : P -> _144947) : (term175 _144947 _144962 P s) = (term175 _144947 _144962 P s).
Proof. exact (eq_refl (term175 _144947 _144962 P s)). Qed.
Lemma lem8226617 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (term176 _144947 _144962 P s y) = (term177 _144947 _144962 P s y x).
Proof. exact (MK_COMB (@lem8226616 _144947 _144962 P s) (@lem8226599 _144962 P y x)). Qed.
Lemma lem8226618 {_144947 _144962 P : Type'} (y : _144962) (x : P) (s : P -> _144947) : (term177 _144947 _144962 P s y x) = (term178 _144947 P s).
Proof. exact (eq_refl (term177 _144947 _144962 P s y x)). Qed.
Lemma lem8226619 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) : (term179 _144947 _144962 P s y) = (term179 _144947 _144962 P s y).
Proof. exact (eq_refl (term179 _144947 _144962 P s y)). Qed.
Lemma lem8226620 {_144947 _144962 P : Type'} (x : P) (y : _144962) (s : P -> _144947) : ((term176 _144947 _144962 P s y) = (term177 _144947 _144962 P s y x)) = ((term176 _144947 _144962 P s y) = (term178 _144947 P s)).
Proof. exact (MK_COMB (@lem8226619 _144947 _144962 P s y) (@lem8226618 _144947 _144962 P y x s)). Qed.
Lemma lem8226621 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : (term176 _144947 _144962 P s y) = (term178 _144947 P s).
Proof. exact (eq_refl (term176 _144947 _144962 P s y)). Qed.
Lemma lem8226622 {_144947 P : Type'} : (@eq (P -> _144947)) = (@eq (P -> _144947)).
Proof. exact (eq_refl (@eq (P -> _144947))). Qed.
Lemma lem8226623 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : (term179 _144947 _144962 P s y) = (term180 _144947 P s).
Proof. exact (MK_COMB (@lem8226622 _144947 P) (@lem8226621 _144947 _144962 P y s)). Qed.
Lemma lem8226624 {_144947 P : Type'} (s : P -> _144947) : (term178 _144947 P s) = (term178 _144947 P s).
Proof. exact (eq_refl (term178 _144947 P s)). Qed.
Lemma lem8226625 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : ((term176 _144947 _144962 P s y) = (term178 _144947 P s)) = ((term178 _144947 P s) = (term178 _144947 P s)).
Proof. exact (MK_COMB (@lem8226623 _144947 _144962 P y s) (@lem8226624 _144947 P s)). Qed.
Lemma lem8226626 {_144947 _144962 P : Type'} (y : _144962) (x : P) (s : P -> _144947) : ((term176 _144947 _144962 P s y) = (term177 _144947 _144962 P s y x)) = ((term178 _144947 P s) = (term178 _144947 P s)).
Proof. exact (TRANS (@lem8226620 _144947 _144962 P x y s) (@lem8226625 _144947 _144962 P y s)). Qed.
Lemma lem8226627 {_144947 P : Type'} (s : P -> _144947) : (term178 _144947 P s) = (term178 _144947 P s).
Proof. exact (EQ_MP (@lem8226626 _144947 Prop P (@el Prop) (@el P) s) (@lem8226617 _144947 Prop P s (@el Prop) (@el P))). Qed.
Lemma lem8226628 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (term181 _144947 P s x) = (term182 _144947 _144962 P s y x).
Proof. exact (MK_COMB (@lem8226627 _144947 P s) (@lem8226615 _144962 P y x)). Qed.
Lemma lem8226629 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (term182 _144947 _144962 P s y x) = (term183 _144947 _144962 P s y x).
Proof. exact (eq_refl (term182 _144947 _144962 P s y x)). Qed.
Lemma lem8226630 {_144947 P : Type'} (s : P -> _144947) (x : P) : (term184 _144947 P s x) = (term184 _144947 P s x).
Proof. exact (eq_refl (term184 _144947 P s x)). Qed.
Lemma lem8226631 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : ((term181 _144947 P s x) = (term182 _144947 _144962 P s y x)) = ((term181 _144947 P s x) = (term183 _144947 _144962 P s y x)).
Proof. exact (MK_COMB (@lem8226630 _144947 P s x) (@lem8226629 _144947 _144962 P s y x)). Qed.
Lemma lem8226632 {_144947 P : Type'} (s : P -> _144947) (x : P) : (term181 _144947 P s x) = (s x).
Proof. exact (eq_refl (term181 _144947 P s x)). Qed.
Lemma lem8226633 {_144947 : Type'} : (@eq _144947) = (@eq _144947).
Proof. exact (eq_refl (@eq _144947)). Qed.
Lemma lem8226634 {_144947 P : Type'} (s : P -> _144947) (x : P) : (term184 _144947 P s x) = (term185 _144947 P s x).
Proof. exact (MK_COMB (@lem8226633 _144947) (@lem8226632 _144947 P s x)). Qed.
Lemma lem8226635 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (term183 _144947 _144962 P s y x) = (term183 _144947 _144962 P s y x).
Proof. exact (eq_refl (term183 _144947 _144962 P s y x)). Qed.
Lemma lem8226636 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : ((term181 _144947 P s x) = (term183 _144947 _144962 P s y x)) = ((s x) = (term183 _144947 _144962 P s y x)).
Proof. exact (MK_COMB (@lem8226634 _144947 P s x) (@lem8226635 _144947 _144962 P s y x)). Qed.
Lemma lem8226637 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : ((term181 _144947 P s x) = (term182 _144947 _144962 P s y x)) = ((s x) = (term183 _144947 _144962 P s y x)).
Proof. exact (TRANS (@lem8226631 _144947 _144962 P s y x) (@lem8226636 _144947 _144962 P s y x)). Qed.
Lemma lem8226638 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (s x) = (term183 _144947 _144962 P s y x).
Proof. exact (EQ_MP (@lem8226637 _144947 _144962 P s y x) (@lem8226628 _144947 _144962 P s y x)). Qed.
Lemma lem8226639 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term183 _144947 _144962 P s y x) = (s x).
Proof. exact (SYM (@lem8226638 _144947 _144962 P s y x)). Qed.
Lemma lem8226640 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) (x : P) : (term186 _144947 _144962 P s y x) = (term183 _144947 _144962 P s y x).
Proof. exact (eq_refl (term186 _144947 _144962 P s y x)). Qed.
Lemma lem8226641 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term186 _144947 _144962 P s y x) = (s x).
Proof. exact (TRANS (@lem8226640 _144947 _144962 P s y x) (@lem8226639 _144947 _144962 P y s x)). Qed.
Lemma lem8226642 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : term187 _144947 _144962 P y s.
Proof. exact (fun x : P => @lem8226641 _144947 _144962 P y s x). Qed.
Lemma lem8226643 {_144947 _144962 P : Type'} (s : P -> _144947) : term188 _144947 _144962 P s.
Proof. exact (fun y : _144962 => @lem8226642 _144947 _144962 P y s). Qed.
Lemma lem8226644 {_144947 _144962 P : Type'} (s : P -> _144947) : term189 _144947 _144962 P s.
Proof. exact (ex_intro (term190 _144947 _144962 P s) (term191 _144947 _144962 P s) (@lem8226643 _144947 _144962 P s)). Qed.
Lemma lem8226646 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8226647 {_144947 : Type'} (a : _144947) (b : _144947) : (a = b) = (@GEQ _144947 a b).
Proof. exact (@lem8226646 _144947 a b). Qed.
Lemma lem8226648 {_144947 _144962 P : Type'} (_109439 : type1224 _144947 _144962 P) (y : _144962) (s : P -> _144947) (x : P) : ((term192 _144947 _144962 P _109439 y x) = (s x)) = (term193 _144947 _144962 P _109439 y s x).
Proof. exact (@lem8226647 _144947 (term192 _144947 _144962 P _109439 y x) (s x)). Qed.
Lemma lem8226649 {_144947 _144962 P : Type'} (_109439 : type1224 _144947 _144962 P) (y : _144962) (s : P -> _144947) : (term194 _144947 _144962 P _109439 y s) = (term195 _144947 _144962 P _109439 y s).
Proof. exact (fun_ext (fun x : P => @lem8226648 _144947 _144962 P _109439 y s x)). Qed.
Lemma lem8226650 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226651 {_144947 _144962 P : Type'} (_109439 : type1224 _144947 _144962 P) (y : _144962) (s : P -> _144947) : (term196 _144947 _144962 P _109439 y s) = (term197 _144947 _144962 P _109439 y s).
Proof. exact (MK_COMB (@lem8226650 P) (@lem8226649 _144947 _144962 P _109439 y s)). Qed.
Lemma lem8226652 {_144947 _144962 P : Type'} (_109439 : type1224 _144947 _144962 P) (s : P -> _144947) : (term198 _144947 _144962 P _109439 s) = (term199 _144947 _144962 P _109439 s).
Proof. exact (fun_ext (fun y : _144962 => @lem8226651 _144947 _144962 P _109439 y s)). Qed.
Lemma lem8226653 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226654 {_144947 _144962 P : Type'} (_109439 : type1224 _144947 _144962 P) (s : P -> _144947) : (term200 _144947 _144962 P _109439 s) = (term201 _144947 _144962 P _109439 s).
Proof. exact (MK_COMB (@lem8226653 _144962) (@lem8226652 _144947 _144962 P _109439 s)). Qed.
Lemma lem8226655 {_144947 _144962 P : Type'} (s : P -> _144947) : (term190 _144947 _144962 P s) = (term202 _144947 _144962 P s).
Proof. exact (fun_ext (fun _109439 : type1224 _144947 _144962 P => @lem8226654 _144947 _144962 P _109439 s)). Qed.
Lemma lem8226656 {_144947 _144962 P : Type'} : (@ex ((prod _144962 P) -> _144947)) = (@ex ((prod _144962 P) -> _144947)).
Proof. exact (eq_refl (@ex ((prod _144962 P) -> _144947))). Qed.
Lemma lem8226657 {_144947 _144962 P : Type'} (s : P -> _144947) : (term189 _144947 _144962 P s) = (term203 _144947 _144962 P s).
Proof. exact (MK_COMB (@lem8226656 _144947 _144962 P) (@lem8226655 _144947 _144962 P s)). Qed.
Lemma lem8226658 {_144947 _144962 P : Type'} (s : P -> _144947) : term203 _144947 _144962 P s.
Proof. exact (EQ_MP (@lem8226657 _144947 _144962 P s) (@lem8226644 _144947 _144962 P s)). Qed.
Lemma lem8226660 {_5076 : Type'} (P : _5076 -> Prop) : term164 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8226661 {_144947 _144962 P : Type'} (P' : type331 _144947 _144962 P) : term204 _144947 _144962 P P'.
Proof. exact (@lem8226660 (type1224 _144947 _144962 P) P'). Qed.
Lemma lem8226662 {_144947 _144962 P : Type'} (s : P -> _144947) : term205 _144947 _144962 P s.
Proof. exact (@lem8226661 _144947 _144962 P (term202 _144947 _144962 P s)). Qed.
Lemma lem8226663 {_144947 _144962 P : Type'} (s : P -> _144947) : term206 _144947 _144962 P s.
Proof. exact (@lem8226662 _144947 _144962 P s (@lem8226658 _144947 _144962 P s)). Qed.
Lemma lem8226664 {_144947 _144962 P : Type'} (s : P -> _144947) : (term206 _144947 _144962 P s) = (term207 _144947 _144962 P s).
Proof. exact (eq_refl (term206 _144947 _144962 P s)). Qed.
Lemma lem8226665 {_144947 _144962 P : Type'} (s : P -> _144947) : term207 _144947 _144962 P s.
Proof. exact (EQ_MP (@lem8226664 _144947 _144962 P s) (@lem8226663 _144947 _144962 P s)). Qed.
Lemma lem8226666 {_144947 _144962 P : Type'} (s : P -> _144947) (y : _144962) : term208 _144947 _144962 P s y.
Proof. exact (@lem8226665 _144947 _144962 P s y). Qed.
Lemma lem8226667 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : (term208 _144947 _144962 P s y) = (term209 _144947 _144962 P y s).
Proof. exact (eq_refl (term208 _144947 _144962 P s y)). Qed.
Lemma lem8226668 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) : term209 _144947 _144962 P y s.
Proof. exact (EQ_MP (@lem8226667 _144947 _144962 P y s) (@lem8226666 _144947 _144962 P s y)). Qed.
Lemma lem8226669 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : term210 _144947 _144962 P y s x.
Proof. exact (@lem8226668 _144947 _144962 P y s x). Qed.
Lemma lem8226670 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term210 _144947 _144962 P y s x) = (term211 _144947 _144962 P y s x).
Proof. exact (eq_refl (term210 _144947 _144962 P y s x)). Qed.
Lemma lem8226671 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : term211 _144947 _144962 P y s x.
Proof. exact (EQ_MP (@lem8226670 _144947 _144962 P y s x) (@lem8226669 _144947 _144962 P y s x)). Qed.
Lemma lem8226673 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8226674 {_144947 : Type'} (a : _144947) (b : _144947) : (@GEQ _144947 a b) = (a = b).
Proof. exact (@lem8226673 _144947 a b). Qed.
Lemma lem8226675 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term211 _144947 _144962 P y s x) = ((term212 _144947 _144962 P s y x) = (s x)).
Proof. exact (@lem8226674 _144947 (term212 _144947 _144962 P s y x) (s x)). Qed.
Lemma lem8226676 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term212 _144947 _144962 P s y x) = (s x).
Proof. exact (EQ_MP (@lem8226675 _144947 _144962 P y s x) (@lem8226671 _144947 _144962 P y s x)). Qed.
Lemma lem8226677 {_144947 _144962 P : Type'} (y : _144962) (s : P -> _144947) (x : P) : (term212 _144947 _144962 P s y x) = (s x).
Proof. exact (@lem8226676 _144947 _144962 P y s x). Qed.
Lemma lem8226678 {_144947 _144962 P : Type'} (p1 : _144962) (s : P -> _144947) (p2 : P) : (term212 _144947 _144962 P s p1 p2) = (s p2).
Proof. exact (@lem8226677 _144947 _144962 P p1 s p2). Qed.
Lemma lem8226679 {_144947 A : Type'} (lt2 : type1470 _144947 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8226680 {_144947 _144962 A P : Type'} (p1 : _144962) (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (p2 : P) : (term213 _144947 _144962 A P lt2 z s p1 p2) = (term214 _144947 A P lt2 z s p2).
Proof. exact (MK_COMB (@lem8226679 _144947 A lt2 z) (@lem8226678 _144947 _144962 P p1 s p2)). Qed.
Lemma lem8226681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8226682 {_144947 _144962 A P : Type'} (p1 : _144962) (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (p2 : P) : (term215 _144947 _144962 A P lt2 z s p1 p2) = (term216 _144947 A P lt2 z s p2).
Proof. exact (MK_COMB (@lem8226681) (@lem8226680 _144947 _144962 A P p1 lt2 z s p2)). Qed.
Lemma lem8226685 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((f z) = (g z)).
Proof. exact (eq_refl ((f z) = (g z))). Qed.
Lemma lem8226686 {_144947 _144962 A B P : Type'} (p1 : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term217 _144947 _144962 A B P lt2 s p1 p2 f g z) = (term218 _144947 A B P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8226682 _144947 _144962 A P p1 lt2 z s p2) (@lem8226685 A B f g z)). Qed.
Lemma lem8226689 {_144947 _144962 A B P : Type'} (p1 : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term219 _144947 _144962 A B P lt2 s p1 p2 f g) = (term220 _144947 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8226686 _144947 _144962 A B P p1 lt2 s p2 f g z)). Qed.
Lemma lem8226690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8226691 {_144947 _144962 A B P : Type'} (p1 : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term221 _144947 _144962 A B P lt2 s p1 p2 f g) = (term222 _144947 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8226690 A) (@lem8226689 _144947 _144962 A B P p1 lt2 s p2 f g)). Qed.
Lemma lem8226698 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term223 _144947 _144962 A B P p l lt2 s p1 p2 f g) = (term224 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8226571 _144962 A B P p p1 l g p2) (@lem8226691 _144947 _144962 A B P p1 lt2 s p2 f g)). Qed.
Lemma lem8226701 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term225 _144947 _144962 A B P p l lt2 s p1 p2 f g) = (term226 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8226436 _144962 A B P p p1 l f p2) (@lem8226698 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8226704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8226705 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term227 _144947 _144962 A B P p l lt2 s p1 p2 f g) = (term228 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8226704) (@lem8226701 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8226709 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8226710 {_144956 _144962 A B P : Type'} (f : type888 _144956 _144962 A B P) (y : A -> B) : (term229 _144956 _144962 A B P f y) = (f y).
Proof. exact (@lem8226709 (A -> B) (type1224 _144956 _144962 P) f y). Qed.
Lemma lem8226711 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term230 _144956 _144962 A B P h f) = (term231 _144956 _144962 A B P h f).
Proof. exact (@lem8226710 _144956 _144962 A B P (term95 _144956 _144962 A B P h) f). Qed.
Lemma lem8226712 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term231 _144956 _144962 A B P h f) = (term232 _144956 _144962 A B P h f).
Proof. exact (eq_refl (term231 _144956 _144962 A B P h f)). Qed.
Lemma lem8226713 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) : (term233 _144956 _144962 A B P h) = (term95 _144956 _144962 A B P h).
Proof. exact (fun_ext (fun f : A -> B => @lem8226712 _144956 _144962 A B P h f)). Qed.
Lemma lem8226714 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8226715 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term230 _144956 _144962 A B P h f) = (term231 _144956 _144962 A B P h f).
Proof. exact (MK_COMB (@lem8226713 _144956 _144962 A B P h) (@lem8226714 A B f)). Qed.
Lemma lem8226716 {_144956 _144962 P : Type'} : (@eq ((prod _144962 P) -> _144956)) = (@eq ((prod _144962 P) -> _144956)).
Proof. exact (eq_refl (@eq ((prod _144962 P) -> _144956))). Qed.
Lemma lem8226717 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term234 _144956 _144962 A B P h f) = (term235 _144956 _144962 A B P h f).
Proof. exact (MK_COMB (@lem8226716 _144956 _144962 P) (@lem8226715 _144956 _144962 A B P h f)). Qed.
Lemma lem8226718 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term231 _144956 _144962 A B P h f) = (term232 _144956 _144962 A B P h f).
Proof. exact (eq_refl (term231 _144956 _144962 A B P h f)). Qed.
Lemma lem8226719 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : ((term230 _144956 _144962 A B P h f) = (term231 _144956 _144962 A B P h f)) = ((term231 _144956 _144962 A B P h f) = (term232 _144956 _144962 A B P h f)).
Proof. exact (MK_COMB (@lem8226717 _144956 _144962 A B P h f) (@lem8226718 _144956 _144962 A B P h f)). Qed.
Lemma lem8226720 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term231 _144956 _144962 A B P h f) = (term232 _144956 _144962 A B P h f).
Proof. exact (EQ_MP (@lem8226719 _144956 _144962 A B P h f) (@lem8226711 _144956 _144962 A B P h f)). Qed.
Lemma lem8226733 {_144962 P : Type'} (p1 : _144962) (p2 : P) : (@pair _144962 P p1 p2) = (@pair _144962 P p1 p2).
Proof. exact (eq_refl (@pair _144962 P p1 p2)). Qed.
Lemma lem8226734 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (p1 : _144962) (p2 : P) : (term236 _144956 _144962 A B P h f p1 p2) = (term237 _144956 _144962 A B P h f p1 p2).
Proof. exact (MK_COMB (@lem8226720 _144956 _144962 A B P h f) (@lem8226733 _144962 P p1 p2)). Qed.
Lemma lem8226735 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a0 = (term126 _144962 P a0 a1).
Proof. exact (@lem51128 _144962 P a0 a1). Qed.
Lemma lem8226736 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (@lem8226735 _144962 P y x). Qed.
Lemma lem8226737 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a1 = (term127 _144962 P a0 a1).
Proof. exact (@lem51159 _144962 P a0 a1). Qed.
Lemma lem8226738 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (@lem8226737 _144962 P y x). Qed.
Lemma lem8226739 {_144962 : Type'} (y : _144962) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8226740 {_144962 : Type'} : (term128 _144962) = (term128 _144962).
Proof. exact (eq_refl (term128 _144962)). Qed.
Lemma lem8226741 {_144962 P : Type'} (y : _144962) (x : P) : (term129 _144962 y) = (term130 _144962 P y x).
Proof. exact (MK_COMB (@lem8226740 _144962) (@lem8226736 _144962 P y x)). Qed.
Lemma lem8226742 {_144962 P : Type'} (y : _144962) (x : P) : (term130 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term130 _144962 P y x)). Qed.
Lemma lem8226743 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (term131 _144962 y).
Proof. exact (eq_refl (term131 _144962 y)). Qed.
Lemma lem8226744 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = ((term129 _144962 y) = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226743 _144962 y) (@lem8226742 _144962 P y x)). Qed.
Lemma lem8226745 {_144962 : Type'} (y : _144962) : (term129 _144962 y) = y.
Proof. exact (eq_refl (term129 _144962 y)). Qed.
Lemma lem8226746 {_144962 : Type'} : (@eq _144962) = (@eq _144962).
Proof. exact (eq_refl (@eq _144962)). Qed.
Lemma lem8226747 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (@eq _144962 y).
Proof. exact (MK_COMB (@lem8226746 _144962) (@lem8226745 _144962 y)). Qed.
Lemma lem8226748 {_144962 P : Type'} (y : _144962) (x : P) : (term126 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term126 _144962 P y x)). Qed.
Lemma lem8226749 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term126 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226747 _144962 y) (@lem8226748 _144962 P y x)). Qed.
Lemma lem8226750 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (TRANS (@lem8226744 _144962 P y x) (@lem8226749 _144962 P y x)). Qed.
Lemma lem8226751 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226750 _144962 P y x) (@lem8226741 _144962 P y x)). Qed.
Lemma lem8226752 {_144962 : Type'} (y : _144962) : (@eq _144962 y) = (@eq _144962 y).
Proof. exact (eq_refl (@eq _144962 y)). Qed.
Lemma lem8226753 {_144962 P : Type'} (y : _144962) (x : P) : (y = y) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226752 _144962 y) (@lem8226751 _144962 P y x)). Qed.
Lemma lem8226754 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226753 _144962 P y x) (@lem8226739 _144962 y)). Qed.
Lemma lem8226755 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8226756 {P : Type'} : (term128 P) = (term128 P).
Proof. exact (eq_refl (term128 P)). Qed.
Lemma lem8226757 {_144962 P : Type'} (y : _144962) (x : P) : (term129 P x) = (term132 _144962 P y x).
Proof. exact (MK_COMB (@lem8226756 P) (@lem8226738 _144962 P y x)). Qed.
Lemma lem8226758 {_144962 P : Type'} (y : _144962) (x : P) : (term132 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term132 _144962 P y x)). Qed.
Lemma lem8226759 {P : Type'} (x : P) : (term131 P x) = (term131 P x).
Proof. exact (eq_refl (term131 P x)). Qed.
Lemma lem8226760 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = ((term129 P x) = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226759 P x) (@lem8226758 _144962 P y x)). Qed.
Lemma lem8226761 {P : Type'} (x : P) : (term129 P x) = x.
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem8226762 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8226763 {P : Type'} (x : P) : (term131 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8226762 P) (@lem8226761 P x)). Qed.
Lemma lem8226764 {_144962 P : Type'} (y : _144962) (x : P) : (term127 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term127 _144962 P y x)). Qed.
Lemma lem8226765 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term127 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226763 P x) (@lem8226764 _144962 P y x)). Qed.
Lemma lem8226766 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (TRANS (@lem8226760 _144962 P y x) (@lem8226765 _144962 P y x)). Qed.
Lemma lem8226767 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226766 _144962 P y x) (@lem8226757 _144962 P y x)). Qed.
Lemma lem8226768 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8226769 {_144962 P : Type'} (y : _144962) (x : P) : (x = x) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226768 P x) (@lem8226767 _144962 P y x)). Qed.
Lemma lem8226770 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226769 _144962 P y x) (@lem8226755 P x)). Qed.
Lemma lem8226771 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term238 _144956 _144962 A B P h f) = (term238 _144956 _144962 A B P h f).
Proof. exact (eq_refl (term238 _144956 _144962 A B P h f)). Qed.
Lemma lem8226772 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term239 _144956 _144962 A B P h f y) = (term240 _144956 _144962 A B P h f y x).
Proof. exact (MK_COMB (@lem8226771 _144956 _144962 A B P h f) (@lem8226754 _144962 P y x)). Qed.
Lemma lem8226773 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term240 _144956 _144962 A B P h f y x) = (term241 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term240 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226774 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term242 _144956 _144962 A B P h f y) = (term242 _144956 _144962 A B P h f y).
Proof. exact (eq_refl (term242 _144956 _144962 A B P h f y)). Qed.
Lemma lem8226775 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h f y) = (term240 _144956 _144962 A B P h f y x)) = ((term239 _144956 _144962 A B P h f y) = (term241 _144956 _144962 A B P h f y x)).
Proof. exact (MK_COMB (@lem8226774 _144956 _144962 A B P h f y) (@lem8226773 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226776 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term239 _144956 _144962 A B P h f y) = (term243 _144956 _144962 A B P h f y).
Proof. exact (eq_refl (term239 _144956 _144962 A B P h f y)). Qed.
Lemma lem8226777 {_144956 P : Type'} : (@eq (P -> _144956)) = (@eq (P -> _144956)).
Proof. exact (eq_refl (@eq (P -> _144956))). Qed.
Lemma lem8226778 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term242 _144956 _144962 A B P h f y) = (term244 _144956 _144962 A B P h f y).
Proof. exact (MK_COMB (@lem8226777 _144956 P) (@lem8226776 _144956 _144962 A B P h f y)). Qed.
Lemma lem8226779 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term241 _144956 _144962 A B P h f y x) = (term241 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term241 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226780 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h f y) = (term241 _144956 _144962 A B P h f y x)) = ((term243 _144956 _144962 A B P h f y) = (term241 _144956 _144962 A B P h f y x)).
Proof. exact (MK_COMB (@lem8226778 _144956 _144962 A B P h f y) (@lem8226779 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226781 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h f y) = (term240 _144956 _144962 A B P h f y x)) = ((term243 _144956 _144962 A B P h f y) = (term241 _144956 _144962 A B P h f y x)).
Proof. exact (TRANS (@lem8226775 _144956 _144962 A B P h f y x) (@lem8226780 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226782 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term243 _144956 _144962 A B P h f y) = (term241 _144956 _144962 A B P h f y x).
Proof. exact (EQ_MP (@lem8226781 _144956 _144962 A B P h f y x) (@lem8226772 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226783 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term245 _144956 _144962 A B P h f y x) = (term246 _144956 _144962 A B P h f y x).
Proof. exact (MK_COMB (@lem8226782 _144956 _144962 A B P h f y x) (@lem8226770 _144962 P y x)). Qed.
Lemma lem8226784 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term246 _144956 _144962 A B P h f y x) = (term247 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term246 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226785 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term248 _144956 _144962 A B P h f y x) = (term248 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term248 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226786 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h f y x) = (term246 _144956 _144962 A B P h f y x)) = ((term245 _144956 _144962 A B P h f y x) = (term247 _144956 _144962 A B P h f y x)).
Proof. exact (MK_COMB (@lem8226785 _144956 _144962 A B P h f y x) (@lem8226784 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226787 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term245 _144956 _144962 A B P h f y x) = (h f x y).
Proof. exact (eq_refl (term245 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226788 {_144956 : Type'} : (@eq _144956) = (@eq _144956).
Proof. exact (eq_refl (@eq _144956)). Qed.
Lemma lem8226789 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term248 _144956 _144962 A B P h f y x) = (term249 _144956 _144962 A B P h f x y).
Proof. exact (MK_COMB (@lem8226788 _144956) (@lem8226787 _144956 _144962 A B P h f x y)). Qed.
Lemma lem8226790 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term247 _144956 _144962 A B P h f y x) = (term247 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term247 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226791 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h f y x) = (term247 _144956 _144962 A B P h f y x)) = ((h f x y) = (term247 _144956 _144962 A B P h f y x)).
Proof. exact (MK_COMB (@lem8226789 _144956 _144962 A B P h f x y) (@lem8226790 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226792 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h f y x) = (term246 _144956 _144962 A B P h f y x)) = ((h f x y) = (term247 _144956 _144962 A B P h f y x)).
Proof. exact (TRANS (@lem8226786 _144956 _144962 A B P h f y x) (@lem8226791 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226793 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (h f x y) = (term247 _144956 _144962 A B P h f y x).
Proof. exact (EQ_MP (@lem8226792 _144956 _144962 A B P h f y x) (@lem8226783 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226794 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term247 _144956 _144962 A B P h f y x) = (h f x y).
Proof. exact (SYM (@lem8226793 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226795 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : (term250 _144956 _144962 A B P h f y x) = (term247 _144956 _144962 A B P h f y x).
Proof. exact (eq_refl (term250 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226796 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term250 _144956 _144962 A B P h f y x) = (h f x y).
Proof. exact (TRANS (@lem8226795 _144956 _144962 A B P h f y x) (@lem8226794 _144956 _144962 A B P h f x y)). Qed.
Lemma lem8226797 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : term251 _144956 _144962 A B P h f y.
Proof. exact (fun x : P => @lem8226796 _144956 _144962 A B P h f x y). Qed.
Lemma lem8226798 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term252 _144956 _144962 A B P h f.
Proof. exact (fun y : _144962 => @lem8226797 _144956 _144962 A B P h f y). Qed.
Lemma lem8226799 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term253 _144956 _144962 A B P h f.
Proof. exact (ex_intro (term254 _144956 _144962 A B P h f) (term255 _144956 _144962 A B P h f) (@lem8226798 _144956 _144962 A B P h f)). Qed.
Lemma lem8226801 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8226802 {_144956 : Type'} (a : _144956) (b : _144956) : (a = b) = (@GEQ _144956 a b).
Proof. exact (@lem8226801 _144956 a b). Qed.
Lemma lem8226803 {_144956 _144962 A B P : Type'} (_109451 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : ((term192 _144956 _144962 P _109451 y x) = (h f x y)) = (term256 _144956 _144962 A B P _109451 h f x y).
Proof. exact (@lem8226802 _144956 (term192 _144956 _144962 P _109451 y x) (h f x y)). Qed.
Lemma lem8226804 {_144956 _144962 A B P : Type'} (_109451 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term257 _144956 _144962 A B P _109451 h f y) = (term258 _144956 _144962 A B P _109451 h f y).
Proof. exact (fun_ext (fun x : P => @lem8226803 _144956 _144962 A B P _109451 h f x y)). Qed.
Lemma lem8226805 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226806 {_144956 _144962 A B P : Type'} (_109451 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term259 _144956 _144962 A B P _109451 h f y) = (term260 _144956 _144962 A B P _109451 h f y).
Proof. exact (MK_COMB (@lem8226805 P) (@lem8226804 _144956 _144962 A B P _109451 h f y)). Qed.
Lemma lem8226807 {_144956 _144962 A B P : Type'} (_109451 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (f : A -> B) : (term261 _144956 _144962 A B P _109451 h f) = (term262 _144956 _144962 A B P _109451 h f).
Proof. exact (fun_ext (fun y : _144962 => @lem8226806 _144956 _144962 A B P _109451 h f y)). Qed.
Lemma lem8226808 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226809 {_144956 _144962 A B P : Type'} (_109451 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (f : A -> B) : (term263 _144956 _144962 A B P _109451 h f) = (term264 _144956 _144962 A B P _109451 h f).
Proof. exact (MK_COMB (@lem8226808 _144962) (@lem8226807 _144956 _144962 A B P _109451 h f)). Qed.
Lemma lem8226810 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term254 _144956 _144962 A B P h f) = (term265 _144956 _144962 A B P h f).
Proof. exact (fun_ext (fun _109451 : type1224 _144956 _144962 P => @lem8226809 _144956 _144962 A B P _109451 h f)). Qed.
Lemma lem8226811 {_144956 _144962 P : Type'} : (@ex ((prod _144962 P) -> _144956)) = (@ex ((prod _144962 P) -> _144956)).
Proof. exact (eq_refl (@ex ((prod _144962 P) -> _144956))). Qed.
Lemma lem8226812 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term253 _144956 _144962 A B P h f) = (term266 _144956 _144962 A B P h f).
Proof. exact (MK_COMB (@lem8226811 _144956 _144962 P) (@lem8226810 _144956 _144962 A B P h f)). Qed.
Lemma lem8226813 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term266 _144956 _144962 A B P h f.
Proof. exact (EQ_MP (@lem8226812 _144956 _144962 A B P h f) (@lem8226799 _144956 _144962 A B P h f)). Qed.
Lemma lem8226815 {_5076 : Type'} (P : _5076 -> Prop) : term164 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8226816 {_144956 _144962 P : Type'} (P' : type331 _144956 _144962 P) : term204 _144956 _144962 P P'.
Proof. exact (@lem8226815 (type1224 _144956 _144962 P) P'). Qed.
Lemma lem8226817 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term267 _144956 _144962 A B P h f.
Proof. exact (@lem8226816 _144956 _144962 P (term265 _144956 _144962 A B P h f)). Qed.
Lemma lem8226818 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term268 _144956 _144962 A B P h f.
Proof. exact (@lem8226817 _144956 _144962 A B P h f (@lem8226813 _144956 _144962 A B P h f)). Qed.
Lemma lem8226819 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term268 _144956 _144962 A B P h f) = (term269 _144956 _144962 A B P h f).
Proof. exact (eq_refl (term268 _144956 _144962 A B P h f)). Qed.
Lemma lem8226820 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : term269 _144956 _144962 A B P h f.
Proof. exact (EQ_MP (@lem8226819 _144956 _144962 A B P h f) (@lem8226818 _144956 _144962 A B P h f)). Qed.
Lemma lem8226821 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : term270 _144956 _144962 A B P h f y.
Proof. exact (@lem8226820 _144956 _144962 A B P h f y). Qed.
Lemma lem8226822 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : (term270 _144956 _144962 A B P h f y) = (term271 _144956 _144962 A B P h f y).
Proof. exact (eq_refl (term270 _144956 _144962 A B P h f y)). Qed.
Lemma lem8226823 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) : term271 _144956 _144962 A B P h f y.
Proof. exact (EQ_MP (@lem8226822 _144956 _144962 A B P h f y) (@lem8226821 _144956 _144962 A B P h f y)). Qed.
Lemma lem8226824 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (y : _144962) (x : P) : term272 _144956 _144962 A B P h f y x.
Proof. exact (@lem8226823 _144956 _144962 A B P h f y x). Qed.
Lemma lem8226825 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term272 _144956 _144962 A B P h f y x) = (term273 _144956 _144962 A B P h f x y).
Proof. exact (eq_refl (term272 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226826 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : term273 _144956 _144962 A B P h f x y.
Proof. exact (EQ_MP (@lem8226825 _144956 _144962 A B P h f x y) (@lem8226824 _144956 _144962 A B P h f y x)). Qed.
Lemma lem8226828 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8226829 {_144956 : Type'} (a : _144956) (b : _144956) : (@GEQ _144956 a b) = (a = b).
Proof. exact (@lem8226828 _144956 a b). Qed.
Lemma lem8226830 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term273 _144956 _144962 A B P h f x y) = ((term237 _144956 _144962 A B P h f y x) = (h f x y)).
Proof. exact (@lem8226829 _144956 (term237 _144956 _144962 A B P h f y x) (h f x y)). Qed.
Lemma lem8226831 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term237 _144956 _144962 A B P h f y x) = (h f x y).
Proof. exact (EQ_MP (@lem8226830 _144956 _144962 A B P h f x y) (@lem8226826 _144956 _144962 A B P h f x y)). Qed.
Lemma lem8226832 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (x : P) (y : _144962) : (term237 _144956 _144962 A B P h f y x) = (h f x y).
Proof. exact (@lem8226831 _144956 _144962 A B P h f x y). Qed.
Lemma lem8226833 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (p2 : P) (p1 : _144962) : (term237 _144956 _144962 A B P h f p1 p2) = (h f p2 p1).
Proof. exact (@lem8226832 _144956 _144962 A B P h f p2 p1). Qed.
Lemma lem8226834 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (p2 : P) (p1 : _144962) : (term236 _144956 _144962 A B P h f p1 p2) = (h f p2 p1).
Proof. exact (TRANS (@lem8226734 _144956 _144962 A B P h f p1 p2) (@lem8226833 _144956 _144962 A B P h f p2 p1)). Qed.
Lemma lem8226835 {_144956 : Type'} : (@eq _144956) = (@eq _144956).
Proof. exact (eq_refl (@eq _144956)). Qed.
Lemma lem8226836 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (p2 : P) (p1 : _144962) : (term274 _144956 _144962 A B P h f p1 p2) = (term249 _144956 _144962 A B P h f p2 p1).
Proof. exact (MK_COMB (@lem8226835 _144956) (@lem8226834 _144956 _144962 A B P h f p2 p1)). Qed.
Lemma lem8226838 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8226839 {_144956 _144962 A B P : Type'} (f : type888 _144956 _144962 A B P) (y : A -> B) : (term229 _144956 _144962 A B P f y) = (f y).
Proof. exact (@lem8226838 (A -> B) (type1224 _144956 _144962 P) f y). Qed.
Lemma lem8226840 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term230 _144956 _144962 A B P h g) = (term231 _144956 _144962 A B P h g).
Proof. exact (@lem8226839 _144956 _144962 A B P (term95 _144956 _144962 A B P h) g). Qed.
Lemma lem8226841 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) : (term231 _144956 _144962 A B P h f) = (term232 _144956 _144962 A B P h f).
Proof. exact (eq_refl (term231 _144956 _144962 A B P h f)). Qed.
Lemma lem8226842 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) : (term233 _144956 _144962 A B P h) = (term95 _144956 _144962 A B P h).
Proof. exact (fun_ext (fun f : A -> B => @lem8226841 _144956 _144962 A B P h f)). Qed.
Lemma lem8226843 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8226844 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term230 _144956 _144962 A B P h g) = (term231 _144956 _144962 A B P h g).
Proof. exact (MK_COMB (@lem8226842 _144956 _144962 A B P h) (@lem8226843 A B g)). Qed.
Lemma lem8226845 {_144956 _144962 P : Type'} : (@eq ((prod _144962 P) -> _144956)) = (@eq ((prod _144962 P) -> _144956)).
Proof. exact (eq_refl (@eq ((prod _144962 P) -> _144956))). Qed.
Lemma lem8226846 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term234 _144956 _144962 A B P h g) = (term235 _144956 _144962 A B P h g).
Proof. exact (MK_COMB (@lem8226845 _144956 _144962 P) (@lem8226844 _144956 _144962 A B P h g)). Qed.
Lemma lem8226847 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term231 _144956 _144962 A B P h g) = (term232 _144956 _144962 A B P h g).
Proof. exact (eq_refl (term231 _144956 _144962 A B P h g)). Qed.
Lemma lem8226848 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : ((term230 _144956 _144962 A B P h g) = (term231 _144956 _144962 A B P h g)) = ((term231 _144956 _144962 A B P h g) = (term232 _144956 _144962 A B P h g)).
Proof. exact (MK_COMB (@lem8226846 _144956 _144962 A B P h g) (@lem8226847 _144956 _144962 A B P h g)). Qed.
Lemma lem8226849 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term231 _144956 _144962 A B P h g) = (term232 _144956 _144962 A B P h g).
Proof. exact (EQ_MP (@lem8226848 _144956 _144962 A B P h g) (@lem8226840 _144956 _144962 A B P h g)). Qed.
Lemma lem8226862 {_144962 P : Type'} (p1 : _144962) (p2 : P) : (@pair _144962 P p1 p2) = (@pair _144962 P p1 p2).
Proof. exact (eq_refl (@pair _144962 P p1 p2)). Qed.
Lemma lem8226863 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) (p2 : P) : (term236 _144956 _144962 A B P h g p1 p2) = (term237 _144956 _144962 A B P h g p1 p2).
Proof. exact (MK_COMB (@lem8226849 _144956 _144962 A B P h g) (@lem8226862 _144962 P p1 p2)). Qed.
Lemma lem8226864 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a0 = (term126 _144962 P a0 a1).
Proof. exact (@lem51128 _144962 P a0 a1). Qed.
Lemma lem8226865 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (@lem8226864 _144962 P y x). Qed.
Lemma lem8226866 {_144962 P : Type'} (a0 : _144962) (a1 : P) : a1 = (term127 _144962 P a0 a1).
Proof. exact (@lem51159 _144962 P a0 a1). Qed.
Lemma lem8226867 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (@lem8226866 _144962 P y x). Qed.
Lemma lem8226868 {_144962 : Type'} (y : _144962) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8226869 {_144962 : Type'} : (term128 _144962) = (term128 _144962).
Proof. exact (eq_refl (term128 _144962)). Qed.
Lemma lem8226870 {_144962 P : Type'} (y : _144962) (x : P) : (term129 _144962 y) = (term130 _144962 P y x).
Proof. exact (MK_COMB (@lem8226869 _144962) (@lem8226865 _144962 P y x)). Qed.
Lemma lem8226871 {_144962 P : Type'} (y : _144962) (x : P) : (term130 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term130 _144962 P y x)). Qed.
Lemma lem8226872 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (term131 _144962 y).
Proof. exact (eq_refl (term131 _144962 y)). Qed.
Lemma lem8226873 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = ((term129 _144962 y) = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226872 _144962 y) (@lem8226871 _144962 P y x)). Qed.
Lemma lem8226874 {_144962 : Type'} (y : _144962) : (term129 _144962 y) = y.
Proof. exact (eq_refl (term129 _144962 y)). Qed.
Lemma lem8226875 {_144962 : Type'} : (@eq _144962) = (@eq _144962).
Proof. exact (eq_refl (@eq _144962)). Qed.
Lemma lem8226876 {_144962 : Type'} (y : _144962) : (term131 _144962 y) = (@eq _144962 y).
Proof. exact (MK_COMB (@lem8226875 _144962) (@lem8226874 _144962 y)). Qed.
Lemma lem8226877 {_144962 P : Type'} (y : _144962) (x : P) : (term126 _144962 P y x) = (term126 _144962 P y x).
Proof. exact (eq_refl (term126 _144962 P y x)). Qed.
Lemma lem8226878 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term126 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226876 _144962 y) (@lem8226877 _144962 P y x)). Qed.
Lemma lem8226879 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 _144962 y) = (term130 _144962 P y x)) = (y = (term126 _144962 P y x)).
Proof. exact (TRANS (@lem8226873 _144962 P y x) (@lem8226878 _144962 P y x)). Qed.
Lemma lem8226880 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226879 _144962 P y x) (@lem8226870 _144962 P y x)). Qed.
Lemma lem8226881 {_144962 : Type'} (y : _144962) : (@eq _144962 y) = (@eq _144962 y).
Proof. exact (eq_refl (@eq _144962 y)). Qed.
Lemma lem8226882 {_144962 P : Type'} (y : _144962) (x : P) : (y = y) = (y = (term126 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226881 _144962 y) (@lem8226880 _144962 P y x)). Qed.
Lemma lem8226883 {_144962 P : Type'} (y : _144962) (x : P) : y = (term126 _144962 P y x).
Proof. exact (EQ_MP (@lem8226882 _144962 P y x) (@lem8226868 _144962 y)). Qed.
Lemma lem8226884 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8226885 {P : Type'} : (term128 P) = (term128 P).
Proof. exact (eq_refl (term128 P)). Qed.
Lemma lem8226886 {_144962 P : Type'} (y : _144962) (x : P) : (term129 P x) = (term132 _144962 P y x).
Proof. exact (MK_COMB (@lem8226885 P) (@lem8226867 _144962 P y x)). Qed.
Lemma lem8226887 {_144962 P : Type'} (y : _144962) (x : P) : (term132 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term132 _144962 P y x)). Qed.
Lemma lem8226888 {P : Type'} (x : P) : (term131 P x) = (term131 P x).
Proof. exact (eq_refl (term131 P x)). Qed.
Lemma lem8226889 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = ((term129 P x) = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226888 P x) (@lem8226887 _144962 P y x)). Qed.
Lemma lem8226890 {P : Type'} (x : P) : (term129 P x) = x.
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem8226891 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8226892 {P : Type'} (x : P) : (term131 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8226891 P) (@lem8226890 P x)). Qed.
Lemma lem8226893 {_144962 P : Type'} (y : _144962) (x : P) : (term127 _144962 P y x) = (term127 _144962 P y x).
Proof. exact (eq_refl (term127 _144962 P y x)). Qed.
Lemma lem8226894 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term127 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226892 P x) (@lem8226893 _144962 P y x)). Qed.
Lemma lem8226895 {_144962 P : Type'} (y : _144962) (x : P) : ((term129 P x) = (term132 _144962 P y x)) = (x = (term127 _144962 P y x)).
Proof. exact (TRANS (@lem8226889 _144962 P y x) (@lem8226894 _144962 P y x)). Qed.
Lemma lem8226896 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226895 _144962 P y x) (@lem8226886 _144962 P y x)). Qed.
Lemma lem8226897 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8226898 {_144962 P : Type'} (y : _144962) (x : P) : (x = x) = (x = (term127 _144962 P y x)).
Proof. exact (MK_COMB (@lem8226897 P x) (@lem8226896 _144962 P y x)). Qed.
Lemma lem8226899 {_144962 P : Type'} (y : _144962) (x : P) : x = (term127 _144962 P y x).
Proof. exact (EQ_MP (@lem8226898 _144962 P y x) (@lem8226884 P x)). Qed.
Lemma lem8226900 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term238 _144956 _144962 A B P h g) = (term238 _144956 _144962 A B P h g).
Proof. exact (eq_refl (term238 _144956 _144962 A B P h g)). Qed.
Lemma lem8226901 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term239 _144956 _144962 A B P h g y) = (term240 _144956 _144962 A B P h g y x).
Proof. exact (MK_COMB (@lem8226900 _144956 _144962 A B P h g) (@lem8226883 _144962 P y x)). Qed.
Lemma lem8226902 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term240 _144956 _144962 A B P h g y x) = (term241 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term240 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226903 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term242 _144956 _144962 A B P h g y) = (term242 _144956 _144962 A B P h g y).
Proof. exact (eq_refl (term242 _144956 _144962 A B P h g y)). Qed.
Lemma lem8226904 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h g y) = (term240 _144956 _144962 A B P h g y x)) = ((term239 _144956 _144962 A B P h g y) = (term241 _144956 _144962 A B P h g y x)).
Proof. exact (MK_COMB (@lem8226903 _144956 _144962 A B P h g y) (@lem8226902 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226905 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term239 _144956 _144962 A B P h g y) = (term243 _144956 _144962 A B P h g y).
Proof. exact (eq_refl (term239 _144956 _144962 A B P h g y)). Qed.
Lemma lem8226906 {_144956 P : Type'} : (@eq (P -> _144956)) = (@eq (P -> _144956)).
Proof. exact (eq_refl (@eq (P -> _144956))). Qed.
Lemma lem8226907 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term242 _144956 _144962 A B P h g y) = (term244 _144956 _144962 A B P h g y).
Proof. exact (MK_COMB (@lem8226906 _144956 P) (@lem8226905 _144956 _144962 A B P h g y)). Qed.
Lemma lem8226908 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term241 _144956 _144962 A B P h g y x) = (term241 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term241 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226909 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h g y) = (term241 _144956 _144962 A B P h g y x)) = ((term243 _144956 _144962 A B P h g y) = (term241 _144956 _144962 A B P h g y x)).
Proof. exact (MK_COMB (@lem8226907 _144956 _144962 A B P h g y) (@lem8226908 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226910 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term239 _144956 _144962 A B P h g y) = (term240 _144956 _144962 A B P h g y x)) = ((term243 _144956 _144962 A B P h g y) = (term241 _144956 _144962 A B P h g y x)).
Proof. exact (TRANS (@lem8226904 _144956 _144962 A B P h g y x) (@lem8226909 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226911 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term243 _144956 _144962 A B P h g y) = (term241 _144956 _144962 A B P h g y x).
Proof. exact (EQ_MP (@lem8226910 _144956 _144962 A B P h g y x) (@lem8226901 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226912 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term245 _144956 _144962 A B P h g y x) = (term246 _144956 _144962 A B P h g y x).
Proof. exact (MK_COMB (@lem8226911 _144956 _144962 A B P h g y x) (@lem8226899 _144962 P y x)). Qed.
Lemma lem8226913 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term246 _144956 _144962 A B P h g y x) = (term247 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term246 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226914 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term248 _144956 _144962 A B P h g y x) = (term248 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term248 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226915 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h g y x) = (term246 _144956 _144962 A B P h g y x)) = ((term245 _144956 _144962 A B P h g y x) = (term247 _144956 _144962 A B P h g y x)).
Proof. exact (MK_COMB (@lem8226914 _144956 _144962 A B P h g y x) (@lem8226913 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226916 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term245 _144956 _144962 A B P h g y x) = (h g x y).
Proof. exact (eq_refl (term245 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226917 {_144956 : Type'} : (@eq _144956) = (@eq _144956).
Proof. exact (eq_refl (@eq _144956)). Qed.
Lemma lem8226918 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term248 _144956 _144962 A B P h g y x) = (term249 _144956 _144962 A B P h g x y).
Proof. exact (MK_COMB (@lem8226917 _144956) (@lem8226916 _144956 _144962 A B P h g x y)). Qed.
Lemma lem8226919 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term247 _144956 _144962 A B P h g y x) = (term247 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term247 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226920 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h g y x) = (term247 _144956 _144962 A B P h g y x)) = ((h g x y) = (term247 _144956 _144962 A B P h g y x)).
Proof. exact (MK_COMB (@lem8226918 _144956 _144962 A B P h g x y) (@lem8226919 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226921 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : ((term245 _144956 _144962 A B P h g y x) = (term246 _144956 _144962 A B P h g y x)) = ((h g x y) = (term247 _144956 _144962 A B P h g y x)).
Proof. exact (TRANS (@lem8226915 _144956 _144962 A B P h g y x) (@lem8226920 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226922 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (h g x y) = (term247 _144956 _144962 A B P h g y x).
Proof. exact (EQ_MP (@lem8226921 _144956 _144962 A B P h g y x) (@lem8226912 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226923 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term247 _144956 _144962 A B P h g y x) = (h g x y).
Proof. exact (SYM (@lem8226922 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226924 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : (term250 _144956 _144962 A B P h g y x) = (term247 _144956 _144962 A B P h g y x).
Proof. exact (eq_refl (term250 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226925 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term250 _144956 _144962 A B P h g y x) = (h g x y).
Proof. exact (TRANS (@lem8226924 _144956 _144962 A B P h g y x) (@lem8226923 _144956 _144962 A B P h g x y)). Qed.
Lemma lem8226926 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : term251 _144956 _144962 A B P h g y.
Proof. exact (fun x : P => @lem8226925 _144956 _144962 A B P h g x y). Qed.
Lemma lem8226927 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term252 _144956 _144962 A B P h g.
Proof. exact (fun y : _144962 => @lem8226926 _144956 _144962 A B P h g y). Qed.
Lemma lem8226928 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term253 _144956 _144962 A B P h g.
Proof. exact (ex_intro (term254 _144956 _144962 A B P h g) (term255 _144956 _144962 A B P h g) (@lem8226927 _144956 _144962 A B P h g)). Qed.
Lemma lem8226930 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8226931 {_144956 : Type'} (a : _144956) (b : _144956) : (a = b) = (@GEQ _144956 a b).
Proof. exact (@lem8226930 _144956 a b). Qed.
Lemma lem8226932 {_144956 _144962 A B P : Type'} (_109463 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : ((term192 _144956 _144962 P _109463 y x) = (h g x y)) = (term256 _144956 _144962 A B P _109463 h g x y).
Proof. exact (@lem8226931 _144956 (term192 _144956 _144962 P _109463 y x) (h g x y)). Qed.
Lemma lem8226933 {_144956 _144962 A B P : Type'} (_109463 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term257 _144956 _144962 A B P _109463 h g y) = (term258 _144956 _144962 A B P _109463 h g y).
Proof. exact (fun_ext (fun x : P => @lem8226932 _144956 _144962 A B P _109463 h g x y)). Qed.
Lemma lem8226934 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226935 {_144956 _144962 A B P : Type'} (_109463 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term259 _144956 _144962 A B P _109463 h g y) = (term260 _144956 _144962 A B P _109463 h g y).
Proof. exact (MK_COMB (@lem8226934 P) (@lem8226933 _144956 _144962 A B P _109463 h g y)). Qed.
Lemma lem8226936 {_144956 _144962 A B P : Type'} (_109463 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term261 _144956 _144962 A B P _109463 h g) = (term262 _144956 _144962 A B P _109463 h g).
Proof. exact (fun_ext (fun y : _144962 => @lem8226935 _144956 _144962 A B P _109463 h g y)). Qed.
Lemma lem8226937 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226938 {_144956 _144962 A B P : Type'} (_109463 : type1224 _144956 _144962 P) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term263 _144956 _144962 A B P _109463 h g) = (term264 _144956 _144962 A B P _109463 h g).
Proof. exact (MK_COMB (@lem8226937 _144962) (@lem8226936 _144956 _144962 A B P _109463 h g)). Qed.
Lemma lem8226939 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term254 _144956 _144962 A B P h g) = (term265 _144956 _144962 A B P h g).
Proof. exact (fun_ext (fun _109463 : type1224 _144956 _144962 P => @lem8226938 _144956 _144962 A B P _109463 h g)). Qed.
Lemma lem8226940 {_144956 _144962 P : Type'} : (@ex ((prod _144962 P) -> _144956)) = (@ex ((prod _144962 P) -> _144956)).
Proof. exact (eq_refl (@ex ((prod _144962 P) -> _144956))). Qed.
Lemma lem8226941 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term253 _144956 _144962 A B P h g) = (term266 _144956 _144962 A B P h g).
Proof. exact (MK_COMB (@lem8226940 _144956 _144962 P) (@lem8226939 _144956 _144962 A B P h g)). Qed.
Lemma lem8226942 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term266 _144956 _144962 A B P h g.
Proof. exact (EQ_MP (@lem8226941 _144956 _144962 A B P h g) (@lem8226928 _144956 _144962 A B P h g)). Qed.
Lemma lem8226944 {_5076 : Type'} (P : _5076 -> Prop) : term164 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8226945 {_144956 _144962 P : Type'} (P' : type331 _144956 _144962 P) : term204 _144956 _144962 P P'.
Proof. exact (@lem8226944 (type1224 _144956 _144962 P) P'). Qed.
Lemma lem8226946 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term267 _144956 _144962 A B P h g.
Proof. exact (@lem8226945 _144956 _144962 P (term265 _144956 _144962 A B P h g)). Qed.
Lemma lem8226947 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term268 _144956 _144962 A B P h g.
Proof. exact (@lem8226946 _144956 _144962 A B P h g (@lem8226942 _144956 _144962 A B P h g)). Qed.
Lemma lem8226948 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : (term268 _144956 _144962 A B P h g) = (term269 _144956 _144962 A B P h g).
Proof. exact (eq_refl (term268 _144956 _144962 A B P h g)). Qed.
Lemma lem8226949 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) : term269 _144956 _144962 A B P h g.
Proof. exact (EQ_MP (@lem8226948 _144956 _144962 A B P h g) (@lem8226947 _144956 _144962 A B P h g)). Qed.
Lemma lem8226950 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : term270 _144956 _144962 A B P h g y.
Proof. exact (@lem8226949 _144956 _144962 A B P h g y). Qed.
Lemma lem8226951 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : (term270 _144956 _144962 A B P h g y) = (term271 _144956 _144962 A B P h g y).
Proof. exact (eq_refl (term270 _144956 _144962 A B P h g y)). Qed.
Lemma lem8226952 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) : term271 _144956 _144962 A B P h g y.
Proof. exact (EQ_MP (@lem8226951 _144956 _144962 A B P h g y) (@lem8226950 _144956 _144962 A B P h g y)). Qed.
Lemma lem8226953 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (y : _144962) (x : P) : term272 _144956 _144962 A B P h g y x.
Proof. exact (@lem8226952 _144956 _144962 A B P h g y x). Qed.
Lemma lem8226954 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term272 _144956 _144962 A B P h g y x) = (term273 _144956 _144962 A B P h g x y).
Proof. exact (eq_refl (term272 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226955 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : term273 _144956 _144962 A B P h g x y.
Proof. exact (EQ_MP (@lem8226954 _144956 _144962 A B P h g x y) (@lem8226953 _144956 _144962 A B P h g y x)). Qed.
Lemma lem8226957 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8226958 {_144956 : Type'} (a : _144956) (b : _144956) : (@GEQ _144956 a b) = (a = b).
Proof. exact (@lem8226957 _144956 a b). Qed.
Lemma lem8226959 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term273 _144956 _144962 A B P h g x y) = ((term237 _144956 _144962 A B P h g y x) = (h g x y)).
Proof. exact (@lem8226958 _144956 (term237 _144956 _144962 A B P h g y x) (h g x y)). Qed.
Lemma lem8226960 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term237 _144956 _144962 A B P h g y x) = (h g x y).
Proof. exact (EQ_MP (@lem8226959 _144956 _144962 A B P h g x y) (@lem8226955 _144956 _144962 A B P h g x y)). Qed.
Lemma lem8226961 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (x : P) (y : _144962) : (term237 _144956 _144962 A B P h g y x) = (h g x y).
Proof. exact (@lem8226960 _144956 _144962 A B P h g x y). Qed.
Lemma lem8226962 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term237 _144956 _144962 A B P h g p1 p2) = (h g p2 p1).
Proof. exact (@lem8226961 _144956 _144962 A B P h g p2 p1). Qed.
Lemma lem8226963 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term236 _144956 _144962 A B P h g p1 p2) = (h g p2 p1).
Proof. exact (TRANS (@lem8226863 _144956 _144962 A B P h g p1 p2) (@lem8226962 _144956 _144962 A B P h g p2 p1)). Qed.
Lemma lem8226964 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((term236 _144956 _144962 A B P h f p1 p2) = (term236 _144956 _144962 A B P h g p1 p2)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (MK_COMB (@lem8226836 _144956 _144962 A B P h f p2 p1) (@lem8226963 _144956 _144962 A B P h g p2 p1)). Qed.
Lemma lem8226967 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term108 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8226705 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8226964 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8226970 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term110 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term276 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8226967 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8226971 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8226972 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term112 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8226971 P) (@lem8226970 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8226979 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term114 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term278 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8226972 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8226980 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8226981 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term115 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term279 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8226980 _144962) (@lem8226979 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226988 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term104 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term279 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (TRANS (@lem8226287 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8226981 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226989 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term280 _144947 _144956 _144962 A B P p l lt2 s f h) = (term281 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8226988 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8226990 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8226991 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term282 _144947 _144956 _144962 A B P p l lt2 s f h) = (term283 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8226990 A B) (@lem8226989 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8226998 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term284 _144947 _144956 _144962 A B P p l lt2 s h) = (term285 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun f : A -> B => @lem8226991 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8226999 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227000 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term92 _144947 _144956 _144962 A B P p l lt2 s h) = (term286 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8226999 A B) (@lem8226998 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227007 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term91 _144947 _144956 _144962 A B P lt2 p l s h) = (term286 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (TRANS (@lem8226252 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8227000 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227008 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term287 _144947 _144956 _144962 A B P lt2 p l s h) = (term288 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8226248 _144947 _144962 A B P p lt2 s l) (@lem8227007 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227012 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term289 _144947 _144956 _144962 A B P lt2 p l s h) = (term290 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8227011) (@lem8227008 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227014 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term86 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8226171 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8226170 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8227015 {_144947 _144956 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (t : type815 _144956 A B P) : (@admissible _144947 B A (list _144956) P lt2 p s t) = (term87 _144947 _144956 A B P p lt2 s t).
Proof. exact (@lem8227014 _144947 B A (list _144956) P p lt2 s t). Qed.
Lemma lem8227016 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term291 _144947 _144956 _144962 A B P lt2 p s h l) = (term292 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (@lem8227015 _144947 _144956 A B P p lt2 s (term293 _144956 _144962 A B P h l)). Qed.
Lemma lem8227054 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8227055 {_144956 A B P : Type'} (f : type815 _144956 A B P) (y : A -> B) : (term294 _144956 A B P f y) = (f y).
Proof. exact (@lem8227054 (A -> B) (type1477 _144956 P) f y). Qed.
Lemma lem8227056 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term295 _144956 _144962 A B P h l f) = (term296 _144956 _144962 A B P h l f).
Proof. exact (@lem8227055 _144956 A B P (term293 _144956 _144962 A B P h l) f). Qed.
Lemma lem8227057 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term296 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f).
Proof. exact (eq_refl (term296 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227058 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term298 _144956 _144962 A B P h l) = (term293 _144956 _144962 A B P h l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227057 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227059 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8227060 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term295 _144956 _144962 A B P h l f) = (term296 _144956 _144962 A B P h l f).
Proof. exact (MK_COMB (@lem8227058 _144956 _144962 A B P h l) (@lem8227059 A B f)). Qed.
Lemma lem8227061 {_144956 P : Type'} : (@eq (P -> list _144956)) = (@eq (P -> list _144956)).
Proof. exact (eq_refl (@eq (P -> list _144956))). Qed.
Lemma lem8227062 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term299 _144956 _144962 A B P h l f) = (term300 _144956 _144962 A B P h l f).
Proof. exact (MK_COMB (@lem8227061 _144956 P) (@lem8227060 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227063 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term296 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f).
Proof. exact (eq_refl (term296 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227064 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : ((term295 _144956 _144962 A B P h l f) = (term296 _144956 _144962 A B P h l f)) = ((term296 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f)).
Proof. exact (MK_COMB (@lem8227062 _144956 _144962 A B P h l f) (@lem8227063 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227065 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term296 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f).
Proof. exact (EQ_MP (@lem8227064 _144956 _144962 A B P h l f) (@lem8227056 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227066 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8227067 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term301 _144956 _144962 A B P h l f a) = (term302 _144956 _144962 A B P h l f a).
Proof. exact (MK_COMB (@lem8227065 _144956 _144962 A B P h l f) (@lem8227066 P a)). Qed.
Lemma lem8227069 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8227070 {_144956 P : Type'} (f : type1477 _144956 P) (y : P) : (term303 _144956 P f y) = (f y).
Proof. exact (@lem8227069 P (list _144956) f y). Qed.
Lemma lem8227071 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term304 _144956 _144962 A B P h l f a) = (term302 _144956 _144962 A B P h l f a).
Proof. exact (@lem8227070 _144956 P (term297 _144956 _144962 A B P h l f) a). Qed.
Lemma lem8227072 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (x : P) : (term302 _144956 _144962 A B P h l f x) = (term305 _144956 _144962 A B P h l f x).
Proof. exact (eq_refl (term302 _144956 _144962 A B P h l f x)). Qed.
Lemma lem8227073 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term306 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f).
Proof. exact (fun_ext (fun x : P => @lem8227072 _144956 _144962 A B P h l f x)). Qed.
Lemma lem8227074 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8227075 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term304 _144956 _144962 A B P h l f a) = (term302 _144956 _144962 A B P h l f a).
Proof. exact (MK_COMB (@lem8227073 _144956 _144962 A B P h l f) (@lem8227074 P a)). Qed.
Lemma lem8227076 {_144956 : Type'} : (@eq (list _144956)) = (@eq (list _144956)).
Proof. exact (eq_refl (@eq (list _144956))). Qed.
Lemma lem8227077 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term307 _144956 _144962 A B P h l f a) = (term308 _144956 _144962 A B P h l f a).
Proof. exact (MK_COMB (@lem8227076 _144956) (@lem8227075 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227078 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term302 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l f a).
Proof. exact (eq_refl (term302 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227079 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : ((term304 _144956 _144962 A B P h l f a) = (term302 _144956 _144962 A B P h l f a)) = ((term302 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l f a)).
Proof. exact (MK_COMB (@lem8227077 _144956 _144962 A B P h l f a) (@lem8227078 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227080 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term302 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l f a).
Proof. exact (EQ_MP (@lem8227079 _144956 _144962 A B P h l f a) (@lem8227071 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227081 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term301 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l f a).
Proof. exact (TRANS (@lem8227067 _144956 _144962 A B P h l f a) (@lem8227080 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227082 {_144956 : Type'} : (@eq (list _144956)) = (@eq (list _144956)).
Proof. exact (eq_refl (@eq (list _144956))). Qed.
Lemma lem8227083 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term309 _144956 _144962 A B P h l f a) = (term310 _144956 _144962 A B P h l f a).
Proof. exact (MK_COMB (@lem8227082 _144956) (@lem8227081 _144956 _144962 A B P h l f a)). Qed.
Lemma lem8227085 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8227086 {_144956 A B P : Type'} (f : type815 _144956 A B P) (y : A -> B) : (term294 _144956 A B P f y) = (f y).
Proof. exact (@lem8227085 (A -> B) (type1477 _144956 P) f y). Qed.
Lemma lem8227087 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term295 _144956 _144962 A B P h l g) = (term296 _144956 _144962 A B P h l g).
Proof. exact (@lem8227086 _144956 A B P (term293 _144956 _144962 A B P h l) g). Qed.
Lemma lem8227088 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (f : A -> B) : (term296 _144956 _144962 A B P h l f) = (term297 _144956 _144962 A B P h l f).
Proof. exact (eq_refl (term296 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227089 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term298 _144956 _144962 A B P h l) = (term293 _144956 _144962 A B P h l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227088 _144956 _144962 A B P h l f)). Qed.
Lemma lem8227090 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8227091 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term295 _144956 _144962 A B P h l g) = (term296 _144956 _144962 A B P h l g).
Proof. exact (MK_COMB (@lem8227089 _144956 _144962 A B P h l) (@lem8227090 A B g)). Qed.
Lemma lem8227092 {_144956 P : Type'} : (@eq (P -> list _144956)) = (@eq (P -> list _144956)).
Proof. exact (eq_refl (@eq (P -> list _144956))). Qed.
Lemma lem8227093 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term299 _144956 _144962 A B P h l g) = (term300 _144956 _144962 A B P h l g).
Proof. exact (MK_COMB (@lem8227092 _144956 P) (@lem8227091 _144956 _144962 A B P h l g)). Qed.
Lemma lem8227094 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term296 _144956 _144962 A B P h l g) = (term297 _144956 _144962 A B P h l g).
Proof. exact (eq_refl (term296 _144956 _144962 A B P h l g)). Qed.
Lemma lem8227095 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : ((term295 _144956 _144962 A B P h l g) = (term296 _144956 _144962 A B P h l g)) = ((term296 _144956 _144962 A B P h l g) = (term297 _144956 _144962 A B P h l g)).
Proof. exact (MK_COMB (@lem8227093 _144956 _144962 A B P h l g) (@lem8227094 _144956 _144962 A B P h l g)). Qed.
Lemma lem8227096 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term296 _144956 _144962 A B P h l g) = (term297 _144956 _144962 A B P h l g).
Proof. exact (EQ_MP (@lem8227095 _144956 _144962 A B P h l g) (@lem8227087 _144956 _144962 A B P h l g)). Qed.
Lemma lem8227097 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8227098 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term301 _144956 _144962 A B P h l g a) = (term302 _144956 _144962 A B P h l g a).
Proof. exact (MK_COMB (@lem8227096 _144956 _144962 A B P h l g) (@lem8227097 P a)). Qed.
Lemma lem8227100 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8227101 {_144956 P : Type'} (f : type1477 _144956 P) (y : P) : (term303 _144956 P f y) = (f y).
Proof. exact (@lem8227100 P (list _144956) f y). Qed.
Lemma lem8227102 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term304 _144956 _144962 A B P h l g a) = (term302 _144956 _144962 A B P h l g a).
Proof. exact (@lem8227101 _144956 P (term297 _144956 _144962 A B P h l g) a). Qed.
Lemma lem8227103 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (x : P) : (term302 _144956 _144962 A B P h l g x) = (term305 _144956 _144962 A B P h l g x).
Proof. exact (eq_refl (term302 _144956 _144962 A B P h l g x)). Qed.
Lemma lem8227104 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term306 _144956 _144962 A B P h l g) = (term297 _144956 _144962 A B P h l g).
Proof. exact (fun_ext (fun x : P => @lem8227103 _144956 _144962 A B P h l g x)). Qed.
Lemma lem8227105 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8227106 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term304 _144956 _144962 A B P h l g a) = (term302 _144956 _144962 A B P h l g a).
Proof. exact (MK_COMB (@lem8227104 _144956 _144962 A B P h l g) (@lem8227105 P a)). Qed.
Lemma lem8227107 {_144956 : Type'} : (@eq (list _144956)) = (@eq (list _144956)).
Proof. exact (eq_refl (@eq (list _144956))). Qed.
Lemma lem8227108 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term307 _144956 _144962 A B P h l g a) = (term308 _144956 _144962 A B P h l g a).
Proof. exact (MK_COMB (@lem8227107 _144956) (@lem8227106 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227109 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term302 _144956 _144962 A B P h l g a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (eq_refl (term302 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227110 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term304 _144956 _144962 A B P h l g a) = (term302 _144956 _144962 A B P h l g a)) = ((term302 _144956 _144962 A B P h l g a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (MK_COMB (@lem8227108 _144956 _144962 A B P h l g a) (@lem8227109 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227111 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term302 _144956 _144962 A B P h l g a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8227110 _144956 _144962 A B P h l g a) (@lem8227102 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227112 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term301 _144956 _144962 A B P h l g a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (TRANS (@lem8227098 _144956 _144962 A B P h l g a) (@lem8227111 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227113 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term301 _144956 _144962 A B P h l f a) = (term301 _144956 _144962 A B P h l g a)) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (MK_COMB (@lem8227083 _144956 _144962 A B P h l f a) (@lem8227112 _144956 _144962 A B P h l g a)). Qed.
Lemma lem8227116 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term311 _144947 A B P p lt2 s a f g) = (term311 _144947 A B P p lt2 s a f g).
Proof. exact (eq_refl (term311 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227117 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term312 _144947 _144956 _144962 A B P p lt2 s f h l g a) = (term313 _144947 _144956 _144962 A B P p lt2 s f h l g a).
Proof. exact (MK_COMB (@lem8227116 _144947 A B P p lt2 s a f g) (@lem8227113 _144956 _144962 A B P f h l g a)). Qed.
Lemma lem8227120 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term314 _144947 _144956 _144962 A B P p lt2 s f h l g) = (term315 _144947 _144956 _144962 A B P p lt2 s f h l g).
Proof. exact (fun_ext (fun a : P => @lem8227117 _144947 _144956 _144962 A B P p lt2 s f h l g a)). Qed.
Lemma lem8227121 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227122 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) : (term316 _144947 _144956 _144962 A B P p lt2 s f h l g) = (term317 _144947 _144956 _144962 A B P p lt2 s f h l g).
Proof. exact (MK_COMB (@lem8227121 P) (@lem8227120 _144947 _144956 _144962 A B P p lt2 s f h l g)). Qed.
Lemma lem8227129 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term318 _144947 _144956 _144962 A B P p lt2 s f h l) = (term319 _144947 _144956 _144962 A B P p lt2 s f h l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227122 _144947 _144956 _144962 A B P p lt2 s f h l g)). Qed.
Lemma lem8227130 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227131 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term320 _144947 _144956 _144962 A B P p lt2 s f h l) = (term321 _144947 _144956 _144962 A B P p lt2 s f h l).
Proof. exact (MK_COMB (@lem8227130 A B) (@lem8227129 _144947 _144956 _144962 A B P p lt2 s f h l)). Qed.
Lemma lem8227138 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term322 _144947 _144956 _144962 A B P p lt2 s h l) = (term323 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227131 _144947 _144956 _144962 A B P p lt2 s f h l)). Qed.
Lemma lem8227139 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227140 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term292 _144947 _144956 _144962 A B P p lt2 s h l) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (MK_COMB (@lem8227139 A B) (@lem8227138 _144947 _144956 _144962 A B P p lt2 s h l)). Qed.
Lemma lem8227147 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term291 _144947 _144956 _144962 A B P lt2 p s h l) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (TRANS (@lem8227016 _144947 _144956 _144962 A B P p lt2 s h l) (@lem8227140 _144947 _144956 _144962 A B P p lt2 s h l)). Qed.
Lemma lem8227148 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : (term325 _144947 _144956 _144962 A B P lt2 p s h l) = (term326 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (MK_COMB (@lem8227012 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8227147 _144947 _144956 _144962 A B P p lt2 s h l)). Qed.
Lemma lem8227151 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term327 _144947 _144956 _144962 A B P lt2 p s h) = (term328 _144947 _144956 _144962 A B P p lt2 s h).
Proof. exact (fun_ext (fun l : type815 _144962 A B P => @lem8227148 _144947 _144956 _144962 A B P p lt2 s h l)). Qed.
Lemma lem8227152 {_144962 A B P : Type'} : (@all ((A -> B) -> P -> list _144962)) = (@all ((A -> B) -> P -> list _144962)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> list _144962))). Qed.
Lemma lem8227153 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term329 _144947 _144956 _144962 A B P lt2 p s h) = (term330 _144947 _144956 _144962 A B P p lt2 s h).
Proof. exact (MK_COMB (@lem8227152 _144962 A B P) (@lem8227151 _144947 _144956 _144962 A B P p lt2 s h)). Qed.
Lemma lem8227160 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) : (term331 _144947 _144956 _144962 A B P lt2 p s) = (term332 _144947 _144956 _144962 A B P p lt2 s).
Proof. exact (fun_ext (fun h : type889 _144956 _144962 A B P => @lem8227153 _144947 _144956 _144962 A B P p lt2 s h)). Qed.
Lemma lem8227161 {_144956 _144962 A B P : Type'} : (@all ((A -> B) -> P -> _144962 -> _144956)) = (@all ((A -> B) -> P -> _144962 -> _144956)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> _144962 -> _144956))). Qed.
Lemma lem8227162 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) : (term333 _144947 _144956 _144962 A B P lt2 p s) = (term334 _144947 _144956 _144962 A B P p lt2 s).
Proof. exact (MK_COMB (@lem8227161 _144956 _144962 A B P) (@lem8227160 _144947 _144956 _144962 A B P p lt2 s)). Qed.
Lemma lem8227169 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) : (term335 _144947 _144956 _144962 A B P lt2 p) = (term336 _144947 _144956 _144962 A B P p lt2).
Proof. exact (fun_ext (fun s : P -> _144947 => @lem8227162 _144947 _144956 _144962 A B P p lt2 s)). Qed.
Lemma lem8227170 {_144947 P : Type'} : (@all (P -> _144947)) = (@all (P -> _144947)).
Proof. exact (eq_refl (@all (P -> _144947))). Qed.
Lemma lem8227171 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) : (term337 _144947 _144956 _144962 A B P lt2 p) = (term338 _144947 _144956 _144962 A B P p lt2).
Proof. exact (MK_COMB (@lem8227170 _144947 P) (@lem8227169 _144947 _144956 _144962 A B P p lt2)). Qed.
Lemma lem8227178 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) : (term339 _144947 _144956 _144962 A B P lt2) = (term340 _144947 _144956 _144962 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8227171 _144947 _144956 _144962 A B P p lt2)). Qed.
Lemma lem8227179 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8227180 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) : (term341 _144947 _144956 _144962 A B P lt2) = (term342 _144947 _144956 _144962 A B P lt2).
Proof. exact (MK_COMB (@lem8227179 A B P) (@lem8227178 _144947 _144956 _144962 A B P lt2)). Qed.
Lemma lem8227187 {_144947 _144956 _144962 A B P : Type'} : (term343 _144947 _144956 _144962 A B P) = (term344 _144947 _144956 _144962 A B P).
Proof. exact (fun_ext (fun lt2 : type1470 _144947 A => @lem8227180 _144947 _144956 _144962 A B P lt2)). Qed.
Lemma lem8227188 {_144947 A : Type'} : (@all (A -> _144947 -> Prop)) = (@all (A -> _144947 -> Prop)).
Proof. exact (eq_refl (@all (A -> _144947 -> Prop))). Qed.
Lemma lem8227189 {_144947 _144956 _144962 A B P : Type'} : (term345 _144947 _144956 _144962 A B P) = (term346 _144947 _144956 _144962 A B P).
Proof. exact (MK_COMB (@lem8227188 _144947 A) (@lem8227187 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227196 {_144947 _144956 _144962 A B P : Type'} : (term346 _144947 _144956 _144962 A B P) = (term345 _144947 _144956 _144962 A B P).
Proof. exact (SYM (@lem8227189 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227197 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : term288 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8227198 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term286 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8227199 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term87 _144947 _144962 A B P p lt2 s l.
Proof. exact (h1). Qed.
Lemma lem8227200 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term347 _144947 A B P p lt2 s a f g) : term347 _144947 A B P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8227201 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term348 _144947 A B P p lt2 s a f g) : term348 _144947 A B P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8227202 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : p f a.
Proof. exact (h1). Qed.
Lemma lem8227203 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term222 _144947 A B P lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8227204 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : p g a.
Proof. exact (h1). Qed.
Lemma lem8227206 {_144870 _144886 : Type'} (f : _144870 -> _144886) (x : list _144870) (g : _144870 -> _144886) (y : list _144870) : term29 _144870 _144886 f x g y.
Proof. exact (@lem8226156 _144870 _144886 f x g y (@lem8226148 _144870 _144886 f x g y)). Qed.
Lemma lem8227207 {_144956 _144962 : Type'} (f : _144962 -> _144956) (x : list _144962) (g : _144962 -> _144956) (y : list _144962) : term349 _144956 _144962 f x g y.
Proof. exact (@lem8227206 _144962 _144956 f x g y). Qed.
Lemma lem8227208 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term350 _144956 _144962 A B P f h l g a.
Proof. exact (@lem8227207 _144956 _144962 (h f a) (l f a) (h g a) (l g a)). Qed.
Lemma lem8227210 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8227211 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = (term351 _144962 A B P f l g a).
Proof. exact (@lem8227210 ((l f a) = (l g a))). Qed.
Lemma lem8227212 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term351 _144962 A B P f l g a) = ((l f a) = (l g a)).
Proof. exact (SYM (@lem8227211 _144962 A B P f l g a)). Qed.
Lemma lem8227213 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term352 _144962 A B P f l g a) : term352 _144962 A B P f l g a.
Proof. exact (h1). Qed.
Lemma lem8227216 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (h1). Qed.
Lemma lem8227217 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a => @lem8227216 _144947 _144956 _144962 A B P h p lt2 s f l g a h0). Qed.
Lemma lem8227218 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (h1). Qed.
Lemma lem8227219 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (h1). Qed.
Lemma lem8227220 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) (h2 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8227218 _144947 _144956 _144962 A B P h p lt2 s f l g a h2 (@lem8227219 _144947 _144956 _144962 A B P h p lt2 s f l g a h1)). Qed.
Lemma lem8227221 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term355 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a => @lem8227220 _144947 _144956 _144962 A B P h p lt2 s f l g a h1 h0). Qed.
Lemma lem8227222 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (h1). Qed.
Lemma lem8227223 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) (h2 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8227221 _144947 _144956 _144962 A B P h p lt2 s f l g a h1 (@lem8227222 _144947 _144956 _144962 A B P h p lt2 s f l g a h2)). Qed.
Lemma lem8227224 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a => @lem8227223 _144947 _144956 _144962 A B P h p lt2 s f l g a h0 h1). Qed.
Lemma lem8227225 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term356 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a => @lem8227224 _144947 _144956 _144962 A B P h p lt2 s f l g a h0). Qed.
Lemma lem8227228 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8227225 _144947 _144956 _144962 A B P h p lt2 s f l g a (@lem8227217 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8227229 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term354 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8227228 _144947 _144956 _144962 A B P h p lt2 s f l g a). Qed.
Lemma lem8227335 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8227336 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term351 _144962 A B P f l g a) = (term357 _144962 A B P f l g a).
Proof. exact (@lem8227335 (term352 _144962 A B P f l g a)). Qed.
Lemma lem8227338 (t : Prop) : (term36 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8227339 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term357 _144962 A B P f l g a) = ((l f a) = (l g a)).
Proof. exact (@lem8227338 ((l f a) = (l g a))). Qed.
Lemma lem8227340 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term351 _144962 A B P f l g a) = ((l f a) = (l g a)).
Proof. exact (TRANS (@lem8227336 _144962 A B P f l g a) (@lem8227339 _144962 A B P f l g a)). Qed.
Lemma lem8227341 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term358 _144947 A B P lt2 s a f g) = (term358 _144947 A B P lt2 s a f g).
Proof. exact (eq_refl (term358 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227342 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term359 _144947 _144962 A B P lt2 s f l g a) = (term360 _144947 _144962 A B P lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227341 _144947 A B P lt2 s a f g) (@lem8227340 _144962 A B P f l g a)). Qed.
Lemma lem8227345 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term361 A B P p g a) = (term361 A B P p g a).
Proof. exact (eq_refl (term361 A B P p g a)). Qed.
Lemma lem8227346 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term362 _144947 _144962 A B P p lt2 s f l g a) = (term363 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227345 A B P p g a) (@lem8227342 _144947 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227349 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term361 A B P p f a) = (term361 A B P p f a).
Proof. exact (eq_refl (term361 A B P p f a)). Qed.
Lemma lem8227350 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term364 _144947 _144962 A B P p lt2 s f l g a) = (term365 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227349 A B P p f a) (@lem8227346 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227353 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term366 _144947 _144956 _144962 A B P p l lt2 s h) = (term366 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (eq_refl (term366 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227354 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term367 _144947 _144956 _144962 A B P h p lt2 s f l g a) = (term368 _144947 _144956 _144962 A B P h p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227353 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8227350 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227357 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term369 _144947 _144962 A B P p lt2 s l) = (term369 _144947 _144962 A B P p lt2 s l).
Proof. exact (eq_refl (term369 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227358 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term353 _144947 _144956 _144962 A B P h p lt2 s f l g a) = (term370 _144947 _144956 _144962 A B P h p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227357 _144947 _144962 A B P p lt2 s l) (@lem8227354 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8227361 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term371 _144947 _144956 _144962 A B P p lt2 s f l g a) = (term372 _144947 _144956 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun h : type889 _144956 _144962 A B P => @lem8227358 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8227362 {_144956 _144962 A B P : Type'} : (@all ((A -> B) -> P -> _144962 -> _144956)) = (@all ((A -> B) -> P -> _144962 -> _144956)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> _144962 -> _144956))). Qed.
Lemma lem8227363 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term373 _144947 _144956 _144962 A B P p lt2 s f l g a) = (term374 _144947 _144956 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227362 _144956 _144962 A B P) (@lem8227361 _144947 _144956 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227368 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term375 _144947 _144956 _144962 A B P lt2 s f l g a) = (term376 _144947 _144956 _144962 A B P lt2 s f l g a).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8227363 _144947 _144956 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227369 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8227370 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term377 _144947 _144956 _144962 A B P lt2 s f l g a) = (term378 _144947 _144956 _144962 A B P lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227369 A B P) (@lem8227368 _144947 _144956 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227375 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term379 _144947 _144956 _144962 A B P s f l g a) = (term380 _144947 _144956 _144962 A B P s f l g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144947 A => @lem8227370 _144947 _144956 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227376 {_144947 A : Type'} : (@all (A -> _144947 -> Prop)) = (@all (A -> _144947 -> Prop)).
Proof. exact (eq_refl (@all (A -> _144947 -> Prop))). Qed.
Lemma lem8227377 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term381 _144947 _144956 _144962 A B P s f l g a) = (term382 _144947 _144956 _144962 A B P s f l g a).
Proof. exact (MK_COMB (@lem8227376 _144947 A) (@lem8227375 _144947 _144956 _144962 A B P s f l g a)). Qed.
Lemma lem8227382 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term383 _144947 _144956 _144962 A B P f l g a) = (term384 _144947 _144956 _144962 A B P f l g a).
Proof. exact (fun_ext (fun s : P -> _144947 => @lem8227377 _144947 _144956 _144962 A B P s f l g a)). Qed.
Lemma lem8227383 {_144947 P : Type'} : (@all (P -> _144947)) = (@all (P -> _144947)).
Proof. exact (eq_refl (@all (P -> _144947))). Qed.
Lemma lem8227384 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term385 _144947 _144956 _144962 A B P f l g a) = (term386 _144947 _144956 _144962 A B P f l g a).
Proof. exact (MK_COMB (@lem8227383 _144947 P) (@lem8227382 _144947 _144956 _144962 A B P f l g a)). Qed.
Lemma lem8227389 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term387 _144947 _144956 _144962 A B P l g a) = (term388 _144947 _144956 _144962 A B P l g a).
Proof. exact (fun_ext (fun f : A -> B => @lem8227384 _144947 _144956 _144962 A B P f l g a)). Qed.
Lemma lem8227390 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227391 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term389 _144947 _144956 _144962 A B P l g a) = (term390 _144947 _144956 _144962 A B P l g a).
Proof. exact (MK_COMB (@lem8227390 A B) (@lem8227389 _144947 _144956 _144962 A B P l g a)). Qed.
Lemma lem8227396 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : (term391 _144947 _144956 _144962 A B P g a) = (term392 _144947 _144956 _144962 A B P g a).
Proof. exact (fun_ext (fun l : type815 _144962 A B P => @lem8227391 _144947 _144956 _144962 A B P l g a)). Qed.
Lemma lem8227397 {_144962 A B P : Type'} : (@all ((A -> B) -> P -> list _144962)) = (@all ((A -> B) -> P -> list _144962)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> list _144962))). Qed.
Lemma lem8227398 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : (term393 _144947 _144956 _144962 A B P g a) = (term394 _144947 _144956 _144962 A B P g a).
Proof. exact (MK_COMB (@lem8227397 _144962 A B P) (@lem8227396 _144947 _144956 _144962 A B P g a)). Qed.
Lemma lem8227403 {_144947 _144956 _144962 A B P : Type'} (a : P) : (term395 _144947 _144956 _144962 A B P a) = (term396 _144947 _144956 _144962 A B P a).
Proof. exact (fun_ext (fun g : A -> B => @lem8227398 _144947 _144956 _144962 A B P g a)). Qed.
Lemma lem8227404 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227405 {_144947 _144956 _144962 A B P : Type'} (a : P) : (term397 _144947 _144956 _144962 A B P a) = (term398 _144947 _144956 _144962 A B P a).
Proof. exact (MK_COMB (@lem8227404 A B) (@lem8227403 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8227410 {_144947 _144956 _144962 A B P : Type'} : (term399 _144947 _144956 _144962 A B P) = (term400 _144947 _144956 _144962 A B P).
Proof. exact (fun_ext (fun a : P => @lem8227405 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8227411 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227420 {_144947 _144956 _144962 A B P : Type'} : (term401 _144947 _144956 _144962 A B P) = (term402 _144947 _144956 _144962 A B P).
Proof. exact (MK_COMB (@lem8227411 P) (@lem8227410 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227421 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227426 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term218 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227427 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term220 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227426 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227428 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8227429 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term222 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8227428 A) (@lem8227427 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227431 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term358 _144947 A B P lt2 s a f g) = (term358 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8227430) (@lem8227429 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227432 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term360 _144947 _144962 A B P lt2 s f l g a) = (term360 _144947 _144962 A B P lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227431 _144947 A B P lt2 s a f g) (@lem8227421 _144962 A B P f l g a)). Qed.
Lemma lem8227435 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term361 A B P p g a) = (term361 A B P p g a).
Proof. exact (eq_refl (term361 A B P p g a)). Qed.
Lemma lem8227436 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term363 _144947 _144962 A B P p lt2 s f l g a) = (term363 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227435 A B P p g a) (@lem8227432 _144947 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227439 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term361 A B P p f a) = (term361 A B P p f a).
Proof. exact (eq_refl (term361 A B P p f a)). Qed.
Lemma lem8227440 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term365 _144947 _144962 A B P p lt2 s f l g a) = (term365 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227439 A B P p f a) (@lem8227436 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227441 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8227446 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s p2 f g z) = (term218 _144947 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term218 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8227447 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s p2 f g) = (term220 _144947 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8227446 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8227448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8227449 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s p2 f g) = (term222 _144947 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8227448 A) (@lem8227447 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8227456 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term174 _144962 A B P p p1 l g p2) = (term174 _144962 A B P p p1 l g p2).
Proof. exact (eq_refl (term174 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8227457 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term224 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term224 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8227456 _144962 A B P p p1 l g p2) (@lem8227449 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8227464 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term174 _144962 A B P p p1 l f p2) = (term174 _144962 A B P p p1 l f p2).
Proof. exact (eq_refl (term174 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8227465 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term226 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8227464 _144962 A B P p p1 l f p2) (@lem8227457 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8227466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227467 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term228 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term228 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8227466) (@lem8227465 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8227468 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8227467 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8227441 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8227469 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term276 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term276 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8227468 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8227470 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227471 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8227470 P) (@lem8227469 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8227472 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term278 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term278 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8227471 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8227473 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8227474 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term279 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term279 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8227473 _144962) (@lem8227472 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8227475 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term281 _144947 _144956 _144962 A B P p l lt2 s f h) = (term281 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8227474 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8227476 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227477 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term283 _144947 _144956 _144962 A B P p l lt2 s f h) = (term283 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8227476 A B) (@lem8227475 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8227478 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term285 _144947 _144956 _144962 A B P p l lt2 s h) = (term285 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun f : A -> B => @lem8227477 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8227479 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227480 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term286 _144947 _144956 _144962 A B P p l lt2 s h) = (term286 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8227479 A B) (@lem8227478 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227482 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term366 _144947 _144956 _144962 A B P p l lt2 s h) = (term366 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8227481) (@lem8227480 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8227483 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term368 _144947 _144956 _144962 A B P h p lt2 s f l g a) = (term368 _144947 _144956 _144962 A B P h p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227482 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8227440 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227484 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227489 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term218 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227490 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term220 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227489 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8227492 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term222 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8227491 A) (@lem8227490 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227495 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term403 A B P p g a) = (term403 A B P p g a).
Proof. exact (eq_refl (term403 A B P p g a)). Qed.
Lemma lem8227496 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term348 _144947 A B P p lt2 s a f g) = (term348 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227495 A B P p g a) (@lem8227492 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227499 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term403 A B P p f a) = (term403 A B P p f a).
Proof. exact (eq_refl (term403 A B P p f a)). Qed.
Lemma lem8227500 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term347 _144947 A B P p lt2 s a f g) = (term347 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227499 A B P p f a) (@lem8227496 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227502 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term311 _144947 A B P p lt2 s a f g) = (term311 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227501) (@lem8227500 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227503 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term404 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227502 _144947 A B P p lt2 s a f g) (@lem8227484 _144962 A B P f l g a)). Qed.
Lemma lem8227504 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term405 _144947 _144962 A B P p lt2 s f l g) = (term405 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8227503 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227505 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227506 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term406 _144947 _144962 A B P p lt2 s f l g) = (term406 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227505 P) (@lem8227504 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227507 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term407 _144947 _144962 A B P p lt2 s f l) = (term407 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227506 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227508 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227509 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term408 _144947 _144962 A B P p lt2 s f l) = (term408 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227508 A B) (@lem8227507 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227510 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term409 _144947 _144962 A B P p lt2 s l) = (term409 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227509 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227511 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227512 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term87 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8227511 A B) (@lem8227510 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8227514 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term369 _144947 _144962 A B P p lt2 s l) = (term369 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8227513) (@lem8227512 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227515 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term370 _144947 _144956 _144962 A B P h p lt2 s f l g a) = (term370 _144947 _144956 _144962 A B P h p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227514 _144947 _144962 A B P p lt2 s l) (@lem8227483 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8227516 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term372 _144947 _144956 _144962 A B P p lt2 s f l g a) = (term372 _144947 _144956 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun h : type889 _144956 _144962 A B P => @lem8227515 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8227517 {_144956 _144962 A B P : Type'} : (@all ((A -> B) -> P -> _144962 -> _144956)) = (@all ((A -> B) -> P -> _144962 -> _144956)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> _144962 -> _144956))). Qed.
Lemma lem8227518 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term374 _144947 _144956 _144962 A B P p lt2 s f l g a) = (term374 _144947 _144956 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227517 _144956 _144962 A B P) (@lem8227516 _144947 _144956 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227519 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term376 _144947 _144956 _144962 A B P lt2 s f l g a) = (term376 _144947 _144956 _144962 A B P lt2 s f l g a).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8227518 _144947 _144956 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227520 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8227521 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term378 _144947 _144956 _144962 A B P lt2 s f l g a) = (term378 _144947 _144956 _144962 A B P lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227520 A B P) (@lem8227519 _144947 _144956 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227522 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term380 _144947 _144956 _144962 A B P s f l g a) = (term380 _144947 _144956 _144962 A B P s f l g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144947 A => @lem8227521 _144947 _144956 _144962 A B P lt2 s f l g a)). Qed.
Lemma lem8227523 {_144947 A : Type'} : (@all (A -> _144947 -> Prop)) = (@all (A -> _144947 -> Prop)).
Proof. exact (eq_refl (@all (A -> _144947 -> Prop))). Qed.
Lemma lem8227524 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term382 _144947 _144956 _144962 A B P s f l g a) = (term382 _144947 _144956 _144962 A B P s f l g a).
Proof. exact (MK_COMB (@lem8227523 _144947 A) (@lem8227522 _144947 _144956 _144962 A B P s f l g a)). Qed.
Lemma lem8227525 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term384 _144947 _144956 _144962 A B P f l g a) = (term384 _144947 _144956 _144962 A B P f l g a).
Proof. exact (fun_ext (fun s : P -> _144947 => @lem8227524 _144947 _144956 _144962 A B P s f l g a)). Qed.
Lemma lem8227526 {_144947 P : Type'} : (@all (P -> _144947)) = (@all (P -> _144947)).
Proof. exact (eq_refl (@all (P -> _144947))). Qed.
Lemma lem8227527 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term386 _144947 _144956 _144962 A B P f l g a) = (term386 _144947 _144956 _144962 A B P f l g a).
Proof. exact (MK_COMB (@lem8227526 _144947 P) (@lem8227525 _144947 _144956 _144962 A B P f l g a)). Qed.
Lemma lem8227528 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term388 _144947 _144956 _144962 A B P l g a) = (term388 _144947 _144956 _144962 A B P l g a).
Proof. exact (fun_ext (fun f : A -> B => @lem8227527 _144947 _144956 _144962 A B P f l g a)). Qed.
Lemma lem8227529 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227530 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term390 _144947 _144956 _144962 A B P l g a) = (term390 _144947 _144956 _144962 A B P l g a).
Proof. exact (MK_COMB (@lem8227529 A B) (@lem8227528 _144947 _144956 _144962 A B P l g a)). Qed.
Lemma lem8227531 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : (term392 _144947 _144956 _144962 A B P g a) = (term392 _144947 _144956 _144962 A B P g a).
Proof. exact (fun_ext (fun l : type815 _144962 A B P => @lem8227530 _144947 _144956 _144962 A B P l g a)). Qed.
Lemma lem8227532 {_144962 A B P : Type'} : (@all ((A -> B) -> P -> list _144962)) = (@all ((A -> B) -> P -> list _144962)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> list _144962))). Qed.
Lemma lem8227533 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : (term394 _144947 _144956 _144962 A B P g a) = (term394 _144947 _144956 _144962 A B P g a).
Proof. exact (MK_COMB (@lem8227532 _144962 A B P) (@lem8227531 _144947 _144956 _144962 A B P g a)). Qed.
Lemma lem8227534 {_144947 _144956 _144962 A B P : Type'} (a : P) : (term396 _144947 _144956 _144962 A B P a) = (term396 _144947 _144956 _144962 A B P a).
Proof. exact (fun_ext (fun g : A -> B => @lem8227533 _144947 _144956 _144962 A B P g a)). Qed.
Lemma lem8227535 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227536 {_144947 _144956 _144962 A B P : Type'} (a : P) : (term398 _144947 _144956 _144962 A B P a) = (term398 _144947 _144956 _144962 A B P a).
Proof. exact (MK_COMB (@lem8227535 A B) (@lem8227534 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8227537 {_144947 _144956 _144962 A B P : Type'} : (term400 _144947 _144956 _144962 A B P) = (term400 _144947 _144956 _144962 A B P).
Proof. exact (fun_ext (fun a : P => @lem8227536 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8227538 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227539 {_144947 _144956 _144962 A B P : Type'} : (term402 _144947 _144956 _144962 A B P) = (term402 _144947 _144956 _144962 A B P).
Proof. exact (MK_COMB (@lem8227538 P) (@lem8227537 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227682 {_144947 _144956 _144962 A B P : Type'} : (term401 _144947 _144956 _144962 A B P) = (term402 _144947 _144956 _144962 A B P).
Proof. exact (TRANS (@lem8227420 _144947 _144956 _144962 A B P) (@lem8227539 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227683 {_144947 _144956 _144962 A B P : Type'} : (term402 _144947 _144956 _144962 A B P) = (term401 _144947 _144956 _144962 A B P).
Proof. exact (SYM (@lem8227682 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8227684 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term87 _144947 _144962 A B P p lt2 s l.
Proof. exact (h1). Qed.
Lemma lem8227685 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term286 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8227688 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term222 _144947 A B P lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8227690 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8227691 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = (term351 _144962 A B P f l g a).
Proof. exact (@lem8227690 ((l f a) = (l g a))). Qed.
Lemma lem8227692 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term351 _144962 A B P f l g a) = ((l f a) = (l g a)).
Proof. exact (SYM (@lem8227691 _144962 A B P f l g a)). Qed.
Lemma lem8227693 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term352 _144962 A B P f l g a) : term352 _144962 A B P f l g a.
Proof. exact (h1). Qed.
Lemma lem8227702 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term410 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term214 _144947 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8227703 {A : Type'} (P : A -> Prop) : (term412 A P) = (term413 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8227704 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s a f g) = (term415 _144947 A B P lt2 s a f g).
Proof. exact (@lem8227703 A (term220 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227705 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term416 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term416 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8227707 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s a f g z) = (term410 _144947 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8227706) (@lem8227705 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227708 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8227707 _144947 A B P lt2 s a f g z) (@lem8227702 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227709 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term418 _144947 A B P lt2 s a f g) = (term419 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227708 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227710 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227711 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term415 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8227710 A) (@lem8227709 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227712 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8227704 _144947 A B P lt2 s a f g) (@lem8227711 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227714 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8227715 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term422 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227714 A B P p g a) (@lem8227712 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227716 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term424 _144947 A B P p lt2 s a f g) = (term422 _144947 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term222 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227717 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term424 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8227716 _144947 A B P p lt2 s a f g) (@lem8227715 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227719 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8227720 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term425 _144947 A B P p lt2 s a f g) = (term426 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227719 A B P p f a) (@lem8227717 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227721 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term427 _144947 A B P p lt2 s a f g) = (term425 _144947 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term348 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227722 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term427 _144947 A B P p lt2 s a f g) = (term426 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8227721 _144947 A B P p lt2 s a f g) (@lem8227720 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227723 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8227725 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term428 _144947 A B P p lt2 s a f g) = (term429 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227724) (@lem8227722 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227726 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term430 _144947 _144962 A B P p lt2 s f l g a) = (term431 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227725 _144947 A B P p lt2 s a f g) (@lem8227723 _144962 A B P f l g a)). Qed.
Lemma lem8227727 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term430 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (@lem17265 (term347 _144947 A B P p lt2 s a f g) ((l f a) = (l g a))). Qed.
Lemma lem8227728 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term431 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (TRANS (@lem8227727 _144947 _144962 A B P p lt2 s f l g a) (@lem8227726 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227729 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term405 _144947 _144962 A B P p lt2 s f l g) = (term432 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8227728 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227730 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227731 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term406 _144947 _144962 A B P p lt2 s f l g) = (term433 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227730 P) (@lem8227729 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227732 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term407 _144947 _144962 A B P p lt2 s f l) = (term434 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227731 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227733 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227734 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term408 _144947 _144962 A B P p lt2 s f l) = (term435 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227733 A B) (@lem8227732 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227735 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term409 _144947 _144962 A B P p lt2 s l) = (term436 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227734 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227736 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227737 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term437 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8227736 A B) (@lem8227735 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8227845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8227844 A P Q). Qed.
Lemma lem8227846 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term440 _144947 A B P p lt2 s a f g) = (term441 _144947 A B P p lt2 s a f g).
Proof. exact (@lem8227845 A (term442 A B P p g a) (term419 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227847 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227848 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term444 _144947 A B P lt2 s a f g) = (term419 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227847 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227850 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term445 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8227849 A) (@lem8227848 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227851 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8227852 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term440 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227851 A B P p g a) (@lem8227850 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8227853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8227854 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term446 _144947 A B P p lt2 s a f g) = (term447 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227853) (@lem8227852 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227855 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227856 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8227857 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term448 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8227856 A B P p g a) (@lem8227855 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8227858 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term450 _144947 A B P p lt2 s a f g) = (term451 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227857 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227860 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term441 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227859 A) (@lem8227858 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227861 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : ((term440 _144947 A B P p lt2 s a f g) = (term441 _144947 A B P p lt2 s a f g)) = ((term423 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8227854 _144947 A B P p lt2 s a f g) (@lem8227860 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227862 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term423 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8227861 _144947 A B P p lt2 s a f g) (@lem8227846 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227863 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8227864 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term426 _144947 A B P p lt2 s a f g) = (term453 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227863 A B P p f a) (@lem8227862 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227866 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8227867 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8227866 A P Q). Qed.
Lemma lem8227868 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term454 _144947 A B P p lt2 s a f g) = (term455 _144947 A B P p lt2 s a f g).
Proof. exact (@lem8227867 A (term442 A B P p f a) (term451 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227869 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term456 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term456 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227870 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term457 _144947 A B P p lt2 s a f g) = (term451 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227869 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227872 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term458 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227871 A) (@lem8227870 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227873 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8227874 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term454 _144947 A B P p lt2 s a f g) = (term453 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227873 A B P p f a) (@lem8227872 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8227876 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term459 _144947 A B P p lt2 s a f g) = (term460 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227875) (@lem8227874 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227877 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term456 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term456 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227878 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8227879 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term461 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8227878 A B P p f a) (@lem8227877 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227880 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term463 _144947 A B P p lt2 s a f g) = (term464 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227879 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227882 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term455 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227881 A) (@lem8227880 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227883 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : ((term454 _144947 A B P p lt2 s a f g) = (term455 _144947 A B P p lt2 s a f g)) = ((term453 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8227876 _144947 A B P p lt2 s a f g) (@lem8227882 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227884 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term453 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8227883 _144947 A B P p lt2 s a f g) (@lem8227868 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227885 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term426 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8227864 _144947 A B P p lt2 s a f g) (@lem8227884 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8227887 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term429 _144947 A B P p lt2 s a f g) = (term466 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227886) (@lem8227885 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227888 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227889 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term431 _144947 _144962 A B P p lt2 s f l g a) = (term467 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227887 _144947 A B P p lt2 s a f g) (@lem8227888 _144962 A B P f l g a)). Qed.
Lemma lem8227891 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8227892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (@lem8227891 A P Q). Qed.
Lemma lem8227893 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term470 _144947 _144962 A B P p lt2 s f l g a) = (term471 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (@lem8227892 A (term464 _144947 A B P p lt2 s a f g) ((l f a) = (l g a))). Qed.
Lemma lem8227894 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term472 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term472 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227895 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term473 _144947 A B P p lt2 s a f g) = (term464 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8227894 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227897 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term474 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227896 A) (@lem8227895 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8227899 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term475 _144947 A B P p lt2 s a f g) = (term466 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8227898) (@lem8227897 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8227900 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227901 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term470 _144947 _144962 A B P p lt2 s f l g a) = (term467 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227899 _144947 A B P p lt2 s a f g) (@lem8227900 _144962 A B P f l g a)). Qed.
Lemma lem8227902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8227903 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term476 _144947 _144962 A B P p lt2 s f l g a) = (term477 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227902) (@lem8227901 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227904 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term472 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term472 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8227906 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term478 _144947 A B P p lt2 s a f g z) = (term479 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8227905) (@lem8227904 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8227907 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8227908 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term480 _144947 _144962 A B P p lt2 s z f l g a) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (MK_COMB (@lem8227906 _144947 A B P p lt2 s a f g z) (@lem8227907 _144962 A B P f l g a)). Qed.
Lemma lem8227909 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term482 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun z : A => @lem8227908 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8227910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227911 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term471 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227910 A) (@lem8227909 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227912 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term470 _144947 _144962 A B P p lt2 s f l g a) = (term471 _144947 _144962 A B P p lt2 s f l g a)) = ((term467 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a)).
Proof. exact (MK_COMB (@lem8227903 _144947 _144962 A B P p lt2 s f l g a) (@lem8227911 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227913 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term467 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (EQ_MP (@lem8227912 _144947 _144962 A B P p lt2 s f l g a) (@lem8227893 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227914 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term431 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (TRANS (@lem8227889 _144947 _144962 A B P p lt2 s f l g a) (@lem8227913 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227915 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term432 _144947 _144962 A B P p lt2 s f l g) = (term485 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8227914 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227916 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227917 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term433 _144947 _144962 A B P p lt2 s f l g) = (term486 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227916 P) (@lem8227915 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227919 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8227920 {A P : Type'} (P' : type1470 A P) : (term489 A P P') = (term490 A P P').
Proof. exact (@lem8227919 P A P'). Qed.
Lemma lem8227921 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term491 _144947 _144962 A B P p lt2 s f l g) = (term492 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (@lem8227920 A P (term493 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227922 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term494 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (eq_refl (term494 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227923 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8227924 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (z : A) : (term495 _144947 _144962 A B P p lt2 s f l g a z) = (term496 _144947 _144962 A B P p lt2 s f l g a z).
Proof. exact (MK_COMB (@lem8227922 _144947 _144962 A B P p lt2 s f l g a) (@lem8227923 A z)). Qed.
Lemma lem8227925 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term496 _144947 _144962 A B P p lt2 s f l g a z) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (eq_refl (term496 _144947 _144962 A B P p lt2 s f l g a z)). Qed.
Lemma lem8227926 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term495 _144947 _144962 A B P p lt2 s f l g a z) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (TRANS (@lem8227924 _144947 _144962 A B P p lt2 s f l g a z) (@lem8227925 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8227927 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term497 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun z : A => @lem8227926 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8227928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8227929 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term498 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8227928 A) (@lem8227927 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227930 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term499 _144947 _144962 A B P p lt2 s f l g) = (term485 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8227929 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227931 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227932 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term491 _144947 _144962 A B P p lt2 s f l g) = (term486 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227931 P) (@lem8227930 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8227934 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term500 _144947 _144962 A B P p lt2 s f l g) = (term501 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227933) (@lem8227932 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227935 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term494 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (eq_refl (term494 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8227936 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8227937 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (z : P -> A) (a : P) : (term502 _144947 _144962 A B P p lt2 s f l g z a) = (term503 _144947 _144962 A B P p lt2 s f l g z a).
Proof. exact (MK_COMB (@lem8227935 _144947 _144962 A B P p lt2 s f l g a) (@lem8227936 A P z a)). Qed.
Lemma lem8227938 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term503 _144947 _144962 A B P p lt2 s f l g z a) = (term504 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (eq_refl (term503 _144947 _144962 A B P p lt2 s f l g z a)). Qed.
Lemma lem8227939 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term502 _144947 _144962 A B P p lt2 s f l g z a) = (term504 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (TRANS (@lem8227937 _144947 _144962 A B P p lt2 s f l g z a) (@lem8227938 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8227940 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term505 _144947 _144962 A B P p lt2 s f l g z) = (term506 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (fun_ext (fun a : P => @lem8227939 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8227941 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8227942 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term507 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (MK_COMB (@lem8227941 P) (@lem8227940 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227943 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term509 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun z : P -> A => @lem8227942 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227944 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8227945 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term492 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227944 A P) (@lem8227943 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227946 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : ((term491 _144947 _144962 A B P p lt2 s f l g) = (term492 _144947 _144962 A B P p lt2 s f l g)) = ((term486 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g)).
Proof. exact (MK_COMB (@lem8227934 _144947 _144962 A B P p lt2 s f l g) (@lem8227945 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227947 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term486 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (EQ_MP (@lem8227946 _144947 _144962 A B P p lt2 s f l g) (@lem8227921 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227948 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term433 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (TRANS (@lem8227917 _144947 _144962 A B P p lt2 s f l g) (@lem8227947 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227949 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term434 _144947 _144962 A B P p lt2 s f l) = (term512 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227948 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227950 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227951 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term435 _144947 _144962 A B P p lt2 s f l) = (term513 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227950 A B) (@lem8227949 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227953 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8227954 {A B P : Type'} (P' : type537 A B P) : (term514 A B P P') = (term515 A B P P').
Proof. exact (@lem8227953 (A -> B) (P -> A) P'). Qed.
Lemma lem8227955 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term516 _144947 _144962 A B P p lt2 s f l) = (term517 _144947 _144962 A B P p lt2 s f l).
Proof. exact (@lem8227954 A B P (term518 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227956 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term519 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (eq_refl (term519 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227957 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8227958 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (z : P -> A) : (term520 _144947 _144962 A B P p lt2 s f l g z) = (term521 _144947 _144962 A B P p lt2 s f l g z).
Proof. exact (MK_COMB (@lem8227956 _144947 _144962 A B P p lt2 s f l g) (@lem8227957 A P z)). Qed.
Lemma lem8227959 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term521 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (eq_refl (term521 _144947 _144962 A B P p lt2 s f l g z)). Qed.
Lemma lem8227960 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term520 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (TRANS (@lem8227958 _144947 _144962 A B P p lt2 s f l g z) (@lem8227959 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227961 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term522 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun z : P -> A => @lem8227960 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227962 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8227963 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term523 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8227962 A P) (@lem8227961 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227964 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term524 _144947 _144962 A B P p lt2 s f l) = (term512 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227963 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227965 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227966 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term516 _144947 _144962 A B P p lt2 s f l) = (term513 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227965 A B) (@lem8227964 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8227968 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term525 _144947 _144962 A B P p lt2 s f l) = (term526 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227967) (@lem8227966 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227969 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term519 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (eq_refl (term519 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8227970 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8227971 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (z : type557 A B P) (g : A -> B) : (term527 _144947 _144962 A B P p lt2 s f l z g) = (term528 _144947 _144962 A B P p lt2 s f l z g).
Proof. exact (MK_COMB (@lem8227969 _144947 _144962 A B P p lt2 s f l g) (@lem8227970 A B P z g)). Qed.
Lemma lem8227972 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term528 _144947 _144962 A B P p lt2 s f l z g) = (term529 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (eq_refl (term528 _144947 _144962 A B P p lt2 s f l z g)). Qed.
Lemma lem8227973 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term527 _144947 _144962 A B P p lt2 s f l z g) = (term529 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (TRANS (@lem8227971 _144947 _144962 A B P p lt2 s f l z g) (@lem8227972 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227974 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term530 _144947 _144962 A B P p lt2 s f l z) = (term531 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8227973 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8227975 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227976 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term532 _144947 _144962 A B P p lt2 s f l z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (MK_COMB (@lem8227975 A B) (@lem8227974 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8227977 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term534 _144947 _144962 A B P p lt2 s f l) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8227976 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8227978 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8227979 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term517 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227978 A B P) (@lem8227977 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227980 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : ((term516 _144947 _144962 A B P p lt2 s f l) = (term517 _144947 _144962 A B P p lt2 s f l)) = ((term513 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l)).
Proof. exact (MK_COMB (@lem8227968 _144947 _144962 A B P p lt2 s f l) (@lem8227979 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227981 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term513 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (EQ_MP (@lem8227980 _144947 _144962 A B P p lt2 s f l) (@lem8227955 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227982 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term435 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (TRANS (@lem8227951 _144947 _144962 A B P p lt2 s f l) (@lem8227981 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227983 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term436 _144947 _144962 A B P p lt2 s l) = (term537 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227982 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227984 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8227985 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term437 _144947 _144962 A B P p lt2 s l) = (term538 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8227984 A B) (@lem8227983 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227987 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8227988 {A B P : Type'} (P' : type495 A B P) : (term539 A B P P') = (term540 A B P P').
Proof. exact (@lem8227987 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8227989 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term541 _144947 _144962 A B P p lt2 s l) = (term542 _144947 _144962 A B P p lt2 s l).
Proof. exact (@lem8227988 A B P (term543 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8227990 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term544 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (eq_refl (term544 _144947 _144962 A B P p lt2 s l f)). Qed.
Lemma lem8227991 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8227992 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (z : type557 A B P) : (term545 _144947 _144962 A B P p lt2 s l f z) = (term546 _144947 _144962 A B P p lt2 s f l z).
Proof. exact (MK_COMB (@lem8227990 _144947 _144962 A B P p lt2 s f l) (@lem8227991 A B P z)). Qed.
Lemma lem8227993 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term546 _144947 _144962 A B P p lt2 s f l z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (eq_refl (term546 _144947 _144962 A B P p lt2 s f l z)). Qed.
Lemma lem8227994 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term545 _144947 _144962 A B P p lt2 s l f z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (TRANS (@lem8227992 _144947 _144962 A B P p lt2 s f l z) (@lem8227993 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8227995 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term547 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8227994 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8227996 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8227997 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term548 _144947 _144962 A B P p lt2 s l f) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8227996 A B P) (@lem8227995 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227998 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term549 _144947 _144962 A B P p lt2 s l) = (term537 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8227997 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8227999 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228000 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term541 _144947 _144962 A B P p lt2 s l) = (term538 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8227999 A B) (@lem8227998 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228002 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term550 _144947 _144962 A B P p lt2 s l) = (term551 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8228001) (@lem8228000 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228003 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term544 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (eq_refl (term544 _144947 _144962 A B P p lt2 s l f)). Qed.
Lemma lem8228004 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8228005 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (z : type518 A B P) (f : A -> B) : (term552 _144947 _144962 A B P p lt2 s l z f) = (term553 _144947 _144962 A B P p lt2 s l z f).
Proof. exact (MK_COMB (@lem8228003 _144947 _144962 A B P p lt2 s f l) (@lem8228004 A B P z f)). Qed.
Lemma lem8228006 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term553 _144947 _144962 A B P p lt2 s l z f) = (term554 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (eq_refl (term553 _144947 _144962 A B P p lt2 s l z f)). Qed.
Lemma lem8228007 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term552 _144947 _144962 A B P p lt2 s l z f) = (term554 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (TRANS (@lem8228005 _144947 _144962 A B P p lt2 s l z f) (@lem8228006 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8228008 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term555 _144947 _144962 A B P p lt2 s l z) = (term556 _144947 _144962 A B P p lt2 s z l).
Proof. exact (fun_ext (fun f : A -> B => @lem8228007 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8228009 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228010 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term557 _144947 _144962 A B P p lt2 s l z) = (term558 _144947 _144962 A B P p lt2 s z l).
Proof. exact (MK_COMB (@lem8228009 A B) (@lem8228008 _144947 _144962 A B P p lt2 s z l)). Qed.
Lemma lem8228011 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term559 _144947 _144962 A B P p lt2 s l) = (term560 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8228010 _144947 _144962 A B P p lt2 s z l)). Qed.
Lemma lem8228012 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8228013 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term542 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8228012 A B P) (@lem8228011 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228014 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : ((term541 _144947 _144962 A B P p lt2 s l) = (term542 _144947 _144962 A B P p lt2 s l)) = ((term538 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l)).
Proof. exact (MK_COMB (@lem8228002 _144947 _144962 A B P p lt2 s l) (@lem8228013 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228015 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term538 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (EQ_MP (@lem8228014 _144947 _144962 A B P p lt2 s l) (@lem8227989 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228017 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term437 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (TRANS (@lem8227985 _144947 _144962 A B P p lt2 s l) (@lem8228015 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228018 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (TRANS (@lem8227737 _144947 _144962 A B P p lt2 s l) (@lem8228017 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8228019 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term561 _144947 _144962 A B P p lt2 s l.
Proof. exact (EQ_MP (@lem8228018 _144947 _144962 A B P p lt2 s l) (@lem8227684 _144947 _144962 A B P p lt2 s l h1)). Qed.
Lemma lem8228026 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term562 _144962 A B P p p1 l f p2) = (term563 _144962 A B P p p1 l f p2).
Proof. exact (@lem17045 (p f p2) (term564 _144962 A B P p1 l f p2)). Qed.
Lemma lem8228033 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term562 _144962 A B P p p1 l g p2) = (term563 _144962 A B P p p1 l g p2).
Proof. exact (@lem17045 (p g p2) (term564 _144962 A B P p1 l g p2)). Qed.
Lemma lem8228040 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term410 _144947 A B P lt2 s p2 f g z) = (term411 _144947 A B P lt2 s p2 f g z).
Proof. exact (@lem17362 (term214 _144947 A P lt2 z s p2) ((f z) = (g z))). Qed.
Lemma lem8228041 {A : Type'} (P : A -> Prop) : (term412 A P) = (term413 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8228042 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s p2 f g) = (term415 _144947 A B P lt2 s p2 f g).
Proof. exact (@lem8228041 A (term220 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228043 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term416 _144947 A B P lt2 s p2 f g z) = (term218 _144947 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term416 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8228045 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s p2 f g z) = (term410 _144947 A B P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8228044) (@lem8228043 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228046 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s p2 f g z) = (term411 _144947 A B P lt2 s p2 f g z).
Proof. exact (TRANS (@lem8228045 _144947 A B P lt2 s p2 f g z) (@lem8228040 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228047 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term418 _144947 A B P lt2 s p2 f g) = (term419 _144947 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228046 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228048 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228049 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term415 _144947 A B P lt2 s p2 f g) = (term420 _144947 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228048 A) (@lem8228047 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228050 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s p2 f g) = (term420 _144947 A B P lt2 s p2 f g).
Proof. exact (TRANS (@lem8228042 _144947 A B P lt2 s p2 f g) (@lem8228049 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228052 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term565 _144962 A B P p p1 l g p2) = (term566 _144962 A B P p p1 l g p2).
Proof. exact (MK_COMB (@lem8228051) (@lem8228033 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8228053 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term567 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term568 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228052 _144962 A B P p p1 l g p2) (@lem8228050 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228054 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term569 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term567 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (@lem17045 (term144 _144962 A B P p p1 l g p2) (term222 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228055 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term569 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term568 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (TRANS (@lem8228054 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228053 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228056 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228057 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term565 _144962 A B P p p1 l f p2) = (term566 _144962 A B P p p1 l f p2).
Proof. exact (MK_COMB (@lem8228056) (@lem8228026 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8228058 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term570 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term571 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228057 _144962 A B P p p1 l f p2) (@lem8228055 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228059 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term572 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term570 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (@lem17045 (term144 _144962 A B P p p1 l f p2) (term224 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228060 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term572 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term571 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (TRANS (@lem8228059 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228058 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228061 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228063 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term573 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term574 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228062) (@lem8228060 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228064 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term575 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term576 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228063 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228061 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8228065 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term575 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (@lem17265 (term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228066 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term576 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8228065 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228064 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228067 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term276 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term577 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8228066 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228068 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8228069 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term578 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228068 P) (@lem8228067 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228070 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term278 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term579 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8228069 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228071 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8228072 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term279 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term580 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228071 _144962) (@lem8228070 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228073 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term281 _144947 _144956 _144962 A B P p l lt2 s f h) = (term581 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8228072 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228074 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228075 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term283 _144947 _144956 _144962 A B P p l lt2 s f h) = (term582 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228074 A B) (@lem8228073 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228076 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term285 _144947 _144956 _144962 A B P p l lt2 s h) = (term583 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun f : A -> B => @lem8228075 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228077 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228078 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term286 _144947 _144956 _144962 A B P p l lt2 s h) = (term584 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8228077 A B) (@lem8228076 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228189 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8228190 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8228189 A P Q). Qed.
Lemma lem8228191 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term585 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term586 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (@lem8228190 A (term563 _144962 A B P p p1 l g p2) (term419 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228192 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s p2 f g z) = (term411 _144947 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228193 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term444 _144947 A B P lt2 s p2 f g) = (term419 _144947 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228192 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228194 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228195 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term445 _144947 A B P lt2 s p2 f g) = (term420 _144947 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228194 A) (@lem8228193 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228196 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term566 _144962 A B P p p1 l g p2) = (term566 _144962 A B P p p1 l g p2).
Proof. exact (eq_refl (term566 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8228197 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term585 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term568 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228196 _144962 A B P p p1 l g p2) (@lem8228195 _144947 A B P lt2 s p2 f g)). Qed.
Lemma lem8228198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228199 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term587 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term588 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228198) (@lem8228197 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228200 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s p2 f g z) = (term411 _144947 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228201 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (g : A -> B) (p2 : P) : (term566 _144962 A B P p p1 l g p2) = (term566 _144962 A B P p p1 l g p2).
Proof. exact (eq_refl (term566 _144962 A B P p p1 l g p2)). Qed.
Lemma lem8228202 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term589 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term590 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8228201 _144962 A B P p p1 l g p2) (@lem8228200 _144947 A B P lt2 s p2 f g z)). Qed.
Lemma lem8228203 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term591 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term592 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228202 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228204 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228205 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term586 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term593 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228204 A) (@lem8228203 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228206 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : ((term585 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term586 _144947 _144962 A B P p p1 l lt2 s p2 f g)) = ((term568 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term593 _144947 _144962 A B P p p1 l lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8228199 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228205 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228207 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term568 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term593 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8228206 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228191 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228208 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term566 _144962 A B P p p1 l f p2) = (term566 _144962 A B P p p1 l f p2).
Proof. exact (eq_refl (term566 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8228209 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term571 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term594 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228208 _144962 A B P p p1 l f p2) (@lem8228207 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228211 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8228212 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8228211 A P Q). Qed.
Lemma lem8228213 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term595 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term596 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (@lem8228212 A (term563 _144962 A B P p p1 l f p2) (term592 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228214 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term597 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term590 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (eq_refl (term597 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228215 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term598 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term592 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228214 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228217 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term599 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term593 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228216 A) (@lem8228215 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228218 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term566 _144962 A B P p p1 l f p2) = (term566 _144962 A B P p p1 l f p2).
Proof. exact (eq_refl (term566 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8228219 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term595 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term594 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228218 _144962 A B P p p1 l f p2) (@lem8228217 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228221 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term600 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term601 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228220) (@lem8228219 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228222 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term597 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term590 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (eq_refl (term597 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228223 {_144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (f : A -> B) (p2 : P) : (term566 _144962 A B P p p1 l f p2) = (term566 _144962 A B P p p1 l f p2).
Proof. exact (eq_refl (term566 _144962 A B P p p1 l f p2)). Qed.
Lemma lem8228224 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term602 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term603 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8228223 _144962 A B P p p1 l f p2) (@lem8228222 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228225 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term604 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term605 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228224 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228226 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228227 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term596 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term606 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228226 A) (@lem8228225 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228228 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : ((term595 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term596 _144947 _144962 A B P p p1 l lt2 s p2 f g)) = ((term594 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term606 _144947 _144962 A B P p p1 l lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8228221 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228227 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228229 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term594 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term606 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8228228 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228213 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228230 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term571 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term606 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (TRANS (@lem8228209 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228229 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228232 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term574 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term607 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228231) (@lem8228230 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228233 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228234 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term576 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term608 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228232 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228233 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8228236 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8228237 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (@lem8228236 A P Q). Qed.
Lemma lem8228238 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term609 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term610 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (@lem8228237 A (term605 _144947 _144962 A B P p p1 l lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228239 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term611 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term603 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (eq_refl (term611 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228240 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term612 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term605 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8228239 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228242 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term613 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term606 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228241 A) (@lem8228240 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228244 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) : (term614 _144947 _144962 A B P p p1 l lt2 s p2 f g) = (term607 _144947 _144962 A B P p p1 l lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8228243) (@lem8228242 _144947 _144962 A B P p p1 l lt2 s p2 f g)). Qed.
Lemma lem8228245 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228246 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term609 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term608 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228244 _144947 _144962 A B P p p1 l lt2 s p2 f g) (@lem8228245 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8228247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228248 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term615 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term616 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228247) (@lem8228246 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228249 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term611 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term603 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (eq_refl (term611 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228251 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term617 _144947 _144962 A B P p p1 l lt2 s p2 f g z) = (term618 _144947 _144962 A B P p p1 l lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8228250) (@lem8228249 _144947 _144962 A B P p p1 l lt2 s p2 f g z)). Qed.
Lemma lem8228252 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8228253 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term619 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1) = (term620 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1).
Proof. exact (MK_COMB (@lem8228251 _144947 _144962 A B P p p1 l lt2 s p2 f g z) (@lem8228252 _144956 _144962 A B P f h g p2 p1)). Qed.
Lemma lem8228254 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term621 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term622 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : A => @lem8228253 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1)). Qed.
Lemma lem8228255 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228256 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term610 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term623 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228255 A) (@lem8228254 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228257 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : ((term609 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term610 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)) = ((term608 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term623 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)).
Proof. exact (MK_COMB (@lem8228248 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228256 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228258 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term608 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term623 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (EQ_MP (@lem8228257 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228238 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228259 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term576 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term623 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8228234 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228258 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228260 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term577 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term624 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8228259 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228261 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8228262 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term578 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term625 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228261 P) (@lem8228260 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228264 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8228265 {A P : Type'} (P' : type1470 A P) : (term489 A P P') = (term490 A P P').
Proof. exact (@lem8228264 P A P'). Qed.
Lemma lem8228266 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term626 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term627 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (@lem8228265 A P (term628 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228267 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term629 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term622 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (eq_refl (term629 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2)). Qed.
Lemma lem8228268 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8228269 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) (z : A) : (term630 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2 z) = (term631 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1 z).
Proof. exact (MK_COMB (@lem8228267 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228268 A z)). Qed.
Lemma lem8228270 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term631 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1 z) = (term620 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term631 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1 z)). Qed.
Lemma lem8228271 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term630 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2 z) = (term620 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8228269 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1 z) (@lem8228270 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1)). Qed.
Lemma lem8228272 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term632 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term622 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : A => @lem8228271 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1)). Qed.
Lemma lem8228273 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8228274 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term633 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term623 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8228273 A) (@lem8228272 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228275 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term634 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term624 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8228274 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8228276 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8228277 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term626 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term625 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228276 P) (@lem8228275 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228279 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term635 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term636 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228278) (@lem8228277 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228280 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term629 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term622 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (eq_refl (term629 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2)). Qed.
Lemma lem8228281 {A P : Type'} (z : P -> A) (p2 : P) : (z p2) = (z p2).
Proof. exact (eq_refl (z p2)). Qed.
Lemma lem8228282 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) (z : P -> A) (p2 : P) : (term637 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2) = (term638 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2).
Proof. exact (MK_COMB (@lem8228280 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8228281 A P z p2)). Qed.
Lemma lem8228283 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term638 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2) = (term639 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term638 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2)). Qed.
Lemma lem8228284 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term637 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2) = (term639 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8228282 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z p2) (@lem8228283 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1)). Qed.
Lemma lem8228285 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term640 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) = (term641 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8228284 _144947 _144956 _144962 A B P p l lt2 s z f h g p2 p1)). Qed.
Lemma lem8228286 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8228287 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term642 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) = (term643 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (MK_COMB (@lem8228286 P) (@lem8228285 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228288 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term644 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term645 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> A => @lem8228287 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228289 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8228290 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term627 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term646 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228289 A P) (@lem8228288 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228291 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : ((term626 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term627 _144947 _144956 _144962 A B P p l lt2 s f h g p1)) = ((term625 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term646 _144947 _144956 _144962 A B P p l lt2 s f h g p1)).
Proof. exact (MK_COMB (@lem8228279 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8228290 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228292 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term625 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term646 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (EQ_MP (@lem8228291 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8228266 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228293 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term578 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term646 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (TRANS (@lem8228262 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8228292 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228294 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term579 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term647 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8228293 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228295 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8228296 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term580 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term648 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228295 _144962) (@lem8228294 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228298 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8228299 {_144962 A P : Type'} (P' : type1377 _144962 A P) : (term649 _144962 A P P') = (term650 _144962 A P P').
Proof. exact (@lem8228298 _144962 (P -> A) P'). Qed.
Lemma lem8228300 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term651 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term652 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (@lem8228299 _144962 A P (term653 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228301 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term654 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term645 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (eq_refl (term654 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228302 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8228303 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) (z : P -> A) : (term655 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) = (term656 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z).
Proof. exact (MK_COMB (@lem8228301 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8228302 A P z)). Qed.
Lemma lem8228304 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term656 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) = (term643 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (eq_refl (term656 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z)). Qed.
Lemma lem8228305 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term655 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) = (term643 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (TRANS (@lem8228303 _144947 _144956 _144962 A B P p l lt2 s f h g p1 z) (@lem8228304 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228306 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term657 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term645 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> A => @lem8228305 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228307 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8228308 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term658 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term646 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8228307 A P) (@lem8228306 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228309 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term659 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term647 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8228308 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228310 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8228311 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term651 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term648 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228310 _144962) (@lem8228309 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228313 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term660 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term661 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228312) (@lem8228311 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228314 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term654 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term645 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (eq_refl (term654 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8228315 {_144962 A P : Type'} (z : type1419 _144962 A P) (p1 : _144962) : (z p1) = (z p1).
Proof. exact (eq_refl (z p1)). Qed.
Lemma lem8228316 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (z : type1419 _144962 A P) (p1 : _144962) : (term662 _144947 _144956 _144962 A B P p l lt2 s f h g z p1) = (term663 _144947 _144956 _144962 A B P p l lt2 s f h g z p1).
Proof. exact (MK_COMB (@lem8228314 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8228315 _144962 A P z p1)). Qed.
Lemma lem8228317 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term663 _144947 _144956 _144962 A B P p l lt2 s f h g z p1) = (term664 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (eq_refl (term663 _144947 _144956 _144962 A B P p l lt2 s f h g z p1)). Qed.
Lemma lem8228318 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term662 _144947 _144956 _144962 A B P p l lt2 s f h g z p1) = (term664 _144947 _144956 _144962 A B P p l lt2 s z f h g p1).
Proof. exact (TRANS (@lem8228316 _144947 _144956 _144962 A B P p l lt2 s f h g z p1) (@lem8228317 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228319 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term665 _144947 _144956 _144962 A B P p l lt2 s f h g z) = (term666 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (fun_ext (fun p1 : _144962 => @lem8228318 _144947 _144956 _144962 A B P p l lt2 s z f h g p1)). Qed.
Lemma lem8228320 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8228321 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term667 _144947 _144956 _144962 A B P p l lt2 s f h g z) = (term668 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (MK_COMB (@lem8228320 _144962) (@lem8228319 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228322 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term669 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term670 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun z : type1419 _144962 A P => @lem8228321 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228323 {_144962 A P : Type'} : (@ex (_144962 -> P -> A)) = (@ex (_144962 -> P -> A)).
Proof. exact (eq_refl (@ex (_144962 -> P -> A))). Qed.
Lemma lem8228324 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term652 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term671 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228323 _144962 A P) (@lem8228322 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228325 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : ((term651 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term652 _144947 _144956 _144962 A B P p l lt2 s f h g)) = ((term648 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term671 _144947 _144956 _144962 A B P p l lt2 s f h g)).
Proof. exact (MK_COMB (@lem8228313 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8228324 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228326 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term648 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term671 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (EQ_MP (@lem8228325 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8228300 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228327 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term580 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term671 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (TRANS (@lem8228296 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8228326 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228328 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term581 _144947 _144956 _144962 A B P p l lt2 s f h) = (term672 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8228327 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228329 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228330 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term582 _144947 _144956 _144962 A B P p l lt2 s f h) = (term673 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228329 A B) (@lem8228328 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228332 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8228333 {_144962 A B P : Type'} (P' : type807 _144962 A B P) : (term674 _144962 A B P P') = (term675 _144962 A B P P').
Proof. exact (@lem8228332 (A -> B) (type1419 _144962 A P) P'). Qed.
Lemma lem8228334 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term676 _144947 _144956 _144962 A B P p l lt2 s f h) = (term677 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (@lem8228333 _144962 A B P (term678 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228335 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term679 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term670 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (eq_refl (term679 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228336 {_144962 A P : Type'} (z : type1419 _144962 A P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8228337 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (z : type1419 _144962 A P) : (term680 _144947 _144956 _144962 A B P p l lt2 s f h g z) = (term681 _144947 _144956 _144962 A B P p l lt2 s f h g z).
Proof. exact (MK_COMB (@lem8228335 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8228336 _144962 A P z)). Qed.
Lemma lem8228338 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term681 _144947 _144956 _144962 A B P p l lt2 s f h g z) = (term668 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (eq_refl (term681 _144947 _144956 _144962 A B P p l lt2 s f h g z)). Qed.
Lemma lem8228339 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type1419 _144962 A P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term680 _144947 _144956 _144962 A B P p l lt2 s f h g z) = (term668 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (TRANS (@lem8228337 _144947 _144956 _144962 A B P p l lt2 s f h g z) (@lem8228338 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228340 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term682 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term670 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (fun_ext (fun z : type1419 _144962 A P => @lem8228339 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228341 {_144962 A P : Type'} : (@ex (_144962 -> P -> A)) = (@ex (_144962 -> P -> A)).
Proof. exact (eq_refl (@ex (_144962 -> P -> A))). Qed.
Lemma lem8228342 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term683 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term671 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (MK_COMB (@lem8228341 _144962 A P) (@lem8228340 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228343 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term684 _144947 _144956 _144962 A B P p l lt2 s f h) = (term672 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8228342 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228344 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228345 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term676 _144947 _144956 _144962 A B P p l lt2 s f h) = (term673 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228344 A B) (@lem8228343 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228347 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term685 _144947 _144956 _144962 A B P p l lt2 s f h) = (term686 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228346) (@lem8228345 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228348 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term679 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term670 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (eq_refl (term679 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8228349 {_144962 A B P : Type'} (z : type811 _144962 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8228350 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (z : type811 _144962 A B P) (g : A -> B) : (term687 _144947 _144956 _144962 A B P p l lt2 s f h z g) = (term688 _144947 _144956 _144962 A B P p l lt2 s f h z g).
Proof. exact (MK_COMB (@lem8228348 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8228349 _144962 A B P z g)). Qed.
Lemma lem8228351 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term688 _144947 _144956 _144962 A B P p l lt2 s f h z g) = (term689 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (eq_refl (term688 _144947 _144956 _144962 A B P p l lt2 s f h z g)). Qed.
Lemma lem8228352 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term687 _144947 _144956 _144962 A B P p l lt2 s f h z g) = (term689 _144947 _144956 _144962 A B P p l lt2 s z f h g).
Proof. exact (TRANS (@lem8228350 _144947 _144956 _144962 A B P p l lt2 s f h z g) (@lem8228351 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228353 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term690 _144947 _144956 _144962 A B P p l lt2 s f h z) = (term691 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (fun_ext (fun g : A -> B => @lem8228352 _144947 _144956 _144962 A B P p l lt2 s z f h g)). Qed.
Lemma lem8228354 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228355 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term692 _144947 _144956 _144962 A B P p l lt2 s f h z) = (term693 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (MK_COMB (@lem8228354 A B) (@lem8228353 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228356 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term694 _144947 _144956 _144962 A B P p l lt2 s f h) = (term695 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun z : type811 _144962 A B P => @lem8228355 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228357 {_144962 A B P : Type'} : (@ex ((A -> B) -> _144962 -> P -> A)) = (@ex ((A -> B) -> _144962 -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> _144962 -> P -> A))). Qed.
Lemma lem8228358 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term677 _144947 _144956 _144962 A B P p l lt2 s f h) = (term696 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228357 _144962 A B P) (@lem8228356 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228359 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : ((term676 _144947 _144956 _144962 A B P p l lt2 s f h) = (term677 _144947 _144956 _144962 A B P p l lt2 s f h)) = ((term673 _144947 _144956 _144962 A B P p l lt2 s f h) = (term696 _144947 _144956 _144962 A B P p l lt2 s f h)).
Proof. exact (MK_COMB (@lem8228347 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8228358 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228360 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term673 _144947 _144956 _144962 A B P p l lt2 s f h) = (term696 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (EQ_MP (@lem8228359 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8228334 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228361 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term582 _144947 _144956 _144962 A B P p l lt2 s f h) = (term696 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (TRANS (@lem8228330 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8228360 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228362 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term583 _144947 _144956 _144962 A B P p l lt2 s h) = (term697 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun f : A -> B => @lem8228361 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228363 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228364 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term584 _144947 _144956 _144962 A B P p l lt2 s h) = (term698 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8228363 A B) (@lem8228362 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228366 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8228367 {_144962 A B P : Type'} (P' : type806 _144962 A B P) : (term699 _144962 A B P P') = (term700 _144962 A B P P').
Proof. exact (@lem8228366 (A -> B) (type811 _144962 A B P) P'). Qed.
Lemma lem8228368 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term701 _144947 _144956 _144962 A B P p l lt2 s h) = (term702 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (@lem8228367 _144962 A B P (term703 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228369 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term704 _144947 _144956 _144962 A B P p l lt2 s h f) = (term695 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (eq_refl (term704 _144947 _144956 _144962 A B P p l lt2 s h f)). Qed.
Lemma lem8228370 {_144962 A B P : Type'} (z : type811 _144962 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8228371 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (z : type811 _144962 A B P) : (term705 _144947 _144956 _144962 A B P p l lt2 s h f z) = (term706 _144947 _144956 _144962 A B P p l lt2 s f h z).
Proof. exact (MK_COMB (@lem8228369 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8228370 _144962 A B P z)). Qed.
Lemma lem8228372 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term706 _144947 _144956 _144962 A B P p l lt2 s f h z) = (term693 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (eq_refl (term706 _144947 _144956 _144962 A B P p l lt2 s f h z)). Qed.
Lemma lem8228373 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type811 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term705 _144947 _144956 _144962 A B P p l lt2 s h f z) = (term693 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (TRANS (@lem8228371 _144947 _144956 _144962 A B P p l lt2 s f h z) (@lem8228372 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228374 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term707 _144947 _144956 _144962 A B P p l lt2 s h f) = (term695 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (fun_ext (fun z : type811 _144962 A B P => @lem8228373 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228375 {_144962 A B P : Type'} : (@ex ((A -> B) -> _144962 -> P -> A)) = (@ex ((A -> B) -> _144962 -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> _144962 -> P -> A))). Qed.
Lemma lem8228376 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term708 _144947 _144956 _144962 A B P p l lt2 s h f) = (term696 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (MK_COMB (@lem8228375 _144962 A B P) (@lem8228374 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228377 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term709 _144947 _144956 _144962 A B P p l lt2 s h) = (term697 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun f : A -> B => @lem8228376 _144947 _144956 _144962 A B P p l lt2 s f h)). Qed.
Lemma lem8228378 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228379 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term701 _144947 _144956 _144962 A B P p l lt2 s h) = (term698 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8228378 A B) (@lem8228377 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8228381 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term710 _144947 _144956 _144962 A B P p l lt2 s h) = (term711 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8228380) (@lem8228379 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228382 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term704 _144947 _144956 _144962 A B P p l lt2 s h f) = (term695 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (eq_refl (term704 _144947 _144956 _144962 A B P p l lt2 s h f)). Qed.
Lemma lem8228383 {_144962 A B P : Type'} (z : type809 _144962 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8228384 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (z : type809 _144962 A B P) (f : A -> B) : (term712 _144947 _144956 _144962 A B P p l lt2 s h z f) = (term713 _144947 _144956 _144962 A B P p l lt2 s h z f).
Proof. exact (MK_COMB (@lem8228382 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8228383 _144962 A B P z f)). Qed.
Lemma lem8228385 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type809 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term713 _144947 _144956 _144962 A B P p l lt2 s h z f) = (term714 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (eq_refl (term713 _144947 _144956 _144962 A B P p l lt2 s h z f)). Qed.
Lemma lem8228386 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type809 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term712 _144947 _144956 _144962 A B P p l lt2 s h z f) = (term714 _144947 _144956 _144962 A B P p l lt2 s z f h).
Proof. exact (TRANS (@lem8228384 _144947 _144956 _144962 A B P p l lt2 s h z f) (@lem8228385 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228387 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type809 _144962 A B P) (h : type889 _144956 _144962 A B P) : (term715 _144947 _144956 _144962 A B P p l lt2 s h z) = (term716 _144947 _144956 _144962 A B P p l lt2 s z h).
Proof. exact (fun_ext (fun f : A -> B => @lem8228386 _144947 _144956 _144962 A B P p l lt2 s z f h)). Qed.
Lemma lem8228388 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8228389 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type809 _144962 A B P) (h : type889 _144956 _144962 A B P) : (term717 _144947 _144956 _144962 A B P p l lt2 s h z) = (term718 _144947 _144956 _144962 A B P p l lt2 s z h).
Proof. exact (MK_COMB (@lem8228388 A B) (@lem8228387 _144947 _144956 _144962 A B P p l lt2 s z h)). Qed.
Lemma lem8228390 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term719 _144947 _144956 _144962 A B P p l lt2 s h) = (term720 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (fun_ext (fun z : type809 _144962 A B P => @lem8228389 _144947 _144956 _144962 A B P p l lt2 s z h)). Qed.
Lemma lem8228391 {_144962 A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> _144962 -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> _144962 -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> _144962 -> P -> A))). Qed.
Lemma lem8228392 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term702 _144947 _144956 _144962 A B P p l lt2 s h) = (term721 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (MK_COMB (@lem8228391 _144962 A B P) (@lem8228390 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228393 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : ((term701 _144947 _144956 _144962 A B P p l lt2 s h) = (term702 _144947 _144956 _144962 A B P p l lt2 s h)) = ((term698 _144947 _144956 _144962 A B P p l lt2 s h) = (term721 _144947 _144956 _144962 A B P p l lt2 s h)).
Proof. exact (MK_COMB (@lem8228381 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8228392 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228394 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term698 _144947 _144956 _144962 A B P p l lt2 s h) = (term721 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (EQ_MP (@lem8228393 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8228368 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228396 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term584 _144947 _144956 _144962 A B P p l lt2 s h) = (term721 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (TRANS (@lem8228364 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8228394 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228397 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : (term286 _144947 _144956 _144962 A B P p l lt2 s h) = (term721 _144947 _144956 _144962 A B P p l lt2 s h).
Proof. exact (TRANS (@lem8228078 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8228396 _144947 _144956 _144962 A B P p l lt2 s h)). Qed.
Lemma lem8228398 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term721 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (EQ_MP (@lem8228397 _144947 _144956 _144962 A B P p l lt2 s h) (@lem8227685 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8228404 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : p f a.
Proof. exact (h1). Qed.
Lemma lem8228410 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : p g a.
Proof. exact (h1). Qed.
Lemma lem8228417 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term722 _144947 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term214 _144947 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8228418 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term723 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8228417 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8228419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8228472 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term724 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8228419 A) (@lem8228418 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8228473 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term724 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8228472 _144947 A B P lt2 s a f g) (@lem8227688 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8228479 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term352 _144962 A B P f l g a) : term352 _144962 A B P f l g a.
Proof. exact (h1). Qed.
Lemma lem8228481 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term558 _144947 _144962 A B P p lt2 s z' l.
Proof. exact (h1). Qed.
Lemma lem8228488 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228489 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8228488 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8228490 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8228489 A B P p f). Qed.
Lemma lem8228491 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228492 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8228490 A B P p f) (@lem8228491 P a)). Qed.
Lemma lem8228494 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228495 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8228494 P Prop f x). Qed.
Lemma lem8228496 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term725 A B P p f a).
Proof. exact (@lem8228495 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8228498 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term725 A B P p f a).
Proof. exact (TRANS (@lem8228492 A B P p f a) (@lem8228496 A B P p f a)). Qed.
Lemma lem8228506 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228507 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8228506 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8228508 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8228507 A B P p g). Qed.
Lemma lem8228509 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228510 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8228508 A B P p g) (@lem8228509 P a)). Qed.
Lemma lem8228512 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228513 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8228512 P Prop f x). Qed.
Lemma lem8228514 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term725 A B P p g a).
Proof. exact (@lem8228513 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8228516 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term725 A B P p g a).
Proof. exact (TRANS (@lem8228510 A B P p g a) (@lem8228514 A B P p g a)). Qed.
Lemma lem8228518 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8228523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8228523 A B f x). Qed.
Lemma lem8228526 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8228524 A B f z). Qed.
Lemma lem8228531 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8228531 A B f x). Qed.
Lemma lem8228534 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8228532 A B g z). Qed.
Lemma lem8228535 {A B : Type'} (f : A -> B) (z : A) : (term726 A B f z) = (term727 A B f z).
Proof. exact (MK_COMB (@lem8228518 B) (@lem8228526 A B f z)). Qed.
Lemma lem8228536 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8228535 A B f z) (@lem8228534 A B g z)). Qed.
Lemma lem8228537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8228544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228545 {_144947 P : Type'} (f : P -> _144947) (x : P) : (f x) = (@I (P -> _144947) f x).
Proof. exact (@lem8228544 P _144947 f x). Qed.
Lemma lem8228547 {_144947 P : Type'} (s : P -> _144947) (a : P) : (s a) = (@I (P -> _144947) s a).
Proof. exact (@lem8228545 _144947 P s a). Qed.
Lemma lem8228548 {_144947 A : Type'} (lt2 : type1470 _144947 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8228549 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term214 _144947 A P lt2 z s a) = (term728 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8228548 _144947 A lt2 z) (@lem8228547 _144947 P s a)). Qed.
Lemma lem8228551 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228552 {_144947 A : Type'} (f : type1470 _144947 A) (x : A) : (f x) = (@I (A -> _144947 -> Prop) f x).
Proof. exact (@lem8228551 A (_144947 -> Prop) f x). Qed.
Lemma lem8228553 {_144947 A : Type'} (lt2 : type1470 _144947 A) (z : A) : (lt2 z) = (@I (A -> _144947 -> Prop) lt2 z).
Proof. exact (@lem8228552 _144947 A lt2 z). Qed.
Lemma lem8228554 {_144947 P : Type'} (s : P -> _144947) (a : P) : (@I (P -> _144947) s a) = (@I (P -> _144947) s a).
Proof. exact (eq_refl (@I (P -> _144947) s a)). Qed.
Lemma lem8228555 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term728 _144947 A P lt2 z s a) = (term729 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8228553 _144947 A lt2 z) (@lem8228554 _144947 P s a)). Qed.
Lemma lem8228557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228558 {_144947 : Type'} (f : _144947 -> Prop) (x : _144947) : (f x) = (@I (_144947 -> Prop) f x).
Proof. exact (@lem8228557 _144947 Prop f x). Qed.
Lemma lem8228559 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term729 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (@lem8228558 _144947 (@I (A -> _144947 -> Prop) lt2 z) (@I (P -> _144947) s a)). Qed.
Lemma lem8228560 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term728 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (TRANS (@lem8228555 _144947 A P lt2 z s a) (@lem8228559 _144947 A P lt2 z s a)). Qed.
Lemma lem8228561 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term214 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (TRANS (@lem8228549 _144947 A P lt2 z s a) (@lem8228560 _144947 A P lt2 z s a)). Qed.
Lemma lem8228562 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term731 _144947 A P lt2 z s a) = (term732 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8228537) (@lem8228561 _144947 A P lt2 z s a)). Qed.
Lemma lem8228563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8228564 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term733 _144947 A P lt2 z s a) = (term734 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8228563) (@lem8228562 _144947 A P lt2 z s a)). Qed.
Lemma lem8228565 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term722 _144947 A B P lt2 s a f g z) = (term735 _144947 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8228564 _144947 A P lt2 z s a) (@lem8228536 A B f g z)). Qed.
Lemma lem8228566 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term723 _144947 A B P lt2 s a f g) = (term736 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8228565 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8228567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8228568 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term724 _144947 A B P lt2 s a f g) = (term737 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8228567 A) (@lem8228566 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8228569 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term737 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8228568 _144947 A B P lt2 s a f g) (@lem8228473 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8228570 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8228571 {_144962 : Type'} : (@eq (list _144962)) = (@eq (list _144962)).
Proof. exact (eq_refl (@eq (list _144962))). Qed.
Lemma lem8228578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228579 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8228578 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8228580 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) : (l f) = (@I ((A -> B) -> P -> list _144962) l f).
Proof. exact (@lem8228579 _144962 A B P l f). Qed.
Lemma lem8228581 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228582 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (@I ((A -> B) -> P -> list _144962) l f a).
Proof. exact (MK_COMB (@lem8228580 _144962 A B P l f) (@lem8228581 P a)). Qed.
Lemma lem8228584 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228585 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8228584 P (list _144962) f x). Qed.
Lemma lem8228586 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l f a) = (term738 _144962 A B P l f a).
Proof. exact (@lem8228585 _144962 P (@I ((A -> B) -> P -> list _144962) l f) a). Qed.
Lemma lem8228588 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (term738 _144962 A B P l f a).
Proof. exact (TRANS (@lem8228582 _144962 A B P l f a) (@lem8228586 _144962 A B P l f a)). Qed.
Lemma lem8228595 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228596 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8228595 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8228597 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) : (l g) = (@I ((A -> B) -> P -> list _144962) l g).
Proof. exact (@lem8228596 _144962 A B P l g). Qed.
Lemma lem8228598 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228599 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (@I ((A -> B) -> P -> list _144962) l g a).
Proof. exact (MK_COMB (@lem8228597 _144962 A B P l g) (@lem8228598 P a)). Qed.
Lemma lem8228601 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228602 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8228601 P (list _144962) f x). Qed.
Lemma lem8228603 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l g a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8228602 _144962 P (@I ((A -> B) -> P -> list _144962) l g) a). Qed.
Lemma lem8228605 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (term738 _144962 A B P l g a).
Proof. exact (TRANS (@lem8228599 _144962 A B P l g a) (@lem8228603 _144962 A B P l g a)). Qed.
Lemma lem8228606 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term739 _144962 A B P l f a) = (term740 _144962 A B P l f a).
Proof. exact (MK_COMB (@lem8228571 _144962) (@lem8228588 _144962 A B P l f a)). Qed.
Lemma lem8228607 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (MK_COMB (@lem8228606 _144962 A B P l f a) (@lem8228605 _144962 A B P l g a)). Qed.
Lemma lem8228608 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term352 _144962 A B P f l g a) = (term741 _144962 A B P f l g a).
Proof. exact (MK_COMB (@lem8228570) (@lem8228607 _144962 A B P f l g a)). Qed.
Lemma lem8228951 {_144962 : Type'} : (@eq (list _144962)) = (@eq (list _144962)).
Proof. exact (eq_refl (@eq (list _144962))). Qed.
Lemma lem8228958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228959 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8228958 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8228960 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) : (l f) = (@I ((A -> B) -> P -> list _144962) l f).
Proof. exact (@lem8228959 _144962 A B P l f). Qed.
Lemma lem8228961 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228962 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (@I ((A -> B) -> P -> list _144962) l f a).
Proof. exact (MK_COMB (@lem8228960 _144962 A B P l f) (@lem8228961 P a)). Qed.
Lemma lem8228964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228965 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8228964 P (list _144962) f x). Qed.
Lemma lem8228966 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l f a) = (term738 _144962 A B P l f a).
Proof. exact (@lem8228965 _144962 P (@I ((A -> B) -> P -> list _144962) l f) a). Qed.
Lemma lem8228968 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (term738 _144962 A B P l f a).
Proof. exact (TRANS (@lem8228962 _144962 A B P l f a) (@lem8228966 _144962 A B P l f a)). Qed.
Lemma lem8228975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228976 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8228975 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8228977 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) : (l g) = (@I ((A -> B) -> P -> list _144962) l g).
Proof. exact (@lem8228976 _144962 A B P l g). Qed.
Lemma lem8228978 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8228979 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (@I ((A -> B) -> P -> list _144962) l g a).
Proof. exact (MK_COMB (@lem8228977 _144962 A B P l g) (@lem8228978 P a)). Qed.
Lemma lem8228981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8228982 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8228981 P (list _144962) f x). Qed.
Lemma lem8228983 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l g a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8228982 _144962 P (@I ((A -> B) -> P -> list _144962) l g) a). Qed.
Lemma lem8228985 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (term738 _144962 A B P l g a).
Proof. exact (TRANS (@lem8228979 _144962 A B P l g a) (@lem8228983 _144962 A B P l g a)). Qed.
Lemma lem8228986 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term739 _144962 A B P l f a) = (term740 _144962 A B P l f a).
Proof. exact (MK_COMB (@lem8228951 _144962) (@lem8228968 _144962 A B P l f a)). Qed.
Lemma lem8228987 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (MK_COMB (@lem8228986 _144962 A B P l f a) (@lem8228985 _144962 A B P l g a)). Qed.
Lemma lem8228988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8228989 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8228990 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8228999 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229000 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8228999 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8229001 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8229000 A B P z' f). Qed.
Lemma lem8229002 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8229003 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8229001 A B P z' f) (@lem8229002 A B g)). Qed.
Lemma lem8229005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229006 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8229005 (A -> B) (P -> A) f x). Qed.
Lemma lem8229007 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term742 A B P z' f g).
Proof. exact (@lem8229006 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8229008 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term742 A B P z' f g).
Proof. exact (TRANS (@lem8229003 A B P z' f g) (@lem8229007 A B P z' f g)). Qed.
Lemma lem8229009 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8229010 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term743 A B P z' f g a).
Proof. exact (MK_COMB (@lem8229008 A B P z' f g) (@lem8229009 P a)). Qed.
Lemma lem8229012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229013 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8229012 P A f x). Qed.
Lemma lem8229014 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z' f g a) = (term744 A B P z' f g a).
Proof. exact (@lem8229013 A P (term742 A B P z' f g) a). Qed.
Lemma lem8229016 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term744 A B P z' f g a).
Proof. exact (TRANS (@lem8229010 A B P z' f g a) (@lem8229014 A B P z' f g a)). Qed.
Lemma lem8229017 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term745 A B P z' f g a) = (term746 A B P z' f g a).
Proof. exact (MK_COMB (@lem8228990 A B f) (@lem8229016 A B P z' f g a)). Qed.
Lemma lem8229019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8229019 A B f x). Qed.
Lemma lem8229021 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term746 A B P z' f g a) = (term747 A B P z' f g a).
Proof. exact (@lem8229020 A B f (term744 A B P z' f g a)). Qed.
Lemma lem8229022 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term745 A B P z' f g a) = (term747 A B P z' f g a).
Proof. exact (TRANS (@lem8229017 A B P z' f g a) (@lem8229021 A B P z' f g a)). Qed.
Lemma lem8229023 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8229032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229033 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8229032 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8229034 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8229033 A B P z' f). Qed.
Lemma lem8229035 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8229036 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8229034 A B P z' f) (@lem8229035 A B g)). Qed.
Lemma lem8229038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229039 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8229038 (A -> B) (P -> A) f x). Qed.
Lemma lem8229040 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term742 A B P z' f g).
Proof. exact (@lem8229039 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8229041 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term742 A B P z' f g).
Proof. exact (TRANS (@lem8229036 A B P z' f g) (@lem8229040 A B P z' f g)). Qed.
Lemma lem8229042 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8229043 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term743 A B P z' f g a).
Proof. exact (MK_COMB (@lem8229041 A B P z' f g) (@lem8229042 P a)). Qed.
Lemma lem8229045 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229046 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8229045 P A f x). Qed.
Lemma lem8229047 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z' f g a) = (term744 A B P z' f g a).
Proof. exact (@lem8229046 A P (term742 A B P z' f g) a). Qed.
Lemma lem8229049 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term744 A B P z' f g a).
Proof. exact (TRANS (@lem8229043 A B P z' f g a) (@lem8229047 A B P z' f g a)). Qed.
Lemma lem8229050 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term748 A B P z' f g a) = (term749 A B P z' f g a).
Proof. exact (MK_COMB (@lem8229023 A B g) (@lem8229049 A B P z' f g a)). Qed.
Lemma lem8229052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8229052 A B f x). Qed.
Lemma lem8229054 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term749 A B P z' f g a) = (term750 A B P z' f g a).
Proof. exact (@lem8229053 A B g (term744 A B P z' f g a)). Qed.
Lemma lem8229055 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term748 A B P z' f g a) = (term750 A B P z' f g a).
Proof. exact (TRANS (@lem8229050 A B P z' f g a) (@lem8229054 A B P z' f g a)). Qed.
Lemma lem8229056 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term751 A B P z' f g a) = (term752 A B P z' f g a).
Proof. exact (MK_COMB (@lem8228989 B) (@lem8229022 A B P z' f g a)). Qed.
Lemma lem8229057 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term745 A B P z' f g a) = (term748 A B P z' f g a)) = ((term747 A B P z' f g a) = (term750 A B P z' f g a)).
Proof. exact (MK_COMB (@lem8229056 A B P z' f g a) (@lem8229055 A B P z' f g a)). Qed.
Lemma lem8229058 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term753 A B P z' f g a) = (term754 A B P z' f g a).
Proof. exact (MK_COMB (@lem8228988) (@lem8229057 A B P z' f g a)). Qed.
Lemma lem8229059 {_144947 A : Type'} (lt2 : type1470 _144947 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8229068 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229069 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8229068 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8229070 {A B P : Type'} (z' : type518 A B P) (f : A -> B) : (z' f) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f).
Proof. exact (@lem8229069 A B P z' f). Qed.
Lemma lem8229071 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8229072 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z' f g).
Proof. exact (MK_COMB (@lem8229070 A B P z' f) (@lem8229071 A B g)). Qed.
Lemma lem8229074 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229075 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8229074 (A -> B) (P -> A) f x). Qed.
Lemma lem8229076 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z' f g) = (term742 A B P z' f g).
Proof. exact (@lem8229075 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z' f) g). Qed.
Lemma lem8229077 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) : (z' f g) = (term742 A B P z' f g).
Proof. exact (TRANS (@lem8229072 A B P z' f g) (@lem8229076 A B P z' f g)). Qed.
Lemma lem8229078 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8229079 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term743 A B P z' f g a).
Proof. exact (MK_COMB (@lem8229077 A B P z' f g) (@lem8229078 P a)). Qed.
Lemma lem8229081 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229082 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8229081 P A f x). Qed.
Lemma lem8229083 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z' f g a) = (term744 A B P z' f g a).
Proof. exact (@lem8229082 A P (term742 A B P z' f g) a). Qed.
Lemma lem8229085 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z' f g a) = (term744 A B P z' f g a).
Proof. exact (TRANS (@lem8229079 A B P z' f g a) (@lem8229083 A B P z' f g a)). Qed.
Lemma lem8229090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229091 {_144947 P : Type'} (f : P -> _144947) (x : P) : (f x) = (@I (P -> _144947) f x).
Proof. exact (@lem8229090 P _144947 f x). Qed.
Lemma lem8229093 {_144947 P : Type'} (s : P -> _144947) (a : P) : (s a) = (@I (P -> _144947) s a).
Proof. exact (@lem8229091 _144947 P s a). Qed.
Lemma lem8229094 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term755 _144947 A B P lt2 z' f g a) = (term756 _144947 A B P lt2 z' f g a).
Proof. exact (MK_COMB (@lem8229059 _144947 A lt2) (@lem8229085 A B P z' f g a)). Qed.
Lemma lem8229095 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term757 _144947 A B P lt2 z' f g s a) = (term758 _144947 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8229094 _144947 A B P lt2 z' f g a) (@lem8229093 _144947 P s a)). Qed.
Lemma lem8229097 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229098 {_144947 A : Type'} (f : type1470 _144947 A) (x : A) : (f x) = (@I (A -> _144947 -> Prop) f x).
Proof. exact (@lem8229097 A (_144947 -> Prop) f x). Qed.
Lemma lem8229099 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term756 _144947 A B P lt2 z' f g a) = (term759 _144947 A B P lt2 z' f g a).
Proof. exact (@lem8229098 _144947 A lt2 (term744 A B P z' f g a)). Qed.
Lemma lem8229100 {_144947 P : Type'} (s : P -> _144947) (a : P) : (@I (P -> _144947) s a) = (@I (P -> _144947) s a).
Proof. exact (eq_refl (@I (P -> _144947) s a)). Qed.
Lemma lem8229101 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term758 _144947 A B P lt2 z' f g s a) = (term760 _144947 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8229099 _144947 A B P lt2 z' f g a) (@lem8229100 _144947 P s a)). Qed.
Lemma lem8229103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229104 {_144947 : Type'} (f : _144947 -> Prop) (x : _144947) : (f x) = (@I (_144947 -> Prop) f x).
Proof. exact (@lem8229103 _144947 Prop f x). Qed.
Lemma lem8229105 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term760 _144947 A B P lt2 z' f g s a) = (term761 _144947 A B P lt2 z' f g s a).
Proof. exact (@lem8229104 _144947 (term759 _144947 A B P lt2 z' f g a) (@I (P -> _144947) s a)). Qed.
Lemma lem8229106 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term758 _144947 A B P lt2 z' f g s a) = (term761 _144947 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8229101 _144947 A B P lt2 z' f g s a) (@lem8229105 _144947 A B P lt2 z' f g s a)). Qed.
Lemma lem8229107 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term757 _144947 A B P lt2 z' f g s a) = (term761 _144947 A B P lt2 z' f g s a).
Proof. exact (TRANS (@lem8229095 _144947 A B P lt2 z' f g s a) (@lem8229106 _144947 A B P lt2 z' f g s a)). Qed.
Lemma lem8229108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8229109 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term762 _144947 A B P lt2 z' f g s a) = (term763 _144947 A B P lt2 z' f g s a).
Proof. exact (MK_COMB (@lem8229108) (@lem8229107 _144947 A B P lt2 z' f g s a)). Qed.
Lemma lem8229110 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term764 _144947 A B P lt2 s z' f g a) = (term765 _144947 A B P lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8229109 _144947 A B P lt2 z' f g s a) (@lem8229058 A B P z' f g a)). Qed.
Lemma lem8229111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8229118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229119 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8229118 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8229120 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8229119 A B P p g). Qed.
Lemma lem8229121 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8229122 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8229120 A B P p g) (@lem8229121 P a)). Qed.
Lemma lem8229124 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229125 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8229124 P Prop f x). Qed.
Lemma lem8229126 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term725 A B P p g a).
Proof. exact (@lem8229125 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8229128 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term725 A B P p g a).
Proof. exact (TRANS (@lem8229122 A B P p g a) (@lem8229126 A B P p g a)). Qed.
Lemma lem8229129 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term442 A B P p g a) = (term766 A B P p g a).
Proof. exact (MK_COMB (@lem8229111) (@lem8229128 A B P p g a)). Qed.
Lemma lem8229130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8229131 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term767 A B P p g a).
Proof. exact (MK_COMB (@lem8229130) (@lem8229129 A B P p g a)). Qed.
Lemma lem8229132 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term768 _144947 A B P p lt2 s z' f g a) = (term769 _144947 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8229131 A B P p g a) (@lem8229110 _144947 A B P lt2 s z' f g a)). Qed.
Lemma lem8229133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8229140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229141 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8229140 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8229142 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8229141 A B P p f). Qed.
Lemma lem8229143 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8229144 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8229142 A B P p f) (@lem8229143 P a)). Qed.
Lemma lem8229146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8229147 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8229146 P Prop f x). Qed.
Lemma lem8229148 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term725 A B P p f a).
Proof. exact (@lem8229147 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8229150 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term725 A B P p f a).
Proof. exact (TRANS (@lem8229144 A B P p f a) (@lem8229148 A B P p f a)). Qed.
Lemma lem8229151 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term442 A B P p f a) = (term766 A B P p f a).
Proof. exact (MK_COMB (@lem8229133) (@lem8229150 A B P p f a)). Qed.
Lemma lem8229152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8229153 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term767 A B P p f a).
Proof. exact (MK_COMB (@lem8229152) (@lem8229151 A B P p f a)). Qed.
Lemma lem8229154 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term770 _144947 A B P p lt2 s z' f g a) = (term771 _144947 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8229153 A B P p f a) (@lem8229132 _144947 A B P p lt2 s z' f g a)). Qed.
Lemma lem8229155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8229156 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term772 _144947 A B P p lt2 s z' f g a) = (term773 _144947 A B P p lt2 s z' f g a).
Proof. exact (MK_COMB (@lem8229155) (@lem8229154 _144947 A B P p lt2 s z' f g a)). Qed.
Lemma lem8229157 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term774 _144947 _144962 A B P p lt2 s z' f l g a) = (term775 _144947 _144962 A B P p lt2 s z' f l g a).
Proof. exact (MK_COMB (@lem8229156 _144947 A B P p lt2 s z' f g a) (@lem8228987 _144962 A B P f l g a)). Qed.
Lemma lem8229158 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term776 _144947 _144962 A B P p lt2 s z' f l g) = (term777 _144947 _144962 A B P p lt2 s z' f l g).
Proof. exact (fun_ext (fun a : P => @lem8229157 _144947 _144962 A B P p lt2 s z' f l g a)). Qed.
Lemma lem8229159 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8229160 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term778 _144947 _144962 A B P p lt2 s z' f l g) = (term779 _144947 _144962 A B P p lt2 s z' f l g).
Proof. exact (MK_COMB (@lem8229159 P) (@lem8229158 _144947 _144962 A B P p lt2 s z' f l g)). Qed.
Lemma lem8229161 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term780 _144947 _144962 A B P p lt2 s z' f l) = (term781 _144947 _144962 A B P p lt2 s z' f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8229160 _144947 _144962 A B P p lt2 s z' f l g)). Qed.
Lemma lem8229162 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8229163 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term554 _144947 _144962 A B P p lt2 s z' f l) = (term782 _144947 _144962 A B P p lt2 s z' f l).
Proof. exact (MK_COMB (@lem8229162 A B) (@lem8229161 _144947 _144962 A B P p lt2 s z' f l)). Qed.
Lemma lem8229164 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) : (term556 _144947 _144962 A B P p lt2 s z' l) = (term783 _144947 _144962 A B P p lt2 s z' l).
Proof. exact (fun_ext (fun f : A -> B => @lem8229163 _144947 _144962 A B P p lt2 s z' f l)). Qed.
Lemma lem8229165 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8229166 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) : (term558 _144947 _144962 A B P p lt2 s z' l) = (term784 _144947 _144962 A B P p lt2 s z' l).
Proof. exact (MK_COMB (@lem8229165 A B) (@lem8229164 _144947 _144962 A B P p lt2 s z' l)). Qed.
Lemma lem8229167 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term784 _144947 _144962 A B P p lt2 s z' l.
Proof. exact (EQ_MP (@lem8229166 _144947 _144962 A B P p lt2 s z' l) (@lem8228481 _144947 _144962 A B P p lt2 s z' l h1)). Qed.
Lemma lem8229183 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term735 _144947 A B P lt2 s a f g z) = (term735 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term735 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8229184 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term736 _144947 A B P lt2 s a f g) = (term736 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8229183 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8229185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8229187 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term737 _144947 A B P lt2 s a f g) = (term737 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8229185 A) (@lem8229184 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8229188 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term737 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8229187 _144947 A B P lt2 s a f g) (@lem8228569 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8229262 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (eq_refl ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8229279 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term769 _144947 A B P p lt2 s z' f g a) = (term785 _144947 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term761 _144947 A B P lt2 z' f g s a) (term766 A B P p g a) (term754 A B P z' f g a)). Qed.
Lemma lem8229282 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term767 A B P p f a) = (term767 A B P p f a).
Proof. exact (eq_refl (term767 A B P p f a)). Qed.
Lemma lem8229283 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term771 _144947 A B P p lt2 s z' f g a) = (term786 _144947 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8229282 A B P p f a) (@lem8229279 _144947 A B P lt2 s p z' f g a)). Qed.
Lemma lem8229290 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term786 _144947 A B P lt2 s p z' f g a) = (term787 _144947 A B P lt2 s p z' f g a).
Proof. exact (@lem19490 (term788 _144947 A B P p lt2 z' f g s a) (term766 A B P p f a) (term789 A B P p z' f g a)). Qed.
Lemma lem8229291 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term771 _144947 A B P p lt2 s z' f g a) = (term787 _144947 A B P lt2 s p z' f g a).
Proof. exact (TRANS (@lem8229283 _144947 A B P lt2 s p z' f g a) (@lem8229290 _144947 A B P lt2 s p z' f g a)). Qed.
Lemma lem8229292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8229293 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term773 _144947 A B P p lt2 s z' f g a) = (term790 _144947 A B P lt2 s p z' f g a).
Proof. exact (MK_COMB (@lem8229292) (@lem8229291 _144947 A B P lt2 s p z' f g a)). Qed.
Lemma lem8229294 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term775 _144947 _144962 A B P p lt2 s z' f l g a) = (term791 _144947 _144962 A B P lt2 s p z' f l g a).
Proof. exact (MK_COMB (@lem8229293 _144947 A B P lt2 s p z' f g a) (@lem8229262 _144962 A B P f l g a)). Qed.
Lemma lem8229301 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term791 _144947 _144962 A B P lt2 s p z' f l g a) = (term792 _144947 _144962 A B P lt2 s p z' f l g a).
Proof. exact (@lem19699 (term793 _144947 A B P p lt2 z' f g s a) (term794 A B P p z' f g a) ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8229302 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term775 _144947 _144962 A B P p lt2 s z' f l g a) = (term792 _144947 _144962 A B P lt2 s p z' f l g a).
Proof. exact (TRANS (@lem8229294 _144947 _144962 A B P lt2 s p z' f l g a) (@lem8229301 _144947 _144962 A B P lt2 s p z' f l g a)). Qed.
Lemma lem8229303 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term777 _144947 _144962 A B P p lt2 s z' f l g) = (term795 _144947 _144962 A B P lt2 s p z' f l g).
Proof. exact (fun_ext (fun a : P => @lem8229302 _144947 _144962 A B P lt2 s p z' f l g a)). Qed.
Lemma lem8229304 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8229305 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term779 _144947 _144962 A B P p lt2 s z' f l g) = (term796 _144947 _144962 A B P lt2 s p z' f l g).
Proof. exact (MK_COMB (@lem8229304 P) (@lem8229303 _144947 _144962 A B P lt2 s p z' f l g)). Qed.
Lemma lem8229306 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term781 _144947 _144962 A B P p lt2 s z' f l) = (term797 _144947 _144962 A B P lt2 s p z' f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8229305 _144947 _144962 A B P lt2 s p z' f l g)). Qed.
Lemma lem8229307 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8229308 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term782 _144947 _144962 A B P p lt2 s z' f l) = (term798 _144947 _144962 A B P lt2 s p z' f l).
Proof. exact (MK_COMB (@lem8229307 A B) (@lem8229306 _144947 _144962 A B P lt2 s p z' f l)). Qed.
Lemma lem8229309 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (l : type815 _144962 A B P) : (term783 _144947 _144962 A B P p lt2 s z' l) = (term799 _144947 _144962 A B P lt2 s p z' l).
Proof. exact (fun_ext (fun f : A -> B => @lem8229308 _144947 _144962 A B P lt2 s p z' f l)). Qed.
Lemma lem8229310 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8229312 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (l : type815 _144962 A B P) : (term784 _144947 _144962 A B P p lt2 s z' l) = (term800 _144947 _144962 A B P lt2 s p z' l).
Proof. exact (MK_COMB (@lem8229310 A B) (@lem8229309 _144947 _144962 A B P lt2 s p z' l)). Qed.
Lemma lem8229313 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term800 _144947 _144962 A B P lt2 s p z' l.
Proof. exact (EQ_MP (@lem8229312 _144947 _144962 A B P lt2 s p z' l) (@lem8229167 _144947 _144962 A B P p lt2 s z' l h1)). Qed.
Lemma lem8229314 {_144947 A B P : Type'} (_109465 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term801 _144947 A B P lt2 s a f g _109465.
Proof. exact (@lem8229188 _144947 A B P lt2 s a f g h1 _109465). Qed.
Lemma lem8229315 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109465 : A) : (term801 _144947 A B P lt2 s a f g _109465) = (term735 _144947 A B P lt2 s a f g _109465).
Proof. exact (eq_refl (term801 _144947 A B P lt2 s a f g _109465)). Qed.
Lemma lem8229329 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term802 _144947 _144962 A B P lt2 s p z' l _109470.
Proof. exact (@lem8229313 _144947 _144962 A B P p lt2 s z' l h1 _109470). Qed.
Lemma lem8229330 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) : (term802 _144947 _144962 A B P lt2 s p z' l _109470) = (term798 _144947 _144962 A B P lt2 s p z' _109470 l).
Proof. exact (eq_refl (term802 _144947 _144962 A B P lt2 s p z' l _109470)). Qed.
Lemma lem8229331 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term798 _144947 _144962 A B P lt2 s p z' _109470 l.
Proof. exact (EQ_MP (@lem8229330 _144947 _144962 A B P lt2 s p z' _109470 l) (@lem8229329 _144947 _144962 A B P _109470 p lt2 s z' l h1)). Qed.
Lemma lem8229332 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term803 _144947 _144962 A B P lt2 s p z' _109470 l _109471.
Proof. exact (@lem8229331 _144947 _144962 A B P _109470 p lt2 s z' l h1 _109471). Qed.
Lemma lem8229333 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) : (term803 _144947 _144962 A B P lt2 s p z' _109470 l _109471) = (term796 _144947 _144962 A B P lt2 s p z' _109470 l _109471).
Proof. exact (eq_refl (term803 _144947 _144962 A B P lt2 s p z' _109470 l _109471)). Qed.
Lemma lem8229334 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term796 _144947 _144962 A B P lt2 s p z' _109470 l _109471.
Proof. exact (EQ_MP (@lem8229333 _144947 _144962 A B P lt2 s p z' _109470 l _109471) (@lem8229332 _144947 _144962 A B P _109470 _109471 p lt2 s z' l h1)). Qed.
Lemma lem8229335 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term804 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472.
Proof. exact (@lem8229334 _144947 _144962 A B P _109470 _109471 p lt2 s z' l h1 _109472). Qed.
Lemma lem8229336 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term804 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472) = (term792 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472).
Proof. exact (eq_refl (term804 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472)). Qed.
Lemma lem8229337 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term792 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472.
Proof. exact (EQ_MP (@lem8229336 _144947 _144962 A B P lt2 s p z' _109470 l _109471 _109472) (@lem8229335 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8229338 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term805 _144962 A B P p z' _109470 l _109471 _109472.
Proof. exact (proj2 (@lem8229337 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8229339 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term806 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472.
Proof. exact (proj1 (@lem8229337 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8229351 {_144947 A B P : Type'} (_109465 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term735 _144947 A B P lt2 s a f g _109465.
Proof. exact (EQ_MP (@lem8229315 _144947 A B P lt2 s a f g _109465) (@lem8229314 _144947 A B P _109465 lt2 s a f g h1)). Qed.
Lemma lem8229353 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term352 _144962 A B P f l g a) : term741 _144962 A B P f l g a.
Proof. exact (EQ_MP (@lem8228608 _144962 A B P f l g a) (@lem8228479 _144962 A B P f l g a h1)). Qed.
Lemma lem8229357 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term806 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term807 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472).
Proof. exact (@lem8225781 (term766 A B P p _109470 _109472) (term788 _144947 A B P p lt2 z' _109470 _109471 s _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8229364 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term808 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term809 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472).
Proof. exact (@lem8225781 (term766 A B P p _109471 _109472) (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8229365 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8229368 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term807 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8229365 A B P p _109470 _109472) (@lem8229364 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472)). Qed.
Lemma lem8229370 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term806 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472).
Proof. exact (TRANS (@lem8229357 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) (@lem8229368 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472)). Qed.
Lemma lem8229371 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472.
Proof. exact (EQ_MP (@lem8229370 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) (@lem8229339 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8229375 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term805 _144962 A B P p z' _109470 l _109471 _109472) = (term811 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (@lem8225781 (term766 A B P p _109470 _109472) (term789 A B P p z' _109470 _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8229382 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term812 _144962 A B P p z' _109470 l _109471 _109472) = (term813 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (@lem8225781 (term766 A B P p _109471 _109472) (term754 A B P z' _109470 _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8229383 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8229386 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term811 _144962 A B P p z' _109470 l _109471 _109472) = (term814 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8229383 A B P p _109470 _109472) (@lem8229382 _144962 A B P p z' _109470 l _109471 _109472)). Qed.
Lemma lem8229388 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term805 _144962 A B P p z' _109470 l _109471 _109472) = (term814 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (TRANS (@lem8229375 _144962 A B P p z' _109470 l _109471 _109472) (@lem8229386 _144962 A B P p z' _109470 l _109471 _109472)). Qed.
Lemma lem8229389 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term814 _144962 A B P p z' _109470 l _109471 _109472.
Proof. exact (EQ_MP (@lem8229388 _144962 A B P p z' _109470 l _109471 _109472) (@lem8229338 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8229800 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8228498 A B P p f a) (@lem8228404 A B P p f a h1)). Qed.
Lemma lem8229801 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term815 A B P p f a.
Proof. exact (fun h0 : term766 A B P p f a => @lem8229800 A B P p f a h1). Qed.
Lemma lem8229803 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8229804 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term815 A B P p f a) = (term725 A B P p f a).
Proof. exact (@lem8229803 (term725 A B P p f a)). Qed.
Lemma lem8229805 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8229804 A B P p f a) (@lem8229801 A B P p f a h1)). Qed.
Lemma lem8229807 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8228516 A B P p g a) (@lem8228410 A B P p g a h1)). Qed.
Lemma lem8229808 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term815 A B P p g a.
Proof. exact (fun h0 : term766 A B P p g a => @lem8229807 A B P p g a h1). Qed.
Lemma lem8229810 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8229811 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term815 A B P p g a) = (term725 A B P p g a).
Proof. exact (@lem8229810 (term725 A B P p g a)). Qed.
Lemma lem8229812 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8229811 A B P p g a) (@lem8229808 A B P p g a h1)). Qed.
Lemma lem8229814 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8228498 A B P p f a) (@lem8228404 A B P p f a h1)). Qed.
Lemma lem8229815 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term815 A B P p f a.
Proof. exact (fun h0 : term766 A B P p f a => @lem8229814 A B P p f a h1). Qed.
Lemma lem8229817 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8229818 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term815 A B P p f a) = (term725 A B P p f a).
Proof. exact (@lem8229817 (term725 A B P p f a)). Qed.
Lemma lem8229819 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8229818 A B P p f a) (@lem8229815 A B P p f a h1)). Qed.
Lemma lem8229821 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8228516 A B P p g a) (@lem8228410 A B P p g a h1)). Qed.
Lemma lem8229822 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term815 A B P p g a.
Proof. exact (fun h0 : term766 A B P p g a => @lem8229821 A B P p g a h1). Qed.
Lemma lem8229824 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8229825 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term815 A B P p g a) = (term725 A B P p g a).
Proof. exact (@lem8229824 (term725 A B P p g a)). Qed.
Lemma lem8229826 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8229825 A B P p g a) (@lem8229822 A B P p g a h1)). Qed.
Lemma lem8229829 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term741 _144962 A B P f l g a.
Proof. exact (h1). Qed.
Lemma lem8229830 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term816 _144962 A B P f l g a.
Proof. exact (fun h0 : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a) => @lem8229829 _144962 A B P f l g a h1). Qed.
Lemma lem8229832 (p : Prop) : (term817 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8229833 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term816 _144962 A B P f l g a) = (term741 _144962 A B P f l g a).
Proof. exact (@lem8229832 ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8229834 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term741 _144962 A B P f l g a.
Proof. exact (EQ_MP (@lem8229833 _144962 A B P f l g a) (@lem8229830 _144962 A B P f l g a h1)). Qed.
Lemma lem8229850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8229851 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term809 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term818 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472).
Proof. exact (@lem8229850 (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) (term766 A B P p _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8229865 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8229866 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term819 _144962 A B P p _109470 l _109471 _109472) = (term820 _144962 A B P _109470 l p _109471 _109472).
Proof. exact (@lem8229865 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8229874 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term821 _144947 A B P lt2 z' _109470 _109471 s _109472) = (term821 _144947 A B P lt2 z' _109470 _109471 s _109472).
Proof. exact (eq_refl (term821 _144947 A B P lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8229875 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term818 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term822 _144947 _144962 A B P lt2 z' s _109470 l p _109471 _109472).
Proof. exact (MK_COMB (@lem8229874 _144947 A B P lt2 z' _109470 _109471 s _109472) (@lem8229866 _144962 A B P _109470 l p _109471 _109472)). Qed.
Lemma lem8229879 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8229880 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term822 _144947 _144962 A B P lt2 z' s _109470 l p _109471 _109472) = (term823 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472).
Proof. exact (@lem8229879 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8229898 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term818 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term823 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472).
Proof. exact (TRANS (@lem8229875 _144947 _144962 A B P lt2 z' s _109470 l p _109471 _109472) (@lem8229880 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472)). Qed.
Lemma lem8229899 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term809 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term823 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472).
Proof. exact (TRANS (@lem8229851 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) (@lem8229898 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472)). Qed.
Lemma lem8229900 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8229901 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term824 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472).
Proof. exact (MK_COMB (@lem8229900 A B P p _109470 _109472) (@lem8229899 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472)). Qed.
Lemma lem8229905 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8229906 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term824 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472) = (term825 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472).
Proof. exact (@lem8229905 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109470 _109472) (term826 _144947 A B P lt2 z' _109470 s p _109471 _109472)). Qed.
Lemma lem8229922 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8229923 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term827 _144947 A B P lt2 z' _109470 s p _109471 _109472) = (term828 _144947 A B P lt2 z' s _109470 p _109471 _109472).
Proof. exact (@lem8229922 (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) (term766 A B P p _109470 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8229939 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term829 _144962 A B P _109470 l _109471 _109472) = (term829 _144962 A B P _109470 l _109471 _109472).
Proof. exact (eq_refl (term829 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8229940 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term825 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8229939 _144962 A B P _109470 l _109471 _109472) (@lem8229923 _144947 A B P lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8229951 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term824 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8229906 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472) (@lem8229940 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8229952 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8229901 _144947 _144962 A B P l lt2 z' _109470 s p _109471 _109472) (@lem8229951 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8229953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8229954 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term831 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term832 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8229953) (@lem8229952 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8229978 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8229979 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term819 _144962 A B P p _109470 l _109471 _109472) = (term820 _144962 A B P _109470 l p _109471 _109472).
Proof. exact (@lem8229978 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8229987 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8229988 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term833 _144962 A B P p _109470 l _109471 _109472) = (term834 _144962 A B P _109470 l p _109471 _109472).
Proof. exact (MK_COMB (@lem8229987 A B P p _109470 _109472) (@lem8229979 _144962 A B P _109470 l p _109471 _109472)). Qed.
Lemma lem8229992 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8229993 {_144962 A B P : Type'} (l : type815 _144962 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term834 _144962 A B P _109470 l p _109471 _109472) = (term835 _144962 A B P l _109470 p _109471 _109472).
Proof. exact (@lem8229992 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109470 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230011 {_144962 A B P : Type'} (l : type815 _144962 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term833 _144962 A B P p _109470 l _109471 _109472) = (term835 _144962 A B P l _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8229988 _144962 A B P _109470 l p _109471 _109472) (@lem8229993 _144962 A B P l _109470 p _109471 _109472)). Qed.
Lemma lem8230012 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term821 _144947 A B P lt2 z' _109470 _109471 s _109472) = (term821 _144947 A B P lt2 z' _109470 _109471 s _109472).
Proof. exact (eq_refl (term821 _144947 A B P lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8230013 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (l : type815 _144962 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term837 _144947 _144962 A B P lt2 z' s l _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230012 _144947 A B P lt2 z' _109470 _109471 s _109472) (@lem8230011 _144962 A B P l _109470 p _109471 _109472)). Qed.
Lemma lem8230017 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230018 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term837 _144947 _144962 A B P lt2 z' s l _109470 p _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (@lem8230017 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) (term838 A B P _109470 p _109471 _109472)). Qed.
Lemma lem8230046 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230013 _144947 _144962 A B P lt2 z' s l _109470 p _109471 _109472) (@lem8230018 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8230047 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : ((term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472)) = ((term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)).
Proof. exact (MK_COMB (@lem8229954 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472) (@lem8230046 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8230049 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8230050 (x : Prop) : (x = x) = True.
Proof. exact (@lem8230049 Prop x). Qed.
Lemma lem8230051 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : ((term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472) = (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)) = True.
Proof. exact (@lem8230050 (term830 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8230052 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : ((term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472)) = True.
Proof. exact (TRANS (@lem8230047 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472) (@lem8230051 _144947 _144962 A B P l lt2 z' s _109470 p _109471 _109472)). Qed.
Lemma lem8230053 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : True = ((term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472)).
Proof. exact (SYM (@lem8230052 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472)). Qed.
Lemma lem8230054 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term810 _144947 _144962 A B P p lt2 z' s _109470 l _109471 _109472) = (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472).
Proof. exact (EQ_MP (@lem8230053 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) (@lem0)). Qed.
Lemma lem8230055 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472.
Proof. exact (EQ_MP (@lem8230054 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) (@lem8229371 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8230057 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8230058 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term840 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472).
Proof. exact (@lem8230057 (term833 _144962 A B P p _109470 l _109471 _109472) (term761 _144947 A B P lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8230060 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8230061 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term843 _144962 A B P p _109470 l _109471 _109472) = (term844 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (@lem8230060 (term766 A B P p _109470 _109472) (term819 _144962 A B P p _109470 l _109471 _109472)). Qed.
Lemma lem8230063 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230064 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term845 A B P p _109470 _109472) = (term725 A B P p _109470 _109472).
Proof. exact (@lem8230063 (term725 A B P p _109470 _109472)). Qed.
Lemma lem8230065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230066 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term846 A B P p _109470 _109472) = (term847 A B P p _109470 _109472).
Proof. exact (MK_COMB (@lem8230065) (@lem8230064 A B P p _109470 _109472)). Qed.
Lemma lem8230068 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8230069 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term848 _144962 A B P p _109470 l _109471 _109472) = (term849 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (@lem8230068 (term766 A B P p _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8230071 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230072 {A B P : Type'} (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term845 A B P p _109471 _109472) = (term725 A B P p _109471 _109472).
Proof. exact (@lem8230071 (term725 A B P p _109471 _109472)). Qed.
Lemma lem8230073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230074 {A B P : Type'} (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term846 A B P p _109471 _109472) = (term847 A B P p _109471 _109472).
Proof. exact (MK_COMB (@lem8230073) (@lem8230072 A B P p _109471 _109472)). Qed.
Lemma lem8230075 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term741 _144962 A B P _109470 l _109471 _109472) = (term741 _144962 A B P _109470 l _109471 _109472).
Proof. exact (eq_refl (term741 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8230076 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term849 _144962 A B P p _109470 l _109471 _109472) = (term850 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8230074 A B P p _109471 _109472) (@lem8230075 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8230077 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term848 _144962 A B P p _109470 l _109471 _109472) = (term850 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (TRANS (@lem8230069 _144962 A B P p _109470 l _109471 _109472) (@lem8230076 _144962 A B P p _109470 l _109471 _109472)). Qed.
Lemma lem8230078 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term844 _144962 A B P p _109470 l _109471 _109472) = (term851 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8230066 A B P p _109470 _109472) (@lem8230077 _144962 A B P p _109470 l _109471 _109472)). Qed.
Lemma lem8230079 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term843 _144962 A B P p _109470 l _109471 _109472) = (term851 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (TRANS (@lem8230061 _144962 A B P p _109470 l _109471 _109472) (@lem8230078 _144962 A B P p _109470 l _109471 _109472)). Qed.
Lemma lem8230080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230081 {_144962 A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term852 _144962 A B P p _109470 l _109471 _109472) = (term853 _144962 A B P p _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8230080) (@lem8230079 _144962 A B P p _109470 l _109471 _109472)). Qed.
Lemma lem8230082 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term761 _144947 A B P lt2 z' _109470 _109471 s _109472) = (term761 _144947 A B P lt2 z' _109470 _109471 s _109472).
Proof. exact (eq_refl (term761 _144947 A B P lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8230083 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term840 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472) = (term854 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472).
Proof. exact (MK_COMB (@lem8230081 _144962 A B P p _109470 l _109471 _109472) (@lem8230082 _144947 A B P lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8230084 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (s : P -> _144947) (_109472 : P) : (term836 _144947 _144962 A B P lt2 z' s p _109470 l _109471 _109472) = (term854 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472).
Proof. exact (TRANS (@lem8230058 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472) (@lem8230083 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472)). Qed.
Lemma lem8230086 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) (h2 : p g a) : term850 _144962 A B P p f l g a.
Proof. exact (conj (@lem8229826 A B P p g a h2) (@lem8229834 _144962 A B P f l g a h1)). Qed.
Lemma lem8230087 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) (h2 : p f a) (h3 : p g a) : term851 _144962 A B P p f l g a.
Proof. exact (conj (@lem8229819 A B P p f a h2) (@lem8230086 _144962 A B P f l p g a h1 h3)). Qed.
Lemma lem8230089 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term854 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472.
Proof. exact (EQ_MP (@lem8230084 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472) (@lem8230055 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8230090 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term854 _144947 _144962 A B P p l lt2 z' _109470 _109471 s _109472.
Proof. exact (@lem8230089 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1). Qed.
Lemma lem8230091 {_144947 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term854 _144947 _144962 A B P p l lt2 z' f g s a.
Proof. exact (@lem8230090 _144947 _144962 A B P f g a p lt2 s z' l h1). Qed.
Lemma lem8230094 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term761 _144947 A B P lt2 z' f g s a.
Proof. exact (@lem8230091 _144947 _144962 A B P f g a p lt2 s z' l h1 (@lem8230087 _144962 A B P l f p g a h2 h3 h4)). Qed.
Lemma lem8230095 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term855 _144947 A B P lt2 z' f g s a.
Proof. exact (fun h0 : term856 _144947 A B P lt2 z' f g s a => @lem8230094 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4). Qed.
Lemma lem8230097 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8230098 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z' : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term855 _144947 A B P lt2 z' f g s a) = (term761 _144947 A B P lt2 z' f g s a).
Proof. exact (@lem8230097 (term761 _144947 A B P lt2 z' f g s a)). Qed.
Lemma lem8230099 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term761 _144947 A B P lt2 z' f g s a.
Proof. exact (EQ_MP (@lem8230098 _144947 A B P lt2 z' f g s a) (@lem8230095 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4)). Qed.
Lemma lem8230105 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8230106 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term735 _144947 A B P lt2 s a f g _109465) = (term857 _144947 A B P f g lt2 _109465 s a).
Proof. exact (@lem8230105 ((@I (A -> B) f _109465) = (@I (A -> B) g _109465)) (term732 _144947 A P lt2 _109465 s a)). Qed.
Lemma lem8230114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8230115 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term858 _144947 A B P lt2 s a f g _109465) = (term859 _144947 A B P f g lt2 _109465 s a).
Proof. exact (MK_COMB (@lem8230114) (@lem8230106 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230123 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term857 _144947 A B P f g lt2 _109465 s a) = (term857 _144947 A B P f g lt2 _109465 s a).
Proof. exact (eq_refl (term857 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230124 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : ((term735 _144947 A B P lt2 s a f g _109465) = (term857 _144947 A B P f g lt2 _109465 s a)) = ((term857 _144947 A B P f g lt2 _109465 s a) = (term857 _144947 A B P f g lt2 _109465 s a)).
Proof. exact (MK_COMB (@lem8230115 _144947 A B P f g lt2 _109465 s a) (@lem8230123 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230126 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8230127 (x : Prop) : (x = x) = True.
Proof. exact (@lem8230126 Prop x). Qed.
Lemma lem8230128 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : ((term857 _144947 A B P f g lt2 _109465 s a) = (term857 _144947 A B P f g lt2 _109465 s a)) = True.
Proof. exact (@lem8230127 (term857 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230129 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : ((term735 _144947 A B P lt2 s a f g _109465) = (term857 _144947 A B P f g lt2 _109465 s a)) = True.
Proof. exact (TRANS (@lem8230124 _144947 A B P f g lt2 _109465 s a) (@lem8230128 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230130 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : True = ((term735 _144947 A B P lt2 s a f g _109465) = (term857 _144947 A B P f g lt2 _109465 s a)).
Proof. exact (SYM (@lem8230129 _144947 A B P f g lt2 _109465 s a)). Qed.
Lemma lem8230131 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term735 _144947 A B P lt2 s a f g _109465) = (term857 _144947 A B P f g lt2 _109465 s a).
Proof. exact (EQ_MP (@lem8230130 _144947 A B P f g lt2 _109465 s a) (@lem0)). Qed.
Lemma lem8230132 {_144947 A B P : Type'} (_109465 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term857 _144947 A B P f g lt2 _109465 s a.
Proof. exact (EQ_MP (@lem8230131 _144947 A B P f g lt2 _109465 s a) (@lem8229351 _144947 A B P _109465 lt2 s a f g h1)). Qed.
Lemma lem8230134 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8230135 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109465 : A) : (term857 _144947 A B P f g lt2 _109465 s a) = (term860 _144947 A B P lt2 s a f g _109465).
Proof. exact (@lem8230134 (term732 _144947 A P lt2 _109465 s a) ((@I (A -> B) f _109465) = (@I (A -> B) g _109465))). Qed.
Lemma lem8230137 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230138 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term861 _144947 A P lt2 _109465 s a) = (term730 _144947 A P lt2 _109465 s a).
Proof. exact (@lem8230137 (term730 _144947 A P lt2 _109465 s a)). Qed.
Lemma lem8230139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230140 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (_109465 : A) (s : P -> _144947) (a : P) : (term862 _144947 A P lt2 _109465 s a) = (term863 _144947 A P lt2 _109465 s a).
Proof. exact (MK_COMB (@lem8230139) (@lem8230138 _144947 A P lt2 _109465 s a)). Qed.
Lemma lem8230141 {A B : Type'} (f : A -> B) (g : A -> B) (_109465 : A) : ((@I (A -> B) f _109465) = (@I (A -> B) g _109465)) = ((@I (A -> B) f _109465) = (@I (A -> B) g _109465)).
Proof. exact (eq_refl ((@I (A -> B) f _109465) = (@I (A -> B) g _109465))). Qed.
Lemma lem8230142 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109465 : A) : (term860 _144947 A B P lt2 s a f g _109465) = (term864 _144947 A B P lt2 s a f g _109465).
Proof. exact (MK_COMB (@lem8230140 _144947 A P lt2 _109465 s a) (@lem8230141 A B f g _109465)). Qed.
Lemma lem8230143 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109465 : A) : (term857 _144947 A B P f g lt2 _109465 s a) = (term864 _144947 A B P lt2 s a f g _109465).
Proof. exact (TRANS (@lem8230135 _144947 A B P lt2 s a f g _109465) (@lem8230142 _144947 A B P lt2 s a f g _109465)). Qed.
Lemma lem8230146 {_144947 A B P : Type'} (_109465 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term864 _144947 A B P lt2 s a f g _109465.
Proof. exact (EQ_MP (@lem8230143 _144947 A B P lt2 s a f g _109465) (@lem8230132 _144947 A B P _109465 lt2 s a f g h1)). Qed.
Lemma lem8230147 {_144947 A B P : Type'} (_109465 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term864 _144947 A B P lt2 s a f g _109465.
Proof. exact (@lem8230146 _144947 A B P _109465 lt2 s a f g h1). Qed.
Lemma lem8230148 {_144947 A B P : Type'} (z' : type518 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term865 _144947 A B P lt2 s z' f g a.
Proof. exact (@lem8230147 _144947 A B P (term744 A B P z' f g a) lt2 s a f g h1). Qed.
Lemma lem8230151 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term747 A B P z' f g a) = (term750 A B P z' f g a).
Proof. exact (@lem8230148 _144947 A B P z' lt2 s a f g h1 (@lem8230099 _144947 _144962 A B P lt2 s z' l f p g a h2 h3 h4 h5)). Qed.
Lemma lem8230152 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term866 A B P z' f g a.
Proof. exact (fun h0 : term754 A B P z' f g a => @lem8230151 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5). Qed.
Lemma lem8230154 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8230155 {A B P : Type'} (z' : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term866 A B P z' f g a) = ((term747 A B P z' f g a) = (term750 A B P z' f g a)).
Proof. exact (@lem8230154 ((term747 A B P z' f g a) = (term750 A B P z' f g a))). Qed.
Lemma lem8230156 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term747 A B P z' f g a) = (term750 A B P z' f g a).
Proof. exact (EQ_MP (@lem8230155 A B P z' f g a) (@lem8230152 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230172 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230173 {_144962 A B P : Type'} (z' : type518 A B P) (p : type560 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term813 _144962 A B P p z' _109470 l _109471 _109472) = (term867 _144962 A B P z' p _109470 l _109471 _109472).
Proof. exact (@lem8230172 (term754 A B P z' _109470 _109471 _109472) (term766 A B P p _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8230189 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8230190 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term819 _144962 A B P p _109470 l _109471 _109472) = (term820 _144962 A B P _109470 l p _109471 _109472).
Proof. exact (@lem8230189 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230198 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term868 A B P z' _109470 _109471 _109472) = (term868 A B P z' _109470 _109471 _109472).
Proof. exact (eq_refl (term868 A B P z' _109470 _109471 _109472)). Qed.
Lemma lem8230199 {_144962 A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term867 _144962 A B P z' p _109470 l _109471 _109472) = (term869 _144962 A B P z' _109470 l p _109471 _109472).
Proof. exact (MK_COMB (@lem8230198 A B P z' _109470 _109471 _109472) (@lem8230190 _144962 A B P _109470 l p _109471 _109472)). Qed.
Lemma lem8230203 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230204 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term869 _144962 A B P z' _109470 l p _109471 _109472) = (term870 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (@lem8230203 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term754 A B P z' _109470 _109471 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230224 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term867 _144962 A B P z' p _109470 l _109471 _109472) = (term870 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230199 _144962 A B P z' _109470 l p _109471 _109472) (@lem8230204 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230225 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term813 _144962 A B P p z' _109470 l _109471 _109472) = (term870 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230173 _144962 A B P z' p _109470 l _109471 _109472) (@lem8230224 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230226 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8230227 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term814 _144962 A B P p z' _109470 l _109471 _109472) = (term871 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230226 A B P p _109470 _109472) (@lem8230225 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230232 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term871 _144962 A B P l z' _109470 p _109471 _109472) = (term872 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (@lem8230231 ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) (term766 A B P p _109470 _109472) (term873 A B P z' _109470 p _109471 _109472)). Qed.
Lemma lem8230248 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230249 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term874 A B P z' _109470 p _109471 _109472) = (term875 A B P z' _109470 p _109471 _109472).
Proof. exact (@lem8230248 (term754 A B P z' _109470 _109471 _109472) (term766 A B P p _109470 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230267 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term829 _144962 A B P _109470 l _109471 _109472) = (term829 _144962 A B P _109470 l _109471 _109472).
Proof. exact (eq_refl (term829 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8230268 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term872 _144962 A B P l z' _109470 p _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230267 _144962 A B P _109470 l _109471 _109472) (@lem8230249 A B P z' _109470 p _109471 _109472)). Qed.
Lemma lem8230279 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term871 _144962 A B P l z' _109470 p _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230232 _144962 A B P l z' _109470 p _109471 _109472) (@lem8230268 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230280 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term814 _144962 A B P p z' _109470 l _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230227 _144962 A B P l z' _109470 p _109471 _109472) (@lem8230279 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8230282 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term877 _144962 A B P p z' _109470 l _109471 _109472) = (term878 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230281) (@lem8230280 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8230309 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term789 A B P p z' _109470 _109471 _109472) = (term873 A B P z' _109470 p _109471 _109472).
Proof. exact (@lem8230308 (term754 A B P z' _109470 _109471 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230317 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term767 A B P p _109470 _109472) = (term767 A B P p _109470 _109472).
Proof. exact (eq_refl (term767 A B P p _109470 _109472)). Qed.
Lemma lem8230318 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term794 A B P p z' _109470 _109471 _109472) = (term874 A B P z' _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230317 A B P p _109470 _109472) (@lem8230309 A B P z' _109470 p _109471 _109472)). Qed.
Lemma lem8230322 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8230323 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term874 A B P z' _109470 p _109471 _109472) = (term875 A B P z' _109470 p _109471 _109472).
Proof. exact (@lem8230322 (term754 A B P z' _109470 _109471 _109472) (term766 A B P p _109470 _109472) (term766 A B P p _109471 _109472)). Qed.
Lemma lem8230341 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term794 A B P p z' _109470 _109471 _109472) = (term875 A B P z' _109470 p _109471 _109472).
Proof. exact (TRANS (@lem8230318 A B P z' _109470 p _109471 _109472) (@lem8230323 A B P z' _109470 p _109471 _109472)). Qed.
Lemma lem8230342 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term829 _144962 A B P _109470 l _109471 _109472) = (term829 _144962 A B P _109470 l _109471 _109472).
Proof. exact (eq_refl (term829 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8230343 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term879 _144962 A B P l p z' _109470 _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472).
Proof. exact (MK_COMB (@lem8230342 _144962 A B P _109470 l _109471 _109472) (@lem8230341 A B P z' _109470 p _109471 _109472)). Qed.
Lemma lem8230354 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : ((term814 _144962 A B P p z' _109470 l _109471 _109472) = (term879 _144962 A B P l p z' _109470 _109471 _109472)) = ((term876 _144962 A B P l z' _109470 p _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472)).
Proof. exact (MK_COMB (@lem8230282 _144962 A B P l z' _109470 p _109471 _109472) (@lem8230343 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230356 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8230357 (x : Prop) : (x = x) = True.
Proof. exact (@lem8230356 Prop x). Qed.
Lemma lem8230358 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z' : type518 A B P) (_109470 : A -> B) (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : ((term876 _144962 A B P l z' _109470 p _109471 _109472) = (term876 _144962 A B P l z' _109470 p _109471 _109472)) = True.
Proof. exact (@lem8230357 (term876 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230359 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : ((term814 _144962 A B P p z' _109470 l _109471 _109472) = (term879 _144962 A B P l p z' _109470 _109471 _109472)) = True.
Proof. exact (TRANS (@lem8230354 _144962 A B P l z' _109470 p _109471 _109472) (@lem8230358 _144962 A B P l z' _109470 p _109471 _109472)). Qed.
Lemma lem8230360 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : True = ((term814 _144962 A B P p z' _109470 l _109471 _109472) = (term879 _144962 A B P l p z' _109470 _109471 _109472)).
Proof. exact (SYM (@lem8230359 _144962 A B P l p z' _109470 _109471 _109472)). Qed.
Lemma lem8230361 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term814 _144962 A B P p z' _109470 l _109471 _109472) = (term879 _144962 A B P l p z' _109470 _109471 _109472).
Proof. exact (EQ_MP (@lem8230360 _144962 A B P l p z' _109470 _109471 _109472) (@lem0)). Qed.
Lemma lem8230362 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term879 _144962 A B P l p z' _109470 _109471 _109472.
Proof. exact (EQ_MP (@lem8230361 _144962 A B P l p z' _109470 _109471 _109472) (@lem8229389 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8230364 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8230365 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term879 _144962 A B P l p z' _109470 _109471 _109472) = (term880 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (@lem8230364 (term794 A B P p z' _109470 _109471 _109472) ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8230367 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8230368 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term881 A B P p z' _109470 _109471 _109472) = (term882 A B P p z' _109470 _109471 _109472).
Proof. exact (@lem8230367 (term766 A B P p _109470 _109472) (term789 A B P p z' _109470 _109471 _109472)). Qed.
Lemma lem8230370 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230371 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term845 A B P p _109470 _109472) = (term725 A B P p _109470 _109472).
Proof. exact (@lem8230370 (term725 A B P p _109470 _109472)). Qed.
Lemma lem8230372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230373 {A B P : Type'} (p : type560 A B P) (_109470 : A -> B) (_109472 : P) : (term846 A B P p _109470 _109472) = (term847 A B P p _109470 _109472).
Proof. exact (MK_COMB (@lem8230372) (@lem8230371 A B P p _109470 _109472)). Qed.
Lemma lem8230375 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8230376 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term883 A B P p z' _109470 _109471 _109472) = (term884 A B P p z' _109470 _109471 _109472).
Proof. exact (@lem8230375 (term766 A B P p _109471 _109472) (term754 A B P z' _109470 _109471 _109472)). Qed.
Lemma lem8230378 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230379 {A B P : Type'} (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term845 A B P p _109471 _109472) = (term725 A B P p _109471 _109472).
Proof. exact (@lem8230378 (term725 A B P p _109471 _109472)). Qed.
Lemma lem8230380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230381 {A B P : Type'} (p : type560 A B P) (_109471 : A -> B) (_109472 : P) : (term846 A B P p _109471 _109472) = (term847 A B P p _109471 _109472).
Proof. exact (MK_COMB (@lem8230380) (@lem8230379 A B P p _109471 _109472)). Qed.
Lemma lem8230383 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8230384 {A B P : Type'} (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term885 A B P z' _109470 _109471 _109472) = ((term747 A B P z' _109470 _109471 _109472) = (term750 A B P z' _109470 _109471 _109472)).
Proof. exact (@lem8230383 ((term747 A B P z' _109470 _109471 _109472) = (term750 A B P z' _109470 _109471 _109472))). Qed.
Lemma lem8230385 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term884 A B P p z' _109470 _109471 _109472) = (term886 A B P p z' _109470 _109471 _109472).
Proof. exact (MK_COMB (@lem8230381 A B P p _109471 _109472) (@lem8230384 A B P z' _109470 _109471 _109472)). Qed.
Lemma lem8230386 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term883 A B P p z' _109470 _109471 _109472) = (term886 A B P p z' _109470 _109471 _109472).
Proof. exact (TRANS (@lem8230376 A B P p z' _109470 _109471 _109472) (@lem8230385 A B P p z' _109470 _109471 _109472)). Qed.
Lemma lem8230387 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term882 A B P p z' _109470 _109471 _109472) = (term887 A B P p z' _109470 _109471 _109472).
Proof. exact (MK_COMB (@lem8230373 A B P p _109470 _109472) (@lem8230386 A B P p z' _109470 _109471 _109472)). Qed.
Lemma lem8230388 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term881 A B P p z' _109470 _109471 _109472) = (term887 A B P p z' _109470 _109471 _109472).
Proof. exact (TRANS (@lem8230368 A B P p z' _109470 _109471 _109472) (@lem8230387 A B P p z' _109470 _109471 _109472)). Qed.
Lemma lem8230389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230390 {A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) : (term888 A B P p z' _109470 _109471 _109472) = (term889 A B P p z' _109470 _109471 _109472).
Proof. exact (MK_COMB (@lem8230389) (@lem8230388 A B P p z' _109470 _109471 _109472)). Qed.
Lemma lem8230391 {_144962 A B P : Type'} (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)) = ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472)).
Proof. exact (eq_refl ((term738 _144962 A B P l _109470 _109472) = (term738 _144962 A B P l _109471 _109472))). Qed.
Lemma lem8230392 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term880 _144962 A B P p z' _109470 l _109471 _109472) = (term890 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (MK_COMB (@lem8230390 A B P p z' _109470 _109471 _109472) (@lem8230391 _144962 A B P _109470 l _109471 _109472)). Qed.
Lemma lem8230393 {_144962 A B P : Type'} (p : type560 A B P) (z' : type518 A B P) (_109470 : A -> B) (l : type815 _144962 A B P) (_109471 : A -> B) (_109472 : P) : (term879 _144962 A B P l p z' _109470 _109471 _109472) = (term890 _144962 A B P p z' _109470 l _109471 _109472).
Proof. exact (TRANS (@lem8230365 _144962 A B P p z' _109470 l _109471 _109472) (@lem8230392 _144962 A B P p z' _109470 l _109471 _109472)). Qed.
Lemma lem8230395 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term886 A B P p z' f g a.
Proof. exact (conj (@lem8229812 A B P p g a h5) (@lem8230156 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230396 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term887 A B P p z' f g a.
Proof. exact (conj (@lem8229805 A B P p f a h4) (@lem8230395 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230398 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term890 _144962 A B P p z' _109470 l _109471 _109472.
Proof. exact (EQ_MP (@lem8230393 _144962 A B P p z' _109470 l _109471 _109472) (@lem8230362 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1)). Qed.
Lemma lem8230399 {_144947 _144962 A B P : Type'} (_109470 : A -> B) (_109471 : A -> B) (_109472 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term890 _144962 A B P p z' _109470 l _109471 _109472.
Proof. exact (@lem8230398 _144947 _144962 A B P _109470 _109471 _109472 p lt2 s z' l h1). Qed.
Lemma lem8230400 {_144947 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z' l) : term890 _144962 A B P p z' f l g a.
Proof. exact (@lem8230399 _144947 _144962 A B P f g a p lt2 s z' l h1). Qed.
Lemma lem8230403 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8230400 _144947 _144962 A B P f g a p lt2 s z' l h2 (@lem8230396 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230404 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : p f a) (h4 : p g a) : term891 _144962 A B P f l g a.
Proof. exact (fun h0 : term741 _144962 A B P f l g a => @lem8230403 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h0 h3 h4). Qed.
Lemma lem8230406 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8230407 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term891 _144962 A B P f l g a) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (@lem8230406 ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8230408 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : p f a) (h4 : p g a) : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a).
Proof. exact (EQ_MP (@lem8230407 _144962 A B P f l g a) (@lem8230404 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4)). Qed.
Lemma lem8230411 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8230413 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term741 _144962 A B P f l g a) = (term892 _144962 A B P f l g a).
Proof. exact (@lem8230411 ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8230416 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term352 _144962 A B P f l g a) : term892 _144962 A B P f l g a.
Proof. exact (EQ_MP (@lem8230413 _144962 A B P f l g a) (@lem8229353 _144962 A B P f l g a h1)). Qed.
Lemma lem8230419 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term352 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : False.
Proof. exact (@lem8230416 _144962 A B P f l g a h3 (@lem8230408 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h4 h5)). Qed.
Lemma lem8230420 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term352 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term69.
Proof. exact (fun h0 : ~ False => @lem8230419 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5). Qed.
Lemma lem8230422 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8230423 : term69 = False.
Proof. exact (@lem8230422 False). Qed.
Lemma lem8230424 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z' : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z' l) (h3 : term352 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : False.
Proof. exact (EQ_MP (@lem8230423) (@lem8230420 _144947 _144962 A B P lt2 s z' l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230425 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term352 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : False.
Proof. exact (ex_elim (@lem8228019 _144947 _144962 A B P p lt2 s l h2) (fun z' : type518 A B P => fun h0 : term560 _144947 _144962 A B P p lt2 s l z' => @lem8230424 _144947 _144962 A B P lt2 s z' l f p g a h1 h0 h3 h4 h5)). Qed.
Lemma lem8230426 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (ex_elim (@lem8228398 _144947 _144956 _144962 A B P p l lt2 s h h2) (fun z : type809 _144962 A B P => fun h0 : term720 _144947 _144956 _144962 A B P p l lt2 s h z => @lem8230425 _144947 _144962 A B P lt2 s l f p g a h1 h3 h4 h5 h6)). Qed.
Lemma lem8230427 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : (term352 _144962 A B P f l g a) = False.
Proof. exact (prop_ext (fun h7 : term352 _144962 A B P f l g a => @lem8230426 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8228479 _144962 A B P f l g a h4)). Qed.
Lemma lem8230428 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8230427 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (@lem8228479 _144962 A B P f l g a h4)). Qed.
Lemma lem8230429 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : (p g a) = False.
Proof. exact (prop_ext (fun h7 : p g a => @lem8230428 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8228410 A B P p g a h6)). Qed.
Lemma lem8230430 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8230429 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (@lem8228410 A B P p g a h6)). Qed.
Lemma lem8230431 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : (p f a) = False.
Proof. exact (prop_ext (fun h7 : p f a => @lem8230430 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8228404 A B P p f a h5)). Qed.
Lemma lem8230432 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8230431 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (@lem8228404 A B P p f a h5)). Qed.
Lemma lem8230433 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : (term352 _144962 A B P f l g a) = False.
Proof. exact (prop_ext (fun h7 : term352 _144962 A B P f l g a => @lem8230432 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8227693 _144962 A B P f l g a h4)). Qed.
Lemma lem8230434 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8230433 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (@lem8227693 _144962 A B P f l g a h4)). Qed.
Lemma lem8230435 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term351 _144962 A B P f l g a.
Proof. exact (fun h0 : term352 _144962 A B P f l g a => @lem8230434 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h0 h4 h5). Qed.
Lemma lem8230436 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (l f a) = (l g a).
Proof. exact (EQ_MP (@lem8227692 _144962 A B P f l g a) (@lem8230435 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230437 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) (h4 : p g a) : term360 _144947 _144962 A B P lt2 s f l g a.
Proof. exact (fun h0 : term222 _144947 A B P lt2 s a f g => @lem8230436 _144947 _144956 _144962 A B P h lt2 s l f p g a h0 h1 h2 h3 h4). Qed.
Lemma lem8230438 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) : term363 _144947 _144962 A B P p lt2 s f l g a.
Proof. exact (fun h0 : p g a => @lem8230437 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h0). Qed.
Lemma lem8230439 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term365 _144947 _144962 A B P p lt2 s f l g a.
Proof. exact (fun h0 : p f a => @lem8230438 _144947 _144956 _144962 A B P g h lt2 s l p f a h1 h2 h0). Qed.
Lemma lem8230440 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term368 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term286 _144947 _144956 _144962 A B P p l lt2 s h => @lem8230439 _144947 _144956 _144962 A B P f g a h p lt2 s l h0 h1). Qed.
Lemma lem8230441 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term370 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (fun h0 : term87 _144947 _144962 A B P p lt2 s l => @lem8230440 _144947 _144956 _144962 A B P h f g a p lt2 s l h0). Qed.
Lemma lem8230446 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term374 _144947 _144956 _144962 A B P p lt2 s f l g a.
Proof. exact (fun h : type889 _144956 _144962 A B P => @lem8230441 _144947 _144956 _144962 A B P h p lt2 s f l g a). Qed.
Lemma lem8230451 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term378 _144947 _144956 _144962 A B P lt2 s f l g a.
Proof. exact (fun p : type560 A B P => @lem8230446 _144947 _144956 _144962 A B P p lt2 s f l g a). Qed.
Lemma lem8230456 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term382 _144947 _144956 _144962 A B P s f l g a.
Proof. exact (fun lt2 : type1470 _144947 A => @lem8230451 _144947 _144956 _144962 A B P lt2 s f l g a). Qed.
Lemma lem8230461 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term386 _144947 _144956 _144962 A B P f l g a.
Proof. exact (fun s : P -> _144947 => @lem8230456 _144947 _144956 _144962 A B P s f l g a). Qed.
Lemma lem8230466 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : term390 _144947 _144956 _144962 A B P l g a.
Proof. exact (fun f : A -> B => @lem8230461 _144947 _144956 _144962 A B P f l g a). Qed.
Lemma lem8230471 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : term394 _144947 _144956 _144962 A B P g a.
Proof. exact (fun l : type815 _144962 A B P => @lem8230466 _144947 _144956 _144962 A B P l g a). Qed.
Lemma lem8230476 {_144947 _144956 _144962 A B P : Type'} (a : P) : term398 _144947 _144956 _144962 A B P a.
Proof. exact (fun g : A -> B => @lem8230471 _144947 _144956 _144962 A B P g a). Qed.
Lemma lem8230481 {_144947 _144956 _144962 A B P : Type'} : term402 _144947 _144956 _144962 A B P.
Proof. exact (fun a : P => @lem8230476 _144947 _144956 _144962 A B P a). Qed.
Lemma lem8230482 {_144947 _144956 _144962 A B P : Type'} : term401 _144947 _144956 _144962 A B P.
Proof. exact (EQ_MP (@lem8227683 _144947 _144956 _144962 A B P) (@lem8230481 _144947 _144956 _144962 A B P)). Qed.
Lemma lem8230483 {_144947 _144956 _144962 A B P : Type'} (a : P) : term893 _144947 _144956 _144962 A B P a.
Proof. exact (@lem8230482 _144947 _144956 _144962 A B P a). Qed.
Lemma lem8230484 {_144947 _144956 _144962 A B P : Type'} (a : P) : (term893 _144947 _144956 _144962 A B P a) = (term397 _144947 _144956 _144962 A B P a).
Proof. exact (eq_refl (term893 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8230485 {_144947 _144956 _144962 A B P : Type'} (a : P) : term397 _144947 _144956 _144962 A B P a.
Proof. exact (EQ_MP (@lem8230484 _144947 _144956 _144962 A B P a) (@lem8230483 _144947 _144956 _144962 A B P a)). Qed.
Lemma lem8230486 {_144947 _144956 _144962 A B P : Type'} (a : P) (g : A -> B) : term894 _144947 _144956 _144962 A B P a g.
Proof. exact (@lem8230485 _144947 _144956 _144962 A B P a g). Qed.
Lemma lem8230487 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : (term894 _144947 _144956 _144962 A B P a g) = (term393 _144947 _144956 _144962 A B P g a).
Proof. exact (eq_refl (term894 _144947 _144956 _144962 A B P a g)). Qed.
Lemma lem8230488 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) : term393 _144947 _144956 _144962 A B P g a.
Proof. exact (EQ_MP (@lem8230487 _144947 _144956 _144962 A B P g a) (@lem8230486 _144947 _144956 _144962 A B P a g)). Qed.
Lemma lem8230489 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (a : P) (l : type815 _144962 A B P) : term895 _144947 _144956 _144962 A B P g a l.
Proof. exact (@lem8230488 _144947 _144956 _144962 A B P g a l). Qed.
Lemma lem8230490 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term895 _144947 _144956 _144962 A B P g a l) = (term389 _144947 _144956 _144962 A B P l g a).
Proof. exact (eq_refl (term895 _144947 _144956 _144962 A B P g a l)). Qed.
Lemma lem8230491 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : term389 _144947 _144956 _144962 A B P l g a.
Proof. exact (EQ_MP (@lem8230490 _144947 _144956 _144962 A B P l g a) (@lem8230489 _144947 _144956 _144962 A B P g a l)). Qed.
Lemma lem8230492 {_144947 _144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) (f : A -> B) : term896 _144947 _144956 _144962 A B P l g a f.
Proof. exact (@lem8230491 _144947 _144956 _144962 A B P l g a f). Qed.
Lemma lem8230493 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term896 _144947 _144956 _144962 A B P l g a f) = (term385 _144947 _144956 _144962 A B P f l g a).
Proof. exact (eq_refl (term896 _144947 _144956 _144962 A B P l g a f)). Qed.
Lemma lem8230494 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term385 _144947 _144956 _144962 A B P f l g a.
Proof. exact (EQ_MP (@lem8230493 _144947 _144956 _144962 A B P f l g a) (@lem8230492 _144947 _144956 _144962 A B P l g a f)). Qed.
Lemma lem8230495 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (s : P -> _144947) : term897 _144947 _144956 _144962 A B P f l g a s.
Proof. exact (@lem8230494 _144947 _144956 _144962 A B P f l g a s). Qed.
Lemma lem8230496 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term897 _144947 _144956 _144962 A B P f l g a s) = (term381 _144947 _144956 _144962 A B P s f l g a).
Proof. exact (eq_refl (term897 _144947 _144956 _144962 A B P f l g a s)). Qed.
Lemma lem8230497 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term381 _144947 _144956 _144962 A B P s f l g a.
Proof. exact (EQ_MP (@lem8230496 _144947 _144956 _144962 A B P s f l g a) (@lem8230495 _144947 _144956 _144962 A B P f l g a s)). Qed.
Lemma lem8230498 {_144947 _144956 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (lt2 : type1470 _144947 A) : term898 _144947 _144956 _144962 A B P s f l g a lt2.
Proof. exact (@lem8230497 _144947 _144956 _144962 A B P s f l g a lt2). Qed.
Lemma lem8230499 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term898 _144947 _144956 _144962 A B P s f l g a lt2) = (term377 _144947 _144956 _144962 A B P lt2 s f l g a).
Proof. exact (eq_refl (term898 _144947 _144956 _144962 A B P s f l g a lt2)). Qed.
Lemma lem8230500 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term377 _144947 _144956 _144962 A B P lt2 s f l g a.
Proof. exact (EQ_MP (@lem8230499 _144947 _144956 _144962 A B P lt2 s f l g a) (@lem8230498 _144947 _144956 _144962 A B P s f l g a lt2)). Qed.
Lemma lem8230501 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (p : type560 A B P) : term899 _144947 _144956 _144962 A B P lt2 s f l g a p.
Proof. exact (@lem8230500 _144947 _144956 _144962 A B P lt2 s f l g a p). Qed.
Lemma lem8230502 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term899 _144947 _144956 _144962 A B P lt2 s f l g a p) = (term373 _144947 _144956 _144962 A B P p lt2 s f l g a).
Proof. exact (eq_refl (term899 _144947 _144956 _144962 A B P lt2 s f l g a p)). Qed.
Lemma lem8230503 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term373 _144947 _144956 _144962 A B P p lt2 s f l g a.
Proof. exact (EQ_MP (@lem8230502 _144947 _144956 _144962 A B P p lt2 s f l g a) (@lem8230501 _144947 _144956 _144962 A B P lt2 s f l g a p)). Qed.
Lemma lem8230504 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h : type889 _144956 _144962 A B P) : term900 _144947 _144956 _144962 A B P p lt2 s f l g a h.
Proof. exact (@lem8230503 _144947 _144956 _144962 A B P p lt2 s f l g a h). Qed.
Lemma lem8230505 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term900 _144947 _144956 _144962 A B P p lt2 s f l g a h) = (term353 _144947 _144956 _144962 A B P h p lt2 s f l g a).
Proof. exact (eq_refl (term900 _144947 _144956 _144962 A B P p lt2 s f l g a h)). Qed.
Lemma lem8230506 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (EQ_MP (@lem8230505 _144947 _144956 _144962 A B P h p lt2 s f l g a) (@lem8230504 _144947 _144956 _144962 A B P p lt2 s f l g a h)). Qed.
Lemma lem8230508 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term353 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8227229 _144947 _144956 _144962 A B P h p lt2 s f l g a (@lem8230506 _144947 _144956 _144962 A B P h p lt2 s f l g a)). Qed.
Lemma lem8230509 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term367 _144947 _144956 _144962 A B P h p lt2 s f l g a.
Proof. exact (@lem8230508 _144947 _144956 _144962 A B P h p lt2 s f l g a (@lem8227199 _144947 _144962 A B P p lt2 s l h1)). Qed.
Lemma lem8230510 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term364 _144947 _144962 A B P p lt2 s f l g a.
Proof. exact (@lem8230509 _144947 _144956 _144962 A B P h f g a p lt2 s l h2 (@lem8227198 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8230511 {_144947 _144956 _144962 A B P : Type'} (g : A -> B) (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) : term362 _144947 _144962 A B P p lt2 s f l g a.
Proof. exact (@lem8230510 _144947 _144956 _144962 A B P f g a h p lt2 s l h1 h2 (@lem8227202 A B P p f a h3)). Qed.
Lemma lem8230512 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) (h4 : p g a) : term359 _144947 _144962 A B P lt2 s f l g a.
Proof. exact (@lem8230511 _144947 _144956 _144962 A B P g h lt2 s l p f a h1 h2 h3 (@lem8227204 A B P p g a h4)). Qed.
Lemma lem8230513 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term351 _144962 A B P f l g a.
Proof. exact (@lem8230512 _144947 _144956 _144962 A B P h lt2 s l f p g a h2 h3 h4 h5 (@lem8227203 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8230514 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (@lem8230513 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h5 h6 (@lem8227213 _144962 A B P f l g a h4)). Qed.
Lemma lem8230515 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : (term352 _144962 A B P f l g a) = False.
Proof. exact (prop_ext (fun h7 : term352 _144962 A B P f l g a => @lem8230514 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8227213 _144962 A B P f l g a h4)). Qed.
Lemma lem8230516 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term352 _144962 A B P f l g a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8230515 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5 h6) (@lem8227213 _144962 A B P f l g a h4)). Qed.
Lemma lem8230517 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term351 _144962 A B P f l g a.
Proof. exact (fun h0 : term352 _144962 A B P f l g a => @lem8230516 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h0 h4 h5). Qed.
Lemma lem8230518 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (l f a) = (l g a).
Proof. exact (EQ_MP (@lem8227212 _144962 A B P f l g a) (@lem8230517 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8230520 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) : term24 _26299 _26310 f g l.
Proof. exact (EQ_MP (@lem8225770 _26299 _26310 f g l) (@lem8225769 _26299 _26310 f g l)). Qed.
Lemma lem8230521 {_144956 _144962 : Type'} (f : _144962 -> _144956) (g : _144962 -> _144956) (l : list _144962) : term901 _144956 _144962 f g l.
Proof. exact (@lem8230520 _144962 _144956 f g l). Qed.
Lemma lem8230522 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (l : type815 _144962 A B P) (f : A -> B) (a : P) : term902 _144956 _144962 A B P h g l f a.
Proof. exact (@lem8230521 _144956 _144962 (h f a) (h g a) (l f a)). Qed.
Lemma lem8230524 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem8225740 _26777 l P) (@lem8225739 _26777 P l)). Qed.
Lemma lem8230525 {_144962 : Type'} (l : list _144962) (P : _144962 -> Prop) : (@List.Forall _144962 P l) = (term7 _144962 l P).
Proof. exact (@lem8230524 _144962 l P). Qed.
Lemma lem8230526 {_144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) : (term903 _144956 _144962 A B P h g l f a) = (term904 _144956 _144962 A B P l f h g a).
Proof. exact (@lem8230525 _144962 (l f a) (term905 _144956 _144962 A B P f h g a)). Qed.
Lemma lem8230534 {A B : Type'} (f : A -> B) (y : A) : (term116 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8230535 {_144962 : Type'} (f : _144962 -> Prop) (y : _144962) : (term906 _144962 f y) = (f y).
Proof. exact (@lem8230534 _144962 Prop f y). Qed.
Lemma lem8230536 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term907 _144956 _144962 A B P f h g a x) = (term908 _144956 _144962 A B P f h g a x).
Proof. exact (@lem8230535 _144962 (term905 _144956 _144962 A B P f h g a) x). Qed.
Lemma lem8230537 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term908 _144956 _144962 A B P f h g a x) = ((h f a x) = (h g a x)).
Proof. exact (eq_refl (term908 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230538 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) : (term909 _144956 _144962 A B P f h g a) = (term905 _144956 _144962 A B P f h g a).
Proof. exact (fun_ext (fun x : _144962 => @lem8230537 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230539 {_144962 : Type'} (x : _144962) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8230540 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term907 _144956 _144962 A B P f h g a x) = (term908 _144956 _144962 A B P f h g a x).
Proof. exact (MK_COMB (@lem8230538 _144956 _144962 A B P f h g a) (@lem8230539 _144962 x)). Qed.
Lemma lem8230541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8230542 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term910 _144956 _144962 A B P f h g a x) = (term911 _144956 _144962 A B P f h g a x).
Proof. exact (MK_COMB (@lem8230541) (@lem8230540 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230543 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term908 _144956 _144962 A B P f h g a x) = ((h f a x) = (h g a x)).
Proof. exact (eq_refl (term908 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230544 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : ((term907 _144956 _144962 A B P f h g a x) = (term908 _144956 _144962 A B P f h g a x)) = ((term908 _144956 _144962 A B P f h g a x) = ((h f a x) = (h g a x))).
Proof. exact (MK_COMB (@lem8230542 _144956 _144962 A B P f h g a x) (@lem8230543 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230545 {_144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term908 _144956 _144962 A B P f h g a x) = ((h f a x) = (h g a x)).
Proof. exact (EQ_MP (@lem8230544 _144956 _144962 A B P f h g a x) (@lem8230536 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230548 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term912 _144962 A B P x l f a) = (term912 _144962 A B P x l f a).
Proof. exact (eq_refl (term912 _144962 A B P x l f a)). Qed.
Lemma lem8230549 {_144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : (term913 _144956 _144962 A B P l f h g a x) = (term914 _144956 _144962 A B P l f h g a x).
Proof. exact (MK_COMB (@lem8230548 _144962 A B P x l f a) (@lem8230545 _144956 _144962 A B P f h g a x)). Qed.
Lemma lem8230552 {_144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) : (term915 _144956 _144962 A B P l f h g a) = (term916 _144956 _144962 A B P l f h g a).
Proof. exact (fun_ext (fun x : _144962 => @lem8230549 _144956 _144962 A B P l f h g a x)). Qed.
Lemma lem8230553 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8230554 {_144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) : (term904 _144956 _144962 A B P l f h g a) = (term917 _144956 _144962 A B P l f h g a).
Proof. exact (MK_COMB (@lem8230553 _144962) (@lem8230552 _144956 _144962 A B P l f h g a)). Qed.
Lemma lem8230559 {_144956 _144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (a : P) : (term903 _144956 _144962 A B P h g l f a) = (term917 _144956 _144962 A B P l f h g a).
Proof. exact (TRANS (@lem8230526 _144956 _144962 A B P l f h g a) (@lem8230554 _144956 _144962 A B P l f h g a)). Qed.
Lemma lem8230560 {_144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (g : A -> B) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term917 _144956 _144962 A B P l f h g a) = (term903 _144956 _144962 A B P h g l f a).
Proof. exact (SYM (@lem8230559 _144956 _144962 A B P l f h g a)). Qed.
Lemma lem8230561 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : term564 _144962 A B P x l f a.
Proof. exact (h1). Qed.
Lemma lem8230580 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term286 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8230581 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term918 _144947 _144956 _144962 A B P p l lt2 s h f.
Proof. exact (@lem8230580 _144947 _144956 _144962 A B P p l lt2 s h h1 f). Qed.
Lemma lem8230582 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term918 _144947 _144956 _144962 A B P p l lt2 s h f) = (term283 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (eq_refl (term918 _144947 _144956 _144962 A B P p l lt2 s h f)). Qed.
Lemma lem8230583 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term283 _144947 _144956 _144962 A B P p l lt2 s f h.
Proof. exact (EQ_MP (@lem8230582 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8230581 _144947 _144956 _144962 A B P f p l lt2 s h h1)). Qed.
Lemma lem8230584 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term919 _144947 _144956 _144962 A B P p l lt2 s f h g.
Proof. exact (@lem8230583 _144947 _144956 _144962 A B P f p l lt2 s h h1 g). Qed.
Lemma lem8230585 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term919 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term279 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (eq_refl (term919 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8230586 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term279 _144947 _144956 _144962 A B P p l lt2 s f h g.
Proof. exact (EQ_MP (@lem8230585 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8230584 _144947 _144956 _144962 A B P f g p l lt2 s h h1)). Qed.
Lemma lem8230587 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term920 _144947 _144956 _144962 A B P p l lt2 s f h g p1.
Proof. exact (@lem8230586 _144947 _144956 _144962 A B P f g p l lt2 s h h1 p1). Qed.
Lemma lem8230588 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p1 : _144962) : (term920 _144947 _144956 _144962 A B P p l lt2 s f h g p1) = (term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1).
Proof. exact (eq_refl (term920 _144947 _144956 _144962 A B P p l lt2 s f h g p1)). Qed.
Lemma lem8230589 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term277 _144947 _144956 _144962 A B P p l lt2 s f h g p1.
Proof. exact (EQ_MP (@lem8230588 _144947 _144956 _144962 A B P p l lt2 s f h g p1) (@lem8230587 _144947 _144956 _144962 A B P f g p1 p l lt2 s h h1)). Qed.
Lemma lem8230590 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p1 : _144962) (p2 : P) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term921 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2.
Proof. exact (@lem8230589 _144947 _144956 _144962 A B P f g p1 p l lt2 s h h1 p2). Qed.
Lemma lem8230591 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term921 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2) = (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (eq_refl (term921 _144947 _144956 _144962 A B P p l lt2 s f h g p1 p2)). Qed.
Lemma lem8230592 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (EQ_MP (@lem8230591 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8230590 _144947 _144956 _144962 A B P f g p1 p2 p l lt2 s h h1)). Qed.
Lemma lem8230593 {_144947 _144962 A B P : Type'} (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (h1 : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g.
Proof. exact (h1). Qed.
Lemma lem8230594 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) : (h f p2 p1) = (h g p2 p1).
Proof. exact (@lem8230592 _144947 _144956 _144962 A B P f g p2 p1 p l lt2 s h h1 (@lem8230593 _144947 _144962 A B P p p1 l lt2 s p2 f g h2)). Qed.
Lemma lem8230595 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (h1 : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) : term922 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (fun h0 : term286 _144947 _144956 _144962 A B P p l lt2 s h => @lem8230594 _144947 _144956 _144962 A B P h p p1 l lt2 s p2 f g h0 h1). Qed.
Lemma lem8230596 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term286 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8230597 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (p1 : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (p2 : P) (f : A -> B) (g : A -> B) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g) : (h f p2 p1) = (h g p2 p1).
Proof. exact (@lem8230595 _144947 _144956 _144962 A B P h p p1 l lt2 s p2 f g h2 (@lem8230596 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8230598 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (fun h0 : term226 _144947 _144962 A B P p p1 l lt2 s p2 f g => @lem8230597 _144947 _144956 _144962 A B P h p p1 l lt2 s p2 f g h1 h0). Qed.
Lemma lem8230599 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term923 _144947 _144956 _144962 A B P p l lt2 s f h g p2.
Proof. exact (fun p1 : _144962 => @lem8230598 _144947 _144956 _144962 A B P f g p2 p1 p l lt2 s h h1). Qed.
Lemma lem8230600 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term924 _144947 _144956 _144962 A B P p l lt2 s f h g.
Proof. exact (fun p2 : P => @lem8230599 _144947 _144956 _144962 A B P f g p2 p l lt2 s h h1). Qed.
Lemma lem8230601 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term925 _144947 _144956 _144962 A B P p l lt2 s f h.
Proof. exact (fun g : A -> B => @lem8230600 _144947 _144956 _144962 A B P f g p l lt2 s h h1). Qed.
Lemma lem8230602 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term926 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (fun f : A -> B => @lem8230601 _144947 _144956 _144962 A B P f p l lt2 s h h1). Qed.
Lemma lem8230603 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : term927 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (fun h0 : term286 _144947 _144956 _144962 A B P p l lt2 s h => @lem8230602 _144947 _144956 _144962 A B P p l lt2 s h h0). Qed.
Lemma lem8230604 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term926 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (@lem8230603 _144947 _144956 _144962 A B P p l lt2 s h (@lem8227198 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8230605 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term928 _144947 _144956 _144962 A B P p l lt2 s h f.
Proof. exact (@lem8230604 _144947 _144956 _144962 A B P p l lt2 s h h1 f). Qed.
Lemma lem8230606 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) : (term928 _144947 _144956 _144962 A B P p l lt2 s h f) = (term925 _144947 _144956 _144962 A B P p l lt2 s f h).
Proof. exact (eq_refl (term928 _144947 _144956 _144962 A B P p l lt2 s h f)). Qed.
Lemma lem8230607 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term925 _144947 _144956 _144962 A B P p l lt2 s f h.
Proof. exact (EQ_MP (@lem8230606 _144947 _144956 _144962 A B P p l lt2 s f h) (@lem8230605 _144947 _144956 _144962 A B P f p l lt2 s h h1)). Qed.
Lemma lem8230608 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term929 _144947 _144956 _144962 A B P p l lt2 s f h g.
Proof. exact (@lem8230607 _144947 _144956 _144962 A B P f p l lt2 s h h1 g). Qed.
Lemma lem8230609 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) : (term929 _144947 _144956 _144962 A B P p l lt2 s f h g) = (term924 _144947 _144956 _144962 A B P p l lt2 s f h g).
Proof. exact (eq_refl (term929 _144947 _144956 _144962 A B P p l lt2 s f h g)). Qed.
Lemma lem8230610 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term924 _144947 _144956 _144962 A B P p l lt2 s f h g.
Proof. exact (EQ_MP (@lem8230609 _144947 _144956 _144962 A B P p l lt2 s f h g) (@lem8230608 _144947 _144956 _144962 A B P f g p l lt2 s h h1)). Qed.
Lemma lem8230611 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term930 _144947 _144956 _144962 A B P p l lt2 s f h g p2.
Proof. exact (@lem8230610 _144947 _144956 _144962 A B P f g p l lt2 s h h1 p2). Qed.
Lemma lem8230612 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) : (term930 _144947 _144956 _144962 A B P p l lt2 s f h g p2) = (term923 _144947 _144956 _144962 A B P p l lt2 s f h g p2).
Proof. exact (eq_refl (term930 _144947 _144956 _144962 A B P p l lt2 s f h g p2)). Qed.
Lemma lem8230613 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term923 _144947 _144956 _144962 A B P p l lt2 s f h g p2.
Proof. exact (EQ_MP (@lem8230612 _144947 _144956 _144962 A B P p l lt2 s f h g p2) (@lem8230611 _144947 _144956 _144962 A B P f g p2 p l lt2 s h h1)). Qed.
Lemma lem8230614 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term931 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (@lem8230613 _144947 _144956 _144962 A B P f g p2 p l lt2 s h h1 p1). Qed.
Lemma lem8230615 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (h : type889 _144956 _144962 A B P) (g : A -> B) (p2 : P) (p1 : _144962) : (term931 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) = (term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1).
Proof. exact (eq_refl (term931 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1)). Qed.
Lemma lem8230618 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (EQ_MP (@lem8230615 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1) (@lem8230614 _144947 _144956 _144962 A B P f g p2 p1 p l lt2 s h h1)). Qed.
Lemma lem8230619 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (p2 : P) (p1 : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term275 _144947 _144956 _144962 A B P p l lt2 s f h g p2 p1.
Proof. exact (@lem8230618 _144947 _144956 _144962 A B P f g p2 p1 p l lt2 s h h1). Qed.
Lemma lem8230620 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (x : _144962) (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) : term275 _144947 _144956 _144962 A B P p l lt2 s f h g a x.
Proof. exact (@lem8230619 _144947 _144956 _144962 A B P f g a x p l lt2 s h h1). Qed.
Lemma lem8230635 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = ((p f a) = True).
Proof. exact (@lem7 (p f a)). Qed.
Lemma lem8230637 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = ((p g a) = True).
Proof. exact (@lem7 (p g a)). Qed.
Lemma lem8230639 {_144947 A B P : Type'} (z : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term416 _144947 A B P lt2 s a f g z.
Proof. exact (@lem8227203 _144947 A B P lt2 s a f g h1 z). Qed.
Lemma lem8230640 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term416 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term416 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230641 {_144947 A B P : Type'} (z : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term218 _144947 A B P lt2 s a f g z.
Proof. exact (EQ_MP (@lem8230640 _144947 A B P lt2 s a f g z) (@lem8230639 _144947 A B P z lt2 s a f g h1)). Qed.
Lemma lem8230642 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = ((term218 _144947 A B P lt2 s a f g z) = True).
Proof. exact (@lem7 (term218 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230644 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term564 _144962 A B P x l f a) = ((term564 _144962 A B P x l f a) = True).
Proof. exact (@lem7 (term564 _144962 A B P x l f a)). Qed.
Lemma lem8230651 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : (p f a) = True.
Proof. exact (EQ_MP (@lem8230635 A B P p f a) (@lem8227202 A B P p f a h1)). Qed.
Lemma lem8230652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230653 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : (term403 A B P p f a) = (and True).
Proof. exact (MK_COMB (@lem8230652) (@lem8230651 A B P p f a h1)). Qed.
Lemma lem8230655 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : (term564 _144962 A B P x l f a) = True.
Proof. exact (EQ_MP (@lem8230644 _144962 A B P x l f a) (@lem8230561 _144962 A B P x l f a h1)). Qed.
Lemma lem8230656 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) (h2 : p f a) : (term144 _144962 A B P p x l f a) = (True /\ True).
Proof. exact (MK_COMB (@lem8230653 A B P p f a h2) (@lem8230655 _144962 A B P x l f a h1)). Qed.
Lemma lem8230658 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8230659 : (True /\ True) = True.
Proof. exact (@lem8230658 True). Qed.
Lemma lem8230660 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) (h2 : p f a) : (term144 _144962 A B P p x l f a) = True.
Proof. exact (TRANS (@lem8230656 _144962 A B P x l p f a h1 h2) (@lem8230659)). Qed.
Lemma lem8230661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230662 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) (h2 : p f a) : (term174 _144962 A B P p x l f a) = (and True).
Proof. exact (MK_COMB (@lem8230661) (@lem8230660 _144962 A B P x l p f a h1 h2)). Qed.
Lemma lem8230668 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : (p g a) = True.
Proof. exact (EQ_MP (@lem8230637 A B P p g a) (@lem8227204 A B P p g a h1)). Qed.
Lemma lem8230669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230670 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : (term403 A B P p g a) = (and True).
Proof. exact (MK_COMB (@lem8230669) (@lem8230668 A B P p g a h1)). Qed.
Lemma lem8230671 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term564 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (eq_refl (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230672 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : (term144 _144962 A B P p x l g a) = (term932 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230670 A B P p g a h1) (@lem8230671 _144962 A B P x l g a)). Qed.
Lemma lem8230674 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8230675 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term932 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (@lem8230674 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230676 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : (term144 _144962 A B P p x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8230672 _144962 A B P x l p g a h1) (@lem8230675 _144962 A B P x l g a)). Qed.
Lemma lem8230677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8230678 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : (term174 _144962 A B P p x l g a) = (term933 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230677) (@lem8230676 _144962 A B P x l p g a h1)). Qed.
Lemma lem8230686 {_144947 A B P : Type'} (z : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : (term218 _144947 A B P lt2 s a f g z) = True.
Proof. exact (EQ_MP (@lem8230642 _144947 A B P lt2 s a f g z) (@lem8230641 _144947 A B P z lt2 s a f g h1)). Qed.
Lemma lem8230687 {_144947 A B P : Type'} (z : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : (term218 _144947 A B P lt2 s a f g z) = True.
Proof. exact (@lem8230686 _144947 A B P z lt2 s a f g h1). Qed.
Lemma lem8230688 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : (term220 _144947 A B P lt2 s a f g) = (term934 A).
Proof. exact (fun_ext (fun z : A => @lem8230687 _144947 A B P z lt2 s a f g h1)). Qed.
Lemma lem8230689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8230690 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : (term222 _144947 A B P lt2 s a f g) = (term935 A).
Proof. exact (MK_COMB (@lem8230689 A) (@lem8230688 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8230692 {A : Type'} (t : Prop) : (term936 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8230693 {A : Type'} (t : Prop) : (term936 A t) = t.
Proof. exact (@lem8230692 A t). Qed.
Lemma lem8230694 {A : Type'} : (term935 A) = True.
Proof. exact (@lem8230693 A True). Qed.
Lemma lem8230695 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : (term222 _144947 A B P lt2 s a f g) = True.
Proof. exact (TRANS (@lem8230690 _144947 A B P lt2 s a f g h1) (@lem8230694 A)). Qed.
Lemma lem8230696 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : p g a) : (term224 _144947 _144962 A B P p x l lt2 s a f g) = (term937 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230678 _144962 A B P x l p g a h2) (@lem8230695 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8230698 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8230699 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term937 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (@lem8230698 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230700 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : p g a) : (term224 _144947 _144962 A B P p x l lt2 s a f g) = (term564 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8230696 _144947 _144962 A B P x l lt2 s f p g a h1 h2) (@lem8230699 _144962 A B P x l g a)). Qed.
Lemma lem8230701 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term564 _144962 A B P x l f a) (h3 : p f a) (h4 : p g a) : (term226 _144947 _144962 A B P p x l lt2 s a f g) = (term932 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230662 _144962 A B P x l p f a h2 h3) (@lem8230700 _144947 _144962 A B P x l lt2 s f p g a h1 h4)). Qed.
Lemma lem8230703 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8230704 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term932 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (@lem8230703 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230705 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term564 _144962 A B P x l f a) (h3 : p f a) (h4 : p g a) : (term226 _144947 _144962 A B P p x l lt2 s a f g) = (term564 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8230701 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4) (@lem8230704 _144962 A B P x l g a)). Qed.
Lemma lem8230706 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term564 _144962 A B P x l f a) (h3 : p f a) (h4 : p g a) : (term564 _144962 A B P x l g a) = (term226 _144947 _144962 A B P p x l lt2 s a f g).
Proof. exact (SYM (@lem8230705 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4)). Qed.
Lemma lem8230708 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8230709 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term564 _144962 A B P x l g a) = (term938 _144962 A B P x l g a).
Proof. exact (@lem8230708 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230710 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term938 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (SYM (@lem8230709 _144962 A B P x l g a)). Qed.
Lemma lem8230711 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term939 _144962 A B P x l g a) : term939 _144962 A B P x l g a.
Proof. exact (h1). Qed.
Lemma lem8230714 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term940 _144947 _144962 A B P p lt2 s f x l g a) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (h1). Qed.
Lemma lem8230715 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : term940 _144947 _144962 A B P p lt2 s f x l g a => @lem8230714 _144947 _144962 A B P p lt2 s f x l g a h0). Qed.
Lemma lem8230716 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term941 _144947 _144962 A B P p lt2 s f x l g a) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (h1). Qed.
Lemma lem8230717 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term940 _144947 _144962 A B P p lt2 s f x l g a) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (h1). Qed.
Lemma lem8230718 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term940 _144947 _144962 A B P p lt2 s f x l g a) (h2 : term941 _144947 _144962 A B P p lt2 s f x l g a) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8230716 _144947 _144962 A B P p lt2 s f x l g a h2 (@lem8230717 _144947 _144962 A B P p lt2 s f x l g a h1)). Qed.
Lemma lem8230719 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term940 _144947 _144962 A B P p lt2 s f x l g a) : term942 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : term941 _144947 _144962 A B P p lt2 s f x l g a => @lem8230718 _144947 _144962 A B P p lt2 s f x l g a h1 h0). Qed.
Lemma lem8230720 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term941 _144947 _144962 A B P p lt2 s f x l g a) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (h1). Qed.
Lemma lem8230721 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term940 _144947 _144962 A B P p lt2 s f x l g a) (h2 : term941 _144947 _144962 A B P p lt2 s f x l g a) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8230719 _144947 _144962 A B P p lt2 s f x l g a h1 (@lem8230720 _144947 _144962 A B P p lt2 s f x l g a h2)). Qed.
Lemma lem8230722 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term941 _144947 _144962 A B P p lt2 s f x l g a) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : term940 _144947 _144962 A B P p lt2 s f x l g a => @lem8230721 _144947 _144962 A B P p lt2 s f x l g a h0 h1). Qed.
Lemma lem8230723 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term943 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : term941 _144947 _144962 A B P p lt2 s f x l g a => @lem8230722 _144947 _144962 A B P p lt2 s f x l g a h0). Qed.
Lemma lem8230726 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8230723 _144947 _144962 A B P p lt2 s f x l g a (@lem8230715 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230727 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term941 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8230726 _144947 _144962 A B P p lt2 s f x l g a). Qed.
Lemma lem8230801 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8230802 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term938 _144962 A B P x l g a) = (term944 _144962 A B P x l g a).
Proof. exact (@lem8230801 (term939 _144962 A B P x l g a)). Qed.
Lemma lem8230804 (t : Prop) : (term36 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8230805 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term944 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (@lem8230804 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8230806 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term938 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8230802 _144962 A B P x l g a) (@lem8230805 _144962 A B P x l g a)). Qed.
Lemma lem8230807 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term912 _144962 A B P x l f a) = (term912 _144962 A B P x l f a).
Proof. exact (eq_refl (term912 _144962 A B P x l f a)). Qed.
Lemma lem8230808 {_144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term945 _144962 A B P f x l g a) = (term946 _144962 A B P f x l g a).
Proof. exact (MK_COMB (@lem8230807 _144962 A B P x l f a) (@lem8230806 _144962 A B P x l g a)). Qed.
Lemma lem8230811 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term358 _144947 A B P lt2 s a f g) = (term358 _144947 A B P lt2 s a f g).
Proof. exact (eq_refl (term358 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8230812 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term947 _144947 _144962 A B P lt2 s f x l g a) = (term948 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230811 _144947 A B P lt2 s a f g) (@lem8230808 _144962 A B P f x l g a)). Qed.
Lemma lem8230815 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term361 A B P p g a) = (term361 A B P p g a).
Proof. exact (eq_refl (term361 A B P p g a)). Qed.
Lemma lem8230816 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term949 _144947 _144962 A B P p lt2 s f x l g a) = (term950 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230815 A B P p g a) (@lem8230812 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230819 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term361 A B P p f a) = (term361 A B P p f a).
Proof. exact (eq_refl (term361 A B P p f a)). Qed.
Lemma lem8230820 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term951 _144947 _144962 A B P p lt2 s f x l g a) = (term952 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230819 A B P p f a) (@lem8230816 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230823 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term369 _144947 _144962 A B P p lt2 s l) = (term369 _144947 _144962 A B P p lt2 s l).
Proof. exact (eq_refl (term369 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8230824 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term940 _144947 _144962 A B P p lt2 s f x l g a) = (term953 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230823 _144947 _144962 A B P p lt2 s l) (@lem8230820 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230827 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term954 _144947 _144962 A B P lt2 s f x l g a) = (term955 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8230824 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230828 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8230829 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term956 _144947 _144962 A B P lt2 s f x l g a) = (term957 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230828 A B P) (@lem8230827 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230834 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term958 _144947 _144962 A B P s f x l g a) = (term959 _144947 _144962 A B P s f x l g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144947 A => @lem8230829 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230835 {_144947 A : Type'} : (@all (A -> _144947 -> Prop)) = (@all (A -> _144947 -> Prop)).
Proof. exact (eq_refl (@all (A -> _144947 -> Prop))). Qed.
Lemma lem8230836 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term960 _144947 _144962 A B P s f x l g a) = (term961 _144947 _144962 A B P s f x l g a).
Proof. exact (MK_COMB (@lem8230835 _144947 A) (@lem8230834 _144947 _144962 A B P s f x l g a)). Qed.
Lemma lem8230841 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term962 _144947 _144962 A B P f x l g a) = (term963 _144947 _144962 A B P f x l g a).
Proof. exact (fun_ext (fun s : P -> _144947 => @lem8230836 _144947 _144962 A B P s f x l g a)). Qed.
Lemma lem8230842 {_144947 P : Type'} : (@all (P -> _144947)) = (@all (P -> _144947)).
Proof. exact (eq_refl (@all (P -> _144947))). Qed.
Lemma lem8230843 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term964 _144947 _144962 A B P f x l g a) = (term965 _144947 _144962 A B P f x l g a).
Proof. exact (MK_COMB (@lem8230842 _144947 P) (@lem8230841 _144947 _144962 A B P f x l g a)). Qed.
Lemma lem8230848 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term966 _144947 _144962 A B P x l g a) = (term967 _144947 _144962 A B P x l g a).
Proof. exact (fun_ext (fun f : A -> B => @lem8230843 _144947 _144962 A B P f x l g a)). Qed.
Lemma lem8230849 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230850 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term968 _144947 _144962 A B P x l g a) = (term969 _144947 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230849 A B) (@lem8230848 _144947 _144962 A B P x l g a)). Qed.
Lemma lem8230855 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term970 _144947 _144962 A B P l g a) = (term971 _144947 _144962 A B P l g a).
Proof. exact (fun_ext (fun x : _144962 => @lem8230850 _144947 _144962 A B P x l g a)). Qed.
Lemma lem8230856 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8230857 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term972 _144947 _144962 A B P l g a) = (term973 _144947 _144962 A B P l g a).
Proof. exact (MK_COMB (@lem8230856 _144962) (@lem8230855 _144947 _144962 A B P l g a)). Qed.
Lemma lem8230862 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : (term974 _144947 _144962 A B P g a) = (term975 _144947 _144962 A B P g a).
Proof. exact (fun_ext (fun l : type815 _144962 A B P => @lem8230857 _144947 _144962 A B P l g a)). Qed.
Lemma lem8230863 {_144962 A B P : Type'} : (@all ((A -> B) -> P -> list _144962)) = (@all ((A -> B) -> P -> list _144962)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> list _144962))). Qed.
Lemma lem8230864 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : (term976 _144947 _144962 A B P g a) = (term977 _144947 _144962 A B P g a).
Proof. exact (MK_COMB (@lem8230863 _144962 A B P) (@lem8230862 _144947 _144962 A B P g a)). Qed.
Lemma lem8230869 {_144947 _144962 A B P : Type'} (a : P) : (term978 _144947 _144962 A B P a) = (term979 _144947 _144962 A B P a).
Proof. exact (fun_ext (fun g : A -> B => @lem8230864 _144947 _144962 A B P g a)). Qed.
Lemma lem8230870 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230871 {_144947 _144962 A B P : Type'} (a : P) : (term980 _144947 _144962 A B P a) = (term981 _144947 _144962 A B P a).
Proof. exact (MK_COMB (@lem8230870 A B) (@lem8230869 _144947 _144962 A B P a)). Qed.
Lemma lem8230876 {_144947 _144962 A B P : Type'} : (term982 _144947 _144962 A B P) = (term983 _144947 _144962 A B P).
Proof. exact (fun_ext (fun a : P => @lem8230871 _144947 _144962 A B P a)). Qed.
Lemma lem8230877 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8230886 {_144947 _144962 A B P : Type'} : (term984 _144947 _144962 A B P) = (term985 _144947 _144962 A B P).
Proof. exact (MK_COMB (@lem8230877 P) (@lem8230876 _144947 _144962 A B P)). Qed.
Lemma lem8230891 {_144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term946 _144962 A B P f x l g a) = (term946 _144962 A B P f x l g a).
Proof. exact (eq_refl (term946 _144962 A B P f x l g a)). Qed.
Lemma lem8230896 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term218 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230897 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term220 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8230896 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8230899 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term222 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8230898 A) (@lem8230897 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8230900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230901 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term358 _144947 A B P lt2 s a f g) = (term358 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8230900) (@lem8230899 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8230902 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term948 _144947 _144962 A B P lt2 s f x l g a) = (term948 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230901 _144947 A B P lt2 s a f g) (@lem8230891 _144962 A B P f x l g a)). Qed.
Lemma lem8230905 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term361 A B P p g a) = (term361 A B P p g a).
Proof. exact (eq_refl (term361 A B P p g a)). Qed.
Lemma lem8230906 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term950 _144947 _144962 A B P p lt2 s f x l g a) = (term950 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230905 A B P p g a) (@lem8230902 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230909 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term361 A B P p f a) = (term361 A B P p f a).
Proof. exact (eq_refl (term361 A B P p f a)). Qed.
Lemma lem8230910 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term952 _144947 _144962 A B P p lt2 s f x l g a) = (term952 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230909 A B P p f a) (@lem8230906 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230911 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8230916 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term218 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230917 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term220 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8230916 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8230918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8230919 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term222 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8230918 A) (@lem8230917 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8230922 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term403 A B P p g a) = (term403 A B P p g a).
Proof. exact (eq_refl (term403 A B P p g a)). Qed.
Lemma lem8230923 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term348 _144947 A B P p lt2 s a f g) = (term348 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8230922 A B P p g a) (@lem8230919 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8230926 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term403 A B P p f a) = (term403 A B P p f a).
Proof. exact (eq_refl (term403 A B P p f a)). Qed.
Lemma lem8230927 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term347 _144947 A B P p lt2 s a f g) = (term347 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8230926 A B P p f a) (@lem8230923 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8230928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230929 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term311 _144947 A B P p lt2 s a f g) = (term311 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8230928) (@lem8230927 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8230930 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term404 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8230929 _144947 A B P p lt2 s a f g) (@lem8230911 _144962 A B P f l g a)). Qed.
Lemma lem8230931 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term405 _144947 _144962 A B P p lt2 s f l g) = (term405 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8230930 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8230932 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8230933 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term406 _144947 _144962 A B P p lt2 s f l g) = (term406 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8230932 P) (@lem8230931 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8230934 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term407 _144947 _144962 A B P p lt2 s f l) = (term407 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8230933 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8230935 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230936 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term408 _144947 _144962 A B P p lt2 s f l) = (term408 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8230935 A B) (@lem8230934 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8230937 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term409 _144947 _144962 A B P p lt2 s l) = (term409 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8230936 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8230938 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230939 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term87 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8230938 A B) (@lem8230937 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8230940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8230941 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term369 _144947 _144962 A B P p lt2 s l) = (term369 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8230940) (@lem8230939 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8230942 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term953 _144947 _144962 A B P p lt2 s f x l g a) = (term953 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230941 _144947 _144962 A B P p lt2 s l) (@lem8230910 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230943 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term955 _144947 _144962 A B P lt2 s f x l g a) = (term955 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8230942 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8230944 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8230945 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term957 _144947 _144962 A B P lt2 s f x l g a) = (term957 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (MK_COMB (@lem8230944 A B P) (@lem8230943 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230946 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term959 _144947 _144962 A B P s f x l g a) = (term959 _144947 _144962 A B P s f x l g a).
Proof. exact (fun_ext (fun lt2 : type1470 _144947 A => @lem8230945 _144947 _144962 A B P lt2 s f x l g a)). Qed.
Lemma lem8230947 {_144947 A : Type'} : (@all (A -> _144947 -> Prop)) = (@all (A -> _144947 -> Prop)).
Proof. exact (eq_refl (@all (A -> _144947 -> Prop))). Qed.
Lemma lem8230948 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term961 _144947 _144962 A B P s f x l g a) = (term961 _144947 _144962 A B P s f x l g a).
Proof. exact (MK_COMB (@lem8230947 _144947 A) (@lem8230946 _144947 _144962 A B P s f x l g a)). Qed.
Lemma lem8230949 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term963 _144947 _144962 A B P f x l g a) = (term963 _144947 _144962 A B P f x l g a).
Proof. exact (fun_ext (fun s : P -> _144947 => @lem8230948 _144947 _144962 A B P s f x l g a)). Qed.
Lemma lem8230950 {_144947 P : Type'} : (@all (P -> _144947)) = (@all (P -> _144947)).
Proof. exact (eq_refl (@all (P -> _144947))). Qed.
Lemma lem8230951 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term965 _144947 _144962 A B P f x l g a) = (term965 _144947 _144962 A B P f x l g a).
Proof. exact (MK_COMB (@lem8230950 _144947 P) (@lem8230949 _144947 _144962 A B P f x l g a)). Qed.
Lemma lem8230952 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term967 _144947 _144962 A B P x l g a) = (term967 _144947 _144962 A B P x l g a).
Proof. exact (fun_ext (fun f : A -> B => @lem8230951 _144947 _144962 A B P f x l g a)). Qed.
Lemma lem8230953 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230954 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term969 _144947 _144962 A B P x l g a) = (term969 _144947 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8230953 A B) (@lem8230952 _144947 _144962 A B P x l g a)). Qed.
Lemma lem8230955 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term971 _144947 _144962 A B P l g a) = (term971 _144947 _144962 A B P l g a).
Proof. exact (fun_ext (fun x : _144962 => @lem8230954 _144947 _144962 A B P x l g a)). Qed.
Lemma lem8230956 {_144962 : Type'} : (@all _144962) = (@all _144962).
Proof. exact (eq_refl (@all _144962)). Qed.
Lemma lem8230957 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term973 _144947 _144962 A B P l g a) = (term973 _144947 _144962 A B P l g a).
Proof. exact (MK_COMB (@lem8230956 _144962) (@lem8230955 _144947 _144962 A B P l g a)). Qed.
Lemma lem8230958 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : (term975 _144947 _144962 A B P g a) = (term975 _144947 _144962 A B P g a).
Proof. exact (fun_ext (fun l : type815 _144962 A B P => @lem8230957 _144947 _144962 A B P l g a)). Qed.
Lemma lem8230959 {_144962 A B P : Type'} : (@all ((A -> B) -> P -> list _144962)) = (@all ((A -> B) -> P -> list _144962)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> list _144962))). Qed.
Lemma lem8230960 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : (term977 _144947 _144962 A B P g a) = (term977 _144947 _144962 A B P g a).
Proof. exact (MK_COMB (@lem8230959 _144962 A B P) (@lem8230958 _144947 _144962 A B P g a)). Qed.
Lemma lem8230961 {_144947 _144962 A B P : Type'} (a : P) : (term979 _144947 _144962 A B P a) = (term979 _144947 _144962 A B P a).
Proof. exact (fun_ext (fun g : A -> B => @lem8230960 _144947 _144962 A B P g a)). Qed.
Lemma lem8230962 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8230963 {_144947 _144962 A B P : Type'} (a : P) : (term981 _144947 _144962 A B P a) = (term981 _144947 _144962 A B P a).
Proof. exact (MK_COMB (@lem8230962 A B) (@lem8230961 _144947 _144962 A B P a)). Qed.
Lemma lem8230964 {_144947 _144962 A B P : Type'} : (term983 _144947 _144962 A B P) = (term983 _144947 _144962 A B P).
Proof. exact (fun_ext (fun a : P => @lem8230963 _144947 _144962 A B P a)). Qed.
Lemma lem8230965 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8230966 {_144947 _144962 A B P : Type'} : (term985 _144947 _144962 A B P) = (term985 _144947 _144962 A B P).
Proof. exact (MK_COMB (@lem8230965 P) (@lem8230964 _144947 _144962 A B P)). Qed.
Lemma lem8231067 {_144947 _144962 A B P : Type'} : (term984 _144947 _144962 A B P) = (term985 _144947 _144962 A B P).
Proof. exact (TRANS (@lem8230886 _144947 _144962 A B P) (@lem8230966 _144947 _144962 A B P)). Qed.
Lemma lem8231068 {_144947 _144962 A B P : Type'} : (term985 _144947 _144962 A B P) = (term984 _144947 _144962 A B P).
Proof. exact (SYM (@lem8231067 _144947 _144962 A B P)). Qed.
Lemma lem8231069 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term87 _144947 _144962 A B P p lt2 s l.
Proof. exact (h1). Qed.
Lemma lem8231072 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term222 _144947 A B P lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8231075 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8231076 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term564 _144962 A B P x l g a) = (term938 _144962 A B P x l g a).
Proof. exact (@lem8231075 (term564 _144962 A B P x l g a)). Qed.
Lemma lem8231077 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term938 _144962 A B P x l g a) = (term564 _144962 A B P x l g a).
Proof. exact (SYM (@lem8231076 _144962 A B P x l g a)). Qed.
Lemma lem8231078 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term939 _144962 A B P x l g a) : term939 _144962 A B P x l g a.
Proof. exact (h1). Qed.
Lemma lem8231087 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term410 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term214 _144947 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8231088 {A : Type'} (P : A -> Prop) : (term412 A P) = (term413 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8231089 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s a f g) = (term415 _144947 A B P lt2 s a f g).
Proof. exact (@lem8231088 A (term220 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231090 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term416 _144947 A B P lt2 s a f g z) = (term218 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term416 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231092 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s a f g z) = (term410 _144947 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8231091) (@lem8231090 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231093 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term417 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8231092 _144947 A B P lt2 s a f g z) (@lem8231087 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231094 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term418 _144947 A B P lt2 s a f g) = (term419 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231093 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231095 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231096 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term415 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8231095 A) (@lem8231094 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231097 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term414 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8231089 _144947 A B P lt2 s a f g) (@lem8231096 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231099 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8231100 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term422 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231099 A B P p g a) (@lem8231097 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231101 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term424 _144947 A B P p lt2 s a f g) = (term422 _144947 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term222 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231102 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term424 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8231101 _144947 A B P p lt2 s a f g) (@lem8231100 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231104 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8231105 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term425 _144947 A B P p lt2 s a f g) = (term426 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231104 A B P p f a) (@lem8231102 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231106 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term427 _144947 A B P p lt2 s a f g) = (term425 _144947 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term348 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231107 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term427 _144947 A B P p lt2 s a f g) = (term426 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8231106 _144947 A B P p lt2 s a f g) (@lem8231105 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231108 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8231109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231110 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term428 _144947 A B P p lt2 s a f g) = (term429 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231109) (@lem8231107 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231111 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term430 _144947 _144962 A B P p lt2 s f l g a) = (term431 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231110 _144947 A B P p lt2 s a f g) (@lem8231108 _144962 A B P f l g a)). Qed.
Lemma lem8231112 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term430 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (@lem17265 (term347 _144947 A B P p lt2 s a f g) ((l f a) = (l g a))). Qed.
Lemma lem8231113 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term404 _144947 _144962 A B P p lt2 s f l g a) = (term431 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (TRANS (@lem8231112 _144947 _144962 A B P p lt2 s f l g a) (@lem8231111 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231114 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term405 _144947 _144962 A B P p lt2 s f l g) = (term432 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8231113 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231115 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231116 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term406 _144947 _144962 A B P p lt2 s f l g) = (term433 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231115 P) (@lem8231114 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231117 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term407 _144947 _144962 A B P p lt2 s f l) = (term434 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231116 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231118 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231119 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term408 _144947 _144962 A B P p lt2 s f l) = (term435 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231118 A B) (@lem8231117 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231120 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term409 _144947 _144962 A B P p lt2 s l) = (term436 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231119 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231121 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231122 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term437 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8231121 A B) (@lem8231120 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231229 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8231230 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8231229 A P Q). Qed.
Lemma lem8231231 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term440 _144947 A B P p lt2 s a f g) = (term441 _144947 A B P p lt2 s a f g).
Proof. exact (@lem8231230 A (term442 A B P p g a) (term419 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231232 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231233 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term444 _144947 A B P lt2 s a f g) = (term419 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231232 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231235 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term445 _144947 A B P lt2 s a f g) = (term420 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8231234 A) (@lem8231233 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231236 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8231237 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term440 _144947 A B P p lt2 s a f g) = (term423 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231236 A B P p g a) (@lem8231235 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231239 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term446 _144947 A B P p lt2 s a f g) = (term447 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231238) (@lem8231237 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231240 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term443 _144947 A B P lt2 s a f g z) = (term411 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term443 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231241 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term421 A B P p g a).
Proof. exact (eq_refl (term421 A B P p g a)). Qed.
Lemma lem8231242 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term448 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8231241 A B P p g a) (@lem8231240 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231243 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term450 _144947 A B P p lt2 s a f g) = (term451 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231242 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231245 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term441 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231244 A) (@lem8231243 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231246 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : ((term440 _144947 A B P p lt2 s a f g) = (term441 _144947 A B P p lt2 s a f g)) = ((term423 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8231239 _144947 A B P p lt2 s a f g) (@lem8231245 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231247 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term423 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8231246 _144947 A B P p lt2 s a f g) (@lem8231231 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231248 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8231249 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term426 _144947 A B P p lt2 s a f g) = (term453 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231248 A B P p f a) (@lem8231247 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231251 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8231252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term438 A P Q) = (term439 A P Q).
Proof. exact (@lem8231251 A P Q). Qed.
Lemma lem8231253 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term454 _144947 A B P p lt2 s a f g) = (term455 _144947 A B P p lt2 s a f g).
Proof. exact (@lem8231252 A (term442 A B P p f a) (term451 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231254 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term456 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term456 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231255 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term457 _144947 A B P p lt2 s a f g) = (term451 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231254 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231256 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231257 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term458 _144947 A B P p lt2 s a f g) = (term452 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231256 A) (@lem8231255 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231258 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8231259 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term454 _144947 A B P p lt2 s a f g) = (term453 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231258 A B P p f a) (@lem8231257 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231261 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term459 _144947 A B P p lt2 s a f g) = (term460 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231260) (@lem8231259 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231262 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term456 _144947 A B P p lt2 s a f g z) = (term449 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term456 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231263 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term421 A B P p f a).
Proof. exact (eq_refl (term421 A B P p f a)). Qed.
Lemma lem8231264 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term461 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8231263 A B P p f a) (@lem8231262 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231265 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term463 _144947 A B P p lt2 s a f g) = (term464 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231264 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231266 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231267 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term455 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231266 A) (@lem8231265 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231268 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : ((term454 _144947 A B P p lt2 s a f g) = (term455 _144947 A B P p lt2 s a f g)) = ((term453 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8231261 _144947 A B P p lt2 s a f g) (@lem8231267 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231269 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term453 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8231268 _144947 A B P p lt2 s a f g) (@lem8231253 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231270 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term426 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8231249 _144947 A B P p lt2 s a f g) (@lem8231269 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231272 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term429 _144947 A B P p lt2 s a f g) = (term466 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231271) (@lem8231270 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231273 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8231274 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term431 _144947 _144962 A B P p lt2 s f l g a) = (term467 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231272 _144947 A B P p lt2 s a f g) (@lem8231273 _144962 A B P f l g a)). Qed.
Lemma lem8231276 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8231277 {A : Type'} (P : A -> Prop) (Q : Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (@lem8231276 A P Q). Qed.
Lemma lem8231278 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term470 _144947 _144962 A B P p lt2 s f l g a) = (term471 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (@lem8231277 A (term464 _144947 A B P p lt2 s a f g) ((l f a) = (l g a))). Qed.
Lemma lem8231279 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term472 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term472 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231280 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term473 _144947 A B P p lt2 s a f g) = (term464 _144947 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231279 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231281 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231282 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term474 _144947 A B P p lt2 s a f g) = (term465 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231281 A) (@lem8231280 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231284 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term475 _144947 A B P p lt2 s a f g) = (term466 _144947 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8231283) (@lem8231282 _144947 A B P p lt2 s a f g)). Qed.
Lemma lem8231285 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8231286 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term470 _144947 _144962 A B P p lt2 s f l g a) = (term467 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231284 _144947 A B P p lt2 s a f g) (@lem8231285 _144962 A B P f l g a)). Qed.
Lemma lem8231287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231288 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term476 _144947 _144962 A B P p lt2 s f l g a) = (term477 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231287) (@lem8231286 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231289 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term472 _144947 A B P p lt2 s a f g z) = (term462 _144947 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term472 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231291 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term478 _144947 A B P p lt2 s a f g z) = (term479 _144947 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8231290) (@lem8231289 _144947 A B P p lt2 s a f g z)). Qed.
Lemma lem8231292 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((l f a) = (l g a)).
Proof. exact (eq_refl ((l f a) = (l g a))). Qed.
Lemma lem8231293 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term480 _144947 _144962 A B P p lt2 s z f l g a) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (MK_COMB (@lem8231291 _144947 A B P p lt2 s a f g z) (@lem8231292 _144962 A B P f l g a)). Qed.
Lemma lem8231294 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term482 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun z : A => @lem8231293 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231295 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231296 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term471 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231295 A) (@lem8231294 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231297 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term470 _144947 _144962 A B P p lt2 s f l g a) = (term471 _144947 _144962 A B P p lt2 s f l g a)) = ((term467 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a)).
Proof. exact (MK_COMB (@lem8231288 _144947 _144962 A B P p lt2 s f l g a) (@lem8231296 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231298 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term467 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (EQ_MP (@lem8231297 _144947 _144962 A B P p lt2 s f l g a) (@lem8231278 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231299 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term431 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (TRANS (@lem8231274 _144947 _144962 A B P p lt2 s f l g a) (@lem8231298 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231300 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term432 _144947 _144962 A B P p lt2 s f l g) = (term485 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8231299 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231301 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231302 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term433 _144947 _144962 A B P p lt2 s f l g) = (term486 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231301 P) (@lem8231300 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231304 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8231305 {A P : Type'} (P' : type1470 A P) : (term489 A P P') = (term490 A P P').
Proof. exact (@lem8231304 P A P'). Qed.
Lemma lem8231306 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term491 _144947 _144962 A B P p lt2 s f l g) = (term492 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (@lem8231305 A P (term493 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231307 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term494 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (eq_refl (term494 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231308 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8231309 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (z : A) : (term495 _144947 _144962 A B P p lt2 s f l g a z) = (term496 _144947 _144962 A B P p lt2 s f l g a z).
Proof. exact (MK_COMB (@lem8231307 _144947 _144962 A B P p lt2 s f l g a) (@lem8231308 A z)). Qed.
Lemma lem8231310 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term496 _144947 _144962 A B P p lt2 s f l g a z) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (eq_refl (term496 _144947 _144962 A B P p lt2 s f l g a z)). Qed.
Lemma lem8231311 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term495 _144947 _144962 A B P p lt2 s f l g a z) = (term481 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (TRANS (@lem8231309 _144947 _144962 A B P p lt2 s f l g a z) (@lem8231310 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231312 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term497 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (fun_ext (fun z : A => @lem8231311 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231313 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8231314 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term498 _144947 _144962 A B P p lt2 s f l g a) = (term484 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (MK_COMB (@lem8231313 A) (@lem8231312 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231315 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term499 _144947 _144962 A B P p lt2 s f l g) = (term485 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun a : P => @lem8231314 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231316 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231317 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term491 _144947 _144962 A B P p lt2 s f l g) = (term486 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231316 P) (@lem8231315 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231319 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term500 _144947 _144962 A B P p lt2 s f l g) = (term501 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231318) (@lem8231317 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231320 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term494 _144947 _144962 A B P p lt2 s f l g a) = (term483 _144947 _144962 A B P p lt2 s f l g a).
Proof. exact (eq_refl (term494 _144947 _144962 A B P p lt2 s f l g a)). Qed.
Lemma lem8231321 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8231322 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (z : P -> A) (a : P) : (term502 _144947 _144962 A B P p lt2 s f l g z a) = (term503 _144947 _144962 A B P p lt2 s f l g z a).
Proof. exact (MK_COMB (@lem8231320 _144947 _144962 A B P p lt2 s f l g a) (@lem8231321 A P z a)). Qed.
Lemma lem8231323 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term503 _144947 _144962 A B P p lt2 s f l g z a) = (term504 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (eq_refl (term503 _144947 _144962 A B P p lt2 s f l g z a)). Qed.
Lemma lem8231324 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term502 _144947 _144962 A B P p lt2 s f l g z a) = (term504 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (TRANS (@lem8231322 _144947 _144962 A B P p lt2 s f l g z a) (@lem8231323 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231325 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term505 _144947 _144962 A B P p lt2 s f l g z) = (term506 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (fun_ext (fun a : P => @lem8231324 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231326 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231327 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term507 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (MK_COMB (@lem8231326 P) (@lem8231325 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231328 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term509 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun z : P -> A => @lem8231327 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231329 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8231330 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term492 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231329 A P) (@lem8231328 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231331 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : ((term491 _144947 _144962 A B P p lt2 s f l g) = (term492 _144947 _144962 A B P p lt2 s f l g)) = ((term486 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g)).
Proof. exact (MK_COMB (@lem8231319 _144947 _144962 A B P p lt2 s f l g) (@lem8231330 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231332 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term486 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (EQ_MP (@lem8231331 _144947 _144962 A B P p lt2 s f l g) (@lem8231306 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231333 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term433 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (TRANS (@lem8231302 _144947 _144962 A B P p lt2 s f l g) (@lem8231332 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231334 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term434 _144947 _144962 A B P p lt2 s f l) = (term512 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231333 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231335 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231336 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term435 _144947 _144962 A B P p lt2 s f l) = (term513 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231335 A B) (@lem8231334 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231338 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8231339 {A B P : Type'} (P' : type537 A B P) : (term514 A B P P') = (term515 A B P P').
Proof. exact (@lem8231338 (A -> B) (P -> A) P'). Qed.
Lemma lem8231340 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term516 _144947 _144962 A B P p lt2 s f l) = (term517 _144947 _144962 A B P p lt2 s f l).
Proof. exact (@lem8231339 A B P (term518 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231341 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term519 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (eq_refl (term519 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231342 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8231343 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (z : P -> A) : (term520 _144947 _144962 A B P p lt2 s f l g z) = (term521 _144947 _144962 A B P p lt2 s f l g z).
Proof. exact (MK_COMB (@lem8231341 _144947 _144962 A B P p lt2 s f l g) (@lem8231342 A P z)). Qed.
Lemma lem8231344 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term521 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (eq_refl (term521 _144947 _144962 A B P p lt2 s f l g z)). Qed.
Lemma lem8231345 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : P -> A) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term520 _144947 _144962 A B P p lt2 s f l g z) = (term508 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (TRANS (@lem8231343 _144947 _144962 A B P p lt2 s f l g z) (@lem8231344 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231346 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term522 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (fun_ext (fun z : P -> A => @lem8231345 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231347 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8231348 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term523 _144947 _144962 A B P p lt2 s f l g) = (term511 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (MK_COMB (@lem8231347 A P) (@lem8231346 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231349 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term524 _144947 _144962 A B P p lt2 s f l) = (term512 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231348 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231350 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231351 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term516 _144947 _144962 A B P p lt2 s f l) = (term513 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231350 A B) (@lem8231349 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231353 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term525 _144947 _144962 A B P p lt2 s f l) = (term526 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231352) (@lem8231351 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231354 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term519 _144947 _144962 A B P p lt2 s f l g) = (term510 _144947 _144962 A B P p lt2 s f l g).
Proof. exact (eq_refl (term519 _144947 _144962 A B P p lt2 s f l g)). Qed.
Lemma lem8231355 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8231356 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (z : type557 A B P) (g : A -> B) : (term527 _144947 _144962 A B P p lt2 s f l z g) = (term528 _144947 _144962 A B P p lt2 s f l z g).
Proof. exact (MK_COMB (@lem8231354 _144947 _144962 A B P p lt2 s f l g) (@lem8231355 A B P z g)). Qed.
Lemma lem8231357 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term528 _144947 _144962 A B P p lt2 s f l z g) = (term529 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (eq_refl (term528 _144947 _144962 A B P p lt2 s f l z g)). Qed.
Lemma lem8231358 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term527 _144947 _144962 A B P p lt2 s f l z g) = (term529 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (TRANS (@lem8231356 _144947 _144962 A B P p lt2 s f l z g) (@lem8231357 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231359 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term530 _144947 _144962 A B P p lt2 s f l z) = (term531 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231358 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231360 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231361 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term532 _144947 _144962 A B P p lt2 s f l z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (MK_COMB (@lem8231360 A B) (@lem8231359 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231362 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term534 _144947 _144962 A B P p lt2 s f l) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8231361 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231363 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8231364 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term517 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231363 A B P) (@lem8231362 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231365 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : ((term516 _144947 _144962 A B P p lt2 s f l) = (term517 _144947 _144962 A B P p lt2 s f l)) = ((term513 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l)).
Proof. exact (MK_COMB (@lem8231353 _144947 _144962 A B P p lt2 s f l) (@lem8231364 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231366 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term513 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (EQ_MP (@lem8231365 _144947 _144962 A B P p lt2 s f l) (@lem8231340 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231367 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term435 _144947 _144962 A B P p lt2 s f l) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (TRANS (@lem8231336 _144947 _144962 A B P p lt2 s f l) (@lem8231366 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231368 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term436 _144947 _144962 A B P p lt2 s l) = (term537 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231367 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231369 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231370 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term437 _144947 _144962 A B P p lt2 s l) = (term538 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8231369 A B) (@lem8231368 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231372 {A B : Type'} (P : type1413 A B) : (term487 A B P) = (term488 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8231373 {A B P : Type'} (P' : type495 A B P) : (term539 A B P P') = (term540 A B P P').
Proof. exact (@lem8231372 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8231374 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term541 _144947 _144962 A B P p lt2 s l) = (term542 _144947 _144962 A B P p lt2 s l).
Proof. exact (@lem8231373 A B P (term543 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231375 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term544 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (eq_refl (term544 _144947 _144962 A B P p lt2 s l f)). Qed.
Lemma lem8231376 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8231377 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) (z : type557 A B P) : (term545 _144947 _144962 A B P p lt2 s l f z) = (term546 _144947 _144962 A B P p lt2 s f l z).
Proof. exact (MK_COMB (@lem8231375 _144947 _144962 A B P p lt2 s f l) (@lem8231376 A B P z)). Qed.
Lemma lem8231378 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term546 _144947 _144962 A B P p lt2 s f l z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (eq_refl (term546 _144947 _144962 A B P p lt2 s f l z)). Qed.
Lemma lem8231379 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type557 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term545 _144947 _144962 A B P p lt2 s l f z) = (term533 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (TRANS (@lem8231377 _144947 _144962 A B P p lt2 s f l z) (@lem8231378 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231380 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term547 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8231379 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231381 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8231382 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term548 _144947 _144962 A B P p lt2 s l f) = (term536 _144947 _144962 A B P p lt2 s f l).
Proof. exact (MK_COMB (@lem8231381 A B P) (@lem8231380 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231383 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term549 _144947 _144962 A B P p lt2 s l) = (term537 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231382 _144947 _144962 A B P p lt2 s f l)). Qed.
Lemma lem8231384 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231385 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term541 _144947 _144962 A B P p lt2 s l) = (term538 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8231384 A B) (@lem8231383 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8231387 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term550 _144947 _144962 A B P p lt2 s l) = (term551 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8231386) (@lem8231385 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231388 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (l : type815 _144962 A B P) : (term544 _144947 _144962 A B P p lt2 s l f) = (term535 _144947 _144962 A B P p lt2 s f l).
Proof. exact (eq_refl (term544 _144947 _144962 A B P p lt2 s l f)). Qed.
Lemma lem8231389 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8231390 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (z : type518 A B P) (f : A -> B) : (term552 _144947 _144962 A B P p lt2 s l z f) = (term553 _144947 _144962 A B P p lt2 s l z f).
Proof. exact (MK_COMB (@lem8231388 _144947 _144962 A B P p lt2 s f l) (@lem8231389 A B P z f)). Qed.
Lemma lem8231391 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term553 _144947 _144962 A B P p lt2 s l z f) = (term554 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (eq_refl (term553 _144947 _144962 A B P p lt2 s l z f)). Qed.
Lemma lem8231392 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term552 _144947 _144962 A B P p lt2 s l z f) = (term554 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (TRANS (@lem8231390 _144947 _144962 A B P p lt2 s l z f) (@lem8231391 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231393 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term555 _144947 _144962 A B P p lt2 s l z) = (term556 _144947 _144962 A B P p lt2 s z l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231392 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231394 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231395 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term557 _144947 _144962 A B P p lt2 s l z) = (term558 _144947 _144962 A B P p lt2 s z l).
Proof. exact (MK_COMB (@lem8231394 A B) (@lem8231393 _144947 _144962 A B P p lt2 s z l)). Qed.
Lemma lem8231396 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term559 _144947 _144962 A B P p lt2 s l) = (term560 _144947 _144962 A B P p lt2 s l).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8231395 _144947 _144962 A B P p lt2 s z l)). Qed.
Lemma lem8231397 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8231398 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term542 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (MK_COMB (@lem8231397 A B P) (@lem8231396 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231399 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : ((term541 _144947 _144962 A B P p lt2 s l) = (term542 _144947 _144962 A B P p lt2 s l)) = ((term538 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l)).
Proof. exact (MK_COMB (@lem8231387 _144947 _144962 A B P p lt2 s l) (@lem8231398 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231400 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term538 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (EQ_MP (@lem8231399 _144947 _144962 A B P p lt2 s l) (@lem8231374 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231402 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term437 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (TRANS (@lem8231370 _144947 _144962 A B P p lt2 s l) (@lem8231400 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231403 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) : (term87 _144947 _144962 A B P p lt2 s l) = (term561 _144947 _144962 A B P p lt2 s l).
Proof. exact (TRANS (@lem8231122 _144947 _144962 A B P p lt2 s l) (@lem8231402 _144947 _144962 A B P p lt2 s l)). Qed.
Lemma lem8231404 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term561 _144947 _144962 A B P p lt2 s l.
Proof. exact (EQ_MP (@lem8231403 _144947 _144962 A B P p lt2 s l) (@lem8231069 _144947 _144962 A B P p lt2 s l h1)). Qed.
Lemma lem8231410 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : p f a.
Proof. exact (h1). Qed.
Lemma lem8231416 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : p g a.
Proof. exact (h1). Qed.
Lemma lem8231423 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term218 _144947 A B P lt2 s a f g z) = (term722 _144947 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term214 _144947 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8231424 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term220 _144947 A B P lt2 s a f g) = (term723 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231423 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8231478 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term222 _144947 A B P lt2 s a f g) = (term724 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8231425 A) (@lem8231424 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231479 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term724 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8231478 _144947 A B P lt2 s a f g) (@lem8231072 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8231485 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : term564 _144962 A B P x l f a.
Proof. exact (h1). Qed.
Lemma lem8231491 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term939 _144962 A B P x l g a) : term939 _144962 A B P x l g a.
Proof. exact (h1). Qed.
Lemma lem8231492 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term558 _144947 _144962 A B P p lt2 s z l.
Proof. exact (h1). Qed.
Lemma lem8231499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231500 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8231499 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8231501 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8231500 A B P p f). Qed.
Lemma lem8231502 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231503 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8231501 A B P p f) (@lem8231502 P a)). Qed.
Lemma lem8231505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231506 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8231505 P Prop f x). Qed.
Lemma lem8231507 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term725 A B P p f a).
Proof. exact (@lem8231506 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8231509 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term725 A B P p f a).
Proof. exact (TRANS (@lem8231503 A B P p f a) (@lem8231507 A B P p f a)). Qed.
Lemma lem8231517 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231518 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8231517 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8231519 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8231518 A B P p g). Qed.
Lemma lem8231520 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231521 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8231519 A B P p g) (@lem8231520 P a)). Qed.
Lemma lem8231523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231524 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8231523 P Prop f x). Qed.
Lemma lem8231525 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term725 A B P p g a).
Proof. exact (@lem8231524 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8231527 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term725 A B P p g a).
Proof. exact (TRANS (@lem8231521 A B P p g a) (@lem8231525 A B P p g a)). Qed.
Lemma lem8231529 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8231534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231535 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8231534 A B f x). Qed.
Lemma lem8231537 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8231535 A B f z). Qed.
Lemma lem8231542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231543 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8231542 A B f x). Qed.
Lemma lem8231545 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8231543 A B g z). Qed.
Lemma lem8231546 {A B : Type'} (f : A -> B) (z : A) : (term726 A B f z) = (term727 A B f z).
Proof. exact (MK_COMB (@lem8231529 B) (@lem8231537 A B f z)). Qed.
Lemma lem8231547 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8231546 A B f z) (@lem8231545 A B g z)). Qed.
Lemma lem8231548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231556 {_144947 P : Type'} (f : P -> _144947) (x : P) : (f x) = (@I (P -> _144947) f x).
Proof. exact (@lem8231555 P _144947 f x). Qed.
Lemma lem8231558 {_144947 P : Type'} (s : P -> _144947) (a : P) : (s a) = (@I (P -> _144947) s a).
Proof. exact (@lem8231556 _144947 P s a). Qed.
Lemma lem8231559 {_144947 A : Type'} (lt2 : type1470 _144947 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8231560 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term214 _144947 A P lt2 z s a) = (term728 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8231559 _144947 A lt2 z) (@lem8231558 _144947 P s a)). Qed.
Lemma lem8231562 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231563 {_144947 A : Type'} (f : type1470 _144947 A) (x : A) : (f x) = (@I (A -> _144947 -> Prop) f x).
Proof. exact (@lem8231562 A (_144947 -> Prop) f x). Qed.
Lemma lem8231564 {_144947 A : Type'} (lt2 : type1470 _144947 A) (z : A) : (lt2 z) = (@I (A -> _144947 -> Prop) lt2 z).
Proof. exact (@lem8231563 _144947 A lt2 z). Qed.
Lemma lem8231565 {_144947 P : Type'} (s : P -> _144947) (a : P) : (@I (P -> _144947) s a) = (@I (P -> _144947) s a).
Proof. exact (eq_refl (@I (P -> _144947) s a)). Qed.
Lemma lem8231566 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term728 _144947 A P lt2 z s a) = (term729 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8231564 _144947 A lt2 z) (@lem8231565 _144947 P s a)). Qed.
Lemma lem8231568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231569 {_144947 : Type'} (f : _144947 -> Prop) (x : _144947) : (f x) = (@I (_144947 -> Prop) f x).
Proof. exact (@lem8231568 _144947 Prop f x). Qed.
Lemma lem8231570 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term729 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (@lem8231569 _144947 (@I (A -> _144947 -> Prop) lt2 z) (@I (P -> _144947) s a)). Qed.
Lemma lem8231571 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term728 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (TRANS (@lem8231566 _144947 A P lt2 z s a) (@lem8231570 _144947 A P lt2 z s a)). Qed.
Lemma lem8231572 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term214 _144947 A P lt2 z s a) = (term730 _144947 A P lt2 z s a).
Proof. exact (TRANS (@lem8231560 _144947 A P lt2 z s a) (@lem8231571 _144947 A P lt2 z s a)). Qed.
Lemma lem8231573 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term731 _144947 A P lt2 z s a) = (term732 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8231548) (@lem8231572 _144947 A P lt2 z s a)). Qed.
Lemma lem8231574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231575 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (z : A) (s : P -> _144947) (a : P) : (term733 _144947 A P lt2 z s a) = (term734 _144947 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8231574) (@lem8231573 _144947 A P lt2 z s a)). Qed.
Lemma lem8231576 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term722 _144947 A B P lt2 s a f g z) = (term735 _144947 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8231575 _144947 A P lt2 z s a) (@lem8231547 A B f g z)). Qed.
Lemma lem8231577 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term723 _144947 A B P lt2 s a f g) = (term736 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231576 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8231579 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term724 _144947 A B P lt2 s a f g) = (term737 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8231578 A) (@lem8231577 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231580 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term737 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8231579 _144947 A B P lt2 s a f g) (@lem8231479 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8231589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231590 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8231589 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8231591 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) : (l f) = (@I ((A -> B) -> P -> list _144962) l f).
Proof. exact (@lem8231590 _144962 A B P l f). Qed.
Lemma lem8231592 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231593 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (@I ((A -> B) -> P -> list _144962) l f a).
Proof. exact (MK_COMB (@lem8231591 _144962 A B P l f) (@lem8231592 P a)). Qed.
Lemma lem8231595 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231596 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8231595 P (list _144962) f x). Qed.
Lemma lem8231597 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l f a) = (term738 _144962 A B P l f a).
Proof. exact (@lem8231596 _144962 P (@I ((A -> B) -> P -> list _144962) l f) a). Qed.
Lemma lem8231599 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (term738 _144962 A B P l f a).
Proof. exact (TRANS (@lem8231593 _144962 A B P l f a) (@lem8231597 _144962 A B P l f a)). Qed.
Lemma lem8231600 {_144962 : Type'} (x : _144962) : (@List.In _144962 x) = (@List.In _144962 x).
Proof. exact (eq_refl (@List.In _144962 x)). Qed.
Lemma lem8231601 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term564 _144962 A B P x l f a) = (term986 _144962 A B P x l f a).
Proof. exact (MK_COMB (@lem8231600 _144962 x) (@lem8231599 _144962 A B P l f a)). Qed.
Lemma lem8231603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231604 {_144962 : Type'} (f : type1398 _144962) (x : _144962) : (f x) = (@I (_144962 -> (list _144962) -> Prop) f x).
Proof. exact (@lem8231603 _144962 (type1143 _144962) f x). Qed.
Lemma lem8231605 {_144962 : Type'} (x : _144962) : (@List.In _144962 x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x).
Proof. exact (@lem8231604 _144962 (@List.In _144962) x). Qed.
Lemma lem8231606 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term738 _144962 A B P l f a) = (term738 _144962 A B P l f a).
Proof. exact (eq_refl (term738 _144962 A B P l f a)). Qed.
Lemma lem8231607 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term986 _144962 A B P x l f a) = (term987 _144962 A B P x l f a).
Proof. exact (MK_COMB (@lem8231605 _144962 x) (@lem8231606 _144962 A B P l f a)). Qed.
Lemma lem8231609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231610 {_144962 : Type'} (f : type1143 _144962) (x : list _144962) : (f x) = (@I ((list _144962) -> Prop) f x).
Proof. exact (@lem8231609 (list _144962) Prop f x). Qed.
Lemma lem8231611 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term987 _144962 A B P x l f a) = (term988 _144962 A B P x l f a).
Proof. exact (@lem8231610 _144962 (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) (term738 _144962 A B P l f a)). Qed.
Lemma lem8231612 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term986 _144962 A B P x l f a) = (term988 _144962 A B P x l f a).
Proof. exact (TRANS (@lem8231607 _144962 A B P x l f a) (@lem8231611 _144962 A B P x l f a)). Qed.
Lemma lem8231613 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term564 _144962 A B P x l f a) = (term988 _144962 A B P x l f a).
Proof. exact (TRANS (@lem8231601 _144962 A B P x l f a) (@lem8231612 _144962 A B P x l f a)). Qed.
Lemma lem8231615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231625 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8231624 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8231626 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) : (l g) = (@I ((A -> B) -> P -> list _144962) l g).
Proof. exact (@lem8231625 _144962 A B P l g). Qed.
Lemma lem8231627 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231628 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (@I ((A -> B) -> P -> list _144962) l g a).
Proof. exact (MK_COMB (@lem8231626 _144962 A B P l g) (@lem8231627 P a)). Qed.
Lemma lem8231630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231631 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8231630 P (list _144962) f x). Qed.
Lemma lem8231632 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l g a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8231631 _144962 P (@I ((A -> B) -> P -> list _144962) l g) a). Qed.
Lemma lem8231634 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (term738 _144962 A B P l g a).
Proof. exact (TRANS (@lem8231628 _144962 A B P l g a) (@lem8231632 _144962 A B P l g a)). Qed.
Lemma lem8231635 {_144962 : Type'} (x : _144962) : (@List.In _144962 x) = (@List.In _144962 x).
Proof. exact (eq_refl (@List.In _144962 x)). Qed.
Lemma lem8231636 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term564 _144962 A B P x l g a) = (term986 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8231635 _144962 x) (@lem8231634 _144962 A B P l g a)). Qed.
Lemma lem8231638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231639 {_144962 : Type'} (f : type1398 _144962) (x : _144962) : (f x) = (@I (_144962 -> (list _144962) -> Prop) f x).
Proof. exact (@lem8231638 _144962 (type1143 _144962) f x). Qed.
Lemma lem8231640 {_144962 : Type'} (x : _144962) : (@List.In _144962 x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x).
Proof. exact (@lem8231639 _144962 (@List.In _144962) x). Qed.
Lemma lem8231641 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term738 _144962 A B P l g a) = (term738 _144962 A B P l g a).
Proof. exact (eq_refl (term738 _144962 A B P l g a)). Qed.
Lemma lem8231642 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term986 _144962 A B P x l g a) = (term987 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8231640 _144962 x) (@lem8231641 _144962 A B P l g a)). Qed.
Lemma lem8231644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231645 {_144962 : Type'} (f : type1143 _144962) (x : list _144962) : (f x) = (@I ((list _144962) -> Prop) f x).
Proof. exact (@lem8231644 (list _144962) Prop f x). Qed.
Lemma lem8231646 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term987 _144962 A B P x l g a) = (term988 _144962 A B P x l g a).
Proof. exact (@lem8231645 _144962 (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) (term738 _144962 A B P l g a)). Qed.
Lemma lem8231647 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term986 _144962 A B P x l g a) = (term988 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8231642 _144962 A B P x l g a) (@lem8231646 _144962 A B P x l g a)). Qed.
Lemma lem8231648 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term564 _144962 A B P x l g a) = (term988 _144962 A B P x l g a).
Proof. exact (TRANS (@lem8231636 _144962 A B P x l g a) (@lem8231647 _144962 A B P x l g a)). Qed.
Lemma lem8231649 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term939 _144962 A B P x l g a) = (term989 _144962 A B P x l g a).
Proof. exact (MK_COMB (@lem8231615) (@lem8231648 _144962 A B P x l g a)). Qed.
Lemma lem8231651 {_144962 : Type'} : (@eq (list _144962)) = (@eq (list _144962)).
Proof. exact (eq_refl (@eq (list _144962))). Qed.
Lemma lem8231658 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231659 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8231658 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8231660 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) : (l f) = (@I ((A -> B) -> P -> list _144962) l f).
Proof. exact (@lem8231659 _144962 A B P l f). Qed.
Lemma lem8231661 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231662 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (@I ((A -> B) -> P -> list _144962) l f a).
Proof. exact (MK_COMB (@lem8231660 _144962 A B P l f) (@lem8231661 P a)). Qed.
Lemma lem8231664 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231665 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8231664 P (list _144962) f x). Qed.
Lemma lem8231666 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l f a) = (term738 _144962 A B P l f a).
Proof. exact (@lem8231665 _144962 P (@I ((A -> B) -> P -> list _144962) l f) a). Qed.
Lemma lem8231668 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (l f a) = (term738 _144962 A B P l f a).
Proof. exact (TRANS (@lem8231662 _144962 A B P l f a) (@lem8231666 _144962 A B P l f a)). Qed.
Lemma lem8231675 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231676 {_144962 A B P : Type'} (f : type815 _144962 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> list _144962) f x).
Proof. exact (@lem8231675 (A -> B) (type1477 _144962 P) f x). Qed.
Lemma lem8231677 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) : (l g) = (@I ((A -> B) -> P -> list _144962) l g).
Proof. exact (@lem8231676 _144962 A B P l g). Qed.
Lemma lem8231678 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231679 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (@I ((A -> B) -> P -> list _144962) l g a).
Proof. exact (MK_COMB (@lem8231677 _144962 A B P l g) (@lem8231678 P a)). Qed.
Lemma lem8231681 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231682 {_144962 P : Type'} (f : type1477 _144962 P) (x : P) : (f x) = (@I (P -> list _144962) f x).
Proof. exact (@lem8231681 P (list _144962) f x). Qed.
Lemma lem8231683 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> list _144962) l g a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8231682 _144962 P (@I ((A -> B) -> P -> list _144962) l g) a). Qed.
Lemma lem8231685 {_144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (l g a) = (term738 _144962 A B P l g a).
Proof. exact (TRANS (@lem8231679 _144962 A B P l g a) (@lem8231683 _144962 A B P l g a)). Qed.
Lemma lem8231686 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term739 _144962 A B P l f a) = (term740 _144962 A B P l f a).
Proof. exact (MK_COMB (@lem8231651 _144962) (@lem8231668 _144962 A B P l f a)). Qed.
Lemma lem8231687 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((l f a) = (l g a)) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (MK_COMB (@lem8231686 _144962 A B P l f a) (@lem8231685 _144962 A B P l g a)). Qed.
Lemma lem8231688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231689 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8231690 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8231699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231700 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8231699 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8231701 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8231700 A B P z f). Qed.
Lemma lem8231702 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8231703 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8231701 A B P z f) (@lem8231702 A B g)). Qed.
Lemma lem8231705 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231706 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8231705 (A -> B) (P -> A) f x). Qed.
Lemma lem8231707 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term742 A B P z f g).
Proof. exact (@lem8231706 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8231708 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term742 A B P z f g).
Proof. exact (TRANS (@lem8231703 A B P z f g) (@lem8231707 A B P z f g)). Qed.
Lemma lem8231709 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231710 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term743 A B P z f g a).
Proof. exact (MK_COMB (@lem8231708 A B P z f g) (@lem8231709 P a)). Qed.
Lemma lem8231712 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231713 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8231712 P A f x). Qed.
Lemma lem8231714 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z f g a) = (term744 A B P z f g a).
Proof. exact (@lem8231713 A P (term742 A B P z f g) a). Qed.
Lemma lem8231716 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term744 A B P z f g a).
Proof. exact (TRANS (@lem8231710 A B P z f g a) (@lem8231714 A B P z f g a)). Qed.
Lemma lem8231717 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term745 A B P z f g a) = (term746 A B P z f g a).
Proof. exact (MK_COMB (@lem8231690 A B f) (@lem8231716 A B P z f g a)). Qed.
Lemma lem8231719 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231720 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8231719 A B f x). Qed.
Lemma lem8231721 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term746 A B P z f g a) = (term747 A B P z f g a).
Proof. exact (@lem8231720 A B f (term744 A B P z f g a)). Qed.
Lemma lem8231722 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term745 A B P z f g a) = (term747 A B P z f g a).
Proof. exact (TRANS (@lem8231717 A B P z f g a) (@lem8231721 A B P z f g a)). Qed.
Lemma lem8231723 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8231732 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231733 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8231732 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8231734 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8231733 A B P z f). Qed.
Lemma lem8231735 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8231736 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8231734 A B P z f) (@lem8231735 A B g)). Qed.
Lemma lem8231738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231739 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8231738 (A -> B) (P -> A) f x). Qed.
Lemma lem8231740 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term742 A B P z f g).
Proof. exact (@lem8231739 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8231741 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term742 A B P z f g).
Proof. exact (TRANS (@lem8231736 A B P z f g) (@lem8231740 A B P z f g)). Qed.
Lemma lem8231742 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231743 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term743 A B P z f g a).
Proof. exact (MK_COMB (@lem8231741 A B P z f g) (@lem8231742 P a)). Qed.
Lemma lem8231745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231746 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8231745 P A f x). Qed.
Lemma lem8231747 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z f g a) = (term744 A B P z f g a).
Proof. exact (@lem8231746 A P (term742 A B P z f g) a). Qed.
Lemma lem8231749 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term744 A B P z f g a).
Proof. exact (TRANS (@lem8231743 A B P z f g a) (@lem8231747 A B P z f g a)). Qed.
Lemma lem8231750 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term748 A B P z f g a) = (term749 A B P z f g a).
Proof. exact (MK_COMB (@lem8231723 A B g) (@lem8231749 A B P z f g a)). Qed.
Lemma lem8231752 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8231752 A B f x). Qed.
Lemma lem8231754 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term749 A B P z f g a) = (term750 A B P z f g a).
Proof. exact (@lem8231753 A B g (term744 A B P z f g a)). Qed.
Lemma lem8231755 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term748 A B P z f g a) = (term750 A B P z f g a).
Proof. exact (TRANS (@lem8231750 A B P z f g a) (@lem8231754 A B P z f g a)). Qed.
Lemma lem8231756 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term751 A B P z f g a) = (term752 A B P z f g a).
Proof. exact (MK_COMB (@lem8231689 B) (@lem8231722 A B P z f g a)). Qed.
Lemma lem8231757 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term745 A B P z f g a) = (term748 A B P z f g a)) = ((term747 A B P z f g a) = (term750 A B P z f g a)).
Proof. exact (MK_COMB (@lem8231756 A B P z f g a) (@lem8231755 A B P z f g a)). Qed.
Lemma lem8231758 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term753 A B P z f g a) = (term754 A B P z f g a).
Proof. exact (MK_COMB (@lem8231688) (@lem8231757 A B P z f g a)). Qed.
Lemma lem8231759 {_144947 A : Type'} (lt2 : type1470 _144947 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8231768 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231769 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8231768 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8231770 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8231769 A B P z f). Qed.
Lemma lem8231771 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8231772 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8231770 A B P z f) (@lem8231771 A B g)). Qed.
Lemma lem8231774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231775 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8231774 (A -> B) (P -> A) f x). Qed.
Lemma lem8231776 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term742 A B P z f g).
Proof. exact (@lem8231775 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8231777 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term742 A B P z f g).
Proof. exact (TRANS (@lem8231772 A B P z f g) (@lem8231776 A B P z f g)). Qed.
Lemma lem8231778 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231779 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term743 A B P z f g a).
Proof. exact (MK_COMB (@lem8231777 A B P z f g) (@lem8231778 P a)). Qed.
Lemma lem8231781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231782 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8231781 P A f x). Qed.
Lemma lem8231783 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term743 A B P z f g a) = (term744 A B P z f g a).
Proof. exact (@lem8231782 A P (term742 A B P z f g) a). Qed.
Lemma lem8231785 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term744 A B P z f g a).
Proof. exact (TRANS (@lem8231779 A B P z f g a) (@lem8231783 A B P z f g a)). Qed.
Lemma lem8231790 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231791 {_144947 P : Type'} (f : P -> _144947) (x : P) : (f x) = (@I (P -> _144947) f x).
Proof. exact (@lem8231790 P _144947 f x). Qed.
Lemma lem8231793 {_144947 P : Type'} (s : P -> _144947) (a : P) : (s a) = (@I (P -> _144947) s a).
Proof. exact (@lem8231791 _144947 P s a). Qed.
Lemma lem8231794 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term755 _144947 A B P lt2 z f g a) = (term756 _144947 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8231759 _144947 A lt2) (@lem8231785 A B P z f g a)). Qed.
Lemma lem8231795 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term757 _144947 A B P lt2 z f g s a) = (term758 _144947 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8231794 _144947 A B P lt2 z f g a) (@lem8231793 _144947 P s a)). Qed.
Lemma lem8231797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231798 {_144947 A : Type'} (f : type1470 _144947 A) (x : A) : (f x) = (@I (A -> _144947 -> Prop) f x).
Proof. exact (@lem8231797 A (_144947 -> Prop) f x). Qed.
Lemma lem8231799 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term756 _144947 A B P lt2 z f g a) = (term759 _144947 A B P lt2 z f g a).
Proof. exact (@lem8231798 _144947 A lt2 (term744 A B P z f g a)). Qed.
Lemma lem8231800 {_144947 P : Type'} (s : P -> _144947) (a : P) : (@I (P -> _144947) s a) = (@I (P -> _144947) s a).
Proof. exact (eq_refl (@I (P -> _144947) s a)). Qed.
Lemma lem8231801 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term758 _144947 A B P lt2 z f g s a) = (term760 _144947 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8231799 _144947 A B P lt2 z f g a) (@lem8231800 _144947 P s a)). Qed.
Lemma lem8231803 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231804 {_144947 : Type'} (f : _144947 -> Prop) (x : _144947) : (f x) = (@I (_144947 -> Prop) f x).
Proof. exact (@lem8231803 _144947 Prop f x). Qed.
Lemma lem8231805 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term760 _144947 A B P lt2 z f g s a) = (term761 _144947 A B P lt2 z f g s a).
Proof. exact (@lem8231804 _144947 (term759 _144947 A B P lt2 z f g a) (@I (P -> _144947) s a)). Qed.
Lemma lem8231806 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term758 _144947 A B P lt2 z f g s a) = (term761 _144947 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8231801 _144947 A B P lt2 z f g s a) (@lem8231805 _144947 A B P lt2 z f g s a)). Qed.
Lemma lem8231807 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term757 _144947 A B P lt2 z f g s a) = (term761 _144947 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8231795 _144947 A B P lt2 z f g s a) (@lem8231806 _144947 A B P lt2 z f g s a)). Qed.
Lemma lem8231808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8231809 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term762 _144947 A B P lt2 z f g s a) = (term763 _144947 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8231808) (@lem8231807 _144947 A B P lt2 z f g s a)). Qed.
Lemma lem8231810 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term764 _144947 A B P lt2 s z f g a) = (term765 _144947 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8231809 _144947 A B P lt2 z f g s a) (@lem8231758 A B P z f g a)). Qed.
Lemma lem8231811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231819 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8231818 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8231820 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8231819 A B P p g). Qed.
Lemma lem8231821 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231822 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8231820 A B P p g) (@lem8231821 P a)). Qed.
Lemma lem8231824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231825 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8231824 P Prop f x). Qed.
Lemma lem8231826 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term725 A B P p g a).
Proof. exact (@lem8231825 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8231828 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term725 A B P p g a).
Proof. exact (TRANS (@lem8231822 A B P p g a) (@lem8231826 A B P p g a)). Qed.
Lemma lem8231829 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term442 A B P p g a) = (term766 A B P p g a).
Proof. exact (MK_COMB (@lem8231811) (@lem8231828 A B P p g a)). Qed.
Lemma lem8231830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231831 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term421 A B P p g a) = (term767 A B P p g a).
Proof. exact (MK_COMB (@lem8231830) (@lem8231829 A B P p g a)). Qed.
Lemma lem8231832 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term768 _144947 A B P p lt2 s z f g a) = (term769 _144947 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8231831 A B P p g a) (@lem8231810 _144947 A B P lt2 s z f g a)). Qed.
Lemma lem8231833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8231840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231841 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8231840 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8231842 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8231841 A B P p f). Qed.
Lemma lem8231843 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8231844 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8231842 A B P p f) (@lem8231843 P a)). Qed.
Lemma lem8231846 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8231847 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8231846 P Prop f x). Qed.
Lemma lem8231848 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term725 A B P p f a).
Proof. exact (@lem8231847 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8231850 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term725 A B P p f a).
Proof. exact (TRANS (@lem8231844 A B P p f a) (@lem8231848 A B P p f a)). Qed.
Lemma lem8231851 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term442 A B P p f a) = (term766 A B P p f a).
Proof. exact (MK_COMB (@lem8231833) (@lem8231850 A B P p f a)). Qed.
Lemma lem8231852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231853 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term421 A B P p f a) = (term767 A B P p f a).
Proof. exact (MK_COMB (@lem8231852) (@lem8231851 A B P p f a)). Qed.
Lemma lem8231854 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term770 _144947 A B P p lt2 s z f g a) = (term771 _144947 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8231853 A B P p f a) (@lem8231832 _144947 A B P p lt2 s z f g a)). Qed.
Lemma lem8231855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231856 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term772 _144947 A B P p lt2 s z f g a) = (term773 _144947 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8231855) (@lem8231854 _144947 A B P p lt2 s z f g a)). Qed.
Lemma lem8231857 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term774 _144947 _144962 A B P p lt2 s z f l g a) = (term775 _144947 _144962 A B P p lt2 s z f l g a).
Proof. exact (MK_COMB (@lem8231856 _144947 A B P p lt2 s z f g a) (@lem8231687 _144962 A B P f l g a)). Qed.
Lemma lem8231858 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term776 _144947 _144962 A B P p lt2 s z f l g) = (term777 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (fun_ext (fun a : P => @lem8231857 _144947 _144962 A B P p lt2 s z f l g a)). Qed.
Lemma lem8231859 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231860 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term778 _144947 _144962 A B P p lt2 s z f l g) = (term779 _144947 _144962 A B P p lt2 s z f l g).
Proof. exact (MK_COMB (@lem8231859 P) (@lem8231858 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231861 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term780 _144947 _144962 A B P p lt2 s z f l) = (term781 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231860 _144947 _144962 A B P p lt2 s z f l g)). Qed.
Lemma lem8231862 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231863 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term554 _144947 _144962 A B P p lt2 s z f l) = (term782 _144947 _144962 A B P p lt2 s z f l).
Proof. exact (MK_COMB (@lem8231862 A B) (@lem8231861 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231864 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term556 _144947 _144962 A B P p lt2 s z l) = (term783 _144947 _144962 A B P p lt2 s z l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231863 _144947 _144962 A B P p lt2 s z f l)). Qed.
Lemma lem8231865 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231866 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) : (term558 _144947 _144962 A B P p lt2 s z l) = (term784 _144947 _144962 A B P p lt2 s z l).
Proof. exact (MK_COMB (@lem8231865 A B) (@lem8231864 _144947 _144962 A B P p lt2 s z l)). Qed.
Lemma lem8231867 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term784 _144947 _144962 A B P p lt2 s z l.
Proof. exact (EQ_MP (@lem8231866 _144947 _144962 A B P p lt2 s z l) (@lem8231492 _144947 _144962 A B P p lt2 s z l h1)). Qed.
Lemma lem8231883 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term735 _144947 A B P lt2 s a f g z) = (term735 _144947 A B P lt2 s a f g z).
Proof. exact (eq_refl (term735 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231884 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term736 _144947 A B P lt2 s a f g) = (term736 _144947 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8231883 _144947 A B P lt2 s a f g z)). Qed.
Lemma lem8231885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8231887 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) : (term737 _144947 A B P lt2 s a f g) = (term737 _144947 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8231885 A) (@lem8231884 _144947 A B P lt2 s a f g)). Qed.
Lemma lem8231888 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term737 _144947 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8231887 _144947 A B P lt2 s a f g) (@lem8231580 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8231898 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (eq_refl ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8231915 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term769 _144947 A B P p lt2 s z f g a) = (term785 _144947 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term761 _144947 A B P lt2 z f g s a) (term766 A B P p g a) (term754 A B P z f g a)). Qed.
Lemma lem8231918 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term767 A B P p f a) = (term767 A B P p f a).
Proof. exact (eq_refl (term767 A B P p f a)). Qed.
Lemma lem8231919 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term771 _144947 A B P p lt2 s z f g a) = (term786 _144947 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8231918 A B P p f a) (@lem8231915 _144947 A B P lt2 s p z f g a)). Qed.
Lemma lem8231926 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term786 _144947 A B P lt2 s p z f g a) = (term787 _144947 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term788 _144947 A B P p lt2 z f g s a) (term766 A B P p f a) (term789 A B P p z f g a)). Qed.
Lemma lem8231927 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term771 _144947 A B P p lt2 s z f g a) = (term787 _144947 A B P lt2 s p z f g a).
Proof. exact (TRANS (@lem8231919 _144947 A B P lt2 s p z f g a) (@lem8231926 _144947 A B P lt2 s p z f g a)). Qed.
Lemma lem8231928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8231929 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term773 _144947 A B P p lt2 s z f g a) = (term790 _144947 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8231928) (@lem8231927 _144947 A B P lt2 s p z f g a)). Qed.
Lemma lem8231930 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term775 _144947 _144962 A B P p lt2 s z f l g a) = (term791 _144947 _144962 A B P lt2 s p z f l g a).
Proof. exact (MK_COMB (@lem8231929 _144947 A B P lt2 s p z f g a) (@lem8231898 _144962 A B P f l g a)). Qed.
Lemma lem8231937 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term791 _144947 _144962 A B P lt2 s p z f l g a) = (term792 _144947 _144962 A B P lt2 s p z f l g a).
Proof. exact (@lem19699 (term793 _144947 A B P p lt2 z f g s a) (term794 A B P p z f g a) ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8231938 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term775 _144947 _144962 A B P p lt2 s z f l g a) = (term792 _144947 _144962 A B P lt2 s p z f l g a).
Proof. exact (TRANS (@lem8231930 _144947 _144962 A B P lt2 s p z f l g a) (@lem8231937 _144947 _144962 A B P lt2 s p z f l g a)). Qed.
Lemma lem8231939 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term777 _144947 _144962 A B P p lt2 s z f l g) = (term795 _144947 _144962 A B P lt2 s p z f l g).
Proof. exact (fun_ext (fun a : P => @lem8231938 _144947 _144962 A B P lt2 s p z f l g a)). Qed.
Lemma lem8231940 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8231941 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) : (term779 _144947 _144962 A B P p lt2 s z f l g) = (term796 _144947 _144962 A B P lt2 s p z f l g).
Proof. exact (MK_COMB (@lem8231940 P) (@lem8231939 _144947 _144962 A B P lt2 s p z f l g)). Qed.
Lemma lem8231942 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term781 _144947 _144962 A B P p lt2 s z f l) = (term797 _144947 _144962 A B P lt2 s p z f l).
Proof. exact (fun_ext (fun g : A -> B => @lem8231941 _144947 _144962 A B P lt2 s p z f l g)). Qed.
Lemma lem8231943 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231944 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (l : type815 _144962 A B P) : (term782 _144947 _144962 A B P p lt2 s z f l) = (term798 _144947 _144962 A B P lt2 s p z f l).
Proof. exact (MK_COMB (@lem8231943 A B) (@lem8231942 _144947 _144962 A B P lt2 s p z f l)). Qed.
Lemma lem8231945 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (l : type815 _144962 A B P) : (term783 _144947 _144962 A B P p lt2 s z l) = (term799 _144947 _144962 A B P lt2 s p z l).
Proof. exact (fun_ext (fun f : A -> B => @lem8231944 _144947 _144962 A B P lt2 s p z f l)). Qed.
Lemma lem8231946 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8231948 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (l : type815 _144962 A B P) : (term784 _144947 _144962 A B P p lt2 s z l) = (term800 _144947 _144962 A B P lt2 s p z l).
Proof. exact (MK_COMB (@lem8231946 A B) (@lem8231945 _144947 _144962 A B P lt2 s p z l)). Qed.
Lemma lem8231949 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term800 _144947 _144962 A B P lt2 s p z l.
Proof. exact (EQ_MP (@lem8231948 _144947 _144962 A B P lt2 s p z l) (@lem8231867 _144947 _144962 A B P p lt2 s z l h1)). Qed.
Lemma lem8231950 {_144947 A B P : Type'} (_109549 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term801 _144947 A B P lt2 s a f g _109549.
Proof. exact (@lem8231888 _144947 A B P lt2 s a f g h1 _109549). Qed.
Lemma lem8231951 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109549 : A) : (term801 _144947 A B P lt2 s a f g _109549) = (term735 _144947 A B P lt2 s a f g _109549).
Proof. exact (eq_refl (term801 _144947 A B P lt2 s a f g _109549)). Qed.
Lemma lem8231953 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term802 _144947 _144962 A B P lt2 s p z l _109550.
Proof. exact (@lem8231949 _144947 _144962 A B P p lt2 s z l h1 _109550). Qed.
Lemma lem8231954 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) : (term802 _144947 _144962 A B P lt2 s p z l _109550) = (term798 _144947 _144962 A B P lt2 s p z _109550 l).
Proof. exact (eq_refl (term802 _144947 _144962 A B P lt2 s p z l _109550)). Qed.
Lemma lem8231955 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term798 _144947 _144962 A B P lt2 s p z _109550 l.
Proof. exact (EQ_MP (@lem8231954 _144947 _144962 A B P lt2 s p z _109550 l) (@lem8231953 _144947 _144962 A B P _109550 p lt2 s z l h1)). Qed.
Lemma lem8231956 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term803 _144947 _144962 A B P lt2 s p z _109550 l _109551.
Proof. exact (@lem8231955 _144947 _144962 A B P _109550 p lt2 s z l h1 _109551). Qed.
Lemma lem8231957 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) : (term803 _144947 _144962 A B P lt2 s p z _109550 l _109551) = (term796 _144947 _144962 A B P lt2 s p z _109550 l _109551).
Proof. exact (eq_refl (term803 _144947 _144962 A B P lt2 s p z _109550 l _109551)). Qed.
Lemma lem8231958 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term796 _144947 _144962 A B P lt2 s p z _109550 l _109551.
Proof. exact (EQ_MP (@lem8231957 _144947 _144962 A B P lt2 s p z _109550 l _109551) (@lem8231956 _144947 _144962 A B P _109550 _109551 p lt2 s z l h1)). Qed.
Lemma lem8231959 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term804 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552.
Proof. exact (@lem8231958 _144947 _144962 A B P _109550 _109551 p lt2 s z l h1 _109552). Qed.
Lemma lem8231960 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term804 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552) = (term792 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552).
Proof. exact (eq_refl (term804 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552)). Qed.
Lemma lem8231961 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term792 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552.
Proof. exact (EQ_MP (@lem8231960 _144947 _144962 A B P lt2 s p z _109550 l _109551 _109552) (@lem8231959 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8231962 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term805 _144962 A B P p z _109550 l _109551 _109552.
Proof. exact (proj2 (@lem8231961 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8231963 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term806 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552.
Proof. exact (proj1 (@lem8231961 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8231973 {_144947 A B P : Type'} (_109549 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term735 _144947 A B P lt2 s a f g _109549.
Proof. exact (EQ_MP (@lem8231951 _144947 A B P lt2 s a f g _109549) (@lem8231950 _144947 A B P _109549 lt2 s a f g h1)). Qed.
Lemma lem8231977 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term939 _144962 A B P x l g a) : term989 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8231649 _144962 A B P x l g a) (@lem8231491 _144962 A B P x l g a h1)). Qed.
Lemma lem8231981 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term806 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term807 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552).
Proof. exact (@lem8225721 (term766 A B P p _109550 _109552) (term788 _144947 A B P p lt2 z _109550 _109551 s _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8231988 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term808 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term809 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552).
Proof. exact (@lem8225721 (term766 A B P p _109551 _109552) (term761 _144947 A B P lt2 z _109550 _109551 s _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8231989 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8231992 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term807 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8231989 A B P p _109550 _109552) (@lem8231988 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552)). Qed.
Lemma lem8231994 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term806 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552).
Proof. exact (TRANS (@lem8231981 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) (@lem8231992 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552)). Qed.
Lemma lem8231995 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552.
Proof. exact (EQ_MP (@lem8231994 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) (@lem8231963 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8231999 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term805 _144962 A B P p z _109550 l _109551 _109552) = (term811 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (@lem8225721 (term766 A B P p _109550 _109552) (term789 A B P p z _109550 _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232006 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term812 _144962 A B P p z _109550 l _109551 _109552) = (term813 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (@lem8225721 (term766 A B P p _109551 _109552) (term754 A B P z _109550 _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232007 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8232010 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term811 _144962 A B P p z _109550 l _109551 _109552) = (term814 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8232007 A B P p _109550 _109552) (@lem8232006 _144962 A B P p z _109550 l _109551 _109552)). Qed.
Lemma lem8232012 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term805 _144962 A B P p z _109550 l _109551 _109552) = (term814 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (TRANS (@lem8231999 _144962 A B P p z _109550 l _109551 _109552) (@lem8232010 _144962 A B P p z _109550 l _109551 _109552)). Qed.
Lemma lem8232013 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term814 _144962 A B P p z _109550 l _109551 _109552.
Proof. exact (EQ_MP (@lem8232012 _144962 A B P p z _109550 l _109551 _109552) (@lem8231962 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8232014 {_144962 : Type'} : (@I ((list _144962) -> Prop)) = (@I ((list _144962) -> Prop)).
Proof. exact (eq_refl (@I ((list _144962) -> Prop))). Qed.
Lemma lem8232015 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) (h1 : _109553 = _109555) : _109553 = _109555.
Proof. exact (h1). Qed.
Lemma lem8232016 {_144962 : Type'} (_109554 : list _144962) (_109556 : list _144962) (h1 : _109554 = _109556) : _109554 = _109556.
Proof. exact (h1). Qed.
Lemma lem8232017 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) (h1 : _109553 = _109555) : (@I ((list _144962) -> Prop) _109553) = (@I ((list _144962) -> Prop) _109555).
Proof. exact (MK_COMB (@lem8232014 _144962) (@lem8232015 _144962 _109553 _109555 h1)). Qed.
Lemma lem8232018 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) (_109554 : list _144962) (_109556 : list _144962) (h1 : _109553 = _109555) (h2 : _109554 = _109556) : (@I ((list _144962) -> Prop) _109553 _109554) = (@I ((list _144962) -> Prop) _109555 _109556).
Proof. exact (MK_COMB (@lem8232017 _144962 _109553 _109555 h1) (@lem8232016 _144962 _109554 _109556 h2)). Qed.
Lemma lem8232020 (b : Prop) (a : Prop) : term990 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem8232021 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : term991 _144962 _109555 _109556 _109553 _109554.
Proof. exact (@lem8232020 (@I ((list _144962) -> Prop) _109555 _109556) (@I ((list _144962) -> Prop) _109553 _109554)). Qed.
Lemma lem8232022 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) (_109554 : list _144962) (_109556 : list _144962) (h1 : _109553 = _109555) (h2 : _109554 = _109556) : term992 _144962 _109555 _109556 _109553 _109554.
Proof. exact (@lem8232021 _144962 _109555 _109556 _109553 _109554 (@lem8232018 _144962 _109553 _109555 _109554 _109556 h1 h2)). Qed.
Lemma lem8232023 {_144962 : Type'} (_109556 : list _144962) (_109554 : list _144962) (_109553 : type1143 _144962) (_109555 : type1143 _144962) (h1 : _109553 = _109555) : term993 _144962 _109555 _109556 _109553 _109554.
Proof. exact (fun h0 : _109554 = _109556 => @lem8232022 _144962 _109553 _109555 _109554 _109556 h1 h0). Qed.
Lemma lem8232025 (a : Prop) (b : Prop) : (a -> b) = (term994 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8232026 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term993 _144962 _109555 _109556 _109553 _109554) = (term995 _144962 _109555 _109556 _109553 _109554).
Proof. exact (@lem8232025 (_109554 = _109556) (term992 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232027 {_144962 : Type'} (_109556 : list _144962) (_109554 : list _144962) (_109553 : type1143 _144962) (_109555 : type1143 _144962) (h1 : _109553 = _109555) : term995 _144962 _109555 _109556 _109553 _109554.
Proof. exact (EQ_MP (@lem8232026 _144962 _109555 _109556 _109553 _109554) (@lem8232023 _144962 _109556 _109554 _109553 _109555 h1)). Qed.
Lemma lem8232028 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : term996 _144962 _109555 _109556 _109553 _109554.
Proof. exact (fun h0 : _109553 = _109555 => @lem8232027 _144962 _109556 _109554 _109553 _109555 h0). Qed.
Lemma lem8232030 (a : Prop) (b : Prop) : (a -> b) = (term994 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8232031 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term996 _144962 _109555 _109556 _109553 _109554) = (term997 _144962 _109555 _109556 _109553 _109554).
Proof. exact (@lem8232030 (_109553 = _109555) (term995 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232032 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : term997 _144962 _109555 _109556 _109553 _109554.
Proof. exact (EQ_MP (@lem8232031 _144962 _109555 _109556 _109553 _109554) (@lem8232028 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232260 {_144962 : Type'} (x : type1143 _144962) : x = x.
Proof. exact (@lem21386 (type1143 _144962) x). Qed.
Lemma lem8232261 {_144962 : Type'} (x : type1143 _144962) : x = x.
Proof. exact (@lem8232260 _144962 x). Qed.
Lemma lem8232262 {_144962 : Type'} (x : _144962) : (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x).
Proof. exact (@lem8232261 _144962 (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x)). Qed.
Lemma lem8232263 {_144962 : Type'} (x : _144962) : term998 _144962 x.
Proof. exact (fun h0 : term999 _144962 x => @lem8232262 _144962 x). Qed.
Lemma lem8232265 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232266 {_144962 : Type'} (x : _144962) : (term998 _144962 x) = ((@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x)).
Proof. exact (@lem8232265 ((@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x))). Qed.
Lemma lem8232267 {_144962 : Type'} (x : _144962) : (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) = (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x).
Proof. exact (EQ_MP (@lem8232266 _144962 x) (@lem8232263 _144962 x)). Qed.
Lemma lem8232269 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8231509 A B P p f a) (@lem8231410 A B P p f a h1)). Qed.
Lemma lem8232270 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term815 A B P p f a.
Proof. exact (fun h0 : term766 A B P p f a => @lem8232269 A B P p f a h1). Qed.
Lemma lem8232272 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232273 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term815 A B P p f a) = (term725 A B P p f a).
Proof. exact (@lem8232272 (term725 A B P p f a)). Qed.
Lemma lem8232274 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8232273 A B P p f a) (@lem8232270 A B P p f a h1)). Qed.
Lemma lem8232276 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8231527 A B P p g a) (@lem8231416 A B P p g a h1)). Qed.
Lemma lem8232277 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term815 A B P p g a.
Proof. exact (fun h0 : term766 A B P p g a => @lem8232276 A B P p g a h1). Qed.
Lemma lem8232279 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232280 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term815 A B P p g a) = (term725 A B P p g a).
Proof. exact (@lem8232279 (term725 A B P p g a)). Qed.
Lemma lem8232281 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8232280 A B P p g a) (@lem8232277 A B P p g a h1)). Qed.
Lemma lem8232283 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8231509 A B P p f a) (@lem8231410 A B P p f a h1)). Qed.
Lemma lem8232284 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term815 A B P p f a.
Proof. exact (fun h0 : term766 A B P p f a => @lem8232283 A B P p f a h1). Qed.
Lemma lem8232286 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232287 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term815 A B P p f a) = (term725 A B P p f a).
Proof. exact (@lem8232286 (term725 A B P p f a)). Qed.
Lemma lem8232288 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) (h1 : p f a) : term725 A B P p f a.
Proof. exact (EQ_MP (@lem8232287 A B P p f a) (@lem8232284 A B P p f a h1)). Qed.
Lemma lem8232290 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8231527 A B P p g a) (@lem8231416 A B P p g a h1)). Qed.
Lemma lem8232291 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term815 A B P p g a.
Proof. exact (fun h0 : term766 A B P p g a => @lem8232290 A B P p g a h1). Qed.
Lemma lem8232293 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232294 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term815 A B P p g a) = (term725 A B P p g a).
Proof. exact (@lem8232293 (term725 A B P p g a)). Qed.
Lemma lem8232295 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) (h1 : p g a) : term725 A B P p g a.
Proof. exact (EQ_MP (@lem8232294 A B P p g a) (@lem8232291 A B P p g a h1)). Qed.
Lemma lem8232298 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term741 _144962 A B P f l g a.
Proof. exact (h1). Qed.
Lemma lem8232299 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term816 _144962 A B P f l g a.
Proof. exact (fun h0 : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a) => @lem8232298 _144962 A B P f l g a h1). Qed.
Lemma lem8232301 (p : Prop) : (term817 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8232302 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term816 _144962 A B P f l g a) = (term741 _144962 A B P f l g a).
Proof. exact (@lem8232301 ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8232303 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) : term741 _144962 A B P f l g a.
Proof. exact (EQ_MP (@lem8232302 _144962 A B P f l g a) (@lem8232299 _144962 A B P f l g a h1)). Qed.
Lemma lem8232319 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232320 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term809 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term818 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552).
Proof. exact (@lem8232319 (term761 _144947 A B P lt2 z _109550 _109551 s _109552) (term766 A B P p _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232334 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8232335 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term819 _144962 A B P p _109550 l _109551 _109552) = (term820 _144962 A B P _109550 l p _109551 _109552).
Proof. exact (@lem8232334 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232343 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term821 _144947 A B P lt2 z _109550 _109551 s _109552) = (term821 _144947 A B P lt2 z _109550 _109551 s _109552).
Proof. exact (eq_refl (term821 _144947 A B P lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232344 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term818 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term822 _144947 _144962 A B P lt2 z s _109550 l p _109551 _109552).
Proof. exact (MK_COMB (@lem8232343 _144947 A B P lt2 z _109550 _109551 s _109552) (@lem8232335 _144962 A B P _109550 l p _109551 _109552)). Qed.
Lemma lem8232348 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232349 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term822 _144947 _144962 A B P lt2 z s _109550 l p _109551 _109552) = (term823 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552).
Proof. exact (@lem8232348 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term761 _144947 A B P lt2 z _109550 _109551 s _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232367 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term818 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term823 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552).
Proof. exact (TRANS (@lem8232344 _144947 _144962 A B P lt2 z s _109550 l p _109551 _109552) (@lem8232349 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552)). Qed.
Lemma lem8232368 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term809 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term823 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552).
Proof. exact (TRANS (@lem8232320 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) (@lem8232367 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552)). Qed.
Lemma lem8232369 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8232370 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term824 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552).
Proof. exact (MK_COMB (@lem8232369 A B P p _109550 _109552) (@lem8232368 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552)). Qed.
Lemma lem8232374 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232375 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (s : P -> _144947) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term824 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552) = (term825 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552).
Proof. exact (@lem8232374 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109550 _109552) (term826 _144947 A B P lt2 z _109550 s p _109551 _109552)). Qed.
Lemma lem8232391 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232392 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term827 _144947 A B P lt2 z _109550 s p _109551 _109552) = (term828 _144947 A B P lt2 z s _109550 p _109551 _109552).
Proof. exact (@lem8232391 (term761 _144947 A B P lt2 z _109550 _109551 s _109552) (term766 A B P p _109550 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232408 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term829 _144962 A B P _109550 l _109551 _109552) = (term829 _144962 A B P _109550 l _109551 _109552).
Proof. exact (eq_refl (term829 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232409 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term825 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232408 _144962 A B P _109550 l _109551 _109552) (@lem8232392 _144947 A B P lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232420 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term824 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232375 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552) (@lem8232409 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232421 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232370 _144947 _144962 A B P l lt2 z _109550 s p _109551 _109552) (@lem8232420 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8232423 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term831 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term832 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232422) (@lem8232421 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232447 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8232448 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term819 _144962 A B P p _109550 l _109551 _109552) = (term820 _144962 A B P _109550 l p _109551 _109552).
Proof. exact (@lem8232447 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232456 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8232457 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term833 _144962 A B P p _109550 l _109551 _109552) = (term834 _144962 A B P _109550 l p _109551 _109552).
Proof. exact (MK_COMB (@lem8232456 A B P p _109550 _109552) (@lem8232448 _144962 A B P _109550 l p _109551 _109552)). Qed.
Lemma lem8232461 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232462 {_144962 A B P : Type'} (l : type815 _144962 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term834 _144962 A B P _109550 l p _109551 _109552) = (term835 _144962 A B P l _109550 p _109551 _109552).
Proof. exact (@lem8232461 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109550 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232480 {_144962 A B P : Type'} (l : type815 _144962 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term833 _144962 A B P p _109550 l _109551 _109552) = (term835 _144962 A B P l _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232457 _144962 A B P _109550 l p _109551 _109552) (@lem8232462 _144962 A B P l _109550 p _109551 _109552)). Qed.
Lemma lem8232481 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term821 _144947 A B P lt2 z _109550 _109551 s _109552) = (term821 _144947 A B P lt2 z _109550 _109551 s _109552).
Proof. exact (eq_refl (term821 _144947 A B P lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232482 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (l : type815 _144962 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term837 _144947 _144962 A B P lt2 z s l _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232481 _144947 A B P lt2 z _109550 _109551 s _109552) (@lem8232480 _144962 A B P l _109550 p _109551 _109552)). Qed.
Lemma lem8232486 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232487 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term837 _144947 _144962 A B P lt2 z s l _109550 p _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (@lem8232486 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term761 _144947 A B P lt2 z _109550 _109551 s _109552) (term838 A B P _109550 p _109551 _109552)). Qed.
Lemma lem8232515 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232482 _144947 _144962 A B P lt2 z s l _109550 p _109551 _109552) (@lem8232487 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232516 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : ((term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552)) = ((term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)).
Proof. exact (MK_COMB (@lem8232423 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552) (@lem8232515 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232518 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8232519 (x : Prop) : (x = x) = True.
Proof. exact (@lem8232518 Prop x). Qed.
Lemma lem8232520 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : ((term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552) = (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)) = True.
Proof. exact (@lem8232519 (term830 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232521 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : ((term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552)) = True.
Proof. exact (TRANS (@lem8232516 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552) (@lem8232520 _144947 _144962 A B P l lt2 z s _109550 p _109551 _109552)). Qed.
Lemma lem8232522 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : True = ((term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552)).
Proof. exact (SYM (@lem8232521 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552)). Qed.
Lemma lem8232523 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (s : P -> _144947) (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term810 _144947 _144962 A B P p lt2 z s _109550 l _109551 _109552) = (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552).
Proof. exact (EQ_MP (@lem8232522 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) (@lem0)). Qed.
Lemma lem8232524 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552.
Proof. exact (EQ_MP (@lem8232523 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) (@lem8231995 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8232526 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8232527 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term840 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552).
Proof. exact (@lem8232526 (term833 _144962 A B P p _109550 l _109551 _109552) (term761 _144947 A B P lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232529 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8232530 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term843 _144962 A B P p _109550 l _109551 _109552) = (term844 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (@lem8232529 (term766 A B P p _109550 _109552) (term819 _144962 A B P p _109550 l _109551 _109552)). Qed.
Lemma lem8232532 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232533 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term845 A B P p _109550 _109552) = (term725 A B P p _109550 _109552).
Proof. exact (@lem8232532 (term725 A B P p _109550 _109552)). Qed.
Lemma lem8232534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8232535 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term846 A B P p _109550 _109552) = (term847 A B P p _109550 _109552).
Proof. exact (MK_COMB (@lem8232534) (@lem8232533 A B P p _109550 _109552)). Qed.
Lemma lem8232537 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8232538 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term848 _144962 A B P p _109550 l _109551 _109552) = (term849 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (@lem8232537 (term766 A B P p _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232540 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232541 {A B P : Type'} (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term845 A B P p _109551 _109552) = (term725 A B P p _109551 _109552).
Proof. exact (@lem8232540 (term725 A B P p _109551 _109552)). Qed.
Lemma lem8232542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8232543 {A B P : Type'} (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term846 A B P p _109551 _109552) = (term847 A B P p _109551 _109552).
Proof. exact (MK_COMB (@lem8232542) (@lem8232541 A B P p _109551 _109552)). Qed.
Lemma lem8232544 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term741 _144962 A B P _109550 l _109551 _109552) = (term741 _144962 A B P _109550 l _109551 _109552).
Proof. exact (eq_refl (term741 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232545 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term849 _144962 A B P p _109550 l _109551 _109552) = (term850 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8232543 A B P p _109551 _109552) (@lem8232544 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232546 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term848 _144962 A B P p _109550 l _109551 _109552) = (term850 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (TRANS (@lem8232538 _144962 A B P p _109550 l _109551 _109552) (@lem8232545 _144962 A B P p _109550 l _109551 _109552)). Qed.
Lemma lem8232547 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term844 _144962 A B P p _109550 l _109551 _109552) = (term851 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8232535 A B P p _109550 _109552) (@lem8232546 _144962 A B P p _109550 l _109551 _109552)). Qed.
Lemma lem8232548 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term843 _144962 A B P p _109550 l _109551 _109552) = (term851 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (TRANS (@lem8232530 _144962 A B P p _109550 l _109551 _109552) (@lem8232547 _144962 A B P p _109550 l _109551 _109552)). Qed.
Lemma lem8232549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8232550 {_144962 A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term852 _144962 A B P p _109550 l _109551 _109552) = (term853 _144962 A B P p _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8232549) (@lem8232548 _144962 A B P p _109550 l _109551 _109552)). Qed.
Lemma lem8232551 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term761 _144947 A B P lt2 z _109550 _109551 s _109552) = (term761 _144947 A B P lt2 z _109550 _109551 s _109552).
Proof. exact (eq_refl (term761 _144947 A B P lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232552 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term840 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552) = (term854 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552).
Proof. exact (MK_COMB (@lem8232550 _144962 A B P p _109550 l _109551 _109552) (@lem8232551 _144947 A B P lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232553 {_144947 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (s : P -> _144947) (_109552 : P) : (term836 _144947 _144962 A B P lt2 z s p _109550 l _109551 _109552) = (term854 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552).
Proof. exact (TRANS (@lem8232527 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552) (@lem8232552 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552)). Qed.
Lemma lem8232555 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) (h2 : p g a) : term850 _144962 A B P p f l g a.
Proof. exact (conj (@lem8232295 A B P p g a h2) (@lem8232303 _144962 A B P f l g a h1)). Qed.
Lemma lem8232556 {_144962 A B P : Type'} (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term741 _144962 A B P f l g a) (h2 : p f a) (h3 : p g a) : term851 _144962 A B P p f l g a.
Proof. exact (conj (@lem8232288 A B P p f a h2) (@lem8232555 _144962 A B P f l p g a h1 h3)). Qed.
Lemma lem8232558 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term854 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552.
Proof. exact (EQ_MP (@lem8232553 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552) (@lem8232524 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8232559 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term854 _144947 _144962 A B P p l lt2 z _109550 _109551 s _109552.
Proof. exact (@lem8232558 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1). Qed.
Lemma lem8232560 {_144947 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term854 _144947 _144962 A B P p l lt2 z f g s a.
Proof. exact (@lem8232559 _144947 _144962 A B P f g a p lt2 s z l h1). Qed.
Lemma lem8232563 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term761 _144947 A B P lt2 z f g s a.
Proof. exact (@lem8232560 _144947 _144962 A B P f g a p lt2 s z l h1 (@lem8232556 _144962 A B P l f p g a h2 h3 h4)). Qed.
Lemma lem8232564 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term855 _144947 A B P lt2 z f g s a.
Proof. exact (fun h0 : term856 _144947 A B P lt2 z f g s a => @lem8232563 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4). Qed.
Lemma lem8232566 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232567 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> _144947) (a : P) : (term855 _144947 A B P lt2 z f g s a) = (term761 _144947 A B P lt2 z f g s a).
Proof. exact (@lem8232566 (term761 _144947 A B P lt2 z f g s a)). Qed.
Lemma lem8232568 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) (h2 : term741 _144962 A B P f l g a) (h3 : p f a) (h4 : p g a) : term761 _144947 A B P lt2 z f g s a.
Proof. exact (EQ_MP (@lem8232567 _144947 A B P lt2 z f g s a) (@lem8232564 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4)). Qed.
Lemma lem8232574 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8232575 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term735 _144947 A B P lt2 s a f g _109549) = (term857 _144947 A B P f g lt2 _109549 s a).
Proof. exact (@lem8232574 ((@I (A -> B) f _109549) = (@I (A -> B) g _109549)) (term732 _144947 A P lt2 _109549 s a)). Qed.
Lemma lem8232583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8232584 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term858 _144947 A B P lt2 s a f g _109549) = (term859 _144947 A B P f g lt2 _109549 s a).
Proof. exact (MK_COMB (@lem8232583) (@lem8232575 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232592 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term857 _144947 A B P f g lt2 _109549 s a) = (term857 _144947 A B P f g lt2 _109549 s a).
Proof. exact (eq_refl (term857 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232593 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : ((term735 _144947 A B P lt2 s a f g _109549) = (term857 _144947 A B P f g lt2 _109549 s a)) = ((term857 _144947 A B P f g lt2 _109549 s a) = (term857 _144947 A B P f g lt2 _109549 s a)).
Proof. exact (MK_COMB (@lem8232584 _144947 A B P f g lt2 _109549 s a) (@lem8232592 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232595 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8232596 (x : Prop) : (x = x) = True.
Proof. exact (@lem8232595 Prop x). Qed.
Lemma lem8232597 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : ((term857 _144947 A B P f g lt2 _109549 s a) = (term857 _144947 A B P f g lt2 _109549 s a)) = True.
Proof. exact (@lem8232596 (term857 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232598 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : ((term735 _144947 A B P lt2 s a f g _109549) = (term857 _144947 A B P f g lt2 _109549 s a)) = True.
Proof. exact (TRANS (@lem8232593 _144947 A B P f g lt2 _109549 s a) (@lem8232597 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232599 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : True = ((term735 _144947 A B P lt2 s a f g _109549) = (term857 _144947 A B P f g lt2 _109549 s a)).
Proof. exact (SYM (@lem8232598 _144947 A B P f g lt2 _109549 s a)). Qed.
Lemma lem8232600 {_144947 A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term735 _144947 A B P lt2 s a f g _109549) = (term857 _144947 A B P f g lt2 _109549 s a).
Proof. exact (EQ_MP (@lem8232599 _144947 A B P f g lt2 _109549 s a) (@lem0)). Qed.
Lemma lem8232601 {_144947 A B P : Type'} (_109549 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term857 _144947 A B P f g lt2 _109549 s a.
Proof. exact (EQ_MP (@lem8232600 _144947 A B P f g lt2 _109549 s a) (@lem8231973 _144947 A B P _109549 lt2 s a f g h1)). Qed.
Lemma lem8232603 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8232604 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109549 : A) : (term857 _144947 A B P f g lt2 _109549 s a) = (term860 _144947 A B P lt2 s a f g _109549).
Proof. exact (@lem8232603 (term732 _144947 A P lt2 _109549 s a) ((@I (A -> B) f _109549) = (@I (A -> B) g _109549))). Qed.
Lemma lem8232606 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232607 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term861 _144947 A P lt2 _109549 s a) = (term730 _144947 A P lt2 _109549 s a).
Proof. exact (@lem8232606 (term730 _144947 A P lt2 _109549 s a)). Qed.
Lemma lem8232608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8232609 {_144947 A P : Type'} (lt2 : type1470 _144947 A) (_109549 : A) (s : P -> _144947) (a : P) : (term862 _144947 A P lt2 _109549 s a) = (term863 _144947 A P lt2 _109549 s a).
Proof. exact (MK_COMB (@lem8232608) (@lem8232607 _144947 A P lt2 _109549 s a)). Qed.
Lemma lem8232610 {A B : Type'} (f : A -> B) (g : A -> B) (_109549 : A) : ((@I (A -> B) f _109549) = (@I (A -> B) g _109549)) = ((@I (A -> B) f _109549) = (@I (A -> B) g _109549)).
Proof. exact (eq_refl ((@I (A -> B) f _109549) = (@I (A -> B) g _109549))). Qed.
Lemma lem8232611 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109549 : A) : (term860 _144947 A B P lt2 s a f g _109549) = (term864 _144947 A B P lt2 s a f g _109549).
Proof. exact (MK_COMB (@lem8232609 _144947 A P lt2 _109549 s a) (@lem8232610 A B f g _109549)). Qed.
Lemma lem8232612 {_144947 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (_109549 : A) : (term857 _144947 A B P f g lt2 _109549 s a) = (term864 _144947 A B P lt2 s a f g _109549).
Proof. exact (TRANS (@lem8232604 _144947 A B P lt2 s a f g _109549) (@lem8232611 _144947 A B P lt2 s a f g _109549)). Qed.
Lemma lem8232615 {_144947 A B P : Type'} (_109549 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term864 _144947 A B P lt2 s a f g _109549.
Proof. exact (EQ_MP (@lem8232612 _144947 A B P lt2 s a f g _109549) (@lem8232601 _144947 A B P _109549 lt2 s a f g h1)). Qed.
Lemma lem8232616 {_144947 A B P : Type'} (_109549 : A) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term864 _144947 A B P lt2 s a f g _109549.
Proof. exact (@lem8232615 _144947 A B P _109549 lt2 s a f g h1). Qed.
Lemma lem8232617 {_144947 A B P : Type'} (z : type518 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term222 _144947 A B P lt2 s a f g) : term865 _144947 A B P lt2 s z f g a.
Proof. exact (@lem8232616 _144947 A B P (term744 A B P z f g a) lt2 s a f g h1). Qed.
Lemma lem8232620 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term747 A B P z f g a) = (term750 A B P z f g a).
Proof. exact (@lem8232617 _144947 A B P z lt2 s a f g h1 (@lem8232568 _144947 _144962 A B P lt2 s z l f p g a h2 h3 h4 h5)). Qed.
Lemma lem8232621 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term866 A B P z f g a.
Proof. exact (fun h0 : term754 A B P z f g a => @lem8232620 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4 h5). Qed.
Lemma lem8232623 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232624 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term866 A B P z f g a) = ((term747 A B P z f g a) = (term750 A B P z f g a)).
Proof. exact (@lem8232623 ((term747 A B P z f g a) = (term750 A B P z f g a))). Qed.
Lemma lem8232625 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term747 A B P z f g a) = (term750 A B P z f g a).
Proof. exact (EQ_MP (@lem8232624 A B P z f g a) (@lem8232621 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8232641 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232642 {_144962 A B P : Type'} (z : type518 A B P) (p : type560 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term813 _144962 A B P p z _109550 l _109551 _109552) = (term867 _144962 A B P z p _109550 l _109551 _109552).
Proof. exact (@lem8232641 (term754 A B P z _109550 _109551 _109552) (term766 A B P p _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232658 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8232659 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term819 _144962 A B P p _109550 l _109551 _109552) = (term820 _144962 A B P _109550 l p _109551 _109552).
Proof. exact (@lem8232658 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232667 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term868 A B P z _109550 _109551 _109552) = (term868 A B P z _109550 _109551 _109552).
Proof. exact (eq_refl (term868 A B P z _109550 _109551 _109552)). Qed.
Lemma lem8232668 {_144962 A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term867 _144962 A B P z p _109550 l _109551 _109552) = (term869 _144962 A B P z _109550 l p _109551 _109552).
Proof. exact (MK_COMB (@lem8232667 A B P z _109550 _109551 _109552) (@lem8232659 _144962 A B P _109550 l p _109551 _109552)). Qed.
Lemma lem8232672 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232673 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term869 _144962 A B P z _109550 l p _109551 _109552) = (term870 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (@lem8232672 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term754 A B P z _109550 _109551 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232693 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term867 _144962 A B P z p _109550 l _109551 _109552) = (term870 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232668 _144962 A B P z _109550 l p _109551 _109552) (@lem8232673 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232694 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term813 _144962 A B P p z _109550 l _109551 _109552) = (term870 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232642 _144962 A B P z p _109550 l _109551 _109552) (@lem8232693 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232695 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8232696 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term814 _144962 A B P p z _109550 l _109551 _109552) = (term871 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232695 A B P p _109550 _109552) (@lem8232694 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232700 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232701 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term871 _144962 A B P l z _109550 p _109551 _109552) = (term872 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (@lem8232700 ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) (term766 A B P p _109550 _109552) (term873 A B P z _109550 p _109551 _109552)). Qed.
Lemma lem8232717 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232718 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term874 A B P z _109550 p _109551 _109552) = (term875 A B P z _109550 p _109551 _109552).
Proof. exact (@lem8232717 (term754 A B P z _109550 _109551 _109552) (term766 A B P p _109550 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232736 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term829 _144962 A B P _109550 l _109551 _109552) = (term829 _144962 A B P _109550 l _109551 _109552).
Proof. exact (eq_refl (term829 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232737 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term872 _144962 A B P l z _109550 p _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232736 _144962 A B P _109550 l _109551 _109552) (@lem8232718 A B P z _109550 p _109551 _109552)). Qed.
Lemma lem8232748 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term871 _144962 A B P l z _109550 p _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232701 _144962 A B P l z _109550 p _109551 _109552) (@lem8232737 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232749 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term814 _144962 A B P p z _109550 l _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232696 _144962 A B P l z _109550 p _109551 _109552) (@lem8232748 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8232751 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term877 _144962 A B P p z _109550 l _109551 _109552) = (term878 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232750) (@lem8232749 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232777 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8232778 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term789 A B P p z _109550 _109551 _109552) = (term873 A B P z _109550 p _109551 _109552).
Proof. exact (@lem8232777 (term754 A B P z _109550 _109551 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232786 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term767 A B P p _109550 _109552) = (term767 A B P p _109550 _109552).
Proof. exact (eq_refl (term767 A B P p _109550 _109552)). Qed.
Lemma lem8232787 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term794 A B P p z _109550 _109551 _109552) = (term874 A B P z _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232786 A B P p _109550 _109552) (@lem8232778 A B P z _109550 p _109551 _109552)). Qed.
Lemma lem8232791 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232792 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term874 A B P z _109550 p _109551 _109552) = (term875 A B P z _109550 p _109551 _109552).
Proof. exact (@lem8232791 (term754 A B P z _109550 _109551 _109552) (term766 A B P p _109550 _109552) (term766 A B P p _109551 _109552)). Qed.
Lemma lem8232810 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term794 A B P p z _109550 _109551 _109552) = (term875 A B P z _109550 p _109551 _109552).
Proof. exact (TRANS (@lem8232787 A B P z _109550 p _109551 _109552) (@lem8232792 A B P z _109550 p _109551 _109552)). Qed.
Lemma lem8232811 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term829 _144962 A B P _109550 l _109551 _109552) = (term829 _144962 A B P _109550 l _109551 _109552).
Proof. exact (eq_refl (term829 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232812 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term879 _144962 A B P l p z _109550 _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552).
Proof. exact (MK_COMB (@lem8232811 _144962 A B P _109550 l _109551 _109552) (@lem8232810 A B P z _109550 p _109551 _109552)). Qed.
Lemma lem8232823 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : ((term814 _144962 A B P p z _109550 l _109551 _109552) = (term879 _144962 A B P l p z _109550 _109551 _109552)) = ((term876 _144962 A B P l z _109550 p _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552)).
Proof. exact (MK_COMB (@lem8232751 _144962 A B P l z _109550 p _109551 _109552) (@lem8232812 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8232826 (x : Prop) : (x = x) = True.
Proof. exact (@lem8232825 Prop x). Qed.
Lemma lem8232827 {_144962 A B P : Type'} (l : type815 _144962 A B P) (z : type518 A B P) (_109550 : A -> B) (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : ((term876 _144962 A B P l z _109550 p _109551 _109552) = (term876 _144962 A B P l z _109550 p _109551 _109552)) = True.
Proof. exact (@lem8232826 (term876 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232828 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : ((term814 _144962 A B P p z _109550 l _109551 _109552) = (term879 _144962 A B P l p z _109550 _109551 _109552)) = True.
Proof. exact (TRANS (@lem8232823 _144962 A B P l z _109550 p _109551 _109552) (@lem8232827 _144962 A B P l z _109550 p _109551 _109552)). Qed.
Lemma lem8232829 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : True = ((term814 _144962 A B P p z _109550 l _109551 _109552) = (term879 _144962 A B P l p z _109550 _109551 _109552)).
Proof. exact (SYM (@lem8232828 _144962 A B P l p z _109550 _109551 _109552)). Qed.
Lemma lem8232830 {_144962 A B P : Type'} (l : type815 _144962 A B P) (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term814 _144962 A B P p z _109550 l _109551 _109552) = (term879 _144962 A B P l p z _109550 _109551 _109552).
Proof. exact (EQ_MP (@lem8232829 _144962 A B P l p z _109550 _109551 _109552) (@lem0)). Qed.
Lemma lem8232831 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term879 _144962 A B P l p z _109550 _109551 _109552.
Proof. exact (EQ_MP (@lem8232830 _144962 A B P l p z _109550 _109551 _109552) (@lem8232013 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8232833 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8232834 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term879 _144962 A B P l p z _109550 _109551 _109552) = (term880 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (@lem8232833 (term794 A B P p z _109550 _109551 _109552) ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232836 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8232837 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term881 A B P p z _109550 _109551 _109552) = (term882 A B P p z _109550 _109551 _109552).
Proof. exact (@lem8232836 (term766 A B P p _109550 _109552) (term789 A B P p z _109550 _109551 _109552)). Qed.
Lemma lem8232839 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232840 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term845 A B P p _109550 _109552) = (term725 A B P p _109550 _109552).
Proof. exact (@lem8232839 (term725 A B P p _109550 _109552)). Qed.
Lemma lem8232841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8232842 {A B P : Type'} (p : type560 A B P) (_109550 : A -> B) (_109552 : P) : (term846 A B P p _109550 _109552) = (term847 A B P p _109550 _109552).
Proof. exact (MK_COMB (@lem8232841) (@lem8232840 A B P p _109550 _109552)). Qed.
Lemma lem8232844 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8232845 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term883 A B P p z _109550 _109551 _109552) = (term884 A B P p z _109550 _109551 _109552).
Proof. exact (@lem8232844 (term766 A B P p _109551 _109552) (term754 A B P z _109550 _109551 _109552)). Qed.
Lemma lem8232847 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232848 {A B P : Type'} (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term845 A B P p _109551 _109552) = (term725 A B P p _109551 _109552).
Proof. exact (@lem8232847 (term725 A B P p _109551 _109552)). Qed.
Lemma lem8232849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8232850 {A B P : Type'} (p : type560 A B P) (_109551 : A -> B) (_109552 : P) : (term846 A B P p _109551 _109552) = (term847 A B P p _109551 _109552).
Proof. exact (MK_COMB (@lem8232849) (@lem8232848 A B P p _109551 _109552)). Qed.
Lemma lem8232852 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8232853 {A B P : Type'} (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term885 A B P z _109550 _109551 _109552) = ((term747 A B P z _109550 _109551 _109552) = (term750 A B P z _109550 _109551 _109552)).
Proof. exact (@lem8232852 ((term747 A B P z _109550 _109551 _109552) = (term750 A B P z _109550 _109551 _109552))). Qed.
Lemma lem8232854 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term884 A B P p z _109550 _109551 _109552) = (term886 A B P p z _109550 _109551 _109552).
Proof. exact (MK_COMB (@lem8232850 A B P p _109551 _109552) (@lem8232853 A B P z _109550 _109551 _109552)). Qed.
Lemma lem8232855 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term883 A B P p z _109550 _109551 _109552) = (term886 A B P p z _109550 _109551 _109552).
Proof. exact (TRANS (@lem8232845 A B P p z _109550 _109551 _109552) (@lem8232854 A B P p z _109550 _109551 _109552)). Qed.
Lemma lem8232856 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term882 A B P p z _109550 _109551 _109552) = (term887 A B P p z _109550 _109551 _109552).
Proof. exact (MK_COMB (@lem8232842 A B P p _109550 _109552) (@lem8232855 A B P p z _109550 _109551 _109552)). Qed.
Lemma lem8232857 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term881 A B P p z _109550 _109551 _109552) = (term887 A B P p z _109550 _109551 _109552).
Proof. exact (TRANS (@lem8232837 A B P p z _109550 _109551 _109552) (@lem8232856 A B P p z _109550 _109551 _109552)). Qed.
Lemma lem8232858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8232859 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) : (term888 A B P p z _109550 _109551 _109552) = (term889 A B P p z _109550 _109551 _109552).
Proof. exact (MK_COMB (@lem8232858) (@lem8232857 A B P p z _109550 _109551 _109552)). Qed.
Lemma lem8232860 {_144962 A B P : Type'} (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)) = ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552)).
Proof. exact (eq_refl ((term738 _144962 A B P l _109550 _109552) = (term738 _144962 A B P l _109551 _109552))). Qed.
Lemma lem8232861 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term880 _144962 A B P p z _109550 l _109551 _109552) = (term890 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (MK_COMB (@lem8232859 A B P p z _109550 _109551 _109552) (@lem8232860 _144962 A B P _109550 l _109551 _109552)). Qed.
Lemma lem8232862 {_144962 A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_109550 : A -> B) (l : type815 _144962 A B P) (_109551 : A -> B) (_109552 : P) : (term879 _144962 A B P l p z _109550 _109551 _109552) = (term890 _144962 A B P p z _109550 l _109551 _109552).
Proof. exact (TRANS (@lem8232834 _144962 A B P p z _109550 l _109551 _109552) (@lem8232861 _144962 A B P p z _109550 l _109551 _109552)). Qed.
Lemma lem8232864 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term886 A B P p z f g a.
Proof. exact (conj (@lem8232281 A B P p g a h5) (@lem8232625 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8232865 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : term887 A B P p z f g a.
Proof. exact (conj (@lem8232274 A B P p f a h4) (@lem8232864 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8232867 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term890 _144962 A B P p z _109550 l _109551 _109552.
Proof. exact (EQ_MP (@lem8232862 _144962 A B P p z _109550 l _109551 _109552) (@lem8232831 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1)). Qed.
Lemma lem8232868 {_144947 _144962 A B P : Type'} (_109550 : A -> B) (_109551 : A -> B) (_109552 : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term890 _144962 A B P p z _109550 l _109551 _109552.
Proof. exact (@lem8232867 _144947 _144962 A B P _109550 _109551 _109552 p lt2 s z l h1). Qed.
Lemma lem8232869 {_144947 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (h1 : term558 _144947 _144962 A B P p lt2 s z l) : term890 _144962 A B P p z f l g a.
Proof. exact (@lem8232868 _144947 _144962 A B P f g a p lt2 s z l h1). Qed.
Lemma lem8232872 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term741 _144962 A B P f l g a) (h4 : p f a) (h5 : p g a) : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a).
Proof. exact (@lem8232869 _144947 _144962 A B P f g a p lt2 s z l h2 (@lem8232865 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8232873 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : p f a) (h4 : p g a) : term891 _144962 A B P f l g a.
Proof. exact (fun h0 : term741 _144962 A B P f l g a => @lem8232872 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h0 h3 h4). Qed.
Lemma lem8232875 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232876 {_144962 A B P : Type'} (f : A -> B) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term891 _144962 A B P f l g a) = ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a)).
Proof. exact (@lem8232875 ((term738 _144962 A B P l f a) = (term738 _144962 A B P l g a))). Qed.
Lemma lem8232877 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : p f a) (h4 : p g a) : (term738 _144962 A B P l f a) = (term738 _144962 A B P l g a).
Proof. exact (EQ_MP (@lem8232876 _144962 A B P f l g a) (@lem8232873 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h3 h4)). Qed.
Lemma lem8232879 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : term988 _144962 A B P x l f a.
Proof. exact (EQ_MP (@lem8231613 _144962 A B P x l f a) (@lem8231485 _144962 A B P x l f a h1)). Qed.
Lemma lem8232880 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : term1000 _144962 A B P x l f a.
Proof. exact (fun h0 : term989 _144962 A B P x l f a => @lem8232879 _144962 A B P x l f a h1). Qed.
Lemma lem8232882 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8232883 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) : (term1000 _144962 A B P x l f a) = (term988 _144962 A B P x l f a).
Proof. exact (@lem8232882 (term988 _144962 A B P x l f a)). Qed.
Lemma lem8232884 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (a : P) (h1 : term564 _144962 A B P x l f a) : term988 _144962 A B P x l f a.
Proof. exact (EQ_MP (@lem8232883 _144962 A B P x l f a) (@lem8232880 _144962 A B P x l f a h1)). Qed.
Lemma lem8232902 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232903 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term995 _144962 _109555 _109556 _109553 _109554) = (term1001 _144962 _109555 _109556 _109553 _109554).
Proof. exact (@lem8232902 (@I ((list _144962) -> Prop) _109555 _109556) (term1002 _144962 _109554 _109556) (term1003 _144962 _109553 _109554)). Qed.
Lemma lem8232921 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) : (term1004 _144962 _109553 _109555) = (term1004 _144962 _109553 _109555).
Proof. exact (eq_refl (term1004 _144962 _109553 _109555)). Qed.
Lemma lem8232922 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term997 _144962 _109555 _109556 _109553 _109554) = (term1005 _144962 _109555 _109556 _109553 _109554).
Proof. exact (MK_COMB (@lem8232921 _144962 _109553 _109555) (@lem8232903 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232926 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8232927 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1005 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554).
Proof. exact (@lem8232926 (@I ((list _144962) -> Prop) _109555 _109556) (term1007 _144962 _109553 _109555) (term1008 _144962 _109556 _109553 _109554)). Qed.
Lemma lem8232957 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term997 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554).
Proof. exact (TRANS (@lem8232922 _144962 _109555 _109556 _109553 _109554) (@lem8232927 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8232959 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1009 _144962 _109555 _109556 _109553 _109554) = (term1010 _144962 _109555 _109556 _109553 _109554).
Proof. exact (MK_COMB (@lem8232958) (@lem8232957 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232989 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1006 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554).
Proof. exact (eq_refl (term1006 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232990 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : ((term997 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554)) = ((term1006 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554)).
Proof. exact (MK_COMB (@lem8232959 _144962 _109555 _109556 _109553 _109554) (@lem8232989 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232992 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8232993 (x : Prop) : (x = x) = True.
Proof. exact (@lem8232992 Prop x). Qed.
Lemma lem8232994 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : ((term1006 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554)) = True.
Proof. exact (@lem8232993 (term1006 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232995 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : ((term997 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554)) = True.
Proof. exact (TRANS (@lem8232990 _144962 _109555 _109556 _109553 _109554) (@lem8232994 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232996 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : True = ((term997 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554)).
Proof. exact (SYM (@lem8232995 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8232997 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term997 _144962 _109555 _109556 _109553 _109554) = (term1006 _144962 _109555 _109556 _109553 _109554).
Proof. exact (EQ_MP (@lem8232996 _144962 _109555 _109556 _109553 _109554) (@lem0)). Qed.
Lemma lem8232998 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : term1006 _144962 _109555 _109556 _109553 _109554.
Proof. exact (EQ_MP (@lem8232997 _144962 _109555 _109556 _109553 _109554) (@lem8232032 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8233000 (b : Prop) (a : Prop) : (a \/ b) = (term839 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8233001 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) (_109555 : type1143 _144962) (_109556 : list _144962) : (term1006 _144962 _109555 _109556 _109553 _109554) = (term1011 _144962 _109553 _109554 _109555 _109556).
Proof. exact (@lem8233000 (term1012 _144962 _109555 _109556 _109553 _109554) (@I ((list _144962) -> Prop) _109555 _109556)). Qed.
Lemma lem8233003 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8233004 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1013 _144962 _109555 _109556 _109553 _109554) = (term1014 _144962 _109555 _109556 _109553 _109554).
Proof. exact (@lem8233003 (term1007 _144962 _109553 _109555) (term1008 _144962 _109556 _109553 _109554)). Qed.
Lemma lem8233006 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8233007 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) : (term1015 _144962 _109553 _109555) = (_109553 = _109555).
Proof. exact (@lem8233006 (_109553 = _109555)). Qed.
Lemma lem8233008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233009 {_144962 : Type'} (_109553 : type1143 _144962) (_109555 : type1143 _144962) : (term1016 _144962 _109553 _109555) = (term1017 _144962 _109553 _109555).
Proof. exact (MK_COMB (@lem8233008) (@lem8233007 _144962 _109553 _109555)). Qed.
Lemma lem8233011 (a : Prop) (b : Prop) : (term841 a b) = (term842 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8233012 {_144962 : Type'} (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1018 _144962 _109556 _109553 _109554) = (term1019 _144962 _109556 _109553 _109554).
Proof. exact (@lem8233011 (term1002 _144962 _109554 _109556) (term1003 _144962 _109553 _109554)). Qed.
Lemma lem8233014 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8233015 {_144962 : Type'} (_109554 : list _144962) (_109556 : list _144962) : (term1020 _144962 _109554 _109556) = (_109554 = _109556).
Proof. exact (@lem8233014 (_109554 = _109556)). Qed.
Lemma lem8233016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8233017 {_144962 : Type'} (_109554 : list _144962) (_109556 : list _144962) : (term1021 _144962 _109554 _109556) = (term1022 _144962 _109554 _109556).
Proof. exact (MK_COMB (@lem8233016) (@lem8233015 _144962 _109554 _109556)). Qed.
Lemma lem8233019 (a : Prop) : (term36 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8233020 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) : (term1023 _144962 _109553 _109554) = (@I ((list _144962) -> Prop) _109553 _109554).
Proof. exact (@lem8233019 (@I ((list _144962) -> Prop) _109553 _109554)). Qed.
Lemma lem8233021 {_144962 : Type'} (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1019 _144962 _109556 _109553 _109554) = (term1024 _144962 _109556 _109553 _109554).
Proof. exact (MK_COMB (@lem8233017 _144962 _109554 _109556) (@lem8233020 _144962 _109553 _109554)). Qed.
Lemma lem8233022 {_144962 : Type'} (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1018 _144962 _109556 _109553 _109554) = (term1024 _144962 _109556 _109553 _109554).
Proof. exact (TRANS (@lem8233012 _144962 _109556 _109553 _109554) (@lem8233021 _144962 _109556 _109553 _109554)). Qed.
Lemma lem8233023 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1014 _144962 _109555 _109556 _109553 _109554) = (term1025 _144962 _109555 _109556 _109553 _109554).
Proof. exact (MK_COMB (@lem8233009 _144962 _109553 _109555) (@lem8233022 _144962 _109556 _109553 _109554)). Qed.
Lemma lem8233024 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1013 _144962 _109555 _109556 _109553 _109554) = (term1025 _144962 _109555 _109556 _109553 _109554).
Proof. exact (TRANS (@lem8233004 _144962 _109555 _109556 _109553 _109554) (@lem8233023 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8233025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8233026 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) (_109553 : type1143 _144962) (_109554 : list _144962) : (term1026 _144962 _109555 _109556 _109553 _109554) = (term1027 _144962 _109555 _109556 _109553 _109554).
Proof. exact (MK_COMB (@lem8233025) (@lem8233024 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8233027 {_144962 : Type'} (_109555 : type1143 _144962) (_109556 : list _144962) : (@I ((list _144962) -> Prop) _109555 _109556) = (@I ((list _144962) -> Prop) _109555 _109556).
Proof. exact (eq_refl (@I ((list _144962) -> Prop) _109555 _109556)). Qed.
Lemma lem8233028 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) (_109555 : type1143 _144962) (_109556 : list _144962) : (term1011 _144962 _109553 _109554 _109555 _109556) = (term1028 _144962 _109553 _109554 _109555 _109556).
Proof. exact (MK_COMB (@lem8233026 _144962 _109555 _109556 _109553 _109554) (@lem8233027 _144962 _109555 _109556)). Qed.
Lemma lem8233029 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) (_109555 : type1143 _144962) (_109556 : list _144962) : (term1006 _144962 _109555 _109556 _109553 _109554) = (term1028 _144962 _109553 _109554 _109555 _109556).
Proof. exact (TRANS (@lem8233001 _144962 _109553 _109554 _109555 _109556) (@lem8233028 _144962 _109553 _109554 _109555 _109556)). Qed.
Lemma lem8233031 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term1029 _144962 A B P g x l f a.
Proof. exact (conj (@lem8232877 _144947 _144962 A B P lt2 s z l f p g a h1 h2 h4 h5) (@lem8232884 _144962 A B P x l f a h3)). Qed.
Lemma lem8233032 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term1030 _144962 A B P g x l f a.
Proof. exact (conj (@lem8232267 _144962 x) (@lem8233031 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233034 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) (_109555 : type1143 _144962) (_109556 : list _144962) : term1028 _144962 _109553 _109554 _109555 _109556.
Proof. exact (EQ_MP (@lem8233029 _144962 _109553 _109554 _109555 _109556) (@lem8232998 _144962 _109555 _109556 _109553 _109554)). Qed.
Lemma lem8233035 {_144962 : Type'} (_109553 : type1143 _144962) (_109554 : list _144962) (_109555 : type1143 _144962) (_109556 : list _144962) : term1028 _144962 _109553 _109554 _109555 _109556.
Proof. exact (@lem8233034 _144962 _109553 _109554 _109555 _109556). Qed.
Lemma lem8233036 {_144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term1031 _144962 A B P f x l g a.
Proof. exact (@lem8233035 _144962 (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) (term738 _144962 A B P l f a) (@I (_144962 -> (list _144962) -> Prop) (@List.In _144962) x) (term738 _144962 A B P l g a)). Qed.
Lemma lem8233039 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term988 _144962 A B P x l g a.
Proof. exact (@lem8233036 _144962 A B P f x l g a (@lem8233032 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233040 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term1000 _144962 A B P x l g a.
Proof. exact (fun h0 : term989 _144962 A B P x l g a => @lem8233039 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5). Qed.
Lemma lem8233042 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8233043 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1000 _144962 A B P x l g a) = (term988 _144962 A B P x l g a).
Proof. exact (@lem8233042 (term988 _144962 A B P x l g a)). Qed.
Lemma lem8233044 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term988 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8233043 _144962 A B P x l g a) (@lem8233040 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233047 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8233049 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term989 _144962 A B P x l g a) = (term1032 _144962 A B P x l g a).
Proof. exact (@lem8233047 (term988 _144962 A B P x l g a)). Qed.
Lemma lem8233052 {_144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (h1 : term939 _144962 A B P x l g a) : term1032 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8233049 _144962 A B P x l g a) (@lem8231977 _144962 A B P x l g a h1)). Qed.
Lemma lem8233055 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (@lem8233052 _144962 A B P x l g a h3 (@lem8233044 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h4 h5 h6)). Qed.
Lemma lem8233056 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : term69.
Proof. exact (fun h0 : ~ False => @lem8233055 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5 h6). Qed.
Lemma lem8233058 (p : Prop) : (term67 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8233059 : term69 = False.
Proof. exact (@lem8233058 False). Qed.
Lemma lem8233060 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (z : type518 A B P) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term558 _144947 _144962 A B P p lt2 s z l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233059) (@lem8233056 _144947 _144962 A B P lt2 s z x l f p g a h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8233061 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (ex_elim (@lem8231404 _144947 _144962 A B P p lt2 s l h2) (fun z : type518 A B P => fun h0 : term560 _144947 _144962 A B P p lt2 s l z => @lem8233060 _144947 _144962 A B P lt2 s z x l f p g a h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem8233062 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (term939 _144962 A B P x l g a) = False.
Proof. exact (prop_ext (fun h7 : term939 _144962 A B P x l g a => @lem8233061 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8231491 _144962 A B P x l g a h3)). Qed.
Lemma lem8233063 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233062 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8231491 _144962 A B P x l g a h3)). Qed.
Lemma lem8233064 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (term564 _144962 A B P x l f a) = False.
Proof. exact (prop_ext (fun h7 : term564 _144962 A B P x l f a => @lem8233063 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8231485 _144962 A B P x l f a h4)). Qed.
Lemma lem8233065 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233064 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8231485 _144962 A B P x l f a h4)). Qed.
Lemma lem8233066 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (p g a) = False.
Proof. exact (prop_ext (fun h7 : p g a => @lem8233065 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8231416 A B P p g a h6)). Qed.
Lemma lem8233067 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233066 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8231416 A B P p g a h6)). Qed.
Lemma lem8233068 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (p f a) = False.
Proof. exact (prop_ext (fun h7 : p f a => @lem8233067 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8231410 A B P p f a h5)). Qed.
Lemma lem8233069 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233068 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8231410 A B P p f a h5)). Qed.
Lemma lem8233070 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (term939 _144962 A B P x l g a) = False.
Proof. exact (prop_ext (fun h7 : term939 _144962 A B P x l g a => @lem8233069 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8231078 _144962 A B P x l g a h3)). Qed.
Lemma lem8233071 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233070 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8231078 _144962 A B P x l g a h3)). Qed.
Lemma lem8233072 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term938 _144962 A B P x l g a.
Proof. exact (fun h0 : term939 _144962 A B P x l g a => @lem8233071 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8233073 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term564 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8231077 _144962 A B P x l g a) (@lem8233072 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233074 {_144947 _144962 A B P : Type'} (x : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) (h4 : p g a) : term946 _144962 A B P f x l g a.
Proof. exact (fun h0 : term564 _144962 A B P x l f a => @lem8233073 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h0 h3 h4). Qed.
Lemma lem8233075 {_144947 _144962 A B P : Type'} (x : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : p f a) (h3 : p g a) : term948 _144947 _144962 A B P lt2 s f x l g a.
Proof. exact (fun h0 : term222 _144947 A B P lt2 s a f g => @lem8233074 _144947 _144962 A B P x lt2 s l f p g a h0 h1 h2 h3). Qed.
Lemma lem8233076 {_144947 _144962 A B P : Type'} (x : _144962) (g : A -> B) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : p f a) : term950 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : p g a => @lem8233075 _144947 _144962 A B P x lt2 s l f p g a h1 h2 h0). Qed.
Lemma lem8233077 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term952 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : p f a => @lem8233076 _144947 _144962 A B P x g lt2 s l p f a h1 h0). Qed.
Lemma lem8233078 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term953 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (fun h0 : term87 _144947 _144962 A B P p lt2 s l => @lem8233077 _144947 _144962 A B P f x g a p lt2 s l h0). Qed.
Lemma lem8233083 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term957 _144947 _144962 A B P lt2 s f x l g a.
Proof. exact (fun p : type560 A B P => @lem8233078 _144947 _144962 A B P p lt2 s f x l g a). Qed.
Lemma lem8233088 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term961 _144947 _144962 A B P s f x l g a.
Proof. exact (fun lt2 : type1470 _144947 A => @lem8233083 _144947 _144962 A B P lt2 s f x l g a). Qed.
Lemma lem8233093 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term965 _144947 _144962 A B P f x l g a.
Proof. exact (fun s : P -> _144947 => @lem8233088 _144947 _144962 A B P s f x l g a). Qed.
Lemma lem8233098 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term969 _144947 _144962 A B P x l g a.
Proof. exact (fun f : A -> B => @lem8233093 _144947 _144962 A B P f x l g a). Qed.
Lemma lem8233103 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : term973 _144947 _144962 A B P l g a.
Proof. exact (fun x : _144962 => @lem8233098 _144947 _144962 A B P x l g a). Qed.
Lemma lem8233108 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : term977 _144947 _144962 A B P g a.
Proof. exact (fun l : type815 _144962 A B P => @lem8233103 _144947 _144962 A B P l g a). Qed.
Lemma lem8233113 {_144947 _144962 A B P : Type'} (a : P) : term981 _144947 _144962 A B P a.
Proof. exact (fun g : A -> B => @lem8233108 _144947 _144962 A B P g a). Qed.
Lemma lem8233118 {_144947 _144962 A B P : Type'} : term985 _144947 _144962 A B P.
Proof. exact (fun a : P => @lem8233113 _144947 _144962 A B P a). Qed.
Lemma lem8233119 {_144947 _144962 A B P : Type'} : term984 _144947 _144962 A B P.
Proof. exact (EQ_MP (@lem8231068 _144947 _144962 A B P) (@lem8233118 _144947 _144962 A B P)). Qed.
Lemma lem8233120 {_144947 _144962 A B P : Type'} (a : P) : term1033 _144947 _144962 A B P a.
Proof. exact (@lem8233119 _144947 _144962 A B P a). Qed.
Lemma lem8233121 {_144947 _144962 A B P : Type'} (a : P) : (term1033 _144947 _144962 A B P a) = (term980 _144947 _144962 A B P a).
Proof. exact (eq_refl (term1033 _144947 _144962 A B P a)). Qed.
Lemma lem8233122 {_144947 _144962 A B P : Type'} (a : P) : term980 _144947 _144962 A B P a.
Proof. exact (EQ_MP (@lem8233121 _144947 _144962 A B P a) (@lem8233120 _144947 _144962 A B P a)). Qed.
Lemma lem8233123 {_144947 _144962 A B P : Type'} (a : P) (g : A -> B) : term1034 _144947 _144962 A B P a g.
Proof. exact (@lem8233122 _144947 _144962 A B P a g). Qed.
Lemma lem8233124 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : (term1034 _144947 _144962 A B P a g) = (term976 _144947 _144962 A B P g a).
Proof. exact (eq_refl (term1034 _144947 _144962 A B P a g)). Qed.
Lemma lem8233125 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) : term976 _144947 _144962 A B P g a.
Proof. exact (EQ_MP (@lem8233124 _144947 _144962 A B P g a) (@lem8233123 _144947 _144962 A B P a g)). Qed.
Lemma lem8233126 {_144947 _144962 A B P : Type'} (g : A -> B) (a : P) (l : type815 _144962 A B P) : term1035 _144947 _144962 A B P g a l.
Proof. exact (@lem8233125 _144947 _144962 A B P g a l). Qed.
Lemma lem8233127 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1035 _144947 _144962 A B P g a l) = (term972 _144947 _144962 A B P l g a).
Proof. exact (eq_refl (term1035 _144947 _144962 A B P g a l)). Qed.
Lemma lem8233128 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) : term972 _144947 _144962 A B P l g a.
Proof. exact (EQ_MP (@lem8233127 _144947 _144962 A B P l g a) (@lem8233126 _144947 _144962 A B P g a l)). Qed.
Lemma lem8233129 {_144947 _144962 A B P : Type'} (l : type815 _144962 A B P) (g : A -> B) (a : P) (x : _144962) : term1036 _144947 _144962 A B P l g a x.
Proof. exact (@lem8233128 _144947 _144962 A B P l g a x). Qed.
Lemma lem8233130 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1036 _144947 _144962 A B P l g a x) = (term968 _144947 _144962 A B P x l g a).
Proof. exact (eq_refl (term1036 _144947 _144962 A B P l g a x)). Qed.
Lemma lem8233131 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term968 _144947 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8233130 _144947 _144962 A B P x l g a) (@lem8233129 _144947 _144962 A B P l g a x)). Qed.
Lemma lem8233132 {_144947 _144962 A B P : Type'} (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (f : A -> B) : term1037 _144947 _144962 A B P x l g a f.
Proof. exact (@lem8233131 _144947 _144962 A B P x l g a f). Qed.
Lemma lem8233133 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1037 _144947 _144962 A B P x l g a f) = (term964 _144947 _144962 A B P f x l g a).
Proof. exact (eq_refl (term1037 _144947 _144962 A B P x l g a f)). Qed.
Lemma lem8233134 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term964 _144947 _144962 A B P f x l g a.
Proof. exact (EQ_MP (@lem8233133 _144947 _144962 A B P f x l g a) (@lem8233132 _144947 _144962 A B P x l g a f)). Qed.
Lemma lem8233135 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (s : P -> _144947) : term1038 _144947 _144962 A B P f x l g a s.
Proof. exact (@lem8233134 _144947 _144962 A B P f x l g a s). Qed.
Lemma lem8233136 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1038 _144947 _144962 A B P f x l g a s) = (term960 _144947 _144962 A B P s f x l g a).
Proof. exact (eq_refl (term1038 _144947 _144962 A B P f x l g a s)). Qed.
Lemma lem8233137 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term960 _144947 _144962 A B P s f x l g a.
Proof. exact (EQ_MP (@lem8233136 _144947 _144962 A B P s f x l g a) (@lem8233135 _144947 _144962 A B P f x l g a s)). Qed.
Lemma lem8233138 {_144947 _144962 A B P : Type'} (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (lt2 : type1470 _144947 A) : term1039 _144947 _144962 A B P s f x l g a lt2.
Proof. exact (@lem8233137 _144947 _144962 A B P s f x l g a lt2). Qed.
Lemma lem8233139 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1039 _144947 _144962 A B P s f x l g a lt2) = (term956 _144947 _144962 A B P lt2 s f x l g a).
Proof. exact (eq_refl (term1039 _144947 _144962 A B P s f x l g a lt2)). Qed.
Lemma lem8233140 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term956 _144947 _144962 A B P lt2 s f x l g a.
Proof. exact (EQ_MP (@lem8233139 _144947 _144962 A B P lt2 s f x l g a) (@lem8233138 _144947 _144962 A B P s f x l g a lt2)). Qed.
Lemma lem8233141 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) (p : type560 A B P) : term1040 _144947 _144962 A B P lt2 s f x l g a p.
Proof. exact (@lem8233140 _144947 _144962 A B P lt2 s f x l g a p). Qed.
Lemma lem8233142 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : (term1040 _144947 _144962 A B P lt2 s f x l g a p) = (term940 _144947 _144962 A B P p lt2 s f x l g a).
Proof. exact (eq_refl (term1040 _144947 _144962 A B P lt2 s f x l g a p)). Qed.
Lemma lem8233143 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (EQ_MP (@lem8233142 _144947 _144962 A B P p lt2 s f x l g a) (@lem8233141 _144947 _144962 A B P lt2 s f x l g a p)). Qed.
Lemma lem8233145 {_144947 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (x : _144962) (l : type815 _144962 A B P) (g : A -> B) (a : P) : term940 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8230727 _144947 _144962 A B P p lt2 s f x l g a (@lem8233143 _144947 _144962 A B P p lt2 s f x l g a)). Qed.
Lemma lem8233146 {_144947 _144962 A B P : Type'} (f : A -> B) (x : _144962) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) : term951 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8233145 _144947 _144962 A B P p lt2 s f x l g a (@lem8227199 _144947 _144962 A B P p lt2 s l h1)). Qed.
Lemma lem8233147 {_144947 _144962 A B P : Type'} (x : _144962) (g : A -> B) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : p f a) : term949 _144947 _144962 A B P p lt2 s f x l g a.
Proof. exact (@lem8233146 _144947 _144962 A B P f x g a p lt2 s l h1 (@lem8227202 A B P p f a h2)). Qed.
Lemma lem8233148 {_144947 _144962 A B P : Type'} (x : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : p f a) (h3 : p g a) : term947 _144947 _144962 A B P lt2 s f x l g a.
Proof. exact (@lem8233147 _144947 _144962 A B P x g lt2 s l p f a h1 h2 (@lem8227204 A B P p g a h3)). Qed.
Lemma lem8233149 {_144947 _144962 A B P : Type'} (x : _144962) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : p f a) (h4 : p g a) : term945 _144962 A B P f x l g a.
Proof. exact (@lem8233148 _144947 _144962 A B P x lt2 s l f p g a h2 h3 h4 (@lem8227203 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8233150 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term938 _144962 A B P x l g a.
Proof. exact (@lem8233149 _144947 _144962 A B P x lt2 s l f p g a h1 h2 h4 h5 (@lem8230561 _144962 A B P x l f a h3)). Qed.
Lemma lem8233151 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (@lem8233150 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h4 h5 h6 (@lem8230711 _144962 A B P x l g a h3)). Qed.
Lemma lem8233152 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (term939 _144962 A B P x l g a) = False.
Proof. exact (prop_ext (fun h7 : term939 _144962 A B P x l g a => @lem8233151 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8230711 _144962 A B P x l g a h3)). Qed.
Lemma lem8233153 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term939 _144962 A B P x l g a) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : False.
Proof. exact (EQ_MP (@lem8233152 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8230711 _144962 A B P x l g a h3)). Qed.
Lemma lem8233154 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term938 _144962 A B P x l g a.
Proof. exact (fun h0 : term939 _144962 A B P x l g a => @lem8233153 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8233155 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term564 _144962 A B P x l g a.
Proof. exact (EQ_MP (@lem8230710 _144962 A B P x l g a) (@lem8233154 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233156 {_144947 _144962 A B P : Type'} (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term564 _144962 A B P x l f a) (h4 : p f a) (h5 : p g a) : term226 _144947 _144962 A B P p x l lt2 s a f g.
Proof. exact (EQ_MP (@lem8230706 _144947 _144962 A B P lt2 s x l f p g a h1 h3 h4 h5) (@lem8233155 _144947 _144962 A B P lt2 s x l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233157 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (h f a x) = (h g a x).
Proof. exact (@lem8230620 _144947 _144956 _144962 A B P f g a x p l lt2 s h h2 (@lem8233156 _144947 _144962 A B P lt2 s x l f p g a h1 h3 h4 h5 h6)). Qed.
Lemma lem8233158 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (term564 _144962 A B P x l f a) = ((h f a x) = (h g a x)).
Proof. exact (prop_ext (fun h7 : term564 _144962 A B P x l f a => @lem8233157 _144947 _144956 _144962 A B P h lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (fun h7 : (h f a x) = (h g a x) => @lem8230561 _144962 A B P x l f a h4)). Qed.
Lemma lem8233159 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (x : _144962) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : term564 _144962 A B P x l f a) (h5 : p f a) (h6 : p g a) : (h f a x) = (h g a x).
Proof. exact (EQ_MP (@lem8233158 _144947 _144956 _144962 A B P h lt2 s x l f p g a h1 h2 h3 h4 h5 h6) (@lem8230561 _144962 A B P x l f a h4)). Qed.
Lemma lem8233160 {_144947 _144956 _144962 A B P : Type'} (x : _144962) (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term914 _144956 _144962 A B P l f h g a x.
Proof. exact (fun h0 : term564 _144962 A B P x l f a => @lem8233159 _144947 _144956 _144962 A B P h lt2 s x l f p g a h1 h2 h3 h0 h4 h5). Qed.
Lemma lem8233165 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term917 _144956 _144962 A B P l f h g a.
Proof. exact (fun x : _144962 => @lem8233160 _144947 _144956 _144962 A B P x h lt2 s l f p g a h1 h2 h3 h4 h5). Qed.
Lemma lem8233166 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term903 _144956 _144962 A B P h g l f a.
Proof. exact (EQ_MP (@lem8230560 _144956 _144962 A B P h g l f a) (@lem8233165 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233167 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (term305 _144956 _144962 A B P h l f a) = (term1041 _144956 _144962 A B P h g l f a).
Proof. exact (@lem8230522 _144956 _144962 A B P h g l f a (@lem8233166 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233168 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : term1042 _144956 _144962 A B P h g l f a.
Proof. exact (conj (@lem8230518 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5) (@lem8233167 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233169 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (@lem8227208 _144956 _144962 A B P f h l g a (@lem8233168 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5)). Qed.
Lemma lem8233170 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term347 _144947 A B P p lt2 s a f g) : term348 _144947 A B P p lt2 s a f g.
Proof. exact (proj2 (@lem8227200 _144947 A B P p lt2 s a f g h1)). Qed.
Lemma lem8233171 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term347 _144947 A B P p lt2 s a f g) : p f a.
Proof. exact (proj1 (@lem8227200 _144947 A B P p lt2 s a f g h1)). Qed.
Lemma lem8233172 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term348 _144947 A B P p lt2 s a f g) : term222 _144947 A B P lt2 s a f g.
Proof. exact (proj2 (@lem8227201 _144947 A B P p lt2 s a f g h1)). Qed.
Lemma lem8233173 {_144947 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term348 _144947 A B P p lt2 s a f g) : p g a.
Proof. exact (proj1 (@lem8227201 _144947 A B P p lt2 s a f g h1)). Qed.
Lemma lem8233174 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (term222 _144947 A B P lt2 s a f g) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h6 : term222 _144947 A B P lt2 s a f g => @lem8233169 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5) (fun h6 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8227203 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8233175 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233174 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5) (@lem8227203 _144947 A B P lt2 s a f g h1)). Qed.
Lemma lem8233176 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (p g a) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h6 : p g a => @lem8233175 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5) (fun h6 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8227204 A B P p g a h5)). Qed.
Lemma lem8233177 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term222 _144947 A B P lt2 s a f g) (h2 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h3 : term87 _144947 _144962 A B P p lt2 s l) (h4 : p f a) (h5 : p g a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233176 _144947 _144956 _144962 A B P h lt2 s l f p g a h1 h2 h3 h4 h5) (@lem8227204 A B P p g a h5)). Qed.
Lemma lem8233178 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) (h5 : p g a) : (term222 _144947 A B P lt2 s a f g) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h6 : term222 _144947 A B P lt2 s a f g => @lem8233177 _144947 _144956 _144962 A B P h lt2 s l f p g a h6 h1 h2 h4 h5) (fun h6 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8233172 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233179 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (f : A -> B) (p : type560 A B P) (g : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) (h5 : p g a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233178 _144947 _144956 _144962 A B P h l lt2 s f p g a h1 h2 h3 h4 h5) (@lem8233172 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233180 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) : (p g a) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h5 : p g a => @lem8233179 _144947 _144956 _144962 A B P h l lt2 s f p g a h1 h2 h3 h4 h5) (fun h5 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8233173 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233181 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233180 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h3 h4) (@lem8233173 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233182 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) : (p f a) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h5 : p f a => @lem8233181 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h3 h4) (fun h5 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8227202 A B P p f a h4)). Qed.
Lemma lem8233183 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term348 _144947 A B P p lt2 s a f g) (h4 : p f a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233182 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h3 h4) (@lem8227202 A B P p f a h4)). Qed.
Lemma lem8233184 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term347 _144947 A B P p lt2 s a f g) (h4 : p f a) : (term348 _144947 A B P p lt2 s a f g) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h5 : term348 _144947 A B P p lt2 s a f g => @lem8233183 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h5 h4) (fun h5 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8233170 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233185 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (g : A -> B) (p : type560 A B P) (f : A -> B) (a : P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term347 _144947 A B P p lt2 s a f g) (h4 : p f a) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233184 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h3 h4) (@lem8233170 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233186 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term347 _144947 A B P p lt2 s a f g) : (p f a) = ((term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a)).
Proof. exact (prop_ext (fun h4 : p f a => @lem8233185 _144947 _144956 _144962 A B P h l lt2 s g p f a h1 h2 h3 h4) (fun h4 : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a) => @lem8233171 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233187 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (a : P) (f : A -> B) (g : A -> B) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) (h3 : term347 _144947 A B P p lt2 s a f g) : (term305 _144956 _144962 A B P h l f a) = (term305 _144956 _144962 A B P h l g a).
Proof. exact (EQ_MP (@lem8233186 _144947 _144956 _144962 A B P h l p lt2 s a f g h1 h2 h3) (@lem8233171 _144947 A B P p lt2 s a f g h3)). Qed.
Lemma lem8233188 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term313 _144947 _144956 _144962 A B P p lt2 s f h l g a.
Proof. exact (fun h0 : term347 _144947 A B P p lt2 s a f g => @lem8233187 _144947 _144956 _144962 A B P h l p lt2 s a f g h1 h2 h0). Qed.
Lemma lem8233193 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (g : A -> B) (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term317 _144947 _144956 _144962 A B P p lt2 s f h l g.
Proof. exact (fun a : P => @lem8233188 _144947 _144956 _144962 A B P f g a h p lt2 s l h1 h2). Qed.
Lemma lem8233198 {_144947 _144956 _144962 A B P : Type'} (f : A -> B) (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term321 _144947 _144956 _144962 A B P p lt2 s f h l.
Proof. exact (fun g : A -> B => @lem8233193 _144947 _144956 _144962 A B P f g h p lt2 s l h1 h2). Qed.
Lemma lem8233203 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term324 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (fun f : A -> B => @lem8233198 _144947 _144956 _144962 A B P f h p lt2 s l h1 h2). Qed.
Lemma lem8233204 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : term286 _144947 _144956 _144962 A B P p l lt2 s h.
Proof. exact (proj2 (@lem8227197 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233205 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : term87 _144947 _144962 A B P p lt2 s l.
Proof. exact (proj1 (@lem8227197 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233206 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : (term286 _144947 _144956 _144962 A B P p l lt2 s h) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (prop_ext (fun h3 : term286 _144947 _144956 _144962 A B P p l lt2 s h => @lem8233203 _144947 _144956 _144962 A B P h p lt2 s l h1 h2) (fun h3 : term324 _144947 _144956 _144962 A B P p lt2 s h l => @lem8227198 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233207 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term324 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (EQ_MP (@lem8233206 _144947 _144956 _144962 A B P h p lt2 s l h1 h2) (@lem8227198 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233208 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : (term87 _144947 _144962 A B P p lt2 s l) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (prop_ext (fun h3 : term87 _144947 _144962 A B P p lt2 s l => @lem8233207 _144947 _144956 _144962 A B P h p lt2 s l h1 h2) (fun h3 : term324 _144947 _144956 _144962 A B P p lt2 s h l => @lem8227199 _144947 _144962 A B P p lt2 s l h2)). Qed.
Lemma lem8233209 {_144947 _144956 _144962 A B P : Type'} (h : type889 _144956 _144962 A B P) (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (l : type815 _144962 A B P) (h1 : term286 _144947 _144956 _144962 A B P p l lt2 s h) (h2 : term87 _144947 _144962 A B P p lt2 s l) : term324 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (EQ_MP (@lem8233208 _144947 _144956 _144962 A B P h p lt2 s l h1 h2) (@lem8227199 _144947 _144962 A B P p lt2 s l h2)). Qed.
Lemma lem8233210 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : (term286 _144947 _144956 _144962 A B P p l lt2 s h) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (prop_ext (fun h3 : term286 _144947 _144956 _144962 A B P p l lt2 s h => @lem8233209 _144947 _144956 _144962 A B P h p lt2 s l h3 h1) (fun h3 : term324 _144947 _144956 _144962 A B P p lt2 s h l => @lem8233204 _144947 _144956 _144962 A B P p l lt2 s h h2)). Qed.
Lemma lem8233211 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term87 _144947 _144962 A B P p lt2 s l) (h2 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : term324 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (EQ_MP (@lem8233210 _144947 _144956 _144962 A B P p l lt2 s h h1 h2) (@lem8233204 _144947 _144956 _144962 A B P p l lt2 s h h2)). Qed.
Lemma lem8233212 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : (term87 _144947 _144962 A B P p lt2 s l) = (term324 _144947 _144956 _144962 A B P p lt2 s h l).
Proof. exact (prop_ext (fun h2 : term87 _144947 _144962 A B P p lt2 s l => @lem8233211 _144947 _144956 _144962 A B P p l lt2 s h h2 h1) (fun h2 : term324 _144947 _144956 _144962 A B P p lt2 s h l => @lem8233205 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233213 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (l : type815 _144962 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (h1 : term288 _144947 _144956 _144962 A B P p l lt2 s h) : term324 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (EQ_MP (@lem8233212 _144947 _144956 _144962 A B P p l lt2 s h h1) (@lem8233205 _144947 _144956 _144962 A B P p l lt2 s h h1)). Qed.
Lemma lem8233214 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) (l : type815 _144962 A B P) : term326 _144947 _144956 _144962 A B P p lt2 s h l.
Proof. exact (fun h0 : term288 _144947 _144956 _144962 A B P p l lt2 s h => @lem8233213 _144947 _144956 _144962 A B P p l lt2 s h h0). Qed.
Lemma lem8233219 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) (h : type889 _144956 _144962 A B P) : term330 _144947 _144956 _144962 A B P p lt2 s h.
Proof. exact (fun l : type815 _144962 A B P => @lem8233214 _144947 _144956 _144962 A B P p lt2 s h l). Qed.
Lemma lem8233224 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) (s : P -> _144947) : term334 _144947 _144956 _144962 A B P p lt2 s.
Proof. exact (fun h : type889 _144956 _144962 A B P => @lem8233219 _144947 _144956 _144962 A B P p lt2 s h). Qed.
Lemma lem8233229 {_144947 _144956 _144962 A B P : Type'} (p : type560 A B P) (lt2 : type1470 _144947 A) : term338 _144947 _144956 _144962 A B P p lt2.
Proof. exact (fun s : P -> _144947 => @lem8233224 _144947 _144956 _144962 A B P p lt2 s). Qed.
Lemma lem8233234 {_144947 _144956 _144962 A B P : Type'} (lt2 : type1470 _144947 A) : term342 _144947 _144956 _144962 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8233229 _144947 _144956 _144962 A B P p lt2). Qed.
Lemma lem8233239 {_144947 _144956 _144962 A B P : Type'} : term346 _144947 _144956 _144962 A B P.
Proof. exact (fun lt2 : type1470 _144947 A => @lem8233234 _144947 _144956 _144962 A B P lt2). Qed.
Lemma lem8233240 {_144947 _144956 _144962 A B P : Type'} : term345 _144947 _144956 _144962 A B P.
Proof. exact (EQ_MP (@lem8227196 _144947 _144956 _144962 A B P) (@lem8233239 _144947 _144956 _144962 A B P)). Qed.

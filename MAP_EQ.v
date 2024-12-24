Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem1118665 {A B : Type'} : term0 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1118666 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem1118665 A B f). Qed.
Lemma lem1118667 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem1118668 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem1118667 A B f) (@lem1118666 A B f)). Qed.
Lemma lem1118669 {A B : Type'} (f : A -> B) (h : A) : term3 A B f h.
Proof. exact (@lem1118668 A B f h). Qed.
Lemma lem1118670 {A B : Type'} (h : A) (f : A -> B) : (term3 A B f h) = (term4 A B h f).
Proof. exact (eq_refl (term3 A B f h)). Qed.
Lemma lem1118671 {A B : Type'} (h : A) (f : A -> B) : term4 A B h f.
Proof. exact (EQ_MP (@lem1118670 A B h f) (@lem1118669 A B f h)). Qed.
Lemma lem1118672 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term5 A B h f t.
Proof. exact (@lem1118671 A B h f t). Qed.
Lemma lem1118673 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term5 A B h f t) = ((term6 A B f h t) = (term7 A B h f t)).
Proof. exact (eq_refl (term5 A B h f t)). Qed.
Lemma lem1118675 {A B : Type'} : term8 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1118676 {A B : Type'} (f : A -> B) : term9 A B f.
Proof. exact (@lem1118675 A B f). Qed.
Lemma lem1118677 {A B : Type'} (f : A -> B) : (term9 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term9 A B f)). Qed.
Lemma lem1118680 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1118681 {_26299 : Type'} (P : type1143 _26299) : term10 _26299 P.
Proof. exact (@lem1118680 _26299 P). Qed.
Lemma lem1118682 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term11 _26299 _26310 f g.
Proof. exact (@lem1118681 _26299 (term12 _26299 _26310 f g)). Qed.
Lemma lem1118683 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term13 _26299 _26310 f g) = (term14 _26299 _26310 f g).
Proof. exact (eq_refl (term13 _26299 _26310 f g)). Qed.
Lemma lem1118684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1118685 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term15 _26299 _26310 f g) = (term16 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118684) (@lem1118683 _26299 _26310 f g)). Qed.
Lemma lem1118686 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term17 _26299 _26310 f g t) = (term18 _26299 _26310 f g t).
Proof. exact (eq_refl (term17 _26299 _26310 f g t)). Qed.
Lemma lem1118687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118688 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term19 _26299 _26310 f g t) = (term20 _26299 _26310 f g t).
Proof. exact (MK_COMB (@lem1118687) (@lem1118686 _26299 _26310 f g t)). Qed.
Lemma lem1118689 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) (t : list _26299) : (term21 _26299 _26310 f g h t) = (term22 _26299 _26310 f g h t).
Proof. exact (eq_refl (term21 _26299 _26310 f g h t)). Qed.
Lemma lem1118690 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) (t : list _26299) : (term23 _26299 _26310 f g h t) = (term24 _26299 _26310 f g h t).
Proof. exact (MK_COMB (@lem1118688 _26299 _26310 f g t) (@lem1118689 _26299 _26310 f g h t)). Qed.
Lemma lem1118691 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term25 _26299 _26310 f g h) = (term26 _26299 _26310 f g h).
Proof. exact (fun_ext (fun t : list _26299 => @lem1118690 _26299 _26310 f g h t)). Qed.
Lemma lem1118692 {_26299 : Type'} : (@all (list _26299)) = (@all (list _26299)).
Proof. exact (eq_refl (@all (list _26299))). Qed.
Lemma lem1118693 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term27 _26299 _26310 f g h) = (term28 _26299 _26310 f g h).
Proof. exact (MK_COMB (@lem1118692 _26299) (@lem1118691 _26299 _26310 f g h)). Qed.
Lemma lem1118694 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term29 _26299 _26310 f g) = (term30 _26299 _26310 f g).
Proof. exact (fun_ext (fun h : _26299 => @lem1118693 _26299 _26310 f g h)). Qed.
Lemma lem1118695 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1118696 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term31 _26299 _26310 f g) = (term32 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118695 _26299) (@lem1118694 _26299 _26310 f g)). Qed.
Lemma lem1118697 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term33 _26299 _26310 f g) = (term34 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118685 _26299 _26310 f g) (@lem1118696 _26299 _26310 f g)). Qed.
Lemma lem1118698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118699 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term35 _26299 _26310 f g) = (term36 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118698) (@lem1118697 _26299 _26310 f g)). Qed.
Lemma lem1118700 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (l : list _26299) : (term17 _26299 _26310 f g l) = (term18 _26299 _26310 f g l).
Proof. exact (eq_refl (term17 _26299 _26310 f g l)). Qed.
Lemma lem1118701 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term37 _26299 _26310 f g) = (term12 _26299 _26310 f g).
Proof. exact (fun_ext (fun l : list _26299 => @lem1118700 _26299 _26310 f g l)). Qed.
Lemma lem1118702 {_26299 : Type'} : (@all (list _26299)) = (@all (list _26299)).
Proof. exact (eq_refl (@all (list _26299))). Qed.
Lemma lem1118703 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term38 _26299 _26310 f g) = (term39 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118702 _26299) (@lem1118701 _26299 _26310 f g)). Qed.
Lemma lem1118704 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term11 _26299 _26310 f g) = (term40 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118699 _26299 _26310 f g) (@lem1118703 _26299 _26310 f g)). Qed.
Lemma lem1118705 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term40 _26299 _26310 f g.
Proof. exact (EQ_MP (@lem1118704 _26299 _26310 f g) (@lem1118682 _26299 _26310 f g)). Qed.
Lemma lem1118706 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term18 _26299 _26310 f g t) : term18 _26299 _26310 f g t.
Proof. exact (h1). Qed.
Lemma lem1118710 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1118711 {_26299 : Type'} (P : _26299 -> Prop) : (@List.Forall _26299 P (@nil _26299)) = True.
Proof. exact (@lem1118710 _26299 P). Qed.
Lemma lem1118712 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term41 _26299 _26310 f g) = True.
Proof. exact (@lem1118711 _26299 (term42 _26299 _26310 f g)). Qed.
Lemma lem1118713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118714 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term43 _26299 _26310 f g) = (imp True).
Proof. exact (MK_COMB (@lem1118713) (@lem1118712 _26299 _26310 f g)). Qed.
Lemma lem1118718 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1118677 A B f) (@lem1118676 A B f)). Qed.
Lemma lem1118719 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (@List.map _26299 _26310 f (@nil _26299)) = (@nil _26310).
Proof. exact (@lem1118718 _26299 _26310 f). Qed.
Lemma lem1118720 {_26310 : Type'} : (@eq (list _26310)) = (@eq (list _26310)).
Proof. exact (eq_refl (@eq (list _26310))). Qed.
Lemma lem1118721 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term44 _26299 _26310 f) = (@eq (list _26310) (@nil _26310)).
Proof. exact (MK_COMB (@lem1118720 _26310) (@lem1118719 _26299 _26310 f)). Qed.
Lemma lem1118723 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1118677 A B f) (@lem1118676 A B f)). Qed.
Lemma lem1118724 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (@List.map _26299 _26310 f (@nil _26299)) = (@nil _26310).
Proof. exact (@lem1118723 _26299 _26310 f). Qed.
Lemma lem1118725 {_26299 _26310 : Type'} (g : _26299 -> _26310) : (@List.map _26299 _26310 g (@nil _26299)) = (@nil _26310).
Proof. exact (@lem1118724 _26299 _26310 g). Qed.
Lemma lem1118726 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : ((@List.map _26299 _26310 f (@nil _26299)) = (@List.map _26299 _26310 g (@nil _26299))) = ((@nil _26310) = (@nil _26310)).
Proof. exact (MK_COMB (@lem1118721 _26299 _26310 f) (@lem1118725 _26299 _26310 g)). Qed.
Lemma lem1118728 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1118729 {_26310 : Type'} (x : list _26310) : (x = x) = True.
Proof. exact (@lem1118728 (list _26310) x). Qed.
Lemma lem1118730 {_26310 : Type'} : ((@nil _26310) = (@nil _26310)) = True.
Proof. exact (@lem1118729 _26310 (@nil _26310)). Qed.
Lemma lem1118731 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : ((@List.map _26299 _26310 f (@nil _26299)) = (@List.map _26299 _26310 g (@nil _26299))) = True.
Proof. exact (TRANS (@lem1118726 _26299 _26310 f g) (@lem1118730 _26310)). Qed.
Lemma lem1118732 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term14 _26299 _26310 f g) = (True -> True).
Proof. exact (MK_COMB (@lem1118714 _26299 _26310 f g) (@lem1118731 _26299 _26310 f g)). Qed.
Lemma lem1118734 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1118735 : (True -> True) = True.
Proof. exact (@lem1118734 True). Qed.
Lemma lem1118736 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term14 _26299 _26310 f g) = True.
Proof. exact (TRANS (@lem1118732 _26299 _26310 f g) (@lem1118735)). Qed.
Lemma lem1118737 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : True = (term14 _26299 _26310 f g).
Proof. exact (SYM (@lem1118736 _26299 _26310 f g)). Qed.
Lemma lem1118738 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term14 _26299 _26310 f g.
Proof. exact (EQ_MP (@lem1118737 _26299 _26310 f g) (@lem0)). Qed.
Lemma lem1118742 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term45 _25307 P h t) = (term46 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1118743 {_26299 : Type'} (h : _26299) (P : _26299 -> Prop) (t : list _26299) : (term45 _26299 P h t) = (term46 _26299 h P t).
Proof. exact (@lem1118742 _26299 h P t). Qed.
Lemma lem1118744 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term47 _26299 _26310 f g h t) = (term48 _26299 _26310 h f g t).
Proof. exact (@lem1118743 _26299 h (term42 _26299 _26310 f g) t). Qed.
Lemma lem1118748 {A B : Type'} (f : A -> B) (y : A) : (term49 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1118749 {_26299 : Type'} (f : _26299 -> Prop) (y : _26299) : (term50 _26299 f y) = (f y).
Proof. exact (@lem1118748 _26299 Prop f y). Qed.
Lemma lem1118750 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term51 _26299 _26310 f g h) = (term52 _26299 _26310 f g h).
Proof. exact (@lem1118749 _26299 (term42 _26299 _26310 f g) h). Qed.
Lemma lem1118751 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : (term52 _26299 _26310 f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term52 _26299 _26310 f g x)). Qed.
Lemma lem1118752 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term53 _26299 _26310 f g) = (term42 _26299 _26310 f g).
Proof. exact (fun_ext (fun x : _26299 => @lem1118751 _26299 _26310 f g x)). Qed.
Lemma lem1118753 {_26299 : Type'} (h : _26299) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1118754 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term51 _26299 _26310 f g h) = (term52 _26299 _26310 f g h).
Proof. exact (MK_COMB (@lem1118752 _26299 _26310 f g) (@lem1118753 _26299 h)). Qed.
Lemma lem1118755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1118756 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term54 _26299 _26310 f g h) = (term55 _26299 _26310 f g h).
Proof. exact (MK_COMB (@lem1118755) (@lem1118754 _26299 _26310 f g h)). Qed.
Lemma lem1118757 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term52 _26299 _26310 f g h) = ((f h) = (g h)).
Proof. exact (eq_refl (term52 _26299 _26310 f g h)). Qed.
Lemma lem1118758 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : ((term51 _26299 _26310 f g h) = (term52 _26299 _26310 f g h)) = ((term52 _26299 _26310 f g h) = ((f h) = (g h))).
Proof. exact (MK_COMB (@lem1118756 _26299 _26310 f g h) (@lem1118757 _26299 _26310 f g h)). Qed.
Lemma lem1118759 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term52 _26299 _26310 f g h) = ((f h) = (g h)).
Proof. exact (EQ_MP (@lem1118758 _26299 _26310 f g h) (@lem1118750 _26299 _26310 f g h)). Qed.
Lemma lem1118762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1118763 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term56 _26299 _26310 f g h) = (term57 _26299 _26310 f g h).
Proof. exact (MK_COMB (@lem1118762) (@lem1118759 _26299 _26310 f g h)). Qed.
Lemma lem1118766 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term58 _26299 _26310 f g t) = (term58 _26299 _26310 f g t).
Proof. exact (eq_refl (term58 _26299 _26310 f g t)). Qed.
Lemma lem1118767 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term48 _26299 _26310 h f g t) = (term59 _26299 _26310 h f g t).
Proof. exact (MK_COMB (@lem1118763 _26299 _26310 f g h) (@lem1118766 _26299 _26310 f g t)). Qed.
Lemma lem1118770 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term47 _26299 _26310 f g h t) = (term59 _26299 _26310 h f g t).
Proof. exact (TRANS (@lem1118744 _26299 _26310 h f g t) (@lem1118767 _26299 _26310 h f g t)). Qed.
Lemma lem1118771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118772 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term60 _26299 _26310 f g h t) = (term61 _26299 _26310 h f g t).
Proof. exact (MK_COMB (@lem1118771) (@lem1118770 _26299 _26310 h f g t)). Qed.
Lemma lem1118776 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term6 A B f h t) = (term7 A B h f t).
Proof. exact (EQ_MP (@lem1118673 A B h f t) (@lem1118672 A B h f t)). Qed.
Lemma lem1118777 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term6 _26299 _26310 f h t) = (term7 _26299 _26310 h f t).
Proof. exact (@lem1118776 _26299 _26310 h f t). Qed.
Lemma lem1118778 {_26310 : Type'} : (@eq (list _26310)) = (@eq (list _26310)).
Proof. exact (eq_refl (@eq (list _26310))). Qed.
Lemma lem1118779 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term62 _26299 _26310 f h t) = (term63 _26299 _26310 h f t).
Proof. exact (MK_COMB (@lem1118778 _26310) (@lem1118777 _26299 _26310 h f t)). Qed.
Lemma lem1118781 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term6 A B f h t) = (term7 A B h f t).
Proof. exact (EQ_MP (@lem1118673 A B h f t) (@lem1118672 A B h f t)). Qed.
Lemma lem1118782 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term6 _26299 _26310 f h t) = (term7 _26299 _26310 h f t).
Proof. exact (@lem1118781 _26299 _26310 h f t). Qed.
Lemma lem1118783 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term6 _26299 _26310 g h t) = (term7 _26299 _26310 h g t).
Proof. exact (@lem1118782 _26299 _26310 h g t). Qed.
Lemma lem1118784 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : ((term6 _26299 _26310 f h t) = (term6 _26299 _26310 g h t)) = ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)).
Proof. exact (MK_COMB (@lem1118779 _26299 _26310 h f t) (@lem1118783 _26299 _26310 h g t)). Qed.
Lemma lem1118787 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term22 _26299 _26310 f g h t) = (term64 _26299 _26310 f h g t).
Proof. exact (MK_COMB (@lem1118772 _26299 _26310 h f g t) (@lem1118784 _26299 _26310 f h g t)). Qed.
Lemma lem1118790 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) (t : list _26299) : (term64 _26299 _26310 f h g t) = (term22 _26299 _26310 f g h t).
Proof. exact (SYM (@lem1118787 _26299 _26310 f h g t)). Qed.
Lemma lem1118792 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1118793 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term64 _26299 _26310 f h g t) = (term66 _26299 _26310 f h g t).
Proof. exact (@lem1118792 (term64 _26299 _26310 f h g t)). Qed.
Lemma lem1118794 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term66 _26299 _26310 f h g t) = (term64 _26299 _26310 f h g t).
Proof. exact (SYM (@lem1118793 _26299 _26310 f h g t)). Qed.
Lemma lem1118795 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term67 _26299 _26310 f h g t) : term67 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1118798 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term68 _26299 _26310 f h g t) : term68 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1118799 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term69 _26299 _26310 f h g t.
Proof. exact (fun h0 : term68 _26299 _26310 f h g t => @lem1118798 _26299 _26310 f h g t h0). Qed.
Lemma lem1118800 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term69 _26299 _26310 f h g t) : term69 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1118801 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term68 _26299 _26310 f h g t) : term68 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1118802 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term69 _26299 _26310 f h g t) (h2 : term68 _26299 _26310 f h g t) : term68 _26299 _26310 f h g t.
Proof. exact (@lem1118800 _26299 _26310 f h g t h1 (@lem1118801 _26299 _26310 f h g t h2)). Qed.
Lemma lem1118803 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term68 _26299 _26310 f h g t) : term70 _26299 _26310 f h g t.
Proof. exact (fun h0 : term69 _26299 _26310 f h g t => @lem1118802 _26299 _26310 f h g t h0 h1). Qed.
Lemma lem1118804 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term69 _26299 _26310 f h g t) : term69 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1118805 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term69 _26299 _26310 f h g t) (h2 : term68 _26299 _26310 f h g t) : term68 _26299 _26310 f h g t.
Proof. exact (@lem1118803 _26299 _26310 f h g t h2 (@lem1118804 _26299 _26310 f h g t h1)). Qed.
Lemma lem1118806 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term69 _26299 _26310 f h g t) : term69 _26299 _26310 f h g t.
Proof. exact (fun h0 : term68 _26299 _26310 f h g t => @lem1118805 _26299 _26310 f h g t h1 h0). Qed.
Lemma lem1118807 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term71 _26299 _26310 f h g t.
Proof. exact (fun h0 : term69 _26299 _26310 f h g t => @lem1118806 _26299 _26310 f h g t h0). Qed.
Lemma lem1118810 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term69 _26299 _26310 f h g t.
Proof. exact (@lem1118807 _26299 _26310 f h g t (@lem1118799 _26299 _26310 f h g t)). Qed.
Lemma lem1118811 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term69 _26299 _26310 f h g t.
Proof. exact (@lem1118810 _26299 _26310 f h g t). Qed.
Lemma lem1118833 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1118834 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term66 _26299 _26310 f h g t) = (term72 _26299 _26310 f h g t).
Proof. exact (@lem1118833 (term67 _26299 _26310 f h g t)). Qed.
Lemma lem1118836 (t : Prop) : (term73 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1118837 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term72 _26299 _26310 f h g t) = (term64 _26299 _26310 f h g t).
Proof. exact (@lem1118836 (term64 _26299 _26310 f h g t)). Qed.
Lemma lem1118840 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term66 _26299 _26310 f h g t) = (term64 _26299 _26310 f h g t).
Proof. exact (TRANS (@lem1118834 _26299 _26310 f h g t) (@lem1118837 _26299 _26310 f h g t)). Qed.
Lemma lem1118843 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term20 _26299 _26310 f g t) = (term20 _26299 _26310 f g t).
Proof. exact (eq_refl (term20 _26299 _26310 f g t)). Qed.
Lemma lem1118844 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term68 _26299 _26310 f h g t) = (term74 _26299 _26310 f h g t).
Proof. exact (MK_COMB (@lem1118843 _26299 _26310 f g t) (@lem1118840 _26299 _26310 f h g t)). Qed.
Lemma lem1118847 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term75 _26299 _26310 h g t) = (term76 _26299 _26310 h g t).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1118844 _26299 _26310 f h g t)). Qed.
Lemma lem1118848 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1118849 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term77 _26299 _26310 h g t) = (term78 _26299 _26310 h g t).
Proof. exact (MK_COMB (@lem1118848 _26299 _26310) (@lem1118847 _26299 _26310 h g t)). Qed.
Lemma lem1118854 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (term79 _26299 _26310 g t) = (term80 _26299 _26310 g t).
Proof. exact (fun_ext (fun h : _26299 => @lem1118849 _26299 _26310 h g t)). Qed.
Lemma lem1118855 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1118856 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (term81 _26299 _26310 g t) = (term82 _26299 _26310 g t).
Proof. exact (MK_COMB (@lem1118855 _26299) (@lem1118854 _26299 _26310 g t)). Qed.
Lemma lem1118861 {_26299 _26310 : Type'} (t : list _26299) : (term83 _26299 _26310 t) = (term84 _26299 _26310 t).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1118856 _26299 _26310 g t)). Qed.
Lemma lem1118862 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1118863 {_26299 _26310 : Type'} (t : list _26299) : (term85 _26299 _26310 t) = (term86 _26299 _26310 t).
Proof. exact (MK_COMB (@lem1118862 _26299 _26310) (@lem1118861 _26299 _26310 t)). Qed.
Lemma lem1118868 {_26299 _26310 : Type'} : (term87 _26299 _26310) = (term88 _26299 _26310).
Proof. exact (fun_ext (fun t : list _26299 => @lem1118863 _26299 _26310 t)). Qed.
Lemma lem1118869 {_26299 : Type'} : (@all (list _26299)) = (@all (list _26299)).
Proof. exact (eq_refl (@all (list _26299))). Qed.
Lemma lem1118876 {_26299 _26310 : Type'} : (term89 _26299 _26310) = (term90 _26299 _26310).
Proof. exact (MK_COMB (@lem1118869 _26299) (@lem1118868 _26299 _26310)). Qed.
Lemma lem1118877 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : _18171 = (term91 _26299 _26310).
Proof. exact (h1). Qed.
Lemma lem1118878 {_26299 _26310 : Type'} (f : _26299 -> _26310) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1118879 {_26299 _26310 : Type'} (f : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (_18171 f) = (term92 _26299 _26310 f).
Proof. exact (MK_COMB (@lem1118877 _26299 _26310 _18171 h1) (@lem1118878 _26299 _26310 f)). Qed.
Lemma lem1118880 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term92 _26299 _26310 f) = (term93 _26299 _26310 f).
Proof. exact (eq_refl (term92 _26299 _26310 f)). Qed.
Lemma lem1118881 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term94 _26299 _26310 _18171 f) = (term94 _26299 _26310 _18171 f).
Proof. exact (eq_refl (term94 _26299 _26310 _18171 f)). Qed.
Lemma lem1118882 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term92 _26299 _26310 f)) = ((_18171 f) = (term93 _26299 _26310 f)).
Proof. exact (MK_COMB (@lem1118881 _26299 _26310 _18171 f) (@lem1118880 _26299 _26310 f)). Qed.
Lemma lem1118883 {_26299 _26310 : Type'} (f : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (_18171 f) = (term93 _26299 _26310 f).
Proof. exact (EQ_MP (@lem1118882 _26299 _26310 _18171 f) (@lem1118879 _26299 _26310 f _18171 h1)). Qed.
Lemma lem1118884 {_26299 _26310 : Type'} (g : _26299 -> _26310) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem1118885 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (_18171 f g) = (term95 _26299 _26310 f g).
Proof. exact (MK_COMB (@lem1118883 _26299 _26310 f _18171 h1) (@lem1118884 _26299 _26310 g)). Qed.
Lemma lem1118886 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term95 _26299 _26310 f g) = (term42 _26299 _26310 f g).
Proof. exact (eq_refl (term95 _26299 _26310 f g)). Qed.
Lemma lem1118887 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term96 _26299 _26310 _18171 f g) = (term96 _26299 _26310 _18171 f g).
Proof. exact (eq_refl (term96 _26299 _26310 _18171 f g)). Qed.
Lemma lem1118888 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term95 _26299 _26310 f g)) = ((_18171 f g) = (term42 _26299 _26310 f g)).
Proof. exact (MK_COMB (@lem1118887 _26299 _26310 _18171 f g) (@lem1118886 _26299 _26310 f g)). Qed.
Lemma lem1118889 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (_18171 f g) = (term42 _26299 _26310 f g).
Proof. exact (EQ_MP (@lem1118888 _26299 _26310 _18171 f g) (@lem1118885 _26299 _26310 f g _18171 h1)). Qed.
Lemma lem1118915 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)) = ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)).
Proof. exact (eq_refl ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t))). Qed.
Lemma lem1118916 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1118918 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term42 _26299 _26310 f g) = (_18171 f g).
Proof. exact (SYM (@lem1118889 _26299 _26310 f g _18171 h1)). Qed.
Lemma lem1118919 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term42 _26299 _26310 f g) = (_18171 f g).
Proof. exact (@lem1118918 _26299 _26310 f g _18171 h1). Qed.
Lemma lem1118920 {_26299 : Type'} : (@List.Forall _26299) = (@List.Forall _26299).
Proof. exact (eq_refl (@List.Forall _26299)). Qed.
Lemma lem1118921 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term97 _26299 _26310 f g) = (term98 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1118920 _26299) (@lem1118919 _26299 _26310 f g _18171 h1)). Qed.
Lemma lem1118922 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term58 _26299 _26310 f g t) = (term99 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1118921 _26299 _26310 f g _18171 h1) (@lem1118916 _26299 t)). Qed.
Lemma lem1118933 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term57 _26299 _26310 f g h) = (term57 _26299 _26310 f g h).
Proof. exact (eq_refl (term57 _26299 _26310 f g h)). Qed.
Lemma lem1118934 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term59 _26299 _26310 h f g t) = (term100 _26299 _26310 h _18171 f g t).
Proof. exact (MK_COMB (@lem1118933 _26299 _26310 f g h) (@lem1118922 _26299 _26310 f g t _18171 h1)). Qed.
Lemma lem1118935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118936 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term61 _26299 _26310 h f g t) = (term101 _26299 _26310 h _18171 f g t).
Proof. exact (MK_COMB (@lem1118935) (@lem1118934 _26299 _26310 h f g t _18171 h1)). Qed.
Lemma lem1118937 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term64 _26299 _26310 f h g t) = (term102 _26299 _26310 _18171 f h g t).
Proof. exact (MK_COMB (@lem1118936 _26299 _26310 h f g t _18171 h1) (@lem1118915 _26299 _26310 f h g t)). Qed.
Lemma lem1118950 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : ((@List.map _26299 _26310 f t) = (@List.map _26299 _26310 g t)) = ((@List.map _26299 _26310 f t) = (@List.map _26299 _26310 g t)).
Proof. exact (eq_refl ((@List.map _26299 _26310 f t) = (@List.map _26299 _26310 g t))). Qed.
Lemma lem1118951 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1118953 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term42 _26299 _26310 f g) = (_18171 f g).
Proof. exact (SYM (@lem1118889 _26299 _26310 f g _18171 h1)). Qed.
Lemma lem1118954 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term42 _26299 _26310 f g) = (_18171 f g).
Proof. exact (@lem1118953 _26299 _26310 f g _18171 h1). Qed.
Lemma lem1118955 {_26299 : Type'} : (@List.Forall _26299) = (@List.Forall _26299).
Proof. exact (eq_refl (@List.Forall _26299)). Qed.
Lemma lem1118956 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term97 _26299 _26310 f g) = (term98 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1118955 _26299) (@lem1118954 _26299 _26310 f g _18171 h1)). Qed.
Lemma lem1118957 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term58 _26299 _26310 f g t) = (term99 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1118956 _26299 _26310 f g _18171 h1) (@lem1118951 _26299 t)). Qed.
Lemma lem1118958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118959 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term103 _26299 _26310 f g t) = (term104 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1118958) (@lem1118957 _26299 _26310 f g t _18171 h1)). Qed.
Lemma lem1118960 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term18 _26299 _26310 f g t) = (term105 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1118959 _26299 _26310 f g t _18171 h1) (@lem1118950 _26299 _26310 f g t)). Qed.
Lemma lem1118961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118962 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term20 _26299 _26310 f g t) = (term106 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1118961) (@lem1118960 _26299 _26310 f g t _18171 h1)). Qed.
Lemma lem1118963 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term74 _26299 _26310 f h g t) = (term107 _26299 _26310 _18171 f h g t).
Proof. exact (MK_COMB (@lem1118962 _26299 _26310 f g t _18171 h1) (@lem1118937 _26299 _26310 f h g t _18171 h1)). Qed.
Lemma lem1118964 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term76 _26299 _26310 h g t) = (term108 _26299 _26310 _18171 h g t).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1118963 _26299 _26310 f h g t _18171 h1)). Qed.
Lemma lem1118965 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1118966 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term78 _26299 _26310 h g t) = (term109 _26299 _26310 _18171 h g t).
Proof. exact (MK_COMB (@lem1118965 _26299 _26310) (@lem1118964 _26299 _26310 h g t _18171 h1)). Qed.
Lemma lem1118967 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term80 _26299 _26310 g t) = (term110 _26299 _26310 _18171 g t).
Proof. exact (fun_ext (fun h : _26299 => @lem1118966 _26299 _26310 h g t _18171 h1)). Qed.
Lemma lem1118968 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1118969 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term82 _26299 _26310 g t) = (term111 _26299 _26310 _18171 g t).
Proof. exact (MK_COMB (@lem1118968 _26299) (@lem1118967 _26299 _26310 g t _18171 h1)). Qed.
Lemma lem1118970 {_26299 _26310 : Type'} (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term84 _26299 _26310 t) = (term112 _26299 _26310 _18171 t).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1118969 _26299 _26310 g t _18171 h1)). Qed.
Lemma lem1118971 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1118972 {_26299 _26310 : Type'} (t : list _26299) (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term86 _26299 _26310 t) = (term113 _26299 _26310 _18171 t).
Proof. exact (MK_COMB (@lem1118971 _26299 _26310) (@lem1118970 _26299 _26310 t _18171 h1)). Qed.
Lemma lem1118973 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term88 _26299 _26310) = (term114 _26299 _26310 _18171).
Proof. exact (fun_ext (fun t : list _26299 => @lem1118972 _26299 _26310 t _18171 h1)). Qed.
Lemma lem1118974 {_26299 : Type'} : (@all (list _26299)) = (@all (list _26299)).
Proof. exact (eq_refl (@all (list _26299))). Qed.
Lemma lem1118975 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h1 : _18171 = (term91 _26299 _26310)) : (term90 _26299 _26310) = (term115 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1118974 _26299) (@lem1118973 _26299 _26310 _18171 h1)). Qed.
Lemma lem1118976 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : term116 _26299 _26310 _18171.
Proof. exact (fun h0 : _18171 = (term91 _26299 _26310) => @lem1118975 _26299 _26310 _18171 h0). Qed.
Lemma lem1118977 {_26299 _26310 : Type'} : term117 _26299 _26310.
Proof. exact (fun _18171 : type516 _26299 _26310 => @lem1118976 _26299 _26310 _18171). Qed.
Lemma lem1118979 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term118 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1118980 {_26299 _26310 : Type'} (P : Prop) (c : type516 _26299 _26310) (Q : type95 _26299 _26310) : term119 _26299 _26310 P c Q.
Proof. exact (@lem1118979 (type516 _26299 _26310) P c Q). Qed.
Lemma lem1118981 {_26299 _26310 : Type'} : term120 _26299 _26310.
Proof. exact (@lem1118980 _26299 _26310 (term90 _26299 _26310) (term91 _26299 _26310) (term121 _26299 _26310)). Qed.
Lemma lem1118982 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term122 _26299 _26310 _18171) = (term115 _26299 _26310 _18171).
Proof. exact (eq_refl (term122 _26299 _26310 _18171)). Qed.
Lemma lem1118983 {_26299 _26310 : Type'} : (term123 _26299 _26310) = (term123 _26299 _26310).
Proof. exact (eq_refl (term123 _26299 _26310)). Qed.
Lemma lem1118984 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : ((term90 _26299 _26310) = (term122 _26299 _26310 _18171)) = ((term90 _26299 _26310) = (term115 _26299 _26310 _18171)).
Proof. exact (MK_COMB (@lem1118983 _26299 _26310) (@lem1118982 _26299 _26310 _18171)). Qed.
Lemma lem1118985 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term124 _26299 _26310 _18171) = (term124 _26299 _26310 _18171).
Proof. exact (eq_refl (term124 _26299 _26310 _18171)). Qed.
Lemma lem1118986 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term125 _26299 _26310 _18171) = (term116 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1118985 _26299 _26310 _18171) (@lem1118984 _26299 _26310 _18171)). Qed.
Lemma lem1118987 {_26299 _26310 : Type'} : (term126 _26299 _26310) = (term127 _26299 _26310).
Proof. exact (fun_ext (fun _18171 : type516 _26299 _26310 => @lem1118986 _26299 _26310 _18171)). Qed.
Lemma lem1118988 {_26299 _26310 : Type'} : (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)) = (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)).
Proof. exact (eq_refl (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop))). Qed.
Lemma lem1118989 {_26299 _26310 : Type'} : (term128 _26299 _26310) = (term117 _26299 _26310).
Proof. exact (MK_COMB (@lem1118988 _26299 _26310) (@lem1118987 _26299 _26310)). Qed.
Lemma lem1118990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1118991 {_26299 _26310 : Type'} : (term129 _26299 _26310) = (term130 _26299 _26310).
Proof. exact (MK_COMB (@lem1118990) (@lem1118989 _26299 _26310)). Qed.
Lemma lem1118992 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term122 _26299 _26310 _18171) = (term115 _26299 _26310 _18171).
Proof. exact (eq_refl (term122 _26299 _26310 _18171)). Qed.
Lemma lem1118993 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term124 _26299 _26310 _18171) = (term124 _26299 _26310 _18171).
Proof. exact (eq_refl (term124 _26299 _26310 _18171)). Qed.
Lemma lem1118994 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term131 _26299 _26310 _18171) = (term132 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1118993 _26299 _26310 _18171) (@lem1118992 _26299 _26310 _18171)). Qed.
Lemma lem1118995 {_26299 _26310 : Type'} : (term133 _26299 _26310) = (term134 _26299 _26310).
Proof. exact (fun_ext (fun _18171 : type516 _26299 _26310 => @lem1118994 _26299 _26310 _18171)). Qed.
Lemma lem1118996 {_26299 _26310 : Type'} : (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)) = (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)).
Proof. exact (eq_refl (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop))). Qed.
Lemma lem1118997 {_26299 _26310 : Type'} : (term135 _26299 _26310) = (term136 _26299 _26310).
Proof. exact (MK_COMB (@lem1118996 _26299 _26310) (@lem1118995 _26299 _26310)). Qed.
Lemma lem1118998 {_26299 _26310 : Type'} : (term123 _26299 _26310) = (term123 _26299 _26310).
Proof. exact (eq_refl (term123 _26299 _26310)). Qed.
Lemma lem1118999 {_26299 _26310 : Type'} : ((term90 _26299 _26310) = (term135 _26299 _26310)) = ((term90 _26299 _26310) = (term136 _26299 _26310)).
Proof. exact (MK_COMB (@lem1118998 _26299 _26310) (@lem1118997 _26299 _26310)). Qed.
Lemma lem1119000 {_26299 _26310 : Type'} : (term120 _26299 _26310) = (term137 _26299 _26310).
Proof. exact (MK_COMB (@lem1118991 _26299 _26310) (@lem1118999 _26299 _26310)). Qed.
Lemma lem1119001 {_26299 _26310 : Type'} : term137 _26299 _26310.
Proof. exact (EQ_MP (@lem1119000 _26299 _26310) (@lem1118981 _26299 _26310)). Qed.
Lemma lem1119002 {_26299 _26310 : Type'} : (term90 _26299 _26310) = (term136 _26299 _26310).
Proof. exact (@lem1119001 _26299 _26310 (@lem1118977 _26299 _26310)). Qed.
Lemma lem1119004 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1119005 {_26299 _26310 : Type'} (s : type516 _26299 _26310) (t : type516 _26299 _26310) : (s = (term140 _26299 _26310 t)) = (term141 _26299 _26310 s t).
Proof. exact (@lem1119004 (type551 _26299 _26310) (_26299 -> _26310) s t). Qed.
Lemma lem1119006 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (_18171 = (term142 _26299 _26310)) = (term143 _26299 _26310 _18171).
Proof. exact (@lem1119005 _26299 _26310 _18171 (term91 _26299 _26310)). Qed.
Lemma lem1119007 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term92 _26299 _26310 f) = (term93 _26299 _26310 f).
Proof. exact (eq_refl (term92 _26299 _26310 f)). Qed.
Lemma lem1119008 {_26299 _26310 : Type'} : (term142 _26299 _26310) = (term91 _26299 _26310).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1119007 _26299 _26310 f)). Qed.
Lemma lem1119009 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (@eq ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171) = (@eq ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171).
Proof. exact (eq_refl (@eq ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171)). Qed.
Lemma lem1119010 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (_18171 = (term142 _26299 _26310)) = (_18171 = (term91 _26299 _26310)).
Proof. exact (MK_COMB (@lem1119009 _26299 _26310 _18171) (@lem1119008 _26299 _26310)). Qed.
Lemma lem1119011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1119012 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term144 _26299 _26310 _18171) = (term145 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119011) (@lem1119010 _26299 _26310 _18171)). Qed.
Lemma lem1119013 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term92 _26299 _26310 f) = (term93 _26299 _26310 f).
Proof. exact (eq_refl (term92 _26299 _26310 f)). Qed.
Lemma lem1119014 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term94 _26299 _26310 _18171 f) = (term94 _26299 _26310 _18171 f).
Proof. exact (eq_refl (term94 _26299 _26310 _18171 f)). Qed.
Lemma lem1119015 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term92 _26299 _26310 f)) = ((_18171 f) = (term93 _26299 _26310 f)).
Proof. exact (MK_COMB (@lem1119014 _26299 _26310 _18171 f) (@lem1119013 _26299 _26310 f)). Qed.
Lemma lem1119016 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term146 _26299 _26310 _18171) = (term147 _26299 _26310 _18171).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1119015 _26299 _26310 _18171 f)). Qed.
Lemma lem1119017 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119018 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term143 _26299 _26310 _18171) = (term148 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119017 _26299 _26310) (@lem1119016 _26299 _26310 _18171)). Qed.
Lemma lem1119019 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : ((_18171 = (term142 _26299 _26310)) = (term143 _26299 _26310 _18171)) = ((_18171 = (term91 _26299 _26310)) = (term148 _26299 _26310 _18171)).
Proof. exact (MK_COMB (@lem1119012 _26299 _26310 _18171) (@lem1119018 _26299 _26310 _18171)). Qed.
Lemma lem1119020 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (_18171 = (term91 _26299 _26310)) = (term148 _26299 _26310 _18171).
Proof. exact (EQ_MP (@lem1119019 _26299 _26310 _18171) (@lem1119006 _26299 _26310 _18171)). Qed.
Lemma lem1119022 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1119023 {_26299 _26310 : Type'} (s : type551 _26299 _26310) (t : type551 _26299 _26310) : (s = (term149 _26299 _26310 t)) = (term150 _26299 _26310 s t).
Proof. exact (@lem1119022 (_26299 -> Prop) (_26299 -> _26310) s t). Qed.
Lemma lem1119024 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term151 _26299 _26310 f)) = (term152 _26299 _26310 _18171 f).
Proof. exact (@lem1119023 _26299 _26310 (_18171 f) (term93 _26299 _26310 f)). Qed.
Lemma lem1119025 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term95 _26299 _26310 f g) = (term42 _26299 _26310 f g).
Proof. exact (eq_refl (term95 _26299 _26310 f g)). Qed.
Lemma lem1119026 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (term151 _26299 _26310 f) = (term93 _26299 _26310 f).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1119025 _26299 _26310 f g)). Qed.
Lemma lem1119027 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term94 _26299 _26310 _18171 f) = (term94 _26299 _26310 _18171 f).
Proof. exact (eq_refl (term94 _26299 _26310 _18171 f)). Qed.
Lemma lem1119028 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term151 _26299 _26310 f)) = ((_18171 f) = (term93 _26299 _26310 f)).
Proof. exact (MK_COMB (@lem1119027 _26299 _26310 _18171 f) (@lem1119026 _26299 _26310 f)). Qed.
Lemma lem1119029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1119030 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term153 _26299 _26310 _18171 f) = (term154 _26299 _26310 _18171 f).
Proof. exact (MK_COMB (@lem1119029) (@lem1119028 _26299 _26310 _18171 f)). Qed.
Lemma lem1119031 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term95 _26299 _26310 f g) = (term42 _26299 _26310 f g).
Proof. exact (eq_refl (term95 _26299 _26310 f g)). Qed.
Lemma lem1119032 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term96 _26299 _26310 _18171 f g) = (term96 _26299 _26310 _18171 f g).
Proof. exact (eq_refl (term96 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119033 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term95 _26299 _26310 f g)) = ((_18171 f g) = (term42 _26299 _26310 f g)).
Proof. exact (MK_COMB (@lem1119032 _26299 _26310 _18171 f g) (@lem1119031 _26299 _26310 f g)). Qed.
Lemma lem1119034 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term155 _26299 _26310 _18171 f) = (term156 _26299 _26310 _18171 f).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1119033 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119035 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119036 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term152 _26299 _26310 _18171 f) = (term157 _26299 _26310 _18171 f).
Proof. exact (MK_COMB (@lem1119035 _26299 _26310) (@lem1119034 _26299 _26310 _18171 f)). Qed.
Lemma lem1119037 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (((_18171 f) = (term151 _26299 _26310 f)) = (term152 _26299 _26310 _18171 f)) = (((_18171 f) = (term93 _26299 _26310 f)) = (term157 _26299 _26310 _18171 f)).
Proof. exact (MK_COMB (@lem1119030 _26299 _26310 _18171 f) (@lem1119036 _26299 _26310 _18171 f)). Qed.
Lemma lem1119038 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term93 _26299 _26310 f)) = (term157 _26299 _26310 _18171 f).
Proof. exact (EQ_MP (@lem1119037 _26299 _26310 _18171 f) (@lem1119024 _26299 _26310 _18171 f)). Qed.
Lemma lem1119040 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term138 _3571 _3575 t)) = (term139 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1119041 {_26299 : Type'} (s : _26299 -> Prop) (t : _26299 -> Prop) : (s = (term158 _26299 t)) = (term159 _26299 s t).
Proof. exact (@lem1119040 Prop _26299 s t). Qed.
Lemma lem1119042 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term53 _26299 _26310 f g)) = (term160 _26299 _26310 _18171 f g).
Proof. exact (@lem1119041 _26299 (_18171 f g) (term42 _26299 _26310 f g)). Qed.
Lemma lem1119043 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : (term52 _26299 _26310 f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term52 _26299 _26310 f g x)). Qed.
Lemma lem1119044 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : (term53 _26299 _26310 f g) = (term42 _26299 _26310 f g).
Proof. exact (fun_ext (fun x : _26299 => @lem1119043 _26299 _26310 f g x)). Qed.
Lemma lem1119045 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term96 _26299 _26310 _18171 f g) = (term96 _26299 _26310 _18171 f g).
Proof. exact (eq_refl (term96 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119046 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term53 _26299 _26310 f g)) = ((_18171 f g) = (term42 _26299 _26310 f g)).
Proof. exact (MK_COMB (@lem1119045 _26299 _26310 _18171 f g) (@lem1119044 _26299 _26310 f g)). Qed.
Lemma lem1119047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1119048 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term161 _26299 _26310 _18171 f g) = (term162 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119047) (@lem1119046 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119049 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : (term52 _26299 _26310 f g x) = ((f x) = (g x)).
Proof. exact (eq_refl (term52 _26299 _26310 f g x)). Qed.
Lemma lem1119050 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : (term163 _26299 _26310 _18171 f g x) = (term163 _26299 _26310 _18171 f g x).
Proof. exact (eq_refl (term163 _26299 _26310 _18171 f g x)). Qed.
Lemma lem1119051 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : ((_18171 f g x) = (term52 _26299 _26310 f g x)) = ((_18171 f g x) = ((f x) = (g x))).
Proof. exact (MK_COMB (@lem1119050 _26299 _26310 _18171 f g x) (@lem1119049 _26299 _26310 f g x)). Qed.
Lemma lem1119052 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term164 _26299 _26310 _18171 f g) = (term165 _26299 _26310 _18171 f g).
Proof. exact (fun_ext (fun x : _26299 => @lem1119051 _26299 _26310 _18171 f g x)). Qed.
Lemma lem1119053 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1119054 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term160 _26299 _26310 _18171 f g) = (term166 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119053 _26299) (@lem1119052 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119055 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (((_18171 f g) = (term53 _26299 _26310 f g)) = (term160 _26299 _26310 _18171 f g)) = (((_18171 f g) = (term42 _26299 _26310 f g)) = (term166 _26299 _26310 _18171 f g)).
Proof. exact (MK_COMB (@lem1119048 _26299 _26310 _18171 f g) (@lem1119054 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119056 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term42 _26299 _26310 f g)) = (term166 _26299 _26310 _18171 f g).
Proof. exact (EQ_MP (@lem1119055 _26299 _26310 _18171 f g) (@lem1119042 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119057 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : ((_18171 f g x) = ((f x) = (g x))) = ((_18171 f g x) = ((f x) = (g x))).
Proof. exact (eq_refl ((_18171 f g x) = ((f x) = (g x)))). Qed.
Lemma lem1119058 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term165 _26299 _26310 _18171 f g) = (term165 _26299 _26310 _18171 f g).
Proof. exact (fun_ext (fun x : _26299 => @lem1119057 _26299 _26310 _18171 f g x)). Qed.
Lemma lem1119059 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1119060 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term166 _26299 _26310 _18171 f g) = (term166 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119059 _26299) (@lem1119058 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119061 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : ((_18171 f g) = (term42 _26299 _26310 f g)) = (term166 _26299 _26310 _18171 f g).
Proof. exact (TRANS (@lem1119056 _26299 _26310 _18171 f g) (@lem1119060 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119062 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term156 _26299 _26310 _18171 f) = (term167 _26299 _26310 _18171 f).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1119061 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119063 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119064 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term157 _26299 _26310 _18171 f) = (term168 _26299 _26310 _18171 f).
Proof. exact (MK_COMB (@lem1119063 _26299 _26310) (@lem1119062 _26299 _26310 _18171 f)). Qed.
Lemma lem1119065 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : ((_18171 f) = (term93 _26299 _26310 f)) = (term168 _26299 _26310 _18171 f).
Proof. exact (TRANS (@lem1119038 _26299 _26310 _18171 f) (@lem1119064 _26299 _26310 _18171 f)). Qed.
Lemma lem1119066 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term147 _26299 _26310 _18171) = (term169 _26299 _26310 _18171).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1119065 _26299 _26310 _18171 f)). Qed.
Lemma lem1119067 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119068 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term148 _26299 _26310 _18171) = (term170 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119067 _26299 _26310) (@lem1119066 _26299 _26310 _18171)). Qed.
Lemma lem1119069 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (_18171 = (term91 _26299 _26310)) = (term170 _26299 _26310 _18171).
Proof. exact (TRANS (@lem1119020 _26299 _26310 _18171) (@lem1119068 _26299 _26310 _18171)). Qed.
Lemma lem1119070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1119071 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term124 _26299 _26310 _18171) = (term171 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119070) (@lem1119069 _26299 _26310 _18171)). Qed.
Lemma lem1119072 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term115 _26299 _26310 _18171) = (term115 _26299 _26310 _18171).
Proof. exact (eq_refl (term115 _26299 _26310 _18171)). Qed.
Lemma lem1119073 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term132 _26299 _26310 _18171) = (term172 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119071 _26299 _26310 _18171) (@lem1119072 _26299 _26310 _18171)). Qed.
Lemma lem1119074 {_26299 _26310 : Type'} : (term134 _26299 _26310) = (term173 _26299 _26310).
Proof. exact (fun_ext (fun _18171 : type516 _26299 _26310 => @lem1119073 _26299 _26310 _18171)). Qed.
Lemma lem1119075 {_26299 _26310 : Type'} : (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)) = (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)).
Proof. exact (eq_refl (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop))). Qed.
Lemma lem1119076 {_26299 _26310 : Type'} : (term136 _26299 _26310) = (term174 _26299 _26310).
Proof. exact (MK_COMB (@lem1119075 _26299 _26310) (@lem1119074 _26299 _26310)). Qed.
Lemma lem1119077 {_26299 _26310 : Type'} : (term123 _26299 _26310) = (term123 _26299 _26310).
Proof. exact (eq_refl (term123 _26299 _26310)). Qed.
Lemma lem1119078 {_26299 _26310 : Type'} : ((term90 _26299 _26310) = (term136 _26299 _26310)) = ((term90 _26299 _26310) = (term174 _26299 _26310)).
Proof. exact (MK_COMB (@lem1119077 _26299 _26310) (@lem1119076 _26299 _26310)). Qed.
Lemma lem1119081 {_26299 _26310 : Type'} : (term90 _26299 _26310) = (term174 _26299 _26310).
Proof. exact (EQ_MP (@lem1119078 _26299 _26310) (@lem1119002 _26299 _26310)). Qed.
Lemma lem1119082 {_26299 _26310 : Type'} : (term89 _26299 _26310) = (term174 _26299 _26310).
Proof. exact (TRANS (@lem1118876 _26299 _26310) (@lem1119081 _26299 _26310)). Qed.
Lemma lem1119099 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term107 _26299 _26310 _18171 f h g t) = (term107 _26299 _26310 _18171 f h g t).
Proof. exact (eq_refl (term107 _26299 _26310 _18171 f h g t)). Qed.
Lemma lem1119100 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term108 _26299 _26310 _18171 h g t) = (term108 _26299 _26310 _18171 h g t).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1119099 _26299 _26310 _18171 f h g t)). Qed.
Lemma lem1119101 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119102 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term109 _26299 _26310 _18171 h g t) = (term109 _26299 _26310 _18171 h g t).
Proof. exact (MK_COMB (@lem1119101 _26299 _26310) (@lem1119100 _26299 _26310 _18171 h g t)). Qed.
Lemma lem1119103 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (g : _26299 -> _26310) (t : list _26299) : (term110 _26299 _26310 _18171 g t) = (term110 _26299 _26310 _18171 g t).
Proof. exact (fun_ext (fun h : _26299 => @lem1119102 _26299 _26310 _18171 h g t)). Qed.
Lemma lem1119104 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1119105 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (g : _26299 -> _26310) (t : list _26299) : (term111 _26299 _26310 _18171 g t) = (term111 _26299 _26310 _18171 g t).
Proof. exact (MK_COMB (@lem1119104 _26299) (@lem1119103 _26299 _26310 _18171 g t)). Qed.
Lemma lem1119106 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (t : list _26299) : (term112 _26299 _26310 _18171 t) = (term112 _26299 _26310 _18171 t).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1119105 _26299 _26310 _18171 g t)). Qed.
Lemma lem1119107 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119108 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (t : list _26299) : (term113 _26299 _26310 _18171 t) = (term113 _26299 _26310 _18171 t).
Proof. exact (MK_COMB (@lem1119107 _26299 _26310) (@lem1119106 _26299 _26310 _18171 t)). Qed.
Lemma lem1119109 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term114 _26299 _26310 _18171) = (term114 _26299 _26310 _18171).
Proof. exact (fun_ext (fun t : list _26299 => @lem1119108 _26299 _26310 _18171 t)). Qed.
Lemma lem1119110 {_26299 : Type'} : (@all (list _26299)) = (@all (list _26299)).
Proof. exact (eq_refl (@all (list _26299))). Qed.
Lemma lem1119111 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term115 _26299 _26310 _18171) = (term115 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119110 _26299) (@lem1119109 _26299 _26310 _18171)). Qed.
Lemma lem1119116 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (x : _26299) : ((_18171 f g x) = ((f x) = (g x))) = ((_18171 f g x) = ((f x) = (g x))).
Proof. exact (eq_refl ((_18171 f g x) = ((f x) = (g x)))). Qed.
Lemma lem1119117 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term165 _26299 _26310 _18171 f g) = (term165 _26299 _26310 _18171 f g).
Proof. exact (fun_ext (fun x : _26299 => @lem1119116 _26299 _26310 _18171 f g x)). Qed.
Lemma lem1119118 {_26299 : Type'} : (@all _26299) = (@all _26299).
Proof. exact (eq_refl (@all _26299)). Qed.
Lemma lem1119119 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term166 _26299 _26310 _18171 f g) = (term166 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119118 _26299) (@lem1119117 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119120 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term167 _26299 _26310 _18171 f) = (term167 _26299 _26310 _18171 f).
Proof. exact (fun_ext (fun g : _26299 -> _26310 => @lem1119119 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119121 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119122 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (term168 _26299 _26310 _18171 f) = (term168 _26299 _26310 _18171 f).
Proof. exact (MK_COMB (@lem1119121 _26299 _26310) (@lem1119120 _26299 _26310 _18171 f)). Qed.
Lemma lem1119123 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term169 _26299 _26310 _18171) = (term169 _26299 _26310 _18171).
Proof. exact (fun_ext (fun f : _26299 -> _26310 => @lem1119122 _26299 _26310 _18171 f)). Qed.
Lemma lem1119124 {_26299 _26310 : Type'} : (@all (_26299 -> _26310)) = (@all (_26299 -> _26310)).
Proof. exact (eq_refl (@all (_26299 -> _26310))). Qed.
Lemma lem1119125 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term170 _26299 _26310 _18171) = (term170 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119124 _26299 _26310) (@lem1119123 _26299 _26310 _18171)). Qed.
Lemma lem1119126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1119127 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term171 _26299 _26310 _18171) = (term171 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119126) (@lem1119125 _26299 _26310 _18171)). Qed.
Lemma lem1119128 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : (term172 _26299 _26310 _18171) = (term172 _26299 _26310 _18171).
Proof. exact (MK_COMB (@lem1119127 _26299 _26310 _18171) (@lem1119111 _26299 _26310 _18171)). Qed.
Lemma lem1119129 {_26299 _26310 : Type'} : (term173 _26299 _26310) = (term173 _26299 _26310).
Proof. exact (fun_ext (fun _18171 : type516 _26299 _26310 => @lem1119128 _26299 _26310 _18171)). Qed.
Lemma lem1119130 {_26299 _26310 : Type'} : (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)) = (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop)).
Proof. exact (eq_refl (@all ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop))). Qed.
Lemma lem1119131 {_26299 _26310 : Type'} : (term174 _26299 _26310) = (term174 _26299 _26310).
Proof. exact (MK_COMB (@lem1119130 _26299 _26310) (@lem1119129 _26299 _26310)). Qed.
Lemma lem1119192 {_26299 _26310 : Type'} : (term89 _26299 _26310) = (term174 _26299 _26310).
Proof. exact (TRANS (@lem1119082 _26299 _26310) (@lem1119131 _26299 _26310)). Qed.
Lemma lem1119193 {_26299 _26310 : Type'} : (term174 _26299 _26310) = (term89 _26299 _26310).
Proof. exact (SYM (@lem1119192 _26299 _26310)). Qed.
Lemma lem1119195 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term105 _26299 _26310 _18171 f g t) : term105 _26299 _26310 _18171 f g t.
Proof. exact (h1). Qed.
Lemma lem1119198 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1119199 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)) = (term175 _26299 _26310 f h g t).
Proof. exact (@lem1119198 ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t))). Qed.
Lemma lem1119200 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term175 _26299 _26310 f h g t) = ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)).
Proof. exact (SYM (@lem1119199 _26299 _26310 f h g t)). Qed.
Lemma lem1119201 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) : term176 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1119649 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term105 _26299 _26310 _18171 f g t) = (term177 _26299 _26310 _18171 f g t).
Proof. exact (@lem17265 (term99 _26299 _26310 _18171 f g t) ((@List.map _26299 _26310 f t) = (@List.map _26299 _26310 g t))). Qed.
Lemma lem1119650 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term105 _26299 _26310 _18171 f g t) : term177 _26299 _26310 _18171 f g t.
Proof. exact (EQ_MP (@lem1119649 _26299 _26310 _18171 f g t) (@lem1119195 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1119660 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term100 _26299 _26310 h _18171 f g t.
Proof. exact (h1). Qed.
Lemma lem1119666 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) : term176 _26299 _26310 f h g t.
Proof. exact (h1). Qed.
Lemma lem1119787 {_26310 : Type'} : (@eq (list _26310)) = (@eq (list _26310)).
Proof. exact (eq_refl (@eq (list _26310))). Qed.
Lemma lem1119794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119795 {_26299 _26310 : Type'} (f : type540 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) f x).
Proof. exact (@lem1119794 (_26299 -> _26310) (type1139 _26299 _26310) f x). Qed.
Lemma lem1119796 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (@List.map _26299 _26310 f) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f).
Proof. exact (@lem1119795 _26299 _26310 (@List.map _26299 _26310) f). Qed.
Lemma lem1119797 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119798 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 f t) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f t).
Proof. exact (MK_COMB (@lem1119796 _26299 _26310 f) (@lem1119797 _26299 t)). Qed.
Lemma lem1119800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119801 {_26299 _26310 : Type'} (f : type1139 _26299 _26310) (x : list _26299) : (f x) = (@I ((list _26299) -> list _26310) f x).
Proof. exact (@lem1119800 (list _26299) (list _26310) f x). Qed.
Lemma lem1119802 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f t) = (term178 _26299 _26310 f t).
Proof. exact (@lem1119801 _26299 _26310 (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f) t). Qed.
Lemma lem1119804 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 f t) = (term178 _26299 _26310 f t).
Proof. exact (TRANS (@lem1119798 _26299 _26310 f t) (@lem1119802 _26299 _26310 f t)). Qed.
Lemma lem1119811 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119812 {_26299 _26310 : Type'} (f : type540 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) f x).
Proof. exact (@lem1119811 (_26299 -> _26310) (type1139 _26299 _26310) f x). Qed.
Lemma lem1119813 {_26299 _26310 : Type'} (g : _26299 -> _26310) : (@List.map _26299 _26310 g) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g).
Proof. exact (@lem1119812 _26299 _26310 (@List.map _26299 _26310) g). Qed.
Lemma lem1119814 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119815 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 g t) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g t).
Proof. exact (MK_COMB (@lem1119813 _26299 _26310 g) (@lem1119814 _26299 t)). Qed.
Lemma lem1119817 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119818 {_26299 _26310 : Type'} (f : type1139 _26299 _26310) (x : list _26299) : (f x) = (@I ((list _26299) -> list _26310) f x).
Proof. exact (@lem1119817 (list _26299) (list _26310) f x). Qed.
Lemma lem1119819 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g t) = (term178 _26299 _26310 g t).
Proof. exact (@lem1119818 _26299 _26310 (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g) t). Qed.
Lemma lem1119821 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 g t) = (term178 _26299 _26310 g t).
Proof. exact (TRANS (@lem1119815 _26299 _26310 g t) (@lem1119819 _26299 _26310 g t)). Qed.
Lemma lem1119822 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (term179 _26299 _26310 f t) = (term180 _26299 _26310 f t).
Proof. exact (MK_COMB (@lem1119787 _26310) (@lem1119804 _26299 _26310 f t)). Qed.
Lemma lem1119823 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : ((@List.map _26299 _26310 f t) = (@List.map _26299 _26310 g t)) = ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)).
Proof. exact (MK_COMB (@lem1119822 _26299 _26310 f t) (@lem1119821 _26299 _26310 g t)). Qed.
Lemma lem1119824 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1119825 {_26299 : Type'} : (@List.Forall _26299) = (@List.Forall _26299).
Proof. exact (eq_refl (@List.Forall _26299)). Qed.
Lemma lem1119832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119833 {_26299 _26310 : Type'} (f : type516 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) f x).
Proof. exact (@lem1119832 (_26299 -> _26310) (type551 _26299 _26310) f x). Qed.
Lemma lem1119834 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (_18171 f) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f).
Proof. exact (@lem1119833 _26299 _26310 _18171 f). Qed.
Lemma lem1119835 {_26299 _26310 : Type'} (g : _26299 -> _26310) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem1119836 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (_18171 f g) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f g).
Proof. exact (MK_COMB (@lem1119834 _26299 _26310 _18171 f) (@lem1119835 _26299 _26310 g)). Qed.
Lemma lem1119838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119839 {_26299 _26310 : Type'} (f : type551 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> _26299 -> Prop) f x).
Proof. exact (@lem1119838 (_26299 -> _26310) (_26299 -> Prop) f x). Qed.
Lemma lem1119840 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f g) = (term181 _26299 _26310 _18171 f g).
Proof. exact (@lem1119839 _26299 _26310 (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f) g). Qed.
Lemma lem1119842 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (_18171 f g) = (term181 _26299 _26310 _18171 f g).
Proof. exact (TRANS (@lem1119836 _26299 _26310 _18171 f g) (@lem1119840 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119843 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119844 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term98 _26299 _26310 _18171 f g) = (term182 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119825 _26299) (@lem1119842 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119845 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term99 _26299 _26310 _18171 f g t) = (term183 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119844 _26299 _26310 _18171 f g) (@lem1119843 _26299 t)). Qed.
Lemma lem1119847 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119848 {_26299 : Type'} (f : type663 _26299) (x : _26299 -> Prop) : (f x) = (@I ((_26299 -> Prop) -> (list _26299) -> Prop) f x).
Proof. exact (@lem1119847 (_26299 -> Prop) (type1143 _26299) f x). Qed.
Lemma lem1119849 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term182 _26299 _26310 _18171 f g) = (term184 _26299 _26310 _18171 f g).
Proof. exact (@lem1119848 _26299 (@List.Forall _26299) (term181 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119850 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119851 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term183 _26299 _26310 _18171 f g t) = (term185 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119849 _26299 _26310 _18171 f g) (@lem1119850 _26299 t)). Qed.
Lemma lem1119853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119854 {_26299 : Type'} (f : type1143 _26299) (x : list _26299) : (f x) = (@I ((list _26299) -> Prop) f x).
Proof. exact (@lem1119853 (list _26299) Prop f x). Qed.
Lemma lem1119855 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term185 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (@lem1119854 _26299 (term184 _26299 _26310 _18171 f g) t). Qed.
Lemma lem1119856 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term183 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (TRANS (@lem1119851 _26299 _26310 _18171 f g t) (@lem1119855 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119857 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term99 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (TRANS (@lem1119845 _26299 _26310 _18171 f g t) (@lem1119856 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119858 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term187 _26299 _26310 _18171 f g t) = (term188 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119824) (@lem1119857 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1119860 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term189 _26299 _26310 _18171 f g t) = (term190 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119859) (@lem1119858 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119861 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term177 _26299 _26310 _18171 f g t) = (term191 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119860 _26299 _26310 _18171 f g t) (@lem1119823 _26299 _26310 f g t)). Qed.
Lemma lem1119862 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term105 _26299 _26310 _18171 f g t) : term191 _26299 _26310 _18171 f g t.
Proof. exact (EQ_MP (@lem1119861 _26299 _26310 _18171 f g t) (@lem1119650 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1119863 {_26299 : Type'} : (@List.Forall _26299) = (@List.Forall _26299).
Proof. exact (eq_refl (@List.Forall _26299)). Qed.
Lemma lem1119870 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119871 {_26299 _26310 : Type'} (f : type516 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) f x).
Proof. exact (@lem1119870 (_26299 -> _26310) (type551 _26299 _26310) f x). Qed.
Lemma lem1119872 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) : (_18171 f) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f).
Proof. exact (@lem1119871 _26299 _26310 _18171 f). Qed.
Lemma lem1119873 {_26299 _26310 : Type'} (g : _26299 -> _26310) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem1119874 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (_18171 f g) = (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f g).
Proof. exact (MK_COMB (@lem1119872 _26299 _26310 _18171 f) (@lem1119873 _26299 _26310 g)). Qed.
Lemma lem1119876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119877 {_26299 _26310 : Type'} (f : type551 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> _26299 -> Prop) f x).
Proof. exact (@lem1119876 (_26299 -> _26310) (_26299 -> Prop) f x). Qed.
Lemma lem1119878 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f g) = (term181 _26299 _26310 _18171 f g).
Proof. exact (@lem1119877 _26299 _26310 (@I ((_26299 -> _26310) -> (_26299 -> _26310) -> _26299 -> Prop) _18171 f) g). Qed.
Lemma lem1119880 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (_18171 f g) = (term181 _26299 _26310 _18171 f g).
Proof. exact (TRANS (@lem1119874 _26299 _26310 _18171 f g) (@lem1119878 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119881 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119882 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term98 _26299 _26310 _18171 f g) = (term182 _26299 _26310 _18171 f g).
Proof. exact (MK_COMB (@lem1119863 _26299) (@lem1119880 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119883 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term99 _26299 _26310 _18171 f g t) = (term183 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119882 _26299 _26310 _18171 f g) (@lem1119881 _26299 t)). Qed.
Lemma lem1119885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119886 {_26299 : Type'} (f : type663 _26299) (x : _26299 -> Prop) : (f x) = (@I ((_26299 -> Prop) -> (list _26299) -> Prop) f x).
Proof. exact (@lem1119885 (_26299 -> Prop) (type1143 _26299) f x). Qed.
Lemma lem1119887 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) : (term182 _26299 _26310 _18171 f g) = (term184 _26299 _26310 _18171 f g).
Proof. exact (@lem1119886 _26299 (@List.Forall _26299) (term181 _26299 _26310 _18171 f g)). Qed.
Lemma lem1119888 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119889 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term183 _26299 _26310 _18171 f g t) = (term185 _26299 _26310 _18171 f g t).
Proof. exact (MK_COMB (@lem1119887 _26299 _26310 _18171 f g) (@lem1119888 _26299 t)). Qed.
Lemma lem1119891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119892 {_26299 : Type'} (f : type1143 _26299) (x : list _26299) : (f x) = (@I ((list _26299) -> Prop) f x).
Proof. exact (@lem1119891 (list _26299) Prop f x). Qed.
Lemma lem1119893 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term185 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (@lem1119892 _26299 (term184 _26299 _26310 _18171 f g) t). Qed.
Lemma lem1119894 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term183 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (TRANS (@lem1119889 _26299 _26310 _18171 f g t) (@lem1119893 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119895 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term99 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (TRANS (@lem1119883 _26299 _26310 _18171 f g t) (@lem1119894 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119896 {_26310 : Type'} : (@eq _26310) = (@eq _26310).
Proof. exact (eq_refl (@eq _26310)). Qed.
Lemma lem1119901 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119902 {_26299 _26310 : Type'} (f : _26299 -> _26310) (x : _26299) : (f x) = (@I (_26299 -> _26310) f x).
Proof. exact (@lem1119901 _26299 _26310 f x). Qed.
Lemma lem1119904 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) : (f h) = (@I (_26299 -> _26310) f h).
Proof. exact (@lem1119902 _26299 _26310 f h). Qed.
Lemma lem1119909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119910 {_26299 _26310 : Type'} (f : _26299 -> _26310) (x : _26299) : (f x) = (@I (_26299 -> _26310) f x).
Proof. exact (@lem1119909 _26299 _26310 f x). Qed.
Lemma lem1119912 {_26299 _26310 : Type'} (g : _26299 -> _26310) (h : _26299) : (g h) = (@I (_26299 -> _26310) g h).
Proof. exact (@lem1119910 _26299 _26310 g h). Qed.
Lemma lem1119913 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) : (term192 _26299 _26310 f h) = (term193 _26299 _26310 f h).
Proof. exact (MK_COMB (@lem1119896 _26310) (@lem1119904 _26299 _26310 f h)). Qed.
Lemma lem1119914 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : ((f h) = (g h)) = ((@I (_26299 -> _26310) f h) = (@I (_26299 -> _26310) g h)).
Proof. exact (MK_COMB (@lem1119913 _26299 _26310 f h) (@lem1119912 _26299 _26310 g h)). Qed.
Lemma lem1119915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1119916 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term57 _26299 _26310 f g h) = (term194 _26299 _26310 f g h).
Proof. exact (MK_COMB (@lem1119915) (@lem1119914 _26299 _26310 f g h)). Qed.
Lemma lem1119917 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term100 _26299 _26310 h _18171 f g t) = (term195 _26299 _26310 h _18171 f g t).
Proof. exact (MK_COMB (@lem1119916 _26299 _26310 f g h) (@lem1119895 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1119918 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term195 _26299 _26310 h _18171 f g t.
Proof. exact (EQ_MP (@lem1119917 _26299 _26310 h _18171 f g t) (@lem1119660 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1119919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1119920 {_26310 : Type'} : (@eq (list _26310)) = (@eq (list _26310)).
Proof. exact (eq_refl (@eq (list _26310))). Qed.
Lemma lem1119921 {_26310 : Type'} : (@cons _26310) = (@cons _26310).
Proof. exact (eq_refl (@cons _26310)). Qed.
Lemma lem1119926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119927 {_26299 _26310 : Type'} (f : _26299 -> _26310) (x : _26299) : (f x) = (@I (_26299 -> _26310) f x).
Proof. exact (@lem1119926 _26299 _26310 f x). Qed.
Lemma lem1119929 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) : (f h) = (@I (_26299 -> _26310) f h).
Proof. exact (@lem1119927 _26299 _26310 f h). Qed.
Lemma lem1119936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119937 {_26299 _26310 : Type'} (f : type540 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) f x).
Proof. exact (@lem1119936 (_26299 -> _26310) (type1139 _26299 _26310) f x). Qed.
Lemma lem1119938 {_26299 _26310 : Type'} (f : _26299 -> _26310) : (@List.map _26299 _26310 f) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f).
Proof. exact (@lem1119937 _26299 _26310 (@List.map _26299 _26310) f). Qed.
Lemma lem1119939 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119940 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 f t) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f t).
Proof. exact (MK_COMB (@lem1119938 _26299 _26310 f) (@lem1119939 _26299 t)). Qed.
Lemma lem1119942 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119943 {_26299 _26310 : Type'} (f : type1139 _26299 _26310) (x : list _26299) : (f x) = (@I ((list _26299) -> list _26310) f x).
Proof. exact (@lem1119942 (list _26299) (list _26310) f x). Qed.
Lemma lem1119944 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f t) = (term178 _26299 _26310 f t).
Proof. exact (@lem1119943 _26299 _26310 (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) f) t). Qed.
Lemma lem1119946 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 f t) = (term178 _26299 _26310 f t).
Proof. exact (TRANS (@lem1119940 _26299 _26310 f t) (@lem1119944 _26299 _26310 f t)). Qed.
Lemma lem1119947 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) : (term196 _26299 _26310 f h) = (term197 _26299 _26310 f h).
Proof. exact (MK_COMB (@lem1119921 _26310) (@lem1119929 _26299 _26310 f h)). Qed.
Lemma lem1119948 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term7 _26299 _26310 h f t) = (term198 _26299 _26310 h f t).
Proof. exact (MK_COMB (@lem1119947 _26299 _26310 f h) (@lem1119946 _26299 _26310 f t)). Qed.
Lemma lem1119950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119951 {_26310 : Type'} (f : type1397 _26310) (x : _26310) : (f x) = (@I (_26310 -> (list _26310) -> list _26310) f x).
Proof. exact (@lem1119950 _26310 (type1138 _26310) f x). Qed.
Lemma lem1119952 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) : (term197 _26299 _26310 f h) = (term199 _26299 _26310 f h).
Proof. exact (@lem1119951 _26310 (@cons _26310) (@I (_26299 -> _26310) f h)). Qed.
Lemma lem1119953 {_26299 _26310 : Type'} (f : _26299 -> _26310) (t : list _26299) : (term178 _26299 _26310 f t) = (term178 _26299 _26310 f t).
Proof. exact (eq_refl (term178 _26299 _26310 f t)). Qed.
Lemma lem1119954 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term198 _26299 _26310 h f t) = (term200 _26299 _26310 h f t).
Proof. exact (MK_COMB (@lem1119952 _26299 _26310 f h) (@lem1119953 _26299 _26310 f t)). Qed.
Lemma lem1119956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119957 {_26310 : Type'} (f : type1138 _26310) (x : list _26310) : (f x) = (@I ((list _26310) -> list _26310) f x).
Proof. exact (@lem1119956 (list _26310) (list _26310) f x). Qed.
Lemma lem1119958 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term200 _26299 _26310 h f t) = (term201 _26299 _26310 h f t).
Proof. exact (@lem1119957 _26310 (term199 _26299 _26310 f h) (term178 _26299 _26310 f t)). Qed.
Lemma lem1119959 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term198 _26299 _26310 h f t) = (term201 _26299 _26310 h f t).
Proof. exact (TRANS (@lem1119954 _26299 _26310 h f t) (@lem1119958 _26299 _26310 h f t)). Qed.
Lemma lem1119960 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term7 _26299 _26310 h f t) = (term201 _26299 _26310 h f t).
Proof. exact (TRANS (@lem1119948 _26299 _26310 h f t) (@lem1119959 _26299 _26310 h f t)). Qed.
Lemma lem1119961 {_26310 : Type'} : (@cons _26310) = (@cons _26310).
Proof. exact (eq_refl (@cons _26310)). Qed.
Lemma lem1119966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119967 {_26299 _26310 : Type'} (f : _26299 -> _26310) (x : _26299) : (f x) = (@I (_26299 -> _26310) f x).
Proof. exact (@lem1119966 _26299 _26310 f x). Qed.
Lemma lem1119969 {_26299 _26310 : Type'} (g : _26299 -> _26310) (h : _26299) : (g h) = (@I (_26299 -> _26310) g h).
Proof. exact (@lem1119967 _26299 _26310 g h). Qed.
Lemma lem1119976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119977 {_26299 _26310 : Type'} (f : type540 _26299 _26310) (x : _26299 -> _26310) : (f x) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) f x).
Proof. exact (@lem1119976 (_26299 -> _26310) (type1139 _26299 _26310) f x). Qed.
Lemma lem1119978 {_26299 _26310 : Type'} (g : _26299 -> _26310) : (@List.map _26299 _26310 g) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g).
Proof. exact (@lem1119977 _26299 _26310 (@List.map _26299 _26310) g). Qed.
Lemma lem1119979 {_26299 : Type'} (t : list _26299) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1119980 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 g t) = (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g t).
Proof. exact (MK_COMB (@lem1119978 _26299 _26310 g) (@lem1119979 _26299 t)). Qed.
Lemma lem1119982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119983 {_26299 _26310 : Type'} (f : type1139 _26299 _26310) (x : list _26299) : (f x) = (@I ((list _26299) -> list _26310) f x).
Proof. exact (@lem1119982 (list _26299) (list _26310) f x). Qed.
Lemma lem1119984 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g t) = (term178 _26299 _26310 g t).
Proof. exact (@lem1119983 _26299 _26310 (@I ((_26299 -> _26310) -> (list _26299) -> list _26310) (@List.map _26299 _26310) g) t). Qed.
Lemma lem1119986 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (@List.map _26299 _26310 g t) = (term178 _26299 _26310 g t).
Proof. exact (TRANS (@lem1119980 _26299 _26310 g t) (@lem1119984 _26299 _26310 g t)). Qed.
Lemma lem1119987 {_26299 _26310 : Type'} (g : _26299 -> _26310) (h : _26299) : (term196 _26299 _26310 g h) = (term197 _26299 _26310 g h).
Proof. exact (MK_COMB (@lem1119961 _26310) (@lem1119969 _26299 _26310 g h)). Qed.
Lemma lem1119988 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term7 _26299 _26310 h g t) = (term198 _26299 _26310 h g t).
Proof. exact (MK_COMB (@lem1119987 _26299 _26310 g h) (@lem1119986 _26299 _26310 g t)). Qed.
Lemma lem1119990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119991 {_26310 : Type'} (f : type1397 _26310) (x : _26310) : (f x) = (@I (_26310 -> (list _26310) -> list _26310) f x).
Proof. exact (@lem1119990 _26310 (type1138 _26310) f x). Qed.
Lemma lem1119992 {_26299 _26310 : Type'} (g : _26299 -> _26310) (h : _26299) : (term197 _26299 _26310 g h) = (term199 _26299 _26310 g h).
Proof. exact (@lem1119991 _26310 (@cons _26310) (@I (_26299 -> _26310) g h)). Qed.
Lemma lem1119993 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (term178 _26299 _26310 g t) = (term178 _26299 _26310 g t).
Proof. exact (eq_refl (term178 _26299 _26310 g t)). Qed.
Lemma lem1119994 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term198 _26299 _26310 h g t) = (term200 _26299 _26310 h g t).
Proof. exact (MK_COMB (@lem1119992 _26299 _26310 g h) (@lem1119993 _26299 _26310 g t)). Qed.
Lemma lem1119996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1119997 {_26310 : Type'} (f : type1138 _26310) (x : list _26310) : (f x) = (@I ((list _26310) -> list _26310) f x).
Proof. exact (@lem1119996 (list _26310) (list _26310) f x). Qed.
Lemma lem1119998 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term200 _26299 _26310 h g t) = (term201 _26299 _26310 h g t).
Proof. exact (@lem1119997 _26310 (term199 _26299 _26310 g h) (term178 _26299 _26310 g t)). Qed.
Lemma lem1119999 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term198 _26299 _26310 h g t) = (term201 _26299 _26310 h g t).
Proof. exact (TRANS (@lem1119994 _26299 _26310 h g t) (@lem1119998 _26299 _26310 h g t)). Qed.
Lemma lem1120000 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term7 _26299 _26310 h g t) = (term201 _26299 _26310 h g t).
Proof. exact (TRANS (@lem1119988 _26299 _26310 h g t) (@lem1119999 _26299 _26310 h g t)). Qed.
Lemma lem1120001 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (t : list _26299) : (term63 _26299 _26310 h f t) = (term202 _26299 _26310 h f t).
Proof. exact (MK_COMB (@lem1119920 _26310) (@lem1119960 _26299 _26310 h f t)). Qed.
Lemma lem1120002 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : ((term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t)) = ((term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t)).
Proof. exact (MK_COMB (@lem1120001 _26299 _26310 h f t) (@lem1120000 _26299 _26310 h g t)). Qed.
Lemma lem1120003 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term176 _26299 _26310 f h g t) = (term203 _26299 _26310 f h g t).
Proof. exact (MK_COMB (@lem1119919) (@lem1120002 _26299 _26310 f h g t)). Qed.
Lemma lem1120064 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) : term188 _26299 _26310 _18171 f g t.
Proof. exact (h1). Qed.
Lemma lem1120118 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t).
Proof. exact (h1). Qed.
Lemma lem1120174 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) : term188 _26299 _26310 _18171 f g t.
Proof. exact (h1). Qed.
Lemma lem1120176 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) : term203 _26299 _26310 f h g t.
Proof. exact (EQ_MP (@lem1120003 _26299 _26310 f h g t) (@lem1119666 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120194 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t).
Proof. exact (h1). Qed.
Lemma lem1120382 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term186 _26299 _26310 _18171 f g t.
Proof. exact (proj2 (@lem1119918 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120383 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term204 _26299 _26310 _18171 f g t.
Proof. exact (fun h0 : term188 _26299 _26310 _18171 f g t => @lem1120382 _26299 _26310 h _18171 f g t h1). Qed.
Lemma lem1120385 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120386 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term204 _26299 _26310 _18171 f g t) = (term186 _26299 _26310 _18171 f g t).
Proof. exact (@lem1120385 (term186 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1120387 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term186 _26299 _26310 _18171 f g t.
Proof. exact (EQ_MP (@lem1120386 _26299 _26310 _18171 f g t) (@lem1120383 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120390 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1120392 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term188 _26299 _26310 _18171 f g t) = (term206 _26299 _26310 _18171 f g t).
Proof. exact (@lem1120390 (term186 _26299 _26310 _18171 f g t)). Qed.
Lemma lem1120395 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) : term206 _26299 _26310 _18171 f g t.
Proof. exact (EQ_MP (@lem1120392 _26299 _26310 _18171 f g t) (@lem1120174 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120398 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : False.
Proof. exact (@lem1120395 _26299 _26310 _18171 f g t h1 (@lem1120387 _26299 _26310 h _18171 f g t h2)). Qed.
Lemma lem1120399 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : term207.
Proof. exact (fun h0 : ~ False => @lem1120398 _26299 _26310 h _18171 f g t h1 h2). Qed.
Lemma lem1120401 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120402 : term207 = False.
Proof. exact (@lem1120401 False). Qed.
Lemma lem1120403 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120402) (@lem1120399 _26299 _26310 h _18171 f g t h1 h2)). Qed.
Lemma lem1120502 {_26310 : Type'} : (@I (_26310 -> (list _26310) -> list _26310)) = (@I (_26310 -> (list _26310) -> list _26310)).
Proof. exact (eq_refl (@I (_26310 -> (list _26310) -> list _26310))). Qed.
Lemma lem1120503 {_26310 : Type'} (_18248 : type1397 _26310) (_18250 : type1397 _26310) (h1 : _18248 = _18250) : _18248 = _18250.
Proof. exact (h1). Qed.
Lemma lem1120504 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (h1 : _18249 = _18251) : _18249 = _18251.
Proof. exact (h1). Qed.
Lemma lem1120505 {_26310 : Type'} (_18248 : type1397 _26310) (_18250 : type1397 _26310) (h1 : _18248 = _18250) : (@I (_26310 -> (list _26310) -> list _26310) _18248) = (@I (_26310 -> (list _26310) -> list _26310) _18250).
Proof. exact (MK_COMB (@lem1120502 _26310) (@lem1120503 _26310 _18248 _18250 h1)). Qed.
Lemma lem1120506 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) (h1 : _18249 = _18251) (h2 : _18248 = _18250) : (@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251).
Proof. exact (MK_COMB (@lem1120505 _26310 _18248 _18250 h2) (@lem1120504 _26310 _18249 _18251 h1)). Qed.
Lemma lem1120507 {_26310 : Type'} (_18248 : type1397 _26310) (_18250 : type1397 _26310) (_18249 : _26310) (_18251 : _26310) (h1 : _18249 = _18251) : term208 _26310 _18248 _18249 _18250 _18251.
Proof. exact (fun h0 : _18248 = _18250 => @lem1120506 _26310 _18249 _18251 _18248 _18250 h1 h0). Qed.
Lemma lem1120509 (a : Prop) (b : Prop) : (a -> b) = (term209 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1120510 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : (term208 _26310 _18248 _18249 _18250 _18251) = (term210 _26310 _18248 _18249 _18250 _18251).
Proof. exact (@lem1120509 (_18248 = _18250) ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251))). Qed.
Lemma lem1120511 {_26310 : Type'} (_18248 : type1397 _26310) (_18250 : type1397 _26310) (_18249 : _26310) (_18251 : _26310) (h1 : _18249 = _18251) : term210 _26310 _18248 _18249 _18250 _18251.
Proof. exact (EQ_MP (@lem1120510 _26310 _18248 _18249 _18250 _18251) (@lem1120507 _26310 _18248 _18250 _18249 _18251 h1)). Qed.
Lemma lem1120512 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : term211 _26310 _18248 _18249 _18250 _18251.
Proof. exact (fun h0 : _18249 = _18251 => @lem1120511 _26310 _18248 _18250 _18249 _18251 h0). Qed.
Lemma lem1120514 (a : Prop) (b : Prop) : (a -> b) = (term209 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1120515 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : (term211 _26310 _18248 _18249 _18250 _18251) = (term212 _26310 _18248 _18249 _18250 _18251).
Proof. exact (@lem1120514 (_18249 = _18251) (term210 _26310 _18248 _18249 _18250 _18251)). Qed.
Lemma lem1120516 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : term212 _26310 _18248 _18249 _18250 _18251.
Proof. exact (EQ_MP (@lem1120515 _26310 _18248 _18249 _18250 _18251) (@lem1120512 _26310 _18248 _18249 _18250 _18251)). Qed.
Lemma lem1120547 {_26310 : Type'} : (@I ((list _26310) -> list _26310)) = (@I ((list _26310) -> list _26310)).
Proof. exact (eq_refl (@I ((list _26310) -> list _26310))). Qed.
Lemma lem1120548 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (h1 : _18260 = _18262) : _18260 = _18262.
Proof. exact (h1). Qed.
Lemma lem1120549 {_26310 : Type'} (_18261 : list _26310) (_18263 : list _26310) (h1 : _18261 = _18263) : _18261 = _18263.
Proof. exact (h1). Qed.
Lemma lem1120550 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (h1 : _18260 = _18262) : (@I ((list _26310) -> list _26310) _18260) = (@I ((list _26310) -> list _26310) _18262).
Proof. exact (MK_COMB (@lem1120547 _26310) (@lem1120548 _26310 _18260 _18262 h1)). Qed.
Lemma lem1120551 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) (h1 : _18260 = _18262) (h2 : _18261 = _18263) : (@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263).
Proof. exact (MK_COMB (@lem1120550 _26310 _18260 _18262 h1) (@lem1120549 _26310 _18261 _18263 h2)). Qed.
Lemma lem1120552 {_26310 : Type'} (_18261 : list _26310) (_18263 : list _26310) (_18260 : type1138 _26310) (_18262 : type1138 _26310) (h1 : _18260 = _18262) : term213 _26310 _18260 _18261 _18262 _18263.
Proof. exact (fun h0 : _18261 = _18263 => @lem1120551 _26310 _18260 _18262 _18261 _18263 h1 h0). Qed.
Lemma lem1120554 (a : Prop) (b : Prop) : (a -> b) = (term209 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1120555 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : (term213 _26310 _18260 _18261 _18262 _18263) = (term214 _26310 _18260 _18261 _18262 _18263).
Proof. exact (@lem1120554 (_18261 = _18263) ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263))). Qed.
Lemma lem1120556 {_26310 : Type'} (_18261 : list _26310) (_18263 : list _26310) (_18260 : type1138 _26310) (_18262 : type1138 _26310) (h1 : _18260 = _18262) : term214 _26310 _18260 _18261 _18262 _18263.
Proof. exact (EQ_MP (@lem1120555 _26310 _18260 _18261 _18262 _18263) (@lem1120552 _26310 _18261 _18263 _18260 _18262 h1)). Qed.
Lemma lem1120557 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : term215 _26310 _18260 _18261 _18262 _18263.
Proof. exact (fun h0 : _18260 = _18262 => @lem1120556 _26310 _18261 _18263 _18260 _18262 h0). Qed.
Lemma lem1120559 (a : Prop) (b : Prop) : (a -> b) = (term209 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1120560 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : (term215 _26310 _18260 _18261 _18262 _18263) = (term216 _26310 _18260 _18261 _18262 _18263).
Proof. exact (@lem1120559 (_18260 = _18262) (term214 _26310 _18260 _18261 _18262 _18263)). Qed.
Lemma lem1120561 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : term216 _26310 _18260 _18261 _18262 _18263.
Proof. exact (EQ_MP (@lem1120560 _26310 _18260 _18261 _18262 _18263) (@lem1120557 _26310 _18260 _18261 _18262 _18263)). Qed.
Lemma lem1120591 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : (@I (_26299 -> _26310) f h) = (@I (_26299 -> _26310) g h).
Proof. exact (proj1 (@lem1119918 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120592 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term217 _26299 _26310 f g h.
Proof. exact (fun h0 : term218 _26299 _26310 f g h => @lem1120591 _26299 _26310 h _18171 f g t h1). Qed.
Lemma lem1120594 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120595 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term217 _26299 _26310 f g h) = ((@I (_26299 -> _26310) f h) = (@I (_26299 -> _26310) g h)).
Proof. exact (@lem1120594 ((@I (_26299 -> _26310) f h) = (@I (_26299 -> _26310) g h))). Qed.
Lemma lem1120596 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : (@I (_26299 -> _26310) f h) = (@I (_26299 -> _26310) g h).
Proof. exact (EQ_MP (@lem1120595 _26299 _26310 f g h) (@lem1120592 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120598 {_26310 : Type'} (x : type1397 _26310) : x = x.
Proof. exact (@lem21386 (type1397 _26310) x). Qed.
Lemma lem1120599 {_26310 : Type'} (x : type1397 _26310) : x = x.
Proof. exact (@lem1120598 _26310 x). Qed.
Lemma lem1120600 {_26310 : Type'} : (@cons _26310) = (@cons _26310).
Proof. exact (@lem1120599 _26310 (@cons _26310)). Qed.
Lemma lem1120601 {_26310 : Type'} : term219 _26310.
Proof. exact (fun h0 : term220 _26310 => @lem1120600 _26310). Qed.
Lemma lem1120603 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120604 {_26310 : Type'} : (term219 _26310) = ((@cons _26310) = (@cons _26310)).
Proof. exact (@lem1120603 ((@cons _26310) = (@cons _26310))). Qed.
Lemma lem1120605 {_26310 : Type'} : (@cons _26310) = (@cons _26310).
Proof. exact (EQ_MP (@lem1120604 _26310) (@lem1120601 _26310)). Qed.
Lemma lem1120623 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1120624 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term210 _26310 _18248 _18249 _18250 _18251) = (term221 _26310 _18249 _18251 _18248 _18250).
Proof. exact (@lem1120623 ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251)) (term222 _26310 _18248 _18250)). Qed.
Lemma lem1120634 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) : (term223 _26310 _18249 _18251) = (term223 _26310 _18249 _18251).
Proof. exact (eq_refl (term223 _26310 _18249 _18251)). Qed.
Lemma lem1120635 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term212 _26310 _18248 _18249 _18250 _18251) = (term224 _26310 _18249 _18251 _18248 _18250).
Proof. exact (MK_COMB (@lem1120634 _26310 _18249 _18251) (@lem1120624 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120639 (q : Prop) (p : Prop) (r : Prop) : (term225 p q r) = (term225 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1120640 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term224 _26310 _18249 _18251 _18248 _18250) = (term226 _26310 _18249 _18251 _18248 _18250).
Proof. exact (@lem1120639 ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251)) (term227 _26310 _18249 _18251) (term222 _26310 _18248 _18250)). Qed.
Lemma lem1120662 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term212 _26310 _18248 _18249 _18250 _18251) = (term226 _26310 _18249 _18251 _18248 _18250).
Proof. exact (TRANS (@lem1120635 _26310 _18249 _18251 _18248 _18250) (@lem1120640 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1120664 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term228 _26310 _18248 _18249 _18250 _18251) = (term229 _26310 _18249 _18251 _18248 _18250).
Proof. exact (MK_COMB (@lem1120663) (@lem1120662 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120686 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term226 _26310 _18249 _18251 _18248 _18250) = (term226 _26310 _18249 _18251 _18248 _18250).
Proof. exact (eq_refl (term226 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120687 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : ((term212 _26310 _18248 _18249 _18250 _18251) = (term226 _26310 _18249 _18251 _18248 _18250)) = ((term226 _26310 _18249 _18251 _18248 _18250) = (term226 _26310 _18249 _18251 _18248 _18250)).
Proof. exact (MK_COMB (@lem1120664 _26310 _18249 _18251 _18248 _18250) (@lem1120686 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1120690 (x : Prop) : (x = x) = True.
Proof. exact (@lem1120689 Prop x). Qed.
Lemma lem1120691 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : ((term226 _26310 _18249 _18251 _18248 _18250) = (term226 _26310 _18249 _18251 _18248 _18250)) = True.
Proof. exact (@lem1120690 (term226 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120692 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : ((term212 _26310 _18248 _18249 _18250 _18251) = (term226 _26310 _18249 _18251 _18248 _18250)) = True.
Proof. exact (TRANS (@lem1120687 _26310 _18249 _18251 _18248 _18250) (@lem1120691 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120693 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : True = ((term212 _26310 _18248 _18249 _18250 _18251) = (term226 _26310 _18249 _18251 _18248 _18250)).
Proof. exact (SYM (@lem1120692 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120694 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term212 _26310 _18248 _18249 _18250 _18251) = (term226 _26310 _18249 _18251 _18248 _18250).
Proof. exact (EQ_MP (@lem1120693 _26310 _18249 _18251 _18248 _18250) (@lem0)). Qed.
Lemma lem1120695 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : term226 _26310 _18249 _18251 _18248 _18250.
Proof. exact (EQ_MP (@lem1120694 _26310 _18249 _18251 _18248 _18250) (@lem1120516 _26310 _18248 _18249 _18250 _18251)). Qed.
Lemma lem1120697 (b : Prop) (a : Prop) : (a \/ b) = (term230 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1120698 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : (term226 _26310 _18249 _18251 _18248 _18250) = (term231 _26310 _18248 _18249 _18250 _18251).
Proof. exact (@lem1120697 (term232 _26310 _18249 _18251 _18248 _18250) ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251))). Qed.
Lemma lem1120700 (a : Prop) (b : Prop) : (term233 a b) = (term234 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1120701 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term235 _26310 _18249 _18251 _18248 _18250) = (term236 _26310 _18249 _18251 _18248 _18250).
Proof. exact (@lem1120700 (term227 _26310 _18249 _18251) (term222 _26310 _18248 _18250)). Qed.
Lemma lem1120703 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1120704 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) : (term237 _26310 _18249 _18251) = (_18249 = _18251).
Proof. exact (@lem1120703 (_18249 = _18251)). Qed.
Lemma lem1120705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1120706 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) : (term238 _26310 _18249 _18251) = (term239 _26310 _18249 _18251).
Proof. exact (MK_COMB (@lem1120705) (@lem1120704 _26310 _18249 _18251)). Qed.
Lemma lem1120708 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1120709 {_26310 : Type'} (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term240 _26310 _18248 _18250) = (_18248 = _18250).
Proof. exact (@lem1120708 (_18248 = _18250)). Qed.
Lemma lem1120710 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term236 _26310 _18249 _18251 _18248 _18250) = (term241 _26310 _18249 _18251 _18248 _18250).
Proof. exact (MK_COMB (@lem1120706 _26310 _18249 _18251) (@lem1120709 _26310 _18248 _18250)). Qed.
Lemma lem1120711 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term235 _26310 _18249 _18251 _18248 _18250) = (term241 _26310 _18249 _18251 _18248 _18250).
Proof. exact (TRANS (@lem1120701 _26310 _18249 _18251 _18248 _18250) (@lem1120710 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1120713 {_26310 : Type'} (_18249 : _26310) (_18251 : _26310) (_18248 : type1397 _26310) (_18250 : type1397 _26310) : (term242 _26310 _18249 _18251 _18248 _18250) = (term243 _26310 _18249 _18251 _18248 _18250).
Proof. exact (MK_COMB (@lem1120712) (@lem1120711 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120714 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251)) = ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251)).
Proof. exact (eq_refl ((@I (_26310 -> (list _26310) -> list _26310) _18248 _18249) = (@I (_26310 -> (list _26310) -> list _26310) _18250 _18251))). Qed.
Lemma lem1120715 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : (term231 _26310 _18248 _18249 _18250 _18251) = (term244 _26310 _18248 _18249 _18250 _18251).
Proof. exact (MK_COMB (@lem1120713 _26310 _18249 _18251 _18248 _18250) (@lem1120714 _26310 _18248 _18249 _18250 _18251)). Qed.
Lemma lem1120716 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : (term226 _26310 _18249 _18251 _18248 _18250) = (term244 _26310 _18248 _18249 _18250 _18251).
Proof. exact (TRANS (@lem1120698 _26310 _18248 _18249 _18250 _18251) (@lem1120715 _26310 _18248 _18249 _18250 _18251)). Qed.
Lemma lem1120718 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term245 _26299 _26310 f g h.
Proof. exact (conj (@lem1120596 _26299 _26310 h _18171 f g t h1) (@lem1120605 _26310)). Qed.
Lemma lem1120720 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : term244 _26310 _18248 _18249 _18250 _18251.
Proof. exact (EQ_MP (@lem1120716 _26310 _18248 _18249 _18250 _18251) (@lem1120695 _26310 _18249 _18251 _18248 _18250)). Qed.
Lemma lem1120721 {_26310 : Type'} (_18248 : type1397 _26310) (_18249 : _26310) (_18250 : type1397 _26310) (_18251 : _26310) : term244 _26310 _18248 _18249 _18250 _18251.
Proof. exact (@lem1120720 _26310 _18248 _18249 _18250 _18251). Qed.
Lemma lem1120722 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : term246 _26299 _26310 f g h.
Proof. exact (@lem1120721 _26310 (@cons _26310) (@I (_26299 -> _26310) f h) (@cons _26310) (@I (_26299 -> _26310) g h)). Qed.
Lemma lem1120725 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : (term199 _26299 _26310 f h) = (term199 _26299 _26310 g h).
Proof. exact (@lem1120722 _26299 _26310 f g h (@lem1120718 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120726 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : term247 _26299 _26310 f g h.
Proof. exact (fun h0 : term248 _26299 _26310 f g h => @lem1120725 _26299 _26310 h _18171 f g t h1). Qed.
Lemma lem1120728 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120729 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : (term247 _26299 _26310 f g h) = ((term199 _26299 _26310 f h) = (term199 _26299 _26310 g h)).
Proof. exact (@lem1120728 ((term199 _26299 _26310 f h) = (term199 _26299 _26310 g h))). Qed.
Lemma lem1120730 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) : (term199 _26299 _26310 f h) = (term199 _26299 _26310 g h).
Proof. exact (EQ_MP (@lem1120729 _26299 _26310 f g h) (@lem1120726 _26299 _26310 h _18171 f g t h1)). Qed.
Lemma lem1120732 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t).
Proof. exact (h1). Qed.
Lemma lem1120733 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : term249 _26299 _26310 f g t.
Proof. exact (fun h0 : term250 _26299 _26310 f g t => @lem1120732 _26299 _26310 f g t h1). Qed.
Lemma lem1120735 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120736 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) : (term249 _26299 _26310 f g t) = ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)).
Proof. exact (@lem1120735 ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t))). Qed.
Lemma lem1120737 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t).
Proof. exact (EQ_MP (@lem1120736 _26299 _26310 f g t) (@lem1120733 _26299 _26310 f g t h1)). Qed.
Lemma lem1120755 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1120756 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term214 _26310 _18260 _18261 _18262 _18263) = (term251 _26310 _18260 _18262 _18261 _18263).
Proof. exact (@lem1120755 ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263)) (term252 _26310 _18261 _18263)). Qed.
Lemma lem1120766 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) : (term253 _26310 _18260 _18262) = (term253 _26310 _18260 _18262).
Proof. exact (eq_refl (term253 _26310 _18260 _18262)). Qed.
Lemma lem1120767 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term216 _26310 _18260 _18261 _18262 _18263) = (term254 _26310 _18260 _18262 _18261 _18263).
Proof. exact (MK_COMB (@lem1120766 _26310 _18260 _18262) (@lem1120756 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120771 (q : Prop) (p : Prop) (r : Prop) : (term225 p q r) = (term225 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1120772 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term254 _26310 _18260 _18262 _18261 _18263) = (term255 _26310 _18260 _18262 _18261 _18263).
Proof. exact (@lem1120771 ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263)) (term256 _26310 _18260 _18262) (term252 _26310 _18261 _18263)). Qed.
Lemma lem1120794 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term216 _26310 _18260 _18261 _18262 _18263) = (term255 _26310 _18260 _18262 _18261 _18263).
Proof. exact (TRANS (@lem1120767 _26310 _18260 _18262 _18261 _18263) (@lem1120772 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1120796 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term257 _26310 _18260 _18261 _18262 _18263) = (term258 _26310 _18260 _18262 _18261 _18263).
Proof. exact (MK_COMB (@lem1120795) (@lem1120794 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120818 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term255 _26310 _18260 _18262 _18261 _18263) = (term255 _26310 _18260 _18262 _18261 _18263).
Proof. exact (eq_refl (term255 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120819 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : ((term216 _26310 _18260 _18261 _18262 _18263) = (term255 _26310 _18260 _18262 _18261 _18263)) = ((term255 _26310 _18260 _18262 _18261 _18263) = (term255 _26310 _18260 _18262 _18261 _18263)).
Proof. exact (MK_COMB (@lem1120796 _26310 _18260 _18262 _18261 _18263) (@lem1120818 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120821 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1120822 (x : Prop) : (x = x) = True.
Proof. exact (@lem1120821 Prop x). Qed.
Lemma lem1120823 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : ((term255 _26310 _18260 _18262 _18261 _18263) = (term255 _26310 _18260 _18262 _18261 _18263)) = True.
Proof. exact (@lem1120822 (term255 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120824 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : ((term216 _26310 _18260 _18261 _18262 _18263) = (term255 _26310 _18260 _18262 _18261 _18263)) = True.
Proof. exact (TRANS (@lem1120819 _26310 _18260 _18262 _18261 _18263) (@lem1120823 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120825 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : True = ((term216 _26310 _18260 _18261 _18262 _18263) = (term255 _26310 _18260 _18262 _18261 _18263)).
Proof. exact (SYM (@lem1120824 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120826 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term216 _26310 _18260 _18261 _18262 _18263) = (term255 _26310 _18260 _18262 _18261 _18263).
Proof. exact (EQ_MP (@lem1120825 _26310 _18260 _18262 _18261 _18263) (@lem0)). Qed.
Lemma lem1120827 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : term255 _26310 _18260 _18262 _18261 _18263.
Proof. exact (EQ_MP (@lem1120826 _26310 _18260 _18262 _18261 _18263) (@lem1120561 _26310 _18260 _18261 _18262 _18263)). Qed.
Lemma lem1120829 (b : Prop) (a : Prop) : (a \/ b) = (term230 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1120830 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : (term255 _26310 _18260 _18262 _18261 _18263) = (term259 _26310 _18260 _18261 _18262 _18263).
Proof. exact (@lem1120829 (term260 _26310 _18260 _18262 _18261 _18263) ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263))). Qed.
Lemma lem1120832 (a : Prop) (b : Prop) : (term233 a b) = (term234 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1120833 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term261 _26310 _18260 _18262 _18261 _18263) = (term262 _26310 _18260 _18262 _18261 _18263).
Proof. exact (@lem1120832 (term256 _26310 _18260 _18262) (term252 _26310 _18261 _18263)). Qed.
Lemma lem1120835 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1120836 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) : (term263 _26310 _18260 _18262) = (_18260 = _18262).
Proof. exact (@lem1120835 (_18260 = _18262)). Qed.
Lemma lem1120837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1120838 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) : (term264 _26310 _18260 _18262) = (term265 _26310 _18260 _18262).
Proof. exact (MK_COMB (@lem1120837) (@lem1120836 _26310 _18260 _18262)). Qed.
Lemma lem1120840 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1120841 {_26310 : Type'} (_18261 : list _26310) (_18263 : list _26310) : (term266 _26310 _18261 _18263) = (_18261 = _18263).
Proof. exact (@lem1120840 (_18261 = _18263)). Qed.
Lemma lem1120842 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term262 _26310 _18260 _18262 _18261 _18263) = (term267 _26310 _18260 _18262 _18261 _18263).
Proof. exact (MK_COMB (@lem1120838 _26310 _18260 _18262) (@lem1120841 _26310 _18261 _18263)). Qed.
Lemma lem1120843 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term261 _26310 _18260 _18262 _18261 _18263) = (term267 _26310 _18260 _18262 _18261 _18263).
Proof. exact (TRANS (@lem1120833 _26310 _18260 _18262 _18261 _18263) (@lem1120842 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1120845 {_26310 : Type'} (_18260 : type1138 _26310) (_18262 : type1138 _26310) (_18261 : list _26310) (_18263 : list _26310) : (term268 _26310 _18260 _18262 _18261 _18263) = (term269 _26310 _18260 _18262 _18261 _18263).
Proof. exact (MK_COMB (@lem1120844) (@lem1120843 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120846 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263)) = ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263)).
Proof. exact (eq_refl ((@I ((list _26310) -> list _26310) _18260 _18261) = (@I ((list _26310) -> list _26310) _18262 _18263))). Qed.
Lemma lem1120847 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : (term259 _26310 _18260 _18261 _18262 _18263) = (term270 _26310 _18260 _18261 _18262 _18263).
Proof. exact (MK_COMB (@lem1120845 _26310 _18260 _18262 _18261 _18263) (@lem1120846 _26310 _18260 _18261 _18262 _18263)). Qed.
Lemma lem1120848 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : (term255 _26310 _18260 _18262 _18261 _18263) = (term270 _26310 _18260 _18261 _18262 _18263).
Proof. exact (TRANS (@lem1120830 _26310 _18260 _18261 _18262 _18263) (@lem1120847 _26310 _18260 _18261 _18262 _18263)). Qed.
Lemma lem1120850 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : term271 _26299 _26310 h f g t.
Proof. exact (conj (@lem1120730 _26299 _26310 h _18171 f g t h1) (@lem1120737 _26299 _26310 f g t h2)). Qed.
Lemma lem1120852 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : term270 _26310 _18260 _18261 _18262 _18263.
Proof. exact (EQ_MP (@lem1120848 _26310 _18260 _18261 _18262 _18263) (@lem1120827 _26310 _18260 _18262 _18261 _18263)). Qed.
Lemma lem1120853 {_26310 : Type'} (_18260 : type1138 _26310) (_18261 : list _26310) (_18262 : type1138 _26310) (_18263 : list _26310) : term270 _26310 _18260 _18261 _18262 _18263.
Proof. exact (@lem1120852 _26310 _18260 _18261 _18262 _18263). Qed.
Lemma lem1120854 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term272 _26299 _26310 f h g t.
Proof. exact (@lem1120853 _26310 (term199 _26299 _26310 f h) (term178 _26299 _26310 f t) (term199 _26299 _26310 g h) (term178 _26299 _26310 g t)). Qed.
Lemma lem1120857 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t).
Proof. exact (@lem1120854 _26299 _26310 f h g t (@lem1120850 _26299 _26310 h _18171 f g t h1 h2)). Qed.
Lemma lem1120858 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : term273 _26299 _26310 f h g t.
Proof. exact (fun h0 : term203 _26299 _26310 f h g t => @lem1120857 _26299 _26310 h _18171 f g t h1 h2). Qed.
Lemma lem1120860 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120861 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term273 _26299 _26310 f h g t) = ((term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t)).
Proof. exact (@lem1120860 ((term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t))). Qed.
Lemma lem1120862 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : (term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t).
Proof. exact (EQ_MP (@lem1120861 _26299 _26310 f h g t) (@lem1120858 _26299 _26310 h _18171 f g t h1 h2)). Qed.
Lemma lem1120865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1120867 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term203 _26299 _26310 f h g t) = (term274 _26299 _26310 f h g t).
Proof. exact (@lem1120865 ((term201 _26299 _26310 h f t) = (term201 _26299 _26310 h g t))). Qed.
Lemma lem1120870 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) : term274 _26299 _26310 f h g t.
Proof. exact (EQ_MP (@lem1120867 _26299 _26310 f h g t) (@lem1120176 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120873 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : False.
Proof. exact (@lem1120870 _26299 _26310 f h g t h1 (@lem1120862 _26299 _26310 h _18171 f g t h2 h3)). Qed.
Lemma lem1120874 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : term207.
Proof. exact (fun h0 : ~ False => @lem1120873 _26299 _26310 h _18171 f g t h1 h2 h3). Qed.
Lemma lem1120876 (p : Prop) : (term205 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1120877 : term207 = False.
Proof. exact (@lem1120876 False). Qed.
Lemma lem1120878 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : False.
Proof. exact (EQ_MP (@lem1120877) (@lem1120874 _26299 _26310 h _18171 f g t h1 h2 h3)). Qed.
Lemma lem1120879 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) = False.
Proof. exact (prop_ext (fun h4 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t) => @lem1120878 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1120194 _26299 _26310 f g t h3)). Qed.
Lemma lem1120880 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : False.
Proof. exact (EQ_MP (@lem1120879 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1120194 _26299 _26310 f g t h3)). Qed.
Lemma lem1120881 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : (term188 _26299 _26310 _18171 f g t) = False.
Proof. exact (prop_ext (fun h3 : term188 _26299 _26310 _18171 f g t => @lem1120403 _26299 _26310 h _18171 f g t h1 h2) (fun h3 : False => @lem1120174 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120882 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120881 _26299 _26310 h _18171 f g t h1 h2) (@lem1120174 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120883 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) = False.
Proof. exact (prop_ext (fun h4 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t) => @lem1120880 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1120118 _26299 _26310 f g t h3)). Qed.
Lemma lem1120884 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : False.
Proof. exact (EQ_MP (@lem1120883 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1120118 _26299 _26310 f g t h3)). Qed.
Lemma lem1120885 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : (term188 _26299 _26310 _18171 f g t) = False.
Proof. exact (prop_ext (fun h3 : term188 _26299 _26310 _18171 f g t => @lem1120882 _26299 _26310 h _18171 f g t h1 h2) (fun h3 : False => @lem1120064 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120886 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120885 _26299 _26310 h _18171 f g t h1 h2) (@lem1120064 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120887 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : ((term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) = False.
Proof. exact (prop_ext (fun h4 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t) => @lem1120884 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1120118 _26299 _26310 f g t h3)). Qed.
Lemma lem1120888 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t)) : False.
Proof. exact (EQ_MP (@lem1120887 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1120118 _26299 _26310 f g t h3)). Qed.
Lemma lem1120889 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : (term188 _26299 _26310 _18171 f g t) = False.
Proof. exact (prop_ext (fun h3 : term188 _26299 _26310 _18171 f g t => @lem1120886 _26299 _26310 h _18171 f g t h1 h2) (fun h3 : False => @lem1120064 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120890 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term188 _26299 _26310 _18171 f g t) (h2 : term100 _26299 _26310 h _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120889 _26299 _26310 h _18171 f g t h1 h2) (@lem1120064 _26299 _26310 _18171 f g t h1)). Qed.
Lemma lem1120891 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : False.
Proof. exact (or_elim (@lem1119862 _26299 _26310 _18171 f g t h3) (fun h0 : term188 _26299 _26310 _18171 f g t => @lem1120890 _26299 _26310 h _18171 f g t h0 h2) (fun h0 : (term178 _26299 _26310 f t) = (term178 _26299 _26310 g t) => @lem1120888 _26299 _26310 h _18171 f g t h1 h2 h0)). Qed.
Lemma lem1120892 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : (term176 _26299 _26310 f h g t) = False.
Proof. exact (prop_ext (fun h4 : term176 _26299 _26310 f h g t => @lem1120891 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1119666 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120893 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120892 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1119666 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120894 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : (term100 _26299 _26310 h _18171 f g t) = False.
Proof. exact (prop_ext (fun h4 : term100 _26299 _26310 h _18171 f g t => @lem1120893 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1119660 _26299 _26310 h _18171 f g t h2)). Qed.
Lemma lem1120895 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120894 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1119660 _26299 _26310 h _18171 f g t h2)). Qed.
Lemma lem1120896 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : (term176 _26299 _26310 f h g t) = False.
Proof. exact (prop_ext (fun h4 : term176 _26299 _26310 f h g t => @lem1120895 _26299 _26310 h _18171 f g t h1 h2 h3) (fun h4 : False => @lem1119201 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120897 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term176 _26299 _26310 f h g t) (h2 : term100 _26299 _26310 h _18171 f g t) (h3 : term105 _26299 _26310 _18171 f g t) : False.
Proof. exact (EQ_MP (@lem1120896 _26299 _26310 h _18171 f g t h1 h2 h3) (@lem1119201 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120898 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : term105 _26299 _26310 _18171 f g t) : term175 _26299 _26310 f h g t.
Proof. exact (fun h0 : term176 _26299 _26310 f h g t => @lem1120897 _26299 _26310 h _18171 f g t h0 h1 h2). Qed.
Lemma lem1120899 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term100 _26299 _26310 h _18171 f g t) (h2 : term105 _26299 _26310 _18171 f g t) : (term7 _26299 _26310 h f t) = (term7 _26299 _26310 h g t).
Proof. exact (EQ_MP (@lem1119200 _26299 _26310 f h g t) (@lem1120898 _26299 _26310 h _18171 f g t h1 h2)). Qed.
Lemma lem1120900 {_26299 _26310 : Type'} (h : _26299) (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term105 _26299 _26310 _18171 f g t) : term102 _26299 _26310 _18171 f h g t.
Proof. exact (fun h0 : term100 _26299 _26310 h _18171 f g t => @lem1120899 _26299 _26310 h _18171 f g t h0 h1). Qed.
Lemma lem1120901 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term107 _26299 _26310 _18171 f h g t.
Proof. exact (fun h0 : term105 _26299 _26310 _18171 f g t => @lem1120900 _26299 _26310 h _18171 f g t h0). Qed.
Lemma lem1120906 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term109 _26299 _26310 _18171 h g t.
Proof. exact (fun f : _26299 -> _26310 => @lem1120901 _26299 _26310 _18171 f h g t). Qed.
Lemma lem1120911 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (g : _26299 -> _26310) (t : list _26299) : term111 _26299 _26310 _18171 g t.
Proof. exact (fun h : _26299 => @lem1120906 _26299 _26310 _18171 h g t). Qed.
Lemma lem1120916 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) (t : list _26299) : term113 _26299 _26310 _18171 t.
Proof. exact (fun g : _26299 -> _26310 => @lem1120911 _26299 _26310 _18171 g t). Qed.
Lemma lem1120921 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : term115 _26299 _26310 _18171.
Proof. exact (fun t : list _26299 => @lem1120916 _26299 _26310 _18171 t). Qed.
Lemma lem1120922 {_26299 _26310 : Type'} (_18171 : type516 _26299 _26310) : term172 _26299 _26310 _18171.
Proof. exact (fun h0 : term170 _26299 _26310 _18171 => @lem1120921 _26299 _26310 _18171). Qed.
Lemma lem1120927 {_26299 _26310 : Type'} : term174 _26299 _26310.
Proof. exact (fun _18171 : type516 _26299 _26310 => @lem1120922 _26299 _26310 _18171). Qed.
Lemma lem1120928 {_26299 _26310 : Type'} : term89 _26299 _26310.
Proof. exact (EQ_MP (@lem1119193 _26299 _26310) (@lem1120927 _26299 _26310)). Qed.
Lemma lem1120929 {_26299 _26310 : Type'} (t : list _26299) : term275 _26299 _26310 t.
Proof. exact (@lem1120928 _26299 _26310 t). Qed.
Lemma lem1120930 {_26299 _26310 : Type'} (t : list _26299) : (term275 _26299 _26310 t) = (term85 _26299 _26310 t).
Proof. exact (eq_refl (term275 _26299 _26310 t)). Qed.
Lemma lem1120931 {_26299 _26310 : Type'} (t : list _26299) : term85 _26299 _26310 t.
Proof. exact (EQ_MP (@lem1120930 _26299 _26310 t) (@lem1120929 _26299 _26310 t)). Qed.
Lemma lem1120932 {_26299 _26310 : Type'} (t : list _26299) (g : _26299 -> _26310) : term276 _26299 _26310 t g.
Proof. exact (@lem1120931 _26299 _26310 t g). Qed.
Lemma lem1120933 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : (term276 _26299 _26310 t g) = (term81 _26299 _26310 g t).
Proof. exact (eq_refl (term276 _26299 _26310 t g)). Qed.
Lemma lem1120934 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) : term81 _26299 _26310 g t.
Proof. exact (EQ_MP (@lem1120933 _26299 _26310 g t) (@lem1120932 _26299 _26310 t g)). Qed.
Lemma lem1120935 {_26299 _26310 : Type'} (g : _26299 -> _26310) (t : list _26299) (h : _26299) : term277 _26299 _26310 g t h.
Proof. exact (@lem1120934 _26299 _26310 g t h). Qed.
Lemma lem1120936 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term277 _26299 _26310 g t h) = (term77 _26299 _26310 h g t).
Proof. exact (eq_refl (term277 _26299 _26310 g t h)). Qed.
Lemma lem1120937 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term77 _26299 _26310 h g t.
Proof. exact (EQ_MP (@lem1120936 _26299 _26310 h g t) (@lem1120935 _26299 _26310 g t h)). Qed.
Lemma lem1120938 {_26299 _26310 : Type'} (h : _26299) (g : _26299 -> _26310) (t : list _26299) (f : _26299 -> _26310) : term278 _26299 _26310 h g t f.
Proof. exact (@lem1120937 _26299 _26310 h g t f). Qed.
Lemma lem1120939 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : (term278 _26299 _26310 h g t f) = (term68 _26299 _26310 f h g t).
Proof. exact (eq_refl (term278 _26299 _26310 h g t f)). Qed.
Lemma lem1120940 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term68 _26299 _26310 f h g t.
Proof. exact (EQ_MP (@lem1120939 _26299 _26310 f h g t) (@lem1120938 _26299 _26310 h g t f)). Qed.
Lemma lem1120942 {_26299 _26310 : Type'} (f : _26299 -> _26310) (h : _26299) (g : _26299 -> _26310) (t : list _26299) : term68 _26299 _26310 f h g t.
Proof. exact (@lem1118811 _26299 _26310 f h g t (@lem1120940 _26299 _26310 f h g t)). Qed.
Lemma lem1120943 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term18 _26299 _26310 f g t) : term66 _26299 _26310 f h g t.
Proof. exact (@lem1120942 _26299 _26310 f h g t (@lem1118706 _26299 _26310 f g t h1)). Qed.
Lemma lem1120944 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term67 _26299 _26310 f h g t) (h2 : term18 _26299 _26310 f g t) : False.
Proof. exact (@lem1120943 _26299 _26310 h f g t h2 (@lem1118795 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120945 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term67 _26299 _26310 f h g t) (h2 : term18 _26299 _26310 f g t) : (term67 _26299 _26310 f h g t) = False.
Proof. exact (prop_ext (fun h3 : term67 _26299 _26310 f h g t => @lem1120944 _26299 _26310 h f g t h1 h2) (fun h3 : False => @lem1118795 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120946 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term67 _26299 _26310 f h g t) (h2 : term18 _26299 _26310 f g t) : False.
Proof. exact (EQ_MP (@lem1120945 _26299 _26310 h f g t h1 h2) (@lem1118795 _26299 _26310 f h g t h1)). Qed.
Lemma lem1120947 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term18 _26299 _26310 f g t) : term66 _26299 _26310 f h g t.
Proof. exact (fun h0 : term67 _26299 _26310 f h g t => @lem1120946 _26299 _26310 h f g t h0 h1). Qed.
Lemma lem1120948 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term18 _26299 _26310 f g t) : term64 _26299 _26310 f h g t.
Proof. exact (EQ_MP (@lem1118794 _26299 _26310 f h g t) (@lem1120947 _26299 _26310 h f g t h1)). Qed.
Lemma lem1120949 {_26299 _26310 : Type'} (h : _26299) (f : _26299 -> _26310) (g : _26299 -> _26310) (t : list _26299) (h1 : term18 _26299 _26310 f g t) : term22 _26299 _26310 f g h t.
Proof. exact (EQ_MP (@lem1118790 _26299 _26310 f g h t) (@lem1120948 _26299 _26310 h f g t h1)). Qed.
Lemma lem1120950 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) (t : list _26299) : term24 _26299 _26310 f g h t.
Proof. exact (fun h0 : term18 _26299 _26310 f g t => @lem1120949 _26299 _26310 h f g t h0). Qed.
Lemma lem1120955 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) (h : _26299) : term28 _26299 _26310 f g h.
Proof. exact (fun t : list _26299 => @lem1120950 _26299 _26310 f g h t). Qed.
Lemma lem1120960 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term32 _26299 _26310 f g.
Proof. exact (fun h : _26299 => @lem1120955 _26299 _26310 f g h). Qed.
Lemma lem1120961 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term34 _26299 _26310 f g.
Proof. exact (conj (@lem1118738 _26299 _26310 f g) (@lem1120960 _26299 _26310 f g)). Qed.
Lemma lem1120962 {_26299 _26310 : Type'} (f : _26299 -> _26310) (g : _26299 -> _26310) : term39 _26299 _26310 f g.
Proof. exact (@lem1118705 _26299 _26310 f g (@lem1120961 _26299 _26310 f g)). Qed.
Lemma lem1120967 {_26299 _26310 : Type'} (f : _26299 -> _26310) : term279 _26299 _26310 f.
Proof. exact (fun g : _26299 -> _26310 => @lem1120962 _26299 _26310 f g). Qed.
Lemma lem1120972 {_26299 _26310 : Type'} : term280 _26299 _26310.
Proof. exact (fun f : _26299 -> _26310 => @lem1120967 _26299 _26310 f). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_ASSOC_term_abbrevs.
Require Import FST_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import PAIR_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1107272_spec.
Require Import thm1107273_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem1156636 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1156637 {_27204 _27220 : Type'} (P : type1126 _27204 _27220) : term1 _27204 _27220 P.
Proof. exact (@lem1156636 (prod _27220 _27204) P). Qed.
Lemma lem1156638 {_27204 _27220 : Type'} : term2 _27204 _27220.
Proof. exact (@lem1156637 _27204 _27220 (term3 _27204 _27220)). Qed.
Lemma lem1156639 {_27204 _27220 : Type'} : (term4 _27204 _27220) = (term5 _27204 _27220).
Proof. exact (eq_refl (term4 _27204 _27220)). Qed.
Lemma lem1156640 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1156641 {_27204 _27220 : Type'} : (term6 _27204 _27220) = (term7 _27204 _27220).
Proof. exact (MK_COMB (@lem1156640) (@lem1156639 _27204 _27220)). Qed.
Lemma lem1156642 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term8 _27204 _27220 t) = (term9 _27204 _27220 t).
Proof. exact (eq_refl (term8 _27204 _27220 t)). Qed.
Lemma lem1156643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156644 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term10 _27204 _27220 t) = (term11 _27204 _27220 t).
Proof. exact (MK_COMB (@lem1156643) (@lem1156642 _27204 _27220 t)). Qed.
Lemma lem1156645 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term12 _27204 _27220 h t) = (term13 _27204 _27220 h t).
Proof. exact (eq_refl (term12 _27204 _27220 h t)). Qed.
Lemma lem1156646 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term14 _27204 _27220 h t) = (term15 _27204 _27220 h t).
Proof. exact (MK_COMB (@lem1156644 _27204 _27220 t) (@lem1156645 _27204 _27220 h t)). Qed.
Lemma lem1156647 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term16 _27204 _27220 h) = (term17 _27204 _27220 h).
Proof. exact (fun_ext (fun t : type1641 _27204 _27220 => @lem1156646 _27204 _27220 h t)). Qed.
Lemma lem1156648 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1156649 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term18 _27204 _27220 h) = (term19 _27204 _27220 h).
Proof. exact (MK_COMB (@lem1156648 _27204 _27220) (@lem1156647 _27204 _27220 h)). Qed.
Lemma lem1156650 {_27204 _27220 : Type'} : (term20 _27204 _27220) = (term21 _27204 _27220).
Proof. exact (fun_ext (fun h : prod _27220 _27204 => @lem1156649 _27204 _27220 h)). Qed.
Lemma lem1156651 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1156652 {_27204 _27220 : Type'} : (term22 _27204 _27220) = (term23 _27204 _27220).
Proof. exact (MK_COMB (@lem1156651 _27204 _27220) (@lem1156650 _27204 _27220)). Qed.
Lemma lem1156653 {_27204 _27220 : Type'} : (term24 _27204 _27220) = (term25 _27204 _27220).
Proof. exact (MK_COMB (@lem1156641 _27204 _27220) (@lem1156652 _27204 _27220)). Qed.
Lemma lem1156654 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1156655 {_27204 _27220 : Type'} : (term26 _27204 _27220) = (term27 _27204 _27220).
Proof. exact (MK_COMB (@lem1156654) (@lem1156653 _27204 _27220)). Qed.
Lemma lem1156656 {_27204 _27220 : Type'} (l : type1641 _27204 _27220) : (term8 _27204 _27220 l) = (term9 _27204 _27220 l).
Proof. exact (eq_refl (term8 _27204 _27220 l)). Qed.
Lemma lem1156657 {_27204 _27220 : Type'} : (term28 _27204 _27220) = (term3 _27204 _27220).
Proof. exact (fun_ext (fun l : type1641 _27204 _27220 => @lem1156656 _27204 _27220 l)). Qed.
Lemma lem1156658 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1156659 {_27204 _27220 : Type'} : (term29 _27204 _27220) = (term30 _27204 _27220).
Proof. exact (MK_COMB (@lem1156658 _27204 _27220) (@lem1156657 _27204 _27220)). Qed.
Lemma lem1156660 {_27204 _27220 : Type'} : (term2 _27204 _27220) = (term31 _27204 _27220).
Proof. exact (MK_COMB (@lem1156655 _27204 _27220) (@lem1156659 _27204 _27220)). Qed.
Lemma lem1156661 {_27204 _27220 : Type'} : term31 _27204 _27220.
Proof. exact (EQ_MP (@lem1156660 _27204 _27220) (@lem1156638 _27204 _27220)). Qed.
Lemma lem1156662 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term9 _27204 _27220 t.
Proof. exact (h1). Qed.
Lemma lem1156673 {A B : Type'} : term32 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1156674 {A B : Type'} (f : A -> B) : term33 A B f.
Proof. exact (@lem1156673 A B f). Qed.
Lemma lem1156675 {A B : Type'} (f : A -> B) : (term33 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term33 A B f)). Qed.
Lemma lem1156686 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1156687 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (@List.In (prod _27220 _27204) x (@nil (prod _27220 _27204))) = False.
Proof. exact (@lem1156686 (prod _27220 _27204) x). Qed.
Lemma lem1156688 {_27204 _27220 : Type'} (x : _27220) : (term34 _27204 _27220 x) = False.
Proof. exact (@lem1156687 _27204 _27220 (term35 _27204 _27220 x)). Qed.
Lemma lem1156689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1156690 {_27204 _27220 : Type'} (x : _27220) : (term36 _27204 _27220 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1156689) (@lem1156688 _27204 _27220 x)). Qed.
Lemma lem1156692 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1156675 A B f) (@lem1156674 A B f)). Qed.
Lemma lem1156693 {_27204 _27220 : Type'} (f : type1222 _27204 _27220) : (@List.map (prod _27220 _27204) _27220 f (@nil (prod _27220 _27204))) = (@nil _27220).
Proof. exact (@lem1156692 (prod _27220 _27204) _27220 f). Qed.
Lemma lem1156694 {_27204 _27220 : Type'} : (@List.map (prod _27220 _27204) _27220 (@fst _27220 _27204) (@nil (prod _27220 _27204))) = (@nil _27220).
Proof. exact (@lem1156693 _27204 _27220 (@fst _27220 _27204)). Qed.
Lemma lem1156695 {_27220 : Type'} (x : _27220) : (@List.In _27220 x) = (@List.In _27220 x).
Proof. exact (eq_refl (@List.In _27220 x)). Qed.
Lemma lem1156696 {_27204 _27220 : Type'} (x : _27220) : (term37 _27204 _27220 x) = (@List.In _27220 x (@nil _27220)).
Proof. exact (MK_COMB (@lem1156695 _27220 x) (@lem1156694 _27204 _27220)). Qed.
Lemma lem1156698 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1156699 {_27220 : Type'} (x : _27220) : (@List.In _27220 x (@nil _27220)) = False.
Proof. exact (@lem1156698 _27220 x). Qed.
Lemma lem1156700 {_27204 _27220 : Type'} (x : _27220) : (term37 _27204 _27220 x) = False.
Proof. exact (TRANS (@lem1156696 _27204 _27220 x) (@lem1156699 _27220 x)). Qed.
Lemma lem1156701 {_27204 _27220 : Type'} (x : _27220) : ((term34 _27204 _27220 x) = (term37 _27204 _27220 x)) = (False = False).
Proof. exact (MK_COMB (@lem1156690 _27204 _27220 x) (@lem1156700 _27204 _27220 x)). Qed.
Lemma lem1156703 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1156704 : (False = False) = (~ False).
Proof. exact (@lem1156703 False). Qed.
Lemma lem1156706 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1156707 : (False = False) = True.
Proof. exact (TRANS (@lem1156704) (@lem1156706)). Qed.
Lemma lem1156708 {_27204 _27220 : Type'} (x : _27220) : ((term34 _27204 _27220 x) = (term37 _27204 _27220 x)) = True.
Proof. exact (TRANS (@lem1156701 _27204 _27220 x) (@lem1156707)). Qed.
Lemma lem1156709 {_27204 _27220 : Type'} : (term38 _27204 _27220) = (term39 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1156708 _27204 _27220 x)). Qed.
Lemma lem1156710 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1156711 {_27204 _27220 : Type'} : (term5 _27204 _27220) = (term40 _27220).
Proof. exact (MK_COMB (@lem1156710 _27220) (@lem1156709 _27204 _27220)). Qed.
Lemma lem1156713 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1156714 {_27220 : Type'} (t : Prop) : (term41 _27220 t) = t.
Proof. exact (@lem1156713 _27220 t). Qed.
Lemma lem1156715 {_27220 : Type'} : (term40 _27220) = True.
Proof. exact (@lem1156714 _27220 True). Qed.
Lemma lem1156716 {_27204 _27220 : Type'} : (term5 _27204 _27220) = True.
Proof. exact (TRANS (@lem1156711 _27204 _27220) (@lem1156715 _27220)). Qed.
Lemma lem1156717 {_27204 _27220 : Type'} : True = (term5 _27204 _27220).
Proof. exact (SYM (@lem1156716 _27204 _27220)). Qed.
Lemma lem1156718 {_27204 _27220 : Type'} : term5 _27204 _27220.
Proof. exact (EQ_MP (@lem1156717 _27204 _27220) (@lem0)). Qed.
Lemma lem1156719 {A B : Type'} : term42 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1156720 {A B : Type'} (f : A -> B) : term43 A B f.
Proof. exact (@lem1156719 A B f). Qed.
Lemma lem1156721 {A B : Type'} (f : A -> B) : (term43 A B f) = (term44 A B f).
Proof. exact (eq_refl (term43 A B f)). Qed.
Lemma lem1156722 {A B : Type'} (f : A -> B) : term44 A B f.
Proof. exact (EQ_MP (@lem1156721 A B f) (@lem1156720 A B f)). Qed.
Lemma lem1156723 {A B : Type'} (f : A -> B) (h : A) : term45 A B f h.
Proof. exact (@lem1156722 A B f h). Qed.
Lemma lem1156724 {A B : Type'} (h : A) (f : A -> B) : (term45 A B f h) = (term46 A B h f).
Proof. exact (eq_refl (term45 A B f h)). Qed.
Lemma lem1156725 {A B : Type'} (h : A) (f : A -> B) : term46 A B h f.
Proof. exact (EQ_MP (@lem1156724 A B h f) (@lem1156723 A B f h)). Qed.
Lemma lem1156726 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term47 A B h f t.
Proof. exact (@lem1156725 A B h f t). Qed.
Lemma lem1156727 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term47 A B h f t) = ((term48 A B f h t) = (term49 A B h f t)).
Proof. exact (eq_refl (term47 A B h f t)). Qed.
Lemma lem1156745 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term50 _25376 x h t) = (term51 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1156746 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : prod _27220 _27204) (t : type1641 _27204 _27220) : (term52 _27204 _27220 x h t) = (term53 _27204 _27220 h x t).
Proof. exact (@lem1156745 (prod _27220 _27204) h x t). Qed.
Lemma lem1156747 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term54 _27204 _27220 x h t) = (term55 _27204 _27220 x h t).
Proof. exact (@lem1156746 _27204 _27220 h (term56 _27204 _27220 x h t) t). Qed.
Lemma lem1156753 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : (term57 _25617 _25623 a h t) = (term58 _25617 _25623 h a t).
Proof. exact (EQ_MP (@lem1107273 _25617 _25623 h a t) (@lem1107272 _25617 _25623 h a t)). Qed.
Lemma lem1156754 {_27204 _27220 : Type'} (h : prod _27220 _27204) (a : _27220) (t : type1641 _27204 _27220) : (term57 _27204 _27220 a h t) = (term58 _27204 _27220 h a t).
Proof. exact (@lem1156753 _27204 _27220 h a t). Qed.
Lemma lem1156755 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term57 _27204 _27220 x h t) = (term58 _27204 _27220 h x t).
Proof. exact (@lem1156754 _27204 _27220 h x t). Qed.
Lemma lem1156760 {_27204 _27220 : Type'} (x : _27220) : (@pair _27220 _27204 x) = (@pair _27220 _27204 x).
Proof. exact (eq_refl (@pair _27220 _27204 x)). Qed.
Lemma lem1156761 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term56 _27204 _27220 x h t) = (term59 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156760 _27204 _27220 x) (@lem1156755 _27204 _27220 h x t)). Qed.
Lemma lem1156762 {_27204 _27220 : Type'} : (@eq (prod _27220 _27204)) = (@eq (prod _27220 _27204)).
Proof. exact (eq_refl (@eq (prod _27220 _27204))). Qed.
Lemma lem1156763 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term60 _27204 _27220 x h t) = (term61 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156762 _27204 _27220) (@lem1156761 _27204 _27220 h x t)). Qed.
Lemma lem1156764 {_27204 _27220 : Type'} (h : prod _27220 _27204) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1156765 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) : ((term56 _27204 _27220 x h t) = h) = ((term59 _27204 _27220 h x t) = h).
Proof. exact (MK_COMB (@lem1156763 _27204 _27220 h x t) (@lem1156764 _27204 _27220 h)). Qed.
Lemma lem1156768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1156769 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) : (term62 _27204 _27220 x t h) = (term63 _27204 _27220 x t h).
Proof. exact (MK_COMB (@lem1156768) (@lem1156765 _27204 _27220 x t h)). Qed.
Lemma lem1156771 {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : type1641 _25617 _25623) : (term57 _25617 _25623 a h t) = (term58 _25617 _25623 h a t).
Proof. exact (EQ_MP (@lem1107273 _25617 _25623 h a t) (@lem1107272 _25617 _25623 h a t)). Qed.
Lemma lem1156772 {_27204 _27220 : Type'} (h : prod _27220 _27204) (a : _27220) (t : type1641 _27204 _27220) : (term57 _27204 _27220 a h t) = (term58 _27204 _27220 h a t).
Proof. exact (@lem1156771 _27204 _27220 h a t). Qed.
Lemma lem1156773 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term57 _27204 _27220 x h t) = (term58 _27204 _27220 h x t).
Proof. exact (@lem1156772 _27204 _27220 h x t). Qed.
Lemma lem1156778 {_27204 _27220 : Type'} (x : _27220) : (@pair _27220 _27204 x) = (@pair _27220 _27204 x).
Proof. exact (eq_refl (@pair _27220 _27204 x)). Qed.
Lemma lem1156779 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term56 _27204 _27220 x h t) = (term59 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156778 _27204 _27220 x) (@lem1156773 _27204 _27220 h x t)). Qed.
Lemma lem1156780 {_27204 _27220 : Type'} : (@List.In (prod _27220 _27204)) = (@List.In (prod _27220 _27204)).
Proof. exact (eq_refl (@List.In (prod _27220 _27204))). Qed.
Lemma lem1156781 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term64 _27204 _27220 x h t) = (term65 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156780 _27204 _27220) (@lem1156779 _27204 _27220 h x t)). Qed.
Lemma lem1156782 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1156783 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term66 _27204 _27220 x h t) = (term67 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156781 _27204 _27220 h x t) (@lem1156782 _27204 _27220 t)). Qed.
Lemma lem1156784 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term55 _27204 _27220 x h t) = (term68 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156769 _27204 _27220 x t h) (@lem1156783 _27204 _27220 h x t)). Qed.
Lemma lem1156787 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term54 _27204 _27220 x h t) = (term68 _27204 _27220 h x t).
Proof. exact (TRANS (@lem1156747 _27204 _27220 x h t) (@lem1156784 _27204 _27220 h x t)). Qed.
Lemma lem1156788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1156789 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term69 _27204 _27220 x h t) = (term70 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156788) (@lem1156787 _27204 _27220 h x t)). Qed.
Lemma lem1156791 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term48 A B f h t) = (term49 A B h f t).
Proof. exact (EQ_MP (@lem1156727 A B h f t) (@lem1156726 A B h f t)). Qed.
Lemma lem1156792 {_27204 _27220 : Type'} (h : prod _27220 _27204) (f : type1222 _27204 _27220) (t : type1641 _27204 _27220) : (term71 _27204 _27220 f h t) = (term72 _27204 _27220 h f t).
Proof. exact (@lem1156791 (prod _27220 _27204) _27220 h f t). Qed.
Lemma lem1156793 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term73 _27204 _27220 h t) = (term74 _27204 _27220 h t).
Proof. exact (@lem1156792 _27204 _27220 h (@fst _27220 _27204) t). Qed.
Lemma lem1156794 {_27220 : Type'} (x : _27220) : (@List.In _27220 x) = (@List.In _27220 x).
Proof. exact (eq_refl (@List.In _27220 x)). Qed.
Lemma lem1156795 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term75 _27204 _27220 x h t) = (term76 _27204 _27220 x h t).
Proof. exact (MK_COMB (@lem1156794 _27220 x) (@lem1156793 _27204 _27220 h t)). Qed.
Lemma lem1156797 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term50 _25376 x h t) = (term51 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1156798 {_27220 : Type'} (h : _27220) (x : _27220) (t : list _27220) : (term50 _27220 x h t) = (term51 _27220 h x t).
Proof. exact (@lem1156797 _27220 h x t). Qed.
Lemma lem1156799 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term76 _27204 _27220 x h t) = (term77 _27204 _27220 h x t).
Proof. exact (@lem1156798 _27220 (@fst _27220 _27204 h) x (@List.map (prod _27220 _27204) _27220 (@fst _27220 _27204) t)). Qed.
Lemma lem1156804 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term75 _27204 _27220 x h t) = (term77 _27204 _27220 h x t).
Proof. exact (TRANS (@lem1156795 _27204 _27220 x h t) (@lem1156799 _27204 _27220 h x t)). Qed.
Lemma lem1156805 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : ((term54 _27204 _27220 x h t) = (term75 _27204 _27220 x h t)) = ((term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (MK_COMB (@lem1156789 _27204 _27220 h x t) (@lem1156804 _27204 _27220 h x t)). Qed.
Lemma lem1156808 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term78 _27204 _27220 h t) = (term79 _27204 _27220 h t).
Proof. exact (fun_ext (fun x : _27220 => @lem1156805 _27204 _27220 h x t)). Qed.
Lemma lem1156809 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1156810 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term13 _27204 _27220 h t) = (term80 _27204 _27220 h t).
Proof. exact (MK_COMB (@lem1156809 _27220) (@lem1156808 _27204 _27220 h t)). Qed.
Lemma lem1156815 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term80 _27204 _27220 h t) = (term13 _27204 _27220 h t).
Proof. exact (SYM (@lem1156810 _27204 _27220 h t)). Qed.
Lemma lem1156816 {_27204 : Type'} (_474 : _27204) (_475 : Prop) (_476 : _27204 -> Prop) (_477 : _27204) : (term81 _27204 _476 _475 _474 _477) = (term82 _27204 _474 _475 _476 _477).
Proof. exact (@lem13473 _27204 _474 _475 _476 _477). Qed.
Lemma lem1156817 {_27204 _27220 : Type'} (_474 : _27204) (_475 : Prop) (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (_477 : _27204) : (term83 _27204 _27220 h x t _475 _474 _477) = (term84 _27204 _27220 _474 _475 h x t _477).
Proof. exact (@lem1156816 _27204 _474 _475 (term85 _27204 _27220 h x t) _477). Qed.
Lemma lem1156818 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term86 _27204 _27220 h x t) = (term87 _27204 _27220 h x t).
Proof. exact (@lem1156817 _27204 _27220 (@snd _27220 _27204 h) ((@fst _27220 _27204 h) = x) h x t (@ASSOC _27204 _27220 x t)). Qed.
Lemma lem1156819 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term88 _27204 _27220 h x t) = ((term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (eq_refl (term88 _27204 _27220 h x t)). Qed.
Lemma lem1156820 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term90 _27204 _27220 h x) = (term90 _27204 _27220 h x).
Proof. exact (eq_refl (term90 _27204 _27220 h x)). Qed.
Lemma lem1156821 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term91 _27204 _27220 h x t) = (term92 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156820 _27204 _27220 h x) (@lem1156819 _27204 _27220 h x t)). Qed.
Lemma lem1156822 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term93 _27204 _27220 x t h) = ((term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t)).
Proof. exact (eq_refl (term93 _27204 _27220 x t h)). Qed.
Lemma lem1156823 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term95 _27204 _27220 h x) = (term95 _27204 _27220 h x).
Proof. exact (eq_refl (term95 _27204 _27220 h x)). Qed.
Lemma lem1156824 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term96 _27204 _27220 x t h) = (term97 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156823 _27204 _27220 h x) (@lem1156822 _27204 _27220 h x t)). Qed.
Lemma lem1156825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1156826 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term98 _27204 _27220 x t h) = (term99 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156825) (@lem1156824 _27204 _27220 h x t)). Qed.
Lemma lem1156827 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term87 _27204 _27220 h x t) = (term100 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156826 _27204 _27220 h x t) (@lem1156821 _27204 _27220 h x t)). Qed.
Lemma lem1156828 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term86 _27204 _27220 h x t) = ((term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (eq_refl (term86 _27204 _27220 h x t)). Qed.
Lemma lem1156829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1156830 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term101 _27204 _27220 h x t) = (term102 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156829) (@lem1156828 _27204 _27220 h x t)). Qed.
Lemma lem1156831 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : ((term86 _27204 _27220 h x t) = (term87 _27204 _27220 h x t)) = (((term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)) = (term100 _27204 _27220 h x t)).
Proof. exact (MK_COMB (@lem1156830 _27204 _27220 h x t) (@lem1156827 _27204 _27220 h x t)). Qed.
Lemma lem1156832 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : ((term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)) = (term100 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1156831 _27204 _27220 h x t) (@lem1156818 _27204 _27220 h x t)). Qed.
Lemma lem1156833 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term100 _27204 _27220 h x t) = ((term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (SYM (@lem1156832 _27204 _27220 h x t)). Qed.
Lemma lem1156834 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (@fst _27220 _27204 h) = x.
Proof. exact (h1). Qed.
Lemma lem1156851 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : term103 _27204 _27220 h x.
Proof. exact (h1). Qed.
Lemma lem1156882 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (@fst _27220 _27204 h) = x.
Proof. exact (h1). Qed.
Lemma lem1156883 {_27220 : Type'} (x : _27220) : (@eq _27220 x) = (@eq _27220 x).
Proof. exact (eq_refl (@eq _27220 x)). Qed.
Lemma lem1156884 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (x = (@fst _27220 _27204 h)) = (x = x).
Proof. exact (MK_COMB (@lem1156883 _27220 x) (@lem1156882 _27204 _27220 h x h1)). Qed.
Lemma lem1156886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1156887 {_27220 : Type'} (x : _27220) : (x = x) = True.
Proof. exact (@lem1156886 _27220 x). Qed.
Lemma lem1156888 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (x = (@fst _27220 _27204 h)) = True.
Proof. exact (TRANS (@lem1156884 _27204 _27220 h x h1) (@lem1156887 _27220 x)). Qed.
Lemma lem1156889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1156890 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term104 _27204 _27220 x h) = (or True).
Proof. exact (MK_COMB (@lem1156889) (@lem1156888 _27204 _27220 h x h1)). Qed.
Lemma lem1156891 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term105 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (eq_refl (term105 _27204 _27220 x t)). Qed.
Lemma lem1156892 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term77 _27204 _27220 h x t) = (term106 _27204 _27220 x t).
Proof. exact (MK_COMB (@lem1156890 _27204 _27220 h x h1) (@lem1156891 _27204 _27220 x t)). Qed.
Lemma lem1156894 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1156895 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term106 _27204 _27220 x t) = True.
Proof. exact (@lem1156894 (term105 _27204 _27220 x t)). Qed.
Lemma lem1156896 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term77 _27204 _27220 h x t) = True.
Proof. exact (TRANS (@lem1156892 _27204 _27220 t h x h1) (@lem1156895 _27204 _27220 x t)). Qed.
Lemma lem1156897 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term107 _27204 _27220 x h t) = (term107 _27204 _27220 x h t).
Proof. exact (eq_refl (term107 _27204 _27220 x h t)). Qed.
Lemma lem1156898 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : ((term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t)) = ((term94 _27204 _27220 x h t) = True).
Proof. exact (MK_COMB (@lem1156897 _27204 _27220 x h t) (@lem1156896 _27204 _27220 t h x h1)). Qed.
Lemma lem1156900 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1156901 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : ((term94 _27204 _27220 x h t) = True) = (term94 _27204 _27220 x h t).
Proof. exact (@lem1156900 (term94 _27204 _27220 x h t)). Qed.
Lemma lem1156906 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : ((term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t)) = (term94 _27204 _27220 x h t).
Proof. exact (TRANS (@lem1156898 _27204 _27220 t h x h1) (@lem1156901 _27204 _27220 x h t)). Qed.
Lemma lem1156907 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term94 _27204 _27220 x h t) = ((term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t)).
Proof. exact (SYM (@lem1156906 _27204 _27220 t h x h1)). Qed.
Lemma lem1156908 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term108 _27204 _27220 t x.
Proof. exact (@lem1156662 _27204 _27220 t h1 x). Qed.
Lemma lem1156909 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term108 _27204 _27220 t x) = ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t)).
Proof. exact (eq_refl (term108 _27204 _27220 t x)). Qed.
Lemma lem1156914 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (@fst _27220 _27204 h) = x.
Proof. exact (h1). Qed.
Lemma lem1156915 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : x = (@fst _27220 _27204 h).
Proof. exact (SYM (@lem1156914 _27204 _27220 h x h1)). Qed.
Lemma lem1156916 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (h1 : x = (@fst _27220 _27204 h)) : x = (@fst _27220 _27204 h).
Proof. exact (h1). Qed.
Lemma lem1156917 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (h1 : x = (@fst _27220 _27204 h)) : (@fst _27220 _27204 h) = x.
Proof. exact (SYM (@lem1156916 _27204 _27220 x h h1)). Qed.
Lemma lem1156918 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : ((@fst _27220 _27204 h) = x) = (x = (@fst _27220 _27204 h)).
Proof. exact (prop_ext (fun h1 : (@fst _27220 _27204 h) = x => @lem1156915 _27204 _27220 h x h1) (fun h1 : x = (@fst _27220 _27204 h) => @lem1156917 _27204 _27220 x h h1)). Qed.
Lemma lem1156919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1156920 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : (term103 _27204 _27220 h x) = (term110 _27204 _27220 x h).
Proof. exact (MK_COMB (@lem1156919) (@lem1156918 _27204 _27220 x h)). Qed.
Lemma lem1156921 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : term110 _27204 _27220 x h.
Proof. exact (EQ_MP (@lem1156920 _27204 _27220 x h) (@lem1156851 _27204 _27220 h x h1)). Qed.
Lemma lem1156922 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : term111 _27204 _27220 x h.
Proof. exact (@lem82 (x = (@fst _27220 _27204 h))). Qed.
Lemma lem1156931 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : (term109 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (EQ_MP (@lem1156909 _27204 _27220 x t) (@lem1156908 _27204 _27220 x t h1)). Qed.
Lemma lem1156932 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : (term109 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (@lem1156931 _27204 _27220 x t h1). Qed.
Lemma lem1156933 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) : (term112 _27204 _27220 x t h) = (term112 _27204 _27220 x t h).
Proof. exact (eq_refl (term112 _27204 _27220 x t h)). Qed.
Lemma lem1156934 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : (term89 _27204 _27220 h x t) = (term113 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156933 _27204 _27220 x t h) (@lem1156932 _27204 _27220 x t h1)). Qed.
Lemma lem1156937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1156938 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : (term114 _27204 _27220 h x t) = (term115 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1156937) (@lem1156934 _27204 _27220 h x t h1)). Qed.
Lemma lem1156942 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : (x = (@fst _27220 _27204 h)) = False.
Proof. exact (@lem1156922 _27204 _27220 x h (@lem1156921 _27204 _27220 h x h1)). Qed.
Lemma lem1156943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1156944 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : (term104 _27204 _27220 x h) = (or False).
Proof. exact (MK_COMB (@lem1156943) (@lem1156942 _27204 _27220 h x h1)). Qed.
Lemma lem1156945 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term105 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (eq_refl (term105 _27204 _27220 x t)). Qed.
Lemma lem1156946 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : (term77 _27204 _27220 h x t) = (term116 _27204 _27220 x t).
Proof. exact (MK_COMB (@lem1156944 _27204 _27220 h x h1) (@lem1156945 _27204 _27220 x t)). Qed.
Lemma lem1156948 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1156949 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term116 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (@lem1156948 (term105 _27204 _27220 x t)). Qed.
Lemma lem1156950 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : (term77 _27204 _27220 h x t) = (term105 _27204 _27220 x t).
Proof. exact (TRANS (@lem1156946 _27204 _27220 t h x h1) (@lem1156949 _27204 _27220 x t)). Qed.
Lemma lem1156951 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : ((term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)) = ((term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t)).
Proof. exact (MK_COMB (@lem1156938 _27204 _27220 h x t h1) (@lem1156950 _27204 _27220 t h x h2)). Qed.
Lemma lem1156954 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : ((term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t)) = ((term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (SYM (@lem1156951 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1156956 (p : Prop) : p = (term117 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1156957 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term94 _27204 _27220 x h t) = (term118 _27204 _27220 x h t).
Proof. exact (@lem1156956 (term94 _27204 _27220 x h t)). Qed.
Lemma lem1156958 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term118 _27204 _27220 x h t) = (term94 _27204 _27220 x h t).
Proof. exact (SYM (@lem1156957 _27204 _27220 x h t)). Qed.
Lemma lem1156959 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term119 _27204 _27220 x h t) : term119 _27204 _27220 x h t.
Proof. exact (h1). Qed.
Lemma lem1156960 {_27204 _27220 : Type'} : term120 _27204 _27220.
Proof. exact (@lem48081 _27220 _27204). Qed.
Lemma lem1156964 {_27220 B : Type'} : term121 _27220 B.
Proof. exact (@lem47827 _27220 B). Qed.
Lemma lem1156965 {_27204 _27220 B : Type'} : term122 _27204 _27220 B.
Proof. exact (@lem47827 (prod _27220 _27204) B). Qed.
Lemma lem1156966 {_27204 _27220 : Type'} : term123 _27204 _27220.
Proof. exact (@lem47827 _27220 _27204). Qed.
Lemma lem1156970 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term124 _27204 _27220 B x h t) : term124 _27204 _27220 B x h t.
Proof. exact (h1). Qed.
Lemma lem1156971 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term125 _27204 _27220 B x h t.
Proof. exact (fun h0 : term124 _27204 _27220 B x h t => @lem1156970 _27204 _27220 B x h t h0). Qed.
Lemma lem1156972 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term125 _27204 _27220 B x h t) : term125 _27204 _27220 B x h t.
Proof. exact (h1). Qed.
Lemma lem1156973 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term124 _27204 _27220 B x h t) : term124 _27204 _27220 B x h t.
Proof. exact (h1). Qed.
Lemma lem1156974 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term124 _27204 _27220 B x h t) (h2 : term125 _27204 _27220 B x h t) : term124 _27204 _27220 B x h t.
Proof. exact (@lem1156972 _27204 _27220 B x h t h2 (@lem1156973 _27204 _27220 B x h t h1)). Qed.
Lemma lem1156975 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term124 _27204 _27220 B x h t) : term126 _27204 _27220 B x h t.
Proof. exact (fun h0 : term125 _27204 _27220 B x h t => @lem1156974 _27204 _27220 B x h t h1 h0). Qed.
Lemma lem1156976 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term125 _27204 _27220 B x h t) : term125 _27204 _27220 B x h t.
Proof. exact (h1). Qed.
Lemma lem1156977 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term124 _27204 _27220 B x h t) (h2 : term125 _27204 _27220 B x h t) : term124 _27204 _27220 B x h t.
Proof. exact (@lem1156975 _27204 _27220 B x h t h1 (@lem1156976 _27204 _27220 B x h t h2)). Qed.
Lemma lem1156978 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term125 _27204 _27220 B x h t) : term125 _27204 _27220 B x h t.
Proof. exact (fun h0 : term124 _27204 _27220 B x h t => @lem1156977 _27204 _27220 B x h t h0 h1). Qed.
Lemma lem1156979 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term127 _27204 _27220 B x h t.
Proof. exact (fun h0 : term125 _27204 _27220 B x h t => @lem1156978 _27204 _27220 B x h t h0). Qed.
Lemma lem1156982 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term125 _27204 _27220 B x h t.
Proof. exact (@lem1156979 _27204 _27220 B x h t (@lem1156971 _27204 _27220 B x h t)). Qed.
Lemma lem1156983 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term125 _27204 _27220 B x h t.
Proof. exact (@lem1156982 _27204 _27220 B x h t). Qed.
Lemma lem1157039 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1157040 {_27204 _27220 : Type'} : (term128 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (@lem1157039 (term120 _27204 _27220)). Qed.
Lemma lem1157045 {_27204 _27220 B : Type'} : (term130 _27204 _27220 B) = (term130 _27204 _27220 B).
Proof. exact (eq_refl (term130 _27204 _27220 B)). Qed.
Lemma lem1157046 {_27204 _27220 B : Type'} : (term131 _27204 _27220 B) = (term132 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157045 _27204 _27220 B) (@lem1157040 _27204 _27220)). Qed.
Lemma lem1157049 {_27220 B : Type'} : (term133 _27220 B) = (term133 _27220 B).
Proof. exact (eq_refl (term133 _27220 B)). Qed.
Lemma lem1157050 {_27204 _27220 B : Type'} : (term134 _27204 _27220 B) = (term135 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157049 _27220 B) (@lem1157046 _27204 _27220 B)). Qed.
Lemma lem1157053 {_27204 _27220 : Type'} : (term136 _27204 _27220) = (term136 _27204 _27220).
Proof. exact (eq_refl (term136 _27204 _27220)). Qed.
Lemma lem1157054 {_27204 _27220 B : Type'} : (term137 _27204 _27220 B) = (term138 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157053 _27204 _27220) (@lem1157050 _27204 _27220 B)). Qed.
Lemma lem1157057 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term139 _27204 _27220 x h t) = (term139 _27204 _27220 x h t).
Proof. exact (eq_refl (term139 _27204 _27220 x h t)). Qed.
Lemma lem1157058 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term140 _27204 _27220 B x h t) = (term141 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157057 _27204 _27220 x h t) (@lem1157054 _27204 _27220 B)). Qed.
Lemma lem1157061 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term95 _27204 _27220 h x) = (term95 _27204 _27220 h x).
Proof. exact (eq_refl (term95 _27204 _27220 h x)). Qed.
Lemma lem1157062 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term142 _27204 _27220 B x h t) = (term143 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157061 _27204 _27220 h x) (@lem1157058 _27204 _27220 B x h t)). Qed.
Lemma lem1157065 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term11 _27204 _27220 t) = (term11 _27204 _27220 t).
Proof. exact (eq_refl (term11 _27204 _27220 t)). Qed.
Lemma lem1157066 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term124 _27204 _27220 B x h t) = (term144 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157065 _27204 _27220 t) (@lem1157062 _27204 _27220 B x h t)). Qed.
Lemma lem1157069 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term145 _27204 _27220 B h t) = (term146 _27204 _27220 B h t).
Proof. exact (fun_ext (fun x : _27220 => @lem1157066 _27204 _27220 B x h t)). Qed.
Lemma lem1157070 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1157071 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term147 _27204 _27220 B h t) = (term148 _27204 _27220 B h t).
Proof. exact (MK_COMB (@lem1157070 _27220) (@lem1157069 _27204 _27220 B h t)). Qed.
Lemma lem1157076 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term149 _27204 _27220 B t) = (term150 _27204 _27220 B t).
Proof. exact (fun_ext (fun h : prod _27220 _27204 => @lem1157071 _27204 _27220 B h t)). Qed.
Lemma lem1157077 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157078 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term151 _27204 _27220 B t) = (term152 _27204 _27220 B t).
Proof. exact (MK_COMB (@lem1157077 _27204 _27220) (@lem1157076 _27204 _27220 B t)). Qed.
Lemma lem1157083 {_27204 _27220 B : Type'} : (term153 _27204 _27220 B) = (term154 _27204 _27220 B).
Proof. exact (fun_ext (fun t : type1641 _27204 _27220 => @lem1157078 _27204 _27220 B t)). Qed.
Lemma lem1157084 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1157093 {_27204 _27220 B : Type'} : (term155 _27204 _27220 B) = (term156 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157084 _27204 _27220) (@lem1157083 _27204 _27220 B)). Qed.
Lemma lem1157094 {_27204 _27220 : Type'} (x : prod _27220 _27204) : ((term157 _27204 _27220 x) = x) = ((term157 _27204 _27220 x) = x).
Proof. exact (eq_refl ((term157 _27204 _27220 x) = x)). Qed.
Lemma lem1157095 {_27204 _27220 : Type'} : (term158 _27204 _27220) = (term158 _27204 _27220).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1157094 _27204 _27220 x)). Qed.
Lemma lem1157096 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157097 {_27204 _27220 : Type'} : (term120 _27204 _27220) = (term120 _27204 _27220).
Proof. exact (MK_COMB (@lem1157096 _27204 _27220) (@lem1157095 _27204 _27220)). Qed.
Lemma lem1157098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1157099 {_27204 _27220 : Type'} : (term129 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (MK_COMB (@lem1157098) (@lem1157097 _27204 _27220)). Qed.
Lemma lem1157100 {_27204 _27220 B : Type'} (y : B) (x : prod _27220 _27204) : ((term159 _27204 _27220 B x y) = x) = ((term159 _27204 _27220 B x y) = x).
Proof. exact (eq_refl ((term159 _27204 _27220 B x y) = x)). Qed.
Lemma lem1157101 {_27204 _27220 B : Type'} (x : prod _27220 _27204) : (term160 _27204 _27220 B x) = (term160 _27204 _27220 B x).
Proof. exact (fun_ext (fun y : B => @lem1157100 _27204 _27220 B y x)). Qed.
Lemma lem1157102 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1157103 {_27204 _27220 B : Type'} (x : prod _27220 _27204) : (term161 _27204 _27220 B x) = (term161 _27204 _27220 B x).
Proof. exact (MK_COMB (@lem1157102 B) (@lem1157101 _27204 _27220 B x)). Qed.
Lemma lem1157104 {_27204 _27220 B : Type'} : (term162 _27204 _27220 B) = (term162 _27204 _27220 B).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1157103 _27204 _27220 B x)). Qed.
Lemma lem1157105 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157106 {_27204 _27220 B : Type'} : (term122 _27204 _27220 B) = (term122 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157105 _27204 _27220) (@lem1157104 _27204 _27220 B)). Qed.
Lemma lem1157107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1157108 {_27204 _27220 B : Type'} : (term130 _27204 _27220 B) = (term130 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157107) (@lem1157106 _27204 _27220 B)). Qed.
Lemma lem1157109 {_27204 _27220 B : Type'} : (term132 _27204 _27220 B) = (term132 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157108 _27204 _27220 B) (@lem1157099 _27204 _27220)). Qed.
Lemma lem1157110 {_27220 B : Type'} (y : B) (x : _27220) : ((term163 _27220 B x y) = x) = ((term163 _27220 B x y) = x).
Proof. exact (eq_refl ((term163 _27220 B x y) = x)). Qed.
Lemma lem1157111 {_27220 B : Type'} (x : _27220) : (term164 _27220 B x) = (term164 _27220 B x).
Proof. exact (fun_ext (fun y : B => @lem1157110 _27220 B y x)). Qed.
Lemma lem1157112 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1157113 {_27220 B : Type'} (x : _27220) : (term165 _27220 B x) = (term165 _27220 B x).
Proof. exact (MK_COMB (@lem1157112 B) (@lem1157111 _27220 B x)). Qed.
Lemma lem1157114 {_27220 B : Type'} : (term166 _27220 B) = (term166 _27220 B).
Proof. exact (fun_ext (fun x : _27220 => @lem1157113 _27220 B x)). Qed.
Lemma lem1157115 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1157116 {_27220 B : Type'} : (term121 _27220 B) = (term121 _27220 B).
Proof. exact (MK_COMB (@lem1157115 _27220) (@lem1157114 _27220 B)). Qed.
Lemma lem1157117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1157118 {_27220 B : Type'} : (term133 _27220 B) = (term133 _27220 B).
Proof. exact (MK_COMB (@lem1157117) (@lem1157116 _27220 B)). Qed.
Lemma lem1157119 {_27204 _27220 B : Type'} : (term135 _27204 _27220 B) = (term135 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157118 _27220 B) (@lem1157109 _27204 _27220 B)). Qed.
Lemma lem1157120 {_27204 _27220 : Type'} (y : _27204) (x : _27220) : ((term167 _27204 _27220 x y) = x) = ((term167 _27204 _27220 x y) = x).
Proof. exact (eq_refl ((term167 _27204 _27220 x y) = x)). Qed.
Lemma lem1157121 {_27204 _27220 : Type'} (x : _27220) : (term168 _27204 _27220 x) = (term168 _27204 _27220 x).
Proof. exact (fun_ext (fun y : _27204 => @lem1157120 _27204 _27220 y x)). Qed.
Lemma lem1157122 {_27204 : Type'} : (@all _27204) = (@all _27204).
Proof. exact (eq_refl (@all _27204)). Qed.
Lemma lem1157123 {_27204 _27220 : Type'} (x : _27220) : (term169 _27204 _27220 x) = (term169 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1157122 _27204) (@lem1157121 _27204 _27220 x)). Qed.
Lemma lem1157124 {_27204 _27220 : Type'} : (term170 _27204 _27220) = (term170 _27204 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1157123 _27204 _27220 x)). Qed.
Lemma lem1157125 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1157126 {_27204 _27220 : Type'} : (term123 _27204 _27220) = (term123 _27204 _27220).
Proof. exact (MK_COMB (@lem1157125 _27220) (@lem1157124 _27204 _27220)). Qed.
Lemma lem1157127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1157128 {_27204 _27220 : Type'} : (term136 _27204 _27220) = (term136 _27204 _27220).
Proof. exact (MK_COMB (@lem1157127) (@lem1157126 _27204 _27220)). Qed.
Lemma lem1157129 {_27204 _27220 B : Type'} : (term138 _27204 _27220 B) = (term138 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157128 _27204 _27220) (@lem1157119 _27204 _27220 B)). Qed.
Lemma lem1157138 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term139 _27204 _27220 x h t) = (term139 _27204 _27220 x h t).
Proof. exact (eq_refl (term139 _27204 _27220 x h t)). Qed.
Lemma lem1157139 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term141 _27204 _27220 B x h t) = (term141 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157138 _27204 _27220 x h t) (@lem1157129 _27204 _27220 B)). Qed.
Lemma lem1157142 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term95 _27204 _27220 h x) = (term95 _27204 _27220 h x).
Proof. exact (eq_refl (term95 _27204 _27220 h x)). Qed.
Lemma lem1157143 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term143 _27204 _27220 B x h t) = (term143 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157142 _27204 _27220 h x) (@lem1157139 _27204 _27220 B x h t)). Qed.
Lemma lem1157148 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t)) = ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t)).
Proof. exact (eq_refl ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t))). Qed.
Lemma lem1157149 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term171 _27204 _27220 t) = (term171 _27204 _27220 t).
Proof. exact (fun_ext (fun x : _27220 => @lem1157148 _27204 _27220 x t)). Qed.
Lemma lem1157150 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1157151 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term9 _27204 _27220 t) = (term9 _27204 _27220 t).
Proof. exact (MK_COMB (@lem1157150 _27220) (@lem1157149 _27204 _27220 t)). Qed.
Lemma lem1157152 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1157153 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term11 _27204 _27220 t) = (term11 _27204 _27220 t).
Proof. exact (MK_COMB (@lem1157152) (@lem1157151 _27204 _27220 t)). Qed.
Lemma lem1157154 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term144 _27204 _27220 B x h t) = (term144 _27204 _27220 B x h t).
Proof. exact (MK_COMB (@lem1157153 _27204 _27220 t) (@lem1157143 _27204 _27220 B x h t)). Qed.
Lemma lem1157155 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term146 _27204 _27220 B h t) = (term146 _27204 _27220 B h t).
Proof. exact (fun_ext (fun x : _27220 => @lem1157154 _27204 _27220 B x h t)). Qed.
Lemma lem1157156 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1157157 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term148 _27204 _27220 B h t) = (term148 _27204 _27220 B h t).
Proof. exact (MK_COMB (@lem1157156 _27220) (@lem1157155 _27204 _27220 B h t)). Qed.
Lemma lem1157158 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term150 _27204 _27220 B t) = (term150 _27204 _27220 B t).
Proof. exact (fun_ext (fun h : prod _27220 _27204 => @lem1157157 _27204 _27220 B h t)). Qed.
Lemma lem1157159 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157160 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term152 _27204 _27220 B t) = (term152 _27204 _27220 B t).
Proof. exact (MK_COMB (@lem1157159 _27204 _27220) (@lem1157158 _27204 _27220 B t)). Qed.
Lemma lem1157161 {_27204 _27220 B : Type'} : (term154 _27204 _27220 B) = (term154 _27204 _27220 B).
Proof. exact (fun_ext (fun t : type1641 _27204 _27220 => @lem1157160 _27204 _27220 B t)). Qed.
Lemma lem1157162 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1157163 {_27204 _27220 B : Type'} : (term156 _27204 _27220 B) = (term156 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1157162 _27204 _27220) (@lem1157161 _27204 _27220 B)). Qed.
Lemma lem1157246 {_27204 _27220 B : Type'} : (term155 _27204 _27220 B) = (term156 _27204 _27220 B).
Proof. exact (TRANS (@lem1157093 _27204 _27220 B) (@lem1157163 _27204 _27220 B)). Qed.
Lemma lem1157247 {_27204 _27220 B : Type'} : (term156 _27204 _27220 B) = (term155 _27204 _27220 B).
Proof. exact (SYM (@lem1157246 _27204 _27220 B)). Qed.
Lemma lem1157250 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term119 _27204 _27220 x h t) : term119 _27204 _27220 x h t.
Proof. exact (h1). Qed.
Lemma lem1157254 {_27204 _27220 : Type'} (h1 : term120 _27204 _27220) : term120 _27204 _27220.
Proof. exact (h1). Qed.
Lemma lem1157405 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (@fst _27220 _27204 h) = x.
Proof. exact (h1). Qed.
Lemma lem1157416 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term119 _27204 _27220 x h t) = (term172 _27204 _27220 x h t).
Proof. exact (@lem17160 ((term173 _27204 _27220 x h) = h) (term174 _27204 _27220 x h t)). Qed.
Lemma lem1157478 {_27204 _27220 : Type'} (x : prod _27220 _27204) : ((term157 _27204 _27220 x) = x) = ((term157 _27204 _27220 x) = x).
Proof. exact (eq_refl ((term157 _27204 _27220 x) = x)). Qed.
Lemma lem1157479 {_27204 _27220 : Type'} : (term158 _27204 _27220) = (term158 _27204 _27220).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1157478 _27204 _27220 x)). Qed.
Lemma lem1157480 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157489 {_27204 _27220 : Type'} : (term120 _27204 _27220) = (term120 _27204 _27220).
Proof. exact (MK_COMB (@lem1157480 _27204 _27220) (@lem1157479 _27204 _27220)). Qed.
Lemma lem1157490 {_27204 _27220 : Type'} (h1 : term120 _27204 _27220) : term120 _27204 _27220.
Proof. exact (EQ_MP (@lem1157489 _27204 _27220) (@lem1157254 _27204 _27220 h1)). Qed.
Lemma lem1157555 {_27220 : Type'} : (@eq _27220) = (@eq _27220).
Proof. exact (eq_refl (@eq _27220)). Qed.
Lemma lem1157560 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1157561 {_27204 _27220 : Type'} (f : type1222 _27204 _27220) (x : prod _27220 _27204) : (f x) = (@I ((prod _27220 _27204) -> _27220) f x).
Proof. exact (@lem1157560 (prod _27220 _27204) _27220 f x). Qed.
Lemma lem1157563 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (@fst _27220 _27204 h) = (@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h).
Proof. exact (@lem1157561 _27204 _27220 (@fst _27220 _27204) h). Qed.
Lemma lem1157564 {_27220 : Type'} (x : _27220) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1157565 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term175 _27204 _27220 h) = (term176 _27204 _27220 h).
Proof. exact (MK_COMB (@lem1157555 _27220) (@lem1157563 _27204 _27220 h)). Qed.
Lemma lem1157566 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : ((@fst _27220 _27204 h) = x) = ((@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h) = x).
Proof. exact (MK_COMB (@lem1157565 _27204 _27220 h) (@lem1157564 _27220 x)). Qed.
Lemma lem1157597 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term119 _27204 _27220 x h t) : term172 _27204 _27220 x h t.
Proof. exact (EQ_MP (@lem1157416 _27204 _27220 x h t) (@lem1157250 _27204 _27220 x h t h1)). Qed.
Lemma lem1157657 {_27204 _27220 : Type'} : (@eq (prod _27220 _27204)) = (@eq (prod _27220 _27204)).
Proof. exact (eq_refl (@eq (prod _27220 _27204))). Qed.
Lemma lem1157658 {_27204 _27220 : Type'} : (@pair _27220 _27204) = (@pair _27220 _27204).
Proof. exact (eq_refl (@pair _27220 _27204)). Qed.
Lemma lem1157663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1157664 {_27204 _27220 : Type'} (f : type1222 _27204 _27220) (x : prod _27220 _27204) : (f x) = (@I ((prod _27220 _27204) -> _27220) f x).
Proof. exact (@lem1157663 (prod _27220 _27204) _27220 f x). Qed.
Lemma lem1157666 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (@fst _27220 _27204 x) = (@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) x).
Proof. exact (@lem1157664 _27204 _27220 (@fst _27220 _27204) x). Qed.
Lemma lem1157669 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (@snd _27220 _27204 x) = (@snd _27220 _27204 x).
Proof. exact (eq_refl (@snd _27220 _27204 x)). Qed.
Lemma lem1157670 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (term177 _27204 _27220 x) = (term178 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1157658 _27204 _27220) (@lem1157666 _27204 _27220 x)). Qed.
Lemma lem1157671 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (term157 _27204 _27220 x) = (term179 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1157670 _27204 _27220 x) (@lem1157669 _27204 _27220 x)). Qed.
Lemma lem1157672 {_27204 _27220 : Type'} (x : prod _27220 _27204) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1157673 {_27204 _27220 : Type'} (x : prod _27220 _27204) : (term180 _27204 _27220 x) = (term181 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1157657 _27204 _27220) (@lem1157671 _27204 _27220 x)). Qed.
Lemma lem1157674 {_27204 _27220 : Type'} (x : prod _27220 _27204) : ((term157 _27204 _27220 x) = x) = ((term179 _27204 _27220 x) = x).
Proof. exact (MK_COMB (@lem1157673 _27204 _27220 x) (@lem1157672 _27204 _27220 x)). Qed.
Lemma lem1157675 {_27204 _27220 : Type'} : (term158 _27204 _27220) = (term182 _27204 _27220).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1157674 _27204 _27220 x)). Qed.
Lemma lem1157676 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157677 {_27204 _27220 : Type'} : (term120 _27204 _27220) = (term183 _27204 _27220).
Proof. exact (MK_COMB (@lem1157676 _27204 _27220) (@lem1157675 _27204 _27220)). Qed.
Lemma lem1157678 {_27204 _27220 : Type'} (h1 : term120 _27204 _27220) : term183 _27204 _27220.
Proof. exact (EQ_MP (@lem1157677 _27204 _27220) (@lem1157490 _27204 _27220 h1)). Qed.
Lemma lem1157718 {_27204 _27220 : Type'} (x : prod _27220 _27204) : ((term179 _27204 _27220 x) = x) = ((term179 _27204 _27220 x) = x).
Proof. exact (eq_refl ((term179 _27204 _27220 x) = x)). Qed.
Lemma lem1157719 {_27204 _27220 : Type'} : (term182 _27204 _27220) = (term182 _27204 _27220).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1157718 _27204 _27220 x)). Qed.
Lemma lem1157720 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1157722 {_27204 _27220 : Type'} : (term183 _27204 _27220) = (term183 _27204 _27220).
Proof. exact (MK_COMB (@lem1157720 _27204 _27220) (@lem1157719 _27204 _27220)). Qed.
Lemma lem1157723 {_27204 _27220 : Type'} (h1 : term120 _27204 _27220) : term183 _27204 _27220.
Proof. exact (EQ_MP (@lem1157722 _27204 _27220) (@lem1157678 _27204 _27220 h1)). Qed.
Lemma lem1157776 {_27204 _27220 : Type'} (_19337 : prod _27220 _27204) (h1 : term120 _27204 _27220) : term184 _27204 _27220 _19337.
Proof. exact (@lem1157723 _27204 _27220 h1 _19337). Qed.
Lemma lem1157777 {_27204 _27220 : Type'} (_19337 : prod _27220 _27204) : (term184 _27204 _27220 _19337) = ((term179 _27204 _27220 _19337) = _19337).
Proof. exact (eq_refl (term184 _27204 _27220 _19337)). Qed.
Lemma lem1157786 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h) = x.
Proof. exact (EQ_MP (@lem1157566 _27204 _27220 h x) (@lem1157405 _27204 _27220 h x h1)). Qed.
Lemma lem1157796 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term119 _27204 _27220 x h t) : term185 _27204 _27220 x h.
Proof. exact (proj1 (@lem1157597 _27204 _27220 x h t h1)). Qed.
Lemma lem1157811 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : x = (@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h).
Proof. exact (SYM (@lem1157786 _27204 _27220 h x h1)). Qed.
Lemma lem1157882 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term186 _27204 _27220 h) = (term186 _27204 _27220 h).
Proof. exact (eq_refl (term186 _27204 _27220 h)). Qed.
Lemma lem1157883 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term187 _27204 _27220 h x) = (term188 _27204 _27220 h).
Proof. exact (MK_COMB (@lem1157882 _27204 _27220 h) (@lem1157811 _27204 _27220 h x h1)). Qed.
Lemma lem1157884 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term188 _27204 _27220 h) = (term189 _27204 _27220 h).
Proof. exact (eq_refl (term188 _27204 _27220 h)). Qed.
Lemma lem1157885 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term190 _27204 _27220 h x) = (term190 _27204 _27220 h x).
Proof. exact (eq_refl (term190 _27204 _27220 h x)). Qed.
Lemma lem1157886 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : ((term187 _27204 _27220 h x) = (term188 _27204 _27220 h)) = ((term187 _27204 _27220 h x) = (term189 _27204 _27220 h)).
Proof. exact (MK_COMB (@lem1157885 _27204 _27220 h x) (@lem1157884 _27204 _27220 h)). Qed.
Lemma lem1157887 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : (term187 _27204 _27220 h x) = (term185 _27204 _27220 x h).
Proof. exact (eq_refl (term187 _27204 _27220 h x)). Qed.
Lemma lem1157888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1157889 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : (term190 _27204 _27220 h x) = (term191 _27204 _27220 x h).
Proof. exact (MK_COMB (@lem1157888) (@lem1157887 _27204 _27220 x h)). Qed.
Lemma lem1157890 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term189 _27204 _27220 h) = (term189 _27204 _27220 h).
Proof. exact (eq_refl (term189 _27204 _27220 h)). Qed.
Lemma lem1157891 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : ((term187 _27204 _27220 h x) = (term189 _27204 _27220 h)) = ((term185 _27204 _27220 x h) = (term189 _27204 _27220 h)).
Proof. exact (MK_COMB (@lem1157889 _27204 _27220 x h) (@lem1157890 _27204 _27220 h)). Qed.
Lemma lem1157892 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : ((term187 _27204 _27220 h x) = (term188 _27204 _27220 h)) = ((term185 _27204 _27220 x h) = (term189 _27204 _27220 h)).
Proof. exact (TRANS (@lem1157886 _27204 _27220 x h) (@lem1157891 _27204 _27220 x h)). Qed.
Lemma lem1157893 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : (term185 _27204 _27220 x h) = (term189 _27204 _27220 h).
Proof. exact (EQ_MP (@lem1157892 _27204 _27220 x h) (@lem1157883 _27204 _27220 h x h1)). Qed.
Lemma lem1157894 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term189 _27204 _27220 h.
Proof. exact (EQ_MP (@lem1157893 _27204 _27220 h x h2) (@lem1157796 _27204 _27220 x h t h1)). Qed.
Lemma lem1158107 {_27204 _27220 : Type'} (_19337 : prod _27220 _27204) (h1 : term120 _27204 _27220) : (term179 _27204 _27220 _19337) = _19337.
Proof. exact (EQ_MP (@lem1157777 _27204 _27220 _19337) (@lem1157776 _27204 _27220 _19337 h1)). Qed.
Lemma lem1158108 {_27204 _27220 : Type'} (_19337 : prod _27220 _27204) (h1 : term120 _27204 _27220) : (term179 _27204 _27220 _19337) = _19337.
Proof. exact (@lem1158107 _27204 _27220 _19337 h1). Qed.
Lemma lem1158109 {_27204 _27220 : Type'} (h : prod _27220 _27204) (h1 : term120 _27204 _27220) : (term179 _27204 _27220 h) = h.
Proof. exact (@lem1158108 _27204 _27220 h h1). Qed.
Lemma lem1158110 {_27204 _27220 : Type'} (h : prod _27220 _27204) (h1 : term120 _27204 _27220) : term192 _27204 _27220 h.
Proof. exact (fun h0 : term189 _27204 _27220 h => @lem1158109 _27204 _27220 h h1). Qed.
Lemma lem1158112 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1158113 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term192 _27204 _27220 h) = ((term179 _27204 _27220 h) = h).
Proof. exact (@lem1158112 ((term179 _27204 _27220 h) = h)). Qed.
Lemma lem1158114 {_27204 _27220 : Type'} (h : prod _27220 _27204) (h1 : term120 _27204 _27220) : (term179 _27204 _27220 h) = h.
Proof. exact (EQ_MP (@lem1158113 _27204 _27220 h) (@lem1158110 _27204 _27220 h h1)). Qed.
Lemma lem1158117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1158119 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term189 _27204 _27220 h) = (term194 _27204 _27220 h).
Proof. exact (@lem1158117 ((term179 _27204 _27220 h) = h)). Qed.
Lemma lem1158122 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term194 _27204 _27220 h.
Proof. exact (EQ_MP (@lem1158119 _27204 _27220 h) (@lem1157894 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1158125 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (@lem1158122 _27204 _27220 t h x h2 h3 (@lem1158114 _27204 _27220 h h1)). Qed.
Lemma lem1158126 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : term195.
Proof. exact (fun h0 : ~ False => @lem1158125 _27204 _27220 t h x h1 h2 h3). Qed.
Lemma lem1158128 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1158129 : term195 = False.
Proof. exact (@lem1158128 False). Qed.
Lemma lem1158131 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (EQ_MP (@lem1158129) (@lem1158126 _27204 _27220 t h x h1 h2 h3)). Qed.
Lemma lem1158132 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : (term120 _27204 _27220) = False.
Proof. exact (prop_ext (fun h4 : term120 _27204 _27220 => @lem1158131 _27204 _27220 t h x h1 h2 h3) (fun h4 : False => @lem1157490 _27204 _27220 h1)). Qed.
Lemma lem1158133 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (EQ_MP (@lem1158132 _27204 _27220 t h x h1 h2 h3) (@lem1157490 _27204 _27220 h1)). Qed.
Lemma lem1158134 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : ((@fst _27220 _27204 h) = x) = False.
Proof. exact (prop_ext (fun h4 : (@fst _27220 _27204 h) = x => @lem1158133 _27204 _27220 t h x h1 h2 h3) (fun h4 : False => @lem1157405 _27204 _27220 h x h3)). Qed.
Lemma lem1158135 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term120 _27204 _27220) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (EQ_MP (@lem1158134 _27204 _27220 t h x h1 h2 h3) (@lem1157405 _27204 _27220 h x h3)). Qed.
Lemma lem1158136 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term128 _27204 _27220.
Proof. exact (fun h0 : term120 _27204 _27220 => @lem1158135 _27204 _27220 t h x h0 h1 h2). Qed.
Lemma lem1158137 {_27204 _27220 : Type'} : (term128 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (@lem69 (term120 _27204 _27220)). Qed.
Lemma lem1158138 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term129 _27204 _27220.
Proof. exact (EQ_MP (@lem1158137 _27204 _27220) (@lem1158136 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1158139 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term132 _27204 _27220 B.
Proof. exact (fun h0 : term122 _27204 _27220 B => @lem1158138 _27204 _27220 t h x h1 h2). Qed.
Lemma lem1158140 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term135 _27204 _27220 B.
Proof. exact (fun h0 : term121 _27220 B => @lem1158139 _27204 _27220 B t h x h1 h2). Qed.
Lemma lem1158141 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term119 _27204 _27220 x h t) (h2 : (@fst _27220 _27204 h) = x) : term138 _27204 _27220 B.
Proof. exact (fun h0 : term123 _27204 _27220 => @lem1158140 _27204 _27220 B t h x h1 h2). Qed.
Lemma lem1158142 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : (@fst _27220 _27204 h) = x) : term141 _27204 _27220 B x h t.
Proof. exact (fun h0 : term119 _27204 _27220 x h t => @lem1158141 _27204 _27220 B t h x h0 h1). Qed.
Lemma lem1158143 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term143 _27204 _27220 B x h t.
Proof. exact (fun h0 : (@fst _27220 _27204 h) = x => @lem1158142 _27204 _27220 B t h x h0). Qed.
Lemma lem1158144 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term144 _27204 _27220 B x h t.
Proof. exact (fun h0 : term9 _27204 _27220 t => @lem1158143 _27204 _27220 B x h t). Qed.
Lemma lem1158149 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term148 _27204 _27220 B h t.
Proof. exact (fun x : _27220 => @lem1158144 _27204 _27220 B x h t). Qed.
Lemma lem1158154 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term152 _27204 _27220 B t.
Proof. exact (fun h : prod _27220 _27204 => @lem1158149 _27204 _27220 B h t). Qed.
Lemma lem1158159 {_27204 _27220 B : Type'} : term156 _27204 _27220 B.
Proof. exact (fun t : type1641 _27204 _27220 => @lem1158154 _27204 _27220 B t). Qed.
Lemma lem1158160 {_27204 _27220 B : Type'} : term155 _27204 _27220 B.
Proof. exact (EQ_MP (@lem1157247 _27204 _27220 B) (@lem1158159 _27204 _27220 B)). Qed.
Lemma lem1158161 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term196 _27204 _27220 B t.
Proof. exact (@lem1158160 _27204 _27220 B t). Qed.
Lemma lem1158162 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term196 _27204 _27220 B t) = (term151 _27204 _27220 B t).
Proof. exact (eq_refl (term196 _27204 _27220 B t)). Qed.
Lemma lem1158163 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term151 _27204 _27220 B t.
Proof. exact (EQ_MP (@lem1158162 _27204 _27220 B t) (@lem1158161 _27204 _27220 B t)). Qed.
Lemma lem1158164 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) : term197 _27204 _27220 B t h.
Proof. exact (@lem1158163 _27204 _27220 B t h). Qed.
Lemma lem1158165 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term197 _27204 _27220 B t h) = (term147 _27204 _27220 B h t).
Proof. exact (eq_refl (term197 _27204 _27220 B t h)). Qed.
Lemma lem1158166 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term147 _27204 _27220 B h t.
Proof. exact (EQ_MP (@lem1158165 _27204 _27220 B h t) (@lem1158164 _27204 _27220 B t h)). Qed.
Lemma lem1158167 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (x : _27220) : term198 _27204 _27220 B h t x.
Proof. exact (@lem1158166 _27204 _27220 B h t x). Qed.
Lemma lem1158168 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : (term198 _27204 _27220 B h t x) = (term124 _27204 _27220 B x h t).
Proof. exact (eq_refl (term198 _27204 _27220 B h t x)). Qed.
Lemma lem1158169 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term124 _27204 _27220 B x h t.
Proof. exact (EQ_MP (@lem1158168 _27204 _27220 B x h t) (@lem1158167 _27204 _27220 B h t x)). Qed.
Lemma lem1158171 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term124 _27204 _27220 B x h t.
Proof. exact (@lem1156983 _27204 _27220 B x h t (@lem1158169 _27204 _27220 B x h t)). Qed.
Lemma lem1158172 {_27204 _27220 B : Type'} (x : _27220) (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term142 _27204 _27220 B x h t.
Proof. exact (@lem1158171 _27204 _27220 B x h t (@lem1156662 _27204 _27220 t h1)). Qed.
Lemma lem1158173 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : term140 _27204 _27220 B x h t.
Proof. exact (@lem1158172 _27204 _27220 B x h t h1 (@lem1156834 _27204 _27220 h x h2)). Qed.
Lemma lem1158174 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : term137 _27204 _27220 B.
Proof. exact (@lem1158173 _27204 _27220 B t h x h1 h3 (@lem1156959 _27204 _27220 x h t h2)). Qed.
Lemma lem1158175 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : term134 _27204 _27220 B.
Proof. exact (@lem1158174 _27204 _27220 B t h x h1 h2 h3 (@lem1156966 _27204 _27220)). Qed.
Lemma lem1158176 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : term131 _27204 _27220 B.
Proof. exact (@lem1158175 _27204 _27220 B t h x h1 h2 h3 (@lem1156964 _27220 B)). Qed.
Lemma lem1158177 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : term128 _27204 _27220.
Proof. exact (@lem1158176 _27204 _27220 Prop t h x h1 h2 h3 (@lem1156965 _27204 _27220 Prop)). Qed.
Lemma lem1158178 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (@lem1158177 _27204 _27220 t h x h1 h2 h3 (@lem1156960 _27204 _27220)). Qed.
Lemma lem1158179 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : (term119 _27204 _27220 x h t) = False.
Proof. exact (prop_ext (fun h4 : term119 _27204 _27220 x h t => @lem1158178 _27204 _27220 t h x h1 h2 h3) (fun h4 : False => @lem1156959 _27204 _27220 x h t h2)). Qed.
Lemma lem1158180 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term119 _27204 _27220 x h t) (h3 : (@fst _27220 _27204 h) = x) : False.
Proof. exact (EQ_MP (@lem1158179 _27204 _27220 t h x h1 h2 h3) (@lem1156959 _27204 _27220 x h t h2)). Qed.
Lemma lem1158181 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : term118 _27204 _27220 x h t.
Proof. exact (fun h0 : term119 _27204 _27220 x h t => @lem1158180 _27204 _27220 t h x h1 h0 h2). Qed.
Lemma lem1158182 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : term94 _27204 _27220 x h t.
Proof. exact (EQ_MP (@lem1156958 _27204 _27220 x h t) (@lem1158181 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1158184 (p : Prop) : p = (term117 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1158185 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : ((term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t)) = (term199 _27204 _27220 h x t).
Proof. exact (@lem1158184 ((term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t))). Qed.
Lemma lem1158186 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term199 _27204 _27220 h x t) = ((term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t)).
Proof. exact (SYM (@lem1158185 _27204 _27220 h x t)). Qed.
Lemma lem1158187 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term200 _27204 _27220 h x t) : term200 _27204 _27220 h x t.
Proof. exact (h1). Qed.
Lemma lem1158188 {_27204 _27220 : Type'} : term120 _27204 _27220.
Proof. exact (@lem48081 _27220 _27204). Qed.
Lemma lem1158191 {_27220 B : Type'} : term121 _27220 B.
Proof. exact (@lem47827 _27220 B). Qed.
Lemma lem1158192 {_27204 _27220 B : Type'} : term122 _27204 _27220 B.
Proof. exact (@lem47827 (prod _27220 _27204) B). Qed.
Lemma lem1158193 {_27204 _27220 : Type'} : term123 _27204 _27220.
Proof. exact (@lem47827 _27220 _27204). Qed.
Lemma lem1158197 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term201 _27204 _27220 B h x t) : term201 _27204 _27220 B h x t.
Proof. exact (h1). Qed.
Lemma lem1158198 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term202 _27204 _27220 B h x t.
Proof. exact (fun h0 : term201 _27204 _27220 B h x t => @lem1158197 _27204 _27220 B h x t h0). Qed.
Lemma lem1158199 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term202 _27204 _27220 B h x t) : term202 _27204 _27220 B h x t.
Proof. exact (h1). Qed.
Lemma lem1158200 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term201 _27204 _27220 B h x t) : term201 _27204 _27220 B h x t.
Proof. exact (h1). Qed.
Lemma lem1158201 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term201 _27204 _27220 B h x t) (h2 : term202 _27204 _27220 B h x t) : term201 _27204 _27220 B h x t.
Proof. exact (@lem1158199 _27204 _27220 B h x t h2 (@lem1158200 _27204 _27220 B h x t h1)). Qed.
Lemma lem1158202 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term201 _27204 _27220 B h x t) : term203 _27204 _27220 B h x t.
Proof. exact (fun h0 : term202 _27204 _27220 B h x t => @lem1158201 _27204 _27220 B h x t h1 h0). Qed.
Lemma lem1158203 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term202 _27204 _27220 B h x t) : term202 _27204 _27220 B h x t.
Proof. exact (h1). Qed.
Lemma lem1158204 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term201 _27204 _27220 B h x t) (h2 : term202 _27204 _27220 B h x t) : term201 _27204 _27220 B h x t.
Proof. exact (@lem1158202 _27204 _27220 B h x t h1 (@lem1158203 _27204 _27220 B h x t h2)). Qed.
Lemma lem1158205 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term202 _27204 _27220 B h x t) : term202 _27204 _27220 B h x t.
Proof. exact (fun h0 : term201 _27204 _27220 B h x t => @lem1158204 _27204 _27220 B h x t h0 h1). Qed.
Lemma lem1158206 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term204 _27204 _27220 B h x t.
Proof. exact (fun h0 : term202 _27204 _27220 B h x t => @lem1158205 _27204 _27220 B h x t h0). Qed.
Lemma lem1158209 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term202 _27204 _27220 B h x t.
Proof. exact (@lem1158206 _27204 _27220 B h x t (@lem1158198 _27204 _27220 B h x t)). Qed.
Lemma lem1158210 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term202 _27204 _27220 B h x t.
Proof. exact (@lem1158209 _27204 _27220 B h x t). Qed.
Lemma lem1158266 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1158267 {_27204 _27220 : Type'} : (term128 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (@lem1158266 (term120 _27204 _27220)). Qed.
Lemma lem1158272 {_27204 _27220 B : Type'} : (term130 _27204 _27220 B) = (term130 _27204 _27220 B).
Proof. exact (eq_refl (term130 _27204 _27220 B)). Qed.
Lemma lem1158273 {_27204 _27220 B : Type'} : (term131 _27204 _27220 B) = (term132 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158272 _27204 _27220 B) (@lem1158267 _27204 _27220)). Qed.
Lemma lem1158276 {_27220 B : Type'} : (term133 _27220 B) = (term133 _27220 B).
Proof. exact (eq_refl (term133 _27220 B)). Qed.
Lemma lem1158277 {_27204 _27220 B : Type'} : (term134 _27204 _27220 B) = (term135 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158276 _27220 B) (@lem1158273 _27204 _27220 B)). Qed.
Lemma lem1158280 {_27204 _27220 : Type'} : (term136 _27204 _27220) = (term136 _27204 _27220).
Proof. exact (eq_refl (term136 _27204 _27220)). Qed.
Lemma lem1158281 {_27204 _27220 B : Type'} : (term137 _27204 _27220 B) = (term138 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158280 _27204 _27220) (@lem1158277 _27204 _27220 B)). Qed.
Lemma lem1158284 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term205 _27204 _27220 h x t) = (term205 _27204 _27220 h x t).
Proof. exact (eq_refl (term205 _27204 _27220 h x t)). Qed.
Lemma lem1158285 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term206 _27204 _27220 B h x t) = (term207 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158284 _27204 _27220 h x t) (@lem1158281 _27204 _27220 B)). Qed.
Lemma lem1158288 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term90 _27204 _27220 h x) = (term90 _27204 _27220 h x).
Proof. exact (eq_refl (term90 _27204 _27220 h x)). Qed.
Lemma lem1158289 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term208 _27204 _27220 B h x t) = (term209 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158288 _27204 _27220 h x) (@lem1158285 _27204 _27220 B h x t)). Qed.
Lemma lem1158292 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term11 _27204 _27220 t) = (term11 _27204 _27220 t).
Proof. exact (eq_refl (term11 _27204 _27220 t)). Qed.
Lemma lem1158293 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term201 _27204 _27220 B h x t) = (term210 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158292 _27204 _27220 t) (@lem1158289 _27204 _27220 B h x t)). Qed.
Lemma lem1158296 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term211 _27204 _27220 B x t) = (term212 _27204 _27220 B x t).
Proof. exact (fun_ext (fun h : prod _27220 _27204 => @lem1158293 _27204 _27220 B h x t)). Qed.
Lemma lem1158297 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1158298 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term213 _27204 _27220 B x t) = (term214 _27204 _27220 B x t).
Proof. exact (MK_COMB (@lem1158297 _27204 _27220) (@lem1158296 _27204 _27220 B x t)). Qed.
Lemma lem1158303 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term215 _27204 _27220 B t) = (term216 _27204 _27220 B t).
Proof. exact (fun_ext (fun x : _27220 => @lem1158298 _27204 _27220 B x t)). Qed.
Lemma lem1158304 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158305 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term217 _27204 _27220 B t) = (term218 _27204 _27220 B t).
Proof. exact (MK_COMB (@lem1158304 _27220) (@lem1158303 _27204 _27220 B t)). Qed.
Lemma lem1158310 {_27204 _27220 B : Type'} : (term219 _27204 _27220 B) = (term220 _27204 _27220 B).
Proof. exact (fun_ext (fun t : type1641 _27204 _27220 => @lem1158305 _27204 _27220 B t)). Qed.
Lemma lem1158311 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1158320 {_27204 _27220 B : Type'} : (term221 _27204 _27220 B) = (term222 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158311 _27204 _27220) (@lem1158310 _27204 _27220 B)). Qed.
Lemma lem1158321 {_27204 _27220 : Type'} (x : prod _27220 _27204) : ((term157 _27204 _27220 x) = x) = ((term157 _27204 _27220 x) = x).
Proof. exact (eq_refl ((term157 _27204 _27220 x) = x)). Qed.
Lemma lem1158322 {_27204 _27220 : Type'} : (term158 _27204 _27220) = (term158 _27204 _27220).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1158321 _27204 _27220 x)). Qed.
Lemma lem1158323 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1158324 {_27204 _27220 : Type'} : (term120 _27204 _27220) = (term120 _27204 _27220).
Proof. exact (MK_COMB (@lem1158323 _27204 _27220) (@lem1158322 _27204 _27220)). Qed.
Lemma lem1158325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1158326 {_27204 _27220 : Type'} : (term129 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (MK_COMB (@lem1158325) (@lem1158324 _27204 _27220)). Qed.
Lemma lem1158327 {_27204 _27220 B : Type'} (y : B) (x : prod _27220 _27204) : ((term159 _27204 _27220 B x y) = x) = ((term159 _27204 _27220 B x y) = x).
Proof. exact (eq_refl ((term159 _27204 _27220 B x y) = x)). Qed.
Lemma lem1158328 {_27204 _27220 B : Type'} (x : prod _27220 _27204) : (term160 _27204 _27220 B x) = (term160 _27204 _27220 B x).
Proof. exact (fun_ext (fun y : B => @lem1158327 _27204 _27220 B y x)). Qed.
Lemma lem1158329 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1158330 {_27204 _27220 B : Type'} (x : prod _27220 _27204) : (term161 _27204 _27220 B x) = (term161 _27204 _27220 B x).
Proof. exact (MK_COMB (@lem1158329 B) (@lem1158328 _27204 _27220 B x)). Qed.
Lemma lem1158331 {_27204 _27220 B : Type'} : (term162 _27204 _27220 B) = (term162 _27204 _27220 B).
Proof. exact (fun_ext (fun x : prod _27220 _27204 => @lem1158330 _27204 _27220 B x)). Qed.
Lemma lem1158332 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1158333 {_27204 _27220 B : Type'} : (term122 _27204 _27220 B) = (term122 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158332 _27204 _27220) (@lem1158331 _27204 _27220 B)). Qed.
Lemma lem1158334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1158335 {_27204 _27220 B : Type'} : (term130 _27204 _27220 B) = (term130 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158334) (@lem1158333 _27204 _27220 B)). Qed.
Lemma lem1158336 {_27204 _27220 B : Type'} : (term132 _27204 _27220 B) = (term132 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158335 _27204 _27220 B) (@lem1158326 _27204 _27220)). Qed.
Lemma lem1158337 {_27220 B : Type'} (y : B) (x : _27220) : ((term163 _27220 B x y) = x) = ((term163 _27220 B x y) = x).
Proof. exact (eq_refl ((term163 _27220 B x y) = x)). Qed.
Lemma lem1158338 {_27220 B : Type'} (x : _27220) : (term164 _27220 B x) = (term164 _27220 B x).
Proof. exact (fun_ext (fun y : B => @lem1158337 _27220 B y x)). Qed.
Lemma lem1158339 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1158340 {_27220 B : Type'} (x : _27220) : (term165 _27220 B x) = (term165 _27220 B x).
Proof. exact (MK_COMB (@lem1158339 B) (@lem1158338 _27220 B x)). Qed.
Lemma lem1158341 {_27220 B : Type'} : (term166 _27220 B) = (term166 _27220 B).
Proof. exact (fun_ext (fun x : _27220 => @lem1158340 _27220 B x)). Qed.
Lemma lem1158342 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158343 {_27220 B : Type'} : (term121 _27220 B) = (term121 _27220 B).
Proof. exact (MK_COMB (@lem1158342 _27220) (@lem1158341 _27220 B)). Qed.
Lemma lem1158344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1158345 {_27220 B : Type'} : (term133 _27220 B) = (term133 _27220 B).
Proof. exact (MK_COMB (@lem1158344) (@lem1158343 _27220 B)). Qed.
Lemma lem1158346 {_27204 _27220 B : Type'} : (term135 _27204 _27220 B) = (term135 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158345 _27220 B) (@lem1158336 _27204 _27220 B)). Qed.
Lemma lem1158347 {_27204 _27220 : Type'} (y : _27204) (x : _27220) : ((term167 _27204 _27220 x y) = x) = ((term167 _27204 _27220 x y) = x).
Proof. exact (eq_refl ((term167 _27204 _27220 x y) = x)). Qed.
Lemma lem1158348 {_27204 _27220 : Type'} (x : _27220) : (term168 _27204 _27220 x) = (term168 _27204 _27220 x).
Proof. exact (fun_ext (fun y : _27204 => @lem1158347 _27204 _27220 y x)). Qed.
Lemma lem1158349 {_27204 : Type'} : (@all _27204) = (@all _27204).
Proof. exact (eq_refl (@all _27204)). Qed.
Lemma lem1158350 {_27204 _27220 : Type'} (x : _27220) : (term169 _27204 _27220 x) = (term169 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1158349 _27204) (@lem1158348 _27204 _27220 x)). Qed.
Lemma lem1158351 {_27204 _27220 : Type'} : (term170 _27204 _27220) = (term170 _27204 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1158350 _27204 _27220 x)). Qed.
Lemma lem1158352 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158353 {_27204 _27220 : Type'} : (term123 _27204 _27220) = (term123 _27204 _27220).
Proof. exact (MK_COMB (@lem1158352 _27220) (@lem1158351 _27204 _27220)). Qed.
Lemma lem1158354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1158355 {_27204 _27220 : Type'} : (term136 _27204 _27220) = (term136 _27204 _27220).
Proof. exact (MK_COMB (@lem1158354) (@lem1158353 _27204 _27220)). Qed.
Lemma lem1158356 {_27204 _27220 B : Type'} : (term138 _27204 _27220 B) = (term138 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158355 _27204 _27220) (@lem1158346 _27204 _27220 B)). Qed.
Lemma lem1158369 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term205 _27204 _27220 h x t) = (term205 _27204 _27220 h x t).
Proof. exact (eq_refl (term205 _27204 _27220 h x t)). Qed.
Lemma lem1158370 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term207 _27204 _27220 B h x t) = (term207 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158369 _27204 _27220 h x t) (@lem1158356 _27204 _27220 B)). Qed.
Lemma lem1158375 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term90 _27204 _27220 h x) = (term90 _27204 _27220 h x).
Proof. exact (eq_refl (term90 _27204 _27220 h x)). Qed.
Lemma lem1158376 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term209 _27204 _27220 B h x t) = (term209 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158375 _27204 _27220 h x) (@lem1158370 _27204 _27220 B h x t)). Qed.
Lemma lem1158381 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t)) = ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t)).
Proof. exact (eq_refl ((term109 _27204 _27220 x t) = (term105 _27204 _27220 x t))). Qed.
Lemma lem1158382 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term171 _27204 _27220 t) = (term171 _27204 _27220 t).
Proof. exact (fun_ext (fun x : _27220 => @lem1158381 _27204 _27220 x t)). Qed.
Lemma lem1158383 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158384 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term9 _27204 _27220 t) = (term9 _27204 _27220 t).
Proof. exact (MK_COMB (@lem1158383 _27220) (@lem1158382 _27204 _27220 t)). Qed.
Lemma lem1158385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1158386 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) : (term11 _27204 _27220 t) = (term11 _27204 _27220 t).
Proof. exact (MK_COMB (@lem1158385) (@lem1158384 _27204 _27220 t)). Qed.
Lemma lem1158387 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term210 _27204 _27220 B h x t) = (term210 _27204 _27220 B h x t).
Proof. exact (MK_COMB (@lem1158386 _27204 _27220 t) (@lem1158376 _27204 _27220 B h x t)). Qed.
Lemma lem1158388 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term212 _27204 _27220 B x t) = (term212 _27204 _27220 B x t).
Proof. exact (fun_ext (fun h : prod _27220 _27204 => @lem1158387 _27204 _27220 B h x t)). Qed.
Lemma lem1158389 {_27204 _27220 : Type'} : (@all (prod _27220 _27204)) = (@all (prod _27220 _27204)).
Proof. exact (eq_refl (@all (prod _27220 _27204))). Qed.
Lemma lem1158390 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term214 _27204 _27220 B x t) = (term214 _27204 _27220 B x t).
Proof. exact (MK_COMB (@lem1158389 _27204 _27220) (@lem1158388 _27204 _27220 B x t)). Qed.
Lemma lem1158391 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term216 _27204 _27220 B t) = (term216 _27204 _27220 B t).
Proof. exact (fun_ext (fun x : _27220 => @lem1158390 _27204 _27220 B x t)). Qed.
Lemma lem1158392 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158393 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term218 _27204 _27220 B t) = (term218 _27204 _27220 B t).
Proof. exact (MK_COMB (@lem1158392 _27220) (@lem1158391 _27204 _27220 B t)). Qed.
Lemma lem1158394 {_27204 _27220 B : Type'} : (term220 _27204 _27220 B) = (term220 _27204 _27220 B).
Proof. exact (fun_ext (fun t : type1641 _27204 _27220 => @lem1158393 _27204 _27220 B t)). Qed.
Lemma lem1158395 {_27204 _27220 : Type'} : (@all (list (prod _27220 _27204))) = (@all (list (prod _27220 _27204))).
Proof. exact (eq_refl (@all (list (prod _27220 _27204)))). Qed.
Lemma lem1158396 {_27204 _27220 B : Type'} : (term222 _27204 _27220 B) = (term222 _27204 _27220 B).
Proof. exact (MK_COMB (@lem1158395 _27204 _27220) (@lem1158394 _27204 _27220 B)). Qed.
Lemma lem1158479 {_27204 _27220 B : Type'} : (term221 _27204 _27220 B) = (term222 _27204 _27220 B).
Proof. exact (TRANS (@lem1158320 _27204 _27220 B) (@lem1158396 _27204 _27220 B)). Qed.
Lemma lem1158480 {_27204 _27220 B : Type'} : (term222 _27204 _27220 B) = (term221 _27204 _27220 B).
Proof. exact (SYM (@lem1158479 _27204 _27220 B)). Qed.
Lemma lem1158483 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term200 _27204 _27220 h x t) : term200 _27204 _27220 h x t.
Proof. exact (h1). Qed.
Lemma lem1158484 {_27204 _27220 : Type'} (h1 : term123 _27204 _27220) : term123 _27204 _27220.
Proof. exact (h1). Qed.
Lemma lem1158638 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : term103 _27204 _27220 h x.
Proof. exact (h1). Qed.
Lemma lem1158647 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term223 _27204 _27220 h x t) = (term224 _27204 _27220 h x t).
Proof. exact (@lem17160 ((term225 _27204 _27220 x t) = h) (term105 _27204 _27220 x t)). Qed.
Lemma lem1158652 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term105 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (eq_refl (term105 _27204 _27220 x t)). Qed.
Lemma lem1158653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1158654 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term226 _27204 _27220 h x t) = (term227 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1158653) (@lem1158647 _27204 _27220 h x t)). Qed.
Lemma lem1158655 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term228 _27204 _27220 h x t) = (term229 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1158654 _27204 _27220 h x t) (@lem1158652 _27204 _27220 x t)). Qed.
Lemma lem1158660 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term230 _27204 _27220 h x t) = (term230 _27204 _27220 h x t).
Proof. exact (eq_refl (term230 _27204 _27220 h x t)). Qed.
Lemma lem1158661 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term231 _27204 _27220 h x t) = (term232 _27204 _27220 h x t).
Proof. exact (MK_COMB (@lem1158660 _27204 _27220 h x t) (@lem1158655 _27204 _27220 h x t)). Qed.
Lemma lem1158662 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term200 _27204 _27220 h x t) = (term231 _27204 _27220 h x t).
Proof. exact (@lem17646 (term113 _27204 _27220 h x t) (term105 _27204 _27220 x t)). Qed.
Lemma lem1158667 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term200 _27204 _27220 h x t) = (term232 _27204 _27220 h x t).
Proof. exact (TRANS (@lem1158662 _27204 _27220 h x t) (@lem1158661 _27204 _27220 h x t)). Qed.
Lemma lem1158669 {_27204 _27220 : Type'} (y : _27204) (x : _27220) : ((term167 _27204 _27220 x y) = x) = ((term167 _27204 _27220 x y) = x).
Proof. exact (eq_refl ((term167 _27204 _27220 x y) = x)). Qed.
Lemma lem1158670 {_27204 _27220 : Type'} (x : _27220) : (term168 _27204 _27220 x) = (term168 _27204 _27220 x).
Proof. exact (fun_ext (fun y : _27204 => @lem1158669 _27204 _27220 y x)). Qed.
Lemma lem1158671 {_27204 : Type'} : (@all _27204) = (@all _27204).
Proof. exact (eq_refl (@all _27204)). Qed.
Lemma lem1158672 {_27204 _27220 : Type'} (x : _27220) : (term169 _27204 _27220 x) = (term169 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1158671 _27204) (@lem1158670 _27204 _27220 x)). Qed.
Lemma lem1158673 {_27204 _27220 : Type'} : (term170 _27204 _27220) = (term170 _27204 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1158672 _27204 _27220 x)). Qed.
Lemma lem1158674 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158687 {_27204 _27220 : Type'} : (term123 _27204 _27220) = (term123 _27204 _27220).
Proof. exact (MK_COMB (@lem1158674 _27220) (@lem1158673 _27204 _27220)). Qed.
Lemma lem1158688 {_27204 _27220 : Type'} (h1 : term123 _27204 _27220) : term123 _27204 _27220.
Proof. exact (EQ_MP (@lem1158687 _27204 _27220) (@lem1158484 _27204 _27220 h1)). Qed.
Lemma lem1158806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1158807 {_27220 : Type'} : (@eq _27220) = (@eq _27220).
Proof. exact (eq_refl (@eq _27220)). Qed.
Lemma lem1158812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1158813 {_27204 _27220 : Type'} (f : type1222 _27204 _27220) (x : prod _27220 _27204) : (f x) = (@I ((prod _27220 _27204) -> _27220) f x).
Proof. exact (@lem1158812 (prod _27220 _27204) _27220 f x). Qed.
Lemma lem1158815 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (@fst _27220 _27204 h) = (@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h).
Proof. exact (@lem1158813 _27204 _27220 (@fst _27220 _27204) h). Qed.
Lemma lem1158816 {_27220 : Type'} (x : _27220) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1158817 {_27204 _27220 : Type'} (h : prod _27220 _27204) : (term175 _27204 _27220 h) = (term176 _27204 _27220 h).
Proof. exact (MK_COMB (@lem1158807 _27220) (@lem1158815 _27204 _27220 h)). Qed.
Lemma lem1158818 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : ((@fst _27220 _27204 h) = x) = ((@I ((prod _27220 _27204) -> _27220) (@fst _27220 _27204) h) = x).
Proof. exact (MK_COMB (@lem1158817 _27204 _27220 h) (@lem1158816 _27220 x)). Qed.
Lemma lem1158819 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term103 _27204 _27220 h x) = (term233 _27204 _27220 h x).
Proof. exact (MK_COMB (@lem1158806) (@lem1158818 _27204 _27220 h x)). Qed.
Lemma lem1158904 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term200 _27204 _27220 h x t) : term232 _27204 _27220 h x t.
Proof. exact (EQ_MP (@lem1158667 _27204 _27220 h x t) (@lem1158483 _27204 _27220 h x t h1)). Qed.
Lemma lem1158905 {_27220 : Type'} : (@eq _27220) = (@eq _27220).
Proof. exact (eq_refl (@eq _27220)). Qed.
Lemma lem1158914 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1158915 {_27204 _27220 : Type'} (f : type1222 _27204 _27220) (x : prod _27220 _27204) : (f x) = (@I ((prod _27220 _27204) -> _27220) f x).
Proof. exact (@lem1158914 (prod _27220 _27204) _27220 f x). Qed.
Lemma lem1158917 {_27204 _27220 : Type'} (x : _27220) (y : _27204) : (term167 _27204 _27220 x y) = (term234 _27204 _27220 x y).
Proof. exact (@lem1158915 _27204 _27220 (@fst _27220 _27204) (@pair _27220 _27204 x y)). Qed.
Lemma lem1158918 {_27220 : Type'} (x : _27220) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1158919 {_27204 _27220 : Type'} (x : _27220) (y : _27204) : (term235 _27204 _27220 x y) = (term236 _27204 _27220 x y).
Proof. exact (MK_COMB (@lem1158905 _27220) (@lem1158917 _27204 _27220 x y)). Qed.
Lemma lem1158920 {_27204 _27220 : Type'} (y : _27204) (x : _27220) : ((term167 _27204 _27220 x y) = x) = ((term234 _27204 _27220 x y) = x).
Proof. exact (MK_COMB (@lem1158919 _27204 _27220 x y) (@lem1158918 _27220 x)). Qed.
Lemma lem1158921 {_27204 _27220 : Type'} (x : _27220) : (term168 _27204 _27220 x) = (term237 _27204 _27220 x).
Proof. exact (fun_ext (fun y : _27204 => @lem1158920 _27204 _27220 y x)). Qed.
Lemma lem1158922 {_27204 : Type'} : (@all _27204) = (@all _27204).
Proof. exact (eq_refl (@all _27204)). Qed.
Lemma lem1158923 {_27204 _27220 : Type'} (x : _27220) : (term169 _27204 _27220 x) = (term238 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1158922 _27204) (@lem1158921 _27204 _27220 x)). Qed.
Lemma lem1158924 {_27204 _27220 : Type'} : (term170 _27204 _27220) = (term239 _27204 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1158923 _27204 _27220 x)). Qed.
Lemma lem1158925 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1158926 {_27204 _27220 : Type'} : (term123 _27204 _27220) = (term240 _27204 _27220).
Proof. exact (MK_COMB (@lem1158925 _27220) (@lem1158924 _27204 _27220)). Qed.
Lemma lem1158927 {_27204 _27220 : Type'} (h1 : term123 _27204 _27220) : term240 _27204 _27220.
Proof. exact (EQ_MP (@lem1158926 _27204 _27220) (@lem1158688 _27204 _27220 h1)). Qed.
Lemma lem1158988 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) : term241 _27204 _27220 h x t.
Proof. exact (h1). Qed.
Lemma lem1158989 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term229 _27204 _27220 h x t.
Proof. exact (h1). Qed.
Lemma lem1158991 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) : term113 _27204 _27220 h x t.
Proof. exact (proj1 (@lem1158988 _27204 _27220 h x t h1)). Qed.
Lemma lem1158995 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term224 _27204 _27220 h x t.
Proof. exact (proj1 (@lem1158989 _27204 _27220 h x t h1)). Qed.
Lemma lem1159003 {_27204 _27220 : Type'} (y : _27204) (x : _27220) : ((term234 _27204 _27220 x y) = x) = ((term234 _27204 _27220 x y) = x).
Proof. exact (eq_refl ((term234 _27204 _27220 x y) = x)). Qed.
Lemma lem1159004 {_27204 _27220 : Type'} (x : _27220) : (term237 _27204 _27220 x) = (term237 _27204 _27220 x).
Proof. exact (fun_ext (fun y : _27204 => @lem1159003 _27204 _27220 y x)). Qed.
Lemma lem1159005 {_27204 : Type'} : (@all _27204) = (@all _27204).
Proof. exact (eq_refl (@all _27204)). Qed.
Lemma lem1159006 {_27204 _27220 : Type'} (x : _27220) : (term238 _27204 _27220 x) = (term238 _27204 _27220 x).
Proof. exact (MK_COMB (@lem1159005 _27204) (@lem1159004 _27204 _27220 x)). Qed.
Lemma lem1159007 {_27204 _27220 : Type'} : (term239 _27204 _27220) = (term239 _27204 _27220).
Proof. exact (fun_ext (fun x : _27220 => @lem1159006 _27204 _27220 x)). Qed.
Lemma lem1159008 {_27220 : Type'} : (@all _27220) = (@all _27220).
Proof. exact (eq_refl (@all _27220)). Qed.
Lemma lem1159010 {_27204 _27220 : Type'} : (term240 _27204 _27220) = (term240 _27204 _27220).
Proof. exact (MK_COMB (@lem1159008 _27220) (@lem1159007 _27204 _27220)). Qed.
Lemma lem1159011 {_27204 _27220 : Type'} (h1 : term123 _27204 _27220) : term240 _27204 _27220.
Proof. exact (EQ_MP (@lem1159010 _27204 _27220) (@lem1158927 _27204 _27220 h1)). Qed.
Lemma lem1159072 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : (term225 _27204 _27220 x t) = h) : (term225 _27204 _27220 x t) = h.
Proof. exact (h1). Qed.
Lemma lem1159147 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term105 _27204 _27220 x t) : term105 _27204 _27220 x t.
Proof. exact (h1). Qed.
Lemma lem1159227 {_27204 _27220 : Type'} (_19396 : _27220) (h1 : term123 _27204 _27220) : term242 _27204 _27220 _19396.
Proof. exact (@lem1159011 _27204 _27220 h1 _19396). Qed.
Lemma lem1159228 {_27204 _27220 : Type'} (_19396 : _27220) : (term242 _27204 _27220 _19396) = (term238 _27204 _27220 _19396).
Proof. exact (eq_refl (term242 _27204 _27220 _19396)). Qed.
Lemma lem1159229 {_27204 _27220 : Type'} (_19396 : _27220) (h1 : term123 _27204 _27220) : term238 _27204 _27220 _19396.
Proof. exact (EQ_MP (@lem1159228 _27204 _27220 _19396) (@lem1159227 _27204 _27220 _19396 h1)). Qed.
Lemma lem1159230 {_27204 _27220 : Type'} (_19396 : _27220) (_19397 : _27204) (h1 : term123 _27204 _27220) : term243 _27204 _27220 _19396 _19397.
Proof. exact (@lem1159229 _27204 _27220 _19396 h1 _19397). Qed.
Lemma lem1159231 {_27204 _27220 : Type'} (_19397 : _27204) (_19396 : _27220) : (term243 _27204 _27220 _19396 _19397) = ((term234 _27204 _27220 _19396 _19397) = _19396).
Proof. exact (eq_refl (term243 _27204 _27220 _19396 _19397)). Qed.
Lemma lem1159309 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : term233 _27204 _27220 h x.
Proof. exact (EQ_MP (@lem1158819 _27204 _27220 h x) (@lem1158638 _27204 _27220 h x h1)). Qed.
Lemma lem1159333 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : (term225 _27204 _27220 x t) = h) : (term225 _27204 _27220 x t) = h.
Proof. exact (h1). Qed.
Lemma lem1159357 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) : term244 _27204 _27220 x t.
Proof. exact (proj2 (@lem1158988 _27204 _27220 h x t h1)). Qed.
Lemma lem1159359 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term105 _27204 _27220 x t) : term105 _27204 _27220 x t.
Proof. exact (h1). Qed.
Lemma lem1159387 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term244 _27204 _27220 x t.
Proof. exact (proj2 (@lem1158995 _27204 _27220 h x t h1)). Qed.
Lemma lem1159388 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : (term225 _27204 _27220 x t) = h) : h = (term225 _27204 _27220 x t).
Proof. exact (SYM (@lem1159333 _27204 _27220 x t h h1)). Qed.
Lemma lem1159403 {_27204 _27220 : Type'} (x : _27220) : (term245 _27204 _27220 x) = (term245 _27204 _27220 x).
Proof. exact (eq_refl (term245 _27204 _27220 x)). Qed.
Lemma lem1159404 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : (term225 _27204 _27220 x t) = h) : (term246 _27204 _27220 x h) = (term247 _27204 _27220 x t).
Proof. exact (MK_COMB (@lem1159403 _27204 _27220 x) (@lem1159388 _27204 _27220 x t h h1)). Qed.
Lemma lem1159405 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) : (term247 _27204 _27220 x t) = (term248 _27204 _27220 t x).
Proof. exact (eq_refl (term247 _27204 _27220 x t)). Qed.
Lemma lem1159406 {_27204 _27220 : Type'} (x : _27220) (h : prod _27220 _27204) : (term249 _27204 _27220 x h) = (term249 _27204 _27220 x h).
Proof. exact (eq_refl (term249 _27204 _27220 x h)). Qed.
Lemma lem1159407 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (x : _27220) : ((term246 _27204 _27220 x h) = (term247 _27204 _27220 x t)) = ((term246 _27204 _27220 x h) = (term248 _27204 _27220 t x)).
Proof. exact (MK_COMB (@lem1159406 _27204 _27220 x h) (@lem1159405 _27204 _27220 t x)). Qed.
Lemma lem1159408 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term246 _27204 _27220 x h) = (term233 _27204 _27220 h x).
Proof. exact (eq_refl (term246 _27204 _27220 x h)). Qed.
Lemma lem1159409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1159410 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) : (term249 _27204 _27220 x h) = (term250 _27204 _27220 h x).
Proof. exact (MK_COMB (@lem1159409) (@lem1159408 _27204 _27220 h x)). Qed.
Lemma lem1159411 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) : (term248 _27204 _27220 t x) = (term248 _27204 _27220 t x).
Proof. exact (eq_refl (term248 _27204 _27220 t x)). Qed.
Lemma lem1159412 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (x : _27220) : ((term246 _27204 _27220 x h) = (term248 _27204 _27220 t x)) = ((term233 _27204 _27220 h x) = (term248 _27204 _27220 t x)).
Proof. exact (MK_COMB (@lem1159410 _27204 _27220 h x) (@lem1159411 _27204 _27220 t x)). Qed.
Lemma lem1159413 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (x : _27220) : ((term246 _27204 _27220 x h) = (term247 _27204 _27220 x t)) = ((term233 _27204 _27220 h x) = (term248 _27204 _27220 t x)).
Proof. exact (TRANS (@lem1159407 _27204 _27220 h t x) (@lem1159412 _27204 _27220 h t x)). Qed.
Lemma lem1159414 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : (term225 _27204 _27220 x t) = h) : (term233 _27204 _27220 h x) = (term248 _27204 _27220 t x).
Proof. exact (EQ_MP (@lem1159413 _27204 _27220 h t x) (@lem1159404 _27204 _27220 x t h h1)). Qed.
Lemma lem1159415 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term103 _27204 _27220 h x) (h2 : (term225 _27204 _27220 x t) = h) : term248 _27204 _27220 t x.
Proof. exact (EQ_MP (@lem1159414 _27204 _27220 x t h h2) (@lem1159309 _27204 _27220 h x h1)). Qed.
Lemma lem1159685 {_27204 _27220 : Type'} (_19397 : _27204) (_19396 : _27220) (h1 : term123 _27204 _27220) : (term234 _27204 _27220 _19396 _19397) = _19396.
Proof. exact (EQ_MP (@lem1159231 _27204 _27220 _19397 _19396) (@lem1159230 _27204 _27220 _19396 _19397 h1)). Qed.
Lemma lem1159686 {_27204 _27220 : Type'} (_19397 : _27204) (_19396 : _27220) (h1 : term123 _27204 _27220) : (term234 _27204 _27220 _19396 _19397) = _19396.
Proof. exact (@lem1159685 _27204 _27220 _19397 _19396 h1). Qed.
Lemma lem1159687 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) (h1 : term123 _27204 _27220) : (term251 _27204 _27220 x t) = x.
Proof. exact (@lem1159686 _27204 _27220 (@ASSOC _27204 _27220 x t) x h1). Qed.
Lemma lem1159688 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) (h1 : term123 _27204 _27220) : term252 _27204 _27220 t x.
Proof. exact (fun h0 : term248 _27204 _27220 t x => @lem1159687 _27204 _27220 t x h1). Qed.
Lemma lem1159690 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1159691 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) : (term252 _27204 _27220 t x) = ((term251 _27204 _27220 x t) = x).
Proof. exact (@lem1159690 ((term251 _27204 _27220 x t) = x)). Qed.
Lemma lem1159692 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) (h1 : term123 _27204 _27220) : (term251 _27204 _27220 x t) = x.
Proof. exact (EQ_MP (@lem1159691 _27204 _27220 t x) (@lem1159688 _27204 _27220 t x h1)). Qed.
Lemma lem1159695 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1159697 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (x : _27220) : (term248 _27204 _27220 t x) = (term253 _27204 _27220 t x).
Proof. exact (@lem1159695 ((term251 _27204 _27220 x t) = x)). Qed.
Lemma lem1159700 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term103 _27204 _27220 h x) (h2 : (term225 _27204 _27220 x t) = h) : term253 _27204 _27220 t x.
Proof. exact (EQ_MP (@lem1159697 _27204 _27220 t x) (@lem1159415 _27204 _27220 x t h h1 h2)). Qed.
Lemma lem1159703 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : False.
Proof. exact (@lem1159700 _27204 _27220 x t h h2 h3 (@lem1159692 _27204 _27220 t x h1)). Qed.
Lemma lem1159704 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : term195.
Proof. exact (fun h0 : ~ False => @lem1159703 _27204 _27220 x t h h1 h2 h3). Qed.
Lemma lem1159706 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1159707 : term195 = False.
Proof. exact (@lem1159706 False). Qed.
Lemma lem1159880 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term105 _27204 _27220 x t) : term105 _27204 _27220 x t.
Proof. exact (h1). Qed.
Lemma lem1159881 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term105 _27204 _27220 x t) : term254 _27204 _27220 x t.
Proof. exact (fun h0 : term244 _27204 _27220 x t => @lem1159880 _27204 _27220 x t h1). Qed.
Lemma lem1159883 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1159884 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term254 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (@lem1159883 (term105 _27204 _27220 x t)). Qed.
Lemma lem1159885 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h1 : term105 _27204 _27220 x t) : term105 _27204 _27220 x t.
Proof. exact (EQ_MP (@lem1159884 _27204 _27220 x t) (@lem1159881 _27204 _27220 x t h1)). Qed.
Lemma lem1159888 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1159890 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term244 _27204 _27220 x t) = (term255 _27204 _27220 x t).
Proof. exact (@lem1159888 (term105 _27204 _27220 x t)). Qed.
Lemma lem1159893 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) : term255 _27204 _27220 x t.
Proof. exact (EQ_MP (@lem1159890 _27204 _27220 x t) (@lem1159357 _27204 _27220 h x t h1)). Qed.
Lemma lem1159896 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : False.
Proof. exact (@lem1159893 _27204 _27220 h x t h1 (@lem1159885 _27204 _27220 x t h2)). Qed.
Lemma lem1159897 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : term195.
Proof. exact (fun h0 : ~ False => @lem1159896 _27204 _27220 h x t h1 h2). Qed.
Lemma lem1159899 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1159900 : term195 = False.
Proof. exact (@lem1159899 False). Qed.
Lemma lem1159901 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : False.
Proof. exact (EQ_MP (@lem1159900) (@lem1159897 _27204 _27220 h x t h1 h2)). Qed.
Lemma lem1160073 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term105 _27204 _27220 x t.
Proof. exact (proj2 (@lem1158989 _27204 _27220 h x t h1)). Qed.
Lemma lem1160074 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term254 _27204 _27220 x t.
Proof. exact (fun h0 : term244 _27204 _27220 x t => @lem1160073 _27204 _27220 h x t h1). Qed.
Lemma lem1160076 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1160077 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term254 _27204 _27220 x t) = (term105 _27204 _27220 x t).
Proof. exact (@lem1160076 (term105 _27204 _27220 x t)). Qed.
Lemma lem1160078 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term105 _27204 _27220 x t.
Proof. exact (EQ_MP (@lem1160077 _27204 _27220 x t) (@lem1160074 _27204 _27220 h x t h1)). Qed.
Lemma lem1160081 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1160083 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term244 _27204 _27220 x t) = (term255 _27204 _27220 x t).
Proof. exact (@lem1160081 (term105 _27204 _27220 x t)). Qed.
Lemma lem1160086 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term255 _27204 _27220 x t.
Proof. exact (EQ_MP (@lem1160083 _27204 _27220 x t) (@lem1159387 _27204 _27220 h x t h1)). Qed.
Lemma lem1160089 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : False.
Proof. exact (@lem1160086 _27204 _27220 h x t h1 (@lem1160078 _27204 _27220 h x t h1)). Qed.
Lemma lem1160090 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : term195.
Proof. exact (fun h0 : ~ False => @lem1160089 _27204 _27220 h x t h1). Qed.
Lemma lem1160092 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1160093 : term195 = False.
Proof. exact (@lem1160092 False). Qed.
Lemma lem1160094 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term229 _27204 _27220 h x t) : False.
Proof. exact (EQ_MP (@lem1160093) (@lem1160090 _27204 _27220 h x t h1)). Qed.
Lemma lem1160095 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : False.
Proof. exact (EQ_MP (@lem1159707) (@lem1159704 _27204 _27220 x t h h1 h2 h3)). Qed.
Lemma lem1160096 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : (term105 _27204 _27220 x t) = False.
Proof. exact (prop_ext (fun h3 : term105 _27204 _27220 x t => @lem1159901 _27204 _27220 h x t h1 h2) (fun h3 : False => @lem1159359 _27204 _27220 x t h2)). Qed.
Lemma lem1160097 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : False.
Proof. exact (EQ_MP (@lem1160096 _27204 _27220 h x t h1 h2) (@lem1159359 _27204 _27220 x t h2)). Qed.
Lemma lem1160098 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : ((term225 _27204 _27220 x t) = h) = False.
Proof. exact (prop_ext (fun h4 : (term225 _27204 _27220 x t) = h => @lem1160095 _27204 _27220 x t h h1 h2 h3) (fun h4 : False => @lem1159333 _27204 _27220 x t h h3)). Qed.
Lemma lem1160099 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : False.
Proof. exact (EQ_MP (@lem1160098 _27204 _27220 x t h h1 h2 h3) (@lem1159333 _27204 _27220 x t h h3)). Qed.
Lemma lem1160100 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : (term105 _27204 _27220 x t) = False.
Proof. exact (prop_ext (fun h3 : term105 _27204 _27220 x t => @lem1160097 _27204 _27220 h x t h1 h2) (fun h3 : False => @lem1159147 _27204 _27220 x t h2)). Qed.
Lemma lem1160101 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : False.
Proof. exact (EQ_MP (@lem1160100 _27204 _27220 h x t h1 h2) (@lem1159147 _27204 _27220 x t h2)). Qed.
Lemma lem1160102 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : ((term225 _27204 _27220 x t) = h) = False.
Proof. exact (prop_ext (fun h4 : (term225 _27204 _27220 x t) = h => @lem1160099 _27204 _27220 x t h h1 h2 h3) (fun h4 : False => @lem1159072 _27204 _27220 x t h h3)). Qed.
Lemma lem1160103 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : False.
Proof. exact (EQ_MP (@lem1160102 _27204 _27220 x t h h1 h2 h3) (@lem1159072 _27204 _27220 x t h h3)). Qed.
Lemma lem1160104 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : (term105 _27204 _27220 x t) = False.
Proof. exact (prop_ext (fun h3 : term105 _27204 _27220 x t => @lem1160101 _27204 _27220 h x t h1 h2) (fun h3 : False => @lem1159147 _27204 _27220 x t h2)). Qed.
Lemma lem1160105 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term241 _27204 _27220 h x t) (h2 : term105 _27204 _27220 x t) : False.
Proof. exact (EQ_MP (@lem1160104 _27204 _27220 h x t h1 h2) (@lem1159147 _27204 _27220 x t h2)). Qed.
Lemma lem1160106 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : ((term225 _27204 _27220 x t) = h) = False.
Proof. exact (prop_ext (fun h4 : (term225 _27204 _27220 x t) = h => @lem1160103 _27204 _27220 x t h h1 h2 h3) (fun h4 : False => @lem1159072 _27204 _27220 x t h h3)). Qed.
Lemma lem1160107 {_27204 _27220 : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : (term225 _27204 _27220 x t) = h) : False.
Proof. exact (EQ_MP (@lem1160106 _27204 _27220 x t h h1 h2 h3) (@lem1159072 _27204 _27220 x t h h3)). Qed.
Lemma lem1160108 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term241 _27204 _27220 h x t) : False.
Proof. exact (or_elim (@lem1158991 _27204 _27220 h x t h3) (fun h0 : (term225 _27204 _27220 x t) = h => @lem1160107 _27204 _27220 x t h h1 h2 h0) (fun h0 : term105 _27204 _27220 x t => @lem1160105 _27204 _27220 h x t h3 h0)). Qed.
Lemma lem1160109 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : False.
Proof. exact (or_elim (@lem1158904 _27204 _27220 h x t h3) (fun h0 : term241 _27204 _27220 h x t => @lem1160108 _27204 _27220 h x t h1 h2 h0) (fun h0 : term229 _27204 _27220 h x t => @lem1160094 _27204 _27220 h x t h0)). Qed.
Lemma lem1160110 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : (term123 _27204 _27220) = False.
Proof. exact (prop_ext (fun h4 : term123 _27204 _27220 => @lem1160109 _27204 _27220 h x t h1 h2 h3) (fun h4 : False => @lem1158688 _27204 _27220 h1)). Qed.
Lemma lem1160111 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : False.
Proof. exact (EQ_MP (@lem1160110 _27204 _27220 h x t h1 h2 h3) (@lem1158688 _27204 _27220 h1)). Qed.
Lemma lem1160112 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : (term103 _27204 _27220 h x) = False.
Proof. exact (prop_ext (fun h4 : term103 _27204 _27220 h x => @lem1160111 _27204 _27220 h x t h1 h2 h3) (fun h4 : False => @lem1158638 _27204 _27220 h x h2)). Qed.
Lemma lem1160113 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : False.
Proof. exact (EQ_MP (@lem1160112 _27204 _27220 h x t h1 h2 h3) (@lem1158638 _27204 _27220 h x h2)). Qed.
Lemma lem1160114 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term128 _27204 _27220.
Proof. exact (fun h0 : term120 _27204 _27220 => @lem1160113 _27204 _27220 h x t h1 h2 h3). Qed.
Lemma lem1160115 {_27204 _27220 : Type'} : (term128 _27204 _27220) = (term129 _27204 _27220).
Proof. exact (@lem69 (term120 _27204 _27220)). Qed.
Lemma lem1160116 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term129 _27204 _27220.
Proof. exact (EQ_MP (@lem1160115 _27204 _27220) (@lem1160114 _27204 _27220 h x t h1 h2 h3)). Qed.
Lemma lem1160117 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term132 _27204 _27220 B.
Proof. exact (fun h0 : term122 _27204 _27220 B => @lem1160116 _27204 _27220 h x t h1 h2 h3). Qed.
Lemma lem1160118 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term123 _27204 _27220) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term135 _27204 _27220 B.
Proof. exact (fun h0 : term121 _27220 B => @lem1160117 _27204 _27220 B h x t h1 h2 h3). Qed.
Lemma lem1160119 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term103 _27204 _27220 h x) (h2 : term200 _27204 _27220 h x t) : term138 _27204 _27220 B.
Proof. exact (fun h0 : term123 _27204 _27220 => @lem1160118 _27204 _27220 B h x t h0 h1 h2). Qed.
Lemma lem1160120 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term103 _27204 _27220 h x) : term207 _27204 _27220 B h x t.
Proof. exact (fun h0 : term200 _27204 _27220 h x t => @lem1160119 _27204 _27220 B h x t h1 h0). Qed.
Lemma lem1160121 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term209 _27204 _27220 B h x t.
Proof. exact (fun h0 : term103 _27204 _27220 h x => @lem1160120 _27204 _27220 B t h x h0). Qed.
Lemma lem1160122 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term210 _27204 _27220 B h x t.
Proof. exact (fun h0 : term9 _27204 _27220 t => @lem1160121 _27204 _27220 B h x t). Qed.
Lemma lem1160127 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : term214 _27204 _27220 B x t.
Proof. exact (fun h : prod _27220 _27204 => @lem1160122 _27204 _27220 B h x t). Qed.
Lemma lem1160132 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term218 _27204 _27220 B t.
Proof. exact (fun x : _27220 => @lem1160127 _27204 _27220 B x t). Qed.
Lemma lem1160137 {_27204 _27220 B : Type'} : term222 _27204 _27220 B.
Proof. exact (fun t : type1641 _27204 _27220 => @lem1160132 _27204 _27220 B t). Qed.
Lemma lem1160138 {_27204 _27220 B : Type'} : term221 _27204 _27220 B.
Proof. exact (EQ_MP (@lem1158480 _27204 _27220 B) (@lem1160137 _27204 _27220 B)). Qed.
Lemma lem1160139 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term256 _27204 _27220 B t.
Proof. exact (@lem1160138 _27204 _27220 B t). Qed.
Lemma lem1160140 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : (term256 _27204 _27220 B t) = (term217 _27204 _27220 B t).
Proof. exact (eq_refl (term256 _27204 _27220 B t)). Qed.
Lemma lem1160141 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) : term217 _27204 _27220 B t.
Proof. exact (EQ_MP (@lem1160140 _27204 _27220 B t) (@lem1160139 _27204 _27220 B t)). Qed.
Lemma lem1160142 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (x : _27220) : term257 _27204 _27220 B t x.
Proof. exact (@lem1160141 _27204 _27220 B t x). Qed.
Lemma lem1160143 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : (term257 _27204 _27220 B t x) = (term213 _27204 _27220 B x t).
Proof. exact (eq_refl (term257 _27204 _27220 B t x)). Qed.
Lemma lem1160144 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) : term213 _27204 _27220 B x t.
Proof. exact (EQ_MP (@lem1160143 _27204 _27220 B x t) (@lem1160142 _27204 _27220 B t x)). Qed.
Lemma lem1160145 {_27204 _27220 B : Type'} (x : _27220) (t : type1641 _27204 _27220) (h : prod _27220 _27204) : term258 _27204 _27220 B x t h.
Proof. exact (@lem1160144 _27204 _27220 B x t h). Qed.
Lemma lem1160146 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : (term258 _27204 _27220 B x t h) = (term201 _27204 _27220 B h x t).
Proof. exact (eq_refl (term258 _27204 _27220 B x t h)). Qed.
Lemma lem1160147 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term201 _27204 _27220 B h x t.
Proof. exact (EQ_MP (@lem1160146 _27204 _27220 B h x t) (@lem1160145 _27204 _27220 B x t h)). Qed.
Lemma lem1160149 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) : term201 _27204 _27220 B h x t.
Proof. exact (@lem1158210 _27204 _27220 B h x t (@lem1160147 _27204 _27220 B h x t)). Qed.
Lemma lem1160150 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term208 _27204 _27220 B h x t.
Proof. exact (@lem1160149 _27204 _27220 B h x t (@lem1156662 _27204 _27220 t h1)). Qed.
Lemma lem1160151 {_27204 _27220 B : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : term206 _27204 _27220 B h x t.
Proof. exact (@lem1160150 _27204 _27220 B h x t h1 (@lem1156851 _27204 _27220 h x h2)). Qed.
Lemma lem1160152 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term137 _27204 _27220 B.
Proof. exact (@lem1160151 _27204 _27220 B t h x h1 h2 (@lem1158187 _27204 _27220 h x t h3)). Qed.
Lemma lem1160153 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term134 _27204 _27220 B.
Proof. exact (@lem1160152 _27204 _27220 B h x t h1 h2 h3 (@lem1158193 _27204 _27220)). Qed.
Lemma lem1160154 {_27204 _27220 B : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term131 _27204 _27220 B.
Proof. exact (@lem1160153 _27204 _27220 B h x t h1 h2 h3 (@lem1158191 _27220 B)). Qed.
Lemma lem1160155 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : term128 _27204 _27220.
Proof. exact (@lem1160154 _27204 _27220 Prop h x t h1 h2 h3 (@lem1158192 _27204 _27220 Prop)). Qed.
Lemma lem1160156 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : False.
Proof. exact (@lem1160155 _27204 _27220 h x t h1 h2 h3 (@lem1158188 _27204 _27220)). Qed.
Lemma lem1160157 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : (term200 _27204 _27220 h x t) = False.
Proof. exact (prop_ext (fun h4 : term200 _27204 _27220 h x t => @lem1160156 _27204 _27220 h x t h1 h2 h3) (fun h4 : False => @lem1158187 _27204 _27220 h x t h3)). Qed.
Lemma lem1160158 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) (h3 : term200 _27204 _27220 h x t) : False.
Proof. exact (EQ_MP (@lem1160157 _27204 _27220 h x t h1 h2 h3) (@lem1158187 _27204 _27220 h x t h3)). Qed.
Lemma lem1160159 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : term199 _27204 _27220 h x t.
Proof. exact (fun h0 : term200 _27204 _27220 h x t => @lem1160158 _27204 _27220 h x t h1 h2 h0). Qed.
Lemma lem1160160 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : (term113 _27204 _27220 h x t) = (term105 _27204 _27220 x t).
Proof. exact (EQ_MP (@lem1158186 _27204 _27220 h x t) (@lem1160159 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1160163 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : (term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1156954 _27204 _27220 t h x h1 h2) (@lem1160160 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1160164 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : (term103 _27204 _27220 h x) = ((term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t)).
Proof. exact (prop_ext (fun h3 : term103 _27204 _27220 h x => @lem1160163 _27204 _27220 t h x h1 h2) (fun h3 : (term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t) => @lem1156851 _27204 _27220 h x h2)). Qed.
Lemma lem1160165 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : term103 _27204 _27220 h x) : (term89 _27204 _27220 h x t) = (term77 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1160164 _27204 _27220 t h x h1 h2) (@lem1156851 _27204 _27220 h x h2)). Qed.
Lemma lem1160166 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term92 _27204 _27220 h x t.
Proof. exact (fun h0 : term103 _27204 _27220 h x => @lem1160165 _27204 _27220 t h x h1 h0). Qed.
Lemma lem1160167 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : (term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1156907 _27204 _27220 t h x h2) (@lem1158182 _27204 _27220 t h x h1 h2)). Qed.
Lemma lem1160168 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : ((@fst _27220 _27204 h) = x) = ((term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t)).
Proof. exact (prop_ext (fun h3 : (@fst _27220 _27204 h) = x => @lem1160167 _27204 _27220 t h x h1 h2) (fun h3 : (term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t) => @lem1156834 _27204 _27220 h x h2)). Qed.
Lemma lem1160169 {_27204 _27220 : Type'} (t : type1641 _27204 _27220) (h : prod _27220 _27204) (x : _27220) (h1 : term9 _27204 _27220 t) (h2 : (@fst _27220 _27204 h) = x) : (term94 _27204 _27220 x h t) = (term77 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1160168 _27204 _27220 t h x h1 h2) (@lem1156834 _27204 _27220 h x h2)). Qed.
Lemma lem1160170 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term97 _27204 _27220 h x t.
Proof. exact (fun h0 : (@fst _27220 _27204 h) = x => @lem1160169 _27204 _27220 t h x h1 h0). Qed.
Lemma lem1160171 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term100 _27204 _27220 h x t.
Proof. exact (conj (@lem1160170 _27204 _27220 h x t h1) (@lem1160166 _27204 _27220 h x t h1)). Qed.
Lemma lem1160172 {_27204 _27220 : Type'} (h : prod _27220 _27204) (x : _27220) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : (term68 _27204 _27220 h x t) = (term77 _27204 _27220 h x t).
Proof. exact (EQ_MP (@lem1156833 _27204 _27220 h x t) (@lem1160171 _27204 _27220 h x t h1)). Qed.
Lemma lem1160177 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term80 _27204 _27220 h t.
Proof. exact (fun x : _27220 => @lem1160172 _27204 _27220 h x t h1). Qed.
Lemma lem1160178 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) (h1 : term9 _27204 _27220 t) : term13 _27204 _27220 h t.
Proof. exact (EQ_MP (@lem1156815 _27204 _27220 h t) (@lem1160177 _27204 _27220 h t h1)). Qed.
Lemma lem1160179 {_27204 _27220 : Type'} (h : prod _27220 _27204) (t : type1641 _27204 _27220) : term15 _27204 _27220 h t.
Proof. exact (fun h0 : term9 _27204 _27220 t => @lem1160178 _27204 _27220 h t h0). Qed.
Lemma lem1160184 {_27204 _27220 : Type'} (h : prod _27220 _27204) : term19 _27204 _27220 h.
Proof. exact (fun t : type1641 _27204 _27220 => @lem1160179 _27204 _27220 h t). Qed.
Lemma lem1160189 {_27204 _27220 : Type'} : term23 _27204 _27220.
Proof. exact (fun h : prod _27220 _27204 => @lem1160184 _27204 _27220 h). Qed.
Lemma lem1160190 {_27204 _27220 : Type'} : term25 _27204 _27220.
Proof. exact (conj (@lem1156718 _27204 _27220) (@lem1160189 _27204 _27220)). Qed.
Lemma lem1160191 {_27204 _27220 : Type'} : term30 _27204 _27220.
Proof. exact (@lem1156661 _27204 _27220 (@lem1160190 _27204 _27220)). Qed.

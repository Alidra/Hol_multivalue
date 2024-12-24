Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALLPAIRS_MEM_term_abbrevs.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1109872_spec.
Require Import thm1109873_spec.
Require Import thm1109884_spec.
Require Import thm1109885_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Lemma lem1177680 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1177681 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1177682 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1177681 t1) (@lem1177680 t1)). Qed.
Lemma lem1177683 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1177682 t1 t2). Qed.
Lemma lem1177684 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1177685 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1177684 t1 t2) (@lem1177683 t1 t2)). Qed.
Lemma lem1177686 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1177685 t1 t2 t3). Qed.
Lemma lem1177687 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1177688 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1177687 t1 t2 t3) (@lem1177686 t1 t2 t3)). Qed.
Lemma lem1177689 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1177688 t1 t2 t3)). Qed.
Lemma lem1177692 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem1177693 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem1177692 _26777 P l h1)). Qed.
Lemma lem1177694 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem1177695 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem1177694 _26777 l P h1)). Qed.
Lemma lem1177696 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem1177693 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem1177695 _26777 l P h1)). Qed.
Lemma lem1177697 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1177696 _26777 l P)). Qed.
Lemma lem1177698 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1177699 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem1177698 _26777) (@lem1177697 _26777 P)). Qed.
Lemma lem1177700 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1177699 _26777 P)). Qed.
Lemma lem1177701 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1177702 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem1177701 _26777) (@lem1177700 _26777)). Qed.
Lemma lem1177703 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem1177702 _26777) (@lem1138070 _26777)). Qed.
Lemma lem1177706 {_26777 : Type'} (P : _26777 -> Prop) : term16 _26777 P.
Proof. exact (@lem1177703 _26777 P). Qed.
Lemma lem1177707 {_26777 : Type'} (P : _26777 -> Prop) : (term16 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term16 _26777 P)). Qed.
Lemma lem1177708 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem1177707 _26777 P) (@lem1177706 _26777 P)). Qed.
Lemma lem1177709 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term17 _26777 P l.
Proof. exact (@lem1177708 _26777 P l). Qed.
Lemma lem1177710 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term17 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term17 _26777 P l)). Qed.
Lemma lem1177715 {A : Type'} (P : type1143 A) : term18 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1177716 {_27495 : Type'} (P : type1143 _27495) : term18 _27495 P.
Proof. exact (@lem1177715 _27495 P). Qed.
Lemma lem1177717 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term19 _27494 _27495 P.
Proof. exact (@lem1177716 _27495 (term20 _27494 _27495 P)). Qed.
Lemma lem1177718 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term21 _27494 _27495 P) = (term22 _27494 _27495 P).
Proof. exact (eq_refl (term21 _27494 _27495 P)). Qed.
Lemma lem1177719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1177720 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term23 _27494 _27495 P) = (term24 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177719) (@lem1177718 _27494 _27495 P)). Qed.
Lemma lem1177721 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term25 _27494 _27495 P t) = (term26 _27494 _27495 P t).
Proof. exact (eq_refl (term25 _27494 _27495 P t)). Qed.
Lemma lem1177722 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1177723 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term27 _27494 _27495 P t) = (term28 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1177722) (@lem1177721 _27494 _27495 P t)). Qed.
Lemma lem1177724 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (t : list _27495) : (term29 _27494 _27495 P h t) = (term30 _27494 _27495 P h t).
Proof. exact (eq_refl (term29 _27494 _27495 P h t)). Qed.
Lemma lem1177725 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (t : list _27495) : (term31 _27494 _27495 P h t) = (term32 _27494 _27495 P h t).
Proof. exact (MK_COMB (@lem1177723 _27494 _27495 P t) (@lem1177724 _27494 _27495 P h t)). Qed.
Lemma lem1177726 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) : (term33 _27494 _27495 P h) = (term34 _27494 _27495 P h).
Proof. exact (fun_ext (fun t : list _27495 => @lem1177725 _27494 _27495 P h t)). Qed.
Lemma lem1177727 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1177728 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) : (term35 _27494 _27495 P h) = (term36 _27494 _27495 P h).
Proof. exact (MK_COMB (@lem1177727 _27495) (@lem1177726 _27494 _27495 P h)). Qed.
Lemma lem1177729 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term37 _27494 _27495 P) = (term38 _27494 _27495 P).
Proof. exact (fun_ext (fun h : _27495 => @lem1177728 _27494 _27495 P h)). Qed.
Lemma lem1177730 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1177731 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term39 _27494 _27495 P) = (term40 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177730 _27495) (@lem1177729 _27494 _27495 P)). Qed.
Lemma lem1177732 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term41 _27494 _27495 P) = (term42 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177720 _27494 _27495 P) (@lem1177731 _27494 _27495 P)). Qed.
Lemma lem1177733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1177734 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term43 _27494 _27495 P) = (term44 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177733) (@lem1177732 _27494 _27495 P)). Qed.
Lemma lem1177735 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) : (term25 _27494 _27495 P l) = (term26 _27494 _27495 P l).
Proof. exact (eq_refl (term25 _27494 _27495 P l)). Qed.
Lemma lem1177736 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term45 _27494 _27495 P) = (term20 _27494 _27495 P).
Proof. exact (fun_ext (fun l : list _27495 => @lem1177735 _27494 _27495 P l)). Qed.
Lemma lem1177737 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1177738 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term46 _27494 _27495 P) = (term47 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177737 _27495) (@lem1177736 _27494 _27495 P)). Qed.
Lemma lem1177739 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term19 _27494 _27495 P) = (term48 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1177734 _27494 _27495 P) (@lem1177738 _27494 _27495 P)). Qed.
Lemma lem1177740 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term48 _27494 _27495 P.
Proof. exact (EQ_MP (@lem1177739 _27494 _27495 P) (@lem1177717 _27494 _27495 P)). Qed.
Lemma lem1177741 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term26 _27494 _27495 P t.
Proof. exact (h1). Qed.
Lemma lem1177761 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1177762 {_27495 : Type'} (x : _27495) : (@List.In _27495 x (@nil _27495)) = False.
Proof. exact (@lem1177761 _27495 x). Qed.
Lemma lem1177763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1177764 {_27495 : Type'} (x : _27495) : (term49 _27495 x) = (and False).
Proof. exact (MK_COMB (@lem1177763) (@lem1177762 _27495 x)). Qed.
Lemma lem1177765 {_27494 : Type'} (y : _27494) (m : list _27494) : (@List.In _27494 y m) = (@List.In _27494 y m).
Proof. exact (eq_refl (@List.In _27494 y m)). Qed.
Lemma lem1177766 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (m : list _27494) : (term50 _27494 _27495 x y m) = (term51 _27494 y m).
Proof. exact (MK_COMB (@lem1177764 _27495 x) (@lem1177765 _27494 y m)). Qed.
Lemma lem1177768 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1177769 {_27494 : Type'} (y : _27494) (m : list _27494) : (term51 _27494 y m) = False.
Proof. exact (@lem1177768 (@List.In _27494 y m)). Qed.
Lemma lem1177770 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (m : list _27494) : (term50 _27494 _27495 x y m) = False.
Proof. exact (TRANS (@lem1177766 _27494 _27495 x y m) (@lem1177769 _27494 y m)). Qed.
Lemma lem1177771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1177772 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (m : list _27494) : (term52 _27494 _27495 x y m) = (imp False).
Proof. exact (MK_COMB (@lem1177771) (@lem1177770 _27494 _27495 x y m)). Qed.
Lemma lem1177773 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1177774 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term53 _27494 _27495 m P x y) = (term54 _27494 _27495 P x y).
Proof. exact (MK_COMB (@lem1177772 _27494 _27495 x y m) (@lem1177773 _27494 _27495 P x y)). Qed.
Lemma lem1177776 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1177777 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term54 _27494 _27495 P x y) = True.
Proof. exact (@lem1177776 (P x y)). Qed.
Lemma lem1177778 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term53 _27494 _27495 m P x y) = True.
Proof. exact (TRANS (@lem1177774 _27494 _27495 m P x y) (@lem1177777 _27494 _27495 P x y)). Qed.
Lemma lem1177779 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term55 _27494 _27495 m P x) = (term56 _27494).
Proof. exact (fun_ext (fun y : _27494 => @lem1177778 _27494 _27495 m P x y)). Qed.
Lemma lem1177780 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1177781 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term57 _27494 _27495 m P x) = (term58 _27494).
Proof. exact (MK_COMB (@lem1177780 _27494) (@lem1177779 _27494 _27495 m P x)). Qed.
Lemma lem1177783 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1177784 {_27494 : Type'} (t : Prop) : (term59 _27494 t) = t.
Proof. exact (@lem1177783 _27494 t). Qed.
Lemma lem1177785 {_27494 : Type'} : (term58 _27494) = True.
Proof. exact (@lem1177784 _27494 True). Qed.
Lemma lem1177786 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term57 _27494 _27495 m P x) = True.
Proof. exact (TRANS (@lem1177781 _27494 _27495 m P x) (@lem1177785 _27494)). Qed.
Lemma lem1177787 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) : (term60 _27494 _27495 m P) = (term56 _27495).
Proof. exact (fun_ext (fun x : _27495 => @lem1177786 _27494 _27495 m P x)). Qed.
Lemma lem1177788 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1177789 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) : (term61 _27494 _27495 m P) = (term58 _27495).
Proof. exact (MK_COMB (@lem1177788 _27495) (@lem1177787 _27494 _27495 m P)). Qed.
Lemma lem1177791 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1177792 {_27495 : Type'} (t : Prop) : (term59 _27495 t) = t.
Proof. exact (@lem1177791 _27495 t). Qed.
Lemma lem1177793 {_27495 : Type'} : (term58 _27495) = True.
Proof. exact (@lem1177792 _27495 True). Qed.
Lemma lem1177794 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) : (term61 _27494 _27495 m P) = True.
Proof. exact (TRANS (@lem1177789 _27494 _27495 m P) (@lem1177793 _27495)). Qed.
Lemma lem1177795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1177796 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) : (term62 _27494 _27495 m P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1177795) (@lem1177794 _27494 _27495 m P)). Qed.
Lemma lem1177798 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
Lemma lem1177799 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (l : list _27494) : (@ALLPAIRS _27494 _27495 f (@nil _27495) l) = True.
Proof. exact (@lem1177798 _27494 _27495 f l). Qed.
Lemma lem1177800 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P (@nil _27495) m) = True.
Proof. exact (@lem1177799 _27494 _27495 P m). Qed.
Lemma lem1177801 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (m : list _27494) : ((term61 _27494 _27495 m P) = (@ALLPAIRS _27494 _27495 P (@nil _27495) m)) = (True = True).
Proof. exact (MK_COMB (@lem1177796 _27494 _27495 m P) (@lem1177800 _27494 _27495 P m)). Qed.
Lemma lem1177803 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1177804 : (True = True) = True.
Proof. exact (@lem1177803 True). Qed.
Lemma lem1177805 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (m : list _27494) : ((term61 _27494 _27495 m P) = (@ALLPAIRS _27494 _27495 P (@nil _27495) m)) = True.
Proof. exact (TRANS (@lem1177801 _27494 _27495 P m) (@lem1177804)). Qed.
Lemma lem1177806 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term63 _27494 _27495 P) = (term64 _27494).
Proof. exact (fun_ext (fun m : list _27494 => @lem1177805 _27494 _27495 P m)). Qed.
Lemma lem1177807 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1177808 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term22 _27494 _27495 P) = (term65 _27494).
Proof. exact (MK_COMB (@lem1177807 _27494) (@lem1177806 _27494 _27495 P)). Qed.
Lemma lem1177810 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1177811 {_27494 : Type'} (t : Prop) : (term66 _27494 t) = t.
Proof. exact (@lem1177810 (list _27494) t). Qed.
Lemma lem1177812 {_27494 : Type'} : (term65 _27494) = True.
Proof. exact (@lem1177811 _27494 True). Qed.
Lemma lem1177813 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term22 _27494 _27495 P) = True.
Proof. exact (TRANS (@lem1177808 _27494 _27495 P) (@lem1177812 _27494)). Qed.
Lemma lem1177814 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : True = (term22 _27494 _27495 P).
Proof. exact (SYM (@lem1177813 _27494 _27495 P)). Qed.
Lemma lem1177815 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term22 _27494 _27495 P.
Proof. exact (EQ_MP (@lem1177814 _27494 _27495 P) (@lem0)). Qed.
Lemma lem1177835 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term67 _25376 x h t) = (term68 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1177836 {_27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) : (term67 _27495 x h t) = (term68 _27495 h x t).
Proof. exact (@lem1177835 _27495 h x t). Qed.
Lemma lem1177841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1177842 {_27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) : (term69 _27495 x h t) = (term70 _27495 h x t).
Proof. exact (MK_COMB (@lem1177841) (@lem1177836 _27495 h x t)). Qed.
Lemma lem1177843 {_27494 : Type'} (y : _27494) (m : list _27494) : (@List.In _27494 y m) = (@List.In _27494 y m).
Proof. exact (eq_refl (@List.In _27494 y m)). Qed.
Lemma lem1177844 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term71 _27494 _27495 x h t y m) = (term72 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1177842 _27495 h x t) (@lem1177843 _27494 y m)). Qed.
Lemma lem1177847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1177848 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term73 _27494 _27495 x h t y m) = (term74 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1177847) (@lem1177844 _27494 _27495 h x t y m)). Qed.
Lemma lem1177849 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1177850 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term75 _27494 _27495 h t m P x y) = (term76 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1177848 _27494 _27495 h x t y m) (@lem1177849 _27494 _27495 P x y)). Qed.
Lemma lem1177853 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term77 _27494 _27495 h t m P x) = (term78 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1177850 _27494 _27495 h t m P x y)). Qed.
Lemma lem1177854 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1177855 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term79 _27494 _27495 h t m P x) = (term80 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1177854 _27494) (@lem1177853 _27494 _27495 h t m P x)). Qed.
Lemma lem1177860 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term81 _27494 _27495 h t m P) = (term82 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1177855 _27494 _27495 h t m P x)). Qed.
Lemma lem1177861 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1177862 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term83 _27494 _27495 h t m P) = (term84 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1177861 _27495) (@lem1177860 _27494 _27495 h t m P)). Qed.
Lemma lem1177867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1177868 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term85 _27494 _27495 h t m P) = (term86 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1177867) (@lem1177862 _27494 _27495 h t m P)). Qed.
Lemma lem1177870 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term87 _25786 _25787 f h t l) = (term88 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1177871 {_27494 _27495 : Type'} (h : _27495) (f : type1470 _27494 _27495) (t : list _27495) (l : list _27494) : (term87 _27494 _27495 f h t l) = (term88 _27494 _27495 h f t l).
Proof. exact (@lem1177870 _27494 _27495 h f t l). Qed.
Lemma lem1177872 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term87 _27494 _27495 P h t m) = (term88 _27494 _27495 h P t m).
Proof. exact (@lem1177871 _27494 _27495 h P t m). Qed.
Lemma lem1177876 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1177710 _26777 l P) (@lem1177709 _26777 P l)). Qed.
Lemma lem1177877 {_27494 : Type'} (l : list _27494) (P : _27494 -> Prop) : (@List.Forall _27494 P l) = (term7 _27494 l P).
Proof. exact (@lem1177876 _27494 l P). Qed.
Lemma lem1177878 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term89 _27494 _27495 P h m) = (term90 _27494 _27495 m P h).
Proof. exact (@lem1177877 _27494 m (P h)). Qed.
Lemma lem1177885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1177886 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term91 _27494 _27495 P h m) = (term92 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1177885) (@lem1177878 _27494 _27495 m P h)). Qed.
Lemma lem1177887 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1177888 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term88 _27494 _27495 h P t m) = (term93 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1177886 _27494 _27495 m P h) (@lem1177887 _27494 _27495 P t m)). Qed.
Lemma lem1177891 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term87 _27494 _27495 P h t m) = (term93 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1177872 _27494 _27495 h P t m) (@lem1177888 _27494 _27495 h P t m)). Qed.
Lemma lem1177892 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term83 _27494 _27495 h t m P) = (term87 _27494 _27495 P h t m)) = ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1177868 _27494 _27495 h t m P) (@lem1177891 _27494 _27495 h P t m)). Qed.
Lemma lem1177895 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term94 _27494 _27495 P h t) = (term95 _27494 _27495 h P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1177892 _27494 _27495 h P t m)). Qed.
Lemma lem1177896 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1177897 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term30 _27494 _27495 P h t) = (term96 _27494 _27495 h P t).
Proof. exact (MK_COMB (@lem1177896 _27494) (@lem1177895 _27494 _27495 h P t)). Qed.
Lemma lem1177902 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (t : list _27495) : (term96 _27494 _27495 h P t) = (term30 _27494 _27495 P h t).
Proof. exact (SYM (@lem1177897 _27494 _27495 h P t)). Qed.
Lemma lem1177904 (p : Prop) : p = (term97 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1177905 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term96 _27494 _27495 h P t) = (term98 _27494 _27495 h P t).
Proof. exact (@lem1177904 (term96 _27494 _27495 h P t)). Qed.
Lemma lem1177906 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term98 _27494 _27495 h P t) = (term96 _27494 _27495 h P t).
Proof. exact (SYM (@lem1177905 _27494 _27495 h P t)). Qed.
Lemma lem1177907 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term99 _27494 _27495 h P t) : term99 _27494 _27495 h P t.
Proof. exact (h1). Qed.
Lemma lem1177910 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term100 _27494 _27495 h P t) : term100 _27494 _27495 h P t.
Proof. exact (h1). Qed.
Lemma lem1177911 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term101 _27494 _27495 h P t.
Proof. exact (fun h0 : term100 _27494 _27495 h P t => @lem1177910 _27494 _27495 h P t h0). Qed.
Lemma lem1177912 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term101 _27494 _27495 h P t) : term101 _27494 _27495 h P t.
Proof. exact (h1). Qed.
Lemma lem1177913 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term100 _27494 _27495 h P t) : term100 _27494 _27495 h P t.
Proof. exact (h1). Qed.
Lemma lem1177914 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term100 _27494 _27495 h P t) (h2 : term101 _27494 _27495 h P t) : term100 _27494 _27495 h P t.
Proof. exact (@lem1177912 _27494 _27495 h P t h2 (@lem1177913 _27494 _27495 h P t h1)). Qed.
Lemma lem1177915 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term100 _27494 _27495 h P t) : term102 _27494 _27495 h P t.
Proof. exact (fun h0 : term101 _27494 _27495 h P t => @lem1177914 _27494 _27495 h P t h1 h0). Qed.
Lemma lem1177916 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term101 _27494 _27495 h P t) : term101 _27494 _27495 h P t.
Proof. exact (h1). Qed.
Lemma lem1177917 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term100 _27494 _27495 h P t) (h2 : term101 _27494 _27495 h P t) : term100 _27494 _27495 h P t.
Proof. exact (@lem1177915 _27494 _27495 h P t h1 (@lem1177916 _27494 _27495 h P t h2)). Qed.
Lemma lem1177918 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term101 _27494 _27495 h P t) : term101 _27494 _27495 h P t.
Proof. exact (fun h0 : term100 _27494 _27495 h P t => @lem1177917 _27494 _27495 h P t h0 h1). Qed.
Lemma lem1177919 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term103 _27494 _27495 h P t.
Proof. exact (fun h0 : term101 _27494 _27495 h P t => @lem1177918 _27494 _27495 h P t h0). Qed.
Lemma lem1177922 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term101 _27494 _27495 h P t.
Proof. exact (@lem1177919 _27494 _27495 h P t (@lem1177911 _27494 _27495 h P t)). Qed.
Lemma lem1177923 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term101 _27494 _27495 h P t.
Proof. exact (@lem1177922 _27494 _27495 h P t). Qed.
Lemma lem1177955 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1177956 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term98 _27494 _27495 h P t) = (term104 _27494 _27495 h P t).
Proof. exact (@lem1177955 (term99 _27494 _27495 h P t)). Qed.
Lemma lem1177958 (t : Prop) : (term105 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1177959 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term104 _27494 _27495 h P t) = (term96 _27494 _27495 h P t).
Proof. exact (@lem1177958 (term96 _27494 _27495 h P t)). Qed.
Lemma lem1177964 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term98 _27494 _27495 h P t) = (term96 _27494 _27495 h P t).
Proof. exact (TRANS (@lem1177956 _27494 _27495 h P t) (@lem1177959 _27494 _27495 h P t)). Qed.
Lemma lem1177987 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term28 _27494 _27495 P t) = (term28 _27494 _27495 P t).
Proof. exact (eq_refl (term28 _27494 _27495 P t)). Qed.
Lemma lem1177988 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term100 _27494 _27495 h P t) = (term106 _27494 _27495 h P t).
Proof. exact (MK_COMB (@lem1177987 _27494 _27495 P t) (@lem1177964 _27494 _27495 h P t)). Qed.
Lemma lem1177991 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term107 _27494 _27495 P t) = (term108 _27494 _27495 P t).
Proof. exact (fun_ext (fun h : _27495 => @lem1177988 _27494 _27495 h P t)). Qed.
Lemma lem1177992 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1177993 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term109 _27494 _27495 P t) = (term110 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1177992 _27495) (@lem1177991 _27494 _27495 P t)). Qed.
Lemma lem1177998 {_27494 _27495 : Type'} (t : list _27495) : (term111 _27494 _27495 t) = (term112 _27494 _27495 t).
Proof. exact (fun_ext (fun P : type1470 _27494 _27495 => @lem1177993 _27494 _27495 P t)). Qed.
Lemma lem1177999 {_27494 _27495 : Type'} : (@all (_27495 -> _27494 -> Prop)) = (@all (_27495 -> _27494 -> Prop)).
Proof. exact (eq_refl (@all (_27495 -> _27494 -> Prop))). Qed.
Lemma lem1178000 {_27494 _27495 : Type'} (t : list _27495) : (term113 _27494 _27495 t) = (term114 _27494 _27495 t).
Proof. exact (MK_COMB (@lem1177999 _27494 _27495) (@lem1177998 _27494 _27495 t)). Qed.
Lemma lem1178005 {_27494 _27495 : Type'} : (term115 _27494 _27495) = (term116 _27494 _27495).
Proof. exact (fun_ext (fun t : list _27495 => @lem1178000 _27494 _27495 t)). Qed.
Lemma lem1178006 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1178015 {_27494 _27495 : Type'} : (term117 _27494 _27495) = (term118 _27494 _27495).
Proof. exact (MK_COMB (@lem1178006 _27495) (@lem1178005 _27494 _27495)). Qed.
Lemma lem1178016 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178021 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term119 _27494 _27495 m P h x) = (term119 _27494 _27495 m P h x).
Proof. exact (eq_refl (term119 _27494 _27495 m P h x)). Qed.
Lemma lem1178022 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term120 _27494 _27495 m P h) = (term120 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1178021 _27494 _27495 m P h x)). Qed.
Lemma lem1178023 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178024 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term90 _27494 _27495 m P h) = (term90 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178023 _27494) (@lem1178022 _27494 _27495 m P h)). Qed.
Lemma lem1178025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178026 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term92 _27494 _27495 m P h) = (term92 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178025) (@lem1178024 _27494 _27495 m P h)). Qed.
Lemma lem1178027 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term93 _27494 _27495 h P t m) = (term93 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178026 _27494 _27495 m P h) (@lem1178016 _27494 _27495 P t m)). Qed.
Lemma lem1178040 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term76 _27494 _27495 h t m P x y) = (term76 _27494 _27495 h t m P x y).
Proof. exact (eq_refl (term76 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178041 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term78 _27494 _27495 h t m P x) = (term78 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178040 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178042 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178043 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term80 _27494 _27495 h t m P x) = (term80 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1178042 _27494) (@lem1178041 _27494 _27495 h t m P x)). Qed.
Lemma lem1178044 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term82 _27494 _27495 h t m P) = (term82 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178043 _27494 _27495 h t m P x)). Qed.
Lemma lem1178045 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1178046 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term84 _27494 _27495 h t m P) = (term84 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178045 _27495) (@lem1178044 _27494 _27495 h t m P)). Qed.
Lemma lem1178047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178048 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term86 _27494 _27495 h t m P) = (term86 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178047) (@lem1178046 _27494 _27495 h t m P)). Qed.
Lemma lem1178049 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m)) = ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1178048 _27494 _27495 h t m P) (@lem1178027 _27494 _27495 h P t m)). Qed.
Lemma lem1178050 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term95 _27494 _27495 h P t) = (term95 _27494 _27495 h P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178049 _27494 _27495 h P t m)). Qed.
Lemma lem1178051 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178052 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term96 _27494 _27495 h P t) = (term96 _27494 _27495 h P t).
Proof. exact (MK_COMB (@lem1178051 _27494) (@lem1178050 _27494 _27495 h P t)). Qed.
Lemma lem1178053 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178062 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term121 _27494 _27495 t m P x y) = (term121 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term121 _27494 _27495 t m P x y)). Qed.
Lemma lem1178063 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term122 _27494 _27495 t m P x) = (term122 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178062 _27494 _27495 t m P x y)). Qed.
Lemma lem1178064 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178065 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term123 _27494 _27495 t m P x) = (term123 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178064 _27494) (@lem1178063 _27494 _27495 t m P x)). Qed.
Lemma lem1178066 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term124 _27494 _27495 t m P) = (term124 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178065 _27494 _27495 t m P x)). Qed.
Lemma lem1178067 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1178068 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term125 _27494 _27495 t m P) = (term125 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178067 _27495) (@lem1178066 _27494 _27495 t m P)). Qed.
Lemma lem1178069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178070 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term126 _27494 _27495 t m P) = (term126 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178069) (@lem1178068 _27494 _27495 t m P)). Qed.
Lemma lem1178071 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term125 _27494 _27495 t m P) = (@ALLPAIRS _27494 _27495 P t m)) = ((term125 _27494 _27495 t m P) = (@ALLPAIRS _27494 _27495 P t m)).
Proof. exact (MK_COMB (@lem1178070 _27494 _27495 t m P) (@lem1178053 _27494 _27495 P t m)). Qed.
Lemma lem1178072 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term127 _27494 _27495 P t) = (term127 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178071 _27494 _27495 P t m)). Qed.
Lemma lem1178073 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178074 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term26 _27494 _27495 P t) = (term26 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178073 _27494) (@lem1178072 _27494 _27495 P t)). Qed.
Lemma lem1178075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1178076 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term28 _27494 _27495 P t) = (term28 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178075) (@lem1178074 _27494 _27495 P t)). Qed.
Lemma lem1178077 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term106 _27494 _27495 h P t) = (term106 _27494 _27495 h P t).
Proof. exact (MK_COMB (@lem1178076 _27494 _27495 P t) (@lem1178052 _27494 _27495 h P t)). Qed.
Lemma lem1178078 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term108 _27494 _27495 P t) = (term108 _27494 _27495 P t).
Proof. exact (fun_ext (fun h : _27495 => @lem1178077 _27494 _27495 h P t)). Qed.
Lemma lem1178079 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1178080 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term110 _27494 _27495 P t) = (term110 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178079 _27495) (@lem1178078 _27494 _27495 P t)). Qed.
Lemma lem1178081 {_27494 _27495 : Type'} (t : list _27495) : (term112 _27494 _27495 t) = (term112 _27494 _27495 t).
Proof. exact (fun_ext (fun P : type1470 _27494 _27495 => @lem1178080 _27494 _27495 P t)). Qed.
Lemma lem1178082 {_27494 _27495 : Type'} : (@all (_27495 -> _27494 -> Prop)) = (@all (_27495 -> _27494 -> Prop)).
Proof. exact (eq_refl (@all (_27495 -> _27494 -> Prop))). Qed.
Lemma lem1178083 {_27494 _27495 : Type'} (t : list _27495) : (term114 _27494 _27495 t) = (term114 _27494 _27495 t).
Proof. exact (MK_COMB (@lem1178082 _27494 _27495) (@lem1178081 _27494 _27495 t)). Qed.
Lemma lem1178084 {_27494 _27495 : Type'} : (term116 _27494 _27495) = (term116 _27494 _27495).
Proof. exact (fun_ext (fun t : list _27495 => @lem1178083 _27494 _27495 t)). Qed.
Lemma lem1178085 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1178086 {_27494 _27495 : Type'} : (term118 _27494 _27495) = (term118 _27494 _27495).
Proof. exact (MK_COMB (@lem1178085 _27495) (@lem1178084 _27494 _27495)). Qed.
Lemma lem1178165 {_27494 _27495 : Type'} : (term117 _27494 _27495) = (term118 _27494 _27495).
Proof. exact (TRANS (@lem1178015 _27494 _27495) (@lem1178086 _27494 _27495)). Qed.
Lemma lem1178166 {_27494 _27495 : Type'} : (term118 _27494 _27495) = (term117 _27494 _27495).
Proof. exact (SYM (@lem1178165 _27494 _27495)). Qed.
Lemma lem1178167 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term26 _27494 _27495 P t.
Proof. exact (h1). Qed.
Lemma lem1178169 (p : Prop) : p = (term97 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1178170 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m)) = (term128 _27494 _27495 h P t m).
Proof. exact (@lem1178169 ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m))). Qed.
Lemma lem1178171 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term128 _27494 _27495 h P t m) = ((term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m)).
Proof. exact (SYM (@lem1178170 _27494 _27495 h P t m)). Qed.
Lemma lem1178172 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term129 _27494 _27495 h P t m) : term129 _27494 _27495 h P t m.
Proof. exact (h1). Qed.
Lemma lem1178181 {_27494 _27495 : Type'} (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term130 _27494 _27495 x t y m) = (term131 _27494 _27495 x t y m).
Proof. exact (@lem17045 (@List.In _27495 x t) (@List.In _27494 y m)). Qed.
Lemma lem1178186 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1178191 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term132 _27494 _27495 t m P x y) = (term133 _27494 _27495 t m P x y).
Proof. exact (@lem17362 (term134 _27494 _27495 x t y m) (P x y)). Qed.
Lemma lem1178192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178193 {_27494 _27495 : Type'} (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term135 _27494 _27495 x t y m) = (term136 _27494 _27495 x t y m).
Proof. exact (MK_COMB (@lem1178192) (@lem1178181 _27494 _27495 x t y m)). Qed.
Lemma lem1178194 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term137 _27494 _27495 t m P x y) = (term138 _27494 _27495 t m P x y).
Proof. exact (MK_COMB (@lem1178193 _27494 _27495 x t y m) (@lem1178186 _27494 _27495 P x y)). Qed.
Lemma lem1178195 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term121 _27494 _27495 t m P x y) = (term137 _27494 _27495 t m P x y).
Proof. exact (@lem17265 (term134 _27494 _27495 x t y m) (P x y)). Qed.
Lemma lem1178196 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term121 _27494 _27495 t m P x y) = (term138 _27494 _27495 t m P x y).
Proof. exact (TRANS (@lem1178195 _27494 _27495 t m P x y) (@lem1178194 _27494 _27495 t m P x y)). Qed.
Lemma lem1178197 {_27494 : Type'} (P : _27494 -> Prop) : (term139 _27494 P) = (term140 _27494 P).
Proof. exact (@lem18392 _27494 P). Qed.
Lemma lem1178198 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term141 _27494 _27495 t m P x) = (term142 _27494 _27495 t m P x).
Proof. exact (@lem1178197 _27494 (term122 _27494 _27495 t m P x)). Qed.
Lemma lem1178199 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term143 _27494 _27495 t m P x y) = (term121 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term143 _27494 _27495 t m P x y)). Qed.
Lemma lem1178200 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1178201 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term144 _27494 _27495 t m P x y) = (term132 _27494 _27495 t m P x y).
Proof. exact (MK_COMB (@lem1178200) (@lem1178199 _27494 _27495 t m P x y)). Qed.
Lemma lem1178202 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term144 _27494 _27495 t m P x y) = (term133 _27494 _27495 t m P x y).
Proof. exact (TRANS (@lem1178201 _27494 _27495 t m P x y) (@lem1178191 _27494 _27495 t m P x y)). Qed.
Lemma lem1178203 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term145 _27494 _27495 t m P x) = (term146 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178202 _27494 _27495 t m P x y)). Qed.
Lemma lem1178204 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178205 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term142 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178204 _27494) (@lem1178203 _27494 _27495 t m P x)). Qed.
Lemma lem1178206 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term141 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (TRANS (@lem1178198 _27494 _27495 t m P x) (@lem1178205 _27494 _27495 t m P x)). Qed.
Lemma lem1178207 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term122 _27494 _27495 t m P x) = (term148 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178196 _27494 _27495 t m P x y)). Qed.
Lemma lem1178208 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178209 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term123 _27494 _27495 t m P x) = (term149 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178208 _27494) (@lem1178207 _27494 _27495 t m P x)). Qed.
Lemma lem1178210 {_27495 : Type'} (P : _27495 -> Prop) : (term139 _27495 P) = (term140 _27495 P).
Proof. exact (@lem18392 _27495 P). Qed.
Lemma lem1178211 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term150 _27494 _27495 t m P) = (term151 _27494 _27495 t m P).
Proof. exact (@lem1178210 _27495 (term124 _27494 _27495 t m P)). Qed.
Lemma lem1178212 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term152 _27494 _27495 t m P x) = (term123 _27494 _27495 t m P x).
Proof. exact (eq_refl (term152 _27494 _27495 t m P x)). Qed.
Lemma lem1178213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1178214 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term153 _27494 _27495 t m P x) = (term141 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178213) (@lem1178212 _27494 _27495 t m P x)). Qed.
Lemma lem1178215 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term153 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (TRANS (@lem1178214 _27494 _27495 t m P x) (@lem1178206 _27494 _27495 t m P x)). Qed.
Lemma lem1178216 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term154 _27494 _27495 t m P) = (term155 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178215 _27494 _27495 t m P x)). Qed.
Lemma lem1178217 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178218 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term151 _27494 _27495 t m P) = (term156 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178217 _27495) (@lem1178216 _27494 _27495 t m P)). Qed.
Lemma lem1178219 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term150 _27494 _27495 t m P) = (term156 _27494 _27495 t m P).
Proof. exact (TRANS (@lem1178211 _27494 _27495 t m P) (@lem1178218 _27494 _27495 t m P)). Qed.
Lemma lem1178220 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term124 _27494 _27495 t m P) = (term157 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178209 _27494 _27495 t m P x)). Qed.
Lemma lem1178221 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1178222 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term125 _27494 _27495 t m P) = (term158 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178221 _27495) (@lem1178220 _27494 _27495 t m P)). Qed.
Lemma lem1178223 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1178224 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178226 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term160 _27494 _27495 t m P) = (term161 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178225) (@lem1178219 _27494 _27495 t m P)). Qed.
Lemma lem1178227 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term162 _27494 _27495 P t m) = (term163 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178226 _27494 _27495 t m P) (@lem1178224 _27494 _27495 P t m)). Qed.
Lemma lem1178228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178229 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term164 _27494 _27495 t m P) = (term165 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178228) (@lem1178222 _27494 _27495 t m P)). Qed.
Lemma lem1178230 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term166 _27494 _27495 P t m) = (term167 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178229 _27494 _27495 t m P) (@lem1178223 _27494 _27495 P t m)). Qed.
Lemma lem1178231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178232 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term168 _27494 _27495 P t m) = (term169 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178231) (@lem1178230 _27494 _27495 P t m)). Qed.
Lemma lem1178233 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term170 _27494 _27495 P t m) = (term171 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178232 _27494 _27495 P t m) (@lem1178227 _27494 _27495 P t m)). Qed.
Lemma lem1178234 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term125 _27494 _27495 t m P) = (@ALLPAIRS _27494 _27495 P t m)) = (term170 _27494 _27495 P t m).
Proof. exact (@lem17784 (term125 _27494 _27495 t m P) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178235 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term125 _27494 _27495 t m P) = (@ALLPAIRS _27494 _27495 P t m)) = (term171 _27494 _27495 P t m).
Proof. exact (TRANS (@lem1178234 _27494 _27495 P t m) (@lem1178233 _27494 _27495 P t m)). Qed.
Lemma lem1178236 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term127 _27494 _27495 P t) = (term172 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178235 _27494 _27495 P t m)). Qed.
Lemma lem1178237 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178238 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term26 _27494 _27495 P t) = (term173 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178237 _27494) (@lem1178236 _27494 _27495 P t)). Qed.
Lemma lem1178240 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1178241 {_27494 : Type'} (P : type1143 _27494) (Q : type1143 _27494) : (term176 _27494 P Q) = (term177 _27494 P Q).
Proof. exact (@lem1178240 (list _27494) P Q). Qed.
Lemma lem1178242 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term178 _27494 _27495 P t) = (term179 _27494 _27495 P t).
Proof. exact (@lem1178241 _27494 (term180 _27494 _27495 P t) (term181 _27494 _27495 P t)). Qed.
Lemma lem1178243 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term182 _27494 _27495 P t m) = (term167 _27494 _27495 P t m).
Proof. exact (eq_refl (term182 _27494 _27495 P t m)). Qed.
Lemma lem1178244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178245 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term183 _27494 _27495 P t m) = (term169 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178244) (@lem1178243 _27494 _27495 P t m)). Qed.
Lemma lem1178246 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term184 _27494 _27495 P t m) = (term163 _27494 _27495 P t m).
Proof. exact (eq_refl (term184 _27494 _27495 P t m)). Qed.
Lemma lem1178247 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term185 _27494 _27495 P t m) = (term171 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178245 _27494 _27495 P t m) (@lem1178246 _27494 _27495 P t m)). Qed.
Lemma lem1178248 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term186 _27494 _27495 P t) = (term172 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178247 _27494 _27495 P t m)). Qed.
Lemma lem1178249 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178250 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term178 _27494 _27495 P t) = (term173 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178249 _27494) (@lem1178248 _27494 _27495 P t)). Qed.
Lemma lem1178251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178252 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term187 _27494 _27495 P t) = (term188 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178251) (@lem1178250 _27494 _27495 P t)). Qed.
Lemma lem1178253 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term182 _27494 _27495 P t m) = (term167 _27494 _27495 P t m).
Proof. exact (eq_refl (term182 _27494 _27495 P t m)). Qed.
Lemma lem1178254 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term189 _27494 _27495 P t) = (term180 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178253 _27494 _27495 P t m)). Qed.
Lemma lem1178255 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178256 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term190 _27494 _27495 P t) = (term191 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178255 _27494) (@lem1178254 _27494 _27495 P t)). Qed.
Lemma lem1178257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178258 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term192 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178257) (@lem1178256 _27494 _27495 P t)). Qed.
Lemma lem1178259 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term184 _27494 _27495 P t m) = (term163 _27494 _27495 P t m).
Proof. exact (eq_refl (term184 _27494 _27495 P t m)). Qed.
Lemma lem1178260 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term194 _27494 _27495 P t) = (term181 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178259 _27494 _27495 P t m)). Qed.
Lemma lem1178261 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178262 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term195 _27494 _27495 P t) = (term196 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178261 _27494) (@lem1178260 _27494 _27495 P t)). Qed.
Lemma lem1178263 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term179 _27494 _27495 P t) = (term197 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178258 _27494 _27495 P t) (@lem1178262 _27494 _27495 P t)). Qed.
Lemma lem1178264 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : ((term178 _27494 _27495 P t) = (term179 _27494 _27495 P t)) = ((term173 _27494 _27495 P t) = (term197 _27494 _27495 P t)).
Proof. exact (MK_COMB (@lem1178252 _27494 _27495 P t) (@lem1178263 _27494 _27495 P t)). Qed.
Lemma lem1178265 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term173 _27494 _27495 P t) = (term197 _27494 _27495 P t).
Proof. exact (EQ_MP (@lem1178264 _27494 _27495 P t) (@lem1178242 _27494 _27495 P t)). Qed.
Lemma lem1178467 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1178468 {_27495 : Type'} (P : _27495 -> Prop) (Q : Prop) : (term198 _27495 P Q) = (term199 _27495 P Q).
Proof. exact (@lem1178467 _27495 P Q). Qed.
Lemma lem1178469 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term200 _27494 _27495 P t m) = (term201 _27494 _27495 P t m).
Proof. exact (@lem1178468 _27495 (term155 _27494 _27495 t m P) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178470 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term202 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (eq_refl (term202 _27494 _27495 t m P x)). Qed.
Lemma lem1178471 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term203 _27494 _27495 t m P) = (term155 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178470 _27494 _27495 t m P x)). Qed.
Lemma lem1178472 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178473 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term204 _27494 _27495 t m P) = (term156 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178472 _27495) (@lem1178471 _27494 _27495 t m P)). Qed.
Lemma lem1178474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178475 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term205 _27494 _27495 t m P) = (term161 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1178474) (@lem1178473 _27494 _27495 t m P)). Qed.
Lemma lem1178476 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178477 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term200 _27494 _27495 P t m) = (term163 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178475 _27494 _27495 t m P) (@lem1178476 _27494 _27495 P t m)). Qed.
Lemma lem1178478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178479 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term206 _27494 _27495 P t m) = (term207 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178478) (@lem1178477 _27494 _27495 P t m)). Qed.
Lemma lem1178480 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term202 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (eq_refl (term202 _27494 _27495 t m P x)). Qed.
Lemma lem1178481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178482 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term208 _27494 _27495 t m P x) = (term209 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178481) (@lem1178480 _27494 _27495 t m P x)). Qed.
Lemma lem1178483 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178484 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term210 _27494 _27495 x P t m) = (term211 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1178482 _27494 _27495 t m P x) (@lem1178483 _27494 _27495 P t m)). Qed.
Lemma lem1178485 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term212 _27494 _27495 P t m) = (term213 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1178484 _27494 _27495 x P t m)). Qed.
Lemma lem1178486 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178487 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term201 _27494 _27495 P t m) = (term214 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178486 _27495) (@lem1178485 _27494 _27495 P t m)). Qed.
Lemma lem1178488 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term200 _27494 _27495 P t m) = (term201 _27494 _27495 P t m)) = ((term163 _27494 _27495 P t m) = (term214 _27494 _27495 P t m)).
Proof. exact (MK_COMB (@lem1178479 _27494 _27495 P t m) (@lem1178487 _27494 _27495 P t m)). Qed.
Lemma lem1178489 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term163 _27494 _27495 P t m) = (term214 _27494 _27495 P t m).
Proof. exact (EQ_MP (@lem1178488 _27494 _27495 P t m) (@lem1178469 _27494 _27495 P t m)). Qed.
Lemma lem1178491 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1178492 {_27494 : Type'} (P : _27494 -> Prop) (Q : Prop) : (term198 _27494 P Q) = (term199 _27494 P Q).
Proof. exact (@lem1178491 _27494 P Q). Qed.
Lemma lem1178493 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term215 _27494 _27495 x P t m) = (term216 _27494 _27495 x P t m).
Proof. exact (@lem1178492 _27494 (term146 _27494 _27495 t m P x) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178494 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term217 _27494 _27495 t m P x y) = (term133 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term217 _27494 _27495 t m P x y)). Qed.
Lemma lem1178495 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term218 _27494 _27495 t m P x) = (term146 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178494 _27494 _27495 t m P x y)). Qed.
Lemma lem1178496 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178497 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term219 _27494 _27495 t m P x) = (term147 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178496 _27494) (@lem1178495 _27494 _27495 t m P x)). Qed.
Lemma lem1178498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178499 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term220 _27494 _27495 t m P x) = (term209 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1178498) (@lem1178497 _27494 _27495 t m P x)). Qed.
Lemma lem1178500 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178501 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term215 _27494 _27495 x P t m) = (term211 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1178499 _27494 _27495 t m P x) (@lem1178500 _27494 _27495 P t m)). Qed.
Lemma lem1178502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178503 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term221 _27494 _27495 x P t m) = (term222 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1178502) (@lem1178501 _27494 _27495 x P t m)). Qed.
Lemma lem1178504 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term217 _27494 _27495 t m P x y) = (term133 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term217 _27494 _27495 t m P x y)). Qed.
Lemma lem1178505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178506 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term223 _27494 _27495 t m P x y) = (term224 _27494 _27495 t m P x y).
Proof. exact (MK_COMB (@lem1178505) (@lem1178504 _27494 _27495 t m P x y)). Qed.
Lemma lem1178507 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178508 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term225 _27494 _27495 x y P t m) = (term226 _27494 _27495 x y P t m).
Proof. exact (MK_COMB (@lem1178506 _27494 _27495 t m P x y) (@lem1178507 _27494 _27495 P t m)). Qed.
Lemma lem1178509 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term227 _27494 _27495 x P t m) = (term228 _27494 _27495 x P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1178508 _27494 _27495 x y P t m)). Qed.
Lemma lem1178510 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178511 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term216 _27494 _27495 x P t m) = (term229 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1178510 _27494) (@lem1178509 _27494 _27495 x P t m)). Qed.
Lemma lem1178512 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term215 _27494 _27495 x P t m) = (term216 _27494 _27495 x P t m)) = ((term211 _27494 _27495 x P t m) = (term229 _27494 _27495 x P t m)).
Proof. exact (MK_COMB (@lem1178503 _27494 _27495 x P t m) (@lem1178511 _27494 _27495 x P t m)). Qed.
Lemma lem1178513 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term211 _27494 _27495 x P t m) = (term229 _27494 _27495 x P t m).
Proof. exact (EQ_MP (@lem1178512 _27494 _27495 x P t m) (@lem1178493 _27494 _27495 x P t m)). Qed.
Lemma lem1178514 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term213 _27494 _27495 P t m) = (term230 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1178513 _27494 _27495 x P t m)). Qed.
Lemma lem1178515 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178516 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term214 _27494 _27495 P t m) = (term231 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178515 _27495) (@lem1178514 _27494 _27495 P t m)). Qed.
Lemma lem1178517 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term163 _27494 _27495 P t m) = (term231 _27494 _27495 P t m).
Proof. exact (TRANS (@lem1178489 _27494 _27495 P t m) (@lem1178516 _27494 _27495 P t m)). Qed.
Lemma lem1178518 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term181 _27494 _27495 P t) = (term232 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178517 _27494 _27495 P t m)). Qed.
Lemma lem1178519 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178520 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term196 _27494 _27495 P t) = (term233 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178519 _27494) (@lem1178518 _27494 _27495 P t)). Qed.
Lemma lem1178522 {A B : Type'} (P : type1413 A B) : (term234 A B P) = (term235 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1178523 {_27494 _27495 : Type'} (P : type1137 _27494 _27495) : (term236 _27494 _27495 P) = (term237 _27494 _27495 P).
Proof. exact (@lem1178522 (list _27494) _27495 P). Qed.
Lemma lem1178524 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term238 _27494 _27495 P t) = (term239 _27494 _27495 P t).
Proof. exact (@lem1178523 _27494 _27495 (term240 _27494 _27495 P t)). Qed.
Lemma lem1178525 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term241 _27494 _27495 P t m) = (term230 _27494 _27495 P t m).
Proof. exact (eq_refl (term241 _27494 _27495 P t m)). Qed.
Lemma lem1178526 {_27495 : Type'} (x : _27495) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1178527 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x : _27495) : (term242 _27494 _27495 P t m x) = (term243 _27494 _27495 P t m x).
Proof. exact (MK_COMB (@lem1178525 _27494 _27495 P t m) (@lem1178526 _27495 x)). Qed.
Lemma lem1178528 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term243 _27494 _27495 P t m x) = (term229 _27494 _27495 x P t m).
Proof. exact (eq_refl (term243 _27494 _27495 P t m x)). Qed.
Lemma lem1178529 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term242 _27494 _27495 P t m x) = (term229 _27494 _27495 x P t m).
Proof. exact (TRANS (@lem1178527 _27494 _27495 P t m x) (@lem1178528 _27494 _27495 x P t m)). Qed.
Lemma lem1178530 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term244 _27494 _27495 P t m) = (term230 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1178529 _27494 _27495 x P t m)). Qed.
Lemma lem1178531 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178532 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term245 _27494 _27495 P t m) = (term231 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1178531 _27495) (@lem1178530 _27494 _27495 P t m)). Qed.
Lemma lem1178533 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term246 _27494 _27495 P t) = (term232 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178532 _27494 _27495 P t m)). Qed.
Lemma lem1178534 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178535 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term238 _27494 _27495 P t) = (term233 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178534 _27494) (@lem1178533 _27494 _27495 P t)). Qed.
Lemma lem1178536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178537 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term247 _27494 _27495 P t) = (term248 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178536) (@lem1178535 _27494 _27495 P t)). Qed.
Lemma lem1178538 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term241 _27494 _27495 P t m) = (term230 _27494 _27495 P t m).
Proof. exact (eq_refl (term241 _27494 _27495 P t m)). Qed.
Lemma lem1178539 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (m : list _27494) : (x m) = (x m).
Proof. exact (eq_refl (x m)). Qed.
Lemma lem1178540 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (x : type1142 _27494 _27495) (m : list _27494) : (term249 _27494 _27495 P t x m) = (term250 _27494 _27495 P t x m).
Proof. exact (MK_COMB (@lem1178538 _27494 _27495 P t m) (@lem1178539 _27494 _27495 x m)). Qed.
Lemma lem1178541 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term250 _27494 _27495 P t x m) = (term251 _27494 _27495 x P t m).
Proof. exact (eq_refl (term250 _27494 _27495 P t x m)). Qed.
Lemma lem1178542 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term249 _27494 _27495 P t x m) = (term251 _27494 _27495 x P t m).
Proof. exact (TRANS (@lem1178540 _27494 _27495 P t x m) (@lem1178541 _27494 _27495 x P t m)). Qed.
Lemma lem1178543 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term252 _27494 _27495 P t x) = (term253 _27494 _27495 x P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178542 _27494 _27495 x P t m)). Qed.
Lemma lem1178544 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178545 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term254 _27494 _27495 P t x) = (term255 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178544 _27494) (@lem1178543 _27494 _27495 x P t)). Qed.
Lemma lem1178546 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term256 _27494 _27495 P t) = (term257 _27494 _27495 P t).
Proof. exact (fun_ext (fun x : type1142 _27494 _27495 => @lem1178545 _27494 _27495 x P t)). Qed.
Lemma lem1178547 {_27494 _27495 : Type'} : (@ex ((list _27494) -> _27495)) = (@ex ((list _27494) -> _27495)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27495))). Qed.
Lemma lem1178548 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term239 _27494 _27495 P t) = (term258 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178547 _27494 _27495) (@lem1178546 _27494 _27495 P t)). Qed.
Lemma lem1178549 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : ((term238 _27494 _27495 P t) = (term239 _27494 _27495 P t)) = ((term233 _27494 _27495 P t) = (term258 _27494 _27495 P t)).
Proof. exact (MK_COMB (@lem1178537 _27494 _27495 P t) (@lem1178548 _27494 _27495 P t)). Qed.
Lemma lem1178550 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term233 _27494 _27495 P t) = (term258 _27494 _27495 P t).
Proof. exact (EQ_MP (@lem1178549 _27494 _27495 P t) (@lem1178524 _27494 _27495 P t)). Qed.
Lemma lem1178552 {A B : Type'} (P : type1413 A B) : (term234 A B P) = (term235 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1178553 {_27494 : Type'} (P : type1136 _27494) : (term259 _27494 P) = (term260 _27494 P).
Proof. exact (@lem1178552 (list _27494) _27494 P). Qed.
Lemma lem1178554 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term261 _27494 _27495 x P t) = (term262 _27494 _27495 x P t).
Proof. exact (@lem1178553 _27494 (term263 _27494 _27495 x P t)). Qed.
Lemma lem1178555 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term264 _27494 _27495 x P t m) = (term265 _27494 _27495 x P t m).
Proof. exact (eq_refl (term264 _27494 _27495 x P t m)). Qed.
Lemma lem1178556 {_27494 : Type'} (y : _27494) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1178557 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (y : _27494) : (term266 _27494 _27495 x P t m y) = (term267 _27494 _27495 x P t m y).
Proof. exact (MK_COMB (@lem1178555 _27494 _27495 x P t m) (@lem1178556 _27494 y)). Qed.
Lemma lem1178558 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term267 _27494 _27495 x P t m y) = (term268 _27494 _27495 x y P t m).
Proof. exact (eq_refl (term267 _27494 _27495 x P t m y)). Qed.
Lemma lem1178559 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term266 _27494 _27495 x P t m y) = (term268 _27494 _27495 x y P t m).
Proof. exact (TRANS (@lem1178557 _27494 _27495 x P t m y) (@lem1178558 _27494 _27495 x y P t m)). Qed.
Lemma lem1178560 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term269 _27494 _27495 x P t m) = (term265 _27494 _27495 x P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1178559 _27494 _27495 x y P t m)). Qed.
Lemma lem1178561 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178562 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term270 _27494 _27495 x P t m) = (term251 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1178561 _27494) (@lem1178560 _27494 _27495 x P t m)). Qed.
Lemma lem1178563 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term271 _27494 _27495 x P t) = (term253 _27494 _27495 x P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178562 _27494 _27495 x P t m)). Qed.
Lemma lem1178564 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178565 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term261 _27494 _27495 x P t) = (term255 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178564 _27494) (@lem1178563 _27494 _27495 x P t)). Qed.
Lemma lem1178566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178567 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term272 _27494 _27495 x P t) = (term273 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178566) (@lem1178565 _27494 _27495 x P t)). Qed.
Lemma lem1178568 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term264 _27494 _27495 x P t m) = (term265 _27494 _27495 x P t m).
Proof. exact (eq_refl (term264 _27494 _27495 x P t m)). Qed.
Lemma lem1178569 {_27494 : Type'} (y : type1141 _27494) (m : list _27494) : (y m) = (y m).
Proof. exact (eq_refl (y m)). Qed.
Lemma lem1178570 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (y : type1141 _27494) (m : list _27494) : (term274 _27494 _27495 x P t y m) = (term275 _27494 _27495 x P t y m).
Proof. exact (MK_COMB (@lem1178568 _27494 _27495 x P t m) (@lem1178569 _27494 y m)). Qed.
Lemma lem1178571 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term275 _27494 _27495 x P t y m) = (term276 _27494 _27495 x y P t m).
Proof. exact (eq_refl (term275 _27494 _27495 x P t y m)). Qed.
Lemma lem1178572 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term274 _27494 _27495 x P t y m) = (term276 _27494 _27495 x y P t m).
Proof. exact (TRANS (@lem1178570 _27494 _27495 x P t y m) (@lem1178571 _27494 _27495 x y P t m)). Qed.
Lemma lem1178573 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term277 _27494 _27495 x P t y) = (term278 _27494 _27495 x y P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1178572 _27494 _27495 x y P t m)). Qed.
Lemma lem1178574 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1178575 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term279 _27494 _27495 x P t y) = (term280 _27494 _27495 x y P t).
Proof. exact (MK_COMB (@lem1178574 _27494) (@lem1178573 _27494 _27495 x y P t)). Qed.
Lemma lem1178576 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term281 _27494 _27495 x P t) = (term282 _27494 _27495 x P t).
Proof. exact (fun_ext (fun y : type1141 _27494 => @lem1178575 _27494 _27495 x y P t)). Qed.
Lemma lem1178577 {_27494 : Type'} : (@ex ((list _27494) -> _27494)) = (@ex ((list _27494) -> _27494)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27494))). Qed.
Lemma lem1178578 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term262 _27494 _27495 x P t) = (term283 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178577 _27494) (@lem1178576 _27494 _27495 x P t)). Qed.
Lemma lem1178579 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : ((term261 _27494 _27495 x P t) = (term262 _27494 _27495 x P t)) = ((term255 _27494 _27495 x P t) = (term283 _27494 _27495 x P t)).
Proof. exact (MK_COMB (@lem1178567 _27494 _27495 x P t) (@lem1178578 _27494 _27495 x P t)). Qed.
Lemma lem1178580 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term255 _27494 _27495 x P t) = (term283 _27494 _27495 x P t).
Proof. exact (EQ_MP (@lem1178579 _27494 _27495 x P t) (@lem1178554 _27494 _27495 x P t)). Qed.
Lemma lem1178581 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term257 _27494 _27495 P t) = (term284 _27494 _27495 P t).
Proof. exact (fun_ext (fun x : type1142 _27494 _27495 => @lem1178580 _27494 _27495 x P t)). Qed.
Lemma lem1178582 {_27494 _27495 : Type'} : (@ex ((list _27494) -> _27495)) = (@ex ((list _27494) -> _27495)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27495))). Qed.
Lemma lem1178583 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term258 _27494 _27495 P t) = (term285 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178582 _27494 _27495) (@lem1178581 _27494 _27495 P t)). Qed.
Lemma lem1178584 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term233 _27494 _27495 P t) = (term285 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178550 _27494 _27495 P t) (@lem1178583 _27494 _27495 P t)). Qed.
Lemma lem1178585 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term196 _27494 _27495 P t) = (term285 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178520 _27494 _27495 P t) (@lem1178584 _27494 _27495 P t)). Qed.
Lemma lem1178586 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (eq_refl (term193 _27494 _27495 P t)). Qed.
Lemma lem1178587 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term197 _27494 _27495 P t) = (term286 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178586 _27494 _27495 P t) (@lem1178585 _27494 _27495 P t)). Qed.
Lemma lem1178589 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1178590 {_27494 _27495 : Type'} (P : Prop) (Q : type278 _27494 _27495) : (term289 _27494 _27495 P Q) = (term290 _27494 _27495 P Q).
Proof. exact (@lem1178589 (type1142 _27494 _27495) P Q). Qed.
Lemma lem1178591 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term291 _27494 _27495 P t) = (term292 _27494 _27495 P t).
Proof. exact (@lem1178590 _27494 _27495 (term191 _27494 _27495 P t) (term284 _27494 _27495 P t)). Qed.
Lemma lem1178592 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term293 _27494 _27495 P t x) = (term283 _27494 _27495 x P t).
Proof. exact (eq_refl (term293 _27494 _27495 P t x)). Qed.
Lemma lem1178593 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term294 _27494 _27495 P t) = (term284 _27494 _27495 P t).
Proof. exact (fun_ext (fun x : type1142 _27494 _27495 => @lem1178592 _27494 _27495 x P t)). Qed.
Lemma lem1178594 {_27494 _27495 : Type'} : (@ex ((list _27494) -> _27495)) = (@ex ((list _27494) -> _27495)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27495))). Qed.
Lemma lem1178595 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term295 _27494 _27495 P t) = (term285 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178594 _27494 _27495) (@lem1178593 _27494 _27495 P t)). Qed.
Lemma lem1178596 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (eq_refl (term193 _27494 _27495 P t)). Qed.
Lemma lem1178597 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term291 _27494 _27495 P t) = (term286 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178596 _27494 _27495 P t) (@lem1178595 _27494 _27495 P t)). Qed.
Lemma lem1178598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178599 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term296 _27494 _27495 P t) = (term297 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178598) (@lem1178597 _27494 _27495 P t)). Qed.
Lemma lem1178600 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term293 _27494 _27495 P t x) = (term283 _27494 _27495 x P t).
Proof. exact (eq_refl (term293 _27494 _27495 P t x)). Qed.
Lemma lem1178601 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (eq_refl (term193 _27494 _27495 P t)). Qed.
Lemma lem1178602 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term298 _27494 _27495 P t x) = (term299 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178601 _27494 _27495 P t) (@lem1178600 _27494 _27495 x P t)). Qed.
Lemma lem1178603 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term300 _27494 _27495 P t) = (term301 _27494 _27495 P t).
Proof. exact (fun_ext (fun x : type1142 _27494 _27495 => @lem1178602 _27494 _27495 x P t)). Qed.
Lemma lem1178604 {_27494 _27495 : Type'} : (@ex ((list _27494) -> _27495)) = (@ex ((list _27494) -> _27495)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27495))). Qed.
Lemma lem1178605 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term292 _27494 _27495 P t) = (term302 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178604 _27494 _27495) (@lem1178603 _27494 _27495 P t)). Qed.
Lemma lem1178606 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : ((term291 _27494 _27495 P t) = (term292 _27494 _27495 P t)) = ((term286 _27494 _27495 P t) = (term302 _27494 _27495 P t)).
Proof. exact (MK_COMB (@lem1178599 _27494 _27495 P t) (@lem1178605 _27494 _27495 P t)). Qed.
Lemma lem1178607 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term286 _27494 _27495 P t) = (term302 _27494 _27495 P t).
Proof. exact (EQ_MP (@lem1178606 _27494 _27495 P t) (@lem1178591 _27494 _27495 P t)). Qed.
Lemma lem1178609 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1178610 {_27494 : Type'} (P : Prop) (Q : type277 _27494) : (term303 _27494 P Q) = (term304 _27494 P Q).
Proof. exact (@lem1178609 (type1141 _27494) P Q). Qed.
Lemma lem1178611 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term305 _27494 _27495 x P t) = (term306 _27494 _27495 x P t).
Proof. exact (@lem1178610 _27494 (term191 _27494 _27495 P t) (term282 _27494 _27495 x P t)). Qed.
Lemma lem1178612 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term307 _27494 _27495 x P t y) = (term280 _27494 _27495 x y P t).
Proof. exact (eq_refl (term307 _27494 _27495 x P t y)). Qed.
Lemma lem1178613 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term308 _27494 _27495 x P t) = (term282 _27494 _27495 x P t).
Proof. exact (fun_ext (fun y : type1141 _27494 => @lem1178612 _27494 _27495 x y P t)). Qed.
Lemma lem1178614 {_27494 : Type'} : (@ex ((list _27494) -> _27494)) = (@ex ((list _27494) -> _27494)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27494))). Qed.
Lemma lem1178615 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term309 _27494 _27495 x P t) = (term283 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178614 _27494) (@lem1178613 _27494 _27495 x P t)). Qed.
Lemma lem1178616 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (eq_refl (term193 _27494 _27495 P t)). Qed.
Lemma lem1178617 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term305 _27494 _27495 x P t) = (term299 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178616 _27494 _27495 P t) (@lem1178615 _27494 _27495 x P t)). Qed.
Lemma lem1178618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178619 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term310 _27494 _27495 x P t) = (term311 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178618) (@lem1178617 _27494 _27495 x P t)). Qed.
Lemma lem1178620 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term307 _27494 _27495 x P t y) = (term280 _27494 _27495 x y P t).
Proof. exact (eq_refl (term307 _27494 _27495 x P t y)). Qed.
Lemma lem1178621 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term193 _27494 _27495 P t).
Proof. exact (eq_refl (term193 _27494 _27495 P t)). Qed.
Lemma lem1178622 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (y : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term312 _27494 _27495 x P t y) = (term313 _27494 _27495 x y P t).
Proof. exact (MK_COMB (@lem1178621 _27494 _27495 P t) (@lem1178620 _27494 _27495 x y P t)). Qed.
Lemma lem1178623 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term314 _27494 _27495 x P t) = (term315 _27494 _27495 x P t).
Proof. exact (fun_ext (fun y : type1141 _27494 => @lem1178622 _27494 _27495 x y P t)). Qed.
Lemma lem1178624 {_27494 : Type'} : (@ex ((list _27494) -> _27494)) = (@ex ((list _27494) -> _27494)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27494))). Qed.
Lemma lem1178625 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term306 _27494 _27495 x P t) = (term316 _27494 _27495 x P t).
Proof. exact (MK_COMB (@lem1178624 _27494) (@lem1178623 _27494 _27495 x P t)). Qed.
Lemma lem1178626 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : ((term305 _27494 _27495 x P t) = (term306 _27494 _27495 x P t)) = ((term299 _27494 _27495 x P t) = (term316 _27494 _27495 x P t)).
Proof. exact (MK_COMB (@lem1178619 _27494 _27495 x P t) (@lem1178625 _27494 _27495 x P t)). Qed.
Lemma lem1178627 {_27494 _27495 : Type'} (x : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term299 _27494 _27495 x P t) = (term316 _27494 _27495 x P t).
Proof. exact (EQ_MP (@lem1178626 _27494 _27495 x P t) (@lem1178611 _27494 _27495 x P t)). Qed.
Lemma lem1178628 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term301 _27494 _27495 P t) = (term317 _27494 _27495 P t).
Proof. exact (fun_ext (fun x : type1142 _27494 _27495 => @lem1178627 _27494 _27495 x P t)). Qed.
Lemma lem1178629 {_27494 _27495 : Type'} : (@ex ((list _27494) -> _27495)) = (@ex ((list _27494) -> _27495)).
Proof. exact (eq_refl (@ex ((list _27494) -> _27495))). Qed.
Lemma lem1178630 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term302 _27494 _27495 P t) = (term318 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1178629 _27494 _27495) (@lem1178628 _27494 _27495 P t)). Qed.
Lemma lem1178631 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term286 _27494 _27495 P t) = (term318 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178607 _27494 _27495 P t) (@lem1178630 _27494 _27495 P t)). Qed.
Lemma lem1178632 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term197 _27494 _27495 P t) = (term318 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178587 _27494 _27495 P t) (@lem1178631 _27494 _27495 P t)). Qed.
Lemma lem1178633 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term173 _27494 _27495 P t) = (term318 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178265 _27494 _27495 P t) (@lem1178632 _27494 _27495 P t)). Qed.
Lemma lem1178634 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term26 _27494 _27495 P t) = (term318 _27494 _27495 P t).
Proof. exact (TRANS (@lem1178238 _27494 _27495 P t) (@lem1178633 _27494 _27495 P t)). Qed.
Lemma lem1178635 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term318 _27494 _27495 P t.
Proof. exact (EQ_MP (@lem1178634 _27494 _27495 P t) (@lem1178167 _27494 _27495 P t h1)). Qed.
Lemma lem1178644 {_27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) : (term319 _27495 h x t) = (term320 _27495 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _27495 x t)). Qed.
Lemma lem1178648 {_27494 : Type'} (y : _27494) (m : list _27494) : (term321 _27494 y m) = (term321 _27494 y m).
Proof. exact (eq_refl (term321 _27494 y m)). Qed.
Lemma lem1178650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178651 {_27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) : (term322 _27495 h x t) = (term323 _27495 h x t).
Proof. exact (MK_COMB (@lem1178650) (@lem1178644 _27495 h x t)). Qed.
Lemma lem1178652 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term324 _27494 _27495 h x t y m) = (term325 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1178651 _27495 h x t) (@lem1178648 _27494 y m)). Qed.
Lemma lem1178653 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term326 _27494 _27495 h x t y m) = (term324 _27494 _27495 h x t y m).
Proof. exact (@lem17045 (term68 _27495 h x t) (@List.In _27494 y m)). Qed.
Lemma lem1178654 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term326 _27494 _27495 h x t y m) = (term325 _27494 _27495 h x t y m).
Proof. exact (TRANS (@lem1178653 _27494 _27495 h x t y m) (@lem1178652 _27494 _27495 h x t y m)). Qed.
Lemma lem1178659 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1178664 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term327 _27494 _27495 h t m P x y) = (term328 _27494 _27495 h t m P x y).
Proof. exact (@lem17362 (term72 _27494 _27495 h x t y m) (P x y)). Qed.
Lemma lem1178665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178666 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term329 _27494 _27495 h x t y m) = (term330 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1178665) (@lem1178654 _27494 _27495 h x t y m)). Qed.
Lemma lem1178667 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term331 _27494 _27495 h t m P x y) = (term332 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1178666 _27494 _27495 h x t y m) (@lem1178659 _27494 _27495 P x y)). Qed.
Lemma lem1178668 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term76 _27494 _27495 h t m P x y) = (term331 _27494 _27495 h t m P x y).
Proof. exact (@lem17265 (term72 _27494 _27495 h x t y m) (P x y)). Qed.
Lemma lem1178669 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term76 _27494 _27495 h t m P x y) = (term332 _27494 _27495 h t m P x y).
Proof. exact (TRANS (@lem1178668 _27494 _27495 h t m P x y) (@lem1178667 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178670 {_27494 : Type'} (P : _27494 -> Prop) : (term139 _27494 P) = (term140 _27494 P).
Proof. exact (@lem18392 _27494 P). Qed.
Lemma lem1178671 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term333 _27494 _27495 h t m P x) = (term334 _27494 _27495 h t m P x).
Proof. exact (@lem1178670 _27494 (term78 _27494 _27495 h t m P x)). Qed.
Lemma lem1178672 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term335 _27494 _27495 h t m P x y) = (term76 _27494 _27495 h t m P x y).
Proof. exact (eq_refl (term335 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1178674 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term336 _27494 _27495 h t m P x y) = (term327 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1178673) (@lem1178672 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178675 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term336 _27494 _27495 h t m P x y) = (term328 _27494 _27495 h t m P x y).
Proof. exact (TRANS (@lem1178674 _27494 _27495 h t m P x y) (@lem1178664 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178676 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term337 _27494 _27495 h t m P x) = (term338 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178675 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178677 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178678 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term334 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1178677 _27494) (@lem1178676 _27494 _27495 h t m P x)). Qed.
Lemma lem1178679 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term333 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (TRANS (@lem1178671 _27494 _27495 h t m P x) (@lem1178678 _27494 _27495 h t m P x)). Qed.
Lemma lem1178680 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term78 _27494 _27495 h t m P x) = (term340 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1178669 _27494 _27495 h t m P x y)). Qed.
Lemma lem1178681 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178682 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term80 _27494 _27495 h t m P x) = (term341 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1178681 _27494) (@lem1178680 _27494 _27495 h t m P x)). Qed.
Lemma lem1178683 {_27495 : Type'} (P : _27495 -> Prop) : (term139 _27495 P) = (term140 _27495 P).
Proof. exact (@lem18392 _27495 P). Qed.
Lemma lem1178684 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term342 _27494 _27495 h t m P) = (term343 _27494 _27495 h t m P).
Proof. exact (@lem1178683 _27495 (term82 _27494 _27495 h t m P)). Qed.
Lemma lem1178685 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term344 _27494 _27495 h t m P x) = (term80 _27494 _27495 h t m P x).
Proof. exact (eq_refl (term344 _27494 _27495 h t m P x)). Qed.
Lemma lem1178686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1178687 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term345 _27494 _27495 h t m P x) = (term333 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1178686) (@lem1178685 _27494 _27495 h t m P x)). Qed.
Lemma lem1178688 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term345 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (TRANS (@lem1178687 _27494 _27495 h t m P x) (@lem1178679 _27494 _27495 h t m P x)). Qed.
Lemma lem1178689 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term346 _27494 _27495 h t m P) = (term347 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178688 _27494 _27495 h t m P x)). Qed.
Lemma lem1178690 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1178691 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term343 _27494 _27495 h t m P) = (term348 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178690 _27495) (@lem1178689 _27494 _27495 h t m P)). Qed.
Lemma lem1178692 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term342 _27494 _27495 h t m P) = (term348 _27494 _27495 h t m P).
Proof. exact (TRANS (@lem1178684 _27494 _27495 h t m P) (@lem1178691 _27494 _27495 h t m P)). Qed.
Lemma lem1178693 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term82 _27494 _27495 h t m P) = (term349 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178682 _27494 _27495 h t m P x)). Qed.
Lemma lem1178694 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1178695 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term84 _27494 _27495 h t m P) = (term350 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178694 _27495) (@lem1178693 _27494 _27495 h t m P)). Qed.
Lemma lem1178704 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term351 _27494 _27495 m P h x) = (term352 _27494 _27495 m P h x).
Proof. exact (@lem17362 (@List.In _27494 x m) (P h x)). Qed.
Lemma lem1178709 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term119 _27494 _27495 m P h x) = (term353 _27494 _27495 m P h x).
Proof. exact (@lem17265 (@List.In _27494 x m) (P h x)). Qed.
Lemma lem1178710 {_27494 : Type'} (P : _27494 -> Prop) : (term139 _27494 P) = (term140 _27494 P).
Proof. exact (@lem18392 _27494 P). Qed.
Lemma lem1178711 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term354 _27494 _27495 m P h) = (term355 _27494 _27495 m P h).
Proof. exact (@lem1178710 _27494 (term120 _27494 _27495 m P h)). Qed.
Lemma lem1178712 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term356 _27494 _27495 m P h x) = (term119 _27494 _27495 m P h x).
Proof. exact (eq_refl (term356 _27494 _27495 m P h x)). Qed.
Lemma lem1178713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1178714 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term357 _27494 _27495 m P h x) = (term351 _27494 _27495 m P h x).
Proof. exact (MK_COMB (@lem1178713) (@lem1178712 _27494 _27495 m P h x)). Qed.
Lemma lem1178715 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term357 _27494 _27495 m P h x) = (term352 _27494 _27495 m P h x).
Proof. exact (TRANS (@lem1178714 _27494 _27495 m P h x) (@lem1178704 _27494 _27495 m P h x)). Qed.
Lemma lem1178716 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term358 _27494 _27495 m P h) = (term359 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1178715 _27494 _27495 m P h x)). Qed.
Lemma lem1178717 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178718 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term355 _27494 _27495 m P h) = (term360 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178717 _27494) (@lem1178716 _27494 _27495 m P h)). Qed.
Lemma lem1178719 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term354 _27494 _27495 m P h) = (term360 _27494 _27495 m P h).
Proof. exact (TRANS (@lem1178711 _27494 _27495 m P h) (@lem1178718 _27494 _27495 m P h)). Qed.
Lemma lem1178720 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term120 _27494 _27495 m P h) = (term361 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1178709 _27494 _27495 m P h x)). Qed.
Lemma lem1178721 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1178722 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term90 _27494 _27495 m P h) = (term362 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178721 _27494) (@lem1178720 _27494 _27495 m P h)). Qed.
Lemma lem1178723 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1178724 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178726 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term363 _27494 _27495 m P h) = (term364 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178725) (@lem1178719 _27494 _27495 m P h)). Qed.
Lemma lem1178727 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term365 _27494 _27495 h P t m) = (term366 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178726 _27494 _27495 m P h) (@lem1178723 _27494 _27495 P t m)). Qed.
Lemma lem1178728 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term367 _27494 _27495 h P t m) = (term365 _27494 _27495 h P t m).
Proof. exact (@lem17045 (term90 _27494 _27495 m P h) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1178729 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term367 _27494 _27495 h P t m) = (term366 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1178728 _27494 _27495 h P t m) (@lem1178727 _27494 _27495 h P t m)). Qed.
Lemma lem1178730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178731 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term92 _27494 _27495 m P h) = (term368 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178730) (@lem1178722 _27494 _27495 m P h)). Qed.
Lemma lem1178732 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term93 _27494 _27495 h P t m) = (term369 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178731 _27494 _27495 m P h) (@lem1178724 _27494 _27495 P t m)). Qed.
Lemma lem1178733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178734 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term370 _27494 _27495 h t m P) = (term371 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178733) (@lem1178692 _27494 _27495 h t m P)). Qed.
Lemma lem1178735 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term372 _27494 _27495 h P t m) = (term373 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178734 _27494 _27495 h t m P) (@lem1178732 _27494 _27495 h P t m)). Qed.
Lemma lem1178736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1178737 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term374 _27494 _27495 h t m P) = (term375 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1178736) (@lem1178695 _27494 _27495 h t m P)). Qed.
Lemma lem1178738 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term376 _27494 _27495 h P t m) = (term377 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178737 _27494 _27495 h t m P) (@lem1178729 _27494 _27495 h P t m)). Qed.
Lemma lem1178739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178740 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term378 _27494 _27495 h P t m) = (term379 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178739) (@lem1178738 _27494 _27495 h P t m)). Qed.
Lemma lem1178741 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term380 _27494 _27495 h P t m) = (term381 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178740 _27494 _27495 h P t m) (@lem1178735 _27494 _27495 h P t m)). Qed.
Lemma lem1178742 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term129 _27494 _27495 h P t m) = (term380 _27494 _27495 h P t m).
Proof. exact (@lem17646 (term84 _27494 _27495 h t m P) (term93 _27494 _27495 h P t m)). Qed.
Lemma lem1178743 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term129 _27494 _27495 h P t m) = (term381 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1178742 _27494 _27495 h P t m) (@lem1178741 _27494 _27495 h P t m)). Qed.
Lemma lem1178946 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1178947 {_27494 : Type'} (P : _27494 -> Prop) (Q : Prop) : (term198 _27494 P Q) = (term199 _27494 P Q).
Proof. exact (@lem1178946 _27494 P Q). Qed.
Lemma lem1178948 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term382 _27494 _27495 h P t m) = (term383 _27494 _27495 h P t m).
Proof. exact (@lem1178947 _27494 (term359 _27494 _27495 m P h) (term159 _27494 _27495 P t m)). Qed.
Lemma lem1178949 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term384 _27494 _27495 m P h x) = (term352 _27494 _27495 m P h x).
Proof. exact (eq_refl (term384 _27494 _27495 m P h x)). Qed.
Lemma lem1178950 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term385 _27494 _27495 m P h) = (term359 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1178949 _27494 _27495 m P h x)). Qed.
Lemma lem1178951 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178952 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term386 _27494 _27495 m P h) = (term360 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178951 _27494) (@lem1178950 _27494 _27495 m P h)). Qed.
Lemma lem1178953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178954 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term387 _27494 _27495 m P h) = (term364 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1178953) (@lem1178952 _27494 _27495 m P h)). Qed.
Lemma lem1178955 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1178956 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term382 _27494 _27495 h P t m) = (term366 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178954 _27494 _27495 m P h) (@lem1178955 _27494 _27495 P t m)). Qed.
Lemma lem1178957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178958 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term388 _27494 _27495 h P t m) = (term389 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178957) (@lem1178956 _27494 _27495 h P t m)). Qed.
Lemma lem1178959 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term384 _27494 _27495 m P h x) = (term352 _27494 _27495 m P h x).
Proof. exact (eq_refl (term384 _27494 _27495 m P h x)). Qed.
Lemma lem1178960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178961 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term390 _27494 _27495 m P h x) = (term391 _27494 _27495 m P h x).
Proof. exact (MK_COMB (@lem1178960) (@lem1178959 _27494 _27495 m P h x)). Qed.
Lemma lem1178962 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1178963 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term392 _27494 _27495 h x P t m) = (term393 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1178961 _27494 _27495 m P h x) (@lem1178962 _27494 _27495 P t m)). Qed.
Lemma lem1178964 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term394 _27494 _27495 h P t m) = (term395 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1178963 _27494 _27495 h x P t m)). Qed.
Lemma lem1178965 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178966 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term383 _27494 _27495 h P t m) = (term396 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178965 _27494) (@lem1178964 _27494 _27495 h P t m)). Qed.
Lemma lem1178967 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term382 _27494 _27495 h P t m) = (term383 _27494 _27495 h P t m)) = ((term366 _27494 _27495 h P t m) = (term396 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1178958 _27494 _27495 h P t m) (@lem1178966 _27494 _27495 h P t m)). Qed.
Lemma lem1178968 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term366 _27494 _27495 h P t m) = (term396 _27494 _27495 h P t m).
Proof. exact (EQ_MP (@lem1178967 _27494 _27495 h P t m) (@lem1178948 _27494 _27495 h P t m)). Qed.
Lemma lem1178969 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term375 _27494 _27495 h t m P) = (term375 _27494 _27495 h t m P).
Proof. exact (eq_refl (term375 _27494 _27495 h t m P)). Qed.
Lemma lem1178970 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term377 _27494 _27495 h P t m) = (term397 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178969 _27494 _27495 h t m P) (@lem1178968 _27494 _27495 h P t m)). Qed.
Lemma lem1178972 {A : Type'} (P : Prop) (Q : A -> Prop) : (term287 A P Q) = (term288 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1178973 {_27494 : Type'} (P : Prop) (Q : _27494 -> Prop) : (term287 _27494 P Q) = (term288 _27494 P Q).
Proof. exact (@lem1178972 _27494 P Q). Qed.
Lemma lem1178974 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term398 _27494 _27495 h P t m) = (term399 _27494 _27495 h P t m).
Proof. exact (@lem1178973 _27494 (term350 _27494 _27495 h t m P) (term395 _27494 _27495 h P t m)). Qed.
Lemma lem1178975 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term400 _27494 _27495 h P t m x) = (term393 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term400 _27494 _27495 h P t m x)). Qed.
Lemma lem1178976 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term401 _27494 _27495 h P t m) = (term395 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1178975 _27494 _27495 h x P t m)). Qed.
Lemma lem1178977 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178978 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term402 _27494 _27495 h P t m) = (term396 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178977 _27494) (@lem1178976 _27494 _27495 h P t m)). Qed.
Lemma lem1178979 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term375 _27494 _27495 h t m P) = (term375 _27494 _27495 h t m P).
Proof. exact (eq_refl (term375 _27494 _27495 h t m P)). Qed.
Lemma lem1178980 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term398 _27494 _27495 h P t m) = (term397 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178979 _27494 _27495 h t m P) (@lem1178978 _27494 _27495 h P t m)). Qed.
Lemma lem1178981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1178982 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term403 _27494 _27495 h P t m) = (term404 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178981) (@lem1178980 _27494 _27495 h P t m)). Qed.
Lemma lem1178983 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term400 _27494 _27495 h P t m x) = (term393 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term400 _27494 _27495 h P t m x)). Qed.
Lemma lem1178984 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term375 _27494 _27495 h t m P) = (term375 _27494 _27495 h t m P).
Proof. exact (eq_refl (term375 _27494 _27495 h t m P)). Qed.
Lemma lem1178985 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term405 _27494 _27495 h P t m x) = (term406 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1178984 _27494 _27495 h t m P) (@lem1178983 _27494 _27495 h x P t m)). Qed.
Lemma lem1178986 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term407 _27494 _27495 h P t m) = (term408 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1178985 _27494 _27495 h x P t m)). Qed.
Lemma lem1178987 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1178988 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term399 _27494 _27495 h P t m) = (term409 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178987 _27494) (@lem1178986 _27494 _27495 h P t m)). Qed.
Lemma lem1178989 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term398 _27494 _27495 h P t m) = (term399 _27494 _27495 h P t m)) = ((term397 _27494 _27495 h P t m) = (term409 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1178982 _27494 _27495 h P t m) (@lem1178988 _27494 _27495 h P t m)). Qed.
Lemma lem1178990 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term397 _27494 _27495 h P t m) = (term409 _27494 _27495 h P t m).
Proof. exact (EQ_MP (@lem1178989 _27494 _27495 h P t m) (@lem1178974 _27494 _27495 h P t m)). Qed.
Lemma lem1178991 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term377 _27494 _27495 h P t m) = (term409 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1178970 _27494 _27495 h P t m) (@lem1178990 _27494 _27495 h P t m)). Qed.
Lemma lem1178992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1178993 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term379 _27494 _27495 h P t m) = (term410 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178992) (@lem1178991 _27494 _27495 h P t m)). Qed.
Lemma lem1178995 {A : Type'} (P : A -> Prop) (Q : Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1178996 {_27495 : Type'} (P : _27495 -> Prop) (Q : Prop) : (term411 _27495 P Q) = (term412 _27495 P Q).
Proof. exact (@lem1178995 _27495 P Q). Qed.
Lemma lem1178997 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term413 _27494 _27495 h P t m) = (term414 _27494 _27495 h P t m).
Proof. exact (@lem1178996 _27495 (term347 _27494 _27495 h t m P) (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1178998 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term415 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (eq_refl (term415 _27494 _27495 h t m P x)). Qed.
Lemma lem1178999 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term416 _27494 _27495 h t m P) = (term347 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1178998 _27494 _27495 h t m P x)). Qed.
Lemma lem1179000 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179001 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term417 _27494 _27495 h t m P) = (term348 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179000 _27495) (@lem1178999 _27494 _27495 h t m P)). Qed.
Lemma lem1179002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179003 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term418 _27494 _27495 h t m P) = (term371 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179002) (@lem1179001 _27494 _27495 h t m P)). Qed.
Lemma lem1179004 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term369 _27494 _27495 h P t m) = (term369 _27494 _27495 h P t m).
Proof. exact (eq_refl (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1179005 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term413 _27494 _27495 h P t m) = (term373 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179003 _27494 _27495 h t m P) (@lem1179004 _27494 _27495 h P t m)). Qed.
Lemma lem1179006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179007 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term419 _27494 _27495 h P t m) = (term420 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179006) (@lem1179005 _27494 _27495 h P t m)). Qed.
Lemma lem1179008 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term415 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (eq_refl (term415 _27494 _27495 h t m P x)). Qed.
Lemma lem1179009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179010 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term421 _27494 _27495 h t m P x) = (term422 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179009) (@lem1179008 _27494 _27495 h t m P x)). Qed.
Lemma lem1179011 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term369 _27494 _27495 h P t m) = (term369 _27494 _27495 h P t m).
Proof. exact (eq_refl (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1179012 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term423 _27494 _27495 x h P t m) = (term424 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179010 _27494 _27495 h t m P x) (@lem1179011 _27494 _27495 h P t m)). Qed.
Lemma lem1179013 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term425 _27494 _27495 h P t m) = (term426 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1179012 _27494 _27495 x h P t m)). Qed.
Lemma lem1179014 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179015 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term414 _27494 _27495 h P t m) = (term427 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179014 _27495) (@lem1179013 _27494 _27495 h P t m)). Qed.
Lemma lem1179016 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term413 _27494 _27495 h P t m) = (term414 _27494 _27495 h P t m)) = ((term373 _27494 _27495 h P t m) = (term427 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1179007 _27494 _27495 h P t m) (@lem1179015 _27494 _27495 h P t m)). Qed.
Lemma lem1179017 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term373 _27494 _27495 h P t m) = (term427 _27494 _27495 h P t m).
Proof. exact (EQ_MP (@lem1179016 _27494 _27495 h P t m) (@lem1178997 _27494 _27495 h P t m)). Qed.
Lemma lem1179019 {A : Type'} (P : A -> Prop) (Q : Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1179020 {_27494 : Type'} (P : _27494 -> Prop) (Q : Prop) : (term411 _27494 P Q) = (term412 _27494 P Q).
Proof. exact (@lem1179019 _27494 P Q). Qed.
Lemma lem1179021 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term428 _27494 _27495 x h P t m) = (term429 _27494 _27495 x h P t m).
Proof. exact (@lem1179020 _27494 (term338 _27494 _27495 h t m P x) (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1179022 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term430 _27494 _27495 h t m P x y) = (term328 _27494 _27495 h t m P x y).
Proof. exact (eq_refl (term430 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179023 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term431 _27494 _27495 h t m P x) = (term338 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179022 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179024 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179025 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term432 _27494 _27495 h t m P x) = (term339 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179024 _27494) (@lem1179023 _27494 _27495 h t m P x)). Qed.
Lemma lem1179026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179027 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term433 _27494 _27495 h t m P x) = (term422 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179026) (@lem1179025 _27494 _27495 h t m P x)). Qed.
Lemma lem1179028 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term369 _27494 _27495 h P t m) = (term369 _27494 _27495 h P t m).
Proof. exact (eq_refl (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1179029 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term428 _27494 _27495 x h P t m) = (term424 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179027 _27494 _27495 h t m P x) (@lem1179028 _27494 _27495 h P t m)). Qed.
Lemma lem1179030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179031 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term434 _27494 _27495 x h P t m) = (term435 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179030) (@lem1179029 _27494 _27495 x h P t m)). Qed.
Lemma lem1179032 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term430 _27494 _27495 h t m P x y) = (term328 _27494 _27495 h t m P x y).
Proof. exact (eq_refl (term430 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179034 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term436 _27494 _27495 h t m P x y) = (term437 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1179033) (@lem1179032 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179035 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term369 _27494 _27495 h P t m) = (term369 _27494 _27495 h P t m).
Proof. exact (eq_refl (term369 _27494 _27495 h P t m)). Qed.
Lemma lem1179036 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term438 _27494 _27495 x y h P t m) = (term439 _27494 _27495 x y h P t m).
Proof. exact (MK_COMB (@lem1179034 _27494 _27495 h t m P x y) (@lem1179035 _27494 _27495 h P t m)). Qed.
Lemma lem1179037 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term440 _27494 _27495 x h P t m) = (term441 _27494 _27495 x h P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1179036 _27494 _27495 x y h P t m)). Qed.
Lemma lem1179038 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179039 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term429 _27494 _27495 x h P t m) = (term442 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179038 _27494) (@lem1179037 _27494 _27495 x h P t m)). Qed.
Lemma lem1179040 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term428 _27494 _27495 x h P t m) = (term429 _27494 _27495 x h P t m)) = ((term424 _27494 _27495 x h P t m) = (term442 _27494 _27495 x h P t m)).
Proof. exact (MK_COMB (@lem1179031 _27494 _27495 x h P t m) (@lem1179039 _27494 _27495 x h P t m)). Qed.
Lemma lem1179041 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term424 _27494 _27495 x h P t m) = (term442 _27494 _27495 x h P t m).
Proof. exact (EQ_MP (@lem1179040 _27494 _27495 x h P t m) (@lem1179021 _27494 _27495 x h P t m)). Qed.
Lemma lem1179042 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term426 _27494 _27495 h P t m) = (term443 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1179041 _27494 _27495 x h P t m)). Qed.
Lemma lem1179043 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179044 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term427 _27494 _27495 h P t m) = (term444 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179043 _27495) (@lem1179042 _27494 _27495 h P t m)). Qed.
Lemma lem1179045 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term373 _27494 _27495 h P t m) = (term444 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1179017 _27494 _27495 h P t m) (@lem1179044 _27494 _27495 h P t m)). Qed.
Lemma lem1179046 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term381 _27494 _27495 h P t m) = (term445 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1178993 _27494 _27495 h P t m) (@lem1179045 _27494 _27495 h P t m)). Qed.
Lemma lem1179050 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1179051 {_27494 : Type'} (P : _27494 -> Prop) (Q : Prop) : (term198 _27494 P Q) = (term199 _27494 P Q).
Proof. exact (@lem1179050 _27494 P Q). Qed.
Lemma lem1179052 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term446 _27494 _27495 h P t m) = (term447 _27494 _27495 h P t m).
Proof. exact (@lem1179051 _27494 (term408 _27494 _27495 h P t m) (term444 _27494 _27495 h P t m)). Qed.
Lemma lem1179053 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term448 _27494 _27495 h P t m x) = (term406 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term448 _27494 _27495 h P t m x)). Qed.
Lemma lem1179054 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term449 _27494 _27495 h P t m) = (term408 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1179053 _27494 _27495 h x P t m)). Qed.
Lemma lem1179055 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179056 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term450 _27494 _27495 h P t m) = (term409 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179055 _27494) (@lem1179054 _27494 _27495 h P t m)). Qed.
Lemma lem1179057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179058 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term451 _27494 _27495 h P t m) = (term410 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179057) (@lem1179056 _27494 _27495 h P t m)). Qed.
Lemma lem1179059 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term444 _27494 _27495 h P t m) = (term444 _27494 _27495 h P t m).
Proof. exact (eq_refl (term444 _27494 _27495 h P t m)). Qed.
Lemma lem1179060 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term446 _27494 _27495 h P t m) = (term445 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179058 _27494 _27495 h P t m) (@lem1179059 _27494 _27495 h P t m)). Qed.
Lemma lem1179061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179062 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term452 _27494 _27495 h P t m) = (term453 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179061) (@lem1179060 _27494 _27495 h P t m)). Qed.
Lemma lem1179063 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term448 _27494 _27495 h P t m x) = (term406 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term448 _27494 _27495 h P t m x)). Qed.
Lemma lem1179064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179065 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term454 _27494 _27495 h P t m x) = (term455 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1179064) (@lem1179063 _27494 _27495 h x P t m)). Qed.
Lemma lem1179066 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term444 _27494 _27495 h P t m) = (term444 _27494 _27495 h P t m).
Proof. exact (eq_refl (term444 _27494 _27495 h P t m)). Qed.
Lemma lem1179067 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term456 _27494 _27495 x h P t m) = (term457 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179065 _27494 _27495 h x P t m) (@lem1179066 _27494 _27495 h P t m)). Qed.
Lemma lem1179068 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term458 _27494 _27495 h P t m) = (term459 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1179067 _27494 _27495 x h P t m)). Qed.
Lemma lem1179069 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179070 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term447 _27494 _27495 h P t m) = (term460 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179069 _27494) (@lem1179068 _27494 _27495 h P t m)). Qed.
Lemma lem1179071 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term446 _27494 _27495 h P t m) = (term447 _27494 _27495 h P t m)) = ((term445 _27494 _27495 h P t m) = (term460 _27494 _27495 h P t m)).
Proof. exact (MK_COMB (@lem1179062 _27494 _27495 h P t m) (@lem1179070 _27494 _27495 h P t m)). Qed.
Lemma lem1179072 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term445 _27494 _27495 h P t m) = (term460 _27494 _27495 h P t m).
Proof. exact (EQ_MP (@lem1179071 _27494 _27495 h P t m) (@lem1179052 _27494 _27495 h P t m)). Qed.
Lemma lem1179074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1179075 {_27495 : Type'} (P : Prop) (Q : _27495 -> Prop) : (term461 _27495 P Q) = (term462 _27495 P Q).
Proof. exact (@lem1179074 _27495 P Q). Qed.
Lemma lem1179076 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term463 _27494 _27495 x h P t m) = (term464 _27494 _27495 x h P t m).
Proof. exact (@lem1179075 _27495 (term406 _27494 _27495 h x P t m) (term443 _27494 _27495 h P t m)). Qed.
Lemma lem1179077 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term465 _27494 _27495 h P t m x) = (term442 _27494 _27495 x h P t m).
Proof. exact (eq_refl (term465 _27494 _27495 h P t m x)). Qed.
Lemma lem1179078 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term466 _27494 _27495 h P t m) = (term443 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1179077 _27494 _27495 x h P t m)). Qed.
Lemma lem1179079 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179080 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term467 _27494 _27495 h P t m) = (term444 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179079 _27495) (@lem1179078 _27494 _27495 h P t m)). Qed.
Lemma lem1179081 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term455 _27494 _27495 h x P t m) = (term455 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term455 _27494 _27495 h x P t m)). Qed.
Lemma lem1179082 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term463 _27494 _27495 x h P t m) = (term457 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179081 _27494 _27495 h x P t m) (@lem1179080 _27494 _27495 h P t m)). Qed.
Lemma lem1179083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179084 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term468 _27494 _27495 x h P t m) = (term469 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179083) (@lem1179082 _27494 _27495 x h P t m)). Qed.
Lemma lem1179085 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term465 _27494 _27495 h P t m x) = (term442 _27494 _27495 x h P t m).
Proof. exact (eq_refl (term465 _27494 _27495 h P t m x)). Qed.
Lemma lem1179086 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term455 _27494 _27495 h x P t m) = (term455 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term455 _27494 _27495 h x P t m)). Qed.
Lemma lem1179087 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term470 _27494 _27495 x h P t m x') = (term471 _27494 _27495 x x' h P t m).
Proof. exact (MK_COMB (@lem1179086 _27494 _27495 h x P t m) (@lem1179085 _27494 _27495 x' h P t m)). Qed.
Lemma lem1179088 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term472 _27494 _27495 x h P t m) = (term473 _27494 _27495 x h P t m).
Proof. exact (fun_ext (fun x' : _27495 => @lem1179087 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179089 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179090 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term464 _27494 _27495 x h P t m) = (term474 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179089 _27495) (@lem1179088 _27494 _27495 x h P t m)). Qed.
Lemma lem1179091 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term463 _27494 _27495 x h P t m) = (term464 _27494 _27495 x h P t m)) = ((term457 _27494 _27495 x h P t m) = (term474 _27494 _27495 x h P t m)).
Proof. exact (MK_COMB (@lem1179084 _27494 _27495 x h P t m) (@lem1179090 _27494 _27495 x h P t m)). Qed.
Lemma lem1179092 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term457 _27494 _27495 x h P t m) = (term474 _27494 _27495 x h P t m).
Proof. exact (EQ_MP (@lem1179091 _27494 _27495 x h P t m) (@lem1179076 _27494 _27495 x h P t m)). Qed.
Lemma lem1179094 {A : Type'} (P : Prop) (Q : A -> Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1179095 {_27494 : Type'} (P : Prop) (Q : _27494 -> Prop) : (term461 _27494 P Q) = (term462 _27494 P Q).
Proof. exact (@lem1179094 _27494 P Q). Qed.
Lemma lem1179096 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term475 _27494 _27495 x x' h P t m) = (term476 _27494 _27495 x x' h P t m).
Proof. exact (@lem1179095 _27494 (term406 _27494 _27495 h x P t m) (term441 _27494 _27495 x' h P t m)). Qed.
Lemma lem1179097 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term477 _27494 _27495 x h P t m y) = (term439 _27494 _27495 x y h P t m).
Proof. exact (eq_refl (term477 _27494 _27495 x h P t m y)). Qed.
Lemma lem1179098 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term478 _27494 _27495 x h P t m) = (term441 _27494 _27495 x h P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1179097 _27494 _27495 x y h P t m)). Qed.
Lemma lem1179099 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179100 {_27494 _27495 : Type'} (x : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term479 _27494 _27495 x h P t m) = (term442 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179099 _27494) (@lem1179098 _27494 _27495 x h P t m)). Qed.
Lemma lem1179101 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term455 _27494 _27495 h x P t m) = (term455 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term455 _27494 _27495 h x P t m)). Qed.
Lemma lem1179102 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term475 _27494 _27495 x x' h P t m) = (term471 _27494 _27495 x x' h P t m).
Proof. exact (MK_COMB (@lem1179101 _27494 _27495 h x P t m) (@lem1179100 _27494 _27495 x' h P t m)). Qed.
Lemma lem1179103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179104 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term480 _27494 _27495 x x' h P t m) = (term481 _27494 _27495 x x' h P t m).
Proof. exact (MK_COMB (@lem1179103) (@lem1179102 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179105 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term477 _27494 _27495 x h P t m y) = (term439 _27494 _27495 x y h P t m).
Proof. exact (eq_refl (term477 _27494 _27495 x h P t m y)). Qed.
Lemma lem1179106 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term455 _27494 _27495 h x P t m) = (term455 _27494 _27495 h x P t m).
Proof. exact (eq_refl (term455 _27494 _27495 h x P t m)). Qed.
Lemma lem1179107 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term482 _27494 _27495 x x' h P t m y) = (term483 _27494 _27495 x x' y h P t m).
Proof. exact (MK_COMB (@lem1179106 _27494 _27495 h x P t m) (@lem1179105 _27494 _27495 x' y h P t m)). Qed.
Lemma lem1179108 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term484 _27494 _27495 x x' h P t m) = (term485 _27494 _27495 x x' h P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1179107 _27494 _27495 x x' y h P t m)). Qed.
Lemma lem1179109 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179110 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term476 _27494 _27495 x x' h P t m) = (term486 _27494 _27495 x x' h P t m).
Proof. exact (MK_COMB (@lem1179109 _27494) (@lem1179108 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179111 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term475 _27494 _27495 x x' h P t m) = (term476 _27494 _27495 x x' h P t m)) = ((term471 _27494 _27495 x x' h P t m) = (term486 _27494 _27495 x x' h P t m)).
Proof. exact (MK_COMB (@lem1179104 _27494 _27495 x x' h P t m) (@lem1179110 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179112 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term471 _27494 _27495 x x' h P t m) = (term486 _27494 _27495 x x' h P t m).
Proof. exact (EQ_MP (@lem1179111 _27494 _27495 x x' h P t m) (@lem1179096 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179113 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term473 _27494 _27495 x h P t m) = (term487 _27494 _27495 x h P t m).
Proof. exact (fun_ext (fun x' : _27495 => @lem1179112 _27494 _27495 x x' h P t m)). Qed.
Lemma lem1179114 {_27495 : Type'} : (@ex _27495) = (@ex _27495).
Proof. exact (eq_refl (@ex _27495)). Qed.
Lemma lem1179115 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term474 _27494 _27495 x h P t m) = (term488 _27494 _27495 x h P t m).
Proof. exact (MK_COMB (@lem1179114 _27495) (@lem1179113 _27494 _27495 x h P t m)). Qed.
Lemma lem1179116 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term457 _27494 _27495 x h P t m) = (term488 _27494 _27495 x h P t m).
Proof. exact (TRANS (@lem1179092 _27494 _27495 x h P t m) (@lem1179115 _27494 _27495 x h P t m)). Qed.
Lemma lem1179117 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term459 _27494 _27495 h P t m) = (term489 _27494 _27495 h P t m).
Proof. exact (fun_ext (fun x : _27494 => @lem1179116 _27494 _27495 x h P t m)). Qed.
Lemma lem1179118 {_27494 : Type'} : (@ex _27494) = (@ex _27494).
Proof. exact (eq_refl (@ex _27494)). Qed.
Lemma lem1179119 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term460 _27494 _27495 h P t m) = (term490 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179118 _27494) (@lem1179117 _27494 _27495 h P t m)). Qed.
Lemma lem1179120 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term445 _27494 _27495 h P t m) = (term490 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1179072 _27494 _27495 h P t m) (@lem1179119 _27494 _27495 h P t m)). Qed.
Lemma lem1179122 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term381 _27494 _27495 h P t m) = (term490 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1179046 _27494 _27495 h P t m) (@lem1179120 _27494 _27495 h P t m)). Qed.
Lemma lem1179123 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term129 _27494 _27495 h P t m) = (term490 _27494 _27495 h P t m).
Proof. exact (TRANS (@lem1178743 _27494 _27495 h P t m) (@lem1179122 _27494 _27495 h P t m)). Qed.
Lemma lem1179124 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term129 _27494 _27495 h P t m) : term490 _27494 _27495 h P t m.
Proof. exact (EQ_MP (@lem1179123 _27494 _27495 h P t m) (@lem1178172 _27494 _27495 h P t m h1)). Qed.
Lemma lem1179125 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term488 _27494 _27495 x h P t m) : term488 _27494 _27495 x h P t m.
Proof. exact (h1). Qed.
Lemma lem1179126 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term486 _27494 _27495 x x' h P t m) : term486 _27494 _27495 x x' h P t m.
Proof. exact (h1). Qed.
Lemma lem1179127 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term483 _27494 _27495 x x' y h P t m) : term483 _27494 _27495 x x' y h P t m.
Proof. exact (h1). Qed.
Lemma lem1179128 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term316 _27494 _27495 x'' P t) : term316 _27494 _27495 x'' P t.
Proof. exact (h1). Qed.
Lemma lem1179129 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term313 _27494 _27495 x'' y' P t.
Proof. exact (h1). Qed.
Lemma lem1179136 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1179143 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179144 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179143 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179145 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) : (P h) = (@I (_27495 -> _27494 -> Prop) P h).
Proof. exact (@lem1179144 _27494 _27495 P h). Qed.
Lemma lem1179146 {_27494 : Type'} (x : _27494) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1179147 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (P h x) = (@I (_27495 -> _27494 -> Prop) P h x).
Proof. exact (MK_COMB (@lem1179145 _27494 _27495 P h) (@lem1179146 _27494 x)). Qed.
Lemma lem1179149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179150 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179149 _27494 Prop f x). Qed.
Lemma lem1179151 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (@I (_27495 -> _27494 -> Prop) P h x) = (term491 _27494 _27495 P h x).
Proof. exact (@lem1179150 _27494 (@I (_27495 -> _27494 -> Prop) P h) x). Qed.
Lemma lem1179153 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (P h x) = (term491 _27494 _27495 P h x).
Proof. exact (TRANS (@lem1179147 _27494 _27495 P h x) (@lem1179151 _27494 _27495 P h x)). Qed.
Lemma lem1179162 {_27494 : Type'} (x : _27494) (m : list _27494) : (term492 _27494 x m) = (term492 _27494 x m).
Proof. exact (eq_refl (term492 _27494 x m)). Qed.
Lemma lem1179163 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term353 _27494 _27495 m P h x) = (term493 _27494 _27495 m P h x).
Proof. exact (MK_COMB (@lem1179162 _27494 x m) (@lem1179153 _27494 _27495 P h x)). Qed.
Lemma lem1179164 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term361 _27494 _27495 m P h) = (term494 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1179163 _27494 _27495 m P h x)). Qed.
Lemma lem1179165 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179166 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term362 _27494 _27495 m P h) = (term495 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1179165 _27494) (@lem1179164 _27494 _27495 m P h)). Qed.
Lemma lem1179167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179168 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term368 _27494 _27495 m P h) = (term496 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1179167) (@lem1179166 _27494 _27495 m P h)). Qed.
Lemma lem1179169 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term369 _27494 _27495 h P t m) = (term497 _27494 _27495 h P t m).
Proof. exact (MK_COMB (@lem1179168 _27494 _27495 m P h) (@lem1179136 _27494 _27495 P t m)). Qed.
Lemma lem1179170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1179177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179178 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179177 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179179 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) : (P x') = (@I (_27495 -> _27494 -> Prop) P x').
Proof. exact (@lem1179178 _27494 _27495 P x'). Qed.
Lemma lem1179180 {_27494 : Type'} (y : _27494) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1179181 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (P x' y) = (@I (_27495 -> _27494 -> Prop) P x' y).
Proof. exact (MK_COMB (@lem1179179 _27494 _27495 P x') (@lem1179180 _27494 y)). Qed.
Lemma lem1179183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179184 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179183 _27494 Prop f x). Qed.
Lemma lem1179185 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (@I (_27495 -> _27494 -> Prop) P x' y) = (term491 _27494 _27495 P x' y).
Proof. exact (@lem1179184 _27494 (@I (_27495 -> _27494 -> Prop) P x') y). Qed.
Lemma lem1179187 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (P x' y) = (term491 _27494 _27495 P x' y).
Proof. exact (TRANS (@lem1179181 _27494 _27495 P x' y) (@lem1179185 _27494 _27495 P x' y)). Qed.
Lemma lem1179188 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term498 _27494 _27495 P x' y) = (term499 _27494 _27495 P x' y).
Proof. exact (MK_COMB (@lem1179170) (@lem1179187 _27494 _27495 P x' y)). Qed.
Lemma lem1179211 {_27494 _27495 : Type'} (h : _27495) (x' : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term500 _27494 _27495 h x' t y m) = (term500 _27494 _27495 h x' t y m).
Proof. exact (eq_refl (term500 _27494 _27495 h x' t y m)). Qed.
Lemma lem1179212 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term328 _27494 _27495 h t m P x' y) = (term501 _27494 _27495 h t m P x' y).
Proof. exact (MK_COMB (@lem1179211 _27494 _27495 h x' t y m) (@lem1179188 _27494 _27495 P x' y)). Qed.
Lemma lem1179213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179214 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term437 _27494 _27495 h t m P x' y) = (term502 _27494 _27495 h t m P x' y).
Proof. exact (MK_COMB (@lem1179213) (@lem1179212 _27494 _27495 h t m P x' y)). Qed.
Lemma lem1179215 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term439 _27494 _27495 x' y h P t m) = (term503 _27494 _27495 x' y h P t m).
Proof. exact (MK_COMB (@lem1179214 _27494 _27495 h t m P x' y) (@lem1179169 _27494 _27495 h P t m)). Qed.
Lemma lem1179224 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1179232 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179233 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179232 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179234 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) : (P h) = (@I (_27495 -> _27494 -> Prop) P h).
Proof. exact (@lem1179233 _27494 _27495 P h). Qed.
Lemma lem1179235 {_27494 : Type'} (x : _27494) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1179236 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (P h x) = (@I (_27495 -> _27494 -> Prop) P h x).
Proof. exact (MK_COMB (@lem1179234 _27494 _27495 P h) (@lem1179235 _27494 x)). Qed.
Lemma lem1179238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179239 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179238 _27494 Prop f x). Qed.
Lemma lem1179240 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (@I (_27495 -> _27494 -> Prop) P h x) = (term491 _27494 _27495 P h x).
Proof. exact (@lem1179239 _27494 (@I (_27495 -> _27494 -> Prop) P h) x). Qed.
Lemma lem1179242 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (P h x) = (term491 _27494 _27495 P h x).
Proof. exact (TRANS (@lem1179236 _27494 _27495 P h x) (@lem1179240 _27494 _27495 P h x)). Qed.
Lemma lem1179243 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term498 _27494 _27495 P h x) = (term499 _27494 _27495 P h x).
Proof. exact (MK_COMB (@lem1179225) (@lem1179242 _27494 _27495 P h x)). Qed.
Lemma lem1179250 {_27494 : Type'} (x : _27494) (m : list _27494) : (term504 _27494 x m) = (term504 _27494 x m).
Proof. exact (eq_refl (term504 _27494 x m)). Qed.
Lemma lem1179251 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term352 _27494 _27495 m P h x) = (term505 _27494 _27495 m P h x).
Proof. exact (MK_COMB (@lem1179250 _27494 x m) (@lem1179243 _27494 _27495 P h x)). Qed.
Lemma lem1179252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179253 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term391 _27494 _27495 m P h x) = (term506 _27494 _27495 m P h x).
Proof. exact (MK_COMB (@lem1179252) (@lem1179251 _27494 _27495 m P h x)). Qed.
Lemma lem1179254 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term393 _27494 _27495 h x P t m) = (term507 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1179253 _27494 _27495 m P h x) (@lem1179224 _27494 _27495 P t m)). Qed.
Lemma lem1179261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179262 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179261 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179263 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) : (P x) = (@I (_27495 -> _27494 -> Prop) P x).
Proof. exact (@lem1179262 _27494 _27495 P x). Qed.
Lemma lem1179264 {_27494 : Type'} (y : _27494) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1179265 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (@I (_27495 -> _27494 -> Prop) P x y).
Proof. exact (MK_COMB (@lem1179263 _27494 _27495 P x) (@lem1179264 _27494 y)). Qed.
Lemma lem1179267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179268 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179267 _27494 Prop f x). Qed.
Lemma lem1179269 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (@I (_27495 -> _27494 -> Prop) P x y) = (term491 _27494 _27495 P x y).
Proof. exact (@lem1179268 _27494 (@I (_27495 -> _27494 -> Prop) P x) y). Qed.
Lemma lem1179271 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (term491 _27494 _27495 P x y).
Proof. exact (TRANS (@lem1179265 _27494 _27495 P x y) (@lem1179269 _27494 _27495 P x y)). Qed.
Lemma lem1179300 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term330 _27494 _27495 h x t y m) = (term330 _27494 _27495 h x t y m).
Proof. exact (eq_refl (term330 _27494 _27495 h x t y m)). Qed.
Lemma lem1179301 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term332 _27494 _27495 h t m P x y) = (term508 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1179300 _27494 _27495 h x t y m) (@lem1179271 _27494 _27495 P x y)). Qed.
Lemma lem1179302 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term340 _27494 _27495 h t m P x) = (term509 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179301 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179303 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179304 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term341 _27494 _27495 h t m P x) = (term510 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179303 _27494) (@lem1179302 _27494 _27495 h t m P x)). Qed.
Lemma lem1179305 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term349 _27494 _27495 h t m P) = (term511 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1179304 _27494 _27495 h t m P x)). Qed.
Lemma lem1179306 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179307 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term350 _27494 _27495 h t m P) = (term512 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179306 _27495) (@lem1179305 _27494 _27495 h t m P)). Qed.
Lemma lem1179308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179309 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term375 _27494 _27495 h t m P) = (term513 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179308) (@lem1179307 _27494 _27495 h t m P)). Qed.
Lemma lem1179310 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term406 _27494 _27495 h x P t m) = (term514 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1179309 _27494 _27495 h t m P) (@lem1179254 _27494 _27495 h x P t m)). Qed.
Lemma lem1179311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179312 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term455 _27494 _27495 h x P t m) = (term515 _27494 _27495 h x P t m).
Proof. exact (MK_COMB (@lem1179311) (@lem1179310 _27494 _27495 h x P t m)). Qed.
Lemma lem1179313 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term483 _27494 _27495 x x' y h P t m) = (term516 _27494 _27495 x x' y h P t m).
Proof. exact (MK_COMB (@lem1179312 _27494 _27495 h x P t m) (@lem1179215 _27494 _27495 x' y h P t m)). Qed.
Lemma lem1179314 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term483 _27494 _27495 x x' y h P t m) : term516 _27494 _27495 x x' y h P t m.
Proof. exact (EQ_MP (@lem1179313 _27494 _27495 x x' y h P t m) (@lem1179127 _27494 _27495 x x' y h P t m h1)). Qed.
Lemma lem1179321 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (@ALLPAIRS _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (eq_refl (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1179322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1179333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179334 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179333 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179335 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (m : list _27494) : (term517 _27494 _27495 P x'' m) = (term518 _27494 _27495 P x'' m).
Proof. exact (@lem1179334 _27494 _27495 P (x'' m)). Qed.
Lemma lem1179336 {_27494 : Type'} (y' : type1141 _27494) (m : list _27494) : (y' m) = (y' m).
Proof. exact (eq_refl (y' m)). Qed.
Lemma lem1179337 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term519 _27494 _27495 P x'' y' m) = (term520 _27494 _27495 P x'' y' m).
Proof. exact (MK_COMB (@lem1179335 _27494 _27495 P x'' m) (@lem1179336 _27494 y' m)). Qed.
Lemma lem1179339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179340 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179339 _27494 Prop f x). Qed.
Lemma lem1179341 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term520 _27494 _27495 P x'' y' m) = (term521 _27494 _27495 P x'' y' m).
Proof. exact (@lem1179340 _27494 (term518 _27494 _27495 P x'' m) (y' m)). Qed.
Lemma lem1179343 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term519 _27494 _27495 P x'' y' m) = (term521 _27494 _27495 P x'' y' m).
Proof. exact (TRANS (@lem1179337 _27494 _27495 P x'' y' m) (@lem1179341 _27494 _27495 P x'' y' m)). Qed.
Lemma lem1179344 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term522 _27494 _27495 P x'' y' m) = (term523 _27494 _27495 P x'' y' m).
Proof. exact (MK_COMB (@lem1179322) (@lem1179343 _27494 _27495 P x'' y' m)). Qed.
Lemma lem1179363 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (m : list _27494) : (term524 _27494 _27495 x'' t y' m) = (term524 _27494 _27495 x'' t y' m).
Proof. exact (eq_refl (term524 _27494 _27495 x'' t y' m)). Qed.
Lemma lem1179364 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term525 _27494 _27495 t P x'' y' m) = (term526 _27494 _27495 t P x'' y' m).
Proof. exact (MK_COMB (@lem1179363 _27494 _27495 x'' t y' m) (@lem1179344 _27494 _27495 P x'' y' m)). Qed.
Lemma lem1179365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179366 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term527 _27494 _27495 t P x'' y' m) = (term528 _27494 _27495 t P x'' y' m).
Proof. exact (MK_COMB (@lem1179365) (@lem1179364 _27494 _27495 t P x'' y' m)). Qed.
Lemma lem1179367 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term276 _27494 _27495 x'' y' P t m) = (term529 _27494 _27495 x'' y' P t m).
Proof. exact (MK_COMB (@lem1179366 _27494 _27495 t P x'' y' m) (@lem1179321 _27494 _27495 P t m)). Qed.
Lemma lem1179368 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term278 _27494 _27495 x'' y' P t) = (term530 _27494 _27495 x'' y' P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1179367 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179369 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1179370 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term280 _27494 _27495 x'' y' P t) = (term531 _27494 _27495 x'' y' P t).
Proof. exact (MK_COMB (@lem1179369 _27494) (@lem1179368 _27494 _27495 x'' y' P t)). Qed.
Lemma lem1179379 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179387 {_27494 _27495 : Type'} (f : type1470 _27494 _27495) (x : _27495) : (f x) = (@I (_27495 -> _27494 -> Prop) f x).
Proof. exact (@lem1179386 _27495 (_27494 -> Prop) f x). Qed.
Lemma lem1179388 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) : (P x) = (@I (_27495 -> _27494 -> Prop) P x).
Proof. exact (@lem1179387 _27494 _27495 P x). Qed.
Lemma lem1179389 {_27494 : Type'} (y : _27494) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1179390 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (@I (_27495 -> _27494 -> Prop) P x y).
Proof. exact (MK_COMB (@lem1179388 _27494 _27495 P x) (@lem1179389 _27494 y)). Qed.
Lemma lem1179392 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1179393 {_27494 : Type'} (f : _27494 -> Prop) (x : _27494) : (f x) = (@I (_27494 -> Prop) f x).
Proof. exact (@lem1179392 _27494 Prop f x). Qed.
Lemma lem1179394 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (@I (_27495 -> _27494 -> Prop) P x y) = (term491 _27494 _27495 P x y).
Proof. exact (@lem1179393 _27494 (@I (_27495 -> _27494 -> Prop) P x) y). Qed.
Lemma lem1179396 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (P x y) = (term491 _27494 _27495 P x y).
Proof. exact (TRANS (@lem1179390 _27494 _27495 P x y) (@lem1179394 _27494 _27495 P x y)). Qed.
Lemma lem1179415 {_27494 _27495 : Type'} (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term136 _27494 _27495 x t y m) = (term136 _27494 _27495 x t y m).
Proof. exact (eq_refl (term136 _27494 _27495 x t y m)). Qed.
Lemma lem1179416 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term138 _27494 _27495 t m P x y) = (term532 _27494 _27495 t m P x y).
Proof. exact (MK_COMB (@lem1179415 _27494 _27495 x t y m) (@lem1179396 _27494 _27495 P x y)). Qed.
Lemma lem1179417 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term148 _27494 _27495 t m P x) = (term533 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179416 _27494 _27495 t m P x y)). Qed.
Lemma lem1179418 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179419 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term149 _27494 _27495 t m P x) = (term534 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1179418 _27494) (@lem1179417 _27494 _27495 t m P x)). Qed.
Lemma lem1179420 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term157 _27494 _27495 t m P) = (term535 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1179419 _27494 _27495 t m P x)). Qed.
Lemma lem1179421 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179422 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term158 _27494 _27495 t m P) = (term536 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1179421 _27495) (@lem1179420 _27494 _27495 t m P)). Qed.
Lemma lem1179423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179424 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term165 _27494 _27495 t m P) = (term537 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1179423) (@lem1179422 _27494 _27495 t m P)). Qed.
Lemma lem1179425 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term167 _27494 _27495 P t m) = (term538 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1179424 _27494 _27495 t m P) (@lem1179379 _27494 _27495 P t m)). Qed.
Lemma lem1179426 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term180 _27494 _27495 P t) = (term539 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1179425 _27494 _27495 P t m)). Qed.
Lemma lem1179427 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1179428 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term191 _27494 _27495 P t) = (term540 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1179427 _27494) (@lem1179426 _27494 _27495 P t)). Qed.
Lemma lem1179429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179430 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term193 _27494 _27495 P t) = (term541 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1179429) (@lem1179428 _27494 _27495 P t)). Qed.
Lemma lem1179431 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term313 _27494 _27495 x'' y' P t) = (term542 _27494 _27495 x'' y' P t).
Proof. exact (MK_COMB (@lem1179430 _27494 _27495 P t) (@lem1179370 _27494 _27495 x'' y' P t)). Qed.
Lemma lem1179432 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term542 _27494 _27495 x'' y' P t.
Proof. exact (EQ_MP (@lem1179431 _27494 _27495 x'' y' P t) (@lem1179129 _27494 _27495 x'' y' P t h1)). Qed.
Lemma lem1179433 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term531 _27494 _27495 x'' y' P t.
Proof. exact (proj2 (@lem1179432 _27494 _27495 x'' y' P t h1)). Qed.
Lemma lem1179434 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term540 _27494 _27495 P t.
Proof. exact (proj1 (@lem1179432 _27494 _27495 x'' y' P t h1)). Qed.
Lemma lem1179435 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term514 _27494 _27495 h x P t m.
Proof. exact (h1). Qed.
Lemma lem1179436 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term503 _27494 _27495 x' y h P t m.
Proof. exact (h1). Qed.
Lemma lem1179437 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term507 _27494 _27495 h x P t m.
Proof. exact (proj2 (@lem1179435 _27494 _27495 h x P t m h1)). Qed.
Lemma lem1179438 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term512 _27494 _27495 h t m P.
Proof. exact (proj1 (@lem1179435 _27494 _27495 h x P t m h1)). Qed.
Lemma lem1179439 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : term505 _27494 _27495 m P h x.
Proof. exact (h1). Qed.
Lemma lem1179443 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term497 _27494 _27495 h P t m.
Proof. exact (proj2 (@lem1179436 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179444 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term501 _27494 _27495 h t m P x' y.
Proof. exact (proj1 (@lem1179436 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179446 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term495 _27494 _27495 m P h.
Proof. exact (proj1 (@lem1179443 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179448 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term72 _27494 _27495 h x' t y m.
Proof. exact (proj1 (@lem1179444 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179450 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term68 _27495 h x' t.
Proof. exact (proj1 (@lem1179448 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179572 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term491 _27494 _27495 P x y) = (term491 _27494 _27495 P x y).
Proof. exact (eq_refl (term491 _27494 _27495 P x y)). Qed.
Lemma lem1179589 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term325 _27494 _27495 h x t y m) = (term543 _27494 _27495 h x t y m).
Proof. exact (@lem19699 (term544 _27495 x h) (term321 _27495 x t) (term321 _27494 y m)). Qed.
Lemma lem1179590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179591 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term330 _27494 _27495 h x t y m) = (term545 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1179590) (@lem1179589 _27494 _27495 h x t y m)). Qed.
Lemma lem1179592 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term508 _27494 _27495 h t m P x y) = (term546 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1179591 _27494 _27495 h x t y m) (@lem1179572 _27494 _27495 P x y)). Qed.
Lemma lem1179599 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term546 _27494 _27495 h t m P x y) = (term547 _27494 _27495 h t m P x y).
Proof. exact (@lem19699 (term548 _27494 _27495 x h y m) (term131 _27494 _27495 x t y m) (term491 _27494 _27495 P x y)). Qed.
Lemma lem1179600 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term508 _27494 _27495 h t m P x y) = (term547 _27494 _27495 h t m P x y).
Proof. exact (TRANS (@lem1179592 _27494 _27495 h t m P x y) (@lem1179599 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179601 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term509 _27494 _27495 h t m P x) = (term549 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179600 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179602 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179603 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term510 _27494 _27495 h t m P x) = (term550 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179602 _27494) (@lem1179601 _27494 _27495 h t m P x)). Qed.
Lemma lem1179604 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term511 _27494 _27495 h t m P) = (term551 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1179603 _27494 _27495 h t m P x)). Qed.
Lemma lem1179605 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179607 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term512 _27494 _27495 h t m P) = (term552 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179605 _27495) (@lem1179604 _27494 _27495 h t m P)). Qed.
Lemma lem1179608 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term552 _27494 _27495 h t m P.
Proof. exact (EQ_MP (@lem1179607 _27494 _27495 h t m P) (@lem1179438 _27494 _27495 h x P t m h1)). Qed.
Lemma lem1179716 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term529 _27494 _27495 x'' y' P t m) = (term553 _27494 _27495 x'' y' P t m).
Proof. exact (@lem19699 (term554 _27494 _27495 x'' t y' m) (term523 _27494 _27495 P x'' y' m) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1179717 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term555 _27494 _27495 x'' y' P t m) = (term555 _27494 _27495 x'' y' P t m).
Proof. exact (eq_refl (term555 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179724 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term556 _27494 _27495 x'' y' P t m) = (term557 _27494 _27495 x'' y' P t m).
Proof. exact (@lem19699 (term558 _27494 _27495 x'' m t) (term559 _27494 y' m) (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1179725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1179726 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term560 _27494 _27495 x'' y' P t m) = (term561 _27494 _27495 x'' y' P t m).
Proof. exact (MK_COMB (@lem1179725) (@lem1179724 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179727 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term553 _27494 _27495 x'' y' P t m) = (term562 _27494 _27495 x'' y' P t m).
Proof. exact (MK_COMB (@lem1179726 _27494 _27495 x'' y' P t m) (@lem1179717 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179729 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term529 _27494 _27495 x'' y' P t m) = (term562 _27494 _27495 x'' y' P t m).
Proof. exact (TRANS (@lem1179716 _27494 _27495 x'' y' P t m) (@lem1179727 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179730 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term530 _27494 _27495 x'' y' P t) = (term563 _27494 _27495 x'' y' P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1179729 _27494 _27495 x'' y' P t m)). Qed.
Lemma lem1179731 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1179733 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) : (term531 _27494 _27495 x'' y' P t) = (term564 _27494 _27495 x'' y' P t).
Proof. exact (MK_COMB (@lem1179731 _27494) (@lem1179730 _27494 _27495 x'' y' P t)). Qed.
Lemma lem1179734 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term564 _27494 _27495 x'' y' P t.
Proof. exact (EQ_MP (@lem1179733 _27494 _27495 x'' y' P t) (@lem1179433 _27494 _27495 x'' y' P t h1)). Qed.
Lemma lem1179736 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term491 _27494 _27495 P x y) = (term491 _27494 _27495 P x y).
Proof. exact (eq_refl (term491 _27494 _27495 P x y)). Qed.
Lemma lem1179753 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term325 _27494 _27495 h x t y m) = (term543 _27494 _27495 h x t y m).
Proof. exact (@lem19699 (term544 _27495 x h) (term321 _27495 x t) (term321 _27494 y m)). Qed.
Lemma lem1179754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179755 {_27494 _27495 : Type'} (h : _27495) (x : _27495) (t : list _27495) (y : _27494) (m : list _27494) : (term330 _27494 _27495 h x t y m) = (term545 _27494 _27495 h x t y m).
Proof. exact (MK_COMB (@lem1179754) (@lem1179753 _27494 _27495 h x t y m)). Qed.
Lemma lem1179756 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term508 _27494 _27495 h t m P x y) = (term546 _27494 _27495 h t m P x y).
Proof. exact (MK_COMB (@lem1179755 _27494 _27495 h x t y m) (@lem1179736 _27494 _27495 P x y)). Qed.
Lemma lem1179763 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term546 _27494 _27495 h t m P x y) = (term547 _27494 _27495 h t m P x y).
Proof. exact (@lem19699 (term548 _27494 _27495 x h y m) (term131 _27494 _27495 x t y m) (term491 _27494 _27495 P x y)). Qed.
Lemma lem1179764 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term508 _27494 _27495 h t m P x y) = (term547 _27494 _27495 h t m P x y).
Proof. exact (TRANS (@lem1179756 _27494 _27495 h t m P x y) (@lem1179763 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179765 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term509 _27494 _27495 h t m P x) = (term549 _27494 _27495 h t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179764 _27494 _27495 h t m P x y)). Qed.
Lemma lem1179766 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179767 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term510 _27494 _27495 h t m P x) = (term550 _27494 _27495 h t m P x).
Proof. exact (MK_COMB (@lem1179766 _27494) (@lem1179765 _27494 _27495 h t m P x)). Qed.
Lemma lem1179768 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term511 _27494 _27495 h t m P) = (term551 _27494 _27495 h t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1179767 _27494 _27495 h t m P x)). Qed.
Lemma lem1179769 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179771 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term512 _27494 _27495 h t m P) = (term552 _27494 _27495 h t m P).
Proof. exact (MK_COMB (@lem1179769 _27495) (@lem1179768 _27494 _27495 h t m P)). Qed.
Lemma lem1179772 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term552 _27494 _27495 h t m P.
Proof. exact (EQ_MP (@lem1179771 _27494 _27495 h t m P) (@lem1179438 _27494 _27495 h x P t m h1)). Qed.
Lemma lem1179776 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (h1). Qed.
Lemma lem1179902 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term493 _27494 _27495 m P h x) = (term493 _27494 _27495 m P h x).
Proof. exact (eq_refl (term493 _27494 _27495 m P h x)). Qed.
Lemma lem1179903 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term494 _27494 _27495 m P h) = (term494 _27494 _27495 m P h).
Proof. exact (fun_ext (fun x : _27494 => @lem1179902 _27494 _27495 m P h x)). Qed.
Lemma lem1179904 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179906 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) : (term495 _27494 _27495 m P h) = (term495 _27494 _27495 m P h).
Proof. exact (MK_COMB (@lem1179904 _27494) (@lem1179903 _27494 _27495 m P h)). Qed.
Lemma lem1179907 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term495 _27494 _27495 m P h.
Proof. exact (EQ_MP (@lem1179906 _27494 _27495 m P h) (@lem1179446 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1179923 {_27495 : Type'} (x' : _27495) (h : _27495) (h1 : x' = h) : x' = h.
Proof. exact (h1). Qed.
Lemma lem1179925 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1179926 {_27495 : Type'} (P : _27495 -> Prop) (Q : Prop) : (term565 _27495 P Q) = (term566 _27495 P Q).
Proof. exact (@lem1179925 _27495 P Q). Qed.
Lemma lem1179927 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term567 _27494 _27495 P t m) = (term568 _27494 _27495 P t m).
Proof. exact (@lem1179926 _27495 (term535 _27494 _27495 t m P) (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179928 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term569 _27494 _27495 t m P x) = (term534 _27494 _27495 t m P x).
Proof. exact (eq_refl (term569 _27494 _27495 t m P x)). Qed.
Lemma lem1179929 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term570 _27494 _27495 t m P) = (term535 _27494 _27495 t m P).
Proof. exact (fun_ext (fun x : _27495 => @lem1179928 _27494 _27495 t m P x)). Qed.
Lemma lem1179930 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179931 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term571 _27494 _27495 t m P) = (term536 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1179930 _27495) (@lem1179929 _27494 _27495 t m P)). Qed.
Lemma lem1179932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179933 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term572 _27494 _27495 t m P) = (term537 _27494 _27495 t m P).
Proof. exact (MK_COMB (@lem1179932) (@lem1179931 _27494 _27495 t m P)). Qed.
Lemma lem1179934 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179935 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term567 _27494 _27495 P t m) = (term538 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1179933 _27494 _27495 t m P) (@lem1179934 _27494 _27495 P t m)). Qed.
Lemma lem1179936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179937 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term573 _27494 _27495 P t m) = (term574 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1179936) (@lem1179935 _27494 _27495 P t m)). Qed.
Lemma lem1179938 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term569 _27494 _27495 t m P x) = (term534 _27494 _27495 t m P x).
Proof. exact (eq_refl (term569 _27494 _27495 t m P x)). Qed.
Lemma lem1179939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179940 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term575 _27494 _27495 t m P x) = (term576 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1179939) (@lem1179938 _27494 _27495 t m P x)). Qed.
Lemma lem1179941 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179942 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term577 _27494 _27495 x P t m) = (term578 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1179940 _27494 _27495 t m P x) (@lem1179941 _27494 _27495 P t m)). Qed.
Lemma lem1179943 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term579 _27494 _27495 P t m) = (term580 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1179942 _27494 _27495 x P t m)). Qed.
Lemma lem1179944 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179945 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term568 _27494 _27495 P t m) = (term581 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1179944 _27495) (@lem1179943 _27494 _27495 P t m)). Qed.
Lemma lem1179946 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term567 _27494 _27495 P t m) = (term568 _27494 _27495 P t m)) = ((term538 _27494 _27495 P t m) = (term581 _27494 _27495 P t m)).
Proof. exact (MK_COMB (@lem1179937 _27494 _27495 P t m) (@lem1179945 _27494 _27495 P t m)). Qed.
Lemma lem1179947 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term538 _27494 _27495 P t m) = (term581 _27494 _27495 P t m).
Proof. exact (EQ_MP (@lem1179946 _27494 _27495 P t m) (@lem1179927 _27494 _27495 P t m)). Qed.
Lemma lem1179949 {A : Type'} (P : A -> Prop) (Q : Prop) : (term565 A P Q) = (term566 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1179950 {_27494 : Type'} (P : _27494 -> Prop) (Q : Prop) : (term565 _27494 P Q) = (term566 _27494 P Q).
Proof. exact (@lem1179949 _27494 P Q). Qed.
Lemma lem1179951 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term582 _27494 _27495 x P t m) = (term583 _27494 _27495 x P t m).
Proof. exact (@lem1179950 _27494 (term533 _27494 _27495 t m P x) (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179952 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term584 _27494 _27495 t m P x y) = (term532 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term584 _27494 _27495 t m P x y)). Qed.
Lemma lem1179953 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term585 _27494 _27495 t m P x) = (term533 _27494 _27495 t m P x).
Proof. exact (fun_ext (fun y : _27494 => @lem1179952 _27494 _27495 t m P x y)). Qed.
Lemma lem1179954 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179955 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term586 _27494 _27495 t m P x) = (term534 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1179954 _27494) (@lem1179953 _27494 _27495 t m P x)). Qed.
Lemma lem1179956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179957 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) : (term587 _27494 _27495 t m P x) = (term576 _27494 _27495 t m P x).
Proof. exact (MK_COMB (@lem1179956) (@lem1179955 _27494 _27495 t m P x)). Qed.
Lemma lem1179958 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179959 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term582 _27494 _27495 x P t m) = (term578 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1179957 _27494 _27495 t m P x) (@lem1179958 _27494 _27495 P t m)). Qed.
Lemma lem1179960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1179961 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term588 _27494 _27495 x P t m) = (term589 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1179960) (@lem1179959 _27494 _27495 x P t m)). Qed.
Lemma lem1179962 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term584 _27494 _27495 t m P x y) = (term532 _27494 _27495 t m P x y).
Proof. exact (eq_refl (term584 _27494 _27495 t m P x y)). Qed.
Lemma lem1179963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1179964 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (x : _27495) (y : _27494) : (term590 _27494 _27495 t m P x y) = (term591 _27494 _27495 t m P x y).
Proof. exact (MK_COMB (@lem1179963) (@lem1179962 _27494 _27495 t m P x y)). Qed.
Lemma lem1179965 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (eq_refl (term159 _27494 _27495 P t m)). Qed.
Lemma lem1179966 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term592 _27494 _27495 x y P t m) = (term593 _27494 _27495 x y P t m).
Proof. exact (MK_COMB (@lem1179964 _27494 _27495 t m P x y) (@lem1179965 _27494 _27495 P t m)). Qed.
Lemma lem1179967 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term594 _27494 _27495 x P t m) = (term595 _27494 _27495 x P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1179966 _27494 _27495 x y P t m)). Qed.
Lemma lem1179968 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1179969 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term583 _27494 _27495 x P t m) = (term596 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1179968 _27494) (@lem1179967 _27494 _27495 x P t m)). Qed.
Lemma lem1179970 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : ((term582 _27494 _27495 x P t m) = (term583 _27494 _27495 x P t m)) = ((term578 _27494 _27495 x P t m) = (term596 _27494 _27495 x P t m)).
Proof. exact (MK_COMB (@lem1179961 _27494 _27495 x P t m) (@lem1179969 _27494 _27495 x P t m)). Qed.
Lemma lem1179971 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term578 _27494 _27495 x P t m) = (term596 _27494 _27495 x P t m).
Proof. exact (EQ_MP (@lem1179970 _27494 _27495 x P t m) (@lem1179951 _27494 _27495 x P t m)). Qed.
Lemma lem1179972 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term580 _27494 _27495 P t m) = (term597 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1179971 _27494 _27495 x P t m)). Qed.
Lemma lem1179973 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1179974 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term581 _27494 _27495 P t m) = (term598 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1179973 _27495) (@lem1179972 _27494 _27495 P t m)). Qed.
Lemma lem1179975 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term538 _27494 _27495 P t m) = (term598 _27494 _27495 P t m).
Proof. exact (TRANS (@lem1179947 _27494 _27495 P t m) (@lem1179974 _27494 _27495 P t m)). Qed.
Lemma lem1179976 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term539 _27494 _27495 P t) = (term599 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1179975 _27494 _27495 P t m)). Qed.
Lemma lem1179977 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1179978 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term540 _27494 _27495 P t) = (term600 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1179977 _27494) (@lem1179976 _27494 _27495 P t)). Qed.
Lemma lem1179997 {_27494 _27495 : Type'} (x : _27495) (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term593 _27494 _27495 x y P t m) = (term593 _27494 _27495 x y P t m).
Proof. exact (eq_refl (term593 _27494 _27495 x y P t m)). Qed.
Lemma lem1179998 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term595 _27494 _27495 x P t m) = (term595 _27494 _27495 x P t m).
Proof. exact (fun_ext (fun y : _27494 => @lem1179997 _27494 _27495 x y P t m)). Qed.
Lemma lem1179999 {_27494 : Type'} : (@all _27494) = (@all _27494).
Proof. exact (eq_refl (@all _27494)). Qed.
Lemma lem1180000 {_27494 _27495 : Type'} (x : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term596 _27494 _27495 x P t m) = (term596 _27494 _27495 x P t m).
Proof. exact (MK_COMB (@lem1179999 _27494) (@lem1179998 _27494 _27495 x P t m)). Qed.
Lemma lem1180001 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term597 _27494 _27495 P t m) = (term597 _27494 _27495 P t m).
Proof. exact (fun_ext (fun x : _27495 => @lem1180000 _27494 _27495 x P t m)). Qed.
Lemma lem1180002 {_27495 : Type'} : (@all _27495) = (@all _27495).
Proof. exact (eq_refl (@all _27495)). Qed.
Lemma lem1180003 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term598 _27494 _27495 P t m) = (term598 _27494 _27495 P t m).
Proof. exact (MK_COMB (@lem1180002 _27495) (@lem1180001 _27494 _27495 P t m)). Qed.
Lemma lem1180004 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term599 _27494 _27495 P t) = (term599 _27494 _27495 P t).
Proof. exact (fun_ext (fun m : list _27494 => @lem1180003 _27494 _27495 P t m)). Qed.
Lemma lem1180005 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1180006 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term600 _27494 _27495 P t) = (term600 _27494 _27495 P t).
Proof. exact (MK_COMB (@lem1180005 _27494) (@lem1180004 _27494 _27495 P t)). Qed.
Lemma lem1180007 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term540 _27494 _27495 P t) = (term600 _27494 _27495 P t).
Proof. exact (TRANS (@lem1179978 _27494 _27495 P t) (@lem1180006 _27494 _27495 P t)). Qed.
Lemma lem1180008 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term600 _27494 _27495 P t.
Proof. exact (EQ_MP (@lem1180007 _27494 _27495 P t) (@lem1179434 _27494 _27495 x'' y' P t h1)). Qed.
Lemma lem1180070 {_27495 : Type'} (x' : _27495) (t : list _27495) (h1 : @List.In _27495 x' t) : @List.In _27495 x' t.
Proof. exact (h1). Qed.
Lemma lem1180083 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term601 _27494 _27495 h t m P _21072.
Proof. exact (@lem1179608 _27494 _27495 h x P t m h1 _21072). Qed.
Lemma lem1180084 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) : (term601 _27494 _27495 h t m P _21072) = (term550 _27494 _27495 h t m P _21072).
Proof. exact (eq_refl (term601 _27494 _27495 h t m P _21072)). Qed.
Lemma lem1180085 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term550 _27494 _27495 h t m P _21072.
Proof. exact (EQ_MP (@lem1180084 _27494 _27495 h t m P _21072) (@lem1180083 _27494 _27495 _21072 h x P t m h1)). Qed.
Lemma lem1180086 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term602 _27494 _27495 h t m P _21072 _21073.
Proof. exact (@lem1180085 _27494 _27495 _21072 h x P t m h1 _21073). Qed.
Lemma lem1180087 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term602 _27494 _27495 h t m P _21072 _21073) = (term547 _27494 _27495 h t m P _21072 _21073).
Proof. exact (eq_refl (term602 _27494 _27495 h t m P _21072 _21073)). Qed.
Lemma lem1180088 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term547 _27494 _27495 h t m P _21072 _21073.
Proof. exact (EQ_MP (@lem1180087 _27494 _27495 h t m P _21072 _21073) (@lem1180086 _27494 _27495 _21072 _21073 h x P t m h1)). Qed.
Lemma lem1180098 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term603 _27494 _27495 x'' y' P t _21077.
Proof. exact (@lem1179734 _27494 _27495 x'' y' P t h1 _21077). Qed.
Lemma lem1180099 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21077 : list _27494) : (term603 _27494 _27495 x'' y' P t _21077) = (term562 _27494 _27495 x'' y' P t _21077).
Proof. exact (eq_refl (term603 _27494 _27495 x'' y' P t _21077)). Qed.
Lemma lem1180100 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term562 _27494 _27495 x'' y' P t _21077.
Proof. exact (EQ_MP (@lem1180099 _27494 _27495 x'' y' P t _21077) (@lem1180098 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180101 {_27494 _27495 : Type'} (_21078 : _27495) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term601 _27494 _27495 h t m P _21078.
Proof. exact (@lem1179772 _27494 _27495 h x P t m h1 _21078). Qed.
Lemma lem1180102 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21078 : _27495) : (term601 _27494 _27495 h t m P _21078) = (term550 _27494 _27495 h t m P _21078).
Proof. exact (eq_refl (term601 _27494 _27495 h t m P _21078)). Qed.
Lemma lem1180103 {_27494 _27495 : Type'} (_21078 : _27495) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term550 _27494 _27495 h t m P _21078.
Proof. exact (EQ_MP (@lem1180102 _27494 _27495 h t m P _21078) (@lem1180101 _27494 _27495 _21078 h x P t m h1)). Qed.
Lemma lem1180104 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term602 _27494 _27495 h t m P _21078 _21079.
Proof. exact (@lem1180103 _27494 _27495 _21078 h x P t m h1 _21079). Qed.
Lemma lem1180105 {_27494 _27495 : Type'} (h : _27495) (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term602 _27494 _27495 h t m P _21078 _21079) = (term547 _27494 _27495 h t m P _21078 _21079).
Proof. exact (eq_refl (term602 _27494 _27495 h t m P _21078 _21079)). Qed.
Lemma lem1180106 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term547 _27494 _27495 h t m P _21078 _21079.
Proof. exact (EQ_MP (@lem1180105 _27494 _27495 h t m P _21078 _21079) (@lem1180104 _27494 _27495 _21078 _21079 h x P t m h1)). Qed.
Lemma lem1180119 {_27494 _27495 : Type'} (_21084 : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term604 _27494 _27495 m P h _21084.
Proof. exact (@lem1179907 _27494 _27495 x' y h P t m h1 _21084). Qed.
Lemma lem1180120 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) : (term604 _27494 _27495 m P h _21084) = (term493 _27494 _27495 m P h _21084).
Proof. exact (eq_refl (term604 _27494 _27495 m P h _21084)). Qed.
Lemma lem1180122 {_27494 _27495 : Type'} (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term605 _27494 _27495 P t _21085.
Proof. exact (@lem1180008 _27494 _27495 x'' y' P t h1 _21085). Qed.
Lemma lem1180123 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term605 _27494 _27495 P t _21085) = (term598 _27494 _27495 P t _21085).
Proof. exact (eq_refl (term605 _27494 _27495 P t _21085)). Qed.
Lemma lem1180124 {_27494 _27495 : Type'} (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term598 _27494 _27495 P t _21085.
Proof. exact (EQ_MP (@lem1180123 _27494 _27495 P t _21085) (@lem1180122 _27494 _27495 _21085 x'' y' P t h1)). Qed.
Lemma lem1180125 {_27494 _27495 : Type'} (_21085 : list _27494) (_21086 : _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term606 _27494 _27495 P t _21085 _21086.
Proof. exact (@lem1180124 _27494 _27495 _21085 x'' y' P t h1 _21086). Qed.
Lemma lem1180126 {_27494 _27495 : Type'} (_21086 : _27495) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term606 _27494 _27495 P t _21085 _21086) = (term596 _27494 _27495 _21086 P t _21085).
Proof. exact (eq_refl (term606 _27494 _27495 P t _21085 _21086)). Qed.
Lemma lem1180127 {_27494 _27495 : Type'} (_21086 : _27495) (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term596 _27494 _27495 _21086 P t _21085.
Proof. exact (EQ_MP (@lem1180126 _27494 _27495 _21086 P t _21085) (@lem1180125 _27494 _27495 _21085 _21086 x'' y' P t h1)). Qed.
Lemma lem1180128 {_27494 _27495 : Type'} (_21086 : _27495) (_21085 : list _27494) (_21087 : _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term607 _27494 _27495 _21086 P t _21085 _21087.
Proof. exact (@lem1180127 _27494 _27495 _21086 _21085 x'' y' P t h1 _21087). Qed.
Lemma lem1180129 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term607 _27494 _27495 _21086 P t _21085 _21087) = (term593 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (eq_refl (term607 _27494 _27495 _21086 P t _21085 _21087)). Qed.
Lemma lem1180130 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term593 _27494 _27495 _21086 _21087 P t _21085.
Proof. exact (EQ_MP (@lem1180129 _27494 _27495 _21086 _21087 P t _21085) (@lem1180128 _27494 _27495 _21086 _21085 _21087 x'' y' P t h1)). Qed.
Lemma lem1180138 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term608 _27494 _27495 h m P _21072 _21073.
Proof. exact (proj1 (@lem1180088 _27494 _27495 _21072 _21073 h x P t m h1)). Qed.
Lemma lem1180143 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term532 _27494 _27495 t m P _21078 _21079.
Proof. exact (proj2 (@lem1180106 _27494 _27495 _21078 _21079 h x P t m h1)). Qed.
Lemma lem1180146 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term557 _27494 _27495 x'' y' P t _21077.
Proof. exact (proj1 (@lem1180100 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180178 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : term499 _27494 _27495 P h x.
Proof. exact (proj2 (@lem1179439 _27494 _27495 m P h x h1)). Qed.
Lemma lem1180189 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term608 _27494 _27495 h m P _21072 _21073) = (term609 _27494 _27495 h m P _21072 _21073).
Proof. exact (@lem1177689 (term544 _27495 _21072 h) (term321 _27494 _21073 m) (term491 _27494 _27495 P _21072 _21073)). Qed.
Lemma lem1180190 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term609 _27494 _27495 h m P _21072 _21073.
Proof. exact (EQ_MP (@lem1180189 _27494 _27495 h m P _21072 _21073) (@lem1180138 _27494 _27495 _21072 _21073 h x P t m h1)). Qed.
Lemma lem1180240 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (h1). Qed.
Lemma lem1180263 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term532 _27494 _27495 t m P _21078 _21079) = (term610 _27494 _27495 t m P _21078 _21079).
Proof. exact (@lem1177689 (term321 _27495 _21078 t) (term321 _27494 _21079 m) (term491 _27494 _27495 P _21078 _21079)). Qed.
Lemma lem1180264 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term610 _27494 _27495 t m P _21078 _21079.
Proof. exact (EQ_MP (@lem1180263 _27494 _27495 t m P _21078 _21079) (@lem1180143 _27494 _27495 _21078 _21079 h x P t m h1)). Qed.
Lemma lem1180270 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term555 _27494 _27495 x'' y' P t _21077.
Proof. exact (proj2 (@lem1180100 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180276 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term611 _27494 _27495 x'' P t _21077.
Proof. exact (proj1 (@lem1180146 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180282 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term612 _27494 _27495 y' P t _21077.
Proof. exact (proj2 (@lem1180146 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180310 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term499 _27494 _27495 P x' y.
Proof. exact (proj2 (@lem1179444 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1180314 {_27495 : Type'} (x' : _27495) (h : _27495) (h1 : x' = h) : x' = h.
Proof. exact (h1). Qed.
Lemma lem1180336 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term593 _27494 _27495 _21086 _21087 P t _21085) = (term613 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (@lem1177689 (term131 _27494 _27495 _21086 t _21087 _21085) (term491 _27494 _27495 P _21086 _21087) (term159 _27494 _27495 P t _21085)). Qed.
Lemma lem1180347 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term613 _27494 _27495 _21086 _21087 P t _21085) = (term614 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (@lem1177689 (term321 _27495 _21086 t) (term321 _27494 _21087 _21085) (term615 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1180349 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term593 _27494 _27495 _21086 _21087 P t _21085) = (term614 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (TRANS (@lem1180336 _27494 _27495 _21086 _21087 P t _21085) (@lem1180347 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1180350 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term614 _27494 _27495 _21086 _21087 P t _21085.
Proof. exact (EQ_MP (@lem1180349 _27494 _27495 _21086 _21087 P t _21085) (@lem1180130 _27494 _27495 _21086 _21087 _21085 x'' y' P t h1)). Qed.
Lemma lem1180360 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term499 _27494 _27495 P x' y.
Proof. exact (proj2 (@lem1179444 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1180364 {_27495 : Type'} (x' : _27495) (t : list _27495) (h1 : @List.In _27495 x' t) : @List.In _27495 x' t.
Proof. exact (h1). Qed.
Lemma lem1180424 {_27494 _27495 : Type'} (_21084 : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term493 _27494 _27495 m P h _21084.
Proof. exact (EQ_MP (@lem1180120 _27494 _27495 m P h _21084) (@lem1180119 _27494 _27495 _21084 x' y h P t m h1)). Qed.
Lemma lem1180439 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (y : _27494) : (term616 _27494 _27495 P y) = (term616 _27494 _27495 P y).
Proof. exact (eq_refl (term616 _27494 _27495 P y)). Qed.
Lemma lem1180440 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (y : _27494) (x' : _27495) (h : _27495) (h1 : x' = h) : (term617 _27494 _27495 P y x') = (term617 _27494 _27495 P y h).
Proof. exact (MK_COMB (@lem1180439 _27494 _27495 P y) (@lem1180314 _27495 x' h h1)). Qed.
Lemma lem1180441 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : (term617 _27494 _27495 P y h) = (term499 _27494 _27495 P h y).
Proof. exact (eq_refl (term617 _27494 _27495 P y h)). Qed.
Lemma lem1180442 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (y : _27494) (x' : _27495) : (term618 _27494 _27495 P y x') = (term618 _27494 _27495 P y x').
Proof. exact (eq_refl (term618 _27494 _27495 P y x')). Qed.
Lemma lem1180443 {_27494 _27495 : Type'} (x' : _27495) (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : ((term617 _27494 _27495 P y x') = (term617 _27494 _27495 P y h)) = ((term617 _27494 _27495 P y x') = (term499 _27494 _27495 P h y)).
Proof. exact (MK_COMB (@lem1180442 _27494 _27495 P y x') (@lem1180441 _27494 _27495 P h y)). Qed.
Lemma lem1180444 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term617 _27494 _27495 P y x') = (term499 _27494 _27495 P x' y).
Proof. exact (eq_refl (term617 _27494 _27495 P y x')). Qed.
Lemma lem1180445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1180446 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term618 _27494 _27495 P y x') = (term619 _27494 _27495 P x' y).
Proof. exact (MK_COMB (@lem1180445) (@lem1180444 _27494 _27495 P x' y)). Qed.
Lemma lem1180447 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : (term499 _27494 _27495 P h y) = (term499 _27494 _27495 P h y).
Proof. exact (eq_refl (term499 _27494 _27495 P h y)). Qed.
Lemma lem1180448 {_27494 _27495 : Type'} (x' : _27495) (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : ((term617 _27494 _27495 P y x') = (term499 _27494 _27495 P h y)) = ((term499 _27494 _27495 P x' y) = (term499 _27494 _27495 P h y)).
Proof. exact (MK_COMB (@lem1180446 _27494 _27495 P x' y) (@lem1180447 _27494 _27495 P h y)). Qed.
Lemma lem1180449 {_27494 _27495 : Type'} (x' : _27495) (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : ((term617 _27494 _27495 P y x') = (term617 _27494 _27495 P y h)) = ((term499 _27494 _27495 P x' y) = (term499 _27494 _27495 P h y)).
Proof. exact (TRANS (@lem1180443 _27494 _27495 x' P h y) (@lem1180448 _27494 _27495 x' P h y)). Qed.
Lemma lem1180450 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (y : _27494) (x' : _27495) (h : _27495) (h1 : x' = h) : (term499 _27494 _27495 P x' y) = (term499 _27494 _27495 P h y).
Proof. exact (EQ_MP (@lem1180449 _27494 _27495 x' P h y) (@lem1180440 _27494 _27495 P y x' h h1)). Qed.
Lemma lem1180451 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : term499 _27494 _27495 P h y.
Proof. exact (EQ_MP (@lem1180450 _27494 _27495 P y x' h h2) (@lem1180310 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1180635 {_27495 : Type'} (x : _27495) : x = x.
Proof. exact (@lem21386 _27495 x). Qed.
Lemma lem1180636 {_27495 : Type'} (x : _27495) : x = x.
Proof. exact (@lem1180635 _27495 x). Qed.
Lemma lem1180637 {_27495 : Type'} (h : _27495) : h = h.
Proof. exact (@lem1180636 _27495 h). Qed.
Lemma lem1180638 {_27495 : Type'} (h : _27495) : term620 _27495 h.
Proof. exact (fun h0 : term621 _27495 h => @lem1180637 _27495 h). Qed.
Lemma lem1180640 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1180641 {_27495 : Type'} (h : _27495) : (term620 _27495 h) = (h = h).
Proof. exact (@lem1180640 (h = h)). Qed.
Lemma lem1180642 {_27495 : Type'} (h : _27495) : h = h.
Proof. exact (EQ_MP (@lem1180641 _27495 h) (@lem1180638 _27495 h)). Qed.
Lemma lem1180644 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : @List.In _27494 x m.
Proof. exact (proj1 (@lem1179439 _27494 _27495 m P h x h1)). Qed.
Lemma lem1180645 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : term623 _27494 x m.
Proof. exact (fun h0 : term321 _27494 x m => @lem1180644 _27494 _27495 m P h x h1). Qed.
Lemma lem1180647 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1180648 {_27494 : Type'} (x : _27494) (m : list _27494) : (term623 _27494 x m) = (@List.In _27494 x m).
Proof. exact (@lem1180647 (@List.In _27494 x m)). Qed.
Lemma lem1180649 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : @List.In _27494 x m.
Proof. exact (EQ_MP (@lem1180648 _27494 x m) (@lem1180645 _27494 _27495 m P h x h1)). Qed.
Lemma lem1180667 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1180668 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) (m : list _27494) : (term493 _27494 _27495 m P _21072 _21073) = (term624 _27494 _27495 P _21072 _21073 m).
Proof. exact (@lem1180667 (term491 _27494 _27495 P _21072 _21073) (term321 _27494 _21073 m)). Qed.
Lemma lem1180674 {_27495 : Type'} (_21072 : _27495) (h : _27495) : (term625 _27495 _21072 h) = (term625 _27495 _21072 h).
Proof. exact (eq_refl (term625 _27495 _21072 h)). Qed.
Lemma lem1180675 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) (m : list _27494) : (term609 _27494 _27495 h m P _21072 _21073) = (term626 _27494 _27495 h P _21072 _21073 m).
Proof. exact (MK_COMB (@lem1180674 _27495 _21072 h) (@lem1180668 _27494 _27495 P _21072 _21073 m)). Qed.
Lemma lem1180679 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1180680 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term626 _27494 _27495 h P _21072 _21073 m) = (term627 _27494 _27495 P _21072 h _21073 m).
Proof. exact (@lem1180679 (term491 _27494 _27495 P _21072 _21073) (term544 _27495 _21072 h) (term321 _27494 _21073 m)). Qed.
Lemma lem1180698 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term609 _27494 _27495 h m P _21072 _21073) = (term627 _27494 _27495 P _21072 h _21073 m).
Proof. exact (TRANS (@lem1180675 _27494 _27495 h P _21072 _21073 m) (@lem1180680 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1180700 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term628 _27494 _27495 h m P _21072 _21073) = (term629 _27494 _27495 P _21072 h _21073 m).
Proof. exact (MK_COMB (@lem1180699) (@lem1180698 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180718 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term627 _27494 _27495 P _21072 h _21073 m) = (term627 _27494 _27495 P _21072 h _21073 m).
Proof. exact (eq_refl (term627 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180719 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : ((term609 _27494 _27495 h m P _21072 _21073) = (term627 _27494 _27495 P _21072 h _21073 m)) = ((term627 _27494 _27495 P _21072 h _21073 m) = (term627 _27494 _27495 P _21072 h _21073 m)).
Proof. exact (MK_COMB (@lem1180700 _27494 _27495 P _21072 h _21073 m) (@lem1180718 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180721 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1180722 (x : Prop) : (x = x) = True.
Proof. exact (@lem1180721 Prop x). Qed.
Lemma lem1180723 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : ((term627 _27494 _27495 P _21072 h _21073 m) = (term627 _27494 _27495 P _21072 h _21073 m)) = True.
Proof. exact (@lem1180722 (term627 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180724 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : ((term609 _27494 _27495 h m P _21072 _21073) = (term627 _27494 _27495 P _21072 h _21073 m)) = True.
Proof. exact (TRANS (@lem1180719 _27494 _27495 P _21072 h _21073 m) (@lem1180723 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180725 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : True = ((term609 _27494 _27495 h m P _21072 _21073) = (term627 _27494 _27495 P _21072 h _21073 m)).
Proof. exact (SYM (@lem1180724 _27494 _27495 P _21072 h _21073 m)). Qed.
Lemma lem1180726 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term609 _27494 _27495 h m P _21072 _21073) = (term627 _27494 _27495 P _21072 h _21073 m).
Proof. exact (EQ_MP (@lem1180725 _27494 _27495 P _21072 h _21073 m) (@lem0)). Qed.
Lemma lem1180727 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term627 _27494 _27495 P _21072 h _21073 m.
Proof. exact (EQ_MP (@lem1180726 _27494 _27495 P _21072 h _21073 m) (@lem1180190 _27494 _27495 _21072 _21073 h x P t m h1)). Qed.
Lemma lem1180729 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1180730 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term627 _27494 _27495 P _21072 h _21073 m) = (term631 _27494 _27495 h m P _21072 _21073).
Proof. exact (@lem1180729 (term548 _27494 _27495 _21072 h _21073 m) (term491 _27494 _27495 P _21072 _21073)). Qed.
Lemma lem1180732 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1180733 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term634 _27494 _27495 _21072 h _21073 m) = (term635 _27494 _27495 _21072 h _21073 m).
Proof. exact (@lem1180732 (term544 _27495 _21072 h) (term321 _27494 _21073 m)). Qed.
Lemma lem1180735 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1180736 {_27495 : Type'} (_21072 : _27495) (h : _27495) : (term636 _27495 _21072 h) = (_21072 = h).
Proof. exact (@lem1180735 (_21072 = h)). Qed.
Lemma lem1180737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1180738 {_27495 : Type'} (_21072 : _27495) (h : _27495) : (term637 _27495 _21072 h) = (term638 _27495 _21072 h).
Proof. exact (MK_COMB (@lem1180737) (@lem1180736 _27495 _21072 h)). Qed.
Lemma lem1180740 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1180741 {_27494 : Type'} (_21073 : _27494) (m : list _27494) : (term639 _27494 _21073 m) = (@List.In _27494 _21073 m).
Proof. exact (@lem1180740 (@List.In _27494 _21073 m)). Qed.
Lemma lem1180742 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term635 _27494 _27495 _21072 h _21073 m) = (term640 _27494 _27495 _21072 h _21073 m).
Proof. exact (MK_COMB (@lem1180738 _27495 _21072 h) (@lem1180741 _27494 _21073 m)). Qed.
Lemma lem1180743 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term634 _27494 _27495 _21072 h _21073 m) = (term640 _27494 _27495 _21072 h _21073 m).
Proof. exact (TRANS (@lem1180733 _27494 _27495 _21072 h _21073 m) (@lem1180742 _27494 _27495 _21072 h _21073 m)). Qed.
Lemma lem1180744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1180745 {_27494 _27495 : Type'} (_21072 : _27495) (h : _27495) (_21073 : _27494) (m : list _27494) : (term641 _27494 _27495 _21072 h _21073 m) = (term642 _27494 _27495 _21072 h _21073 m).
Proof. exact (MK_COMB (@lem1180744) (@lem1180743 _27494 _27495 _21072 h _21073 m)). Qed.
Lemma lem1180746 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term491 _27494 _27495 P _21072 _21073) = (term491 _27494 _27495 P _21072 _21073).
Proof. exact (eq_refl (term491 _27494 _27495 P _21072 _21073)). Qed.
Lemma lem1180747 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term631 _27494 _27495 h m P _21072 _21073) = (term643 _27494 _27495 h m P _21072 _21073).
Proof. exact (MK_COMB (@lem1180745 _27494 _27495 _21072 h _21073 m) (@lem1180746 _27494 _27495 P _21072 _21073)). Qed.
Lemma lem1180748 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (_21072 : _27495) (_21073 : _27494) : (term627 _27494 _27495 P _21072 h _21073 m) = (term643 _27494 _27495 h m P _21072 _21073).
Proof. exact (TRANS (@lem1180730 _27494 _27495 h m P _21072 _21073) (@lem1180747 _27494 _27495 h m P _21072 _21073)). Qed.
Lemma lem1180750 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : term644 _27494 _27495 h x m.
Proof. exact (conj (@lem1180642 _27495 h) (@lem1180649 _27494 _27495 m P h x h1)). Qed.
Lemma lem1180752 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term643 _27494 _27495 h m P _21072 _21073.
Proof. exact (EQ_MP (@lem1180748 _27494 _27495 h m P _21072 _21073) (@lem1180727 _27494 _27495 _21072 _21073 h x P t m h1)). Qed.
Lemma lem1180753 {_27494 _27495 : Type'} (_21072 : _27495) (_21073 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term643 _27494 _27495 h m P _21072 _21073.
Proof. exact (@lem1180752 _27494 _27495 _21072 _21073 h x P t m h1). Qed.
Lemma lem1180754 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term645 _27494 _27495 m P h x.
Proof. exact (@lem1180753 _27494 _27495 h x h x P t m h1). Qed.
Lemma lem1180757 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : term491 _27494 _27495 P h x.
Proof. exact (@lem1180754 _27494 _27495 h x P t m h1 (@lem1180750 _27494 _27495 m P h x h2)). Qed.
Lemma lem1180758 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : term646 _27494 _27495 P h x.
Proof. exact (fun h0 : term499 _27494 _27495 P h x => @lem1180757 _27494 _27495 t m P h x h1 h2). Qed.
Lemma lem1180760 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1180761 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term646 _27494 _27495 P h x) = (term491 _27494 _27495 P h x).
Proof. exact (@lem1180760 (term491 _27494 _27495 P h x)). Qed.
Lemma lem1180762 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : term491 _27494 _27495 P h x.
Proof. exact (EQ_MP (@lem1180761 _27494 _27495 P h x) (@lem1180758 _27494 _27495 t m P h x h1 h2)). Qed.
Lemma lem1180765 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1180767 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (x : _27494) : (term499 _27494 _27495 P h x) = (term647 _27494 _27495 P h x).
Proof. exact (@lem1180765 (term491 _27494 _27495 P h x)). Qed.
Lemma lem1180770 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term505 _27494 _27495 m P h x) : term647 _27494 _27495 P h x.
Proof. exact (EQ_MP (@lem1180767 _27494 _27495 P h x) (@lem1180178 _27494 _27495 m P h x h1)). Qed.
Lemma lem1180773 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : False.
Proof. exact (@lem1180770 _27494 _27495 m P h x h2 (@lem1180762 _27494 _27495 t m P h x h1 h2)). Qed.
Lemma lem1180774 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : term648.
Proof. exact (fun h0 : ~ False => @lem1180773 _27494 _27495 t m P h x h1 h2). Qed.
Lemma lem1180776 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1180777 : term648 = False.
Proof. exact (@lem1180776 False). Qed.
Lemma lem1180778 {_27494 _27495 : Type'} (t : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (x : _27494) (h1 : term514 _27494 _27495 h x P t m) (h2 : term505 _27494 _27495 m P h x) : False.
Proof. exact (EQ_MP (@lem1180777) (@lem1180774 _27494 _27495 t m P h x h1 h2)). Qed.
Lemma lem1180907 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (h1). Qed.
Lemma lem1180908 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term649 _27494 _27495 P t m.
Proof. exact (fun h0 : @ALLPAIRS _27494 _27495 P t m => @lem1180907 _27494 _27495 P t m h1). Qed.
Lemma lem1180910 (p : Prop) : (term650 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1180911 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term649 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (@lem1180910 (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1180912 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (EQ_MP (@lem1180911 _27494 _27495 P t m) (@lem1180908 _27494 _27495 P t m h1)). Qed.
Lemma lem1180914 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1180917 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (_21077 : list _27494) (t : list _27495) : (term611 _27494 _27495 x'' P t _21077) = (term651 _27494 _27495 P x'' _21077 t).
Proof. exact (@lem1180914 (@ALLPAIRS _27494 _27495 P t _21077) (term558 _27494 _27495 x'' _21077 t)). Qed.
Lemma lem1180920 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term651 _27494 _27495 P x'' _21077 t.
Proof. exact (EQ_MP (@lem1180917 _27494 _27495 P x'' _21077 t) (@lem1180276 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180921 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term651 _27494 _27495 P x'' _21077 t.
Proof. exact (@lem1180920 _27494 _27495 _21077 x'' y' P t h1). Qed.
Lemma lem1180922 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term651 _27494 _27495 P x'' m t.
Proof. exact (@lem1180921 _27494 _27495 m x'' y' P t h1). Qed.
Lemma lem1180925 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term558 _27494 _27495 x'' m t.
Proof. exact (@lem1180922 _27494 _27495 m x'' y' P t h2 (@lem1180912 _27494 _27495 P t m h1)). Qed.
Lemma lem1180926 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term652 _27494 _27495 x'' m t.
Proof. exact (fun h0 : term653 _27494 _27495 x'' m t => @lem1180925 _27494 _27495 m x'' y' P t h1 h2). Qed.
Lemma lem1180928 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1180929 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (m : list _27494) (t : list _27495) : (term652 _27494 _27495 x'' m t) = (term558 _27494 _27495 x'' m t).
Proof. exact (@lem1180928 (term558 _27494 _27495 x'' m t)). Qed.
Lemma lem1180930 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term558 _27494 _27495 x'' m t.
Proof. exact (EQ_MP (@lem1180929 _27494 _27495 x'' m t) (@lem1180926 _27494 _27495 m x'' y' P t h1 h2)). Qed.
Lemma lem1180933 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (h1). Qed.
Lemma lem1180934 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term649 _27494 _27495 P t m.
Proof. exact (fun h0 : @ALLPAIRS _27494 _27495 P t m => @lem1180933 _27494 _27495 P t m h1). Qed.
Lemma lem1180936 (p : Prop) : (term650 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1180937 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term649 _27494 _27495 P t m) = (term159 _27494 _27495 P t m).
Proof. exact (@lem1180936 (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1180938 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term159 _27494 _27495 P t m.
Proof. exact (EQ_MP (@lem1180937 _27494 _27495 P t m) (@lem1180934 _27494 _27495 P t m h1)). Qed.
Lemma lem1180940 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1180943 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (_21077 : list _27494) : (term555 _27494 _27495 x'' y' P t _21077) = (term654 _27494 _27495 t P x'' y' _21077).
Proof. exact (@lem1180940 (@ALLPAIRS _27494 _27495 P t _21077) (term523 _27494 _27495 P x'' y' _21077)). Qed.
Lemma lem1180946 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term654 _27494 _27495 t P x'' y' _21077.
Proof. exact (EQ_MP (@lem1180943 _27494 _27495 t P x'' y' _21077) (@lem1180270 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1180947 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term654 _27494 _27495 t P x'' y' _21077.
Proof. exact (@lem1180946 _27494 _27495 _21077 x'' y' P t h1). Qed.
Lemma lem1180948 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term654 _27494 _27495 t P x'' y' m.
Proof. exact (@lem1180947 _27494 _27495 m x'' y' P t h1). Qed.
Lemma lem1180951 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term523 _27494 _27495 P x'' y' m.
Proof. exact (@lem1180948 _27494 _27495 m x'' y' P t h2 (@lem1180938 _27494 _27495 P t m h1)). Qed.
Lemma lem1180952 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term655 _27494 _27495 P x'' y' m.
Proof. exact (fun h0 : term521 _27494 _27495 P x'' y' m => @lem1180951 _27494 _27495 m x'' y' P t h1 h2). Qed.
Lemma lem1180954 (p : Prop) : (term650 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1180955 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (m : list _27494) : (term655 _27494 _27495 P x'' y' m) = (term523 _27494 _27495 P x'' y' m).
Proof. exact (@lem1180954 (term521 _27494 _27495 P x'' y' m)). Qed.
Lemma lem1180956 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term523 _27494 _27495 P x'' y' m.
Proof. exact (EQ_MP (@lem1180955 _27494 _27495 P x'' y' m) (@lem1180952 _27494 _27495 m x'' y' P t h1 h2)). Qed.
Lemma lem1180962 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1180963 {_27494 _27495 : Type'} (m : list _27494) (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term610 _27494 _27495 t m P _21078 _21079) = (term656 _27494 _27495 m t P _21078 _21079).
Proof. exact (@lem1180962 (term321 _27494 _21079 m) (term321 _27495 _21078 t) (term491 _27494 _27495 P _21078 _21079)). Qed.
Lemma lem1180977 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1180978 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (_21078 : _27495) (t : list _27495) : (term657 _27494 _27495 t P _21078 _21079) = (term658 _27494 _27495 P _21079 _21078 t).
Proof. exact (@lem1180977 (term491 _27494 _27495 P _21078 _21079) (term321 _27495 _21078 t)). Qed.
Lemma lem1180984 {_27494 : Type'} (_21079 : _27494) (m : list _27494) : (term492 _27494 _21079 m) = (term492 _27494 _21079 m).
Proof. exact (eq_refl (term492 _27494 _21079 m)). Qed.
Lemma lem1180985 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (_21079 : _27494) (_21078 : _27495) (t : list _27495) : (term656 _27494 _27495 m t P _21078 _21079) = (term659 _27494 _27495 m P _21079 _21078 t).
Proof. exact (MK_COMB (@lem1180984 _27494 _21079 m) (@lem1180978 _27494 _27495 P _21079 _21078 t)). Qed.
Lemma lem1180989 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1180990 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term659 _27494 _27495 m P _21079 _21078 t) = (term660 _27494 _27495 P _21079 m _21078 t).
Proof. exact (@lem1180989 (term491 _27494 _27495 P _21078 _21079) (term321 _27494 _21079 m) (term321 _27495 _21078 t)). Qed.
Lemma lem1181006 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term656 _27494 _27495 m t P _21078 _21079) = (term660 _27494 _27495 P _21079 m _21078 t).
Proof. exact (TRANS (@lem1180985 _27494 _27495 m P _21079 _21078 t) (@lem1180990 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181007 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term610 _27494 _27495 t m P _21078 _21079) = (term660 _27494 _27495 P _21079 m _21078 t).
Proof. exact (TRANS (@lem1180963 _27494 _27495 m t P _21078 _21079) (@lem1181006 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181009 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term661 _27494 _27495 t m P _21078 _21079) = (term662 _27494 _27495 P _21079 m _21078 t).
Proof. exact (MK_COMB (@lem1181008) (@lem1181007 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181023 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1181024 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (_21078 : _27495) (t : list _27495) : (term657 _27494 _27495 t P _21078 _21079) = (term658 _27494 _27495 P _21079 _21078 t).
Proof. exact (@lem1181023 (term491 _27494 _27495 P _21078 _21079) (term321 _27495 _21078 t)). Qed.
Lemma lem1181030 {_27494 : Type'} (_21079 : _27494) (m : list _27494) : (term492 _27494 _21079 m) = (term492 _27494 _21079 m).
Proof. exact (eq_refl (term492 _27494 _21079 m)). Qed.
Lemma lem1181031 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (_21079 : _27494) (_21078 : _27495) (t : list _27495) : (term656 _27494 _27495 m t P _21078 _21079) = (term659 _27494 _27495 m P _21079 _21078 t).
Proof. exact (MK_COMB (@lem1181030 _27494 _21079 m) (@lem1181024 _27494 _27495 P _21079 _21078 t)). Qed.
Lemma lem1181035 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181036 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term659 _27494 _27495 m P _21079 _21078 t) = (term660 _27494 _27495 P _21079 m _21078 t).
Proof. exact (@lem1181035 (term491 _27494 _27495 P _21078 _21079) (term321 _27494 _21079 m) (term321 _27495 _21078 t)). Qed.
Lemma lem1181052 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : (term656 _27494 _27495 m t P _21078 _21079) = (term660 _27494 _27495 P _21079 m _21078 t).
Proof. exact (TRANS (@lem1181031 _27494 _27495 m P _21079 _21078 t) (@lem1181036 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181053 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : ((term610 _27494 _27495 t m P _21078 _21079) = (term656 _27494 _27495 m t P _21078 _21079)) = ((term660 _27494 _27495 P _21079 m _21078 t) = (term660 _27494 _27495 P _21079 m _21078 t)).
Proof. exact (MK_COMB (@lem1181009 _27494 _27495 P _21079 m _21078 t) (@lem1181052 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1181056 (x : Prop) : (x = x) = True.
Proof. exact (@lem1181055 Prop x). Qed.
Lemma lem1181057 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21079 : _27494) (m : list _27494) (_21078 : _27495) (t : list _27495) : ((term660 _27494 _27495 P _21079 m _21078 t) = (term660 _27494 _27495 P _21079 m _21078 t)) = True.
Proof. exact (@lem1181056 (term660 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181058 {_27494 _27495 : Type'} (m : list _27494) (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : ((term610 _27494 _27495 t m P _21078 _21079) = (term656 _27494 _27495 m t P _21078 _21079)) = True.
Proof. exact (TRANS (@lem1181053 _27494 _27495 P _21079 m _21078 t) (@lem1181057 _27494 _27495 P _21079 m _21078 t)). Qed.
Lemma lem1181059 {_27494 _27495 : Type'} (m : list _27494) (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : True = ((term610 _27494 _27495 t m P _21078 _21079) = (term656 _27494 _27495 m t P _21078 _21079)).
Proof. exact (SYM (@lem1181058 _27494 _27495 m t P _21078 _21079)). Qed.
Lemma lem1181060 {_27494 _27495 : Type'} (m : list _27494) (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term610 _27494 _27495 t m P _21078 _21079) = (term656 _27494 _27495 m t P _21078 _21079).
Proof. exact (EQ_MP (@lem1181059 _27494 _27495 m t P _21078 _21079) (@lem0)). Qed.
Lemma lem1181061 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term656 _27494 _27495 m t P _21078 _21079.
Proof. exact (EQ_MP (@lem1181060 _27494 _27495 m t P _21078 _21079) (@lem1180264 _27494 _27495 _21078 _21079 h x P t m h1)). Qed.
Lemma lem1181063 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1181064 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) (m : list _27494) : (term656 _27494 _27495 m t P _21078 _21079) = (term663 _27494 _27495 t P _21078 _21079 m).
Proof. exact (@lem1181063 (term657 _27494 _27495 t P _21078 _21079) (term321 _27494 _21079 m)). Qed.
Lemma lem1181066 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1181067 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term664 _27494 _27495 t P _21078 _21079) = (term665 _27494 _27495 t P _21078 _21079).
Proof. exact (@lem1181066 (term321 _27495 _21078 t) (term491 _27494 _27495 P _21078 _21079)). Qed.
Lemma lem1181069 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1181070 {_27495 : Type'} (_21078 : _27495) (t : list _27495) : (term639 _27495 _21078 t) = (@List.In _27495 _21078 t).
Proof. exact (@lem1181069 (@List.In _27495 _21078 t)). Qed.
Lemma lem1181071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1181072 {_27495 : Type'} (_21078 : _27495) (t : list _27495) : (term666 _27495 _21078 t) = (term504 _27495 _21078 t).
Proof. exact (MK_COMB (@lem1181071) (@lem1181070 _27495 _21078 t)). Qed.
Lemma lem1181073 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term499 _27494 _27495 P _21078 _21079) = (term499 _27494 _27495 P _21078 _21079).
Proof. exact (eq_refl (term499 _27494 _27495 P _21078 _21079)). Qed.
Lemma lem1181074 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term665 _27494 _27495 t P _21078 _21079) = (term667 _27494 _27495 t P _21078 _21079).
Proof. exact (MK_COMB (@lem1181072 _27495 _21078 t) (@lem1181073 _27494 _27495 P _21078 _21079)). Qed.
Lemma lem1181075 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term664 _27494 _27495 t P _21078 _21079) = (term667 _27494 _27495 t P _21078 _21079).
Proof. exact (TRANS (@lem1181067 _27494 _27495 t P _21078 _21079) (@lem1181074 _27494 _27495 t P _21078 _21079)). Qed.
Lemma lem1181076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1181077 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) : (term668 _27494 _27495 t P _21078 _21079) = (term669 _27494 _27495 t P _21078 _21079).
Proof. exact (MK_COMB (@lem1181076) (@lem1181075 _27494 _27495 t P _21078 _21079)). Qed.
Lemma lem1181078 {_27494 : Type'} (_21079 : _27494) (m : list _27494) : (term321 _27494 _21079 m) = (term321 _27494 _21079 m).
Proof. exact (eq_refl (term321 _27494 _21079 m)). Qed.
Lemma lem1181079 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) (m : list _27494) : (term663 _27494 _27495 t P _21078 _21079 m) = (term670 _27494 _27495 t P _21078 _21079 m).
Proof. exact (MK_COMB (@lem1181077 _27494 _27495 t P _21078 _21079) (@lem1181078 _27494 _21079 m)). Qed.
Lemma lem1181080 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) (_21078 : _27495) (_21079 : _27494) (m : list _27494) : (term656 _27494 _27495 m t P _21078 _21079) = (term670 _27494 _27495 t P _21078 _21079 m).
Proof. exact (TRANS (@lem1181064 _27494 _27495 t P _21078 _21079 m) (@lem1181079 _27494 _27495 t P _21078 _21079 m)). Qed.
Lemma lem1181082 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term671 _27494 _27495 t P x'' y' m.
Proof. exact (conj (@lem1180930 _27494 _27495 m x'' y' P t h1 h2) (@lem1180956 _27494 _27495 m x'' y' P t h1 h2)). Qed.
Lemma lem1181084 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term670 _27494 _27495 t P _21078 _21079 m.
Proof. exact (EQ_MP (@lem1181080 _27494 _27495 t P _21078 _21079 m) (@lem1181061 _27494 _27495 _21078 _21079 h x P t m h1)). Qed.
Lemma lem1181085 {_27494 _27495 : Type'} (_21078 : _27495) (_21079 : _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term670 _27494 _27495 t P _21078 _21079 m.
Proof. exact (@lem1181084 _27494 _27495 _21078 _21079 h x P t m h1). Qed.
Lemma lem1181086 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (h : _27495) (x : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term514 _27494 _27495 h x P t m) : term672 _27494 _27495 t P x'' y' m.
Proof. exact (@lem1181085 _27494 _27495 (x'' m) (y' m) h x P t m h1). Qed.
Lemma lem1181089 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : term673 _27494 y' m.
Proof. exact (@lem1181086 _27494 _27495 x'' y' h x P t m h2 (@lem1181082 _27494 _27495 m x'' y' P t h1 h3)). Qed.
Lemma lem1181090 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : term674 _27494 y' m.
Proof. exact (fun h0 : term559 _27494 y' m => @lem1181089 _27494 _27495 h x m x'' y' P t h1 h2 h3). Qed.
Lemma lem1181092 (p : Prop) : (term650 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1181093 {_27494 : Type'} (y' : type1141 _27494) (m : list _27494) : (term674 _27494 y' m) = (term673 _27494 y' m).
Proof. exact (@lem1181092 (term559 _27494 y' m)). Qed.
Lemma lem1181094 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : term673 _27494 y' m.
Proof. exact (EQ_MP (@lem1181093 _27494 y' m) (@lem1181090 _27494 _27495 h x m x'' y' P t h1 h2 h3)). Qed.
Lemma lem1181100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1181101 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : (term612 _27494 _27495 y' P t _21077) = (term675 _27494 _27495 P t y' _21077).
Proof. exact (@lem1181100 (@ALLPAIRS _27494 _27495 P t _21077) (term559 _27494 y' _21077)). Qed.
Lemma lem1181107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181108 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : (term676 _27494 _27495 y' P t _21077) = (term677 _27494 _27495 P t y' _21077).
Proof. exact (MK_COMB (@lem1181107) (@lem1181101 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181114 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : (term675 _27494 _27495 P t y' _21077) = (term675 _27494 _27495 P t y' _21077).
Proof. exact (eq_refl (term675 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181115 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : ((term612 _27494 _27495 y' P t _21077) = (term675 _27494 _27495 P t y' _21077)) = ((term675 _27494 _27495 P t y' _21077) = (term675 _27494 _27495 P t y' _21077)).
Proof. exact (MK_COMB (@lem1181108 _27494 _27495 P t y' _21077) (@lem1181114 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1181118 (x : Prop) : (x = x) = True.
Proof. exact (@lem1181117 Prop x). Qed.
Lemma lem1181119 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : ((term675 _27494 _27495 P t y' _21077) = (term675 _27494 _27495 P t y' _21077)) = True.
Proof. exact (@lem1181118 (term675 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181120 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : ((term612 _27494 _27495 y' P t _21077) = (term675 _27494 _27495 P t y' _21077)) = True.
Proof. exact (TRANS (@lem1181115 _27494 _27495 P t y' _21077) (@lem1181119 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181121 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : True = ((term612 _27494 _27495 y' P t _21077) = (term675 _27494 _27495 P t y' _21077)).
Proof. exact (SYM (@lem1181120 _27494 _27495 P t y' _21077)). Qed.
Lemma lem1181122 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (y' : type1141 _27494) (_21077 : list _27494) : (term612 _27494 _27495 y' P t _21077) = (term675 _27494 _27495 P t y' _21077).
Proof. exact (EQ_MP (@lem1181121 _27494 _27495 P t y' _21077) (@lem0)). Qed.
Lemma lem1181123 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term675 _27494 _27495 P t y' _21077.
Proof. exact (EQ_MP (@lem1181122 _27494 _27495 P t y' _21077) (@lem1180282 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1181125 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1181128 {_27494 _27495 : Type'} (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21077 : list _27494) : (term675 _27494 _27495 P t y' _21077) = (term678 _27494 _27495 y' P t _21077).
Proof. exact (@lem1181125 (term559 _27494 y' _21077) (@ALLPAIRS _27494 _27495 P t _21077)). Qed.
Lemma lem1181131 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term678 _27494 _27495 y' P t _21077.
Proof. exact (EQ_MP (@lem1181128 _27494 _27495 y' P t _21077) (@lem1181123 _27494 _27495 _21077 x'' y' P t h1)). Qed.
Lemma lem1181132 {_27494 _27495 : Type'} (_21077 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term678 _27494 _27495 y' P t _21077.
Proof. exact (@lem1181131 _27494 _27495 _21077 x'' y' P t h1). Qed.
Lemma lem1181133 {_27494 _27495 : Type'} (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term678 _27494 _27495 y' P t m.
Proof. exact (@lem1181132 _27494 _27495 m x'' y' P t h1). Qed.
Lemma lem1181136 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : @ALLPAIRS _27494 _27495 P t m.
Proof. exact (@lem1181133 _27494 _27495 m x'' y' P t h3 (@lem1181094 _27494 _27495 h x m x'' y' P t h1 h2 h3)). Qed.
Lemma lem1181137 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term514 _27494 _27495 h x P t m) (h2 : term313 _27494 _27495 x'' y' P t) : term679 _27494 _27495 P t m.
Proof. exact (fun h0 : term159 _27494 _27495 P t m => @lem1181136 _27494 _27495 h x m x'' y' P t h0 h1 h2). Qed.
Lemma lem1181139 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181140 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term679 _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (@lem1181139 (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1181141 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term514 _27494 _27495 h x P t m) (h2 : term313 _27494 _27495 x'' y' P t) : @ALLPAIRS _27494 _27495 P t m.
Proof. exact (EQ_MP (@lem1181140 _27494 _27495 P t m) (@lem1181137 _27494 _27495 h x m x'' y' P t h1 h2)). Qed.
Lemma lem1181144 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1181146 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term159 _27494 _27495 P t m) = (term680 _27494 _27495 P t m).
Proof. exact (@lem1181144 (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1181149 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term159 _27494 _27495 P t m) : term680 _27494 _27495 P t m.
Proof. exact (EQ_MP (@lem1181146 _27494 _27495 P t m) (@lem1180240 _27494 _27495 P t m h1)). Qed.
Lemma lem1181152 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (@lem1181149 _27494 _27495 P t m h1 (@lem1181141 _27494 _27495 h x m x'' y' P t h2 h3)). Qed.
Lemma lem1181153 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : term648.
Proof. exact (fun h0 : ~ False => @lem1181152 _27494 _27495 h x m x'' y' P t h1 h2 h3). Qed.
Lemma lem1181155 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181156 : term648 = False.
Proof. exact (@lem1181155 False). Qed.
Lemma lem1181157 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (EQ_MP (@lem1181156) (@lem1181153 _27494 _27495 h x m x'' y' P t h1 h2 h3)). Qed.
Lemma lem1181159 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @List.In _27494 y m.
Proof. exact (proj2 (@lem1179448 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181160 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term623 _27494 y m.
Proof. exact (fun h0 : term321 _27494 y m => @lem1181159 _27494 _27495 x' y h P t m h1). Qed.
Lemma lem1181162 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181163 {_27494 : Type'} (y : _27494) (m : list _27494) : (term623 _27494 y m) = (@List.In _27494 y m).
Proof. exact (@lem1181162 (@List.In _27494 y m)). Qed.
Lemma lem1181164 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @List.In _27494 y m.
Proof. exact (EQ_MP (@lem1181163 _27494 y m) (@lem1181160 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181170 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1181171 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : (term493 _27494 _27495 m P h _21084) = (term624 _27494 _27495 P h _21084 m).
Proof. exact (@lem1181170 (term491 _27494 _27495 P h _21084) (term321 _27494 _21084 m)). Qed.
Lemma lem1181177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181178 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : (term681 _27494 _27495 m P h _21084) = (term682 _27494 _27495 P h _21084 m).
Proof. exact (MK_COMB (@lem1181177) (@lem1181171 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181184 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : (term624 _27494 _27495 P h _21084 m) = (term624 _27494 _27495 P h _21084 m).
Proof. exact (eq_refl (term624 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181185 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : ((term493 _27494 _27495 m P h _21084) = (term624 _27494 _27495 P h _21084 m)) = ((term624 _27494 _27495 P h _21084 m) = (term624 _27494 _27495 P h _21084 m)).
Proof. exact (MK_COMB (@lem1181178 _27494 _27495 P h _21084 m) (@lem1181184 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181187 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1181188 (x : Prop) : (x = x) = True.
Proof. exact (@lem1181187 Prop x). Qed.
Lemma lem1181189 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : ((term624 _27494 _27495 P h _21084 m) = (term624 _27494 _27495 P h _21084 m)) = True.
Proof. exact (@lem1181188 (term624 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181190 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : ((term493 _27494 _27495 m P h _21084) = (term624 _27494 _27495 P h _21084 m)) = True.
Proof. exact (TRANS (@lem1181185 _27494 _27495 P h _21084 m) (@lem1181189 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181191 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : True = ((term493 _27494 _27495 m P h _21084) = (term624 _27494 _27495 P h _21084 m)).
Proof. exact (SYM (@lem1181190 _27494 _27495 P h _21084 m)). Qed.
Lemma lem1181192 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) (m : list _27494) : (term493 _27494 _27495 m P h _21084) = (term624 _27494 _27495 P h _21084 m).
Proof. exact (EQ_MP (@lem1181191 _27494 _27495 P h _21084 m) (@lem0)). Qed.
Lemma lem1181193 {_27494 _27495 : Type'} (_21084 : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term624 _27494 _27495 P h _21084 m.
Proof. exact (EQ_MP (@lem1181192 _27494 _27495 P h _21084 m) (@lem1180424 _27494 _27495 _21084 x' y h P t m h1)). Qed.
Lemma lem1181195 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1181196 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) : (term624 _27494 _27495 P h _21084 m) = (term683 _27494 _27495 m P h _21084).
Proof. exact (@lem1181195 (term321 _27494 _21084 m) (term491 _27494 _27495 P h _21084)). Qed.
Lemma lem1181198 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1181199 {_27494 : Type'} (_21084 : _27494) (m : list _27494) : (term639 _27494 _21084 m) = (@List.In _27494 _21084 m).
Proof. exact (@lem1181198 (@List.In _27494 _21084 m)). Qed.
Lemma lem1181200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1181201 {_27494 : Type'} (_21084 : _27494) (m : list _27494) : (term684 _27494 _21084 m) = (term685 _27494 _21084 m).
Proof. exact (MK_COMB (@lem1181200) (@lem1181199 _27494 _21084 m)). Qed.
Lemma lem1181202 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) : (term491 _27494 _27495 P h _21084) = (term491 _27494 _27495 P h _21084).
Proof. exact (eq_refl (term491 _27494 _27495 P h _21084)). Qed.
Lemma lem1181203 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) : (term683 _27494 _27495 m P h _21084) = (term686 _27494 _27495 m P h _21084).
Proof. exact (MK_COMB (@lem1181201 _27494 _21084 m) (@lem1181202 _27494 _27495 P h _21084)). Qed.
Lemma lem1181204 {_27494 _27495 : Type'} (m : list _27494) (P : type1470 _27494 _27495) (h : _27495) (_21084 : _27494) : (term624 _27494 _27495 P h _21084 m) = (term686 _27494 _27495 m P h _21084).
Proof. exact (TRANS (@lem1181196 _27494 _27495 m P h _21084) (@lem1181203 _27494 _27495 m P h _21084)). Qed.
Lemma lem1181207 {_27494 _27495 : Type'} (_21084 : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term686 _27494 _27495 m P h _21084.
Proof. exact (EQ_MP (@lem1181204 _27494 _27495 m P h _21084) (@lem1181193 _27494 _27495 _21084 x' y h P t m h1)). Qed.
Lemma lem1181208 {_27494 _27495 : Type'} (_21084 : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term686 _27494 _27495 m P h _21084.
Proof. exact (@lem1181207 _27494 _27495 _21084 x' y h P t m h1). Qed.
Lemma lem1181209 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term686 _27494 _27495 m P h y.
Proof. exact (@lem1181208 _27494 _27495 y x' y h P t m h1). Qed.
Lemma lem1181212 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term491 _27494 _27495 P h y.
Proof. exact (@lem1181209 _27494 _27495 x' y h P t m h1 (@lem1181164 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181213 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term646 _27494 _27495 P h y.
Proof. exact (fun h0 : term499 _27494 _27495 P h y => @lem1181212 _27494 _27495 x' y h P t m h1). Qed.
Lemma lem1181215 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181216 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : (term646 _27494 _27495 P h y) = (term491 _27494 _27495 P h y).
Proof. exact (@lem1181215 (term491 _27494 _27495 P h y)). Qed.
Lemma lem1181217 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term491 _27494 _27495 P h y.
Proof. exact (EQ_MP (@lem1181216 _27494 _27495 P h y) (@lem1181213 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1181222 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (y : _27494) : (term499 _27494 _27495 P h y) = (term647 _27494 _27495 P h y).
Proof. exact (@lem1181220 (term491 _27494 _27495 P h y)). Qed.
Lemma lem1181225 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : term647 _27494 _27495 P h y.
Proof. exact (EQ_MP (@lem1181222 _27494 _27495 P h y) (@lem1180451 _27494 _27495 y P t m x' h h1 h2)). Qed.
Lemma lem1181228 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : False.
Proof. exact (@lem1181225 _27494 _27495 y P t m x' h h1 h2 (@lem1181217 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181229 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : term648.
Proof. exact (fun h0 : ~ False => @lem1181228 _27494 _27495 y P t m x' h h1 h2). Qed.
Lemma lem1181231 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181232 : term648 = False.
Proof. exact (@lem1181231 False). Qed.
Lemma lem1181235 {_27495 : Type'} (x' : _27495) (t : list _27495) (h1 : @List.In _27495 x' t) : @List.In _27495 x' t.
Proof. exact (h1). Qed.
Lemma lem1181236 {_27495 : Type'} (x' : _27495) (t : list _27495) (h1 : @List.In _27495 x' t) : term623 _27495 x' t.
Proof. exact (fun h0 : term321 _27495 x' t => @lem1181235 _27495 x' t h1). Qed.
Lemma lem1181238 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181239 {_27495 : Type'} (x' : _27495) (t : list _27495) : (term623 _27495 x' t) = (@List.In _27495 x' t).
Proof. exact (@lem1181238 (@List.In _27495 x' t)). Qed.
Lemma lem1181240 {_27495 : Type'} (x' : _27495) (t : list _27495) (h1 : @List.In _27495 x' t) : @List.In _27495 x' t.
Proof. exact (EQ_MP (@lem1181239 _27495 x' t) (@lem1181236 _27495 x' t h1)). Qed.
Lemma lem1181242 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @List.In _27494 y m.
Proof. exact (proj2 (@lem1179448 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181243 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term623 _27494 y m.
Proof. exact (fun h0 : term321 _27494 y m => @lem1181242 _27494 _27495 x' y h P t m h1). Qed.
Lemma lem1181245 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181246 {_27494 : Type'} (y : _27494) (m : list _27494) : (term623 _27494 y m) = (@List.In _27494 y m).
Proof. exact (@lem1181245 (@List.In _27494 y m)). Qed.
Lemma lem1181247 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @List.In _27494 y m.
Proof. exact (EQ_MP (@lem1181246 _27494 y m) (@lem1181243 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181249 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @ALLPAIRS _27494 _27495 P t m.
Proof. exact (proj2 (@lem1179443 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181250 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term679 _27494 _27495 P t m.
Proof. exact (fun h0 : term159 _27494 _27495 P t m => @lem1181249 _27494 _27495 x' y h P t m h1). Qed.
Lemma lem1181252 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181253 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) : (term679 _27494 _27495 P t m) = (@ALLPAIRS _27494 _27495 P t m).
Proof. exact (@lem1181252 (@ALLPAIRS _27494 _27495 P t m)). Qed.
Lemma lem1181254 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : @ALLPAIRS _27494 _27495 P t m.
Proof. exact (EQ_MP (@lem1181253 _27494 _27495 P t m) (@lem1181250 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181260 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181261 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term614 _27494 _27495 _21086 _21087 P t _21085) = (term687 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (@lem1181260 (term321 _27494 _21087 _21085) (term321 _27495 _21086 t) (term615 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1181275 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181276 {_27494 _27495 : Type'} (_21087 : _27494) (_21086 : _27495) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term688 _27494 _27495 _21086 _21087 P t _21085) = (term689 _27494 _27495 _21087 _21086 P t _21085).
Proof. exact (@lem1181275 (term491 _27494 _27495 P _21086 _21087) (term321 _27495 _21086 t) (term159 _27494 _27495 P t _21085)). Qed.
Lemma lem1181290 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1181291 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term690 _27494 _27495 _21086 P t _21085) = (term691 _27494 _27495 P _21085 _21086 t).
Proof. exact (@lem1181290 (term159 _27494 _27495 P t _21085) (term321 _27495 _21086 t)). Qed.
Lemma lem1181297 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term692 _27494 _27495 P _21086 _21087) = (term692 _27494 _27495 P _21086 _21087).
Proof. exact (eq_refl (term692 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181298 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term689 _27494 _27495 _21087 _21086 P t _21085) = (term693 _27494 _27495 _21087 P _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181297 _27494 _27495 P _21086 _21087) (@lem1181291 _27494 _27495 P _21085 _21086 t)). Qed.
Lemma lem1181309 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term688 _27494 _27495 _21086 _21087 P t _21085) = (term693 _27494 _27495 _21087 P _21085 _21086 t).
Proof. exact (TRANS (@lem1181276 _27494 _27495 _21087 _21086 P t _21085) (@lem1181298 _27494 _27495 _21087 P _21085 _21086 t)). Qed.
Lemma lem1181310 {_27494 : Type'} (_21087 : _27494) (_21085 : list _27494) : (term492 _27494 _21087 _21085) = (term492 _27494 _21087 _21085).
Proof. exact (eq_refl (term492 _27494 _21087 _21085)). Qed.
Lemma lem1181311 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term687 _27494 _27495 _21086 _21087 P t _21085) = (term694 _27494 _27495 _21087 P _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181310 _27494 _21087 _21085) (@lem1181309 _27494 _27495 _21087 P _21085 _21086 t)). Qed.
Lemma lem1181315 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181316 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term694 _27494 _27495 _21087 P _21085 _21086 t) = (term695 _27494 _27495 _21087 P _21085 _21086 t).
Proof. exact (@lem1181315 (term491 _27494 _27495 P _21086 _21087) (term321 _27494 _21087 _21085) (term691 _27494 _27495 P _21085 _21086 t)). Qed.
Lemma lem1181330 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181331 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term696 _27494 _27495 _21087 P _21085 _21086 t) = (term697 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (@lem1181330 (term159 _27494 _27495 P t _21085) (term321 _27494 _21087 _21085) (term321 _27495 _21086 t)). Qed.
Lemma lem1181347 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term692 _27494 _27495 P _21086 _21087) = (term692 _27494 _27495 P _21086 _21087).
Proof. exact (eq_refl (term692 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181348 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term695 _27494 _27495 _21087 P _21085 _21086 t) = (term698 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181347 _27494 _27495 P _21086 _21087) (@lem1181331 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181359 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term694 _27494 _27495 _21087 P _21085 _21086 t) = (term698 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (TRANS (@lem1181316 _27494 _27495 _21087 P _21085 _21086 t) (@lem1181348 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181360 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term687 _27494 _27495 _21086 _21087 P t _21085) = (term698 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (TRANS (@lem1181311 _27494 _27495 _21087 P _21085 _21086 t) (@lem1181359 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181361 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term614 _27494 _27495 _21086 _21087 P t _21085) = (term698 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (TRANS (@lem1181261 _27494 _27495 _21086 _21087 P t _21085) (@lem1181360 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181363 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term699 _27494 _27495 _21086 _21087 P t _21085) = (term700 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181362) (@lem1181361 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181377 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181378 {_27494 _27495 : Type'} (_21087 : _27494) (_21086 : _27495) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term701 _27494 _27495 _21086 _21087 P t _21085) = (term702 _27494 _27495 _21087 _21086 P t _21085).
Proof. exact (@lem1181377 (term321 _27494 _21087 _21085) (term321 _27495 _21086 t) (term159 _27494 _27495 P t _21085)). Qed.
Lemma lem1181392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1181393 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term690 _27494 _27495 _21086 P t _21085) = (term691 _27494 _27495 P _21085 _21086 t).
Proof. exact (@lem1181392 (term159 _27494 _27495 P t _21085) (term321 _27495 _21086 t)). Qed.
Lemma lem1181399 {_27494 : Type'} (_21087 : _27494) (_21085 : list _27494) : (term492 _27494 _21087 _21085) = (term492 _27494 _21087 _21085).
Proof. exact (eq_refl (term492 _27494 _21087 _21085)). Qed.
Lemma lem1181400 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term702 _27494 _27495 _21087 _21086 P t _21085) = (term696 _27494 _27495 _21087 P _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181399 _27494 _21087 _21085) (@lem1181393 _27494 _27495 P _21085 _21086 t)). Qed.
Lemma lem1181404 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1181405 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term696 _27494 _27495 _21087 P _21085 _21086 t) = (term697 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (@lem1181404 (term159 _27494 _27495 P t _21085) (term321 _27494 _21087 _21085) (term321 _27495 _21086 t)). Qed.
Lemma lem1181421 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term702 _27494 _27495 _21087 _21086 P t _21085) = (term697 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (TRANS (@lem1181400 _27494 _27495 _21087 P _21085 _21086 t) (@lem1181405 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181422 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term701 _27494 _27495 _21086 _21087 P t _21085) = (term697 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (TRANS (@lem1181378 _27494 _27495 _21087 _21086 P t _21085) (@lem1181421 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181423 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term692 _27494 _27495 P _21086 _21087) = (term692 _27494 _27495 P _21086 _21087).
Proof. exact (eq_refl (term692 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181424 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : (term703 _27494 _27495 _21086 _21087 P t _21085) = (term698 _27494 _27495 P _21087 _21085 _21086 t).
Proof. exact (MK_COMB (@lem1181423 _27494 _27495 P _21086 _21087) (@lem1181422 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181435 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : ((term614 _27494 _27495 _21086 _21087 P t _21085) = (term703 _27494 _27495 _21086 _21087 P t _21085)) = ((term698 _27494 _27495 P _21087 _21085 _21086 t) = (term698 _27494 _27495 P _21087 _21085 _21086 t)).
Proof. exact (MK_COMB (@lem1181363 _27494 _27495 P _21087 _21085 _21086 t) (@lem1181424 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1181438 (x : Prop) : (x = x) = True.
Proof. exact (@lem1181437 Prop x). Qed.
Lemma lem1181439 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21087 : _27494) (_21085 : list _27494) (_21086 : _27495) (t : list _27495) : ((term698 _27494 _27495 P _21087 _21085 _21086 t) = (term698 _27494 _27495 P _21087 _21085 _21086 t)) = True.
Proof. exact (@lem1181438 (term698 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181440 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : ((term614 _27494 _27495 _21086 _21087 P t _21085) = (term703 _27494 _27495 _21086 _21087 P t _21085)) = True.
Proof. exact (TRANS (@lem1181435 _27494 _27495 P _21087 _21085 _21086 t) (@lem1181439 _27494 _27495 P _21087 _21085 _21086 t)). Qed.
Lemma lem1181441 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : True = ((term614 _27494 _27495 _21086 _21087 P t _21085) = (term703 _27494 _27495 _21086 _21087 P t _21085)).
Proof. exact (SYM (@lem1181440 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1181442 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term614 _27494 _27495 _21086 _21087 P t _21085) = (term703 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (EQ_MP (@lem1181441 _27494 _27495 _21086 _21087 P t _21085) (@lem0)). Qed.
Lemma lem1181443 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (_21085 : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term703 _27494 _27495 _21086 _21087 P t _21085.
Proof. exact (EQ_MP (@lem1181442 _27494 _27495 _21086 _21087 P t _21085) (@lem1180350 _27494 _27495 _21086 _21087 _21085 x'' y' P t h1)). Qed.
Lemma lem1181445 (b : Prop) (a : Prop) : (a \/ b) = (term630 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1181446 {_27494 _27495 : Type'} (t : list _27495) (_21085 : list _27494) (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term703 _27494 _27495 _21086 _21087 P t _21085) = (term704 _27494 _27495 t _21085 P _21086 _21087).
Proof. exact (@lem1181445 (term701 _27494 _27495 _21086 _21087 P t _21085) (term491 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181448 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1181449 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term705 _27494 _27495 _21086 _21087 P t _21085) = (term706 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (@lem1181448 (term321 _27495 _21086 t) (term707 _27494 _27495 _21087 P t _21085)). Qed.
Lemma lem1181451 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1181452 {_27495 : Type'} (_21086 : _27495) (t : list _27495) : (term639 _27495 _21086 t) = (@List.In _27495 _21086 t).
Proof. exact (@lem1181451 (@List.In _27495 _21086 t)). Qed.
Lemma lem1181453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1181454 {_27495 : Type'} (_21086 : _27495) (t : list _27495) : (term666 _27495 _21086 t) = (term504 _27495 _21086 t).
Proof. exact (MK_COMB (@lem1181453) (@lem1181452 _27495 _21086 t)). Qed.
Lemma lem1181456 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1181457 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term708 _27494 _27495 _21087 P t _21085) = (term709 _27494 _27495 _21087 P t _21085).
Proof. exact (@lem1181456 (term321 _27494 _21087 _21085) (term159 _27494 _27495 P t _21085)). Qed.
Lemma lem1181459 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1181460 {_27494 : Type'} (_21087 : _27494) (_21085 : list _27494) : (term639 _27494 _21087 _21085) = (@List.In _27494 _21087 _21085).
Proof. exact (@lem1181459 (@List.In _27494 _21087 _21085)). Qed.
Lemma lem1181461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1181462 {_27494 : Type'} (_21087 : _27494) (_21085 : list _27494) : (term666 _27494 _21087 _21085) = (term504 _27494 _21087 _21085).
Proof. exact (MK_COMB (@lem1181461) (@lem1181460 _27494 _21087 _21085)). Qed.
Lemma lem1181464 (a : Prop) : (term105 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1181465 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term710 _27494 _27495 P t _21085) = (@ALLPAIRS _27494 _27495 P t _21085).
Proof. exact (@lem1181464 (@ALLPAIRS _27494 _27495 P t _21085)). Qed.
Lemma lem1181466 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term709 _27494 _27495 _21087 P t _21085) = (term711 _27494 _27495 _21087 P t _21085).
Proof. exact (MK_COMB (@lem1181462 _27494 _21087 _21085) (@lem1181465 _27494 _27495 P t _21085)). Qed.
Lemma lem1181467 {_27494 _27495 : Type'} (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term708 _27494 _27495 _21087 P t _21085) = (term711 _27494 _27495 _21087 P t _21085).
Proof. exact (TRANS (@lem1181457 _27494 _27495 _21087 P t _21085) (@lem1181466 _27494 _27495 _21087 P t _21085)). Qed.
Lemma lem1181468 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term706 _27494 _27495 _21086 _21087 P t _21085) = (term712 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (MK_COMB (@lem1181454 _27495 _21086 t) (@lem1181467 _27494 _27495 _21087 P t _21085)). Qed.
Lemma lem1181469 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term705 _27494 _27495 _21086 _21087 P t _21085) = (term712 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (TRANS (@lem1181449 _27494 _27495 _21086 _21087 P t _21085) (@lem1181468 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1181470 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1181471 {_27494 _27495 : Type'} (_21086 : _27495) (_21087 : _27494) (P : type1470 _27494 _27495) (t : list _27495) (_21085 : list _27494) : (term713 _27494 _27495 _21086 _21087 P t _21085) = (term714 _27494 _27495 _21086 _21087 P t _21085).
Proof. exact (MK_COMB (@lem1181470) (@lem1181469 _27494 _27495 _21086 _21087 P t _21085)). Qed.
Lemma lem1181472 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term491 _27494 _27495 P _21086 _21087) = (term491 _27494 _27495 P _21086 _21087).
Proof. exact (eq_refl (term491 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181473 {_27494 _27495 : Type'} (t : list _27495) (_21085 : list _27494) (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term704 _27494 _27495 t _21085 P _21086 _21087) = (term715 _27494 _27495 t _21085 P _21086 _21087).
Proof. exact (MK_COMB (@lem1181471 _27494 _27495 _21086 _21087 P t _21085) (@lem1181472 _27494 _27495 P _21086 _21087)). Qed.
Lemma lem1181474 {_27494 _27495 : Type'} (t : list _27495) (_21085 : list _27494) (P : type1470 _27494 _27495) (_21086 : _27495) (_21087 : _27494) : (term703 _27494 _27495 _21086 _21087 P t _21085) = (term715 _27494 _27495 t _21085 P _21086 _21087).
Proof. exact (TRANS (@lem1181446 _27494 _27495 t _21085 P _21086 _21087) (@lem1181473 _27494 _27495 t _21085 P _21086 _21087)). Qed.
Lemma lem1181476 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term711 _27494 _27495 y P t m.
Proof. exact (conj (@lem1181247 _27494 _27495 x' y h P t m h1) (@lem1181254 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181477 {_27494 _27495 : Type'} (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : @List.In _27495 x' t) : term712 _27494 _27495 x' y P t m.
Proof. exact (conj (@lem1181240 _27495 x' t h2) (@lem1181476 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181479 {_27494 _27495 : Type'} (_21085 : list _27494) (_21086 : _27495) (_21087 : _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term715 _27494 _27495 t _21085 P _21086 _21087.
Proof. exact (EQ_MP (@lem1181474 _27494 _27495 t _21085 P _21086 _21087) (@lem1181443 _27494 _27495 _21086 _21087 _21085 x'' y' P t h1)). Qed.
Lemma lem1181480 {_27494 _27495 : Type'} (_21085 : list _27494) (_21086 : _27495) (_21087 : _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term715 _27494 _27495 t _21085 P _21086 _21087.
Proof. exact (@lem1181479 _27494 _27495 _21085 _21086 _21087 x'' y' P t h1). Qed.
Lemma lem1181481 {_27494 _27495 : Type'} (m : list _27494) (x' : _27495) (y : _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) : term715 _27494 _27495 t m P x' y.
Proof. exact (@lem1181480 _27494 _27495 m x' y x'' y' P t h1). Qed.
Lemma lem1181484 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : term491 _27494 _27495 P x' y.
Proof. exact (@lem1181481 _27494 _27495 m x' y x'' y' P t h1 (@lem1181477 _27494 _27495 y h P m x' t h2 h3)). Qed.
Lemma lem1181485 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : term646 _27494 _27495 P x' y.
Proof. exact (fun h0 : term499 _27494 _27495 P x' y => @lem1181484 _27494 _27495 x'' y' y h P m x' t h1 h2 h3). Qed.
Lemma lem1181487 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181488 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term646 _27494 _27495 P x' y) = (term491 _27494 _27495 P x' y).
Proof. exact (@lem1181487 (term491 _27494 _27495 P x' y)). Qed.
Lemma lem1181489 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : term491 _27494 _27495 P x' y.
Proof. exact (EQ_MP (@lem1181488 _27494 _27495 P x' y) (@lem1181485 _27494 _27495 x'' y' y h P m x' t h1 h2 h3)). Qed.
Lemma lem1181492 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1181494 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (x' : _27495) (y : _27494) : (term499 _27494 _27495 P x' y) = (term647 _27494 _27495 P x' y).
Proof. exact (@lem1181492 (term491 _27494 _27495 P x' y)). Qed.
Lemma lem1181497 {_27494 _27495 : Type'} (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term503 _27494 _27495 x' y h P t m) : term647 _27494 _27495 P x' y.
Proof. exact (EQ_MP (@lem1181494 _27494 _27495 P x' y) (@lem1180360 _27494 _27495 x' y h P t m h1)). Qed.
Lemma lem1181500 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : False.
Proof. exact (@lem1181497 _27494 _27495 x' y h P t m h2 (@lem1181489 _27494 _27495 x'' y' y h P m x' t h1 h2 h3)). Qed.
Lemma lem1181501 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : term648.
Proof. exact (fun h0 : ~ False => @lem1181500 _27494 _27495 x'' y' y h P m x' t h1 h2 h3). Qed.
Lemma lem1181503 (p : Prop) : (term622 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1181504 : term648 = False.
Proof. exact (@lem1181503 False). Qed.
Lemma lem1181505 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : False.
Proof. exact (EQ_MP (@lem1181504) (@lem1181501 _27494 _27495 x'' y' y h P m x' t h1 h2 h3)). Qed.
Lemma lem1181506 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : False.
Proof. exact (EQ_MP (@lem1181232) (@lem1181229 _27494 _27495 y P t m x' h h1 h2)). Qed.
Lemma lem1181507 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : (@List.In _27495 x' t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27495 x' t => @lem1181505 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (fun h4 : False => @lem1180364 _27495 x' t h3)). Qed.
Lemma lem1181508 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : False.
Proof. exact (EQ_MP (@lem1181507 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (@lem1180364 _27495 x' t h3)). Qed.
Lemma lem1181509 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : (x' = h) = False.
Proof. exact (prop_ext (fun h3 : x' = h => @lem1181506 _27494 _27495 y P t m x' h h1 h2) (fun h3 : False => @lem1180314 _27495 x' h h2)). Qed.
Lemma lem1181510 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : False.
Proof. exact (EQ_MP (@lem1181509 _27494 _27495 y P t m x' h h1 h2) (@lem1180314 _27495 x' h h2)). Qed.
Lemma lem1181511 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : (term159 _27494 _27495 P t m) = False.
Proof. exact (prop_ext (fun h4 : term159 _27494 _27495 P t m => @lem1181157 _27494 _27495 h x m x'' y' P t h1 h2 h3) (fun h4 : False => @lem1180240 _27494 _27495 P t m h1)). Qed.
Lemma lem1181512 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (EQ_MP (@lem1181511 _27494 _27495 h x m x'' y' P t h1 h2 h3) (@lem1180240 _27494 _27495 P t m h1)). Qed.
Lemma lem1181513 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : (@List.In _27495 x' t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27495 x' t => @lem1181508 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (fun h4 : False => @lem1180070 _27495 x' t h3)). Qed.
Lemma lem1181514 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : False.
Proof. exact (EQ_MP (@lem1181513 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (@lem1180070 _27495 x' t h3)). Qed.
Lemma lem1181515 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : (x' = h) = False.
Proof. exact (prop_ext (fun h3 : x' = h => @lem1181510 _27494 _27495 y P t m x' h h1 h2) (fun h3 : False => @lem1179923 _27495 x' h h2)). Qed.
Lemma lem1181516 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : False.
Proof. exact (EQ_MP (@lem1181515 _27494 _27495 y P t m x' h h1 h2) (@lem1179923 _27495 x' h h2)). Qed.
Lemma lem1181517 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : (term159 _27494 _27495 P t m) = False.
Proof. exact (prop_ext (fun h4 : term159 _27494 _27495 P t m => @lem1181512 _27494 _27495 h x m x'' y' P t h1 h2 h3) (fun h4 : False => @lem1179776 _27494 _27495 P t m h1)). Qed.
Lemma lem1181518 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (EQ_MP (@lem1181517 _27494 _27495 h x m x'' y' P t h1 h2 h3) (@lem1179776 _27494 _27495 P t m h1)). Qed.
Lemma lem1181519 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : (@List.In _27495 x' t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27495 x' t => @lem1181514 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (fun h4 : False => @lem1180070 _27495 x' t h3)). Qed.
Lemma lem1181520 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (m : list _27494) (x' : _27495) (t : list _27495) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) (h3 : @List.In _27495 x' t) : False.
Proof. exact (EQ_MP (@lem1181519 _27494 _27495 x'' y' y h P m x' t h1 h2 h3) (@lem1180070 _27495 x' t h3)). Qed.
Lemma lem1181521 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : (x' = h) = False.
Proof. exact (prop_ext (fun h3 : x' = h => @lem1181516 _27494 _27495 y P t m x' h h1 h2) (fun h3 : False => @lem1179923 _27495 x' h h2)). Qed.
Lemma lem1181522 {_27494 _27495 : Type'} (y : _27494) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (x' : _27495) (h : _27495) (h1 : term503 _27494 _27495 x' y h P t m) (h2 : x' = h) : False.
Proof. exact (EQ_MP (@lem1181521 _27494 _27495 y P t m x' h h1 h2) (@lem1179923 _27495 x' h h2)). Qed.
Lemma lem1181523 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : (term159 _27494 _27495 P t m) = False.
Proof. exact (prop_ext (fun h4 : term159 _27494 _27495 P t m => @lem1181518 _27494 _27495 h x m x'' y' P t h1 h2 h3) (fun h4 : False => @lem1179776 _27494 _27495 P t m h1)). Qed.
Lemma lem1181524 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term159 _27494 _27495 P t m) (h2 : term514 _27494 _27495 h x P t m) (h3 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (EQ_MP (@lem1181523 _27494 _27495 h x m x'' y' P t h1 h2 h3) (@lem1179776 _27494 _27495 P t m h1)). Qed.
Lemma lem1181525 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term503 _27494 _27495 x' y h P t m) : False.
Proof. exact (or_elim (@lem1179450 _27494 _27495 x' y h P t m h2) (fun h0 : x' = h => @lem1181522 _27494 _27495 y P t m x' h h2 h0) (fun h0 : @List.In _27495 x' t => @lem1181520 _27494 _27495 x'' y' y h P m x' t h1 h2 h0)). Qed.
Lemma lem1181526 {_27494 _27495 : Type'} (h : _27495) (x : _27494) (m : list _27494) (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term514 _27494 _27495 h x P t m) (h2 : term313 _27494 _27495 x'' y' P t) : False.
Proof. exact (or_elim (@lem1179437 _27494 _27495 h x P t m h1) (fun h0 : term505 _27494 _27495 m P h x => @lem1180778 _27494 _27495 t m P h x h1 h0) (fun h0 : term159 _27494 _27495 P t m => @lem1181524 _27494 _27495 h x m x'' y' P t h0 h1 h2)). Qed.
Lemma lem1181527 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (y' : type1141 _27494) (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term313 _27494 _27495 x'' y' P t) (h2 : term483 _27494 _27495 x x' y h P t m) : False.
Proof. exact (or_elim (@lem1179314 _27494 _27495 x x' y h P t m h2) (fun h0 : term514 _27494 _27495 h x P t m => @lem1181526 _27494 _27495 h x m x'' y' P t h0 h1) (fun h0 : term503 _27494 _27495 x' y h P t m => @lem1181525 _27494 _27495 x'' y' x' y h P t m h1 h0)). Qed.
Lemma lem1181528 {_27494 _27495 : Type'} (x'' : type1142 _27494 _27495) (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term316 _27494 _27495 x'' P t) (h2 : term483 _27494 _27495 x x' y h P t m) : False.
Proof. exact (ex_elim (@lem1179128 _27494 _27495 x'' P t h1) (fun y' : type1141 _27494 => fun h0 : term315 _27494 _27495 x'' P t y' => @lem1181527 _27494 _27495 x'' y' x x' y h P t m h0 h2)). Qed.
Lemma lem1181529 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (y : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term483 _27494 _27495 x x' y h P t m) : False.
Proof. exact (ex_elim (@lem1178635 _27494 _27495 P t h1) (fun x'' : type1142 _27494 _27495 => fun h0 : term317 _27494 _27495 P t x'' => @lem1181528 _27494 _27495 x'' x x' y h P t m h0 h2)). Qed.
Lemma lem1181530 {_27494 _27495 : Type'} (x : _27494) (x' : _27495) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term486 _27494 _27495 x x' h P t m) : False.
Proof. exact (ex_elim (@lem1179126 _27494 _27495 x x' h P t m h2) (fun y : _27494 => fun h0 : term485 _27494 _27495 x x' h P t m y => @lem1181529 _27494 _27495 x x' y h P t m h1 h0)). Qed.
Lemma lem1181531 {_27494 _27495 : Type'} (x : _27494) (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term488 _27494 _27495 x h P t m) : False.
Proof. exact (ex_elim (@lem1179125 _27494 _27495 x h P t m h2) (fun x' : _27495 => fun h0 : term487 _27494 _27495 x h P t m x' => @lem1181530 _27494 _27495 x x' h P t m h1 h0)). Qed.
Lemma lem1181532 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term129 _27494 _27495 h P t m) : False.
Proof. exact (ex_elim (@lem1179124 _27494 _27495 h P t m h2) (fun x : _27494 => fun h0 : term489 _27494 _27495 h P t m x => @lem1181531 _27494 _27495 x h P t m h1 h0)). Qed.
Lemma lem1181533 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term129 _27494 _27495 h P t m) : (term129 _27494 _27495 h P t m) = False.
Proof. exact (prop_ext (fun h3 : term129 _27494 _27495 h P t m => @lem1181532 _27494 _27495 h P t m h1 h2) (fun h3 : False => @lem1178172 _27494 _27495 h P t m h2)). Qed.
Lemma lem1181534 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (m : list _27494) (h1 : term26 _27494 _27495 P t) (h2 : term129 _27494 _27495 h P t m) : False.
Proof. exact (EQ_MP (@lem1181533 _27494 _27495 h P t m h1 h2) (@lem1178172 _27494 _27495 h P t m h2)). Qed.
Lemma lem1181535 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term128 _27494 _27495 h P t m.
Proof. exact (fun h0 : term129 _27494 _27495 h P t m => @lem1181534 _27494 _27495 h P t m h1 h0). Qed.
Lemma lem1181536 {_27494 _27495 : Type'} (h : _27495) (m : list _27494) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : (term84 _27494 _27495 h t m P) = (term93 _27494 _27495 h P t m).
Proof. exact (EQ_MP (@lem1178171 _27494 _27495 h P t m) (@lem1181535 _27494 _27495 h m P t h1)). Qed.
Lemma lem1181541 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term96 _27494 _27495 h P t.
Proof. exact (fun m : list _27494 => @lem1181536 _27494 _27495 h m P t h1). Qed.
Lemma lem1181542 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term106 _27494 _27495 h P t.
Proof. exact (fun h0 : term26 _27494 _27495 P t => @lem1181541 _27494 _27495 h P t h0). Qed.
Lemma lem1181547 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : term110 _27494 _27495 P t.
Proof. exact (fun h : _27495 => @lem1181542 _27494 _27495 h P t). Qed.
Lemma lem1181552 {_27494 _27495 : Type'} (t : list _27495) : term114 _27494 _27495 t.
Proof. exact (fun P : type1470 _27494 _27495 => @lem1181547 _27494 _27495 P t). Qed.
Lemma lem1181557 {_27494 _27495 : Type'} : term118 _27494 _27495.
Proof. exact (fun t : list _27495 => @lem1181552 _27494 _27495 t). Qed.
Lemma lem1181558 {_27494 _27495 : Type'} : term117 _27494 _27495.
Proof. exact (EQ_MP (@lem1178166 _27494 _27495) (@lem1181557 _27494 _27495)). Qed.
Lemma lem1181559 {_27494 _27495 : Type'} (t : list _27495) : term716 _27494 _27495 t.
Proof. exact (@lem1181558 _27494 _27495 t). Qed.
Lemma lem1181560 {_27494 _27495 : Type'} (t : list _27495) : (term716 _27494 _27495 t) = (term113 _27494 _27495 t).
Proof. exact (eq_refl (term716 _27494 _27495 t)). Qed.
Lemma lem1181561 {_27494 _27495 : Type'} (t : list _27495) : term113 _27494 _27495 t.
Proof. exact (EQ_MP (@lem1181560 _27494 _27495 t) (@lem1181559 _27494 _27495 t)). Qed.
Lemma lem1181562 {_27494 _27495 : Type'} (t : list _27495) (P : type1470 _27494 _27495) : term717 _27494 _27495 t P.
Proof. exact (@lem1181561 _27494 _27495 t P). Qed.
Lemma lem1181563 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : (term717 _27494 _27495 t P) = (term109 _27494 _27495 P t).
Proof. exact (eq_refl (term717 _27494 _27495 t P)). Qed.
Lemma lem1181564 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) : term109 _27494 _27495 P t.
Proof. exact (EQ_MP (@lem1181563 _27494 _27495 P t) (@lem1181562 _27494 _27495 t P)). Qed.
Lemma lem1181565 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (t : list _27495) (h : _27495) : term718 _27494 _27495 P t h.
Proof. exact (@lem1181564 _27494 _27495 P t h). Qed.
Lemma lem1181566 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : (term718 _27494 _27495 P t h) = (term100 _27494 _27495 h P t).
Proof. exact (eq_refl (term718 _27494 _27495 P t h)). Qed.
Lemma lem1181567 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term100 _27494 _27495 h P t.
Proof. exact (EQ_MP (@lem1181566 _27494 _27495 h P t) (@lem1181565 _27494 _27495 P t h)). Qed.
Lemma lem1181569 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) : term100 _27494 _27495 h P t.
Proof. exact (@lem1177923 _27494 _27495 h P t (@lem1181567 _27494 _27495 h P t)). Qed.
Lemma lem1181570 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term98 _27494 _27495 h P t.
Proof. exact (@lem1181569 _27494 _27495 h P t (@lem1177741 _27494 _27495 P t h1)). Qed.
Lemma lem1181571 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) (h2 : term99 _27494 _27495 h P t) : False.
Proof. exact (@lem1181570 _27494 _27495 h P t h1 (@lem1177907 _27494 _27495 h P t h2)). Qed.
Lemma lem1181572 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) (h2 : term99 _27494 _27495 h P t) : (term99 _27494 _27495 h P t) = False.
Proof. exact (prop_ext (fun h3 : term99 _27494 _27495 h P t => @lem1181571 _27494 _27495 h P t h1 h2) (fun h3 : False => @lem1177907 _27494 _27495 h P t h2)). Qed.
Lemma lem1181573 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) (h2 : term99 _27494 _27495 h P t) : False.
Proof. exact (EQ_MP (@lem1181572 _27494 _27495 h P t h1 h2) (@lem1177907 _27494 _27495 h P t h2)). Qed.
Lemma lem1181574 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term98 _27494 _27495 h P t.
Proof. exact (fun h0 : term99 _27494 _27495 h P t => @lem1181573 _27494 _27495 h P t h1 h0). Qed.
Lemma lem1181575 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term96 _27494 _27495 h P t.
Proof. exact (EQ_MP (@lem1177906 _27494 _27495 h P t) (@lem1181574 _27494 _27495 h P t h1)). Qed.
Lemma lem1181576 {_27494 _27495 : Type'} (h : _27495) (P : type1470 _27494 _27495) (t : list _27495) (h1 : term26 _27494 _27495 P t) : term30 _27494 _27495 P h t.
Proof. exact (EQ_MP (@lem1177902 _27494 _27495 P h t) (@lem1181575 _27494 _27495 h P t h1)). Qed.
Lemma lem1181577 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) (t : list _27495) : term32 _27494 _27495 P h t.
Proof. exact (fun h0 : term26 _27494 _27495 P t => @lem1181576 _27494 _27495 h P t h0). Qed.
Lemma lem1181582 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (h : _27495) : term36 _27494 _27495 P h.
Proof. exact (fun t : list _27495 => @lem1181577 _27494 _27495 P h t). Qed.
Lemma lem1181587 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term40 _27494 _27495 P.
Proof. exact (fun h : _27495 => @lem1181582 _27494 _27495 P h). Qed.
Lemma lem1181588 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term42 _27494 _27495 P.
Proof. exact (conj (@lem1177815 _27494 _27495 P) (@lem1181587 _27494 _27495 P)). Qed.
Lemma lem1181589 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term47 _27494 _27495 P.
Proof. exact (@lem1177740 _27494 _27495 P (@lem1181588 _27494 _27495 P)). Qed.
Lemma lem1181594 {_27494 _27495 : Type'} : term719 _27494 _27495.
Proof. exact (fun P : type1470 _27494 _27495 => @lem1181589 _27494 _27495 P). Qed.

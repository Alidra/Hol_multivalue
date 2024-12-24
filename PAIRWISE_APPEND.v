Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_APPEND_term_abbrevs.
Require Import ALL_APPEND_spec.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import list_INDUCT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1095962_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1110672_spec.
Require Import thm1110673_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
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
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
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
Lemma lem1222740 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1222741 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1222742 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1222741 t1) (@lem1222740 t1)). Qed.
Lemma lem1222743 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1222742 t1 t2). Qed.
Lemma lem1222744 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1222745 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1222744 t1 t2) (@lem1222743 t1 t2)). Qed.
Lemma lem1222746 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1222745 t1 t2 t3). Qed.
Lemma lem1222747 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1222748 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1222747 t1 t2 t3) (@lem1222746 t1 t2 t3)). Qed.
Lemma lem1222749 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1222748 t1 t2 t3)). Qed.
Lemma lem1222752 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem1222753 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem1222752 _26777 P l h1)). Qed.
Lemma lem1222754 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem1222755 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem1222754 _26777 l P h1)). Qed.
Lemma lem1222756 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem1222753 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem1222755 _26777 l P h1)). Qed.
Lemma lem1222757 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1222756 _26777 l P)). Qed.
Lemma lem1222758 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1222759 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem1222758 _26777) (@lem1222757 _26777 P)). Qed.
Lemma lem1222760 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1222759 _26777 P)). Qed.
Lemma lem1222761 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1222762 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem1222761 _26777) (@lem1222760 _26777)). Qed.
Lemma lem1222763 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem1222762 _26777) (@lem1138070 _26777)). Qed.
Lemma lem1222764 {_26777 : Type'} (P : _26777 -> Prop) : term16 _26777 P.
Proof. exact (@lem1222763 _26777 P). Qed.
Lemma lem1222765 {_26777 : Type'} (P : _26777 -> Prop) : (term16 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term16 _26777 P)). Qed.
Lemma lem1222766 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem1222765 _26777 P) (@lem1222764 _26777 P)). Qed.
Lemma lem1222767 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term17 _26777 P l.
Proof. exact (@lem1222766 _26777 P l). Qed.
Lemma lem1222768 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term17 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term17 _26777 P l)). Qed.
Lemma lem1222770 {_27241 : Type'} (P : _27241 -> Prop) : term18 _27241 P.
Proof. exact (@lem1160417 _27241 P). Qed.
Lemma lem1222771 {_27241 : Type'} (P : _27241 -> Prop) : (term18 _27241 P) = (term19 _27241 P).
Proof. exact (eq_refl (term18 _27241 P)). Qed.
Lemma lem1222772 {_27241 : Type'} (P : _27241 -> Prop) : term19 _27241 P.
Proof. exact (EQ_MP (@lem1222771 _27241 P) (@lem1222770 _27241 P)). Qed.
Lemma lem1222773 {_27241 : Type'} (P : _27241 -> Prop) (l1 : list _27241) : term20 _27241 P l1.
Proof. exact (@lem1222772 _27241 P l1). Qed.
Lemma lem1222774 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) : (term20 _27241 P l1) = (term21 _27241 l1 P).
Proof. exact (eq_refl (term20 _27241 P l1)). Qed.
Lemma lem1222775 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) : term21 _27241 l1 P.
Proof. exact (EQ_MP (@lem1222774 _27241 l1 P) (@lem1222773 _27241 P l1)). Qed.
Lemma lem1222776 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : term22 _27241 l1 P l2.
Proof. exact (@lem1222775 _27241 l1 P l2). Qed.
Lemma lem1222777 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term22 _27241 l1 P l2) = ((term23 _27241 P l1 l2) = (term24 _27241 l1 P l2)).
Proof. exact (eq_refl (term22 _27241 l1 P l2)). Qed.
Lemma lem1222783 {A : Type'} : term25 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1222784 {A : Type'} (h : A) : term26 A h.
Proof. exact (@lem1222783 A h). Qed.
Lemma lem1222785 {A : Type'} (h : A) : (term26 A h) = (term27 A h).
Proof. exact (eq_refl (term26 A h)). Qed.
Lemma lem1222786 {A : Type'} (h : A) : term27 A h.
Proof. exact (EQ_MP (@lem1222785 A h) (@lem1222784 A h)). Qed.
Lemma lem1222787 {A : Type'} (h : A) (t : list A) : term28 A h t.
Proof. exact (@lem1222786 A h t). Qed.
Lemma lem1222788 {A : Type'} (h : A) (t : list A) : (term28 A h t) = (term29 A h t).
Proof. exact (eq_refl (term28 A h t)). Qed.
Lemma lem1222789 {A : Type'} (h : A) (t : list A) : term29 A h t.
Proof. exact (EQ_MP (@lem1222788 A h t) (@lem1222787 A h t)). Qed.
Lemma lem1222790 {A : Type'} (h : A) (t : list A) (l : list A) : term30 A h t l.
Proof. exact (@lem1222789 A h t l). Qed.
Lemma lem1222791 {A : Type'} (h : A) (t : list A) (l : list A) : (term30 A h t l) = ((term31 A h t l) = (term32 A h t l)).
Proof. exact (eq_refl (term30 A h t l)). Qed.
Lemma lem1222793 {A : Type'} : term33 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1222794 {A : Type'} (l : list A) : term34 A l.
Proof. exact (@lem1222793 A l). Qed.
Lemma lem1222795 {A : Type'} (l : list A) : (term34 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term34 A l)). Qed.
Lemma lem1222797 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem1222798 {A : Type'} (P : type1143 A) (h1 : term35 A) : term36 A P.
Proof. exact (@lem1222797 A h1 P). Qed.
Lemma lem1222799 {A : Type'} (P : type1143 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem1222800 {A : Type'} (P : type1143 A) (h1 : term35 A) : term37 A P.
Proof. exact (EQ_MP (@lem1222799 A P) (@lem1222798 A P h1)). Qed.
Lemma lem1222801 {A : Type'} (P : type1143 A) (h1 : term38 A P) : term38 A P.
Proof. exact (h1). Qed.
Lemma lem1222802 {A : Type'} (P : type1143 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem1222800 A P h1 (@lem1222801 A P h2)). Qed.
Lemma lem1222803 {A : Type'} (P : type1143 A) (h1 : term38 A P) : term40 A P.
Proof. exact (fun h0 : term35 A => @lem1222802 A P h0 h1). Qed.
Lemma lem1222804 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem1222805 {A : Type'} (P : type1143 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem1222803 A P h2 (@lem1222804 A h1)). Qed.
Lemma lem1222806 {A : Type'} (P : type1143 A) (h1 : term35 A) : term37 A P.
Proof. exact (fun h0 : term38 A P => @lem1222805 A P h1 h0). Qed.
Lemma lem1222807 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun P : type1143 A => @lem1222806 A P h1). Qed.
Lemma lem1222808 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem1222807 A h0). Qed.
Lemma lem1222809 {A : Type'} : term35 A.
Proof. exact (@lem1222808 A (@lem1071853 A)). Qed.
Lemma lem1222810 {A : Type'} (P : type1143 A) : term36 A P.
Proof. exact (@lem1222809 A P). Qed.
Lemma lem1222811 {A : Type'} (P : type1143 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem1222814 {A : Type'} (P : type1143 A) : term37 A P.
Proof. exact (EQ_MP (@lem1222811 A P) (@lem1222810 A P)). Qed.
Lemma lem1222815 {A : Type'} (P : type1143 A) : term37 A P.
Proof. exact (@lem1222814 A P). Qed.
Lemma lem1222816 {A : Type'} (R : type1402 A) : term42 A R.
Proof. exact (@lem1222815 A (term43 A R)). Qed.
Lemma lem1222817 {A : Type'} (R : type1402 A) : (term44 A R) = (term45 A R).
Proof. exact (eq_refl (term44 A R)). Qed.
Lemma lem1222818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1222819 {A : Type'} (R : type1402 A) : (term46 A R) = (term47 A R).
Proof. exact (MK_COMB (@lem1222818) (@lem1222817 A R)). Qed.
Lemma lem1222820 {A : Type'} (a1 : list A) (R : type1402 A) : (term48 A R a1) = (term49 A a1 R).
Proof. exact (eq_refl (term48 A R a1)). Qed.
Lemma lem1222821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222822 {A : Type'} (a1 : list A) (R : type1402 A) : (term50 A R a1) = (term51 A a1 R).
Proof. exact (MK_COMB (@lem1222821) (@lem1222820 A a1 R)). Qed.
Lemma lem1222823 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term52 A R a0 a1) = (term53 A a0 a1 R).
Proof. exact (eq_refl (term52 A R a0 a1)). Qed.
Lemma lem1222824 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term54 A R a0 a1) = (term55 A a0 a1 R).
Proof. exact (MK_COMB (@lem1222822 A a1 R) (@lem1222823 A a0 a1 R)). Qed.
Lemma lem1222825 {A : Type'} (a0 : A) (R : type1402 A) : (term56 A R a0) = (term57 A a0 R).
Proof. exact (fun_ext (fun a1 : list A => @lem1222824 A a0 a1 R)). Qed.
Lemma lem1222826 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222827 {A : Type'} (a0 : A) (R : type1402 A) : (term58 A R a0) = (term59 A a0 R).
Proof. exact (MK_COMB (@lem1222826 A) (@lem1222825 A a0 R)). Qed.
Lemma lem1222828 {A : Type'} (R : type1402 A) : (term60 A R) = (term61 A R).
Proof. exact (fun_ext (fun a0 : A => @lem1222827 A a0 R)). Qed.
Lemma lem1222829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222830 {A : Type'} (R : type1402 A) : (term62 A R) = (term63 A R).
Proof. exact (MK_COMB (@lem1222829 A) (@lem1222828 A R)). Qed.
Lemma lem1222831 {A : Type'} (R : type1402 A) : (term64 A R) = (term65 A R).
Proof. exact (MK_COMB (@lem1222819 A R) (@lem1222830 A R)). Qed.
Lemma lem1222832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222833 {A : Type'} (R : type1402 A) : (term66 A R) = (term67 A R).
Proof. exact (MK_COMB (@lem1222832) (@lem1222831 A R)). Qed.
Lemma lem1222834 {A : Type'} (l : list A) (R : type1402 A) : (term48 A R l) = (term49 A l R).
Proof. exact (eq_refl (term48 A R l)). Qed.
Lemma lem1222835 {A : Type'} (R : type1402 A) : (term68 A R) = (term43 A R).
Proof. exact (fun_ext (fun l : list A => @lem1222834 A l R)). Qed.
Lemma lem1222836 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222837 {A : Type'} (R : type1402 A) : (term69 A R) = (term70 A R).
Proof. exact (MK_COMB (@lem1222836 A) (@lem1222835 A R)). Qed.
Lemma lem1222838 {A : Type'} (R : type1402 A) : (term42 A R) = (term71 A R).
Proof. exact (MK_COMB (@lem1222833 A R) (@lem1222837 A R)). Qed.
Lemma lem1222839 {A : Type'} (R : type1402 A) : term71 A R.
Proof. exact (EQ_MP (@lem1222838 A R) (@lem1222816 A R)). Qed.
Lemma lem1222849 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1222795 A l) (@lem1222794 A l)). Qed.
Lemma lem1222850 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1222849 A l). Qed.
Lemma lem1222851 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1222850 A m). Qed.
Lemma lem1222852 {A : Type'} (R : type1402 A) : (@List.ForallOrdPairs A R) = (@List.ForallOrdPairs A R).
Proof. exact (eq_refl (@List.ForallOrdPairs A R)). Qed.
Lemma lem1222853 {A : Type'} (R : type1402 A) (m : list A) : (term72 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (MK_COMB (@lem1222852 A R) (@lem1222851 A m)). Qed.
Lemma lem1222854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1222855 {A : Type'} (R : type1402 A) (m : list A) : (term73 A R m) = (term74 A R m).
Proof. exact (MK_COMB (@lem1222854) (@lem1222853 A R m)). Qed.
Lemma lem1222859 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem1222860 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (@lem1222859 A r). Qed.
Lemma lem1222861 {A : Type'} (R : type1402 A) : (@List.ForallOrdPairs A R (@nil A)) = True.
Proof. exact (@lem1222860 A R). Qed.
Lemma lem1222862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1222863 {A : Type'} (R : type1402 A) : (term75 A R) = (and True).
Proof. exact (MK_COMB (@lem1222862) (@lem1222861 A R)). Qed.
Lemma lem1222879 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1222880 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem1222879 A x). Qed.
Lemma lem1222881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1222882 {A : Type'} (x : A) : (term76 A x) = (and False).
Proof. exact (MK_COMB (@lem1222881) (@lem1222880 A x)). Qed.
Lemma lem1222883 {A : Type'} (y : A) (m : list A) : (@List.In A y m) = (@List.In A y m).
Proof. exact (eq_refl (@List.In A y m)). Qed.
Lemma lem1222884 {A : Type'} (x : A) (y : A) (m : list A) : (term77 A x y m) = (term78 A y m).
Proof. exact (MK_COMB (@lem1222882 A x) (@lem1222883 A y m)). Qed.
Lemma lem1222886 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1222887 {A : Type'} (y : A) (m : list A) : (term78 A y m) = False.
Proof. exact (@lem1222886 (@List.In A y m)). Qed.
Lemma lem1222888 {A : Type'} (x : A) (y : A) (m : list A) : (term77 A x y m) = False.
Proof. exact (TRANS (@lem1222884 A x y m) (@lem1222887 A y m)). Qed.
Lemma lem1222889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1222890 {A : Type'} (x : A) (y : A) (m : list A) : (term79 A x y m) = (imp False).
Proof. exact (MK_COMB (@lem1222889) (@lem1222888 A x y m)). Qed.
Lemma lem1222891 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1222892 {A : Type'} (m : list A) (R : type1402 A) (x : A) (y : A) : (term80 A m R x y) = (term81 A R x y).
Proof. exact (MK_COMB (@lem1222890 A x y m) (@lem1222891 A R x y)). Qed.
Lemma lem1222894 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1222895 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term81 A R x y) = True.
Proof. exact (@lem1222894 (R x y)). Qed.
Lemma lem1222896 {A : Type'} (m : list A) (R : type1402 A) (x : A) (y : A) : (term80 A m R x y) = True.
Proof. exact (TRANS (@lem1222892 A m R x y) (@lem1222895 A R x y)). Qed.
Lemma lem1222897 {A : Type'} (m : list A) (R : type1402 A) (x : A) : (term82 A m R x) = (term83 A).
Proof. exact (fun_ext (fun y : A => @lem1222896 A m R x y)). Qed.
Lemma lem1222898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222899 {A : Type'} (m : list A) (R : type1402 A) (x : A) : (term84 A m R x) = (term85 A).
Proof. exact (MK_COMB (@lem1222898 A) (@lem1222897 A m R x)). Qed.
Lemma lem1222901 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1222902 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (@lem1222901 A t). Qed.
Lemma lem1222903 {A : Type'} : (term85 A) = True.
Proof. exact (@lem1222902 A True). Qed.
Lemma lem1222904 {A : Type'} (m : list A) (R : type1402 A) (x : A) : (term84 A m R x) = True.
Proof. exact (TRANS (@lem1222899 A m R x) (@lem1222903 A)). Qed.
Lemma lem1222905 {A : Type'} (m : list A) (R : type1402 A) : (term87 A m R) = (term83 A).
Proof. exact (fun_ext (fun x : A => @lem1222904 A m R x)). Qed.
Lemma lem1222906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1222907 {A : Type'} (m : list A) (R : type1402 A) : (term88 A m R) = (term85 A).
Proof. exact (MK_COMB (@lem1222906 A) (@lem1222905 A m R)). Qed.
Lemma lem1222909 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1222910 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (@lem1222909 A t). Qed.
Lemma lem1222911 {A : Type'} : (term85 A) = True.
Proof. exact (@lem1222910 A True). Qed.
Lemma lem1222912 {A : Type'} (m : list A) (R : type1402 A) : (term88 A m R) = True.
Proof. exact (TRANS (@lem1222907 A m R) (@lem1222911 A)). Qed.
Lemma lem1222913 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1222914 {A : Type'} (R : type1402 A) (m : list A) : (term90 A m R) = (term91 A R m).
Proof. exact (MK_COMB (@lem1222913 A R m) (@lem1222912 A m R)). Qed.
Lemma lem1222916 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1222917 {A : Type'} (R : type1402 A) (m : list A) : (term91 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1222916 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1222918 {A : Type'} (R : type1402 A) (m : list A) : (term90 A m R) = (@List.ForallOrdPairs A R m).
Proof. exact (TRANS (@lem1222914 A R m) (@lem1222917 A R m)). Qed.
Lemma lem1222919 {A : Type'} (R : type1402 A) (m : list A) : (term92 A m R) = (term93 A R m).
Proof. exact (MK_COMB (@lem1222863 A R) (@lem1222918 A R m)). Qed.
Lemma lem1222921 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1222922 {A : Type'} (R : type1402 A) (m : list A) : (term93 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1222921 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1222923 {A : Type'} (R : type1402 A) (m : list A) : (term92 A m R) = (@List.ForallOrdPairs A R m).
Proof. exact (TRANS (@lem1222919 A R m) (@lem1222922 A R m)). Qed.
Lemma lem1222924 {A : Type'} (R : type1402 A) (m : list A) : ((term72 A R m) = (term92 A m R)) = ((@List.ForallOrdPairs A R m) = (@List.ForallOrdPairs A R m)).
Proof. exact (MK_COMB (@lem1222855 A R m) (@lem1222923 A R m)). Qed.
Lemma lem1222926 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1222927 (x : Prop) : (x = x) = True.
Proof. exact (@lem1222926 Prop x). Qed.
Lemma lem1222928 {A : Type'} (R : type1402 A) (m : list A) : ((@List.ForallOrdPairs A R m) = (@List.ForallOrdPairs A R m)) = True.
Proof. exact (@lem1222927 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1222929 {A : Type'} (m : list A) (R : type1402 A) : ((term72 A R m) = (term92 A m R)) = True.
Proof. exact (TRANS (@lem1222924 A R m) (@lem1222928 A R m)). Qed.
Lemma lem1222930 {A : Type'} (R : type1402 A) : (term94 A R) = (term95 A).
Proof. exact (fun_ext (fun m : list A => @lem1222929 A m R)). Qed.
Lemma lem1222931 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1222932 {A : Type'} (R : type1402 A) : (term45 A R) = (term96 A).
Proof. exact (MK_COMB (@lem1222931 A) (@lem1222930 A R)). Qed.
Lemma lem1222934 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1222935 {A : Type'} (t : Prop) : (term97 A t) = t.
Proof. exact (@lem1222934 (list A) t). Qed.
Lemma lem1222936 {A : Type'} : (term96 A) = True.
Proof. exact (@lem1222935 A True). Qed.
Lemma lem1222937 {A : Type'} (R : type1402 A) : (term45 A R) = True.
Proof. exact (TRANS (@lem1222932 A R) (@lem1222936 A)). Qed.
Lemma lem1222938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1222939 {A : Type'} (R : type1402 A) : (term47 A R) = (and True).
Proof. exact (MK_COMB (@lem1222938) (@lem1222937 A R)). Qed.
Lemma lem1222979 {A : Type'} (h : A) (t : list A) (l : list A) : (term31 A h t l) = (term32 A h t l).
Proof. exact (EQ_MP (@lem1222791 A h t l) (@lem1222790 A h t l)). Qed.
Lemma lem1222980 {A : Type'} (h : A) (t : list A) (l : list A) : (term31 A h t l) = (term32 A h t l).
Proof. exact (@lem1222979 A h t l). Qed.
Lemma lem1222981 {A : Type'} (a0 : A) (a1 : list A) (m : list A) : (term31 A a0 a1 m) = (term32 A a0 a1 m).
Proof. exact (@lem1222980 A a0 a1 m). Qed.
Lemma lem1222982 {A : Type'} (R : type1402 A) : (@List.ForallOrdPairs A R) = (@List.ForallOrdPairs A R).
Proof. exact (eq_refl (@List.ForallOrdPairs A R)). Qed.
Lemma lem1222983 {A : Type'} (R : type1402 A) (a0 : A) (a1 : list A) (m : list A) : (term98 A R a0 a1 m) = (term99 A R a0 a1 m).
Proof. exact (MK_COMB (@lem1222982 A R) (@lem1222981 A a0 a1 m)). Qed.
Lemma lem1222985 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term100 A r h t) = (term101 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1222986 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term100 A r h t) = (term101 A h r t).
Proof. exact (@lem1222985 A h r t). Qed.
Lemma lem1222987 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term99 A R a0 a1 m) = (term102 A a0 R a1 m).
Proof. exact (@lem1222986 A a0 R (@List.app A a1 m)). Qed.
Lemma lem1222991 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term23 _27241 P l1 l2) = (term24 _27241 l1 P l2).
Proof. exact (EQ_MP (@lem1222777 _27241 l1 P l2) (@lem1222776 _27241 l1 P l2)). Qed.
Lemma lem1222992 {A : Type'} (l1 : list A) (P : A -> Prop) (l2 : list A) : (term23 A P l1 l2) = (term24 A l1 P l2).
Proof. exact (@lem1222991 A l1 P l2). Qed.
Lemma lem1222993 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (m : list A) : (term103 A R a0 a1 m) = (term104 A a1 R a0 m).
Proof. exact (@lem1222992 A a1 (R a0) m). Qed.
Lemma lem1222997 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1222768 _26777 l P) (@lem1222767 _26777 P l)). Qed.
Lemma lem1222998 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1222997 A l P). Qed.
Lemma lem1222999 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term105 A R a0 a1) = (term106 A a1 R a0).
Proof. exact (@lem1222998 A a1 (R a0)). Qed.
Lemma lem1223006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223007 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term107 A R a0 a1) = (term108 A a1 R a0).
Proof. exact (MK_COMB (@lem1223006) (@lem1222999 A a1 R a0)). Qed.
Lemma lem1223009 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1222768 _26777 l P) (@lem1222767 _26777 P l)). Qed.
Lemma lem1223010 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1223009 A l P). Qed.
Lemma lem1223011 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term105 A R a0 m) = (term106 A m R a0).
Proof. exact (@lem1223010 A m (R a0)). Qed.
Lemma lem1223018 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term104 A a1 R a0 m) = (term109 A a1 m R a0).
Proof. exact (MK_COMB (@lem1223007 A a1 R a0) (@lem1223011 A m R a0)). Qed.
Lemma lem1223021 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term103 A R a0 a1 m) = (term109 A a1 m R a0).
Proof. exact (TRANS (@lem1222993 A a1 R a0 m) (@lem1223018 A a1 m R a0)). Qed.
Lemma lem1223022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223023 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term110 A R a0 a1 m) = (term111 A a1 m R a0).
Proof. exact (MK_COMB (@lem1223022) (@lem1223021 A a1 m R a0)). Qed.
Lemma lem1223024 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term112 A R a1 m) = (term112 A R a1 m).
Proof. exact (eq_refl (term112 A R a1 m)). Qed.
Lemma lem1223025 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term102 A a0 R a1 m) = (term113 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1223023 A a1 m R a0) (@lem1223024 A R a1 m)). Qed.
Lemma lem1223028 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term99 A R a0 a1 m) = (term113 A a0 R a1 m).
Proof. exact (TRANS (@lem1222987 A a0 R a1 m) (@lem1223025 A a0 R a1 m)). Qed.
Lemma lem1223029 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term98 A R a0 a1 m) = (term113 A a0 R a1 m).
Proof. exact (TRANS (@lem1222983 A R a0 a1 m) (@lem1223028 A a0 R a1 m)). Qed.
Lemma lem1223030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223031 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term114 A R a0 a1 m) = (term115 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1223030) (@lem1223029 A a0 R a1 m)). Qed.
Lemma lem1223035 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term100 A r h t) = (term101 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1223036 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term100 A r h t) = (term101 A h r t).
Proof. exact (@lem1223035 A h r t). Qed.
Lemma lem1223037 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term100 A R a0 a1) = (term101 A a0 R a1).
Proof. exact (@lem1223036 A a0 R a1). Qed.
Lemma lem1223041 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1222768 _26777 l P) (@lem1222767 _26777 P l)). Qed.
Lemma lem1223042 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1223041 A l P). Qed.
Lemma lem1223043 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term105 A R a0 a1) = (term106 A a1 R a0).
Proof. exact (@lem1223042 A a1 (R a0)). Qed.
Lemma lem1223050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223051 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term107 A R a0 a1) = (term108 A a1 R a0).
Proof. exact (MK_COMB (@lem1223050) (@lem1223043 A a1 R a0)). Qed.
Lemma lem1223052 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1223053 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term101 A a0 R a1) = (term116 A a0 R a1).
Proof. exact (MK_COMB (@lem1223051 A a1 R a0) (@lem1223052 A R a1)). Qed.
Lemma lem1223056 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term100 A R a0 a1) = (term116 A a0 R a1).
Proof. exact (TRANS (@lem1223037 A a0 R a1) (@lem1223053 A a0 R a1)). Qed.
Lemma lem1223057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223058 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term117 A R a0 a1) = (term118 A a0 R a1).
Proof. exact (MK_COMB (@lem1223057) (@lem1223056 A a0 R a1)). Qed.
Lemma lem1223074 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term119 _25376 x h t) = (term120 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1223075 {A : Type'} (h : A) (x : A) (t : list A) : (term119 A x h t) = (term120 A h x t).
Proof. exact (@lem1223074 A h x t). Qed.
Lemma lem1223076 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term119 A x a0 a1) = (term120 A a0 x a1).
Proof. exact (@lem1223075 A a0 x a1). Qed.
Lemma lem1223081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223082 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term121 A x a0 a1) = (term122 A a0 x a1).
Proof. exact (MK_COMB (@lem1223081) (@lem1223076 A a0 x a1)). Qed.
Lemma lem1223083 {A : Type'} (y : A) (m : list A) : (@List.In A y m) = (@List.In A y m).
Proof. exact (eq_refl (@List.In A y m)). Qed.
Lemma lem1223084 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term123 A x a0 a1 y m) = (term124 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1223082 A a0 x a1) (@lem1223083 A y m)). Qed.
Lemma lem1223087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1223088 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term125 A x a0 a1 y m) = (term126 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1223087) (@lem1223084 A a0 x a1 y m)). Qed.
Lemma lem1223089 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1223090 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term127 A a0 a1 m R x y) = (term128 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1223088 A a0 x a1 y m) (@lem1223089 A R x y)). Qed.
Lemma lem1223093 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term129 A a0 a1 m R x) = (term130 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223090 A a0 a1 m R x y)). Qed.
Lemma lem1223094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223095 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term131 A a0 a1 m R x) = (term132 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1223094 A) (@lem1223093 A a0 a1 m R x)). Qed.
Lemma lem1223100 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term133 A a0 a1 m R) = (term134 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223095 A a0 a1 m R x)). Qed.
Lemma lem1223101 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223102 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term135 A a0 a1 m R) = (term136 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223101 A) (@lem1223100 A a0 a1 m R)). Qed.
Lemma lem1223107 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1223108 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term137 A a0 a1 m R) = (term138 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223107 A R m) (@lem1223102 A a0 a1 m R)). Qed.
Lemma lem1223111 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term139 A a0 a1 m R) = (term140 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223058 A a0 R a1) (@lem1223108 A a0 a1 m R)). Qed.
Lemma lem1223114 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term98 A R a0 a1 m) = (term139 A a0 a1 m R)) = ((term113 A a0 R a1 m) = (term140 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1223031 A a0 R a1 m) (@lem1223111 A a0 a1 m R)). Qed.
Lemma lem1223117 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term141 A a0 a1 R) = (term142 A a0 a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223114 A a0 a1 m R)). Qed.
Lemma lem1223118 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223119 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term53 A a0 a1 R) = (term143 A a0 a1 R).
Proof. exact (MK_COMB (@lem1223118 A) (@lem1223117 A a0 a1 R)). Qed.
Lemma lem1223124 {A : Type'} (a1 : list A) (R : type1402 A) : (term51 A a1 R) = (term51 A a1 R).
Proof. exact (eq_refl (term51 A a1 R)). Qed.
Lemma lem1223125 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term55 A a0 a1 R) = (term144 A a0 a1 R).
Proof. exact (MK_COMB (@lem1223124 A a1 R) (@lem1223119 A a0 a1 R)). Qed.
Lemma lem1223128 {A : Type'} (a0 : A) (R : type1402 A) : (term57 A a0 R) = (term145 A a0 R).
Proof. exact (fun_ext (fun a1 : list A => @lem1223125 A a0 a1 R)). Qed.
Lemma lem1223129 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223130 {A : Type'} (a0 : A) (R : type1402 A) : (term59 A a0 R) = (term146 A a0 R).
Proof. exact (MK_COMB (@lem1223129 A) (@lem1223128 A a0 R)). Qed.
Lemma lem1223135 {A : Type'} (R : type1402 A) : (term61 A R) = (term147 A R).
Proof. exact (fun_ext (fun a0 : A => @lem1223130 A a0 R)). Qed.
Lemma lem1223136 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223137 {A : Type'} (R : type1402 A) : (term63 A R) = (term148 A R).
Proof. exact (MK_COMB (@lem1223136 A) (@lem1223135 A R)). Qed.
Lemma lem1223142 {A : Type'} (R : type1402 A) : (term65 A R) = (term149 A R).
Proof. exact (MK_COMB (@lem1222939 A R) (@lem1223137 A R)). Qed.
Lemma lem1223144 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1223145 {A : Type'} (R : type1402 A) : (term149 A R) = (term148 A R).
Proof. exact (@lem1223144 (term148 A R)). Qed.
Lemma lem1223228 {A : Type'} (R : type1402 A) : (term65 A R) = (term148 A R).
Proof. exact (TRANS (@lem1223142 A R) (@lem1223145 A R)). Qed.
Lemma lem1223229 {A : Type'} (R : type1402 A) : (term148 A R) = (term65 A R).
Proof. exact (SYM (@lem1223228 A R)). Qed.
Lemma lem1223231 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1223232 {A : Type'} (R : type1402 A) : (term148 A R) = (term151 A R).
Proof. exact (@lem1223231 (term148 A R)). Qed.
Lemma lem1223233 {A : Type'} (R : type1402 A) : (term151 A R) = (term148 A R).
Proof. exact (SYM (@lem1223232 A R)). Qed.
Lemma lem1223234 {A : Type'} (R : type1402 A) (h1 : term152 A R) : term152 A R.
Proof. exact (h1). Qed.
Lemma lem1223237 {A : Type'} (R : type1402 A) (h1 : term151 A R) : term151 A R.
Proof. exact (h1). Qed.
Lemma lem1223238 {A : Type'} (R : type1402 A) : term153 A R.
Proof. exact (fun h0 : term151 A R => @lem1223237 A R h0). Qed.
Lemma lem1223239 {A : Type'} (R : type1402 A) (h1 : term153 A R) : term153 A R.
Proof. exact (h1). Qed.
Lemma lem1223240 {A : Type'} (R : type1402 A) (h1 : term151 A R) : term151 A R.
Proof. exact (h1). Qed.
Lemma lem1223241 {A : Type'} (R : type1402 A) (h1 : term151 A R) (h2 : term153 A R) : term151 A R.
Proof. exact (@lem1223239 A R h2 (@lem1223240 A R h1)). Qed.
Lemma lem1223242 {A : Type'} (R : type1402 A) (h1 : term151 A R) : term154 A R.
Proof. exact (fun h0 : term153 A R => @lem1223241 A R h1 h0). Qed.
Lemma lem1223243 {A : Type'} (R : type1402 A) (h1 : term153 A R) : term153 A R.
Proof. exact (h1). Qed.
Lemma lem1223244 {A : Type'} (R : type1402 A) (h1 : term151 A R) (h2 : term153 A R) : term151 A R.
Proof. exact (@lem1223242 A R h1 (@lem1223243 A R h2)). Qed.
Lemma lem1223245 {A : Type'} (R : type1402 A) (h1 : term153 A R) : term153 A R.
Proof. exact (fun h0 : term151 A R => @lem1223244 A R h0 h1). Qed.
Lemma lem1223246 {A : Type'} (R : type1402 A) : term155 A R.
Proof. exact (fun h0 : term153 A R => @lem1223245 A R h0). Qed.
Lemma lem1223249 {A : Type'} (R : type1402 A) : term153 A R.
Proof. exact (@lem1223246 A R (@lem1223238 A R)). Qed.
Lemma lem1223250 {A : Type'} (R : type1402 A) : term153 A R.
Proof. exact (@lem1223249 A R). Qed.
Lemma lem1223256 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1223257 {A : Type'} (R : type1402 A) : (term151 A R) = (term156 A R).
Proof. exact (@lem1223256 (term152 A R)). Qed.
Lemma lem1223259 (t : Prop) : (term157 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1223260 {A : Type'} (R : type1402 A) : (term156 A R) = (term148 A R).
Proof. exact (@lem1223259 (term148 A R)). Qed.
Lemma lem1223265 {A : Type'} (R : type1402 A) : (term151 A R) = (term148 A R).
Proof. exact (TRANS (@lem1223257 A R) (@lem1223260 A R)). Qed.
Lemma lem1223338 {A : Type'} : (term158 A) = (term159 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem1223265 A R)). Qed.
Lemma lem1223339 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1223348 {A : Type'} : (term160 A) = (term161 A).
Proof. exact (MK_COMB (@lem1223339 A) (@lem1223338 A)). Qed.
Lemma lem1223361 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term128 A a0 a1 m R x y) = (term128 A a0 a1 m R x y).
Proof. exact (eq_refl (term128 A a0 a1 m R x y)). Qed.
Lemma lem1223362 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term130 A a0 a1 m R x) = (term130 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223361 A a0 a1 m R x y)). Qed.
Lemma lem1223363 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223364 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term132 A a0 a1 m R x) = (term132 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1223363 A) (@lem1223362 A a0 a1 m R x)). Qed.
Lemma lem1223365 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term134 A a0 a1 m R) = (term134 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223364 A a0 a1 m R x)). Qed.
Lemma lem1223366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223367 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term136 A a0 a1 m R) = (term136 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223366 A) (@lem1223365 A a0 a1 m R)). Qed.
Lemma lem1223370 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1223371 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term138 A a0 a1 m R) = (term138 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223370 A R m) (@lem1223367 A a0 a1 m R)). Qed.
Lemma lem1223372 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1223377 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A a1 R a0 x) = (term162 A a1 R a0 x).
Proof. exact (eq_refl (term162 A a1 R a0 x)). Qed.
Lemma lem1223378 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term163 A a1 R a0) = (term163 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1223377 A a1 R a0 x)). Qed.
Lemma lem1223379 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223380 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term106 A a1 R a0) = (term106 A a1 R a0).
Proof. exact (MK_COMB (@lem1223379 A) (@lem1223378 A a1 R a0)). Qed.
Lemma lem1223381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223382 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term108 A a1 R a0) = (term108 A a1 R a0).
Proof. exact (MK_COMB (@lem1223381) (@lem1223380 A a1 R a0)). Qed.
Lemma lem1223383 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term116 A a0 R a1) = (term116 A a0 R a1).
Proof. exact (MK_COMB (@lem1223382 A a1 R a0) (@lem1223372 A R a1)). Qed.
Lemma lem1223384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223385 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term118 A a0 R a1) = (term118 A a0 R a1).
Proof. exact (MK_COMB (@lem1223384) (@lem1223383 A a0 R a1)). Qed.
Lemma lem1223386 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term140 A a0 a1 m R) = (term140 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1223385 A a0 R a1) (@lem1223371 A a0 a1 m R)). Qed.
Lemma lem1223387 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term112 A R a1 m) = (term112 A R a1 m).
Proof. exact (eq_refl (term112 A R a1 m)). Qed.
Lemma lem1223392 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A m R a0 x) = (term162 A m R a0 x).
Proof. exact (eq_refl (term162 A m R a0 x)). Qed.
Lemma lem1223393 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term163 A m R a0) = (term163 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1223392 A m R a0 x)). Qed.
Lemma lem1223394 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223395 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term106 A m R a0) = (term106 A m R a0).
Proof. exact (MK_COMB (@lem1223394 A) (@lem1223393 A m R a0)). Qed.
Lemma lem1223400 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A a1 R a0 x) = (term162 A a1 R a0 x).
Proof. exact (eq_refl (term162 A a1 R a0 x)). Qed.
Lemma lem1223401 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term163 A a1 R a0) = (term163 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1223400 A a1 R a0 x)). Qed.
Lemma lem1223402 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223403 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term106 A a1 R a0) = (term106 A a1 R a0).
Proof. exact (MK_COMB (@lem1223402 A) (@lem1223401 A a1 R a0)). Qed.
Lemma lem1223404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223405 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term108 A a1 R a0) = (term108 A a1 R a0).
Proof. exact (MK_COMB (@lem1223404) (@lem1223403 A a1 R a0)). Qed.
Lemma lem1223406 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term109 A a1 m R a0) = (term109 A a1 m R a0).
Proof. exact (MK_COMB (@lem1223405 A a1 R a0) (@lem1223395 A m R a0)). Qed.
Lemma lem1223407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223408 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term111 A a1 m R a0) = (term111 A a1 m R a0).
Proof. exact (MK_COMB (@lem1223407) (@lem1223406 A a1 m R a0)). Qed.
Lemma lem1223409 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term113 A a0 R a1 m) = (term113 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1223408 A a1 m R a0) (@lem1223387 A R a1 m)). Qed.
Lemma lem1223410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223411 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term115 A a0 R a1 m) = (term115 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1223410) (@lem1223409 A a0 R a1 m)). Qed.
Lemma lem1223412 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term113 A a0 R a1 m) = (term140 A a0 a1 m R)) = ((term113 A a0 R a1 m) = (term140 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1223411 A a0 R a1 m) (@lem1223386 A a0 a1 m R)). Qed.
Lemma lem1223413 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term142 A a0 a1 R) = (term142 A a0 a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223412 A a0 a1 m R)). Qed.
Lemma lem1223414 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223415 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term143 A a0 a1 R) = (term143 A a0 a1 R).
Proof. exact (MK_COMB (@lem1223414 A) (@lem1223413 A a0 a1 R)). Qed.
Lemma lem1223424 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term164 A a1 m R x y) = (term164 A a1 m R x y).
Proof. exact (eq_refl (term164 A a1 m R x y)). Qed.
Lemma lem1223425 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term165 A a1 m R x) = (term165 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223424 A a1 m R x y)). Qed.
Lemma lem1223426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223427 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term166 A a1 m R x) = (term166 A a1 m R x).
Proof. exact (MK_COMB (@lem1223426 A) (@lem1223425 A a1 m R x)). Qed.
Lemma lem1223428 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term167 A a1 m R) = (term167 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223427 A a1 m R x)). Qed.
Lemma lem1223429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223430 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term168 A a1 m R) = (term168 A a1 m R).
Proof. exact (MK_COMB (@lem1223429 A) (@lem1223428 A a1 m R)). Qed.
Lemma lem1223433 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1223434 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term169 A a1 m R) = (term169 A a1 m R).
Proof. exact (MK_COMB (@lem1223433 A R m) (@lem1223430 A a1 m R)). Qed.
Lemma lem1223437 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1223438 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term170 A a1 m R) = (term170 A a1 m R).
Proof. exact (MK_COMB (@lem1223437 A R a1) (@lem1223434 A a1 m R)). Qed.
Lemma lem1223441 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term171 A R a1 m) = (term171 A R a1 m).
Proof. exact (eq_refl (term171 A R a1 m)). Qed.
Lemma lem1223442 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term112 A R a1 m) = (term170 A a1 m R)) = ((term112 A R a1 m) = (term170 A a1 m R)).
Proof. exact (MK_COMB (@lem1223441 A R a1 m) (@lem1223438 A a1 m R)). Qed.
Lemma lem1223443 {A : Type'} (a1 : list A) (R : type1402 A) : (term172 A a1 R) = (term172 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223442 A a1 m R)). Qed.
Lemma lem1223444 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223445 {A : Type'} (a1 : list A) (R : type1402 A) : (term49 A a1 R) = (term49 A a1 R).
Proof. exact (MK_COMB (@lem1223444 A) (@lem1223443 A a1 R)). Qed.
Lemma lem1223446 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1223447 {A : Type'} (a1 : list A) (R : type1402 A) : (term51 A a1 R) = (term51 A a1 R).
Proof. exact (MK_COMB (@lem1223446) (@lem1223445 A a1 R)). Qed.
Lemma lem1223448 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : (term144 A a0 a1 R) = (term144 A a0 a1 R).
Proof. exact (MK_COMB (@lem1223447 A a1 R) (@lem1223415 A a0 a1 R)). Qed.
Lemma lem1223449 {A : Type'} (a0 : A) (R : type1402 A) : (term145 A a0 R) = (term145 A a0 R).
Proof. exact (fun_ext (fun a1 : list A => @lem1223448 A a0 a1 R)). Qed.
Lemma lem1223450 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223451 {A : Type'} (a0 : A) (R : type1402 A) : (term146 A a0 R) = (term146 A a0 R).
Proof. exact (MK_COMB (@lem1223450 A) (@lem1223449 A a0 R)). Qed.
Lemma lem1223452 {A : Type'} (R : type1402 A) : (term147 A R) = (term147 A R).
Proof. exact (fun_ext (fun a0 : A => @lem1223451 A a0 R)). Qed.
Lemma lem1223453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223454 {A : Type'} (R : type1402 A) : (term148 A R) = (term148 A R).
Proof. exact (MK_COMB (@lem1223453 A) (@lem1223452 A R)). Qed.
Lemma lem1223455 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem1223454 A R)). Qed.
Lemma lem1223456 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1223457 {A : Type'} : (term161 A) = (term161 A).
Proof. exact (MK_COMB (@lem1223456 A) (@lem1223455 A)). Qed.
Lemma lem1223564 {A : Type'} : (term160 A) = (term161 A).
Proof. exact (TRANS (@lem1223348 A) (@lem1223457 A)). Qed.
Lemma lem1223565 {A : Type'} : (term161 A) = (term160 A).
Proof. exact (SYM (@lem1223564 A)). Qed.
Lemma lem1223566 {A : Type'} (a1 : list A) (R : type1402 A) (h1 : term49 A a1 R) : term49 A a1 R.
Proof. exact (h1). Qed.
Lemma lem1223568 (p : Prop) : p = (term150 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1223569 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term113 A a0 R a1 m) = (term140 A a0 a1 m R)) = (term173 A a0 a1 m R).
Proof. exact (@lem1223568 ((term113 A a0 R a1 m) = (term140 A a0 a1 m R))). Qed.
Lemma lem1223570 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term173 A a0 a1 m R) = ((term113 A a0 R a1 m) = (term140 A a0 a1 m R)).
Proof. exact (SYM (@lem1223569 A a0 a1 m R)). Qed.
Lemma lem1223571 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term174 A a0 a1 m R) : term174 A a0 a1 m R.
Proof. exact (h1). Qed.
Lemma lem1223586 {A : Type'} (x : A) (a1 : list A) (y : A) (m : list A) : (term175 A x a1 y m) = (term176 A x a1 y m).
Proof. exact (@lem17045 (@List.In A x a1) (@List.In A y m)). Qed.
Lemma lem1223591 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1223596 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term177 A a1 m R x y) = (term178 A a1 m R x y).
Proof. exact (@lem17362 (term179 A x a1 y m) (R x y)). Qed.
Lemma lem1223597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1223598 {A : Type'} (x : A) (a1 : list A) (y : A) (m : list A) : (term180 A x a1 y m) = (term181 A x a1 y m).
Proof. exact (MK_COMB (@lem1223597) (@lem1223586 A x a1 y m)). Qed.
Lemma lem1223599 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term182 A a1 m R x y) = (term183 A a1 m R x y).
Proof. exact (MK_COMB (@lem1223598 A x a1 y m) (@lem1223591 A R x y)). Qed.
Lemma lem1223600 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term164 A a1 m R x y) = (term182 A a1 m R x y).
Proof. exact (@lem17265 (term179 A x a1 y m) (R x y)). Qed.
Lemma lem1223601 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term164 A a1 m R x y) = (term183 A a1 m R x y).
Proof. exact (TRANS (@lem1223600 A a1 m R x y) (@lem1223599 A a1 m R x y)). Qed.
Lemma lem1223602 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1223603 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term186 A a1 m R x) = (term187 A a1 m R x).
Proof. exact (@lem1223602 A (term165 A a1 m R x)). Qed.
Lemma lem1223604 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term188 A a1 m R x y) = (term164 A a1 m R x y).
Proof. exact (eq_refl (term188 A a1 m R x y)). Qed.
Lemma lem1223605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1223606 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term189 A a1 m R x y) = (term177 A a1 m R x y).
Proof. exact (MK_COMB (@lem1223605) (@lem1223604 A a1 m R x y)). Qed.
Lemma lem1223607 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term189 A a1 m R x y) = (term178 A a1 m R x y).
Proof. exact (TRANS (@lem1223606 A a1 m R x y) (@lem1223596 A a1 m R x y)). Qed.
Lemma lem1223608 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term190 A a1 m R x) = (term191 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223607 A a1 m R x y)). Qed.
Lemma lem1223609 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223610 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term187 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (MK_COMB (@lem1223609 A) (@lem1223608 A a1 m R x)). Qed.
Lemma lem1223611 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term186 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (TRANS (@lem1223603 A a1 m R x) (@lem1223610 A a1 m R x)). Qed.
Lemma lem1223612 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term165 A a1 m R x) = (term193 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223601 A a1 m R x y)). Qed.
Lemma lem1223613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223614 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term166 A a1 m R x) = (term194 A a1 m R x).
Proof. exact (MK_COMB (@lem1223613 A) (@lem1223612 A a1 m R x)). Qed.
Lemma lem1223615 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1223616 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term195 A a1 m R) = (term196 A a1 m R).
Proof. exact (@lem1223615 A (term167 A a1 m R)). Qed.
Lemma lem1223617 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term197 A a1 m R x) = (term166 A a1 m R x).
Proof. exact (eq_refl (term197 A a1 m R x)). Qed.
Lemma lem1223618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1223619 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term198 A a1 m R x) = (term186 A a1 m R x).
Proof. exact (MK_COMB (@lem1223618) (@lem1223617 A a1 m R x)). Qed.
Lemma lem1223620 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term198 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (TRANS (@lem1223619 A a1 m R x) (@lem1223611 A a1 m R x)). Qed.
Lemma lem1223621 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term199 A a1 m R) = (term200 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223620 A a1 m R x)). Qed.
Lemma lem1223622 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223623 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term196 A a1 m R) = (term201 A a1 m R).
Proof. exact (MK_COMB (@lem1223622 A) (@lem1223621 A a1 m R)). Qed.
Lemma lem1223624 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term195 A a1 m R) = (term201 A a1 m R).
Proof. exact (TRANS (@lem1223616 A a1 m R) (@lem1223623 A a1 m R)). Qed.
Lemma lem1223625 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term167 A a1 m R) = (term202 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223614 A a1 m R x)). Qed.
Lemma lem1223626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1223627 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term168 A a1 m R) = (term203 A a1 m R).
Proof. exact (MK_COMB (@lem1223626 A) (@lem1223625 A a1 m R)). Qed.
Lemma lem1223629 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1223630 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term205 A a1 m R) = (term206 A a1 m R).
Proof. exact (MK_COMB (@lem1223629 A R m) (@lem1223624 A a1 m R)). Qed.
Lemma lem1223631 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term207 A a1 m R) = (term205 A a1 m R).
Proof. exact (@lem17045 (@List.ForallOrdPairs A R m) (term168 A a1 m R)). Qed.
Lemma lem1223632 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term207 A a1 m R) = (term206 A a1 m R).
Proof. exact (TRANS (@lem1223631 A a1 m R) (@lem1223630 A a1 m R)). Qed.
Lemma lem1223634 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1223635 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term169 A a1 m R) = (term208 A a1 m R).
Proof. exact (MK_COMB (@lem1223634 A R m) (@lem1223627 A a1 m R)). Qed.
Lemma lem1223637 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223638 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term209 A a1 m R) = (term210 A a1 m R).
Proof. exact (MK_COMB (@lem1223637 A R a1) (@lem1223632 A a1 m R)). Qed.
Lemma lem1223639 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term211 A a1 m R) = (term209 A a1 m R).
Proof. exact (@lem17045 (@List.ForallOrdPairs A R a1) (term169 A a1 m R)). Qed.
Lemma lem1223640 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term211 A a1 m R) = (term210 A a1 m R).
Proof. exact (TRANS (@lem1223639 A a1 m R) (@lem1223638 A a1 m R)). Qed.
Lemma lem1223642 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1223643 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term170 A a1 m R) = (term212 A a1 m R).
Proof. exact (MK_COMB (@lem1223642 A R a1) (@lem1223635 A a1 m R)). Qed.
Lemma lem1223645 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1223646 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term214 A a1 m R) = (term215 A a1 m R).
Proof. exact (MK_COMB (@lem1223645 A R a1 m) (@lem1223643 A a1 m R)). Qed.
Lemma lem1223648 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1223649 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term217 A a1 m R) = (term218 A a1 m R).
Proof. exact (MK_COMB (@lem1223648 A R a1 m) (@lem1223640 A a1 m R)). Qed.
Lemma lem1223650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223651 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term219 A a1 m R) = (term220 A a1 m R).
Proof. exact (MK_COMB (@lem1223650) (@lem1223649 A a1 m R)). Qed.
Lemma lem1223652 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term221 A a1 m R) = (term222 A a1 m R).
Proof. exact (MK_COMB (@lem1223651 A a1 m R) (@lem1223646 A a1 m R)). Qed.
Lemma lem1223653 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term112 A R a1 m) = (term170 A a1 m R)) = (term221 A a1 m R).
Proof. exact (@lem17784 (term112 A R a1 m) (term170 A a1 m R)). Qed.
Lemma lem1223654 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term112 A R a1 m) = (term170 A a1 m R)) = (term222 A a1 m R).
Proof. exact (TRANS (@lem1223653 A a1 m R) (@lem1223652 A a1 m R)). Qed.
Lemma lem1223655 {A : Type'} (a1 : list A) (R : type1402 A) : (term172 A a1 R) = (term223 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223654 A a1 m R)). Qed.
Lemma lem1223656 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223657 {A : Type'} (a1 : list A) (R : type1402 A) : (term49 A a1 R) = (term224 A a1 R).
Proof. exact (MK_COMB (@lem1223656 A) (@lem1223655 A a1 R)). Qed.
Lemma lem1223659 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term225 A P Q) = (term226 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1223660 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term227 A P Q) = (term228 A P Q).
Proof. exact (@lem1223659 (list A) P Q). Qed.
Lemma lem1223661 {A : Type'} (a1 : list A) (R : type1402 A) : (term229 A a1 R) = (term230 A a1 R).
Proof. exact (@lem1223660 A (term231 A a1 R) (term232 A a1 R)). Qed.
Lemma lem1223662 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term233 A a1 R m) = (term218 A a1 m R).
Proof. exact (eq_refl (term233 A a1 R m)). Qed.
Lemma lem1223663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223664 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term234 A a1 R m) = (term220 A a1 m R).
Proof. exact (MK_COMB (@lem1223663) (@lem1223662 A a1 m R)). Qed.
Lemma lem1223665 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term235 A a1 R m) = (term215 A a1 m R).
Proof. exact (eq_refl (term235 A a1 R m)). Qed.
Lemma lem1223666 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term236 A a1 R m) = (term222 A a1 m R).
Proof. exact (MK_COMB (@lem1223664 A a1 m R) (@lem1223665 A a1 m R)). Qed.
Lemma lem1223667 {A : Type'} (a1 : list A) (R : type1402 A) : (term237 A a1 R) = (term223 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223666 A a1 m R)). Qed.
Lemma lem1223668 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223669 {A : Type'} (a1 : list A) (R : type1402 A) : (term229 A a1 R) = (term224 A a1 R).
Proof. exact (MK_COMB (@lem1223668 A) (@lem1223667 A a1 R)). Qed.
Lemma lem1223670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223671 {A : Type'} (a1 : list A) (R : type1402 A) : (term238 A a1 R) = (term239 A a1 R).
Proof. exact (MK_COMB (@lem1223670) (@lem1223669 A a1 R)). Qed.
Lemma lem1223672 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term233 A a1 R m) = (term218 A a1 m R).
Proof. exact (eq_refl (term233 A a1 R m)). Qed.
Lemma lem1223673 {A : Type'} (a1 : list A) (R : type1402 A) : (term240 A a1 R) = (term231 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223672 A a1 m R)). Qed.
Lemma lem1223674 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223675 {A : Type'} (a1 : list A) (R : type1402 A) : (term241 A a1 R) = (term242 A a1 R).
Proof. exact (MK_COMB (@lem1223674 A) (@lem1223673 A a1 R)). Qed.
Lemma lem1223676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1223677 {A : Type'} (a1 : list A) (R : type1402 A) : (term243 A a1 R) = (term244 A a1 R).
Proof. exact (MK_COMB (@lem1223676) (@lem1223675 A a1 R)). Qed.
Lemma lem1223678 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term235 A a1 R m) = (term215 A a1 m R).
Proof. exact (eq_refl (term235 A a1 R m)). Qed.
Lemma lem1223679 {A : Type'} (a1 : list A) (R : type1402 A) : (term245 A a1 R) = (term232 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1223678 A a1 m R)). Qed.
Lemma lem1223680 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1223681 {A : Type'} (a1 : list A) (R : type1402 A) : (term246 A a1 R) = (term247 A a1 R).
Proof. exact (MK_COMB (@lem1223680 A) (@lem1223679 A a1 R)). Qed.
Lemma lem1223682 {A : Type'} (a1 : list A) (R : type1402 A) : (term230 A a1 R) = (term248 A a1 R).
Proof. exact (MK_COMB (@lem1223677 A a1 R) (@lem1223681 A a1 R)). Qed.
Lemma lem1223683 {A : Type'} (a1 : list A) (R : type1402 A) : ((term229 A a1 R) = (term230 A a1 R)) = ((term224 A a1 R) = (term248 A a1 R)).
Proof. exact (MK_COMB (@lem1223671 A a1 R) (@lem1223682 A a1 R)). Qed.
Lemma lem1223684 {A : Type'} (a1 : list A) (R : type1402 A) : (term224 A a1 R) = (term248 A a1 R).
Proof. exact (EQ_MP (@lem1223683 A a1 R) (@lem1223661 A a1 R)). Qed.
Lemma lem1223886 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1223887 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223886 A P Q). Qed.
Lemma lem1223888 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term251 A a1 m R) = (term252 A a1 m R).
Proof. exact (@lem1223887 A (term253 A R m) (term200 A a1 m R)). Qed.
Lemma lem1223889 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term254 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (eq_refl (term254 A a1 m R x)). Qed.
Lemma lem1223890 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term255 A a1 m R) = (term200 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223889 A a1 m R x)). Qed.
Lemma lem1223891 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223892 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term256 A a1 m R) = (term201 A a1 m R).
Proof. exact (MK_COMB (@lem1223891 A) (@lem1223890 A a1 m R)). Qed.
Lemma lem1223893 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1223894 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term251 A a1 m R) = (term206 A a1 m R).
Proof. exact (MK_COMB (@lem1223893 A R m) (@lem1223892 A a1 m R)). Qed.
Lemma lem1223895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223896 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term257 A a1 m R) = (term258 A a1 m R).
Proof. exact (MK_COMB (@lem1223895) (@lem1223894 A a1 m R)). Qed.
Lemma lem1223897 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term254 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (eq_refl (term254 A a1 m R x)). Qed.
Lemma lem1223898 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1223899 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term259 A a1 m R x) = (term260 A a1 m R x).
Proof. exact (MK_COMB (@lem1223898 A R m) (@lem1223897 A a1 m R x)). Qed.
Lemma lem1223900 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term261 A a1 m R) = (term262 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223899 A a1 m R x)). Qed.
Lemma lem1223901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223902 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term252 A a1 m R) = (term263 A a1 m R).
Proof. exact (MK_COMB (@lem1223901 A) (@lem1223900 A a1 m R)). Qed.
Lemma lem1223903 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term251 A a1 m R) = (term252 A a1 m R)) = ((term206 A a1 m R) = (term263 A a1 m R)).
Proof. exact (MK_COMB (@lem1223896 A a1 m R) (@lem1223902 A a1 m R)). Qed.
Lemma lem1223904 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term206 A a1 m R) = (term263 A a1 m R).
Proof. exact (EQ_MP (@lem1223903 A a1 m R) (@lem1223888 A a1 m R)). Qed.
Lemma lem1223906 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1223907 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223906 A P Q). Qed.
Lemma lem1223908 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term264 A a1 m R x) = (term265 A a1 m R x).
Proof. exact (@lem1223907 A (term253 A R m) (term191 A a1 m R x)). Qed.
Lemma lem1223909 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term266 A a1 m R x y) = (term178 A a1 m R x y).
Proof. exact (eq_refl (term266 A a1 m R x y)). Qed.
Lemma lem1223910 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term267 A a1 m R x) = (term191 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223909 A a1 m R x y)). Qed.
Lemma lem1223911 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223912 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term268 A a1 m R x) = (term192 A a1 m R x).
Proof. exact (MK_COMB (@lem1223911 A) (@lem1223910 A a1 m R x)). Qed.
Lemma lem1223913 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1223914 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term264 A a1 m R x) = (term260 A a1 m R x).
Proof. exact (MK_COMB (@lem1223913 A R m) (@lem1223912 A a1 m R x)). Qed.
Lemma lem1223915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223916 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term269 A a1 m R x) = (term270 A a1 m R x).
Proof. exact (MK_COMB (@lem1223915) (@lem1223914 A a1 m R x)). Qed.
Lemma lem1223917 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term266 A a1 m R x y) = (term178 A a1 m R x y).
Proof. exact (eq_refl (term266 A a1 m R x y)). Qed.
Lemma lem1223918 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1223919 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term271 A a1 m R x y) = (term272 A a1 m R x y).
Proof. exact (MK_COMB (@lem1223918 A R m) (@lem1223917 A a1 m R x y)). Qed.
Lemma lem1223920 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term273 A a1 m R x) = (term274 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223919 A a1 m R x y)). Qed.
Lemma lem1223921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223922 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term265 A a1 m R x) = (term275 A a1 m R x).
Proof. exact (MK_COMB (@lem1223921 A) (@lem1223920 A a1 m R x)). Qed.
Lemma lem1223923 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term264 A a1 m R x) = (term265 A a1 m R x)) = ((term260 A a1 m R x) = (term275 A a1 m R x)).
Proof. exact (MK_COMB (@lem1223916 A a1 m R x) (@lem1223922 A a1 m R x)). Qed.
Lemma lem1223924 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term260 A a1 m R x) = (term275 A a1 m R x).
Proof. exact (EQ_MP (@lem1223923 A a1 m R x) (@lem1223908 A a1 m R x)). Qed.
Lemma lem1223925 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term262 A a1 m R) = (term276 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223924 A a1 m R x)). Qed.
Lemma lem1223926 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223927 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term263 A a1 m R) = (term277 A a1 m R).
Proof. exact (MK_COMB (@lem1223926 A) (@lem1223925 A a1 m R)). Qed.
Lemma lem1223928 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term206 A a1 m R) = (term277 A a1 m R).
Proof. exact (TRANS (@lem1223904 A a1 m R) (@lem1223927 A a1 m R)). Qed.
Lemma lem1223929 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223930 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term210 A a1 m R) = (term278 A a1 m R).
Proof. exact (MK_COMB (@lem1223929 A R a1) (@lem1223928 A a1 m R)). Qed.
Lemma lem1223932 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1223933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223932 A P Q). Qed.
Lemma lem1223934 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term279 A a1 m R) = (term280 A a1 m R).
Proof. exact (@lem1223933 A (term253 A R a1) (term276 A a1 m R)). Qed.
Lemma lem1223935 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term281 A a1 m R x) = (term275 A a1 m R x).
Proof. exact (eq_refl (term281 A a1 m R x)). Qed.
Lemma lem1223936 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term282 A a1 m R) = (term276 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223935 A a1 m R x)). Qed.
Lemma lem1223937 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223938 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term283 A a1 m R) = (term277 A a1 m R).
Proof. exact (MK_COMB (@lem1223937 A) (@lem1223936 A a1 m R)). Qed.
Lemma lem1223939 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223940 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term279 A a1 m R) = (term278 A a1 m R).
Proof. exact (MK_COMB (@lem1223939 A R a1) (@lem1223938 A a1 m R)). Qed.
Lemma lem1223941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223942 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term284 A a1 m R) = (term285 A a1 m R).
Proof. exact (MK_COMB (@lem1223941) (@lem1223940 A a1 m R)). Qed.
Lemma lem1223943 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term281 A a1 m R x) = (term275 A a1 m R x).
Proof. exact (eq_refl (term281 A a1 m R x)). Qed.
Lemma lem1223944 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223945 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term286 A a1 m R x) = (term287 A a1 m R x).
Proof. exact (MK_COMB (@lem1223944 A R a1) (@lem1223943 A a1 m R x)). Qed.
Lemma lem1223946 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term288 A a1 m R) = (term289 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223945 A a1 m R x)). Qed.
Lemma lem1223947 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223948 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term280 A a1 m R) = (term290 A a1 m R).
Proof. exact (MK_COMB (@lem1223947 A) (@lem1223946 A a1 m R)). Qed.
Lemma lem1223949 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term279 A a1 m R) = (term280 A a1 m R)) = ((term278 A a1 m R) = (term290 A a1 m R)).
Proof. exact (MK_COMB (@lem1223942 A a1 m R) (@lem1223948 A a1 m R)). Qed.
Lemma lem1223950 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term278 A a1 m R) = (term290 A a1 m R).
Proof. exact (EQ_MP (@lem1223949 A a1 m R) (@lem1223934 A a1 m R)). Qed.
Lemma lem1223952 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1223953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223952 A P Q). Qed.
Lemma lem1223954 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term291 A a1 m R x) = (term292 A a1 m R x).
Proof. exact (@lem1223953 A (term253 A R a1) (term274 A a1 m R x)). Qed.
Lemma lem1223955 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term293 A a1 m R x y) = (term272 A a1 m R x y).
Proof. exact (eq_refl (term293 A a1 m R x y)). Qed.
Lemma lem1223956 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term294 A a1 m R x) = (term274 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223955 A a1 m R x y)). Qed.
Lemma lem1223957 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223958 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term295 A a1 m R x) = (term275 A a1 m R x).
Proof. exact (MK_COMB (@lem1223957 A) (@lem1223956 A a1 m R x)). Qed.
Lemma lem1223959 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223960 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term291 A a1 m R x) = (term287 A a1 m R x).
Proof. exact (MK_COMB (@lem1223959 A R a1) (@lem1223958 A a1 m R x)). Qed.
Lemma lem1223961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223962 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term296 A a1 m R x) = (term297 A a1 m R x).
Proof. exact (MK_COMB (@lem1223961) (@lem1223960 A a1 m R x)). Qed.
Lemma lem1223963 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term293 A a1 m R x y) = (term272 A a1 m R x y).
Proof. exact (eq_refl (term293 A a1 m R x y)). Qed.
Lemma lem1223964 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1223965 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term298 A a1 m R x y) = (term299 A a1 m R x y).
Proof. exact (MK_COMB (@lem1223964 A R a1) (@lem1223963 A a1 m R x y)). Qed.
Lemma lem1223966 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term300 A a1 m R x) = (term301 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1223965 A a1 m R x y)). Qed.
Lemma lem1223967 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223968 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term292 A a1 m R x) = (term302 A a1 m R x).
Proof. exact (MK_COMB (@lem1223967 A) (@lem1223966 A a1 m R x)). Qed.
Lemma lem1223969 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term291 A a1 m R x) = (term292 A a1 m R x)) = ((term287 A a1 m R x) = (term302 A a1 m R x)).
Proof. exact (MK_COMB (@lem1223962 A a1 m R x) (@lem1223968 A a1 m R x)). Qed.
Lemma lem1223970 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term287 A a1 m R x) = (term302 A a1 m R x).
Proof. exact (EQ_MP (@lem1223969 A a1 m R x) (@lem1223954 A a1 m R x)). Qed.
Lemma lem1223971 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term289 A a1 m R) = (term303 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223970 A a1 m R x)). Qed.
Lemma lem1223972 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223973 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term290 A a1 m R) = (term304 A a1 m R).
Proof. exact (MK_COMB (@lem1223972 A) (@lem1223971 A a1 m R)). Qed.
Lemma lem1223974 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term278 A a1 m R) = (term304 A a1 m R).
Proof. exact (TRANS (@lem1223950 A a1 m R) (@lem1223973 A a1 m R)). Qed.
Lemma lem1223975 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term210 A a1 m R) = (term304 A a1 m R).
Proof. exact (TRANS (@lem1223930 A a1 m R) (@lem1223974 A a1 m R)). Qed.
Lemma lem1223976 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1223977 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term218 A a1 m R) = (term305 A a1 m R).
Proof. exact (MK_COMB (@lem1223976 A R a1 m) (@lem1223975 A a1 m R)). Qed.
Lemma lem1223979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1223980 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223979 A P Q). Qed.
Lemma lem1223981 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term306 A a1 m R) = (term307 A a1 m R).
Proof. exact (@lem1223980 A (term112 A R a1 m) (term303 A a1 m R)). Qed.
Lemma lem1223982 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term308 A a1 m R x) = (term302 A a1 m R x).
Proof. exact (eq_refl (term308 A a1 m R x)). Qed.
Lemma lem1223983 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term309 A a1 m R) = (term303 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223982 A a1 m R x)). Qed.
Lemma lem1223984 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223985 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term310 A a1 m R) = (term304 A a1 m R).
Proof. exact (MK_COMB (@lem1223984 A) (@lem1223983 A a1 m R)). Qed.
Lemma lem1223986 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1223987 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term306 A a1 m R) = (term305 A a1 m R).
Proof. exact (MK_COMB (@lem1223986 A R a1 m) (@lem1223985 A a1 m R)). Qed.
Lemma lem1223988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1223989 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term311 A a1 m R) = (term312 A a1 m R).
Proof. exact (MK_COMB (@lem1223988) (@lem1223987 A a1 m R)). Qed.
Lemma lem1223990 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term308 A a1 m R x) = (term302 A a1 m R x).
Proof. exact (eq_refl (term308 A a1 m R x)). Qed.
Lemma lem1223991 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1223992 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term313 A a1 m R x) = (term314 A a1 m R x).
Proof. exact (MK_COMB (@lem1223991 A R a1 m) (@lem1223990 A a1 m R x)). Qed.
Lemma lem1223993 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term315 A a1 m R) = (term316 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1223992 A a1 m R x)). Qed.
Lemma lem1223994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1223995 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term307 A a1 m R) = (term317 A a1 m R).
Proof. exact (MK_COMB (@lem1223994 A) (@lem1223993 A a1 m R)). Qed.
Lemma lem1223996 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term306 A a1 m R) = (term307 A a1 m R)) = ((term305 A a1 m R) = (term317 A a1 m R)).
Proof. exact (MK_COMB (@lem1223989 A a1 m R) (@lem1223995 A a1 m R)). Qed.
Lemma lem1223997 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term305 A a1 m R) = (term317 A a1 m R).
Proof. exact (EQ_MP (@lem1223996 A a1 m R) (@lem1223981 A a1 m R)). Qed.
Lemma lem1223999 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1224000 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1223999 A P Q). Qed.
Lemma lem1224001 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term318 A a1 m R x) = (term319 A a1 m R x).
Proof. exact (@lem1224000 A (term112 A R a1 m) (term301 A a1 m R x)). Qed.
Lemma lem1224002 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a1 m R x y) = (term299 A a1 m R x y).
Proof. exact (eq_refl (term320 A a1 m R x y)). Qed.
Lemma lem1224003 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term321 A a1 m R x) = (term301 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224002 A a1 m R x y)). Qed.
Lemma lem1224004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224005 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term322 A a1 m R x) = (term302 A a1 m R x).
Proof. exact (MK_COMB (@lem1224004 A) (@lem1224003 A a1 m R x)). Qed.
Lemma lem1224006 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1224007 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term318 A a1 m R x) = (term314 A a1 m R x).
Proof. exact (MK_COMB (@lem1224006 A R a1 m) (@lem1224005 A a1 m R x)). Qed.
Lemma lem1224008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224009 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term323 A a1 m R x) = (term324 A a1 m R x).
Proof. exact (MK_COMB (@lem1224008) (@lem1224007 A a1 m R x)). Qed.
Lemma lem1224010 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a1 m R x y) = (term299 A a1 m R x y).
Proof. exact (eq_refl (term320 A a1 m R x y)). Qed.
Lemma lem1224011 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1224012 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term325 A a1 m R x y) = (term326 A a1 m R x y).
Proof. exact (MK_COMB (@lem1224011 A R a1 m) (@lem1224010 A a1 m R x y)). Qed.
Lemma lem1224013 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term327 A a1 m R x) = (term328 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224012 A a1 m R x y)). Qed.
Lemma lem1224014 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224015 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term319 A a1 m R x) = (term329 A a1 m R x).
Proof. exact (MK_COMB (@lem1224014 A) (@lem1224013 A a1 m R x)). Qed.
Lemma lem1224016 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term318 A a1 m R x) = (term319 A a1 m R x)) = ((term314 A a1 m R x) = (term329 A a1 m R x)).
Proof. exact (MK_COMB (@lem1224009 A a1 m R x) (@lem1224015 A a1 m R x)). Qed.
Lemma lem1224017 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term314 A a1 m R x) = (term329 A a1 m R x).
Proof. exact (EQ_MP (@lem1224016 A a1 m R x) (@lem1224001 A a1 m R x)). Qed.
Lemma lem1224018 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term316 A a1 m R) = (term330 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224017 A a1 m R x)). Qed.
Lemma lem1224019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224020 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term317 A a1 m R) = (term331 A a1 m R).
Proof. exact (MK_COMB (@lem1224019 A) (@lem1224018 A a1 m R)). Qed.
Lemma lem1224021 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term305 A a1 m R) = (term331 A a1 m R).
Proof. exact (TRANS (@lem1223997 A a1 m R) (@lem1224020 A a1 m R)). Qed.
Lemma lem1224022 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term218 A a1 m R) = (term331 A a1 m R).
Proof. exact (TRANS (@lem1223977 A a1 m R) (@lem1224021 A a1 m R)). Qed.
Lemma lem1224023 {A : Type'} (a1 : list A) (R : type1402 A) : (term231 A a1 R) = (term332 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1224022 A a1 m R)). Qed.
Lemma lem1224024 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1224025 {A : Type'} (a1 : list A) (R : type1402 A) : (term242 A a1 R) = (term333 A a1 R).
Proof. exact (MK_COMB (@lem1224024 A) (@lem1224023 A a1 R)). Qed.
Lemma lem1224027 {A B : Type'} (P : type1413 A B) : (term334 A B P) = (term335 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1224028 {A : Type'} (P : type1136 A) : (term336 A P) = (term337 A P).
Proof. exact (@lem1224027 (list A) A P). Qed.
Lemma lem1224029 {A : Type'} (a1 : list A) (R : type1402 A) : (term338 A a1 R) = (term339 A a1 R).
Proof. exact (@lem1224028 A (term340 A a1 R)). Qed.
Lemma lem1224030 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term341 A a1 R m) = (term330 A a1 m R).
Proof. exact (eq_refl (term341 A a1 R m)). Qed.
Lemma lem1224031 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1224032 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term342 A a1 R m x) = (term343 A a1 m R x).
Proof. exact (MK_COMB (@lem1224030 A a1 m R) (@lem1224031 A x)). Qed.
Lemma lem1224033 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term343 A a1 m R x) = (term329 A a1 m R x).
Proof. exact (eq_refl (term343 A a1 m R x)). Qed.
Lemma lem1224034 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term342 A a1 R m x) = (term329 A a1 m R x).
Proof. exact (TRANS (@lem1224032 A a1 m R x) (@lem1224033 A a1 m R x)). Qed.
Lemma lem1224035 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term344 A a1 R m) = (term330 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224034 A a1 m R x)). Qed.
Lemma lem1224036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224037 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term345 A a1 R m) = (term331 A a1 m R).
Proof. exact (MK_COMB (@lem1224036 A) (@lem1224035 A a1 m R)). Qed.
Lemma lem1224038 {A : Type'} (a1 : list A) (R : type1402 A) : (term346 A a1 R) = (term332 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1224037 A a1 m R)). Qed.
Lemma lem1224039 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1224040 {A : Type'} (a1 : list A) (R : type1402 A) : (term338 A a1 R) = (term333 A a1 R).
Proof. exact (MK_COMB (@lem1224039 A) (@lem1224038 A a1 R)). Qed.
Lemma lem1224041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224042 {A : Type'} (a1 : list A) (R : type1402 A) : (term347 A a1 R) = (term348 A a1 R).
Proof. exact (MK_COMB (@lem1224041) (@lem1224040 A a1 R)). Qed.
Lemma lem1224043 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term341 A a1 R m) = (term330 A a1 m R).
Proof. exact (eq_refl (term341 A a1 R m)). Qed.
Lemma lem1224044 {A : Type'} (x : type1141 A) (m : list A) : (x m) = (x m).
Proof. exact (eq_refl (x m)). Qed.
Lemma lem1224045 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term349 A a1 R x m) = (term350 A a1 R x m).
Proof. exact (MK_COMB (@lem1224043 A a1 m R) (@lem1224044 A x m)). Qed.
Lemma lem1224046 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term350 A a1 R x m) = (term351 A a1 R x m).
Proof. exact (eq_refl (term350 A a1 R x m)). Qed.
Lemma lem1224047 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term349 A a1 R x m) = (term351 A a1 R x m).
Proof. exact (TRANS (@lem1224045 A a1 R x m) (@lem1224046 A a1 R x m)). Qed.
Lemma lem1224048 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term352 A a1 R x) = (term353 A a1 R x).
Proof. exact (fun_ext (fun m : list A => @lem1224047 A a1 R x m)). Qed.
Lemma lem1224049 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1224050 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term354 A a1 R x) = (term355 A a1 R x).
Proof. exact (MK_COMB (@lem1224049 A) (@lem1224048 A a1 R x)). Qed.
Lemma lem1224051 {A : Type'} (a1 : list A) (R : type1402 A) : (term356 A a1 R) = (term357 A a1 R).
Proof. exact (fun_ext (fun x : type1141 A => @lem1224050 A a1 R x)). Qed.
Lemma lem1224052 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224053 {A : Type'} (a1 : list A) (R : type1402 A) : (term339 A a1 R) = (term358 A a1 R).
Proof. exact (MK_COMB (@lem1224052 A) (@lem1224051 A a1 R)). Qed.
Lemma lem1224054 {A : Type'} (a1 : list A) (R : type1402 A) : ((term338 A a1 R) = (term339 A a1 R)) = ((term333 A a1 R) = (term358 A a1 R)).
Proof. exact (MK_COMB (@lem1224042 A a1 R) (@lem1224053 A a1 R)). Qed.
Lemma lem1224055 {A : Type'} (a1 : list A) (R : type1402 A) : (term333 A a1 R) = (term358 A a1 R).
Proof. exact (EQ_MP (@lem1224054 A a1 R) (@lem1224029 A a1 R)). Qed.
Lemma lem1224057 {A B : Type'} (P : type1413 A B) : (term334 A B P) = (term335 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1224058 {A : Type'} (P : type1136 A) : (term336 A P) = (term337 A P).
Proof. exact (@lem1224057 (list A) A P). Qed.
Lemma lem1224059 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term359 A a1 R x) = (term360 A a1 R x).
Proof. exact (@lem1224058 A (term361 A a1 R x)). Qed.
Lemma lem1224060 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term362 A a1 R x m) = (term363 A a1 R x m).
Proof. exact (eq_refl (term362 A a1 R x m)). Qed.
Lemma lem1224061 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1224062 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) (y : A) : (term364 A a1 R x m y) = (term365 A a1 R x m y).
Proof. exact (MK_COMB (@lem1224060 A a1 R x m) (@lem1224061 A y)). Qed.
Lemma lem1224063 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) (y : A) : (term365 A a1 R x m y) = (term366 A a1 R x m y).
Proof. exact (eq_refl (term365 A a1 R x m y)). Qed.
Lemma lem1224064 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) (y : A) : (term364 A a1 R x m y) = (term366 A a1 R x m y).
Proof. exact (TRANS (@lem1224062 A a1 R x m y) (@lem1224063 A a1 R x m y)). Qed.
Lemma lem1224065 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term367 A a1 R x m) = (term363 A a1 R x m).
Proof. exact (fun_ext (fun y : A => @lem1224064 A a1 R x m y)). Qed.
Lemma lem1224066 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224067 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term368 A a1 R x m) = (term351 A a1 R x m).
Proof. exact (MK_COMB (@lem1224066 A) (@lem1224065 A a1 R x m)). Qed.
Lemma lem1224068 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term369 A a1 R x) = (term353 A a1 R x).
Proof. exact (fun_ext (fun m : list A => @lem1224067 A a1 R x m)). Qed.
Lemma lem1224069 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1224070 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term359 A a1 R x) = (term355 A a1 R x).
Proof. exact (MK_COMB (@lem1224069 A) (@lem1224068 A a1 R x)). Qed.
Lemma lem1224071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224072 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term370 A a1 R x) = (term371 A a1 R x).
Proof. exact (MK_COMB (@lem1224071) (@lem1224070 A a1 R x)). Qed.
Lemma lem1224073 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (m : list A) : (term362 A a1 R x m) = (term363 A a1 R x m).
Proof. exact (eq_refl (term362 A a1 R x m)). Qed.
Lemma lem1224074 {A : Type'} (y : type1141 A) (m : list A) : (y m) = (y m).
Proof. exact (eq_refl (y m)). Qed.
Lemma lem1224075 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) (m : list A) : (term372 A a1 R x y m) = (term373 A a1 R x y m).
Proof. exact (MK_COMB (@lem1224073 A a1 R x m) (@lem1224074 A y m)). Qed.
Lemma lem1224076 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) (m : list A) : (term373 A a1 R x y m) = (term374 A a1 R x y m).
Proof. exact (eq_refl (term373 A a1 R x y m)). Qed.
Lemma lem1224077 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) (m : list A) : (term372 A a1 R x y m) = (term374 A a1 R x y m).
Proof. exact (TRANS (@lem1224075 A a1 R x y m) (@lem1224076 A a1 R x y m)). Qed.
Lemma lem1224078 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) : (term375 A a1 R x y) = (term376 A a1 R x y).
Proof. exact (fun_ext (fun m : list A => @lem1224077 A a1 R x y m)). Qed.
Lemma lem1224079 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1224080 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) : (term377 A a1 R x y) = (term378 A a1 R x y).
Proof. exact (MK_COMB (@lem1224079 A) (@lem1224078 A a1 R x y)). Qed.
Lemma lem1224081 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term379 A a1 R x) = (term380 A a1 R x).
Proof. exact (fun_ext (fun y : type1141 A => @lem1224080 A a1 R x y)). Qed.
Lemma lem1224082 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224083 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term360 A a1 R x) = (term381 A a1 R x).
Proof. exact (MK_COMB (@lem1224082 A) (@lem1224081 A a1 R x)). Qed.
Lemma lem1224084 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : ((term359 A a1 R x) = (term360 A a1 R x)) = ((term355 A a1 R x) = (term381 A a1 R x)).
Proof. exact (MK_COMB (@lem1224072 A a1 R x) (@lem1224083 A a1 R x)). Qed.
Lemma lem1224085 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term355 A a1 R x) = (term381 A a1 R x).
Proof. exact (EQ_MP (@lem1224084 A a1 R x) (@lem1224059 A a1 R x)). Qed.
Lemma lem1224086 {A : Type'} (a1 : list A) (R : type1402 A) : (term357 A a1 R) = (term382 A a1 R).
Proof. exact (fun_ext (fun x : type1141 A => @lem1224085 A a1 R x)). Qed.
Lemma lem1224087 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224088 {A : Type'} (a1 : list A) (R : type1402 A) : (term358 A a1 R) = (term383 A a1 R).
Proof. exact (MK_COMB (@lem1224087 A) (@lem1224086 A a1 R)). Qed.
Lemma lem1224089 {A : Type'} (a1 : list A) (R : type1402 A) : (term333 A a1 R) = (term383 A a1 R).
Proof. exact (TRANS (@lem1224055 A a1 R) (@lem1224088 A a1 R)). Qed.
Lemma lem1224090 {A : Type'} (a1 : list A) (R : type1402 A) : (term242 A a1 R) = (term383 A a1 R).
Proof. exact (TRANS (@lem1224025 A a1 R) (@lem1224089 A a1 R)). Qed.
Lemma lem1224091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224092 {A : Type'} (a1 : list A) (R : type1402 A) : (term244 A a1 R) = (term384 A a1 R).
Proof. exact (MK_COMB (@lem1224091) (@lem1224090 A a1 R)). Qed.
Lemma lem1224093 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term247 A a1 R).
Proof. exact (eq_refl (term247 A a1 R)). Qed.
Lemma lem1224094 {A : Type'} (a1 : list A) (R : type1402 A) : (term248 A a1 R) = (term385 A a1 R).
Proof. exact (MK_COMB (@lem1224092 A a1 R) (@lem1224093 A a1 R)). Qed.
Lemma lem1224096 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1224097 {A : Type'} (P : type277 A) (Q : Prop) : (term388 A P Q) = (term389 A P Q).
Proof. exact (@lem1224096 (type1141 A) P Q). Qed.
Lemma lem1224098 {A : Type'} (a1 : list A) (R : type1402 A) : (term390 A a1 R) = (term391 A a1 R).
Proof. exact (@lem1224097 A (term382 A a1 R) (term247 A a1 R)). Qed.
Lemma lem1224099 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term392 A a1 R x) = (term381 A a1 R x).
Proof. exact (eq_refl (term392 A a1 R x)). Qed.
Lemma lem1224100 {A : Type'} (a1 : list A) (R : type1402 A) : (term393 A a1 R) = (term382 A a1 R).
Proof. exact (fun_ext (fun x : type1141 A => @lem1224099 A a1 R x)). Qed.
Lemma lem1224101 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224102 {A : Type'} (a1 : list A) (R : type1402 A) : (term394 A a1 R) = (term383 A a1 R).
Proof. exact (MK_COMB (@lem1224101 A) (@lem1224100 A a1 R)). Qed.
Lemma lem1224103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224104 {A : Type'} (a1 : list A) (R : type1402 A) : (term395 A a1 R) = (term384 A a1 R).
Proof. exact (MK_COMB (@lem1224103) (@lem1224102 A a1 R)). Qed.
Lemma lem1224105 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term247 A a1 R).
Proof. exact (eq_refl (term247 A a1 R)). Qed.
Lemma lem1224106 {A : Type'} (a1 : list A) (R : type1402 A) : (term390 A a1 R) = (term385 A a1 R).
Proof. exact (MK_COMB (@lem1224104 A a1 R) (@lem1224105 A a1 R)). Qed.
Lemma lem1224107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224108 {A : Type'} (a1 : list A) (R : type1402 A) : (term396 A a1 R) = (term397 A a1 R).
Proof. exact (MK_COMB (@lem1224107) (@lem1224106 A a1 R)). Qed.
Lemma lem1224109 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term392 A a1 R x) = (term381 A a1 R x).
Proof. exact (eq_refl (term392 A a1 R x)). Qed.
Lemma lem1224110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224111 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term398 A a1 R x) = (term399 A a1 R x).
Proof. exact (MK_COMB (@lem1224110) (@lem1224109 A a1 R x)). Qed.
Lemma lem1224112 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term247 A a1 R).
Proof. exact (eq_refl (term247 A a1 R)). Qed.
Lemma lem1224113 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term400 A x a1 R) = (term401 A x a1 R).
Proof. exact (MK_COMB (@lem1224111 A a1 R x) (@lem1224112 A a1 R)). Qed.
Lemma lem1224114 {A : Type'} (a1 : list A) (R : type1402 A) : (term402 A a1 R) = (term403 A a1 R).
Proof. exact (fun_ext (fun x : type1141 A => @lem1224113 A x a1 R)). Qed.
Lemma lem1224115 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224116 {A : Type'} (a1 : list A) (R : type1402 A) : (term391 A a1 R) = (term404 A a1 R).
Proof. exact (MK_COMB (@lem1224115 A) (@lem1224114 A a1 R)). Qed.
Lemma lem1224117 {A : Type'} (a1 : list A) (R : type1402 A) : ((term390 A a1 R) = (term391 A a1 R)) = ((term385 A a1 R) = (term404 A a1 R)).
Proof. exact (MK_COMB (@lem1224108 A a1 R) (@lem1224116 A a1 R)). Qed.
Lemma lem1224118 {A : Type'} (a1 : list A) (R : type1402 A) : (term385 A a1 R) = (term404 A a1 R).
Proof. exact (EQ_MP (@lem1224117 A a1 R) (@lem1224098 A a1 R)). Qed.
Lemma lem1224120 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1224121 {A : Type'} (P : type277 A) (Q : Prop) : (term388 A P Q) = (term389 A P Q).
Proof. exact (@lem1224120 (type1141 A) P Q). Qed.
Lemma lem1224122 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term405 A x a1 R) = (term406 A x a1 R).
Proof. exact (@lem1224121 A (term380 A a1 R x) (term247 A a1 R)). Qed.
Lemma lem1224123 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) : (term407 A a1 R x y) = (term378 A a1 R x y).
Proof. exact (eq_refl (term407 A a1 R x y)). Qed.
Lemma lem1224124 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term408 A a1 R x) = (term380 A a1 R x).
Proof. exact (fun_ext (fun y : type1141 A => @lem1224123 A a1 R x y)). Qed.
Lemma lem1224125 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224126 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term409 A a1 R x) = (term381 A a1 R x).
Proof. exact (MK_COMB (@lem1224125 A) (@lem1224124 A a1 R x)). Qed.
Lemma lem1224127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224128 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) : (term410 A a1 R x) = (term399 A a1 R x).
Proof. exact (MK_COMB (@lem1224127) (@lem1224126 A a1 R x)). Qed.
Lemma lem1224129 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term247 A a1 R).
Proof. exact (eq_refl (term247 A a1 R)). Qed.
Lemma lem1224130 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term405 A x a1 R) = (term401 A x a1 R).
Proof. exact (MK_COMB (@lem1224128 A a1 R x) (@lem1224129 A a1 R)). Qed.
Lemma lem1224131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224132 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term411 A x a1 R) = (term412 A x a1 R).
Proof. exact (MK_COMB (@lem1224131) (@lem1224130 A x a1 R)). Qed.
Lemma lem1224133 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) : (term407 A a1 R x y) = (term378 A a1 R x y).
Proof. exact (eq_refl (term407 A a1 R x y)). Qed.
Lemma lem1224134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224135 {A : Type'} (a1 : list A) (R : type1402 A) (x : type1141 A) (y : type1141 A) : (term413 A a1 R x y) = (term414 A a1 R x y).
Proof. exact (MK_COMB (@lem1224134) (@lem1224133 A a1 R x y)). Qed.
Lemma lem1224136 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term247 A a1 R).
Proof. exact (eq_refl (term247 A a1 R)). Qed.
Lemma lem1224137 {A : Type'} (x : type1141 A) (y : type1141 A) (a1 : list A) (R : type1402 A) : (term415 A x y a1 R) = (term416 A x y a1 R).
Proof. exact (MK_COMB (@lem1224135 A a1 R x y) (@lem1224136 A a1 R)). Qed.
Lemma lem1224138 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term417 A x a1 R) = (term418 A x a1 R).
Proof. exact (fun_ext (fun y : type1141 A => @lem1224137 A x y a1 R)). Qed.
Lemma lem1224139 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224140 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term406 A x a1 R) = (term419 A x a1 R).
Proof. exact (MK_COMB (@lem1224139 A) (@lem1224138 A x a1 R)). Qed.
Lemma lem1224141 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : ((term405 A x a1 R) = (term406 A x a1 R)) = ((term401 A x a1 R) = (term419 A x a1 R)).
Proof. exact (MK_COMB (@lem1224132 A x a1 R) (@lem1224140 A x a1 R)). Qed.
Lemma lem1224142 {A : Type'} (x : type1141 A) (a1 : list A) (R : type1402 A) : (term401 A x a1 R) = (term419 A x a1 R).
Proof. exact (EQ_MP (@lem1224141 A x a1 R) (@lem1224122 A x a1 R)). Qed.
Lemma lem1224143 {A : Type'} (a1 : list A) (R : type1402 A) : (term403 A a1 R) = (term420 A a1 R).
Proof. exact (fun_ext (fun x : type1141 A => @lem1224142 A x a1 R)). Qed.
Lemma lem1224144 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1224145 {A : Type'} (a1 : list A) (R : type1402 A) : (term404 A a1 R) = (term421 A a1 R).
Proof. exact (MK_COMB (@lem1224144 A) (@lem1224143 A a1 R)). Qed.
Lemma lem1224146 {A : Type'} (a1 : list A) (R : type1402 A) : (term385 A a1 R) = (term421 A a1 R).
Proof. exact (TRANS (@lem1224118 A a1 R) (@lem1224145 A a1 R)). Qed.
Lemma lem1224147 {A : Type'} (a1 : list A) (R : type1402 A) : (term248 A a1 R) = (term421 A a1 R).
Proof. exact (TRANS (@lem1224094 A a1 R) (@lem1224146 A a1 R)). Qed.
Lemma lem1224148 {A : Type'} (a1 : list A) (R : type1402 A) : (term224 A a1 R) = (term421 A a1 R).
Proof. exact (TRANS (@lem1223684 A a1 R) (@lem1224147 A a1 R)). Qed.
Lemma lem1224149 {A : Type'} (a1 : list A) (R : type1402 A) : (term49 A a1 R) = (term421 A a1 R).
Proof. exact (TRANS (@lem1223657 A a1 R) (@lem1224148 A a1 R)). Qed.
Lemma lem1224150 {A : Type'} (a1 : list A) (R : type1402 A) (h1 : term49 A a1 R) : term421 A a1 R.
Proof. exact (EQ_MP (@lem1224149 A a1 R) (@lem1223566 A a1 R h1)). Qed.
Lemma lem1224159 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term422 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (@lem17362 (@List.In A x a1) (R a0 x)). Qed.
Lemma lem1224164 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A a1 R a0 x) = (term424 A a1 R a0 x).
Proof. exact (@lem17265 (@List.In A x a1) (R a0 x)). Qed.
Lemma lem1224165 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1224166 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term425 A a1 R a0) = (term426 A a1 R a0).
Proof. exact (@lem1224165 A (term163 A a1 R a0)). Qed.
Lemma lem1224167 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term427 A a1 R a0 x) = (term162 A a1 R a0 x).
Proof. exact (eq_refl (term427 A a1 R a0 x)). Qed.
Lemma lem1224168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1224169 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A a1 R a0 x) = (term422 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1224168) (@lem1224167 A a1 R a0 x)). Qed.
Lemma lem1224170 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (TRANS (@lem1224169 A a1 R a0 x) (@lem1224159 A a1 R a0 x)). Qed.
Lemma lem1224171 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term429 A a1 R a0) = (term430 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224170 A a1 R a0 x)). Qed.
Lemma lem1224172 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224173 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term426 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (MK_COMB (@lem1224172 A) (@lem1224171 A a1 R a0)). Qed.
Lemma lem1224174 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term425 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (TRANS (@lem1224166 A a1 R a0) (@lem1224173 A a1 R a0)). Qed.
Lemma lem1224175 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term163 A a1 R a0) = (term432 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224164 A a1 R a0 x)). Qed.
Lemma lem1224176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1224177 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term106 A a1 R a0) = (term433 A a1 R a0).
Proof. exact (MK_COMB (@lem1224176 A) (@lem1224175 A a1 R a0)). Qed.
Lemma lem1224186 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term422 A m R a0 x) = (term423 A m R a0 x).
Proof. exact (@lem17362 (@List.In A x m) (R a0 x)). Qed.
Lemma lem1224191 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A m R a0 x) = (term424 A m R a0 x).
Proof. exact (@lem17265 (@List.In A x m) (R a0 x)). Qed.
Lemma lem1224192 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1224193 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term425 A m R a0) = (term426 A m R a0).
Proof. exact (@lem1224192 A (term163 A m R a0)). Qed.
Lemma lem1224194 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term427 A m R a0 x) = (term162 A m R a0 x).
Proof. exact (eq_refl (term427 A m R a0 x)). Qed.
Lemma lem1224195 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1224196 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A m R a0 x) = (term422 A m R a0 x).
Proof. exact (MK_COMB (@lem1224195) (@lem1224194 A m R a0 x)). Qed.
Lemma lem1224197 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A m R a0 x) = (term423 A m R a0 x).
Proof. exact (TRANS (@lem1224196 A m R a0 x) (@lem1224186 A m R a0 x)). Qed.
Lemma lem1224198 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term429 A m R a0) = (term430 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1224197 A m R a0 x)). Qed.
Lemma lem1224199 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224200 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term426 A m R a0) = (term431 A m R a0).
Proof. exact (MK_COMB (@lem1224199 A) (@lem1224198 A m R a0)). Qed.
Lemma lem1224201 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term425 A m R a0) = (term431 A m R a0).
Proof. exact (TRANS (@lem1224193 A m R a0) (@lem1224200 A m R a0)). Qed.
Lemma lem1224202 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term163 A m R a0) = (term432 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1224191 A m R a0 x)). Qed.
Lemma lem1224203 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1224204 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term106 A m R a0) = (term433 A m R a0).
Proof. exact (MK_COMB (@lem1224203 A) (@lem1224202 A m R a0)). Qed.
Lemma lem1224205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224206 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term434 A a1 R a0) = (term435 A a1 R a0).
Proof. exact (MK_COMB (@lem1224205) (@lem1224174 A a1 R a0)). Qed.
Lemma lem1224207 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term436 A a1 m R a0) = (term437 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224206 A a1 R a0) (@lem1224201 A m R a0)). Qed.
Lemma lem1224208 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term438 A a1 m R a0) = (term436 A a1 m R a0).
Proof. exact (@lem17045 (term106 A a1 R a0) (term106 A m R a0)). Qed.
Lemma lem1224209 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term438 A a1 m R a0) = (term437 A a1 m R a0).
Proof. exact (TRANS (@lem1224208 A a1 m R a0) (@lem1224207 A a1 m R a0)). Qed.
Lemma lem1224210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224211 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term108 A a1 R a0) = (term439 A a1 R a0).
Proof. exact (MK_COMB (@lem1224210) (@lem1224177 A a1 R a0)). Qed.
Lemma lem1224212 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term109 A a1 m R a0) = (term440 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224211 A a1 R a0) (@lem1224204 A m R a0)). Qed.
Lemma lem1224213 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term441 A R a1 m).
Proof. exact (eq_refl (term441 A R a1 m)). Qed.
Lemma lem1224214 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term112 A R a1 m) = (term112 A R a1 m).
Proof. exact (eq_refl (term112 A R a1 m)). Qed.
Lemma lem1224215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224216 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term442 A a1 m R a0) = (term443 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224215) (@lem1224209 A a1 m R a0)). Qed.
Lemma lem1224217 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term444 A a0 R a1 m) = (term445 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224216 A a1 m R a0) (@lem1224213 A R a1 m)). Qed.
Lemma lem1224218 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term446 A a0 R a1 m) = (term444 A a0 R a1 m).
Proof. exact (@lem17045 (term109 A a1 m R a0) (term112 A R a1 m)). Qed.
Lemma lem1224219 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term446 A a0 R a1 m) = (term445 A a0 R a1 m).
Proof. exact (TRANS (@lem1224218 A a0 R a1 m) (@lem1224217 A a0 R a1 m)). Qed.
Lemma lem1224220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224221 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term111 A a1 m R a0) = (term447 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224220) (@lem1224212 A a1 m R a0)). Qed.
Lemma lem1224222 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term113 A a0 R a1 m) = (term448 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224221 A a1 m R a0) (@lem1224214 A R a1 m)). Qed.
Lemma lem1224231 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term422 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (@lem17362 (@List.In A x a1) (R a0 x)). Qed.
Lemma lem1224236 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term162 A a1 R a0 x) = (term424 A a1 R a0 x).
Proof. exact (@lem17265 (@List.In A x a1) (R a0 x)). Qed.
Lemma lem1224237 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1224238 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term425 A a1 R a0) = (term426 A a1 R a0).
Proof. exact (@lem1224237 A (term163 A a1 R a0)). Qed.
Lemma lem1224239 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term427 A a1 R a0 x) = (term162 A a1 R a0 x).
Proof. exact (eq_refl (term427 A a1 R a0 x)). Qed.
Lemma lem1224240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1224241 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A a1 R a0 x) = (term422 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1224240) (@lem1224239 A a1 R a0 x)). Qed.
Lemma lem1224242 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term428 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (TRANS (@lem1224241 A a1 R a0 x) (@lem1224231 A a1 R a0 x)). Qed.
Lemma lem1224243 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term429 A a1 R a0) = (term430 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224242 A a1 R a0 x)). Qed.
Lemma lem1224244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224245 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term426 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (MK_COMB (@lem1224244 A) (@lem1224243 A a1 R a0)). Qed.
Lemma lem1224246 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term425 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (TRANS (@lem1224238 A a1 R a0) (@lem1224245 A a1 R a0)). Qed.
Lemma lem1224247 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term163 A a1 R a0) = (term432 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224236 A a1 R a0 x)). Qed.
Lemma lem1224248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1224249 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term106 A a1 R a0) = (term433 A a1 R a0).
Proof. exact (MK_COMB (@lem1224248 A) (@lem1224247 A a1 R a0)). Qed.
Lemma lem1224250 {A : Type'} (R : type1402 A) (a1 : list A) : (term253 A R a1) = (term253 A R a1).
Proof. exact (eq_refl (term253 A R a1)). Qed.
Lemma lem1224251 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1224252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224253 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term434 A a1 R a0) = (term435 A a1 R a0).
Proof. exact (MK_COMB (@lem1224252) (@lem1224246 A a1 R a0)). Qed.
Lemma lem1224254 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term449 A a0 R a1) = (term450 A a0 R a1).
Proof. exact (MK_COMB (@lem1224253 A a1 R a0) (@lem1224250 A R a1)). Qed.
Lemma lem1224255 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term451 A a0 R a1) = (term449 A a0 R a1).
Proof. exact (@lem17045 (term106 A a1 R a0) (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1224256 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term451 A a0 R a1) = (term450 A a0 R a1).
Proof. exact (TRANS (@lem1224255 A a0 R a1) (@lem1224254 A a0 R a1)). Qed.
Lemma lem1224257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224258 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term108 A a1 R a0) = (term439 A a1 R a0).
Proof. exact (MK_COMB (@lem1224257) (@lem1224249 A a1 R a0)). Qed.
Lemma lem1224259 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term116 A a0 R a1) = (term452 A a0 R a1).
Proof. exact (MK_COMB (@lem1224258 A a1 R a0) (@lem1224251 A R a1)). Qed.
Lemma lem1224270 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term453 A a0 x a1) = (term454 A a0 x a1).
Proof. exact (@lem17160 (x = a0) (@List.In A x a1)). Qed.
Lemma lem1224274 {A : Type'} (y : A) (m : list A) : (term455 A y m) = (term455 A y m).
Proof. exact (eq_refl (term455 A y m)). Qed.
Lemma lem1224276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224277 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term456 A a0 x a1) = (term457 A a0 x a1).
Proof. exact (MK_COMB (@lem1224276) (@lem1224270 A a0 x a1)). Qed.
Lemma lem1224278 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term458 A a0 x a1 y m) = (term459 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1224277 A a0 x a1) (@lem1224274 A y m)). Qed.
Lemma lem1224279 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term460 A a0 x a1 y m) = (term458 A a0 x a1 y m).
Proof. exact (@lem17045 (term120 A a0 x a1) (@List.In A y m)). Qed.
Lemma lem1224280 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term460 A a0 x a1 y m) = (term459 A a0 x a1 y m).
Proof. exact (TRANS (@lem1224279 A a0 x a1 y m) (@lem1224278 A a0 x a1 y m)). Qed.
Lemma lem1224285 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1224290 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term461 A a0 a1 m R x y) = (term462 A a0 a1 m R x y).
Proof. exact (@lem17362 (term124 A a0 x a1 y m) (R x y)). Qed.
Lemma lem1224291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224292 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term463 A a0 x a1 y m) = (term464 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1224291) (@lem1224280 A a0 x a1 y m)). Qed.
Lemma lem1224293 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term465 A a0 a1 m R x y) = (term466 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1224292 A a0 x a1 y m) (@lem1224285 A R x y)). Qed.
Lemma lem1224294 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term128 A a0 a1 m R x y) = (term465 A a0 a1 m R x y).
Proof. exact (@lem17265 (term124 A a0 x a1 y m) (R x y)). Qed.
Lemma lem1224295 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term128 A a0 a1 m R x y) = (term466 A a0 a1 m R x y).
Proof. exact (TRANS (@lem1224294 A a0 a1 m R x y) (@lem1224293 A a0 a1 m R x y)). Qed.
Lemma lem1224296 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1224297 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term467 A a0 a1 m R x) = (term468 A a0 a1 m R x).
Proof. exact (@lem1224296 A (term130 A a0 a1 m R x)). Qed.
Lemma lem1224298 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term469 A a0 a1 m R x y) = (term128 A a0 a1 m R x y).
Proof. exact (eq_refl (term469 A a0 a1 m R x y)). Qed.
Lemma lem1224299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1224300 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term470 A a0 a1 m R x y) = (term461 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1224299) (@lem1224298 A a0 a1 m R x y)). Qed.
Lemma lem1224301 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term470 A a0 a1 m R x y) = (term462 A a0 a1 m R x y).
Proof. exact (TRANS (@lem1224300 A a0 a1 m R x y) (@lem1224290 A a0 a1 m R x y)). Qed.
Lemma lem1224302 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term471 A a0 a1 m R x) = (term472 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224301 A a0 a1 m R x y)). Qed.
Lemma lem1224303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224304 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term468 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224303 A) (@lem1224302 A a0 a1 m R x)). Qed.
Lemma lem1224305 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term467 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (TRANS (@lem1224297 A a0 a1 m R x) (@lem1224304 A a0 a1 m R x)). Qed.
Lemma lem1224306 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term130 A a0 a1 m R x) = (term474 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224295 A a0 a1 m R x y)). Qed.
Lemma lem1224307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1224308 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term132 A a0 a1 m R x) = (term475 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224307 A) (@lem1224306 A a0 a1 m R x)). Qed.
Lemma lem1224309 {A : Type'} (P : A -> Prop) : (term184 A P) = (term185 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1224310 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term476 A a0 a1 m R) = (term477 A a0 a1 m R).
Proof. exact (@lem1224309 A (term134 A a0 a1 m R)). Qed.
Lemma lem1224311 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term478 A a0 a1 m R x) = (term132 A a0 a1 m R x).
Proof. exact (eq_refl (term478 A a0 a1 m R x)). Qed.
Lemma lem1224312 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1224313 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term479 A a0 a1 m R x) = (term467 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224312) (@lem1224311 A a0 a1 m R x)). Qed.
Lemma lem1224314 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term479 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (TRANS (@lem1224313 A a0 a1 m R x) (@lem1224305 A a0 a1 m R x)). Qed.
Lemma lem1224315 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term480 A a0 a1 m R) = (term481 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224314 A a0 a1 m R x)). Qed.
Lemma lem1224316 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224317 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term477 A a0 a1 m R) = (term482 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224316 A) (@lem1224315 A a0 a1 m R)). Qed.
Lemma lem1224318 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term476 A a0 a1 m R) = (term482 A a0 a1 m R).
Proof. exact (TRANS (@lem1224310 A a0 a1 m R) (@lem1224317 A a0 a1 m R)). Qed.
Lemma lem1224319 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term134 A a0 a1 m R) = (term483 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224308 A a0 a1 m R x)). Qed.
Lemma lem1224320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1224321 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term136 A a0 a1 m R) = (term484 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224320 A) (@lem1224319 A a0 a1 m R)). Qed.
Lemma lem1224323 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1224324 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term485 A a0 a1 m R) = (term486 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224323 A R m) (@lem1224318 A a0 a1 m R)). Qed.
Lemma lem1224325 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term487 A a0 a1 m R) = (term485 A a0 a1 m R).
Proof. exact (@lem17045 (@List.ForallOrdPairs A R m) (term136 A a0 a1 m R)). Qed.
Lemma lem1224326 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term487 A a0 a1 m R) = (term486 A a0 a1 m R).
Proof. exact (TRANS (@lem1224325 A a0 a1 m R) (@lem1224324 A a0 a1 m R)). Qed.
Lemma lem1224328 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1224329 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term138 A a0 a1 m R) = (term488 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224328 A R m) (@lem1224321 A a0 a1 m R)). Qed.
Lemma lem1224330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224331 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term489 A a0 R a1) = (term490 A a0 R a1).
Proof. exact (MK_COMB (@lem1224330) (@lem1224256 A a0 R a1)). Qed.
Lemma lem1224332 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term491 A a0 a1 m R) = (term492 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224331 A a0 R a1) (@lem1224326 A a0 a1 m R)). Qed.
Lemma lem1224333 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term493 A a0 a1 m R) = (term491 A a0 a1 m R).
Proof. exact (@lem17045 (term116 A a0 R a1) (term138 A a0 a1 m R)). Qed.
Lemma lem1224334 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term493 A a0 a1 m R) = (term492 A a0 a1 m R).
Proof. exact (TRANS (@lem1224333 A a0 a1 m R) (@lem1224332 A a0 a1 m R)). Qed.
Lemma lem1224335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224336 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term118 A a0 R a1) = (term494 A a0 R a1).
Proof. exact (MK_COMB (@lem1224335) (@lem1224259 A a0 R a1)). Qed.
Lemma lem1224337 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term140 A a0 a1 m R) = (term495 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224336 A a0 R a1) (@lem1224329 A a0 a1 m R)). Qed.
Lemma lem1224338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224339 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term496 A a0 R a1 m) = (term497 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224338) (@lem1224219 A a0 R a1 m)). Qed.
Lemma lem1224340 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term498 A a0 a1 m R) = (term499 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224339 A a0 R a1 m) (@lem1224337 A a0 a1 m R)). Qed.
Lemma lem1224341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224342 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term500 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224341) (@lem1224222 A a0 R a1 m)). Qed.
Lemma lem1224343 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term502 A a0 a1 m R) = (term503 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224342 A a0 R a1 m) (@lem1224334 A a0 a1 m R)). Qed.
Lemma lem1224344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224345 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term504 A a0 a1 m R) = (term505 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224344) (@lem1224343 A a0 a1 m R)). Qed.
Lemma lem1224346 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term506 A a0 a1 m R) = (term507 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224345 A a0 a1 m R) (@lem1224340 A a0 a1 m R)). Qed.
Lemma lem1224347 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term174 A a0 a1 m R) = (term506 A a0 a1 m R).
Proof. exact (@lem17646 (term113 A a0 R a1 m) (term140 A a0 a1 m R)). Qed.
Lemma lem1224348 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term174 A a0 a1 m R) = (term507 A a0 a1 m R).
Proof. exact (TRANS (@lem1224347 A a0 a1 m R) (@lem1224346 A a0 a1 m R)). Qed.
Lemma lem1224743 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1224744 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (@lem1224743 A P Q). Qed.
Lemma lem1224745 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term510 A a0 R a1) = (term511 A a0 R a1).
Proof. exact (@lem1224744 A (term430 A a1 R a0) (term253 A R a1)). Qed.
Lemma lem1224746 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (eq_refl (term512 A a1 R a0 x)). Qed.
Lemma lem1224747 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term513 A a1 R a0) = (term430 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224746 A a1 R a0 x)). Qed.
Lemma lem1224748 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224749 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term514 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (MK_COMB (@lem1224748 A) (@lem1224747 A a1 R a0)). Qed.
Lemma lem1224750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224751 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term515 A a1 R a0) = (term435 A a1 R a0).
Proof. exact (MK_COMB (@lem1224750) (@lem1224749 A a1 R a0)). Qed.
Lemma lem1224752 {A : Type'} (R : type1402 A) (a1 : list A) : (term253 A R a1) = (term253 A R a1).
Proof. exact (eq_refl (term253 A R a1)). Qed.
Lemma lem1224753 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term510 A a0 R a1) = (term450 A a0 R a1).
Proof. exact (MK_COMB (@lem1224751 A a1 R a0) (@lem1224752 A R a1)). Qed.
Lemma lem1224754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224755 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term516 A a0 R a1) = (term517 A a0 R a1).
Proof. exact (MK_COMB (@lem1224754) (@lem1224753 A a0 R a1)). Qed.
Lemma lem1224756 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (eq_refl (term512 A a1 R a0 x)). Qed.
Lemma lem1224757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224758 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term518 A a1 R a0 x) = (term519 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1224757) (@lem1224756 A a1 R a0 x)). Qed.
Lemma lem1224759 {A : Type'} (R : type1402 A) (a1 : list A) : (term253 A R a1) = (term253 A R a1).
Proof. exact (eq_refl (term253 A R a1)). Qed.
Lemma lem1224760 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term520 A a0 x R a1) = (term521 A a0 x R a1).
Proof. exact (MK_COMB (@lem1224758 A a1 R a0 x) (@lem1224759 A R a1)). Qed.
Lemma lem1224761 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term522 A a0 R a1) = (term523 A a0 R a1).
Proof. exact (fun_ext (fun x : A => @lem1224760 A a0 x R a1)). Qed.
Lemma lem1224762 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224763 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term511 A a0 R a1) = (term524 A a0 R a1).
Proof. exact (MK_COMB (@lem1224762 A) (@lem1224761 A a0 R a1)). Qed.
Lemma lem1224764 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : ((term510 A a0 R a1) = (term511 A a0 R a1)) = ((term450 A a0 R a1) = (term524 A a0 R a1)).
Proof. exact (MK_COMB (@lem1224755 A a0 R a1) (@lem1224763 A a0 R a1)). Qed.
Lemma lem1224765 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term450 A a0 R a1) = (term524 A a0 R a1).
Proof. exact (EQ_MP (@lem1224764 A a0 R a1) (@lem1224745 A a0 R a1)). Qed.
Lemma lem1224766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224767 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term490 A a0 R a1) = (term525 A a0 R a1).
Proof. exact (MK_COMB (@lem1224766) (@lem1224765 A a0 R a1)). Qed.
Lemma lem1224769 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1224770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1224769 A P Q). Qed.
Lemma lem1224771 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term526 A a0 a1 m R) = (term527 A a0 a1 m R).
Proof. exact (@lem1224770 A (term253 A R m) (term481 A a0 a1 m R)). Qed.
Lemma lem1224772 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term528 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (eq_refl (term528 A a0 a1 m R x)). Qed.
Lemma lem1224773 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term529 A a0 a1 m R) = (term481 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224772 A a0 a1 m R x)). Qed.
Lemma lem1224774 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224775 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term530 A a0 a1 m R) = (term482 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224774 A) (@lem1224773 A a0 a1 m R)). Qed.
Lemma lem1224776 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1224777 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term526 A a0 a1 m R) = (term486 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224776 A R m) (@lem1224775 A a0 a1 m R)). Qed.
Lemma lem1224778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224779 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term531 A a0 a1 m R) = (term532 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224778) (@lem1224777 A a0 a1 m R)). Qed.
Lemma lem1224780 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term528 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (eq_refl (term528 A a0 a1 m R x)). Qed.
Lemma lem1224781 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1224782 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term533 A a0 a1 m R x) = (term534 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224781 A R m) (@lem1224780 A a0 a1 m R x)). Qed.
Lemma lem1224783 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term535 A a0 a1 m R) = (term536 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224782 A a0 a1 m R x)). Qed.
Lemma lem1224784 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224785 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term527 A a0 a1 m R) = (term537 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224784 A) (@lem1224783 A a0 a1 m R)). Qed.
Lemma lem1224786 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term526 A a0 a1 m R) = (term527 A a0 a1 m R)) = ((term486 A a0 a1 m R) = (term537 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1224779 A a0 a1 m R) (@lem1224785 A a0 a1 m R)). Qed.
Lemma lem1224787 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term486 A a0 a1 m R) = (term537 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1224786 A a0 a1 m R) (@lem1224771 A a0 a1 m R)). Qed.
Lemma lem1224789 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1224790 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1224789 A P Q). Qed.
Lemma lem1224791 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term538 A a0 a1 m R x) = (term539 A a0 a1 m R x).
Proof. exact (@lem1224790 A (term253 A R m) (term472 A a0 a1 m R x)). Qed.
Lemma lem1224792 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term540 A a0 a1 m R x y) = (term462 A a0 a1 m R x y).
Proof. exact (eq_refl (term540 A a0 a1 m R x y)). Qed.
Lemma lem1224793 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term541 A a0 a1 m R x) = (term472 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224792 A a0 a1 m R x y)). Qed.
Lemma lem1224794 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224795 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term542 A a0 a1 m R x) = (term473 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224794 A) (@lem1224793 A a0 a1 m R x)). Qed.
Lemma lem1224796 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1224797 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term538 A a0 a1 m R x) = (term534 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224796 A R m) (@lem1224795 A a0 a1 m R x)). Qed.
Lemma lem1224798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224799 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term543 A a0 a1 m R x) = (term544 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224798) (@lem1224797 A a0 a1 m R x)). Qed.
Lemma lem1224800 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term540 A a0 a1 m R x y) = (term462 A a0 a1 m R x y).
Proof. exact (eq_refl (term540 A a0 a1 m R x y)). Qed.
Lemma lem1224801 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1224802 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term545 A a0 a1 m R x y) = (term546 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1224801 A R m) (@lem1224800 A a0 a1 m R x y)). Qed.
Lemma lem1224803 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term547 A a0 a1 m R x) = (term548 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224802 A a0 a1 m R x y)). Qed.
Lemma lem1224804 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224805 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term539 A a0 a1 m R x) = (term549 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224804 A) (@lem1224803 A a0 a1 m R x)). Qed.
Lemma lem1224806 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term538 A a0 a1 m R x) = (term539 A a0 a1 m R x)) = ((term534 A a0 a1 m R x) = (term549 A a0 a1 m R x)).
Proof. exact (MK_COMB (@lem1224799 A a0 a1 m R x) (@lem1224805 A a0 a1 m R x)). Qed.
Lemma lem1224807 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term534 A a0 a1 m R x) = (term549 A a0 a1 m R x).
Proof. exact (EQ_MP (@lem1224806 A a0 a1 m R x) (@lem1224791 A a0 a1 m R x)). Qed.
Lemma lem1224808 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term536 A a0 a1 m R) = (term550 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224807 A a0 a1 m R x)). Qed.
Lemma lem1224809 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224810 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term537 A a0 a1 m R) = (term551 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224809 A) (@lem1224808 A a0 a1 m R)). Qed.
Lemma lem1224811 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term486 A a0 a1 m R) = (term551 A a0 a1 m R).
Proof. exact (TRANS (@lem1224787 A a0 a1 m R) (@lem1224810 A a0 a1 m R)). Qed.
Lemma lem1224812 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term492 A a0 a1 m R) = (term552 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224767 A a0 R a1) (@lem1224811 A a0 a1 m R)). Qed.
Lemma lem1224814 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1224815 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (@lem1224814 A P Q). Qed.
Lemma lem1224816 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term555 A a0 a1 m R) = (term556 A a0 a1 m R).
Proof. exact (@lem1224815 A (term523 A a0 R a1) (term550 A a0 a1 m R)). Qed.
Lemma lem1224817 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term557 A a0 R a1 x) = (term521 A a0 x R a1).
Proof. exact (eq_refl (term557 A a0 R a1 x)). Qed.
Lemma lem1224818 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term558 A a0 R a1) = (term523 A a0 R a1).
Proof. exact (fun_ext (fun x : A => @lem1224817 A a0 x R a1)). Qed.
Lemma lem1224819 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224820 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term559 A a0 R a1) = (term524 A a0 R a1).
Proof. exact (MK_COMB (@lem1224819 A) (@lem1224818 A a0 R a1)). Qed.
Lemma lem1224821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224822 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term560 A a0 R a1) = (term525 A a0 R a1).
Proof. exact (MK_COMB (@lem1224821) (@lem1224820 A a0 R a1)). Qed.
Lemma lem1224823 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term561 A a0 a1 m R x) = (term549 A a0 a1 m R x).
Proof. exact (eq_refl (term561 A a0 a1 m R x)). Qed.
Lemma lem1224824 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term562 A a0 a1 m R) = (term550 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224823 A a0 a1 m R x)). Qed.
Lemma lem1224825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224826 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term563 A a0 a1 m R) = (term551 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224825 A) (@lem1224824 A a0 a1 m R)). Qed.
Lemma lem1224827 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term555 A a0 a1 m R) = (term552 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224822 A a0 R a1) (@lem1224826 A a0 a1 m R)). Qed.
Lemma lem1224828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224829 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term564 A a0 a1 m R) = (term565 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224828) (@lem1224827 A a0 a1 m R)). Qed.
Lemma lem1224830 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term557 A a0 R a1 x) = (term521 A a0 x R a1).
Proof. exact (eq_refl (term557 A a0 R a1 x)). Qed.
Lemma lem1224831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224832 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term566 A a0 R a1 x) = (term567 A a0 x R a1).
Proof. exact (MK_COMB (@lem1224831) (@lem1224830 A a0 x R a1)). Qed.
Lemma lem1224833 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term561 A a0 a1 m R x) = (term549 A a0 a1 m R x).
Proof. exact (eq_refl (term561 A a0 a1 m R x)). Qed.
Lemma lem1224834 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term568 A a0 a1 m R x) = (term569 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224832 A a0 x R a1) (@lem1224833 A a0 a1 m R x)). Qed.
Lemma lem1224835 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term570 A a0 a1 m R) = (term571 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224834 A a0 a1 m R x)). Qed.
Lemma lem1224836 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224837 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term556 A a0 a1 m R) = (term572 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224836 A) (@lem1224835 A a0 a1 m R)). Qed.
Lemma lem1224838 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term555 A a0 a1 m R) = (term556 A a0 a1 m R)) = ((term552 A a0 a1 m R) = (term572 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1224829 A a0 a1 m R) (@lem1224837 A a0 a1 m R)). Qed.
Lemma lem1224839 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term552 A a0 a1 m R) = (term572 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1224838 A a0 a1 m R) (@lem1224816 A a0 a1 m R)). Qed.
Lemma lem1224841 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1224842 {A : Type'} (P : Prop) (Q : A -> Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (@lem1224841 A P Q). Qed.
Lemma lem1224843 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term573 A a0 a1 m R x) = (term574 A a0 a1 m R x).
Proof. exact (@lem1224842 A (term521 A a0 x R a1) (term548 A a0 a1 m R x)). Qed.
Lemma lem1224844 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term575 A a0 a1 m R x y) = (term546 A a0 a1 m R x y).
Proof. exact (eq_refl (term575 A a0 a1 m R x y)). Qed.
Lemma lem1224845 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term576 A a0 a1 m R x) = (term548 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224844 A a0 a1 m R x y)). Qed.
Lemma lem1224846 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224847 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term577 A a0 a1 m R x) = (term549 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224846 A) (@lem1224845 A a0 a1 m R x)). Qed.
Lemma lem1224848 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term567 A a0 x R a1) = (term567 A a0 x R a1).
Proof. exact (eq_refl (term567 A a0 x R a1)). Qed.
Lemma lem1224849 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term573 A a0 a1 m R x) = (term569 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224848 A a0 x R a1) (@lem1224847 A a0 a1 m R x)). Qed.
Lemma lem1224850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224851 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term578 A a0 a1 m R x) = (term579 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224850) (@lem1224849 A a0 a1 m R x)). Qed.
Lemma lem1224852 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term575 A a0 a1 m R x y) = (term546 A a0 a1 m R x y).
Proof. exact (eq_refl (term575 A a0 a1 m R x y)). Qed.
Lemma lem1224853 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term567 A a0 x R a1) = (term567 A a0 x R a1).
Proof. exact (eq_refl (term567 A a0 x R a1)). Qed.
Lemma lem1224854 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term580 A a0 a1 m R x y) = (term581 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1224853 A a0 x R a1) (@lem1224852 A a0 a1 m R x y)). Qed.
Lemma lem1224855 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term582 A a0 a1 m R x) = (term583 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224854 A a0 a1 m R x y)). Qed.
Lemma lem1224856 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224857 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term574 A a0 a1 m R x) = (term584 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224856 A) (@lem1224855 A a0 a1 m R x)). Qed.
Lemma lem1224858 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term573 A a0 a1 m R x) = (term574 A a0 a1 m R x)) = ((term569 A a0 a1 m R x) = (term584 A a0 a1 m R x)).
Proof. exact (MK_COMB (@lem1224851 A a0 a1 m R x) (@lem1224857 A a0 a1 m R x)). Qed.
Lemma lem1224859 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term569 A a0 a1 m R x) = (term584 A a0 a1 m R x).
Proof. exact (EQ_MP (@lem1224858 A a0 a1 m R x) (@lem1224843 A a0 a1 m R x)). Qed.
Lemma lem1224860 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term571 A a0 a1 m R) = (term585 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224859 A a0 a1 m R x)). Qed.
Lemma lem1224861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224862 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term572 A a0 a1 m R) = (term586 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224861 A) (@lem1224860 A a0 a1 m R)). Qed.
Lemma lem1224863 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term552 A a0 a1 m R) = (term586 A a0 a1 m R).
Proof. exact (TRANS (@lem1224839 A a0 a1 m R) (@lem1224862 A a0 a1 m R)). Qed.
Lemma lem1224864 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term492 A a0 a1 m R) = (term586 A a0 a1 m R).
Proof. exact (TRANS (@lem1224812 A a0 a1 m R) (@lem1224863 A a0 a1 m R)). Qed.
Lemma lem1224865 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (eq_refl (term501 A a0 R a1 m)). Qed.
Lemma lem1224866 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term503 A a0 a1 m R) = (term587 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224865 A a0 R a1 m) (@lem1224864 A a0 a1 m R)). Qed.
Lemma lem1224868 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1224869 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (@lem1224868 A P Q). Qed.
Lemma lem1224870 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term590 A a0 a1 m R) = (term591 A a0 a1 m R).
Proof. exact (@lem1224869 A (term448 A a0 R a1 m) (term585 A a0 a1 m R)). Qed.
Lemma lem1224871 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term592 A a0 a1 m R x) = (term584 A a0 a1 m R x).
Proof. exact (eq_refl (term592 A a0 a1 m R x)). Qed.
Lemma lem1224872 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term593 A a0 a1 m R) = (term585 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224871 A a0 a1 m R x)). Qed.
Lemma lem1224873 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224874 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term594 A a0 a1 m R) = (term586 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224873 A) (@lem1224872 A a0 a1 m R)). Qed.
Lemma lem1224875 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (eq_refl (term501 A a0 R a1 m)). Qed.
Lemma lem1224876 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term590 A a0 a1 m R) = (term587 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224875 A a0 R a1 m) (@lem1224874 A a0 a1 m R)). Qed.
Lemma lem1224877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224878 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term595 A a0 a1 m R) = (term596 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224877) (@lem1224876 A a0 a1 m R)). Qed.
Lemma lem1224879 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term592 A a0 a1 m R x) = (term584 A a0 a1 m R x).
Proof. exact (eq_refl (term592 A a0 a1 m R x)). Qed.
Lemma lem1224880 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (eq_refl (term501 A a0 R a1 m)). Qed.
Lemma lem1224881 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term597 A a0 a1 m R x) = (term598 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224880 A a0 R a1 m) (@lem1224879 A a0 a1 m R x)). Qed.
Lemma lem1224882 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term599 A a0 a1 m R) = (term600 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224881 A a0 a1 m R x)). Qed.
Lemma lem1224883 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224884 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term591 A a0 a1 m R) = (term601 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224883 A) (@lem1224882 A a0 a1 m R)). Qed.
Lemma lem1224885 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term590 A a0 a1 m R) = (term591 A a0 a1 m R)) = ((term587 A a0 a1 m R) = (term601 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1224878 A a0 a1 m R) (@lem1224884 A a0 a1 m R)). Qed.
Lemma lem1224886 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term587 A a0 a1 m R) = (term601 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1224885 A a0 a1 m R) (@lem1224870 A a0 a1 m R)). Qed.
Lemma lem1224888 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1224889 {A : Type'} (P : Prop) (Q : A -> Prop) : (term588 A P Q) = (term589 A P Q).
Proof. exact (@lem1224888 A P Q). Qed.
Lemma lem1224890 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term602 A a0 a1 m R x) = (term603 A a0 a1 m R x).
Proof. exact (@lem1224889 A (term448 A a0 R a1 m) (term583 A a0 a1 m R x)). Qed.
Lemma lem1224891 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term604 A a0 a1 m R x y) = (term581 A a0 a1 m R x y).
Proof. exact (eq_refl (term604 A a0 a1 m R x y)). Qed.
Lemma lem1224892 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term605 A a0 a1 m R x) = (term583 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224891 A a0 a1 m R x y)). Qed.
Lemma lem1224893 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224894 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term606 A a0 a1 m R x) = (term584 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224893 A) (@lem1224892 A a0 a1 m R x)). Qed.
Lemma lem1224895 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (eq_refl (term501 A a0 R a1 m)). Qed.
Lemma lem1224896 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term602 A a0 a1 m R x) = (term598 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224895 A a0 R a1 m) (@lem1224894 A a0 a1 m R x)). Qed.
Lemma lem1224897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224898 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term607 A a0 a1 m R x) = (term608 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224897) (@lem1224896 A a0 a1 m R x)). Qed.
Lemma lem1224899 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term604 A a0 a1 m R x y) = (term581 A a0 a1 m R x y).
Proof. exact (eq_refl (term604 A a0 a1 m R x y)). Qed.
Lemma lem1224900 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term501 A a0 R a1 m).
Proof. exact (eq_refl (term501 A a0 R a1 m)). Qed.
Lemma lem1224901 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term609 A a0 a1 m R x y) = (term610 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1224900 A a0 R a1 m) (@lem1224899 A a0 a1 m R x y)). Qed.
Lemma lem1224902 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term611 A a0 a1 m R x) = (term612 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1224901 A a0 a1 m R x y)). Qed.
Lemma lem1224903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224904 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term603 A a0 a1 m R x) = (term613 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1224903 A) (@lem1224902 A a0 a1 m R x)). Qed.
Lemma lem1224905 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term602 A a0 a1 m R x) = (term603 A a0 a1 m R x)) = ((term598 A a0 a1 m R x) = (term613 A a0 a1 m R x)).
Proof. exact (MK_COMB (@lem1224898 A a0 a1 m R x) (@lem1224904 A a0 a1 m R x)). Qed.
Lemma lem1224906 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term598 A a0 a1 m R x) = (term613 A a0 a1 m R x).
Proof. exact (EQ_MP (@lem1224905 A a0 a1 m R x) (@lem1224890 A a0 a1 m R x)). Qed.
Lemma lem1224907 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term600 A a0 a1 m R) = (term614 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224906 A a0 a1 m R x)). Qed.
Lemma lem1224908 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224909 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term601 A a0 a1 m R) = (term615 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224908 A) (@lem1224907 A a0 a1 m R)). Qed.
Lemma lem1224910 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term587 A a0 a1 m R) = (term615 A a0 a1 m R).
Proof. exact (TRANS (@lem1224886 A a0 a1 m R) (@lem1224909 A a0 a1 m R)). Qed.
Lemma lem1224911 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term503 A a0 a1 m R) = (term615 A a0 a1 m R).
Proof. exact (TRANS (@lem1224866 A a0 a1 m R) (@lem1224910 A a0 a1 m R)). Qed.
Lemma lem1224912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224913 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term505 A a0 a1 m R) = (term616 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224912) (@lem1224911 A a0 a1 m R)). Qed.
Lemma lem1224915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1224916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (@lem1224915 A P Q). Qed.
Lemma lem1224917 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term617 A a1 m R a0) = (term618 A a1 m R a0).
Proof. exact (@lem1224916 A (term430 A a1 R a0) (term430 A m R a0)). Qed.
Lemma lem1224918 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (eq_refl (term512 A a1 R a0 x)). Qed.
Lemma lem1224919 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term513 A a1 R a0) = (term430 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1224918 A a1 R a0 x)). Qed.
Lemma lem1224920 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224921 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term514 A a1 R a0) = (term431 A a1 R a0).
Proof. exact (MK_COMB (@lem1224920 A) (@lem1224919 A a1 R a0)). Qed.
Lemma lem1224922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224923 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term515 A a1 R a0) = (term435 A a1 R a0).
Proof. exact (MK_COMB (@lem1224922) (@lem1224921 A a1 R a0)). Qed.
Lemma lem1224924 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A m R a0 x) = (term423 A m R a0 x).
Proof. exact (eq_refl (term512 A m R a0 x)). Qed.
Lemma lem1224925 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term513 A m R a0) = (term430 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1224924 A m R a0 x)). Qed.
Lemma lem1224926 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224927 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term514 A m R a0) = (term431 A m R a0).
Proof. exact (MK_COMB (@lem1224926 A) (@lem1224925 A m R a0)). Qed.
Lemma lem1224928 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term617 A a1 m R a0) = (term437 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224923 A a1 R a0) (@lem1224927 A m R a0)). Qed.
Lemma lem1224929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224930 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term619 A a1 m R a0) = (term620 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224929) (@lem1224928 A a1 m R a0)). Qed.
Lemma lem1224931 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A a1 R a0 x) = (term423 A a1 R a0 x).
Proof. exact (eq_refl (term512 A a1 R a0 x)). Qed.
Lemma lem1224932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224933 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term518 A a1 R a0 x) = (term519 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1224932) (@lem1224931 A a1 R a0 x)). Qed.
Lemma lem1224934 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term512 A m R a0 x) = (term423 A m R a0 x).
Proof. exact (eq_refl (term512 A m R a0 x)). Qed.
Lemma lem1224935 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term621 A a1 m R a0 x) = (term622 A a1 m R a0 x).
Proof. exact (MK_COMB (@lem1224933 A a1 R a0 x) (@lem1224934 A m R a0 x)). Qed.
Lemma lem1224936 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term623 A a1 m R a0) = (term624 A a1 m R a0).
Proof. exact (fun_ext (fun x : A => @lem1224935 A a1 m R a0 x)). Qed.
Lemma lem1224937 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224938 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term618 A a1 m R a0) = (term625 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224937 A) (@lem1224936 A a1 m R a0)). Qed.
Lemma lem1224939 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : ((term617 A a1 m R a0) = (term618 A a1 m R a0)) = ((term437 A a1 m R a0) = (term625 A a1 m R a0)).
Proof. exact (MK_COMB (@lem1224930 A a1 m R a0) (@lem1224938 A a1 m R a0)). Qed.
Lemma lem1224940 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term437 A a1 m R a0) = (term625 A a1 m R a0).
Proof. exact (EQ_MP (@lem1224939 A a1 m R a0) (@lem1224917 A a1 m R a0)). Qed.
Lemma lem1224941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224942 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term443 A a1 m R a0) = (term626 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224941) (@lem1224940 A a1 m R a0)). Qed.
Lemma lem1224943 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term441 A R a1 m).
Proof. exact (eq_refl (term441 A R a1 m)). Qed.
Lemma lem1224944 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term445 A a0 R a1 m) = (term627 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224942 A a1 m R a0) (@lem1224943 A R a1 m)). Qed.
Lemma lem1224946 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1224947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (@lem1224946 A P Q). Qed.
Lemma lem1224948 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term628 A a0 R a1 m) = (term629 A a0 R a1 m).
Proof. exact (@lem1224947 A (term624 A a1 m R a0) (term441 A R a1 m)). Qed.
Lemma lem1224949 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term630 A a1 m R a0 x) = (term622 A a1 m R a0 x).
Proof. exact (eq_refl (term630 A a1 m R a0 x)). Qed.
Lemma lem1224950 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term631 A a1 m R a0) = (term624 A a1 m R a0).
Proof. exact (fun_ext (fun x : A => @lem1224949 A a1 m R a0 x)). Qed.
Lemma lem1224951 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224952 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term632 A a1 m R a0) = (term625 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224951 A) (@lem1224950 A a1 m R a0)). Qed.
Lemma lem1224953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224954 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term633 A a1 m R a0) = (term626 A a1 m R a0).
Proof. exact (MK_COMB (@lem1224953) (@lem1224952 A a1 m R a0)). Qed.
Lemma lem1224955 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term441 A R a1 m).
Proof. exact (eq_refl (term441 A R a1 m)). Qed.
Lemma lem1224956 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term628 A a0 R a1 m) = (term627 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224954 A a1 m R a0) (@lem1224955 A R a1 m)). Qed.
Lemma lem1224957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224958 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term634 A a0 R a1 m) = (term635 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224957) (@lem1224956 A a0 R a1 m)). Qed.
Lemma lem1224959 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term630 A a1 m R a0 x) = (term622 A a1 m R a0 x).
Proof. exact (eq_refl (term630 A a1 m R a0 x)). Qed.
Lemma lem1224960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1224961 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term636 A a1 m R a0 x) = (term637 A a1 m R a0 x).
Proof. exact (MK_COMB (@lem1224960) (@lem1224959 A a1 m R a0 x)). Qed.
Lemma lem1224962 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term441 A R a1 m).
Proof. exact (eq_refl (term441 A R a1 m)). Qed.
Lemma lem1224963 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term638 A a0 x R a1 m) = (term639 A a0 x R a1 m).
Proof. exact (MK_COMB (@lem1224961 A a1 m R a0 x) (@lem1224962 A R a1 m)). Qed.
Lemma lem1224964 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term640 A a0 R a1 m) = (term641 A a0 R a1 m).
Proof. exact (fun_ext (fun x : A => @lem1224963 A a0 x R a1 m)). Qed.
Lemma lem1224965 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224966 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term629 A a0 R a1 m) = (term642 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224965 A) (@lem1224964 A a0 R a1 m)). Qed.
Lemma lem1224967 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : ((term628 A a0 R a1 m) = (term629 A a0 R a1 m)) = ((term627 A a0 R a1 m) = (term642 A a0 R a1 m)).
Proof. exact (MK_COMB (@lem1224958 A a0 R a1 m) (@lem1224966 A a0 R a1 m)). Qed.
Lemma lem1224968 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term627 A a0 R a1 m) = (term642 A a0 R a1 m).
Proof. exact (EQ_MP (@lem1224967 A a0 R a1 m) (@lem1224948 A a0 R a1 m)). Qed.
Lemma lem1224969 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term445 A a0 R a1 m) = (term642 A a0 R a1 m).
Proof. exact (TRANS (@lem1224944 A a0 R a1 m) (@lem1224968 A a0 R a1 m)). Qed.
Lemma lem1224970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224971 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term497 A a0 R a1 m) = (term643 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224970) (@lem1224969 A a0 R a1 m)). Qed.
Lemma lem1224972 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term495 A a0 a1 m R) = (term495 A a0 a1 m R).
Proof. exact (eq_refl (term495 A a0 a1 m R)). Qed.
Lemma lem1224973 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term499 A a0 a1 m R) = (term644 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224971 A a0 R a1 m) (@lem1224972 A a0 a1 m R)). Qed.
Lemma lem1224975 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1224976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (@lem1224975 A P Q). Qed.
Lemma lem1224977 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term645 A a0 a1 m R) = (term646 A a0 a1 m R).
Proof. exact (@lem1224976 A (term641 A a0 R a1 m) (term495 A a0 a1 m R)). Qed.
Lemma lem1224978 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term647 A a0 R a1 m x) = (term639 A a0 x R a1 m).
Proof. exact (eq_refl (term647 A a0 R a1 m x)). Qed.
Lemma lem1224979 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term648 A a0 R a1 m) = (term641 A a0 R a1 m).
Proof. exact (fun_ext (fun x : A => @lem1224978 A a0 x R a1 m)). Qed.
Lemma lem1224980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224981 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term649 A a0 R a1 m) = (term642 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224980 A) (@lem1224979 A a0 R a1 m)). Qed.
Lemma lem1224982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224983 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term650 A a0 R a1 m) = (term643 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1224982) (@lem1224981 A a0 R a1 m)). Qed.
Lemma lem1224984 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term495 A a0 a1 m R) = (term495 A a0 a1 m R).
Proof. exact (eq_refl (term495 A a0 a1 m R)). Qed.
Lemma lem1224985 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term645 A a0 a1 m R) = (term644 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224983 A a0 R a1 m) (@lem1224984 A a0 a1 m R)). Qed.
Lemma lem1224986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1224987 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term651 A a0 a1 m R) = (term652 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224986) (@lem1224985 A a0 a1 m R)). Qed.
Lemma lem1224988 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term647 A a0 R a1 m x) = (term639 A a0 x R a1 m).
Proof. exact (eq_refl (term647 A a0 R a1 m x)). Qed.
Lemma lem1224989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1224990 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term653 A a0 R a1 m x) = (term654 A a0 x R a1 m).
Proof. exact (MK_COMB (@lem1224989) (@lem1224988 A a0 x R a1 m)). Qed.
Lemma lem1224991 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term495 A a0 a1 m R) = (term495 A a0 a1 m R).
Proof. exact (eq_refl (term495 A a0 a1 m R)). Qed.
Lemma lem1224992 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term655 A x a0 a1 m R) = (term656 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1224990 A a0 x R a1 m) (@lem1224991 A a0 a1 m R)). Qed.
Lemma lem1224993 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term657 A a0 a1 m R) = (term658 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1224992 A x a0 a1 m R)). Qed.
Lemma lem1224994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1224995 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term646 A a0 a1 m R) = (term659 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224994 A) (@lem1224993 A a0 a1 m R)). Qed.
Lemma lem1224996 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term645 A a0 a1 m R) = (term646 A a0 a1 m R)) = ((term644 A a0 a1 m R) = (term659 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1224987 A a0 a1 m R) (@lem1224995 A a0 a1 m R)). Qed.
Lemma lem1224997 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term644 A a0 a1 m R) = (term659 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1224996 A a0 a1 m R) (@lem1224977 A a0 a1 m R)). Qed.
Lemma lem1224998 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term499 A a0 a1 m R) = (term659 A a0 a1 m R).
Proof. exact (TRANS (@lem1224973 A a0 a1 m R) (@lem1224997 A a0 a1 m R)). Qed.
Lemma lem1224999 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term507 A a0 a1 m R) = (term660 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1224913 A a0 a1 m R) (@lem1224998 A a0 a1 m R)). Qed.
Lemma lem1225001 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1225002 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (@lem1225001 A P Q). Qed.
Lemma lem1225003 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term661 A a0 a1 m R) = (term662 A a0 a1 m R).
Proof. exact (@lem1225002 A (term614 A a0 a1 m R) (term658 A a0 a1 m R)). Qed.
Lemma lem1225004 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term663 A a0 a1 m R x) = (term613 A a0 a1 m R x).
Proof. exact (eq_refl (term663 A a0 a1 m R x)). Qed.
Lemma lem1225005 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term664 A a0 a1 m R) = (term614 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225004 A a0 a1 m R x)). Qed.
Lemma lem1225006 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225007 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term665 A a0 a1 m R) = (term615 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225006 A) (@lem1225005 A a0 a1 m R)). Qed.
Lemma lem1225008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225009 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term666 A a0 a1 m R) = (term616 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225008) (@lem1225007 A a0 a1 m R)). Qed.
Lemma lem1225010 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term667 A a0 a1 m R x) = (term656 A x a0 a1 m R).
Proof. exact (eq_refl (term667 A a0 a1 m R x)). Qed.
Lemma lem1225011 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term668 A a0 a1 m R) = (term658 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225010 A x a0 a1 m R)). Qed.
Lemma lem1225012 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225013 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term669 A a0 a1 m R) = (term659 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225012 A) (@lem1225011 A a0 a1 m R)). Qed.
Lemma lem1225014 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term661 A a0 a1 m R) = (term660 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225009 A a0 a1 m R) (@lem1225013 A a0 a1 m R)). Qed.
Lemma lem1225015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1225016 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term670 A a0 a1 m R) = (term671 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225015) (@lem1225014 A a0 a1 m R)). Qed.
Lemma lem1225017 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term663 A a0 a1 m R x) = (term613 A a0 a1 m R x).
Proof. exact (eq_refl (term663 A a0 a1 m R x)). Qed.
Lemma lem1225018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225019 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term672 A a0 a1 m R x) = (term673 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1225018) (@lem1225017 A a0 a1 m R x)). Qed.
Lemma lem1225020 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term667 A a0 a1 m R x) = (term656 A x a0 a1 m R).
Proof. exact (eq_refl (term667 A a0 a1 m R x)). Qed.
Lemma lem1225021 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term674 A a0 a1 m R x) = (term675 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225019 A a0 a1 m R x) (@lem1225020 A x a0 a1 m R)). Qed.
Lemma lem1225022 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term676 A a0 a1 m R) = (term677 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225021 A x a0 a1 m R)). Qed.
Lemma lem1225023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225024 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term662 A a0 a1 m R) = (term678 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225023 A) (@lem1225022 A a0 a1 m R)). Qed.
Lemma lem1225025 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term661 A a0 a1 m R) = (term662 A a0 a1 m R)) = ((term660 A a0 a1 m R) = (term678 A a0 a1 m R)).
Proof. exact (MK_COMB (@lem1225016 A a0 a1 m R) (@lem1225024 A a0 a1 m R)). Qed.
Lemma lem1225026 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term660 A a0 a1 m R) = (term678 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1225025 A a0 a1 m R) (@lem1225003 A a0 a1 m R)). Qed.
Lemma lem1225028 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1225029 {A : Type'} (P : A -> Prop) (Q : Prop) : (term508 A P Q) = (term509 A P Q).
Proof. exact (@lem1225028 A P Q). Qed.
Lemma lem1225030 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term679 A x a0 a1 m R) = (term680 A x a0 a1 m R).
Proof. exact (@lem1225029 A (term612 A a0 a1 m R x) (term656 A x a0 a1 m R)). Qed.
Lemma lem1225031 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term681 A a0 a1 m R x y) = (term610 A a0 a1 m R x y).
Proof. exact (eq_refl (term681 A a0 a1 m R x y)). Qed.
Lemma lem1225032 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term682 A a0 a1 m R x) = (term612 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1225031 A a0 a1 m R x y)). Qed.
Lemma lem1225033 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225034 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term683 A a0 a1 m R x) = (term613 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1225033 A) (@lem1225032 A a0 a1 m R x)). Qed.
Lemma lem1225035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225036 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term684 A a0 a1 m R x) = (term673 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1225035) (@lem1225034 A a0 a1 m R x)). Qed.
Lemma lem1225037 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term656 A x a0 a1 m R) = (term656 A x a0 a1 m R).
Proof. exact (eq_refl (term656 A x a0 a1 m R)). Qed.
Lemma lem1225038 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term679 A x a0 a1 m R) = (term675 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225036 A a0 a1 m R x) (@lem1225037 A x a0 a1 m R)). Qed.
Lemma lem1225039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1225040 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term685 A x a0 a1 m R) = (term686 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225039) (@lem1225038 A x a0 a1 m R)). Qed.
Lemma lem1225041 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term681 A a0 a1 m R x y) = (term610 A a0 a1 m R x y).
Proof. exact (eq_refl (term681 A a0 a1 m R x y)). Qed.
Lemma lem1225042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225043 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term687 A a0 a1 m R x y) = (term688 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225042) (@lem1225041 A a0 a1 m R x y)). Qed.
Lemma lem1225044 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term656 A x a0 a1 m R) = (term656 A x a0 a1 m R).
Proof. exact (eq_refl (term656 A x a0 a1 m R)). Qed.
Lemma lem1225045 {A : Type'} (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term689 A y x a0 a1 m R) = (term690 A y x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225043 A a0 a1 m R x y) (@lem1225044 A x a0 a1 m R)). Qed.
Lemma lem1225046 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term691 A x a0 a1 m R) = (term692 A x a0 a1 m R).
Proof. exact (fun_ext (fun y : A => @lem1225045 A y x a0 a1 m R)). Qed.
Lemma lem1225047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225048 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term680 A x a0 a1 m R) = (term693 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225047 A) (@lem1225046 A x a0 a1 m R)). Qed.
Lemma lem1225049 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : ((term679 A x a0 a1 m R) = (term680 A x a0 a1 m R)) = ((term675 A x a0 a1 m R) = (term693 A x a0 a1 m R)).
Proof. exact (MK_COMB (@lem1225040 A x a0 a1 m R) (@lem1225048 A x a0 a1 m R)). Qed.
Lemma lem1225050 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term675 A x a0 a1 m R) = (term693 A x a0 a1 m R).
Proof. exact (EQ_MP (@lem1225049 A x a0 a1 m R) (@lem1225030 A x a0 a1 m R)). Qed.
Lemma lem1225051 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term677 A a0 a1 m R) = (term694 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225050 A x a0 a1 m R)). Qed.
Lemma lem1225052 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1225053 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term678 A a0 a1 m R) = (term695 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225052 A) (@lem1225051 A a0 a1 m R)). Qed.
Lemma lem1225054 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term660 A a0 a1 m R) = (term695 A a0 a1 m R).
Proof. exact (TRANS (@lem1225026 A a0 a1 m R) (@lem1225053 A a0 a1 m R)). Qed.
Lemma lem1225056 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term507 A a0 a1 m R) = (term695 A a0 a1 m R).
Proof. exact (TRANS (@lem1224999 A a0 a1 m R) (@lem1225054 A a0 a1 m R)). Qed.
Lemma lem1225057 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term174 A a0 a1 m R) = (term695 A a0 a1 m R).
Proof. exact (TRANS (@lem1224348 A a0 a1 m R) (@lem1225056 A a0 a1 m R)). Qed.
Lemma lem1225058 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term174 A a0 a1 m R) : term695 A a0 a1 m R.
Proof. exact (EQ_MP (@lem1225057 A a0 a1 m R) (@lem1223571 A a0 a1 m R h1)). Qed.
Lemma lem1225059 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term693 A x a0 a1 m R) : term693 A x a0 a1 m R.
Proof. exact (h1). Qed.
Lemma lem1225060 {A : Type'} (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term690 A y x a0 a1 m R) : term690 A y x a0 a1 m R.
Proof. exact (h1). Qed.
Lemma lem1225061 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term419 A x' a1 R) : term419 A x' a1 R.
Proof. exact (h1). Qed.
Lemma lem1225062 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term416 A x' y' a1 R.
Proof. exact (h1). Qed.
Lemma lem1225069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225070 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225069 A (A -> Prop) f x). Qed.
Lemma lem1225071 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1225070 A R x). Qed.
Lemma lem1225072 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1225073 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1225071 A R x) (@lem1225072 A y)). Qed.
Lemma lem1225075 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225076 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225075 A Prop f x). Qed.
Lemma lem1225077 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term696 A R x y).
Proof. exact (@lem1225076 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1225079 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term696 A R x y).
Proof. exact (TRANS (@lem1225073 A R x y) (@lem1225077 A R x y)). Qed.
Lemma lem1225108 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term464 A a0 x a1 y m) = (term464 A a0 x a1 y m).
Proof. exact (eq_refl (term464 A a0 x a1 y m)). Qed.
Lemma lem1225109 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term466 A a0 a1 m R x y) = (term697 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225108 A a0 x a1 y m) (@lem1225079 A R x y)). Qed.
Lemma lem1225110 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term474 A a0 a1 m R x) = (term698 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1225109 A a0 a1 m R x y)). Qed.
Lemma lem1225111 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225112 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term475 A a0 a1 m R x) = (term699 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1225111 A) (@lem1225110 A a0 a1 m R x)). Qed.
Lemma lem1225113 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term483 A a0 a1 m R) = (term700 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225112 A a0 a1 m R x)). Qed.
Lemma lem1225114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225115 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term484 A a0 a1 m R) = (term701 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225114 A) (@lem1225113 A a0 a1 m R)). Qed.
Lemma lem1225122 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1225123 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term488 A a0 a1 m R) = (term702 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225122 A R m) (@lem1225115 A a0 a1 m R)). Qed.
Lemma lem1225128 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1225135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225136 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225135 A (A -> Prop) f x). Qed.
Lemma lem1225137 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225136 A R a0). Qed.
Lemma lem1225138 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225139 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225137 A R a0) (@lem1225138 A x)). Qed.
Lemma lem1225141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225142 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225141 A Prop f x). Qed.
Lemma lem1225143 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225142 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225145 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225139 A R a0 x) (@lem1225143 A R a0 x)). Qed.
Lemma lem1225154 {A : Type'} (x : A) (a1 : list A) : (term703 A x a1) = (term703 A x a1).
Proof. exact (eq_refl (term703 A x a1)). Qed.
Lemma lem1225155 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term424 A a1 R a0 x) = (term704 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225154 A x a1) (@lem1225145 A R a0 x)). Qed.
Lemma lem1225156 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term432 A a1 R a0) = (term705 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1225155 A a1 R a0 x)). Qed.
Lemma lem1225157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225158 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term433 A a1 R a0) = (term706 A a1 R a0).
Proof. exact (MK_COMB (@lem1225157 A) (@lem1225156 A a1 R a0)). Qed.
Lemma lem1225159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225160 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term439 A a1 R a0) = (term707 A a1 R a0).
Proof. exact (MK_COMB (@lem1225159) (@lem1225158 A a1 R a0)). Qed.
Lemma lem1225161 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term452 A a0 R a1) = (term708 A a0 R a1).
Proof. exact (MK_COMB (@lem1225160 A a1 R a0) (@lem1225128 A R a1)). Qed.
Lemma lem1225162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225163 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term494 A a0 R a1) = (term709 A a0 R a1).
Proof. exact (MK_COMB (@lem1225162) (@lem1225161 A a0 R a1)). Qed.
Lemma lem1225164 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term495 A a0 a1 m R) = (term710 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1225163 A a0 R a1) (@lem1225123 A a0 a1 m R)). Qed.
Lemma lem1225175 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term441 A R a1 m).
Proof. exact (eq_refl (term441 A R a1 m)). Qed.
Lemma lem1225176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1225183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225184 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225183 A (A -> Prop) f x). Qed.
Lemma lem1225185 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225184 A R a0). Qed.
Lemma lem1225186 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225187 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225185 A R a0) (@lem1225186 A x)). Qed.
Lemma lem1225189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225190 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225189 A Prop f x). Qed.
Lemma lem1225191 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225190 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225193 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225187 A R a0 x) (@lem1225191 A R a0 x)). Qed.
Lemma lem1225194 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term711 A R a0 x) = (term712 A R a0 x).
Proof. exact (MK_COMB (@lem1225176) (@lem1225193 A R a0 x)). Qed.
Lemma lem1225201 {A : Type'} (x : A) (m : list A) : (term713 A x m) = (term713 A x m).
Proof. exact (eq_refl (term713 A x m)). Qed.
Lemma lem1225202 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term423 A m R a0 x) = (term714 A m R a0 x).
Proof. exact (MK_COMB (@lem1225201 A x m) (@lem1225194 A R a0 x)). Qed.
Lemma lem1225203 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1225210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225211 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225210 A (A -> Prop) f x). Qed.
Lemma lem1225212 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225211 A R a0). Qed.
Lemma lem1225213 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225214 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225212 A R a0) (@lem1225213 A x)). Qed.
Lemma lem1225216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225217 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225216 A Prop f x). Qed.
Lemma lem1225218 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225217 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225220 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225214 A R a0 x) (@lem1225218 A R a0 x)). Qed.
Lemma lem1225221 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term711 A R a0 x) = (term712 A R a0 x).
Proof. exact (MK_COMB (@lem1225203) (@lem1225220 A R a0 x)). Qed.
Lemma lem1225228 {A : Type'} (x : A) (a1 : list A) : (term713 A x a1) = (term713 A x a1).
Proof. exact (eq_refl (term713 A x a1)). Qed.
Lemma lem1225229 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term423 A a1 R a0 x) = (term714 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225228 A x a1) (@lem1225221 A R a0 x)). Qed.
Lemma lem1225230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225231 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term519 A a1 R a0 x) = (term715 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225230) (@lem1225229 A a1 R a0 x)). Qed.
Lemma lem1225232 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term622 A a1 m R a0 x) = (term716 A a1 m R a0 x).
Proof. exact (MK_COMB (@lem1225231 A a1 R a0 x) (@lem1225202 A m R a0 x)). Qed.
Lemma lem1225233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225234 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term637 A a1 m R a0 x) = (term717 A a1 m R a0 x).
Proof. exact (MK_COMB (@lem1225233) (@lem1225232 A a1 m R a0 x)). Qed.
Lemma lem1225235 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term639 A a0 x R a1 m) = (term718 A a0 x R a1 m).
Proof. exact (MK_COMB (@lem1225234 A a1 m R a0 x) (@lem1225175 A R a1 m)). Qed.
Lemma lem1225236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225237 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (m : list A) : (term654 A a0 x R a1 m) = (term719 A a0 x R a1 m).
Proof. exact (MK_COMB (@lem1225236) (@lem1225235 A a0 x R a1 m)). Qed.
Lemma lem1225238 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term656 A x a0 a1 m R) = (term720 A x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225237 A a0 x R a1 m) (@lem1225164 A a0 a1 m R)). Qed.
Lemma lem1225239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1225246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225247 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225246 A (A -> Prop) f x). Qed.
Lemma lem1225248 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1225247 A R x). Qed.
Lemma lem1225249 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1225250 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1225248 A R x) (@lem1225249 A y)). Qed.
Lemma lem1225252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225253 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225252 A Prop f x). Qed.
Lemma lem1225254 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term696 A R x y).
Proof. exact (@lem1225253 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1225256 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term696 A R x y).
Proof. exact (TRANS (@lem1225250 A R x y) (@lem1225254 A R x y)). Qed.
Lemma lem1225257 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term711 A R x y) = (term712 A R x y).
Proof. exact (MK_COMB (@lem1225239) (@lem1225256 A R x y)). Qed.
Lemma lem1225280 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term721 A a0 x a1 y m) = (term721 A a0 x a1 y m).
Proof. exact (eq_refl (term721 A a0 x a1 y m)). Qed.
Lemma lem1225281 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term462 A a0 a1 m R x y) = (term722 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225280 A a0 x a1 y m) (@lem1225257 A R x y)). Qed.
Lemma lem1225290 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1225291 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term546 A a0 a1 m R x y) = (term723 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225290 A R m) (@lem1225281 A a0 a1 m R x y)). Qed.
Lemma lem1225298 {A : Type'} (R : type1402 A) (a1 : list A) : (term253 A R a1) = (term253 A R a1).
Proof. exact (eq_refl (term253 A R a1)). Qed.
Lemma lem1225299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1225306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225307 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225306 A (A -> Prop) f x). Qed.
Lemma lem1225308 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225307 A R a0). Qed.
Lemma lem1225309 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225310 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225308 A R a0) (@lem1225309 A x)). Qed.
Lemma lem1225312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225313 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225312 A Prop f x). Qed.
Lemma lem1225314 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225313 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225316 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225310 A R a0 x) (@lem1225314 A R a0 x)). Qed.
Lemma lem1225317 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term711 A R a0 x) = (term712 A R a0 x).
Proof. exact (MK_COMB (@lem1225299) (@lem1225316 A R a0 x)). Qed.
Lemma lem1225324 {A : Type'} (x : A) (a1 : list A) : (term713 A x a1) = (term713 A x a1).
Proof. exact (eq_refl (term713 A x a1)). Qed.
Lemma lem1225325 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term423 A a1 R a0 x) = (term714 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225324 A x a1) (@lem1225317 A R a0 x)). Qed.
Lemma lem1225326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225327 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term519 A a1 R a0 x) = (term715 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225326) (@lem1225325 A a1 R a0 x)). Qed.
Lemma lem1225328 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term521 A a0 x R a1) = (term724 A a0 x R a1).
Proof. exact (MK_COMB (@lem1225327 A a1 R a0 x) (@lem1225298 A R a1)). Qed.
Lemma lem1225329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225330 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) : (term567 A a0 x R a1) = (term725 A a0 x R a1).
Proof. exact (MK_COMB (@lem1225329) (@lem1225328 A a0 x R a1)). Qed.
Lemma lem1225331 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term581 A a0 a1 m R x y) = (term726 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225330 A a0 x R a1) (@lem1225291 A a0 a1 m R x y)). Qed.
Lemma lem1225340 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term112 A R a1 m) = (term112 A R a1 m).
Proof. exact (eq_refl (term112 A R a1 m)). Qed.
Lemma lem1225347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225348 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225347 A (A -> Prop) f x). Qed.
Lemma lem1225349 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225348 A R a0). Qed.
Lemma lem1225350 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225351 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225349 A R a0) (@lem1225350 A x)). Qed.
Lemma lem1225353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225354 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225353 A Prop f x). Qed.
Lemma lem1225355 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225354 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225357 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225351 A R a0 x) (@lem1225355 A R a0 x)). Qed.
Lemma lem1225366 {A : Type'} (x : A) (m : list A) : (term703 A x m) = (term703 A x m).
Proof. exact (eq_refl (term703 A x m)). Qed.
Lemma lem1225367 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term424 A m R a0 x) = (term704 A m R a0 x).
Proof. exact (MK_COMB (@lem1225366 A x m) (@lem1225357 A R a0 x)). Qed.
Lemma lem1225368 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term432 A m R a0) = (term705 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1225367 A m R a0 x)). Qed.
Lemma lem1225369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225370 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term433 A m R a0) = (term706 A m R a0).
Proof. exact (MK_COMB (@lem1225369 A) (@lem1225368 A m R a0)). Qed.
Lemma lem1225377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225378 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225377 A (A -> Prop) f x). Qed.
Lemma lem1225379 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1225378 A R a0). Qed.
Lemma lem1225380 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1225381 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1225379 A R a0) (@lem1225380 A x)). Qed.
Lemma lem1225383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225384 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225383 A Prop f x). Qed.
Lemma lem1225385 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1225384 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1225387 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term696 A R a0 x).
Proof. exact (TRANS (@lem1225381 A R a0 x) (@lem1225385 A R a0 x)). Qed.
Lemma lem1225396 {A : Type'} (x : A) (a1 : list A) : (term703 A x a1) = (term703 A x a1).
Proof. exact (eq_refl (term703 A x a1)). Qed.
Lemma lem1225397 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term424 A a1 R a0 x) = (term704 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1225396 A x a1) (@lem1225387 A R a0 x)). Qed.
Lemma lem1225398 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term432 A a1 R a0) = (term705 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1225397 A a1 R a0 x)). Qed.
Lemma lem1225399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225400 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term433 A a1 R a0) = (term706 A a1 R a0).
Proof. exact (MK_COMB (@lem1225399 A) (@lem1225398 A a1 R a0)). Qed.
Lemma lem1225401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225402 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term439 A a1 R a0) = (term707 A a1 R a0).
Proof. exact (MK_COMB (@lem1225401) (@lem1225400 A a1 R a0)). Qed.
Lemma lem1225403 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term440 A a1 m R a0) = (term727 A a1 m R a0).
Proof. exact (MK_COMB (@lem1225402 A a1 R a0) (@lem1225370 A m R a0)). Qed.
Lemma lem1225404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225405 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) : (term447 A a1 m R a0) = (term728 A a1 m R a0).
Proof. exact (MK_COMB (@lem1225404) (@lem1225403 A a1 m R a0)). Qed.
Lemma lem1225406 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term448 A a0 R a1 m) = (term729 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1225405 A a1 m R a0) (@lem1225340 A R a1 m)). Qed.
Lemma lem1225407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225408 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) (m : list A) : (term501 A a0 R a1 m) = (term730 A a0 R a1 m).
Proof. exact (MK_COMB (@lem1225407) (@lem1225406 A a0 R a1 m)). Qed.
Lemma lem1225409 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term610 A a0 a1 m R x y) = (term731 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225408 A a0 R a1 m) (@lem1225331 A a0 a1 m R x y)). Qed.
Lemma lem1225410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1225411 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term688 A a0 a1 m R x y) = (term732 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1225410) (@lem1225409 A a0 a1 m R x y)). Qed.
Lemma lem1225412 {A : Type'} (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term690 A y x a0 a1 m R) = (term733 A y x a0 a1 m R).
Proof. exact (MK_COMB (@lem1225411 A a0 a1 m R x y) (@lem1225238 A x a0 a1 m R)). Qed.
Lemma lem1225413 {A : Type'} (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term690 A y x a0 a1 m R) : term733 A y x a0 a1 m R.
Proof. exact (EQ_MP (@lem1225412 A y x a0 a1 m R) (@lem1225060 A y x a0 a1 m R h1)). Qed.
Lemma lem1225420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225421 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225420 A (A -> Prop) f x). Qed.
Lemma lem1225422 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1225421 A R x). Qed.
Lemma lem1225423 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1225424 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1225422 A R x) (@lem1225423 A y)). Qed.
Lemma lem1225426 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225427 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225426 A Prop f x). Qed.
Lemma lem1225428 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term696 A R x y).
Proof. exact (@lem1225427 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1225430 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term696 A R x y).
Proof. exact (TRANS (@lem1225424 A R x y) (@lem1225428 A R x y)). Qed.
Lemma lem1225449 {A : Type'} (x : A) (a1 : list A) (y : A) (m : list A) : (term181 A x a1 y m) = (term181 A x a1 y m).
Proof. exact (eq_refl (term181 A x a1 y m)). Qed.
Lemma lem1225450 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term183 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (MK_COMB (@lem1225449 A x a1 y m) (@lem1225430 A R x y)). Qed.
Lemma lem1225451 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term193 A a1 m R x) = (term735 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1225450 A a1 m R x y)). Qed.
Lemma lem1225452 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225453 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term194 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (MK_COMB (@lem1225452 A) (@lem1225451 A a1 m R x)). Qed.
Lemma lem1225454 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term202 A a1 m R) = (term737 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225453 A a1 m R x)). Qed.
Lemma lem1225455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225456 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term203 A a1 m R) = (term738 A a1 m R).
Proof. exact (MK_COMB (@lem1225455 A) (@lem1225454 A a1 m R)). Qed.
Lemma lem1225463 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1225464 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term208 A a1 m R) = (term739 A a1 m R).
Proof. exact (MK_COMB (@lem1225463 A R m) (@lem1225456 A a1 m R)). Qed.
Lemma lem1225471 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1225472 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term212 A a1 m R) = (term740 A a1 m R).
Proof. exact (MK_COMB (@lem1225471 A R a1) (@lem1225464 A a1 m R)). Qed.
Lemma lem1225485 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1225486 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term215 A a1 m R) = (term741 A a1 m R).
Proof. exact (MK_COMB (@lem1225485 A R a1 m) (@lem1225472 A a1 m R)). Qed.
Lemma lem1225487 {A : Type'} (a1 : list A) (R : type1402 A) : (term232 A a1 R) = (term742 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1225486 A a1 m R)). Qed.
Lemma lem1225488 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1225489 {A : Type'} (a1 : list A) (R : type1402 A) : (term247 A a1 R) = (term743 A a1 R).
Proof. exact (MK_COMB (@lem1225488 A) (@lem1225487 A a1 R)). Qed.
Lemma lem1225490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1225501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225502 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1225501 A (A -> Prop) f x). Qed.
Lemma lem1225503 {A : Type'} (R : type1402 A) (x' : type1141 A) (m : list A) : (term744 A R x' m) = (term745 A R x' m).
Proof. exact (@lem1225502 A R (x' m)). Qed.
Lemma lem1225504 {A : Type'} (y' : type1141 A) (m : list A) : (y' m) = (y' m).
Proof. exact (eq_refl (y' m)). Qed.
Lemma lem1225505 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term746 A R x' y' m) = (term747 A R x' y' m).
Proof. exact (MK_COMB (@lem1225503 A R x' m) (@lem1225504 A y' m)). Qed.
Lemma lem1225507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1225508 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1225507 A Prop f x). Qed.
Lemma lem1225509 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term747 A R x' y' m) = (term748 A R x' y' m).
Proof. exact (@lem1225508 A (term745 A R x' m) (y' m)). Qed.
Lemma lem1225511 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term746 A R x' y' m) = (term748 A R x' y' m).
Proof. exact (TRANS (@lem1225505 A R x' y' m) (@lem1225509 A R x' y' m)). Qed.
Lemma lem1225512 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term749 A R x' y' m) = (term750 A R x' y' m).
Proof. exact (MK_COMB (@lem1225490) (@lem1225511 A R x' y' m)). Qed.
Lemma lem1225531 {A : Type'} (x' : type1141 A) (a1 : list A) (y' : type1141 A) (m : list A) : (term751 A x' a1 y' m) = (term751 A x' a1 y' m).
Proof. exact (eq_refl (term751 A x' a1 y' m)). Qed.
Lemma lem1225532 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term752 A a1 R x' y' m) = (term753 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1225531 A x' a1 y' m) (@lem1225512 A R x' y' m)). Qed.
Lemma lem1225541 {A : Type'} (R : type1402 A) (m : list A) : (term204 A R m) = (term204 A R m).
Proof. exact (eq_refl (term204 A R m)). Qed.
Lemma lem1225542 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term754 A a1 R x' y' m) = (term755 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1225541 A R m) (@lem1225532 A a1 R x' y' m)). Qed.
Lemma lem1225551 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1225552 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term756 A a1 R x' y' m) = (term757 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1225551 A R a1) (@lem1225542 A a1 R x' y' m)). Qed.
Lemma lem1225563 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1225564 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term374 A a1 R x' y' m) = (term758 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1225563 A R a1 m) (@lem1225552 A a1 R x' y' m)). Qed.
Lemma lem1225565 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) : (term376 A a1 R x' y') = (term759 A a1 R x' y').
Proof. exact (fun_ext (fun m : list A => @lem1225564 A a1 R x' y' m)). Qed.
Lemma lem1225566 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1225567 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) : (term378 A a1 R x' y') = (term760 A a1 R x' y').
Proof. exact (MK_COMB (@lem1225566 A) (@lem1225565 A a1 R x' y')). Qed.
Lemma lem1225568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1225569 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) : (term414 A a1 R x' y') = (term761 A a1 R x' y').
Proof. exact (MK_COMB (@lem1225568) (@lem1225567 A a1 R x' y')). Qed.
Lemma lem1225570 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) : (term416 A x' y' a1 R) = (term762 A x' y' a1 R).
Proof. exact (MK_COMB (@lem1225569 A a1 R x' y') (@lem1225489 A a1 R)). Qed.
Lemma lem1225571 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term762 A x' y' a1 R.
Proof. exact (EQ_MP (@lem1225570 A x' y' a1 R) (@lem1225062 A x' y' a1 R h1)). Qed.
Lemma lem1225572 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term743 A a1 R.
Proof. exact (proj2 (@lem1225571 A x' y' a1 R h1)). Qed.
Lemma lem1225573 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term760 A a1 R x' y'.
Proof. exact (proj1 (@lem1225571 A x' y' a1 R h1)). Qed.
Lemma lem1225574 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term731 A a0 a1 m R x y.
Proof. exact (h1). Qed.
Lemma lem1225575 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term720 A x a0 a1 m R.
Proof. exact (h1). Qed.
Lemma lem1225576 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term726 A a0 a1 m R x y.
Proof. exact (proj2 (@lem1225574 A a0 a1 m R x y h1)). Qed.
Lemma lem1225577 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term729 A a0 R a1 m.
Proof. exact (proj1 (@lem1225574 A a0 a1 m R x y h1)). Qed.
Lemma lem1225579 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term727 A a1 m R a0.
Proof. exact (proj1 (@lem1225577 A a0 a1 m R x y h1)). Qed.
Lemma lem1225580 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term706 A m R a0.
Proof. exact (proj2 (@lem1225579 A a0 a1 m R x y h1)). Qed.
Lemma lem1225581 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term706 A a1 R a0.
Proof. exact (proj1 (@lem1225579 A a0 a1 m R x y h1)). Qed.
Lemma lem1225582 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (h1 : term724 A a0 x R a1) : term724 A a0 x R a1.
Proof. exact (h1). Qed.
Lemma lem1225583 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term723 A a0 a1 m R x y) : term723 A a0 a1 m R x y.
Proof. exact (h1). Qed.
Lemma lem1225584 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term714 A a1 R a0 x.
Proof. exact (h1). Qed.
Lemma lem1225589 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term722 A a0 a1 m R x y.
Proof. exact (h1). Qed.
Lemma lem1225591 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term124 A a0 x a1 y m.
Proof. exact (proj1 (@lem1225589 A a0 a1 m R x y h1)). Qed.
Lemma lem1225593 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term120 A a0 x a1.
Proof. exact (proj1 (@lem1225591 A a0 a1 m R x y h1)). Qed.
Lemma lem1225596 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term710 A a0 a1 m R.
Proof. exact (proj2 (@lem1225575 A x a0 a1 m R h1)). Qed.
Lemma lem1225597 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term718 A a0 x R a1 m.
Proof. exact (proj1 (@lem1225575 A x a0 a1 m R h1)). Qed.
Lemma lem1225598 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term702 A a0 a1 m R.
Proof. exact (proj2 (@lem1225596 A x a0 a1 m R h1)). Qed.
Lemma lem1225599 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term708 A a0 R a1.
Proof. exact (proj1 (@lem1225596 A x a0 a1 m R h1)). Qed.
Lemma lem1225600 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term701 A a0 a1 m R.
Proof. exact (proj2 (@lem1225598 A x a0 a1 m R h1)). Qed.
Lemma lem1225603 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term706 A a1 R a0.
Proof. exact (proj1 (@lem1225599 A x a0 a1 m R h1)). Qed.
Lemma lem1225604 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term716 A a1 m R a0 x) : term716 A a1 m R a0 x.
Proof. exact (h1). Qed.
Lemma lem1225606 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term714 A a1 R a0 x.
Proof. exact (h1). Qed.
Lemma lem1225607 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : term714 A m R a0 x.
Proof. exact (h1). Qed.
Lemma lem1225883 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term704 A a1 R a0 x) = (term704 A a1 R a0 x).
Proof. exact (eq_refl (term704 A a1 R a0 x)). Qed.
Lemma lem1225884 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term705 A a1 R a0) = (term705 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1225883 A a1 R a0 x)). Qed.
Lemma lem1225885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225887 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term706 A a1 R a0) = (term706 A a1 R a0).
Proof. exact (MK_COMB (@lem1225885 A) (@lem1225884 A a1 R a0)). Qed.
Lemma lem1225888 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term706 A a1 R a0.
Proof. exact (EQ_MP (@lem1225887 A a1 R a0) (@lem1225581 A a0 a1 m R x y h1)). Qed.
Lemma lem1225980 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1225981 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1225980 A P Q). Qed.
Lemma lem1225982 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term766 A a1 m R).
Proof. exact (@lem1225981 A (@List.ForallOrdPairs A R m) (term737 A a1 m R)). Qed.
Lemma lem1225983 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1225984 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term768 A a1 m R) = (term737 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225983 A a1 m R x)). Qed.
Lemma lem1225985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225986 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term769 A a1 m R) = (term738 A a1 m R).
Proof. exact (MK_COMB (@lem1225985 A) (@lem1225984 A a1 m R)). Qed.
Lemma lem1225987 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1225988 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term739 A a1 m R).
Proof. exact (MK_COMB (@lem1225987 A R m) (@lem1225986 A a1 m R)). Qed.
Lemma lem1225989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1225990 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term770 A a1 m R) = (term771 A a1 m R).
Proof. exact (MK_COMB (@lem1225989) (@lem1225988 A a1 m R)). Qed.
Lemma lem1225991 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1225992 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1225993 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term772 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1225992 A R m) (@lem1225991 A a1 m R x)). Qed.
Lemma lem1225994 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term774 A a1 m R) = (term775 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1225993 A a1 m R x)). Qed.
Lemma lem1225995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1225996 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term766 A a1 m R) = (term776 A a1 m R).
Proof. exact (MK_COMB (@lem1225995 A) (@lem1225994 A a1 m R)). Qed.
Lemma lem1225997 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term765 A a1 m R) = (term766 A a1 m R)) = ((term739 A a1 m R) = (term776 A a1 m R)).
Proof. exact (MK_COMB (@lem1225990 A a1 m R) (@lem1225996 A a1 m R)). Qed.
Lemma lem1225998 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term776 A a1 m R).
Proof. exact (EQ_MP (@lem1225997 A a1 m R) (@lem1225982 A a1 m R)). Qed.
Lemma lem1226000 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226001 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226000 A P Q). Qed.
Lemma lem1226002 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term778 A a1 m R x).
Proof. exact (@lem1226001 A (@List.ForallOrdPairs A R m) (term735 A a1 m R x)). Qed.
Lemma lem1226003 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226004 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term780 A a1 m R x) = (term735 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226003 A a1 m R x y)). Qed.
Lemma lem1226005 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226006 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term781 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (MK_COMB (@lem1226005 A) (@lem1226004 A a1 m R x)). Qed.
Lemma lem1226007 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226008 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1226007 A R m) (@lem1226006 A a1 m R x)). Qed.
Lemma lem1226009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226010 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term782 A a1 m R x) = (term783 A a1 m R x).
Proof. exact (MK_COMB (@lem1226009) (@lem1226008 A a1 m R x)). Qed.
Lemma lem1226011 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226012 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226013 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term784 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226012 A R m) (@lem1226011 A a1 m R x y)). Qed.
Lemma lem1226014 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term786 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226013 A a1 m R x y)). Qed.
Lemma lem1226015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226016 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term778 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226015 A) (@lem1226014 A a1 m R x)). Qed.
Lemma lem1226017 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term777 A a1 m R x) = (term778 A a1 m R x)) = ((term773 A a1 m R x) = (term788 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226010 A a1 m R x) (@lem1226016 A a1 m R x)). Qed.
Lemma lem1226018 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term773 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (EQ_MP (@lem1226017 A a1 m R x) (@lem1226002 A a1 m R x)). Qed.
Lemma lem1226019 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term775 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226018 A a1 m R x)). Qed.
Lemma lem1226020 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226021 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term776 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226020 A) (@lem1226019 A a1 m R)). Qed.
Lemma lem1226022 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term790 A a1 m R).
Proof. exact (TRANS (@lem1225998 A a1 m R) (@lem1226021 A a1 m R)). Qed.
Lemma lem1226023 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226024 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226023 A R a1) (@lem1226022 A a1 m R)). Qed.
Lemma lem1226026 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226027 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226026 A P Q). Qed.
Lemma lem1226028 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term793 A a1 m R).
Proof. exact (@lem1226027 A (@List.ForallOrdPairs A R a1) (term789 A a1 m R)). Qed.
Lemma lem1226029 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226030 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term795 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226029 A a1 m R x)). Qed.
Lemma lem1226031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226032 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term796 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226031 A) (@lem1226030 A a1 m R)). Qed.
Lemma lem1226033 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226034 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226033 A R a1) (@lem1226032 A a1 m R)). Qed.
Lemma lem1226035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226036 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term797 A a1 m R) = (term798 A a1 m R).
Proof. exact (MK_COMB (@lem1226035) (@lem1226034 A a1 m R)). Qed.
Lemma lem1226037 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226038 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226039 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term799 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226038 A R a1) (@lem1226037 A a1 m R x)). Qed.
Lemma lem1226040 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term801 A a1 m R) = (term802 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226039 A a1 m R x)). Qed.
Lemma lem1226041 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226042 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term793 A a1 m R) = (term803 A a1 m R).
Proof. exact (MK_COMB (@lem1226041 A) (@lem1226040 A a1 m R)). Qed.
Lemma lem1226043 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term792 A a1 m R) = (term793 A a1 m R)) = ((term791 A a1 m R) = (term803 A a1 m R)).
Proof. exact (MK_COMB (@lem1226036 A a1 m R) (@lem1226042 A a1 m R)). Qed.
Lemma lem1226044 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term803 A a1 m R).
Proof. exact (EQ_MP (@lem1226043 A a1 m R) (@lem1226028 A a1 m R)). Qed.
Lemma lem1226046 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226047 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226046 A P Q). Qed.
Lemma lem1226048 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term805 A a1 m R x).
Proof. exact (@lem1226047 A (@List.ForallOrdPairs A R a1) (term787 A a1 m R x)). Qed.
Lemma lem1226049 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226050 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term807 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226049 A a1 m R x y)). Qed.
Lemma lem1226051 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226052 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term808 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226051 A) (@lem1226050 A a1 m R x)). Qed.
Lemma lem1226053 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226054 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226053 A R a1) (@lem1226052 A a1 m R x)). Qed.
Lemma lem1226055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226056 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term809 A a1 m R x) = (term810 A a1 m R x).
Proof. exact (MK_COMB (@lem1226055) (@lem1226054 A a1 m R x)). Qed.
Lemma lem1226057 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226058 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226059 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term811 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226058 A R a1) (@lem1226057 A a1 m R x y)). Qed.
Lemma lem1226060 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term813 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226059 A a1 m R x y)). Qed.
Lemma lem1226061 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226062 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term805 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226061 A) (@lem1226060 A a1 m R x)). Qed.
Lemma lem1226063 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term804 A a1 m R x) = (term805 A a1 m R x)) = ((term800 A a1 m R x) = (term815 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226056 A a1 m R x) (@lem1226062 A a1 m R x)). Qed.
Lemma lem1226064 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term800 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (EQ_MP (@lem1226063 A a1 m R x) (@lem1226048 A a1 m R x)). Qed.
Lemma lem1226065 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term802 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226064 A a1 m R x)). Qed.
Lemma lem1226066 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226067 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term803 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226066 A) (@lem1226065 A a1 m R)). Qed.
Lemma lem1226068 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226044 A a1 m R) (@lem1226067 A a1 m R)). Qed.
Lemma lem1226069 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226024 A a1 m R) (@lem1226068 A a1 m R)). Qed.
Lemma lem1226070 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226071 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226070 A R a1 m) (@lem1226069 A a1 m R)). Qed.
Lemma lem1226073 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226073 A P Q). Qed.
Lemma lem1226075 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term822 A a1 m R).
Proof. exact (@lem1226074 A (term441 A R a1 m) (term816 A a1 m R)). Qed.
Lemma lem1226076 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226077 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term824 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226076 A a1 m R x)). Qed.
Lemma lem1226078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226079 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term825 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226078 A) (@lem1226077 A a1 m R)). Qed.
Lemma lem1226080 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226081 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226080 A R a1 m) (@lem1226079 A a1 m R)). Qed.
Lemma lem1226082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226083 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term826 A a1 m R) = (term827 A a1 m R).
Proof. exact (MK_COMB (@lem1226082) (@lem1226081 A a1 m R)). Qed.
Lemma lem1226084 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226085 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226086 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term828 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226085 A R a1 m) (@lem1226084 A a1 m R x)). Qed.
Lemma lem1226087 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term830 A a1 m R) = (term831 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226086 A a1 m R x)). Qed.
Lemma lem1226088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226089 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term822 A a1 m R) = (term832 A a1 m R).
Proof. exact (MK_COMB (@lem1226088 A) (@lem1226087 A a1 m R)). Qed.
Lemma lem1226090 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term821 A a1 m R) = (term822 A a1 m R)) = ((term818 A a1 m R) = (term832 A a1 m R)).
Proof. exact (MK_COMB (@lem1226083 A a1 m R) (@lem1226089 A a1 m R)). Qed.
Lemma lem1226091 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term832 A a1 m R).
Proof. exact (EQ_MP (@lem1226090 A a1 m R) (@lem1226075 A a1 m R)). Qed.
Lemma lem1226093 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226094 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226093 A P Q). Qed.
Lemma lem1226095 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term834 A a1 m R x).
Proof. exact (@lem1226094 A (term441 A R a1 m) (term814 A a1 m R x)). Qed.
Lemma lem1226096 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226097 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term836 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226096 A a1 m R x y)). Qed.
Lemma lem1226098 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226099 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term837 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226098 A) (@lem1226097 A a1 m R x)). Qed.
Lemma lem1226100 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226101 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226100 A R a1 m) (@lem1226099 A a1 m R x)). Qed.
Lemma lem1226102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226103 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term838 A a1 m R x) = (term839 A a1 m R x).
Proof. exact (MK_COMB (@lem1226102) (@lem1226101 A a1 m R x)). Qed.
Lemma lem1226104 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226105 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226106 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term840 A a1 m R x y) = (term841 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226105 A R a1 m) (@lem1226104 A a1 m R x y)). Qed.
Lemma lem1226107 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term842 A a1 m R x) = (term843 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226106 A a1 m R x y)). Qed.
Lemma lem1226108 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226109 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term834 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (MK_COMB (@lem1226108 A) (@lem1226107 A a1 m R x)). Qed.
Lemma lem1226110 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term833 A a1 m R x) = (term834 A a1 m R x)) = ((term829 A a1 m R x) = (term844 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226103 A a1 m R x) (@lem1226109 A a1 m R x)). Qed.
Lemma lem1226111 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term829 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (EQ_MP (@lem1226110 A a1 m R x) (@lem1226095 A a1 m R x)). Qed.
Lemma lem1226112 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term831 A a1 m R) = (term845 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226111 A a1 m R x)). Qed.
Lemma lem1226113 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226114 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term832 A a1 m R) = (term846 A a1 m R).
Proof. exact (MK_COMB (@lem1226113 A) (@lem1226112 A a1 m R)). Qed.
Lemma lem1226115 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226091 A a1 m R) (@lem1226114 A a1 m R)). Qed.
Lemma lem1226116 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226071 A a1 m R) (@lem1226115 A a1 m R)). Qed.
Lemma lem1226117 {A : Type'} (a1 : list A) (R : type1402 A) : (term742 A a1 R) = (term847 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1226116 A a1 m R)). Qed.
Lemma lem1226118 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1226119 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term848 A a1 R).
Proof. exact (MK_COMB (@lem1226118 A) (@lem1226117 A a1 R)). Qed.
Lemma lem1226145 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term849 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R a1) (term441 A R a1 m) (term785 A a1 m R x y)). Qed.
Lemma lem1226152 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term850 A a1 m R x y) = (term851 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R m) (term441 A R a1 m) (term734 A a1 m R x y)). Qed.
Lemma lem1226155 {A : Type'} (m : list A) (R : type1402 A) (a1 : list A) : (term852 A m R a1) = (term852 A m R a1).
Proof. exact (eq_refl (term852 A m R a1)). Qed.
Lemma lem1226156 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term849 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226155 A m R a1) (@lem1226152 A a1 m R x y)). Qed.
Lemma lem1226158 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (TRANS (@lem1226145 A a1 m R x y) (@lem1226156 A a1 m R x y)). Qed.
Lemma lem1226159 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term843 A a1 m R x) = (term854 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226158 A a1 m R x y)). Qed.
Lemma lem1226160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226161 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term844 A a1 m R x) = (term855 A a1 m R x).
Proof. exact (MK_COMB (@lem1226160 A) (@lem1226159 A a1 m R x)). Qed.
Lemma lem1226162 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term845 A a1 m R) = (term856 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226161 A a1 m R x)). Qed.
Lemma lem1226163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226164 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term846 A a1 m R) = (term857 A a1 m R).
Proof. exact (MK_COMB (@lem1226163 A) (@lem1226162 A a1 m R)). Qed.
Lemma lem1226165 {A : Type'} (a1 : list A) (R : type1402 A) : (term847 A a1 R) = (term858 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1226164 A a1 m R)). Qed.
Lemma lem1226166 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1226167 {A : Type'} (a1 : list A) (R : type1402 A) : (term848 A a1 R) = (term859 A a1 R).
Proof. exact (MK_COMB (@lem1226166 A) (@lem1226165 A a1 R)). Qed.
Lemma lem1226168 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term859 A a1 R).
Proof. exact (TRANS (@lem1226119 A a1 R) (@lem1226167 A a1 R)). Qed.
Lemma lem1226169 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term859 A a1 R.
Proof. exact (EQ_MP (@lem1226168 A a1 R) (@lem1225572 A x' y' a1 R h1)). Qed.
Lemma lem1226203 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term253 A R a1) : term253 A R a1.
Proof. exact (h1). Qed.
Lemma lem1226274 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226275 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226274 A P Q). Qed.
Lemma lem1226276 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term766 A a1 m R).
Proof. exact (@lem1226275 A (@List.ForallOrdPairs A R m) (term737 A a1 m R)). Qed.
Lemma lem1226277 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1226278 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term768 A a1 m R) = (term737 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226277 A a1 m R x)). Qed.
Lemma lem1226279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226280 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term769 A a1 m R) = (term738 A a1 m R).
Proof. exact (MK_COMB (@lem1226279 A) (@lem1226278 A a1 m R)). Qed.
Lemma lem1226281 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226282 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term739 A a1 m R).
Proof. exact (MK_COMB (@lem1226281 A R m) (@lem1226280 A a1 m R)). Qed.
Lemma lem1226283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226284 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term770 A a1 m R) = (term771 A a1 m R).
Proof. exact (MK_COMB (@lem1226283) (@lem1226282 A a1 m R)). Qed.
Lemma lem1226285 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1226286 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226287 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term772 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1226286 A R m) (@lem1226285 A a1 m R x)). Qed.
Lemma lem1226288 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term774 A a1 m R) = (term775 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226287 A a1 m R x)). Qed.
Lemma lem1226289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226290 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term766 A a1 m R) = (term776 A a1 m R).
Proof. exact (MK_COMB (@lem1226289 A) (@lem1226288 A a1 m R)). Qed.
Lemma lem1226291 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term765 A a1 m R) = (term766 A a1 m R)) = ((term739 A a1 m R) = (term776 A a1 m R)).
Proof. exact (MK_COMB (@lem1226284 A a1 m R) (@lem1226290 A a1 m R)). Qed.
Lemma lem1226292 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term776 A a1 m R).
Proof. exact (EQ_MP (@lem1226291 A a1 m R) (@lem1226276 A a1 m R)). Qed.
Lemma lem1226294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226295 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226294 A P Q). Qed.
Lemma lem1226296 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term778 A a1 m R x).
Proof. exact (@lem1226295 A (@List.ForallOrdPairs A R m) (term735 A a1 m R x)). Qed.
Lemma lem1226297 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226298 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term780 A a1 m R x) = (term735 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226297 A a1 m R x y)). Qed.
Lemma lem1226299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226300 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term781 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (MK_COMB (@lem1226299 A) (@lem1226298 A a1 m R x)). Qed.
Lemma lem1226301 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226302 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1226301 A R m) (@lem1226300 A a1 m R x)). Qed.
Lemma lem1226303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226304 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term782 A a1 m R x) = (term783 A a1 m R x).
Proof. exact (MK_COMB (@lem1226303) (@lem1226302 A a1 m R x)). Qed.
Lemma lem1226305 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226306 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226307 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term784 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226306 A R m) (@lem1226305 A a1 m R x y)). Qed.
Lemma lem1226308 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term786 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226307 A a1 m R x y)). Qed.
Lemma lem1226309 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226310 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term778 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226309 A) (@lem1226308 A a1 m R x)). Qed.
Lemma lem1226311 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term777 A a1 m R x) = (term778 A a1 m R x)) = ((term773 A a1 m R x) = (term788 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226304 A a1 m R x) (@lem1226310 A a1 m R x)). Qed.
Lemma lem1226312 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term773 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (EQ_MP (@lem1226311 A a1 m R x) (@lem1226296 A a1 m R x)). Qed.
Lemma lem1226313 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term775 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226312 A a1 m R x)). Qed.
Lemma lem1226314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226315 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term776 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226314 A) (@lem1226313 A a1 m R)). Qed.
Lemma lem1226316 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term790 A a1 m R).
Proof. exact (TRANS (@lem1226292 A a1 m R) (@lem1226315 A a1 m R)). Qed.
Lemma lem1226317 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226318 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226317 A R a1) (@lem1226316 A a1 m R)). Qed.
Lemma lem1226320 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226321 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226320 A P Q). Qed.
Lemma lem1226322 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term793 A a1 m R).
Proof. exact (@lem1226321 A (@List.ForallOrdPairs A R a1) (term789 A a1 m R)). Qed.
Lemma lem1226323 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226324 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term795 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226323 A a1 m R x)). Qed.
Lemma lem1226325 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226326 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term796 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226325 A) (@lem1226324 A a1 m R)). Qed.
Lemma lem1226327 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226328 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226327 A R a1) (@lem1226326 A a1 m R)). Qed.
Lemma lem1226329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226330 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term797 A a1 m R) = (term798 A a1 m R).
Proof. exact (MK_COMB (@lem1226329) (@lem1226328 A a1 m R)). Qed.
Lemma lem1226331 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226332 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226333 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term799 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226332 A R a1) (@lem1226331 A a1 m R x)). Qed.
Lemma lem1226334 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term801 A a1 m R) = (term802 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226333 A a1 m R x)). Qed.
Lemma lem1226335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226336 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term793 A a1 m R) = (term803 A a1 m R).
Proof. exact (MK_COMB (@lem1226335 A) (@lem1226334 A a1 m R)). Qed.
Lemma lem1226337 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term792 A a1 m R) = (term793 A a1 m R)) = ((term791 A a1 m R) = (term803 A a1 m R)).
Proof. exact (MK_COMB (@lem1226330 A a1 m R) (@lem1226336 A a1 m R)). Qed.
Lemma lem1226338 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term803 A a1 m R).
Proof. exact (EQ_MP (@lem1226337 A a1 m R) (@lem1226322 A a1 m R)). Qed.
Lemma lem1226340 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226341 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226340 A P Q). Qed.
Lemma lem1226342 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term805 A a1 m R x).
Proof. exact (@lem1226341 A (@List.ForallOrdPairs A R a1) (term787 A a1 m R x)). Qed.
Lemma lem1226343 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226344 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term807 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226343 A a1 m R x y)). Qed.
Lemma lem1226345 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226346 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term808 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226345 A) (@lem1226344 A a1 m R x)). Qed.
Lemma lem1226347 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226348 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226347 A R a1) (@lem1226346 A a1 m R x)). Qed.
Lemma lem1226349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226350 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term809 A a1 m R x) = (term810 A a1 m R x).
Proof. exact (MK_COMB (@lem1226349) (@lem1226348 A a1 m R x)). Qed.
Lemma lem1226351 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226352 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226353 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term811 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226352 A R a1) (@lem1226351 A a1 m R x y)). Qed.
Lemma lem1226354 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term813 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226353 A a1 m R x y)). Qed.
Lemma lem1226355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226356 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term805 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226355 A) (@lem1226354 A a1 m R x)). Qed.
Lemma lem1226357 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term804 A a1 m R x) = (term805 A a1 m R x)) = ((term800 A a1 m R x) = (term815 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226350 A a1 m R x) (@lem1226356 A a1 m R x)). Qed.
Lemma lem1226358 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term800 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (EQ_MP (@lem1226357 A a1 m R x) (@lem1226342 A a1 m R x)). Qed.
Lemma lem1226359 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term802 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226358 A a1 m R x)). Qed.
Lemma lem1226360 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226361 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term803 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226360 A) (@lem1226359 A a1 m R)). Qed.
Lemma lem1226362 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226338 A a1 m R) (@lem1226361 A a1 m R)). Qed.
Lemma lem1226363 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226318 A a1 m R) (@lem1226362 A a1 m R)). Qed.
Lemma lem1226364 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226365 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226364 A R a1 m) (@lem1226363 A a1 m R)). Qed.
Lemma lem1226367 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226367 A P Q). Qed.
Lemma lem1226369 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term822 A a1 m R).
Proof. exact (@lem1226368 A (term441 A R a1 m) (term816 A a1 m R)). Qed.
Lemma lem1226370 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226371 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term824 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226370 A a1 m R x)). Qed.
Lemma lem1226372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226373 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term825 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226372 A) (@lem1226371 A a1 m R)). Qed.
Lemma lem1226374 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226375 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226374 A R a1 m) (@lem1226373 A a1 m R)). Qed.
Lemma lem1226376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226377 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term826 A a1 m R) = (term827 A a1 m R).
Proof. exact (MK_COMB (@lem1226376) (@lem1226375 A a1 m R)). Qed.
Lemma lem1226378 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226379 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226380 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term828 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226379 A R a1 m) (@lem1226378 A a1 m R x)). Qed.
Lemma lem1226381 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term830 A a1 m R) = (term831 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226380 A a1 m R x)). Qed.
Lemma lem1226382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226383 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term822 A a1 m R) = (term832 A a1 m R).
Proof. exact (MK_COMB (@lem1226382 A) (@lem1226381 A a1 m R)). Qed.
Lemma lem1226384 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term821 A a1 m R) = (term822 A a1 m R)) = ((term818 A a1 m R) = (term832 A a1 m R)).
Proof. exact (MK_COMB (@lem1226377 A a1 m R) (@lem1226383 A a1 m R)). Qed.
Lemma lem1226385 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term832 A a1 m R).
Proof. exact (EQ_MP (@lem1226384 A a1 m R) (@lem1226369 A a1 m R)). Qed.
Lemma lem1226387 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226388 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226387 A P Q). Qed.
Lemma lem1226389 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term834 A a1 m R x).
Proof. exact (@lem1226388 A (term441 A R a1 m) (term814 A a1 m R x)). Qed.
Lemma lem1226390 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226391 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term836 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226390 A a1 m R x y)). Qed.
Lemma lem1226392 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226393 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term837 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226392 A) (@lem1226391 A a1 m R x)). Qed.
Lemma lem1226394 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226395 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226394 A R a1 m) (@lem1226393 A a1 m R x)). Qed.
Lemma lem1226396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226397 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term838 A a1 m R x) = (term839 A a1 m R x).
Proof. exact (MK_COMB (@lem1226396) (@lem1226395 A a1 m R x)). Qed.
Lemma lem1226398 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226399 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226400 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term840 A a1 m R x y) = (term841 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226399 A R a1 m) (@lem1226398 A a1 m R x y)). Qed.
Lemma lem1226401 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term842 A a1 m R x) = (term843 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226400 A a1 m R x y)). Qed.
Lemma lem1226402 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226403 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term834 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (MK_COMB (@lem1226402 A) (@lem1226401 A a1 m R x)). Qed.
Lemma lem1226404 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term833 A a1 m R x) = (term834 A a1 m R x)) = ((term829 A a1 m R x) = (term844 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226397 A a1 m R x) (@lem1226403 A a1 m R x)). Qed.
Lemma lem1226405 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term829 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (EQ_MP (@lem1226404 A a1 m R x) (@lem1226389 A a1 m R x)). Qed.
Lemma lem1226406 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term831 A a1 m R) = (term845 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226405 A a1 m R x)). Qed.
Lemma lem1226407 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226408 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term832 A a1 m R) = (term846 A a1 m R).
Proof. exact (MK_COMB (@lem1226407 A) (@lem1226406 A a1 m R)). Qed.
Lemma lem1226409 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226385 A a1 m R) (@lem1226408 A a1 m R)). Qed.
Lemma lem1226410 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226365 A a1 m R) (@lem1226409 A a1 m R)). Qed.
Lemma lem1226411 {A : Type'} (a1 : list A) (R : type1402 A) : (term742 A a1 R) = (term847 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1226410 A a1 m R)). Qed.
Lemma lem1226412 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1226413 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term848 A a1 R).
Proof. exact (MK_COMB (@lem1226412 A) (@lem1226411 A a1 R)). Qed.
Lemma lem1226439 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term849 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R a1) (term441 A R a1 m) (term785 A a1 m R x y)). Qed.
Lemma lem1226446 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term850 A a1 m R x y) = (term851 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R m) (term441 A R a1 m) (term734 A a1 m R x y)). Qed.
Lemma lem1226449 {A : Type'} (m : list A) (R : type1402 A) (a1 : list A) : (term852 A m R a1) = (term852 A m R a1).
Proof. exact (eq_refl (term852 A m R a1)). Qed.
Lemma lem1226450 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term849 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226449 A m R a1) (@lem1226446 A a1 m R x y)). Qed.
Lemma lem1226452 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (TRANS (@lem1226439 A a1 m R x y) (@lem1226450 A a1 m R x y)). Qed.
Lemma lem1226453 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term843 A a1 m R x) = (term854 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226452 A a1 m R x y)). Qed.
Lemma lem1226454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226455 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term844 A a1 m R x) = (term855 A a1 m R x).
Proof. exact (MK_COMB (@lem1226454 A) (@lem1226453 A a1 m R x)). Qed.
Lemma lem1226456 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term845 A a1 m R) = (term856 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226455 A a1 m R x)). Qed.
Lemma lem1226457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226458 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term846 A a1 m R) = (term857 A a1 m R).
Proof. exact (MK_COMB (@lem1226457 A) (@lem1226456 A a1 m R)). Qed.
Lemma lem1226459 {A : Type'} (a1 : list A) (R : type1402 A) : (term847 A a1 R) = (term858 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1226458 A a1 m R)). Qed.
Lemma lem1226460 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1226461 {A : Type'} (a1 : list A) (R : type1402 A) : (term848 A a1 R) = (term859 A a1 R).
Proof. exact (MK_COMB (@lem1226460 A) (@lem1226459 A a1 R)). Qed.
Lemma lem1226462 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term859 A a1 R).
Proof. exact (TRANS (@lem1226413 A a1 R) (@lem1226461 A a1 R)). Qed.
Lemma lem1226463 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term859 A a1 R.
Proof. exact (EQ_MP (@lem1226462 A a1 R) (@lem1225572 A x' y' a1 R h1)). Qed.
Lemma lem1226497 {A : Type'} (R : type1402 A) (m : list A) (h1 : term253 A R m) : term253 A R m.
Proof. exact (h1). Qed.
Lemma lem1226782 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) : (term704 A m R a0 x) = (term704 A m R a0 x).
Proof. exact (eq_refl (term704 A m R a0 x)). Qed.
Lemma lem1226783 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term705 A m R a0) = (term705 A m R a0).
Proof. exact (fun_ext (fun x : A => @lem1226782 A m R a0 x)). Qed.
Lemma lem1226784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226786 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) : (term706 A m R a0) = (term706 A m R a0).
Proof. exact (MK_COMB (@lem1226784 A) (@lem1226783 A m R a0)). Qed.
Lemma lem1226787 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term706 A m R a0.
Proof. exact (EQ_MP (@lem1226786 A m R a0) (@lem1225580 A a0 a1 m R x y h1)). Qed.
Lemma lem1226799 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem1226870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226870 A P Q). Qed.
Lemma lem1226872 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term766 A a1 m R).
Proof. exact (@lem1226871 A (@List.ForallOrdPairs A R m) (term737 A a1 m R)). Qed.
Lemma lem1226873 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1226874 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term768 A a1 m R) = (term737 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226873 A a1 m R x)). Qed.
Lemma lem1226875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226876 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term769 A a1 m R) = (term738 A a1 m R).
Proof. exact (MK_COMB (@lem1226875 A) (@lem1226874 A a1 m R)). Qed.
Lemma lem1226877 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226878 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term765 A a1 m R) = (term739 A a1 m R).
Proof. exact (MK_COMB (@lem1226877 A R m) (@lem1226876 A a1 m R)). Qed.
Lemma lem1226879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226880 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term770 A a1 m R) = (term771 A a1 m R).
Proof. exact (MK_COMB (@lem1226879) (@lem1226878 A a1 m R)). Qed.
Lemma lem1226881 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term767 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (eq_refl (term767 A a1 m R x)). Qed.
Lemma lem1226882 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226883 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term772 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1226882 A R m) (@lem1226881 A a1 m R x)). Qed.
Lemma lem1226884 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term774 A a1 m R) = (term775 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226883 A a1 m R x)). Qed.
Lemma lem1226885 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226886 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term766 A a1 m R) = (term776 A a1 m R).
Proof. exact (MK_COMB (@lem1226885 A) (@lem1226884 A a1 m R)). Qed.
Lemma lem1226887 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term765 A a1 m R) = (term766 A a1 m R)) = ((term739 A a1 m R) = (term776 A a1 m R)).
Proof. exact (MK_COMB (@lem1226880 A a1 m R) (@lem1226886 A a1 m R)). Qed.
Lemma lem1226888 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term776 A a1 m R).
Proof. exact (EQ_MP (@lem1226887 A a1 m R) (@lem1226872 A a1 m R)). Qed.
Lemma lem1226890 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226891 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226890 A P Q). Qed.
Lemma lem1226892 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term778 A a1 m R x).
Proof. exact (@lem1226891 A (@List.ForallOrdPairs A R m) (term735 A a1 m R x)). Qed.
Lemma lem1226893 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226894 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term780 A a1 m R x) = (term735 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226893 A a1 m R x y)). Qed.
Lemma lem1226895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226896 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term781 A a1 m R x) = (term736 A a1 m R x).
Proof. exact (MK_COMB (@lem1226895 A) (@lem1226894 A a1 m R x)). Qed.
Lemma lem1226897 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226898 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term777 A a1 m R x) = (term773 A a1 m R x).
Proof. exact (MK_COMB (@lem1226897 A R m) (@lem1226896 A a1 m R x)). Qed.
Lemma lem1226899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226900 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term782 A a1 m R x) = (term783 A a1 m R x).
Proof. exact (MK_COMB (@lem1226899) (@lem1226898 A a1 m R x)). Qed.
Lemma lem1226901 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term779 A a1 m R x y) = (term734 A a1 m R x y).
Proof. exact (eq_refl (term779 A a1 m R x y)). Qed.
Lemma lem1226902 {A : Type'} (R : type1402 A) (m : list A) : (term89 A R m) = (term89 A R m).
Proof. exact (eq_refl (term89 A R m)). Qed.
Lemma lem1226903 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term784 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226902 A R m) (@lem1226901 A a1 m R x y)). Qed.
Lemma lem1226904 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term786 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226903 A a1 m R x y)). Qed.
Lemma lem1226905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226906 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term778 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226905 A) (@lem1226904 A a1 m R x)). Qed.
Lemma lem1226907 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term777 A a1 m R x) = (term778 A a1 m R x)) = ((term773 A a1 m R x) = (term788 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226900 A a1 m R x) (@lem1226906 A a1 m R x)). Qed.
Lemma lem1226908 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term773 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (EQ_MP (@lem1226907 A a1 m R x) (@lem1226892 A a1 m R x)). Qed.
Lemma lem1226909 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term775 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226908 A a1 m R x)). Qed.
Lemma lem1226910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226911 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term776 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226910 A) (@lem1226909 A a1 m R)). Qed.
Lemma lem1226912 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term739 A a1 m R) = (term790 A a1 m R).
Proof. exact (TRANS (@lem1226888 A a1 m R) (@lem1226911 A a1 m R)). Qed.
Lemma lem1226913 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226914 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226913 A R a1) (@lem1226912 A a1 m R)). Qed.
Lemma lem1226916 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226916 A P Q). Qed.
Lemma lem1226918 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term793 A a1 m R).
Proof. exact (@lem1226917 A (@List.ForallOrdPairs A R a1) (term789 A a1 m R)). Qed.
Lemma lem1226919 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226920 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term795 A a1 m R) = (term789 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226919 A a1 m R x)). Qed.
Lemma lem1226921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226922 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term796 A a1 m R) = (term790 A a1 m R).
Proof. exact (MK_COMB (@lem1226921 A) (@lem1226920 A a1 m R)). Qed.
Lemma lem1226923 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226924 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term792 A a1 m R) = (term791 A a1 m R).
Proof. exact (MK_COMB (@lem1226923 A R a1) (@lem1226922 A a1 m R)). Qed.
Lemma lem1226925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226926 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term797 A a1 m R) = (term798 A a1 m R).
Proof. exact (MK_COMB (@lem1226925) (@lem1226924 A a1 m R)). Qed.
Lemma lem1226927 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term794 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (eq_refl (term794 A a1 m R x)). Qed.
Lemma lem1226928 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226929 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term799 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226928 A R a1) (@lem1226927 A a1 m R x)). Qed.
Lemma lem1226930 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term801 A a1 m R) = (term802 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226929 A a1 m R x)). Qed.
Lemma lem1226931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226932 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term793 A a1 m R) = (term803 A a1 m R).
Proof. exact (MK_COMB (@lem1226931 A) (@lem1226930 A a1 m R)). Qed.
Lemma lem1226933 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term792 A a1 m R) = (term793 A a1 m R)) = ((term791 A a1 m R) = (term803 A a1 m R)).
Proof. exact (MK_COMB (@lem1226926 A a1 m R) (@lem1226932 A a1 m R)). Qed.
Lemma lem1226934 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term803 A a1 m R).
Proof. exact (EQ_MP (@lem1226933 A a1 m R) (@lem1226918 A a1 m R)). Qed.
Lemma lem1226936 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem1226937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term763 A P Q) = (term764 A P Q).
Proof. exact (@lem1226936 A P Q). Qed.
Lemma lem1226938 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term805 A a1 m R x).
Proof. exact (@lem1226937 A (@List.ForallOrdPairs A R a1) (term787 A a1 m R x)). Qed.
Lemma lem1226939 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226940 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term807 A a1 m R x) = (term787 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226939 A a1 m R x y)). Qed.
Lemma lem1226941 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226942 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term808 A a1 m R x) = (term788 A a1 m R x).
Proof. exact (MK_COMB (@lem1226941 A) (@lem1226940 A a1 m R x)). Qed.
Lemma lem1226943 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226944 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term804 A a1 m R x) = (term800 A a1 m R x).
Proof. exact (MK_COMB (@lem1226943 A R a1) (@lem1226942 A a1 m R x)). Qed.
Lemma lem1226945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226946 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term809 A a1 m R x) = (term810 A a1 m R x).
Proof. exact (MK_COMB (@lem1226945) (@lem1226944 A a1 m R x)). Qed.
Lemma lem1226947 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term806 A a1 m R x y) = (term785 A a1 m R x y).
Proof. exact (eq_refl (term806 A a1 m R x y)). Qed.
Lemma lem1226948 {A : Type'} (R : type1402 A) (a1 : list A) : (term89 A R a1) = (term89 A R a1).
Proof. exact (eq_refl (term89 A R a1)). Qed.
Lemma lem1226949 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term811 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226948 A R a1) (@lem1226947 A a1 m R x y)). Qed.
Lemma lem1226950 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term813 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226949 A a1 m R x y)). Qed.
Lemma lem1226951 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226952 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term805 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226951 A) (@lem1226950 A a1 m R x)). Qed.
Lemma lem1226953 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term804 A a1 m R x) = (term805 A a1 m R x)) = ((term800 A a1 m R x) = (term815 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226946 A a1 m R x) (@lem1226952 A a1 m R x)). Qed.
Lemma lem1226954 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term800 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (EQ_MP (@lem1226953 A a1 m R x) (@lem1226938 A a1 m R x)). Qed.
Lemma lem1226955 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term802 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226954 A a1 m R x)). Qed.
Lemma lem1226956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226957 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term803 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226956 A) (@lem1226955 A a1 m R)). Qed.
Lemma lem1226958 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term791 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226934 A a1 m R) (@lem1226957 A a1 m R)). Qed.
Lemma lem1226959 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term740 A a1 m R) = (term817 A a1 m R).
Proof. exact (TRANS (@lem1226914 A a1 m R) (@lem1226958 A a1 m R)). Qed.
Lemma lem1226960 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226961 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226960 A R a1 m) (@lem1226959 A a1 m R)). Qed.
Lemma lem1226963 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226963 A P Q). Qed.
Lemma lem1226965 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term822 A a1 m R).
Proof. exact (@lem1226964 A (term441 A R a1 m) (term816 A a1 m R)). Qed.
Lemma lem1226966 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226967 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term824 A a1 m R) = (term816 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226966 A a1 m R x)). Qed.
Lemma lem1226968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226969 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term825 A a1 m R) = (term817 A a1 m R).
Proof. exact (MK_COMB (@lem1226968 A) (@lem1226967 A a1 m R)). Qed.
Lemma lem1226970 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226971 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term821 A a1 m R) = (term818 A a1 m R).
Proof. exact (MK_COMB (@lem1226970 A R a1 m) (@lem1226969 A a1 m R)). Qed.
Lemma lem1226972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226973 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term826 A a1 m R) = (term827 A a1 m R).
Proof. exact (MK_COMB (@lem1226972) (@lem1226971 A a1 m R)). Qed.
Lemma lem1226974 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term823 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (eq_refl (term823 A a1 m R x)). Qed.
Lemma lem1226975 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226976 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term828 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226975 A R a1 m) (@lem1226974 A a1 m R x)). Qed.
Lemma lem1226977 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term830 A a1 m R) = (term831 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1226976 A a1 m R x)). Qed.
Lemma lem1226978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226979 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term822 A a1 m R) = (term832 A a1 m R).
Proof. exact (MK_COMB (@lem1226978 A) (@lem1226977 A a1 m R)). Qed.
Lemma lem1226980 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : ((term821 A a1 m R) = (term822 A a1 m R)) = ((term818 A a1 m R) = (term832 A a1 m R)).
Proof. exact (MK_COMB (@lem1226973 A a1 m R) (@lem1226979 A a1 m R)). Qed.
Lemma lem1226981 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term832 A a1 m R).
Proof. exact (EQ_MP (@lem1226980 A a1 m R) (@lem1226965 A a1 m R)). Qed.
Lemma lem1226983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1226984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term819 A P Q) = (term820 A P Q).
Proof. exact (@lem1226983 A P Q). Qed.
Lemma lem1226985 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term834 A a1 m R x).
Proof. exact (@lem1226984 A (term441 A R a1 m) (term814 A a1 m R x)). Qed.
Lemma lem1226986 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226987 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term836 A a1 m R x) = (term814 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226986 A a1 m R x y)). Qed.
Lemma lem1226988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226989 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term837 A a1 m R x) = (term815 A a1 m R x).
Proof. exact (MK_COMB (@lem1226988 A) (@lem1226987 A a1 m R x)). Qed.
Lemma lem1226990 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226991 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term833 A a1 m R x) = (term829 A a1 m R x).
Proof. exact (MK_COMB (@lem1226990 A R a1 m) (@lem1226989 A a1 m R x)). Qed.
Lemma lem1226992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1226993 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term838 A a1 m R x) = (term839 A a1 m R x).
Proof. exact (MK_COMB (@lem1226992) (@lem1226991 A a1 m R x)). Qed.
Lemma lem1226994 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term835 A a1 m R x y) = (term812 A a1 m R x y).
Proof. exact (eq_refl (term835 A a1 m R x y)). Qed.
Lemma lem1226995 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term213 A R a1 m) = (term213 A R a1 m).
Proof. exact (eq_refl (term213 A R a1 m)). Qed.
Lemma lem1226996 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term840 A a1 m R x y) = (term841 A a1 m R x y).
Proof. exact (MK_COMB (@lem1226995 A R a1 m) (@lem1226994 A a1 m R x y)). Qed.
Lemma lem1226997 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term842 A a1 m R x) = (term843 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1226996 A a1 m R x y)). Qed.
Lemma lem1226998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1226999 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term834 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (MK_COMB (@lem1226998 A) (@lem1226997 A a1 m R x)). Qed.
Lemma lem1227000 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : ((term833 A a1 m R x) = (term834 A a1 m R x)) = ((term829 A a1 m R x) = (term844 A a1 m R x)).
Proof. exact (MK_COMB (@lem1226993 A a1 m R x) (@lem1226999 A a1 m R x)). Qed.
Lemma lem1227001 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term829 A a1 m R x) = (term844 A a1 m R x).
Proof. exact (EQ_MP (@lem1227000 A a1 m R x) (@lem1226985 A a1 m R x)). Qed.
Lemma lem1227002 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term831 A a1 m R) = (term845 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1227001 A a1 m R x)). Qed.
Lemma lem1227003 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227004 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term832 A a1 m R) = (term846 A a1 m R).
Proof. exact (MK_COMB (@lem1227003 A) (@lem1227002 A a1 m R)). Qed.
Lemma lem1227005 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term818 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226981 A a1 m R) (@lem1227004 A a1 m R)). Qed.
Lemma lem1227006 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term741 A a1 m R) = (term846 A a1 m R).
Proof. exact (TRANS (@lem1226961 A a1 m R) (@lem1227005 A a1 m R)). Qed.
Lemma lem1227007 {A : Type'} (a1 : list A) (R : type1402 A) : (term742 A a1 R) = (term847 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1227006 A a1 m R)). Qed.
Lemma lem1227008 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1227009 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term848 A a1 R).
Proof. exact (MK_COMB (@lem1227008 A) (@lem1227007 A a1 R)). Qed.
Lemma lem1227035 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term849 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R a1) (term441 A R a1 m) (term785 A a1 m R x y)). Qed.
Lemma lem1227042 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term850 A a1 m R x y) = (term851 A a1 m R x y).
Proof. exact (@lem19490 (@List.ForallOrdPairs A R m) (term441 A R a1 m) (term734 A a1 m R x y)). Qed.
Lemma lem1227045 {A : Type'} (m : list A) (R : type1402 A) (a1 : list A) : (term852 A m R a1) = (term852 A m R a1).
Proof. exact (eq_refl (term852 A m R a1)). Qed.
Lemma lem1227046 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term849 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (MK_COMB (@lem1227045 A m R a1) (@lem1227042 A a1 m R x y)). Qed.
Lemma lem1227048 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term841 A a1 m R x y) = (term853 A a1 m R x y).
Proof. exact (TRANS (@lem1227035 A a1 m R x y) (@lem1227046 A a1 m R x y)). Qed.
Lemma lem1227049 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term843 A a1 m R x) = (term854 A a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1227048 A a1 m R x y)). Qed.
Lemma lem1227050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227051 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term844 A a1 m R x) = (term855 A a1 m R x).
Proof. exact (MK_COMB (@lem1227050 A) (@lem1227049 A a1 m R x)). Qed.
Lemma lem1227052 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term845 A a1 m R) = (term856 A a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1227051 A a1 m R x)). Qed.
Lemma lem1227053 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227054 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) : (term846 A a1 m R) = (term857 A a1 m R).
Proof. exact (MK_COMB (@lem1227053 A) (@lem1227052 A a1 m R)). Qed.
Lemma lem1227055 {A : Type'} (a1 : list A) (R : type1402 A) : (term847 A a1 R) = (term858 A a1 R).
Proof. exact (fun_ext (fun m : list A => @lem1227054 A a1 m R)). Qed.
Lemma lem1227056 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1227057 {A : Type'} (a1 : list A) (R : type1402 A) : (term848 A a1 R) = (term859 A a1 R).
Proof. exact (MK_COMB (@lem1227056 A) (@lem1227055 A a1 R)). Qed.
Lemma lem1227058 {A : Type'} (a1 : list A) (R : type1402 A) : (term743 A a1 R) = (term859 A a1 R).
Proof. exact (TRANS (@lem1227009 A a1 R) (@lem1227057 A a1 R)). Qed.
Lemma lem1227059 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term859 A a1 R.
Proof. exact (EQ_MP (@lem1227058 A a1 R) (@lem1225572 A x' y' a1 R h1)). Qed.
Lemma lem1227101 {A : Type'} (x : A) (a1 : list A) (h1 : @List.In A x a1) : @List.In A x a1.
Proof. exact (h1). Qed.
Lemma lem1227411 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term704 A a1 R a0 x) = (term704 A a1 R a0 x).
Proof. exact (eq_refl (term704 A a1 R a0 x)). Qed.
Lemma lem1227412 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term705 A a1 R a0) = (term705 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1227411 A a1 R a0 x)). Qed.
Lemma lem1227413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227415 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term706 A a1 R a0) = (term706 A a1 R a0).
Proof. exact (MK_COMB (@lem1227413 A) (@lem1227412 A a1 R a0)). Qed.
Lemma lem1227416 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term706 A a1 R a0.
Proof. exact (EQ_MP (@lem1227415 A a1 R a0) (@lem1225603 A x a0 a1 m R h1)). Qed.
Lemma lem1227694 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term696 A R x y) = (term696 A R x y).
Proof. exact (eq_refl (term696 A R x y)). Qed.
Lemma lem1227711 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term459 A a0 x a1 y m) = (term860 A a0 x a1 y m).
Proof. exact (@lem19699 (term861 A x a0) (term455 A x a1) (term455 A y m)). Qed.
Lemma lem1227712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1227713 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term464 A a0 x a1 y m) = (term862 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1227712) (@lem1227711 A a0 x a1 y m)). Qed.
Lemma lem1227714 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term697 A a0 a1 m R x y) = (term863 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1227713 A a0 x a1 y m) (@lem1227694 A R x y)). Qed.
Lemma lem1227721 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term863 A a0 a1 m R x y) = (term864 A a0 a1 m R x y).
Proof. exact (@lem19699 (term865 A x a0 y m) (term176 A x a1 y m) (term696 A R x y)). Qed.
Lemma lem1227722 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term697 A a0 a1 m R x y) = (term864 A a0 a1 m R x y).
Proof. exact (TRANS (@lem1227714 A a0 a1 m R x y) (@lem1227721 A a0 a1 m R x y)). Qed.
Lemma lem1227723 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term698 A a0 a1 m R x) = (term866 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1227722 A a0 a1 m R x y)). Qed.
Lemma lem1227724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227725 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term699 A a0 a1 m R x) = (term867 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1227724 A) (@lem1227723 A a0 a1 m R x)). Qed.
Lemma lem1227726 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term700 A a0 a1 m R) = (term868 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1227725 A a0 a1 m R x)). Qed.
Lemma lem1227727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1227729 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term701 A a0 a1 m R) = (term869 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1227727 A) (@lem1227726 A a0 a1 m R)). Qed.
Lemma lem1227730 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term869 A a0 a1 m R.
Proof. exact (EQ_MP (@lem1227729 A a0 a1 m R) (@lem1225600 A x a0 a1 m R h1)). Qed.
Lemma lem1227770 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term755 A a1 R x' y' m) = (term870 A a1 R x' y' m).
Proof. exact (@lem19490 (term871 A x' a1 y' m) (term253 A R m) (term750 A R x' y' m)). Qed.
Lemma lem1227771 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term872 A R x' y' m) = (term872 A R x' y' m).
Proof. exact (eq_refl (term872 A R x' y' m)). Qed.
Lemma lem1227778 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term873 A R x' a1 y' m) = (term874 A x' a1 R y' m).
Proof. exact (@lem19490 (term875 A x' m a1) (term253 A R m) (term876 A y' m)). Qed.
Lemma lem1227779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1227780 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term877 A R x' a1 y' m) = (term878 A x' a1 R y' m).
Proof. exact (MK_COMB (@lem1227779) (@lem1227778 A x' a1 R y' m)). Qed.
Lemma lem1227781 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term870 A a1 R x' y' m) = (term879 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1227780 A x' a1 R y' m) (@lem1227771 A R x' y' m)). Qed.
Lemma lem1227783 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term755 A a1 R x' y' m) = (term879 A a1 R x' y' m).
Proof. exact (TRANS (@lem1227770 A a1 R x' y' m) (@lem1227781 A a1 R x' y' m)). Qed.
Lemma lem1227786 {A : Type'} (R : type1402 A) (a1 : list A) : (term204 A R a1) = (term204 A R a1).
Proof. exact (eq_refl (term204 A R a1)). Qed.
Lemma lem1227787 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term757 A a1 R x' y' m) = (term880 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1227786 A R a1) (@lem1227783 A a1 R x' y' m)). Qed.
Lemma lem1227788 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term880 A a1 R x' y' m) = (term881 A a1 R x' y' m).
Proof. exact (@lem19490 (term874 A x' a1 R y' m) (term253 A R a1) (term872 A R x' y' m)). Qed.
Lemma lem1227789 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term882 A a1 R x' y' m) = (term882 A a1 R x' y' m).
Proof. exact (eq_refl (term882 A a1 R x' y' m)). Qed.
Lemma lem1227796 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term883 A x' a1 R y' m) = (term884 A x' a1 R y' m).
Proof. exact (@lem19490 (term885 A R x' m a1) (term253 A R a1) (term886 A R y' m)). Qed.
Lemma lem1227797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1227798 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term887 A x' a1 R y' m) = (term888 A x' a1 R y' m).
Proof. exact (MK_COMB (@lem1227797) (@lem1227796 A x' a1 R y' m)). Qed.
Lemma lem1227799 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term881 A a1 R x' y' m) = (term889 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1227798 A x' a1 R y' m) (@lem1227789 A a1 R x' y' m)). Qed.
Lemma lem1227800 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term880 A a1 R x' y' m) = (term889 A a1 R x' y' m).
Proof. exact (TRANS (@lem1227788 A a1 R x' y' m) (@lem1227799 A a1 R x' y' m)). Qed.
Lemma lem1227801 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term757 A a1 R x' y' m) = (term889 A a1 R x' y' m).
Proof. exact (TRANS (@lem1227787 A a1 R x' y' m) (@lem1227800 A a1 R x' y' m)). Qed.
Lemma lem1227804 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term216 A R a1 m) = (term216 A R a1 m).
Proof. exact (eq_refl (term216 A R a1 m)). Qed.
Lemma lem1227805 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term758 A a1 R x' y' m) = (term890 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1227804 A R a1 m) (@lem1227801 A a1 R x' y' m)). Qed.
Lemma lem1227806 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term890 A a1 R x' y' m) = (term891 A a1 R x' y' m).
Proof. exact (@lem19490 (term884 A x' a1 R y' m) (term112 A R a1 m) (term882 A a1 R x' y' m)). Qed.
Lemma lem1227807 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term892 A a1 R x' y' m) = (term892 A a1 R x' y' m).
Proof. exact (eq_refl (term892 A a1 R x' y' m)). Qed.
Lemma lem1227814 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term893 A x' a1 R y' m) = (term894 A x' a1 R y' m).
Proof. exact (@lem19490 (term895 A R x' m a1) (term112 A R a1 m) (term896 A a1 R y' m)). Qed.
Lemma lem1227815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1227816 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (y' : type1141 A) (m : list A) : (term897 A x' a1 R y' m) = (term898 A x' a1 R y' m).
Proof. exact (MK_COMB (@lem1227815) (@lem1227814 A x' a1 R y' m)). Qed.
Lemma lem1227817 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term891 A a1 R x' y' m) = (term899 A a1 R x' y' m).
Proof. exact (MK_COMB (@lem1227816 A x' a1 R y' m) (@lem1227807 A a1 R x' y' m)). Qed.
Lemma lem1227818 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term890 A a1 R x' y' m) = (term899 A a1 R x' y' m).
Proof. exact (TRANS (@lem1227806 A a1 R x' y' m) (@lem1227817 A a1 R x' y' m)). Qed.
Lemma lem1227819 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term758 A a1 R x' y' m) = (term899 A a1 R x' y' m).
Proof. exact (TRANS (@lem1227805 A a1 R x' y' m) (@lem1227818 A a1 R x' y' m)). Qed.
Lemma lem1227820 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) : (term759 A a1 R x' y') = (term900 A a1 R x' y').
Proof. exact (fun_ext (fun m : list A => @lem1227819 A a1 R x' y' m)). Qed.
Lemma lem1227821 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1227823 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) : (term760 A a1 R x' y') = (term901 A a1 R x' y').
Proof. exact (MK_COMB (@lem1227821 A) (@lem1227820 A a1 R x' y')). Qed.
Lemma lem1227824 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term901 A a1 R x' y'.
Proof. exact (EQ_MP (@lem1227823 A a1 R x' y') (@lem1225573 A x' y' a1 R h1)). Qed.
Lemma lem1228021 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term696 A R x y) = (term696 A R x y).
Proof. exact (eq_refl (term696 A R x y)). Qed.
Lemma lem1228038 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term459 A a0 x a1 y m) = (term860 A a0 x a1 y m).
Proof. exact (@lem19699 (term861 A x a0) (term455 A x a1) (term455 A y m)). Qed.
Lemma lem1228039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1228040 {A : Type'} (a0 : A) (x : A) (a1 : list A) (y : A) (m : list A) : (term464 A a0 x a1 y m) = (term862 A a0 x a1 y m).
Proof. exact (MK_COMB (@lem1228039) (@lem1228038 A a0 x a1 y m)). Qed.
Lemma lem1228041 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term697 A a0 a1 m R x y) = (term863 A a0 a1 m R x y).
Proof. exact (MK_COMB (@lem1228040 A a0 x a1 y m) (@lem1228021 A R x y)). Qed.
Lemma lem1228048 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term863 A a0 a1 m R x y) = (term864 A a0 a1 m R x y).
Proof. exact (@lem19699 (term865 A x a0 y m) (term176 A x a1 y m) (term696 A R x y)). Qed.
Lemma lem1228049 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) : (term697 A a0 a1 m R x y) = (term864 A a0 a1 m R x y).
Proof. exact (TRANS (@lem1228041 A a0 a1 m R x y) (@lem1228048 A a0 a1 m R x y)). Qed.
Lemma lem1228050 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term698 A a0 a1 m R x) = (term866 A a0 a1 m R x).
Proof. exact (fun_ext (fun y : A => @lem1228049 A a0 a1 m R x y)). Qed.
Lemma lem1228051 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1228052 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) : (term699 A a0 a1 m R x) = (term867 A a0 a1 m R x).
Proof. exact (MK_COMB (@lem1228051 A) (@lem1228050 A a0 a1 m R x)). Qed.
Lemma lem1228053 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term700 A a0 a1 m R) = (term868 A a0 a1 m R).
Proof. exact (fun_ext (fun x : A => @lem1228052 A a0 a1 m R x)). Qed.
Lemma lem1228054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1228056 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) : (term701 A a0 a1 m R) = (term869 A a0 a1 m R).
Proof. exact (MK_COMB (@lem1228054 A) (@lem1228053 A a0 a1 m R)). Qed.
Lemma lem1228057 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term869 A a0 a1 m R.
Proof. exact (EQ_MP (@lem1228056 A a0 a1 m R) (@lem1225600 A x a0 a1 m R h1)). Qed.
Lemma lem1228078 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (h1). Qed.
Lemma lem1228091 {A : Type'} (_22404 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term902 A a1 R a0 _22404.
Proof. exact (@lem1225888 A a0 a1 m R x y h1 _22404). Qed.
Lemma lem1228092 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22404 : A) : (term902 A a1 R a0 _22404) = (term704 A a1 R a0 _22404).
Proof. exact (eq_refl (term902 A a1 R a0 _22404)). Qed.
Lemma lem1228100 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term903 A a1 R _22407.
Proof. exact (@lem1226169 A x' y' a1 R h1 _22407). Qed.
Lemma lem1228101 {A : Type'} (a1 : list A) (_22407 : list A) (R : type1402 A) : (term903 A a1 R _22407) = (term857 A a1 _22407 R).
Proof. exact (eq_refl (term903 A a1 R _22407)). Qed.
Lemma lem1228102 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term857 A a1 _22407 R.
Proof. exact (EQ_MP (@lem1228101 A a1 _22407 R) (@lem1228100 A _22407 x' y' a1 R h1)). Qed.
Lemma lem1228103 {A : Type'} (_22407 : list A) (_22408 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term904 A a1 _22407 R _22408.
Proof. exact (@lem1228102 A _22407 x' y' a1 R h1 _22408). Qed.
Lemma lem1228104 {A : Type'} (a1 : list A) (_22407 : list A) (R : type1402 A) (_22408 : A) : (term904 A a1 _22407 R _22408) = (term855 A a1 _22407 R _22408).
Proof. exact (eq_refl (term904 A a1 _22407 R _22408)). Qed.
Lemma lem1228105 {A : Type'} (_22407 : list A) (_22408 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term855 A a1 _22407 R _22408.
Proof. exact (EQ_MP (@lem1228104 A a1 _22407 R _22408) (@lem1228103 A _22407 _22408 x' y' a1 R h1)). Qed.
Lemma lem1228106 {A : Type'} (_22407 : list A) (_22408 : A) (_22409 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term905 A a1 _22407 R _22408 _22409.
Proof. exact (@lem1228105 A _22407 _22408 x' y' a1 R h1 _22409). Qed.
Lemma lem1228107 {A : Type'} (a1 : list A) (_22407 : list A) (R : type1402 A) (_22408 : A) (_22409 : A) : (term905 A a1 _22407 R _22408 _22409) = (term853 A a1 _22407 R _22408 _22409).
Proof. exact (eq_refl (term905 A a1 _22407 R _22408 _22409)). Qed.
Lemma lem1228108 {A : Type'} (_22407 : list A) (_22408 : A) (_22409 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term853 A a1 _22407 R _22408 _22409.
Proof. exact (EQ_MP (@lem1228107 A a1 _22407 R _22408 _22409) (@lem1228106 A _22407 _22408 _22409 x' y' a1 R h1)). Qed.
Lemma lem1228118 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term903 A a1 R _22413.
Proof. exact (@lem1226463 A x' y' a1 R h1 _22413). Qed.
Lemma lem1228119 {A : Type'} (a1 : list A) (_22413 : list A) (R : type1402 A) : (term903 A a1 R _22413) = (term857 A a1 _22413 R).
Proof. exact (eq_refl (term903 A a1 R _22413)). Qed.
Lemma lem1228120 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term857 A a1 _22413 R.
Proof. exact (EQ_MP (@lem1228119 A a1 _22413 R) (@lem1228118 A _22413 x' y' a1 R h1)). Qed.
Lemma lem1228121 {A : Type'} (_22413 : list A) (_22414 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term904 A a1 _22413 R _22414.
Proof. exact (@lem1228120 A _22413 x' y' a1 R h1 _22414). Qed.
Lemma lem1228122 {A : Type'} (a1 : list A) (_22413 : list A) (R : type1402 A) (_22414 : A) : (term904 A a1 _22413 R _22414) = (term855 A a1 _22413 R _22414).
Proof. exact (eq_refl (term904 A a1 _22413 R _22414)). Qed.
Lemma lem1228123 {A : Type'} (_22413 : list A) (_22414 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term855 A a1 _22413 R _22414.
Proof. exact (EQ_MP (@lem1228122 A a1 _22413 R _22414) (@lem1228121 A _22413 _22414 x' y' a1 R h1)). Qed.
Lemma lem1228124 {A : Type'} (_22413 : list A) (_22414 : A) (_22415 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term905 A a1 _22413 R _22414 _22415.
Proof. exact (@lem1228123 A _22413 _22414 x' y' a1 R h1 _22415). Qed.
Lemma lem1228125 {A : Type'} (a1 : list A) (_22413 : list A) (R : type1402 A) (_22414 : A) (_22415 : A) : (term905 A a1 _22413 R _22414 _22415) = (term853 A a1 _22413 R _22414 _22415).
Proof. exact (eq_refl (term905 A a1 _22413 R _22414 _22415)). Qed.
Lemma lem1228126 {A : Type'} (_22413 : list A) (_22414 : A) (_22415 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term853 A a1 _22413 R _22414 _22415.
Proof. exact (EQ_MP (@lem1228125 A a1 _22413 R _22414 _22415) (@lem1228124 A _22413 _22414 _22415 x' y' a1 R h1)). Qed.
Lemma lem1228148 {A : Type'} (_22423 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term902 A m R a0 _22423.
Proof. exact (@lem1226787 A a0 a1 m R x y h1 _22423). Qed.
Lemma lem1228149 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (_22423 : A) : (term902 A m R a0 _22423) = (term704 A m R a0 _22423).
Proof. exact (eq_refl (term902 A m R a0 _22423)). Qed.
Lemma lem1228154 {A : Type'} (_22425 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term903 A a1 R _22425.
Proof. exact (@lem1227059 A x' y' a1 R h1 _22425). Qed.
Lemma lem1228155 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) : (term903 A a1 R _22425) = (term857 A a1 _22425 R).
Proof. exact (eq_refl (term903 A a1 R _22425)). Qed.
Lemma lem1228156 {A : Type'} (_22425 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term857 A a1 _22425 R.
Proof. exact (EQ_MP (@lem1228155 A a1 _22425 R) (@lem1228154 A _22425 x' y' a1 R h1)). Qed.
Lemma lem1228157 {A : Type'} (_22425 : list A) (_22426 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term904 A a1 _22425 R _22426.
Proof. exact (@lem1228156 A _22425 x' y' a1 R h1 _22426). Qed.
Lemma lem1228158 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) : (term904 A a1 _22425 R _22426) = (term855 A a1 _22425 R _22426).
Proof. exact (eq_refl (term904 A a1 _22425 R _22426)). Qed.
Lemma lem1228159 {A : Type'} (_22425 : list A) (_22426 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term855 A a1 _22425 R _22426.
Proof. exact (EQ_MP (@lem1228158 A a1 _22425 R _22426) (@lem1228157 A _22425 _22426 x' y' a1 R h1)). Qed.
Lemma lem1228160 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term905 A a1 _22425 R _22426 _22427.
Proof. exact (@lem1228159 A _22425 _22426 x' y' a1 R h1 _22427). Qed.
Lemma lem1228161 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term905 A a1 _22425 R _22426 _22427) = (term853 A a1 _22425 R _22426 _22427).
Proof. exact (eq_refl (term905 A a1 _22425 R _22426 _22427)). Qed.
Lemma lem1228162 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term853 A a1 _22425 R _22426 _22427.
Proof. exact (EQ_MP (@lem1228161 A a1 _22425 R _22426 _22427) (@lem1228160 A _22425 _22426 _22427 x' y' a1 R h1)). Qed.
Lemma lem1228187 {A : Type'} (_22436 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term902 A a1 R a0 _22436.
Proof. exact (@lem1227416 A x a0 a1 m R h1 _22436). Qed.
Lemma lem1228188 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22436 : A) : (term902 A a1 R a0 _22436) = (term704 A a1 R a0 _22436).
Proof. exact (eq_refl (term902 A a1 R a0 _22436)). Qed.
Lemma lem1228202 {A : Type'} (_22441 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term906 A a0 a1 m R _22441.
Proof. exact (@lem1227730 A x a0 a1 m R h1 _22441). Qed.
Lemma lem1228203 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (_22441 : A) : (term906 A a0 a1 m R _22441) = (term867 A a0 a1 m R _22441).
Proof. exact (eq_refl (term906 A a0 a1 m R _22441)). Qed.
Lemma lem1228204 {A : Type'} (_22441 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term867 A a0 a1 m R _22441.
Proof. exact (EQ_MP (@lem1228203 A a0 a1 m R _22441) (@lem1228202 A _22441 x a0 a1 m R h1)). Qed.
Lemma lem1228205 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term907 A a0 a1 m R _22441 _22442.
Proof. exact (@lem1228204 A _22441 x a0 a1 m R h1 _22442). Qed.
Lemma lem1228206 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (_22441 : A) (_22442 : A) : (term907 A a0 a1 m R _22441 _22442) = (term864 A a0 a1 m R _22441 _22442).
Proof. exact (eq_refl (term907 A a0 a1 m R _22441 _22442)). Qed.
Lemma lem1228207 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term864 A a0 a1 m R _22441 _22442.
Proof. exact (EQ_MP (@lem1228206 A a0 a1 m R _22441 _22442) (@lem1228205 A _22441 _22442 x a0 a1 m R h1)). Qed.
Lemma lem1228211 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term908 A a1 R x' y' _22444.
Proof. exact (@lem1227824 A x' y' a1 R h1 _22444). Qed.
Lemma lem1228212 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term908 A a1 R x' y' _22444) = (term899 A a1 R x' y' _22444).
Proof. exact (eq_refl (term908 A a1 R x' y' _22444)). Qed.
Lemma lem1228213 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term899 A a1 R x' y' _22444.
Proof. exact (EQ_MP (@lem1228212 A a1 R x' y' _22444) (@lem1228211 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1228223 {A : Type'} (_22448 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term906 A a0 a1 m R _22448.
Proof. exact (@lem1228057 A x a0 a1 m R h1 _22448). Qed.
Lemma lem1228224 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (_22448 : A) : (term906 A a0 a1 m R _22448) = (term867 A a0 a1 m R _22448).
Proof. exact (eq_refl (term906 A a0 a1 m R _22448)). Qed.
Lemma lem1228225 {A : Type'} (_22448 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term867 A a0 a1 m R _22448.
Proof. exact (EQ_MP (@lem1228224 A a0 a1 m R _22448) (@lem1228223 A _22448 x a0 a1 m R h1)). Qed.
Lemma lem1228226 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term907 A a0 a1 m R _22448 _22449.
Proof. exact (@lem1228225 A _22448 x a0 a1 m R h1 _22449). Qed.
Lemma lem1228227 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term907 A a0 a1 m R _22448 _22449) = (term864 A a0 a1 m R _22448 _22449).
Proof. exact (eq_refl (term907 A a0 a1 m R _22448 _22449)). Qed.
Lemma lem1228228 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term864 A a0 a1 m R _22448 _22449.
Proof. exact (EQ_MP (@lem1228227 A a0 a1 m R _22448 _22449) (@lem1228226 A _22448 _22449 x a0 a1 m R h1)). Qed.
Lemma lem1228248 {A : Type'} (_22413 : list A) (_22414 : A) (_22415 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term851 A a1 _22413 R _22414 _22415.
Proof. exact (proj2 (@lem1228126 A _22413 _22414 _22415 x' y' a1 R h1)). Qed.
Lemma lem1228264 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term851 A a1 _22425 R _22426 _22427.
Proof. exact (proj2 (@lem1228162 A _22425 _22426 _22427 x' y' a1 R h1)). Qed.
Lemma lem1228266 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term909 A a1 _22425 R _22426 _22427.
Proof. exact (proj2 (@lem1228264 A _22425 _22426 _22427 x' y' a1 R h1)). Qed.
Lemma lem1228283 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term910 A a0 m R _22441 _22442.
Proof. exact (proj1 (@lem1228207 A _22441 _22442 x a0 a1 m R h1)). Qed.
Lemma lem1228292 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term734 A a1 m R _22448 _22449.
Proof. exact (proj2 (@lem1228228 A _22448 _22449 x a0 a1 m R h1)). Qed.
Lemma lem1228299 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term894 A x' a1 R y' _22444.
Proof. exact (proj1 (@lem1228213 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1228309 {A : Type'} (_22404 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term704 A a1 R a0 _22404.
Proof. exact (EQ_MP (@lem1228092 A a1 R a0 _22404) (@lem1228091 A _22404 a0 a1 m R x y h1)). Qed.
Lemma lem1228319 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term712 A R a0 x.
Proof. exact (proj2 (@lem1225584 A a1 R a0 x h1)). Qed.
Lemma lem1228405 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term253 A R a1) : term253 A R a1.
Proof. exact (h1). Qed.
Lemma lem1228411 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term911 A _22407 R a1.
Proof. exact (proj1 (@lem1228108 A _22407 (@el A) (@el A) x' y' a1 R h1)). Qed.
Lemma lem1228491 {A : Type'} (R : type1402 A) (m : list A) (h1 : term253 A R m) : term253 A R m.
Proof. exact (h1). Qed.
Lemma lem1228503 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term912 A a1 R _22413.
Proof. exact (proj1 (@lem1228248 A _22413 (@el A) (@el A) x' y' a1 R h1)). Qed.
Lemma lem1228577 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term712 A R x y.
Proof. exact (proj2 (@lem1225589 A a0 a1 m R x y h1)). Qed.
Lemma lem1228581 {A : Type'} (x : A) (a0 : A) (h1 : x = a0) : x = a0.
Proof. exact (h1). Qed.
Lemma lem1228667 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term712 A R x y.
Proof. exact (proj2 (@lem1225589 A a0 a1 m R x y h1)). Qed.
Lemma lem1228671 {A : Type'} (x : A) (a1 : list A) (h1 : @List.In A x a1) : @List.In A x a1.
Proof. exact (h1). Qed.
Lemma lem1228694 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term734 A a1 _22425 R _22426 _22427) = (term913 A a1 _22425 R _22426 _22427).
Proof. exact (@lem1222749 (term455 A _22426 a1) (term455 A _22427 _22425) (term696 A R _22426 _22427)). Qed.
Lemma lem1228695 {A : Type'} (R : type1402 A) (a1 : list A) (_22425 : list A) : (term213 A R a1 _22425) = (term213 A R a1 _22425).
Proof. exact (eq_refl (term213 A R a1 _22425)). Qed.
Lemma lem1228698 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term909 A a1 _22425 R _22426 _22427) = (term914 A a1 _22425 R _22426 _22427).
Proof. exact (MK_COMB (@lem1228695 A R a1 _22425) (@lem1228694 A a1 _22425 R _22426 _22427)). Qed.
Lemma lem1228699 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term914 A a1 _22425 R _22426 _22427.
Proof. exact (EQ_MP (@lem1228698 A a1 _22425 R _22426 _22427) (@lem1228266 A _22425 _22426 _22427 x' y' a1 R h1)). Qed.
Lemma lem1228749 {A : Type'} (_22436 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term704 A a1 R a0 _22436.
Proof. exact (EQ_MP (@lem1228188 A a1 R a0 _22436) (@lem1228187 A _22436 x a0 a1 m R h1)). Qed.
Lemma lem1228755 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term712 A R a0 x.
Proof. exact (proj2 (@lem1225606 A a1 R a0 x h1)). Qed.
Lemma lem1228863 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : term712 A R a0 x.
Proof. exact (proj2 (@lem1225607 A m R a0 x h1)). Qed.
Lemma lem1228874 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (_22441 : A) (_22442 : A) : (term910 A a0 m R _22441 _22442) = (term915 A a0 m R _22441 _22442).
Proof. exact (@lem1222749 (term861 A _22441 a0) (term455 A _22442 m) (term696 A R _22441 _22442)). Qed.
Lemma lem1228875 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term915 A a0 m R _22441 _22442.
Proof. exact (EQ_MP (@lem1228874 A a0 m R _22441 _22442) (@lem1228283 A _22441 _22442 x a0 a1 m R h1)). Qed.
Lemma lem1228969 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (h1). Qed.
Lemma lem1228992 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term734 A a1 m R _22448 _22449) = (term913 A a1 m R _22448 _22449).
Proof. exact (@lem1222749 (term455 A _22448 a1) (term455 A _22449 m) (term696 A R _22448 _22449)). Qed.
Lemma lem1228993 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term913 A a1 m R _22448 _22449.
Proof. exact (EQ_MP (@lem1228992 A a1 m R _22448 _22449) (@lem1228292 A _22448 _22449 x a0 a1 m R h1)). Qed.
Lemma lem1229035 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term892 A a1 R x' y' _22444.
Proof. exact (proj2 (@lem1228213 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1229049 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term916 A R x' _22444 a1.
Proof. exact (proj1 (@lem1228299 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1229063 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term917 A a1 R y' _22444.
Proof. exact (proj2 (@lem1228299 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1229119 {A : Type'} (_22423 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term704 A m R a0 _22423.
Proof. exact (EQ_MP (@lem1228149 A m R a0 _22423) (@lem1228148 A _22423 a0 a1 m R x y h1)). Qed.
Lemma lem1229120 {A : Type'} (R : type1402 A) (y : A) : (term918 A R y) = (term918 A R y).
Proof. exact (eq_refl (term918 A R y)). Qed.
Lemma lem1229121 {A : Type'} (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : x = a0) : (term919 A R y x) = (term919 A R y a0).
Proof. exact (MK_COMB (@lem1229120 A R y) (@lem1228581 A x a0 h1)). Qed.
Lemma lem1229122 {A : Type'} (R : type1402 A) (a0 : A) (y : A) : (term919 A R y a0) = (term712 A R a0 y).
Proof. exact (eq_refl (term919 A R y a0)). Qed.
Lemma lem1229123 {A : Type'} (R : type1402 A) (y : A) (x : A) : (term920 A R y x) = (term920 A R y x).
Proof. exact (eq_refl (term920 A R y x)). Qed.
Lemma lem1229124 {A : Type'} (x : A) (R : type1402 A) (a0 : A) (y : A) : ((term919 A R y x) = (term919 A R y a0)) = ((term919 A R y x) = (term712 A R a0 y)).
Proof. exact (MK_COMB (@lem1229123 A R y x) (@lem1229122 A R a0 y)). Qed.
Lemma lem1229125 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term919 A R y x) = (term712 A R x y).
Proof. exact (eq_refl (term919 A R y x)). Qed.
Lemma lem1229126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229127 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term920 A R y x) = (term921 A R x y).
Proof. exact (MK_COMB (@lem1229126) (@lem1229125 A R x y)). Qed.
Lemma lem1229128 {A : Type'} (R : type1402 A) (a0 : A) (y : A) : (term712 A R a0 y) = (term712 A R a0 y).
Proof. exact (eq_refl (term712 A R a0 y)). Qed.
Lemma lem1229129 {A : Type'} (x : A) (R : type1402 A) (a0 : A) (y : A) : ((term919 A R y x) = (term712 A R a0 y)) = ((term712 A R x y) = (term712 A R a0 y)).
Proof. exact (MK_COMB (@lem1229127 A R x y) (@lem1229128 A R a0 y)). Qed.
Lemma lem1229130 {A : Type'} (x : A) (R : type1402 A) (a0 : A) (y : A) : ((term919 A R y x) = (term919 A R y a0)) = ((term712 A R x y) = (term712 A R a0 y)).
Proof. exact (TRANS (@lem1229124 A x R a0 y) (@lem1229129 A x R a0 y)). Qed.
Lemma lem1229131 {A : Type'} (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : x = a0) : (term712 A R x y) = (term712 A R a0 y).
Proof. exact (EQ_MP (@lem1229130 A x R a0 y) (@lem1229121 A R y x a0 h1)). Qed.
Lemma lem1229132 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term722 A a0 a1 m R x y) (h2 : x = a0) : term712 A R a0 y.
Proof. exact (EQ_MP (@lem1229131 A R y x a0 h2) (@lem1228577 A a0 a1 m R x y h1)). Qed.
Lemma lem1229232 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : @List.In A x a1.
Proof. exact (proj1 (@lem1225584 A a1 R a0 x h1)). Qed.
Lemma lem1229233 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term922 A x a1.
Proof. exact (fun h0 : term455 A x a1 => @lem1229232 A a1 R a0 x h1). Qed.
Lemma lem1229235 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229236 {A : Type'} (x : A) (a1 : list A) : (term922 A x a1) = (@List.In A x a1).
Proof. exact (@lem1229235 (@List.In A x a1)). Qed.
Lemma lem1229237 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : @List.In A x a1.
Proof. exact (EQ_MP (@lem1229236 A x a1) (@lem1229233 A a1 R a0 x h1)). Qed.
Lemma lem1229243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229244 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : (term704 A a1 R a0 _22404) = (term924 A R a0 _22404 a1).
Proof. exact (@lem1229243 (term696 A R a0 _22404) (term455 A _22404 a1)). Qed.
Lemma lem1229250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229251 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : (term925 A a1 R a0 _22404) = (term926 A R a0 _22404 a1).
Proof. exact (MK_COMB (@lem1229250) (@lem1229244 A R a0 _22404 a1)). Qed.
Lemma lem1229257 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : (term924 A R a0 _22404 a1) = (term924 A R a0 _22404 a1).
Proof. exact (eq_refl (term924 A R a0 _22404 a1)). Qed.
Lemma lem1229258 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : ((term704 A a1 R a0 _22404) = (term924 A R a0 _22404 a1)) = ((term924 A R a0 _22404 a1) = (term924 A R a0 _22404 a1)).
Proof. exact (MK_COMB (@lem1229251 A R a0 _22404 a1) (@lem1229257 A R a0 _22404 a1)). Qed.
Lemma lem1229260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229261 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229260 Prop x). Qed.
Lemma lem1229262 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : ((term924 A R a0 _22404 a1) = (term924 A R a0 _22404 a1)) = True.
Proof. exact (@lem1229261 (term924 A R a0 _22404 a1)). Qed.
Lemma lem1229263 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : ((term704 A a1 R a0 _22404) = (term924 A R a0 _22404 a1)) = True.
Proof. exact (TRANS (@lem1229258 A R a0 _22404 a1) (@lem1229262 A R a0 _22404 a1)). Qed.
Lemma lem1229264 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : True = ((term704 A a1 R a0 _22404) = (term924 A R a0 _22404 a1)).
Proof. exact (SYM (@lem1229263 A R a0 _22404 a1)). Qed.
Lemma lem1229265 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) (a1 : list A) : (term704 A a1 R a0 _22404) = (term924 A R a0 _22404 a1).
Proof. exact (EQ_MP (@lem1229264 A R a0 _22404 a1) (@lem0)). Qed.
Lemma lem1229266 {A : Type'} (_22404 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term924 A R a0 _22404 a1.
Proof. exact (EQ_MP (@lem1229265 A R a0 _22404 a1) (@lem1228309 A _22404 a0 a1 m R x y h1)). Qed.
Lemma lem1229268 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229269 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22404 : A) : (term924 A R a0 _22404 a1) = (term928 A a1 R a0 _22404).
Proof. exact (@lem1229268 (term455 A _22404 a1) (term696 A R a0 _22404)). Qed.
Lemma lem1229271 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229272 {A : Type'} (_22404 : A) (a1 : list A) : (term929 A _22404 a1) = (@List.In A _22404 a1).
Proof. exact (@lem1229271 (@List.In A _22404 a1)). Qed.
Lemma lem1229273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229274 {A : Type'} (_22404 : A) (a1 : list A) : (term930 A _22404 a1) = (term931 A _22404 a1).
Proof. exact (MK_COMB (@lem1229273) (@lem1229272 A _22404 a1)). Qed.
Lemma lem1229275 {A : Type'} (R : type1402 A) (a0 : A) (_22404 : A) : (term696 A R a0 _22404) = (term696 A R a0 _22404).
Proof. exact (eq_refl (term696 A R a0 _22404)). Qed.
Lemma lem1229276 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22404 : A) : (term928 A a1 R a0 _22404) = (term932 A a1 R a0 _22404).
Proof. exact (MK_COMB (@lem1229274 A _22404 a1) (@lem1229275 A R a0 _22404)). Qed.
Lemma lem1229277 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22404 : A) : (term924 A R a0 _22404 a1) = (term932 A a1 R a0 _22404).
Proof. exact (TRANS (@lem1229269 A a1 R a0 _22404) (@lem1229276 A a1 R a0 _22404)). Qed.
Lemma lem1229280 {A : Type'} (_22404 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A a1 R a0 _22404.
Proof. exact (EQ_MP (@lem1229277 A a1 R a0 _22404) (@lem1229266 A _22404 a0 a1 m R x y h1)). Qed.
Lemma lem1229281 {A : Type'} (_22404 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A a1 R a0 _22404.
Proof. exact (@lem1229280 A _22404 a0 a1 m R x y h1). Qed.
Lemma lem1229282 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A a1 R a0 x.
Proof. exact (@lem1229281 A x a0 a1 m R x y h1). Qed.
Lemma lem1229285 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : term696 A R a0 x.
Proof. exact (@lem1229282 A a0 a1 m R x y h1 (@lem1229237 A a1 R a0 x h2)). Qed.
Lemma lem1229286 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : term933 A R a0 x.
Proof. exact (fun h0 : term712 A R a0 x => @lem1229285 A m y a1 R a0 x h1 h2). Qed.
Lemma lem1229288 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229289 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term933 A R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1229288 (term696 A R a0 x)). Qed.
Lemma lem1229290 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : term696 A R a0 x.
Proof. exact (EQ_MP (@lem1229289 A R a0 x) (@lem1229286 A m y a1 R a0 x h1 h2)). Qed.
Lemma lem1229293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229295 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term712 A R a0 x) = (term934 A R a0 x).
Proof. exact (@lem1229293 (term696 A R a0 x)). Qed.
Lemma lem1229298 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term934 A R a0 x.
Proof. exact (EQ_MP (@lem1229295 A R a0 x) (@lem1228319 A a1 R a0 x h1)). Qed.
Lemma lem1229301 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : False.
Proof. exact (@lem1229298 A a1 R a0 x h2 (@lem1229290 A m y a1 R a0 x h1 h2)). Qed.
Lemma lem1229302 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : term935.
Proof. exact (fun h0 : ~ False => @lem1229301 A m y a1 R a0 x h1 h2). Qed.
Lemma lem1229304 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229305 : term935 = False.
Proof. exact (@lem1229304 False). Qed.
Lemma lem1229306 {A : Type'} (m : list A) (y : A) (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term731 A a0 a1 m R x y) (h2 : term714 A a1 R a0 x) : False.
Proof. exact (EQ_MP (@lem1229305) (@lem1229302 A m y a1 R a0 x h1 h2)). Qed.
Lemma lem1229308 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (proj2 (@lem1225577 A a0 a1 m R x y h1)). Qed.
Lemma lem1229309 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term936 A R a1 m.
Proof. exact (fun h0 : term441 A R a1 m => @lem1229308 A a0 a1 m R x y h1). Qed.
Lemma lem1229311 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229312 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term936 A R a1 m) = (term112 A R a1 m).
Proof. exact (@lem1229311 (term112 A R a1 m)). Qed.
Lemma lem1229313 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (EQ_MP (@lem1229312 A R a1 m) (@lem1229309 A a0 a1 m R x y h1)). Qed.
Lemma lem1229319 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229320 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term911 A _22407 R a1) = (term937 A R a1 _22407).
Proof. exact (@lem1229319 (@List.ForallOrdPairs A R a1) (term441 A R a1 _22407)). Qed.
Lemma lem1229326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229327 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term938 A _22407 R a1) = (term939 A R a1 _22407).
Proof. exact (MK_COMB (@lem1229326) (@lem1229320 A R a1 _22407)). Qed.
Lemma lem1229333 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term937 A R a1 _22407) = (term937 A R a1 _22407).
Proof. exact (eq_refl (term937 A R a1 _22407)). Qed.
Lemma lem1229334 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : ((term911 A _22407 R a1) = (term937 A R a1 _22407)) = ((term937 A R a1 _22407) = (term937 A R a1 _22407)).
Proof. exact (MK_COMB (@lem1229327 A R a1 _22407) (@lem1229333 A R a1 _22407)). Qed.
Lemma lem1229336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229337 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229336 Prop x). Qed.
Lemma lem1229338 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : ((term937 A R a1 _22407) = (term937 A R a1 _22407)) = True.
Proof. exact (@lem1229337 (term937 A R a1 _22407)). Qed.
Lemma lem1229339 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : ((term911 A _22407 R a1) = (term937 A R a1 _22407)) = True.
Proof. exact (TRANS (@lem1229334 A R a1 _22407) (@lem1229338 A R a1 _22407)). Qed.
Lemma lem1229340 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : True = ((term911 A _22407 R a1) = (term937 A R a1 _22407)).
Proof. exact (SYM (@lem1229339 A R a1 _22407)). Qed.
Lemma lem1229341 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term911 A _22407 R a1) = (term937 A R a1 _22407).
Proof. exact (EQ_MP (@lem1229340 A R a1 _22407) (@lem0)). Qed.
Lemma lem1229342 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term937 A R a1 _22407.
Proof. exact (EQ_MP (@lem1229341 A R a1 _22407) (@lem1228411 A _22407 x' y' a1 R h1)). Qed.
Lemma lem1229344 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229345 {A : Type'} (_22407 : list A) (R : type1402 A) (a1 : list A) : (term937 A R a1 _22407) = (term940 A _22407 R a1).
Proof. exact (@lem1229344 (term441 A R a1 _22407) (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1229347 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229348 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term941 A R a1 _22407) = (term112 A R a1 _22407).
Proof. exact (@lem1229347 (term112 A R a1 _22407)). Qed.
Lemma lem1229349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229350 {A : Type'} (R : type1402 A) (a1 : list A) (_22407 : list A) : (term942 A R a1 _22407) = (term943 A R a1 _22407).
Proof. exact (MK_COMB (@lem1229349) (@lem1229348 A R a1 _22407)). Qed.
Lemma lem1229351 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1229352 {A : Type'} (_22407 : list A) (R : type1402 A) (a1 : list A) : (term940 A _22407 R a1) = (term944 A _22407 R a1).
Proof. exact (MK_COMB (@lem1229350 A R a1 _22407) (@lem1229351 A R a1)). Qed.
Lemma lem1229353 {A : Type'} (_22407 : list A) (R : type1402 A) (a1 : list A) : (term937 A R a1 _22407) = (term944 A _22407 R a1).
Proof. exact (TRANS (@lem1229345 A _22407 R a1) (@lem1229352 A _22407 R a1)). Qed.
Lemma lem1229356 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term944 A _22407 R a1.
Proof. exact (EQ_MP (@lem1229353 A _22407 R a1) (@lem1229342 A _22407 x' y' a1 R h1)). Qed.
Lemma lem1229357 {A : Type'} (_22407 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term944 A _22407 R a1.
Proof. exact (@lem1229356 A _22407 x' y' a1 R h1). Qed.
Lemma lem1229358 {A : Type'} (m : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term944 A m R a1.
Proof. exact (@lem1229357 A m x' y' a1 R h1). Qed.
Lemma lem1229361 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : @List.ForallOrdPairs A R a1.
Proof. exact (@lem1229358 A m x' y' a1 R h1 (@lem1229313 A a0 a1 m R x y h2)). Qed.
Lemma lem1229362 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : term945 A R a1.
Proof. exact (fun h0 : term253 A R a1 => @lem1229361 A x' y' a0 a1 m R x y h1 h2). Qed.
Lemma lem1229364 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229365 {A : Type'} (R : type1402 A) (a1 : list A) : (term945 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1229364 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1229366 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1229365 A R a1) (@lem1229362 A x' y' a0 a1 m R x y h1 h2)). Qed.
Lemma lem1229369 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229371 {A : Type'} (R : type1402 A) (a1 : list A) : (term253 A R a1) = (term946 A R a1).
Proof. exact (@lem1229369 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1229374 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term253 A R a1) : term946 A R a1.
Proof. exact (EQ_MP (@lem1229371 A R a1) (@lem1228405 A R a1 h1)). Qed.
Lemma lem1229377 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (@lem1229374 A R a1 h1 (@lem1229366 A x' y' a0 a1 m R x y h2 h3)). Qed.
Lemma lem1229378 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : term935.
Proof. exact (fun h0 : ~ False => @lem1229377 A x' y' a0 a1 m R x y h1 h2 h3). Qed.
Lemma lem1229380 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229381 : term935 = False.
Proof. exact (@lem1229380 False). Qed.
Lemma lem1229382 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1229381) (@lem1229378 A x' y' a0 a1 m R x y h1 h2 h3)). Qed.
Lemma lem1229384 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (proj2 (@lem1225577 A a0 a1 m R x y h1)). Qed.
Lemma lem1229385 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term936 A R a1 m.
Proof. exact (fun h0 : term441 A R a1 m => @lem1229384 A a0 a1 m R x y h1). Qed.
Lemma lem1229387 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229388 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term936 A R a1 m) = (term112 A R a1 m).
Proof. exact (@lem1229387 (term112 A R a1 m)). Qed.
Lemma lem1229389 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (EQ_MP (@lem1229388 A R a1 m) (@lem1229385 A a0 a1 m R x y h1)). Qed.
Lemma lem1229395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229396 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term912 A a1 R _22413) = (term947 A R a1 _22413).
Proof. exact (@lem1229395 (@List.ForallOrdPairs A R _22413) (term441 A R a1 _22413)). Qed.
Lemma lem1229402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229403 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term948 A a1 R _22413) = (term949 A R a1 _22413).
Proof. exact (MK_COMB (@lem1229402) (@lem1229396 A R a1 _22413)). Qed.
Lemma lem1229409 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term947 A R a1 _22413) = (term947 A R a1 _22413).
Proof. exact (eq_refl (term947 A R a1 _22413)). Qed.
Lemma lem1229410 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : ((term912 A a1 R _22413) = (term947 A R a1 _22413)) = ((term947 A R a1 _22413) = (term947 A R a1 _22413)).
Proof. exact (MK_COMB (@lem1229403 A R a1 _22413) (@lem1229409 A R a1 _22413)). Qed.
Lemma lem1229412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229413 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229412 Prop x). Qed.
Lemma lem1229414 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : ((term947 A R a1 _22413) = (term947 A R a1 _22413)) = True.
Proof. exact (@lem1229413 (term947 A R a1 _22413)). Qed.
Lemma lem1229415 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : ((term912 A a1 R _22413) = (term947 A R a1 _22413)) = True.
Proof. exact (TRANS (@lem1229410 A R a1 _22413) (@lem1229414 A R a1 _22413)). Qed.
Lemma lem1229416 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : True = ((term912 A a1 R _22413) = (term947 A R a1 _22413)).
Proof. exact (SYM (@lem1229415 A R a1 _22413)). Qed.
Lemma lem1229417 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term912 A a1 R _22413) = (term947 A R a1 _22413).
Proof. exact (EQ_MP (@lem1229416 A R a1 _22413) (@lem0)). Qed.
Lemma lem1229418 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term947 A R a1 _22413.
Proof. exact (EQ_MP (@lem1229417 A R a1 _22413) (@lem1228503 A _22413 x' y' a1 R h1)). Qed.
Lemma lem1229420 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229421 {A : Type'} (a1 : list A) (R : type1402 A) (_22413 : list A) : (term947 A R a1 _22413) = (term950 A a1 R _22413).
Proof. exact (@lem1229420 (term441 A R a1 _22413) (@List.ForallOrdPairs A R _22413)). Qed.
Lemma lem1229423 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229424 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term941 A R a1 _22413) = (term112 A R a1 _22413).
Proof. exact (@lem1229423 (term112 A R a1 _22413)). Qed.
Lemma lem1229425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229426 {A : Type'} (R : type1402 A) (a1 : list A) (_22413 : list A) : (term942 A R a1 _22413) = (term943 A R a1 _22413).
Proof. exact (MK_COMB (@lem1229425) (@lem1229424 A R a1 _22413)). Qed.
Lemma lem1229427 {A : Type'} (R : type1402 A) (_22413 : list A) : (@List.ForallOrdPairs A R _22413) = (@List.ForallOrdPairs A R _22413).
Proof. exact (eq_refl (@List.ForallOrdPairs A R _22413)). Qed.
Lemma lem1229428 {A : Type'} (a1 : list A) (R : type1402 A) (_22413 : list A) : (term950 A a1 R _22413) = (term951 A a1 R _22413).
Proof. exact (MK_COMB (@lem1229426 A R a1 _22413) (@lem1229427 A R _22413)). Qed.
Lemma lem1229429 {A : Type'} (a1 : list A) (R : type1402 A) (_22413 : list A) : (term947 A R a1 _22413) = (term951 A a1 R _22413).
Proof. exact (TRANS (@lem1229421 A a1 R _22413) (@lem1229428 A a1 R _22413)). Qed.
Lemma lem1229432 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term951 A a1 R _22413.
Proof. exact (EQ_MP (@lem1229429 A a1 R _22413) (@lem1229418 A _22413 x' y' a1 R h1)). Qed.
Lemma lem1229433 {A : Type'} (_22413 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term951 A a1 R _22413.
Proof. exact (@lem1229432 A _22413 x' y' a1 R h1). Qed.
Lemma lem1229434 {A : Type'} (m : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term951 A a1 R m.
Proof. exact (@lem1229433 A m x' y' a1 R h1). Qed.
Lemma lem1229437 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : @List.ForallOrdPairs A R m.
Proof. exact (@lem1229434 A m x' y' a1 R h1 (@lem1229389 A a0 a1 m R x y h2)). Qed.
Lemma lem1229438 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : term945 A R m.
Proof. exact (fun h0 : term253 A R m => @lem1229437 A x' y' a0 a1 m R x y h1 h2). Qed.
Lemma lem1229440 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229441 {A : Type'} (R : type1402 A) (m : list A) : (term945 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1229440 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1229442 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : @List.ForallOrdPairs A R m.
Proof. exact (EQ_MP (@lem1229441 A R m) (@lem1229438 A x' y' a0 a1 m R x y h1 h2)). Qed.
Lemma lem1229445 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229447 {A : Type'} (R : type1402 A) (m : list A) : (term253 A R m) = (term946 A R m).
Proof. exact (@lem1229445 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1229450 {A : Type'} (R : type1402 A) (m : list A) (h1 : term253 A R m) : term946 A R m.
Proof. exact (EQ_MP (@lem1229447 A R m) (@lem1228491 A R m h1)). Qed.
Lemma lem1229453 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (@lem1229450 A R m h1 (@lem1229442 A x' y' a0 a1 m R x y h2 h3)). Qed.
Lemma lem1229454 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : term935.
Proof. exact (fun h0 : ~ False => @lem1229453 A x' y' a0 a1 m R x y h1 h2 h3). Qed.
Lemma lem1229456 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229457 : term935 = False.
Proof. exact (@lem1229456 False). Qed.
Lemma lem1229458 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1229457) (@lem1229454 A x' y' a0 a1 m R x y h1 h2 h3)). Qed.
Lemma lem1229460 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : @List.In A y m.
Proof. exact (proj2 (@lem1225591 A a0 a1 m R x y h1)). Qed.
Lemma lem1229461 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term922 A y m.
Proof. exact (fun h0 : term455 A y m => @lem1229460 A a0 a1 m R x y h1). Qed.
Lemma lem1229463 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229464 {A : Type'} (y : A) (m : list A) : (term922 A y m) = (@List.In A y m).
Proof. exact (@lem1229463 (@List.In A y m)). Qed.
Lemma lem1229465 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : @List.In A y m.
Proof. exact (EQ_MP (@lem1229464 A y m) (@lem1229461 A a0 a1 m R x y h1)). Qed.
Lemma lem1229471 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229472 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : (term704 A m R a0 _22423) = (term924 A R a0 _22423 m).
Proof. exact (@lem1229471 (term696 A R a0 _22423) (term455 A _22423 m)). Qed.
Lemma lem1229478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229479 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : (term925 A m R a0 _22423) = (term926 A R a0 _22423 m).
Proof. exact (MK_COMB (@lem1229478) (@lem1229472 A R a0 _22423 m)). Qed.
Lemma lem1229485 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : (term924 A R a0 _22423 m) = (term924 A R a0 _22423 m).
Proof. exact (eq_refl (term924 A R a0 _22423 m)). Qed.
Lemma lem1229486 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : ((term704 A m R a0 _22423) = (term924 A R a0 _22423 m)) = ((term924 A R a0 _22423 m) = (term924 A R a0 _22423 m)).
Proof. exact (MK_COMB (@lem1229479 A R a0 _22423 m) (@lem1229485 A R a0 _22423 m)). Qed.
Lemma lem1229488 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229489 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229488 Prop x). Qed.
Lemma lem1229490 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : ((term924 A R a0 _22423 m) = (term924 A R a0 _22423 m)) = True.
Proof. exact (@lem1229489 (term924 A R a0 _22423 m)). Qed.
Lemma lem1229491 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : ((term704 A m R a0 _22423) = (term924 A R a0 _22423 m)) = True.
Proof. exact (TRANS (@lem1229486 A R a0 _22423 m) (@lem1229490 A R a0 _22423 m)). Qed.
Lemma lem1229492 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : True = ((term704 A m R a0 _22423) = (term924 A R a0 _22423 m)).
Proof. exact (SYM (@lem1229491 A R a0 _22423 m)). Qed.
Lemma lem1229493 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) (m : list A) : (term704 A m R a0 _22423) = (term924 A R a0 _22423 m).
Proof. exact (EQ_MP (@lem1229492 A R a0 _22423 m) (@lem0)). Qed.
Lemma lem1229494 {A : Type'} (_22423 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term924 A R a0 _22423 m.
Proof. exact (EQ_MP (@lem1229493 A R a0 _22423 m) (@lem1229119 A _22423 a0 a1 m R x y h1)). Qed.
Lemma lem1229496 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229497 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (_22423 : A) : (term924 A R a0 _22423 m) = (term928 A m R a0 _22423).
Proof. exact (@lem1229496 (term455 A _22423 m) (term696 A R a0 _22423)). Qed.
Lemma lem1229499 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229500 {A : Type'} (_22423 : A) (m : list A) : (term929 A _22423 m) = (@List.In A _22423 m).
Proof. exact (@lem1229499 (@List.In A _22423 m)). Qed.
Lemma lem1229501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229502 {A : Type'} (_22423 : A) (m : list A) : (term930 A _22423 m) = (term931 A _22423 m).
Proof. exact (MK_COMB (@lem1229501) (@lem1229500 A _22423 m)). Qed.
Lemma lem1229503 {A : Type'} (R : type1402 A) (a0 : A) (_22423 : A) : (term696 A R a0 _22423) = (term696 A R a0 _22423).
Proof. exact (eq_refl (term696 A R a0 _22423)). Qed.
Lemma lem1229504 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (_22423 : A) : (term928 A m R a0 _22423) = (term932 A m R a0 _22423).
Proof. exact (MK_COMB (@lem1229502 A _22423 m) (@lem1229503 A R a0 _22423)). Qed.
Lemma lem1229505 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (_22423 : A) : (term924 A R a0 _22423 m) = (term932 A m R a0 _22423).
Proof. exact (TRANS (@lem1229497 A m R a0 _22423) (@lem1229504 A m R a0 _22423)). Qed.
Lemma lem1229508 {A : Type'} (_22423 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A m R a0 _22423.
Proof. exact (EQ_MP (@lem1229505 A m R a0 _22423) (@lem1229494 A _22423 a0 a1 m R x y h1)). Qed.
Lemma lem1229509 {A : Type'} (_22423 : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A m R a0 _22423.
Proof. exact (@lem1229508 A _22423 a0 a1 m R x y h1). Qed.
Lemma lem1229510 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term932 A m R a0 y.
Proof. exact (@lem1229509 A y a0 a1 m R x y h1). Qed.
Lemma lem1229513 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) : term696 A R a0 y.
Proof. exact (@lem1229510 A a0 a1 m R x y h1 (@lem1229465 A a0 a1 m R x y h2)). Qed.
Lemma lem1229514 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) : term933 A R a0 y.
Proof. exact (fun h0 : term712 A R a0 y => @lem1229513 A a0 a1 m R x y h1 h2). Qed.
Lemma lem1229516 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229517 {A : Type'} (R : type1402 A) (a0 : A) (y : A) : (term933 A R a0 y) = (term696 A R a0 y).
Proof. exact (@lem1229516 (term696 A R a0 y)). Qed.
Lemma lem1229518 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) : term696 A R a0 y.
Proof. exact (EQ_MP (@lem1229517 A R a0 y) (@lem1229514 A a0 a1 m R x y h1 h2)). Qed.
Lemma lem1229521 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229523 {A : Type'} (R : type1402 A) (a0 : A) (y : A) : (term712 A R a0 y) = (term934 A R a0 y).
Proof. exact (@lem1229521 (term696 A R a0 y)). Qed.
Lemma lem1229526 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term722 A a0 a1 m R x y) (h2 : x = a0) : term934 A R a0 y.
Proof. exact (EQ_MP (@lem1229523 A R a0 y) (@lem1229132 A a1 m R y x a0 h1 h2)). Qed.
Lemma lem1229529 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : False.
Proof. exact (@lem1229526 A a1 m R y x a0 h2 h3 (@lem1229518 A a0 a1 m R x y h1 h2)). Qed.
Lemma lem1229530 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : term935.
Proof. exact (fun h0 : ~ False => @lem1229529 A a1 m R y x a0 h1 h2 h3). Qed.
Lemma lem1229532 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229533 : term935 = False.
Proof. exact (@lem1229532 False). Qed.
Lemma lem1229536 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (proj2 (@lem1225577 A a0 a1 m R x y h1)). Qed.
Lemma lem1229537 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term936 A R a1 m.
Proof. exact (fun h0 : term441 A R a1 m => @lem1229536 A a0 a1 m R x y h1). Qed.
Lemma lem1229539 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229540 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term936 A R a1 m) = (term112 A R a1 m).
Proof. exact (@lem1229539 (term112 A R a1 m)). Qed.
Lemma lem1229541 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term731 A a0 a1 m R x y) : term112 A R a1 m.
Proof. exact (EQ_MP (@lem1229540 A R a1 m) (@lem1229537 A a0 a1 m R x y h1)). Qed.
Lemma lem1229543 {A : Type'} (x : A) (a1 : list A) (h1 : @List.In A x a1) : @List.In A x a1.
Proof. exact (h1). Qed.
Lemma lem1229544 {A : Type'} (x : A) (a1 : list A) (h1 : @List.In A x a1) : term922 A x a1.
Proof. exact (fun h0 : term455 A x a1 => @lem1229543 A x a1 h1). Qed.
Lemma lem1229546 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229547 {A : Type'} (x : A) (a1 : list A) : (term922 A x a1) = (@List.In A x a1).
Proof. exact (@lem1229546 (@List.In A x a1)). Qed.
Lemma lem1229548 {A : Type'} (x : A) (a1 : list A) (h1 : @List.In A x a1) : @List.In A x a1.
Proof. exact (EQ_MP (@lem1229547 A x a1) (@lem1229544 A x a1 h1)). Qed.
Lemma lem1229550 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : @List.In A y m.
Proof. exact (proj2 (@lem1225591 A a0 a1 m R x y h1)). Qed.
Lemma lem1229551 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term922 A y m.
Proof. exact (fun h0 : term455 A y m => @lem1229550 A a0 a1 m R x y h1). Qed.
Lemma lem1229553 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229554 {A : Type'} (y : A) (m : list A) : (term922 A y m) = (@List.In A y m).
Proof. exact (@lem1229553 (@List.In A y m)). Qed.
Lemma lem1229555 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : @List.In A y m.
Proof. exact (EQ_MP (@lem1229554 A y m) (@lem1229551 A a0 a1 m R x y h1)). Qed.
Lemma lem1229561 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1229562 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term914 A a1 _22425 R _22426 _22427) = (term952 A a1 _22425 R _22426 _22427).
Proof. exact (@lem1229561 (term455 A _22426 a1) (term441 A R a1 _22425) (term704 A _22425 R _22426 _22427)). Qed.
Lemma lem1229576 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1229577 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term953 A a1 _22425 R _22426 _22427) = (term954 A a1 _22425 R _22426 _22427).
Proof. exact (@lem1229576 (term455 A _22427 _22425) (term441 A R a1 _22425) (term696 A R _22426 _22427)). Qed.
Lemma lem1229591 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229592 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term955 A a1 _22425 R _22426 _22427) = (term956 A _22426 _22427 R a1 _22425).
Proof. exact (@lem1229591 (term696 A R _22426 _22427) (term441 A R a1 _22425)). Qed.
Lemma lem1229598 {A : Type'} (_22427 : A) (_22425 : list A) : (term703 A _22427 _22425) = (term703 A _22427 _22425).
Proof. exact (eq_refl (term703 A _22427 _22425)). Qed.
Lemma lem1229599 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term954 A a1 _22425 R _22426 _22427) = (term957 A _22426 _22427 R a1 _22425).
Proof. exact (MK_COMB (@lem1229598 A _22427 _22425) (@lem1229592 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229603 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1229604 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term957 A _22426 _22427 R a1 _22425) = (term958 A _22426 _22427 R a1 _22425).
Proof. exact (@lem1229603 (term696 A R _22426 _22427) (term455 A _22427 _22425) (term441 A R a1 _22425)). Qed.
Lemma lem1229620 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term954 A a1 _22425 R _22426 _22427) = (term958 A _22426 _22427 R a1 _22425).
Proof. exact (TRANS (@lem1229599 A _22426 _22427 R a1 _22425) (@lem1229604 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229621 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term953 A a1 _22425 R _22426 _22427) = (term958 A _22426 _22427 R a1 _22425).
Proof. exact (TRANS (@lem1229577 A a1 _22425 R _22426 _22427) (@lem1229620 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229622 {A : Type'} (_22426 : A) (a1 : list A) : (term703 A _22426 a1) = (term703 A _22426 a1).
Proof. exact (eq_refl (term703 A _22426 a1)). Qed.
Lemma lem1229623 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term952 A a1 _22425 R _22426 _22427) = (term959 A _22426 _22427 R a1 _22425).
Proof. exact (MK_COMB (@lem1229622 A _22426 a1) (@lem1229621 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229627 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1229628 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term959 A _22426 _22427 R a1 _22425) = (term960 A _22426 _22427 R a1 _22425).
Proof. exact (@lem1229627 (term696 A R _22426 _22427) (term455 A _22426 a1) (term961 A _22427 R a1 _22425)). Qed.
Lemma lem1229654 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term952 A a1 _22425 R _22426 _22427) = (term960 A _22426 _22427 R a1 _22425).
Proof. exact (TRANS (@lem1229623 A _22426 _22427 R a1 _22425) (@lem1229628 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229655 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term914 A a1 _22425 R _22426 _22427) = (term960 A _22426 _22427 R a1 _22425).
Proof. exact (TRANS (@lem1229562 A a1 _22425 R _22426 _22427) (@lem1229654 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229657 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term962 A a1 _22425 R _22426 _22427) = (term963 A _22426 _22427 R a1 _22425).
Proof. exact (MK_COMB (@lem1229656) (@lem1229655 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229671 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1229672 {A : Type'} (_22426 : A) (R : type1402 A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term964 A R _22426 a1 _22427 _22425) = (term965 A _22426 R a1 _22427 _22425).
Proof. exact (@lem1229671 (term455 A _22426 a1) (term441 A R a1 _22425) (term455 A _22427 _22425)). Qed.
Lemma lem1229686 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229687 {A : Type'} (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term966 A R a1 _22427 _22425) = (term961 A _22427 R a1 _22425).
Proof. exact (@lem1229686 (term455 A _22427 _22425) (term441 A R a1 _22425)). Qed.
Lemma lem1229693 {A : Type'} (_22426 : A) (a1 : list A) : (term703 A _22426 a1) = (term703 A _22426 a1).
Proof. exact (eq_refl (term703 A _22426 a1)). Qed.
Lemma lem1229694 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term965 A _22426 R a1 _22427 _22425) = (term967 A _22426 _22427 R a1 _22425).
Proof. exact (MK_COMB (@lem1229693 A _22426 a1) (@lem1229687 A _22427 R a1 _22425)). Qed.
Lemma lem1229705 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term964 A R _22426 a1 _22427 _22425) = (term967 A _22426 _22427 R a1 _22425).
Proof. exact (TRANS (@lem1229672 A _22426 R a1 _22427 _22425) (@lem1229694 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229706 {A : Type'} (R : type1402 A) (_22426 : A) (_22427 : A) : (term968 A R _22426 _22427) = (term968 A R _22426 _22427).
Proof. exact (eq_refl (term968 A R _22426 _22427)). Qed.
Lemma lem1229707 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : (term969 A R _22426 a1 _22427 _22425) = (term960 A _22426 _22427 R a1 _22425).
Proof. exact (MK_COMB (@lem1229706 A R _22426 _22427) (@lem1229705 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229718 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : ((term914 A a1 _22425 R _22426 _22427) = (term969 A R _22426 a1 _22427 _22425)) = ((term960 A _22426 _22427 R a1 _22425) = (term960 A _22426 _22427 R a1 _22425)).
Proof. exact (MK_COMB (@lem1229657 A _22426 _22427 R a1 _22425) (@lem1229707 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229720 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229721 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229720 Prop x). Qed.
Lemma lem1229722 {A : Type'} (_22426 : A) (_22427 : A) (R : type1402 A) (a1 : list A) (_22425 : list A) : ((term960 A _22426 _22427 R a1 _22425) = (term960 A _22426 _22427 R a1 _22425)) = True.
Proof. exact (@lem1229721 (term960 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229723 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : ((term914 A a1 _22425 R _22426 _22427) = (term969 A R _22426 a1 _22427 _22425)) = True.
Proof. exact (TRANS (@lem1229718 A _22426 _22427 R a1 _22425) (@lem1229722 A _22426 _22427 R a1 _22425)). Qed.
Lemma lem1229724 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : True = ((term914 A a1 _22425 R _22426 _22427) = (term969 A R _22426 a1 _22427 _22425)).
Proof. exact (SYM (@lem1229723 A R _22426 a1 _22427 _22425)). Qed.
Lemma lem1229725 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term914 A a1 _22425 R _22426 _22427) = (term969 A R _22426 a1 _22427 _22425).
Proof. exact (EQ_MP (@lem1229724 A R _22426 a1 _22427 _22425) (@lem0)). Qed.
Lemma lem1229726 {A : Type'} (_22426 : A) (_22427 : A) (_22425 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term969 A R _22426 a1 _22427 _22425.
Proof. exact (EQ_MP (@lem1229725 A R _22426 a1 _22427 _22425) (@lem1228699 A _22425 _22426 _22427 x' y' a1 R h1)). Qed.
Lemma lem1229728 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229729 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term969 A R _22426 a1 _22427 _22425) = (term970 A a1 _22425 R _22426 _22427).
Proof. exact (@lem1229728 (term964 A R _22426 a1 _22427 _22425) (term696 A R _22426 _22427)). Qed.
Lemma lem1229731 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1229732 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term973 A R _22426 a1 _22427 _22425) = (term974 A R _22426 a1 _22427 _22425).
Proof. exact (@lem1229731 (term441 A R a1 _22425) (term176 A _22426 a1 _22427 _22425)). Qed.
Lemma lem1229734 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229735 {A : Type'} (R : type1402 A) (a1 : list A) (_22425 : list A) : (term941 A R a1 _22425) = (term112 A R a1 _22425).
Proof. exact (@lem1229734 (term112 A R a1 _22425)). Qed.
Lemma lem1229736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1229737 {A : Type'} (R : type1402 A) (a1 : list A) (_22425 : list A) : (term975 A R a1 _22425) = (term976 A R a1 _22425).
Proof. exact (MK_COMB (@lem1229736) (@lem1229735 A R a1 _22425)). Qed.
Lemma lem1229739 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1229740 {A : Type'} (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term977 A _22426 a1 _22427 _22425) = (term978 A _22426 a1 _22427 _22425).
Proof. exact (@lem1229739 (term455 A _22426 a1) (term455 A _22427 _22425)). Qed.
Lemma lem1229742 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229743 {A : Type'} (_22426 : A) (a1 : list A) : (term929 A _22426 a1) = (@List.In A _22426 a1).
Proof. exact (@lem1229742 (@List.In A _22426 a1)). Qed.
Lemma lem1229744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1229745 {A : Type'} (_22426 : A) (a1 : list A) : (term979 A _22426 a1) = (term713 A _22426 a1).
Proof. exact (MK_COMB (@lem1229744) (@lem1229743 A _22426 a1)). Qed.
Lemma lem1229747 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229748 {A : Type'} (_22427 : A) (_22425 : list A) : (term929 A _22427 _22425) = (@List.In A _22427 _22425).
Proof. exact (@lem1229747 (@List.In A _22427 _22425)). Qed.
Lemma lem1229749 {A : Type'} (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term978 A _22426 a1 _22427 _22425) = (term179 A _22426 a1 _22427 _22425).
Proof. exact (MK_COMB (@lem1229745 A _22426 a1) (@lem1229748 A _22427 _22425)). Qed.
Lemma lem1229750 {A : Type'} (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term977 A _22426 a1 _22427 _22425) = (term179 A _22426 a1 _22427 _22425).
Proof. exact (TRANS (@lem1229740 A _22426 a1 _22427 _22425) (@lem1229749 A _22426 a1 _22427 _22425)). Qed.
Lemma lem1229751 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term974 A R _22426 a1 _22427 _22425) = (term980 A R _22426 a1 _22427 _22425).
Proof. exact (MK_COMB (@lem1229737 A R a1 _22425) (@lem1229750 A _22426 a1 _22427 _22425)). Qed.
Lemma lem1229752 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term973 A R _22426 a1 _22427 _22425) = (term980 A R _22426 a1 _22427 _22425).
Proof. exact (TRANS (@lem1229732 A R _22426 a1 _22427 _22425) (@lem1229751 A R _22426 a1 _22427 _22425)). Qed.
Lemma lem1229753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229754 {A : Type'} (R : type1402 A) (_22426 : A) (a1 : list A) (_22427 : A) (_22425 : list A) : (term981 A R _22426 a1 _22427 _22425) = (term982 A R _22426 a1 _22427 _22425).
Proof. exact (MK_COMB (@lem1229753) (@lem1229752 A R _22426 a1 _22427 _22425)). Qed.
Lemma lem1229755 {A : Type'} (R : type1402 A) (_22426 : A) (_22427 : A) : (term696 A R _22426 _22427) = (term696 A R _22426 _22427).
Proof. exact (eq_refl (term696 A R _22426 _22427)). Qed.
Lemma lem1229756 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term970 A a1 _22425 R _22426 _22427) = (term983 A a1 _22425 R _22426 _22427).
Proof. exact (MK_COMB (@lem1229754 A R _22426 a1 _22427 _22425) (@lem1229755 A R _22426 _22427)). Qed.
Lemma lem1229757 {A : Type'} (a1 : list A) (_22425 : list A) (R : type1402 A) (_22426 : A) (_22427 : A) : (term969 A R _22426 a1 _22427 _22425) = (term983 A a1 _22425 R _22426 _22427).
Proof. exact (TRANS (@lem1229729 A a1 _22425 R _22426 _22427) (@lem1229756 A a1 _22425 R _22426 _22427)). Qed.
Lemma lem1229759 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term722 A a0 a1 m R x y) (h2 : @List.In A x a1) : term179 A x a1 y m.
Proof. exact (conj (@lem1229548 A x a1 h2) (@lem1229555 A a0 a1 m R x y h1)). Qed.
Lemma lem1229760 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : @List.In A x a1) : term980 A R x a1 y m.
Proof. exact (conj (@lem1229541 A a0 a1 m R x y h1) (@lem1229759 A a0 m R y x a1 h2 h3)). Qed.
Lemma lem1229762 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term983 A a1 _22425 R _22426 _22427.
Proof. exact (EQ_MP (@lem1229757 A a1 _22425 R _22426 _22427) (@lem1229726 A _22426 _22427 _22425 x' y' a1 R h1)). Qed.
Lemma lem1229763 {A : Type'} (_22425 : list A) (_22426 : A) (_22427 : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term983 A a1 _22425 R _22426 _22427.
Proof. exact (@lem1229762 A _22425 _22426 _22427 x' y' a1 R h1). Qed.
Lemma lem1229764 {A : Type'} (m : list A) (x : A) (y : A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term983 A a1 m R x y.
Proof. exact (@lem1229763 A m x y x' y' a1 R h1). Qed.
Lemma lem1229767 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : term696 A R x y.
Proof. exact (@lem1229764 A m x y x' y' a1 R h1 (@lem1229760 A a0 m R y x a1 h2 h3 h4)). Qed.
Lemma lem1229768 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : term933 A R x y.
Proof. exact (fun h0 : term712 A R x y => @lem1229767 A x' y' a0 m R y x a1 h1 h2 h3 h4). Qed.
Lemma lem1229770 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229771 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term933 A R x y) = (term696 A R x y).
Proof. exact (@lem1229770 (term696 A R x y)). Qed.
Lemma lem1229772 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : term696 A R x y.
Proof. exact (EQ_MP (@lem1229771 A R x y) (@lem1229768 A x' y' a0 m R y x a1 h1 h2 h3 h4)). Qed.
Lemma lem1229775 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229777 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term712 A R x y) = (term934 A R x y).
Proof. exact (@lem1229775 (term696 A R x y)). Qed.
Lemma lem1229780 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term722 A a0 a1 m R x y) : term934 A R x y.
Proof. exact (EQ_MP (@lem1229777 A R x y) (@lem1228667 A a0 a1 m R x y h1)). Qed.
Lemma lem1229783 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : False.
Proof. exact (@lem1229780 A a0 a1 m R x y h3 (@lem1229772 A x' y' a0 m R y x a1 h1 h2 h3 h4)). Qed.
Lemma lem1229784 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : term935.
Proof. exact (fun h0 : ~ False => @lem1229783 A x' y' a0 m R y x a1 h1 h2 h3 h4). Qed.
Lemma lem1229786 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229787 : term935 = False.
Proof. exact (@lem1229786 False). Qed.
Lemma lem1229788 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : False.
Proof. exact (EQ_MP (@lem1229787) (@lem1229784 A x' y' a0 m R y x a1 h1 h2 h3 h4)). Qed.
Lemma lem1229901 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : @List.In A x a1.
Proof. exact (proj1 (@lem1225606 A a1 R a0 x h1)). Qed.
Lemma lem1229902 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term922 A x a1.
Proof. exact (fun h0 : term455 A x a1 => @lem1229901 A a1 R a0 x h1). Qed.
Lemma lem1229904 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229905 {A : Type'} (x : A) (a1 : list A) : (term922 A x a1) = (@List.In A x a1).
Proof. exact (@lem1229904 (@List.In A x a1)). Qed.
Lemma lem1229906 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : @List.In A x a1.
Proof. exact (EQ_MP (@lem1229905 A x a1) (@lem1229902 A a1 R a0 x h1)). Qed.
Lemma lem1229912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1229913 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : (term704 A a1 R a0 _22436) = (term924 A R a0 _22436 a1).
Proof. exact (@lem1229912 (term696 A R a0 _22436) (term455 A _22436 a1)). Qed.
Lemma lem1229919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1229920 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : (term925 A a1 R a0 _22436) = (term926 A R a0 _22436 a1).
Proof. exact (MK_COMB (@lem1229919) (@lem1229913 A R a0 _22436 a1)). Qed.
Lemma lem1229926 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : (term924 A R a0 _22436 a1) = (term924 A R a0 _22436 a1).
Proof. exact (eq_refl (term924 A R a0 _22436 a1)). Qed.
Lemma lem1229927 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : ((term704 A a1 R a0 _22436) = (term924 A R a0 _22436 a1)) = ((term924 A R a0 _22436 a1) = (term924 A R a0 _22436 a1)).
Proof. exact (MK_COMB (@lem1229920 A R a0 _22436 a1) (@lem1229926 A R a0 _22436 a1)). Qed.
Lemma lem1229929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1229930 (x : Prop) : (x = x) = True.
Proof. exact (@lem1229929 Prop x). Qed.
Lemma lem1229931 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : ((term924 A R a0 _22436 a1) = (term924 A R a0 _22436 a1)) = True.
Proof. exact (@lem1229930 (term924 A R a0 _22436 a1)). Qed.
Lemma lem1229932 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : ((term704 A a1 R a0 _22436) = (term924 A R a0 _22436 a1)) = True.
Proof. exact (TRANS (@lem1229927 A R a0 _22436 a1) (@lem1229931 A R a0 _22436 a1)). Qed.
Lemma lem1229933 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : True = ((term704 A a1 R a0 _22436) = (term924 A R a0 _22436 a1)).
Proof. exact (SYM (@lem1229932 A R a0 _22436 a1)). Qed.
Lemma lem1229934 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) (a1 : list A) : (term704 A a1 R a0 _22436) = (term924 A R a0 _22436 a1).
Proof. exact (EQ_MP (@lem1229933 A R a0 _22436 a1) (@lem0)). Qed.
Lemma lem1229935 {A : Type'} (_22436 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term924 A R a0 _22436 a1.
Proof. exact (EQ_MP (@lem1229934 A R a0 _22436 a1) (@lem1228749 A _22436 x a0 a1 m R h1)). Qed.
Lemma lem1229937 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1229938 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22436 : A) : (term924 A R a0 _22436 a1) = (term928 A a1 R a0 _22436).
Proof. exact (@lem1229937 (term455 A _22436 a1) (term696 A R a0 _22436)). Qed.
Lemma lem1229940 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1229941 {A : Type'} (_22436 : A) (a1 : list A) : (term929 A _22436 a1) = (@List.In A _22436 a1).
Proof. exact (@lem1229940 (@List.In A _22436 a1)). Qed.
Lemma lem1229942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1229943 {A : Type'} (_22436 : A) (a1 : list A) : (term930 A _22436 a1) = (term931 A _22436 a1).
Proof. exact (MK_COMB (@lem1229942) (@lem1229941 A _22436 a1)). Qed.
Lemma lem1229944 {A : Type'} (R : type1402 A) (a0 : A) (_22436 : A) : (term696 A R a0 _22436) = (term696 A R a0 _22436).
Proof. exact (eq_refl (term696 A R a0 _22436)). Qed.
Lemma lem1229945 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22436 : A) : (term928 A a1 R a0 _22436) = (term932 A a1 R a0 _22436).
Proof. exact (MK_COMB (@lem1229943 A _22436 a1) (@lem1229944 A R a0 _22436)). Qed.
Lemma lem1229946 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22436 : A) : (term924 A R a0 _22436 a1) = (term932 A a1 R a0 _22436).
Proof. exact (TRANS (@lem1229938 A a1 R a0 _22436) (@lem1229945 A a1 R a0 _22436)). Qed.
Lemma lem1229949 {A : Type'} (_22436 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term932 A a1 R a0 _22436.
Proof. exact (EQ_MP (@lem1229946 A a1 R a0 _22436) (@lem1229935 A _22436 x a0 a1 m R h1)). Qed.
Lemma lem1229950 {A : Type'} (_22436 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term932 A a1 R a0 _22436.
Proof. exact (@lem1229949 A _22436 x a0 a1 m R h1). Qed.
Lemma lem1229951 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term932 A a1 R a0 x.
Proof. exact (@lem1229950 A x x a0 a1 m R h1). Qed.
Lemma lem1229954 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : term696 A R a0 x.
Proof. exact (@lem1229951 A x a0 a1 m R h2 (@lem1229906 A a1 R a0 x h1)). Qed.
Lemma lem1229955 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : term933 A R a0 x.
Proof. exact (fun h0 : term712 A R a0 x => @lem1229954 A x a0 a1 m R h1 h2). Qed.
Lemma lem1229957 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229958 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term933 A R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1229957 (term696 A R a0 x)). Qed.
Lemma lem1229959 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : term696 A R a0 x.
Proof. exact (EQ_MP (@lem1229958 A R a0 x) (@lem1229955 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1229962 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1229964 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term712 A R a0 x) = (term934 A R a0 x).
Proof. exact (@lem1229962 (term696 A R a0 x)). Qed.
Lemma lem1229967 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A a1 R a0 x) : term934 A R a0 x.
Proof. exact (EQ_MP (@lem1229964 A R a0 x) (@lem1228755 A a1 R a0 x h1)). Qed.
Lemma lem1229970 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : False.
Proof. exact (@lem1229967 A a1 R a0 x h1 (@lem1229959 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1229971 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : term935.
Proof. exact (fun h0 : ~ False => @lem1229970 A x a0 a1 m R h1 h2). Qed.
Lemma lem1229973 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1229974 : term935 = False.
Proof. exact (@lem1229973 False). Qed.
Lemma lem1229975 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A a1 R a0 x) (h2 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1229974) (@lem1229971 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1230088 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1230089 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1230088 A x). Qed.
Lemma lem1230090 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (@lem1230089 A a0). Qed.
Lemma lem1230091 {A : Type'} (a0 : A) : term984 A a0.
Proof. exact (fun h0 : term985 A a0 => @lem1230090 A a0). Qed.
Lemma lem1230093 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230094 {A : Type'} (a0 : A) : (term984 A a0) = (a0 = a0).
Proof. exact (@lem1230093 (a0 = a0)). Qed.
Lemma lem1230095 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (EQ_MP (@lem1230094 A a0) (@lem1230091 A a0)). Qed.
Lemma lem1230097 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : @List.In A x m.
Proof. exact (proj1 (@lem1225607 A m R a0 x h1)). Qed.
Lemma lem1230098 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : term922 A x m.
Proof. exact (fun h0 : term455 A x m => @lem1230097 A m R a0 x h1). Qed.
Lemma lem1230100 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230101 {A : Type'} (x : A) (m : list A) : (term922 A x m) = (@List.In A x m).
Proof. exact (@lem1230100 (@List.In A x m)). Qed.
Lemma lem1230102 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : @List.In A x m.
Proof. exact (EQ_MP (@lem1230101 A x m) (@lem1230098 A m R a0 x h1)). Qed.
Lemma lem1230120 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230121 {A : Type'} (R : type1402 A) (_22441 : A) (_22442 : A) (m : list A) : (term704 A m R _22441 _22442) = (term924 A R _22441 _22442 m).
Proof. exact (@lem1230120 (term696 A R _22441 _22442) (term455 A _22442 m)). Qed.
Lemma lem1230127 {A : Type'} (_22441 : A) (a0 : A) : (term986 A _22441 a0) = (term986 A _22441 a0).
Proof. exact (eq_refl (term986 A _22441 a0)). Qed.
Lemma lem1230128 {A : Type'} (a0 : A) (R : type1402 A) (_22441 : A) (_22442 : A) (m : list A) : (term915 A a0 m R _22441 _22442) = (term987 A a0 R _22441 _22442 m).
Proof. exact (MK_COMB (@lem1230127 A _22441 a0) (@lem1230121 A R _22441 _22442 m)). Qed.
Lemma lem1230132 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230133 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term987 A a0 R _22441 _22442 m) = (term988 A R _22441 a0 _22442 m).
Proof. exact (@lem1230132 (term696 A R _22441 _22442) (term861 A _22441 a0) (term455 A _22442 m)). Qed.
Lemma lem1230151 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term915 A a0 m R _22441 _22442) = (term988 A R _22441 a0 _22442 m).
Proof. exact (TRANS (@lem1230128 A a0 R _22441 _22442 m) (@lem1230133 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1230153 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term989 A a0 m R _22441 _22442) = (term990 A R _22441 a0 _22442 m).
Proof. exact (MK_COMB (@lem1230152) (@lem1230151 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230171 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term988 A R _22441 a0 _22442 m) = (term988 A R _22441 a0 _22442 m).
Proof. exact (eq_refl (term988 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230172 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : ((term915 A a0 m R _22441 _22442) = (term988 A R _22441 a0 _22442 m)) = ((term988 A R _22441 a0 _22442 m) = (term988 A R _22441 a0 _22442 m)).
Proof. exact (MK_COMB (@lem1230153 A R _22441 a0 _22442 m) (@lem1230171 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230174 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1230175 (x : Prop) : (x = x) = True.
Proof. exact (@lem1230174 Prop x). Qed.
Lemma lem1230176 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : ((term988 A R _22441 a0 _22442 m) = (term988 A R _22441 a0 _22442 m)) = True.
Proof. exact (@lem1230175 (term988 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230177 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : ((term915 A a0 m R _22441 _22442) = (term988 A R _22441 a0 _22442 m)) = True.
Proof. exact (TRANS (@lem1230172 A R _22441 a0 _22442 m) (@lem1230176 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230178 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : True = ((term915 A a0 m R _22441 _22442) = (term988 A R _22441 a0 _22442 m)).
Proof. exact (SYM (@lem1230177 A R _22441 a0 _22442 m)). Qed.
Lemma lem1230179 {A : Type'} (R : type1402 A) (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term915 A a0 m R _22441 _22442) = (term988 A R _22441 a0 _22442 m).
Proof. exact (EQ_MP (@lem1230178 A R _22441 a0 _22442 m) (@lem0)). Qed.
Lemma lem1230180 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term988 A R _22441 a0 _22442 m.
Proof. exact (EQ_MP (@lem1230179 A R _22441 a0 _22442 m) (@lem1228875 A _22441 _22442 x a0 a1 m R h1)). Qed.
Lemma lem1230182 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1230183 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (_22441 : A) (_22442 : A) : (term988 A R _22441 a0 _22442 m) = (term991 A a0 m R _22441 _22442).
Proof. exact (@lem1230182 (term865 A _22441 a0 _22442 m) (term696 A R _22441 _22442)). Qed.
Lemma lem1230185 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230186 {A : Type'} (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term992 A _22441 a0 _22442 m) = (term993 A _22441 a0 _22442 m).
Proof. exact (@lem1230185 (term861 A _22441 a0) (term455 A _22442 m)). Qed.
Lemma lem1230188 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230189 {A : Type'} (_22441 : A) (a0 : A) : (term994 A _22441 a0) = (_22441 = a0).
Proof. exact (@lem1230188 (_22441 = a0)). Qed.
Lemma lem1230190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230191 {A : Type'} (_22441 : A) (a0 : A) : (term995 A _22441 a0) = (term996 A _22441 a0).
Proof. exact (MK_COMB (@lem1230190) (@lem1230189 A _22441 a0)). Qed.
Lemma lem1230193 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230194 {A : Type'} (_22442 : A) (m : list A) : (term929 A _22442 m) = (@List.In A _22442 m).
Proof. exact (@lem1230193 (@List.In A _22442 m)). Qed.
Lemma lem1230195 {A : Type'} (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term993 A _22441 a0 _22442 m) = (term997 A _22441 a0 _22442 m).
Proof. exact (MK_COMB (@lem1230191 A _22441 a0) (@lem1230194 A _22442 m)). Qed.
Lemma lem1230196 {A : Type'} (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term992 A _22441 a0 _22442 m) = (term997 A _22441 a0 _22442 m).
Proof. exact (TRANS (@lem1230186 A _22441 a0 _22442 m) (@lem1230195 A _22441 a0 _22442 m)). Qed.
Lemma lem1230197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1230198 {A : Type'} (_22441 : A) (a0 : A) (_22442 : A) (m : list A) : (term998 A _22441 a0 _22442 m) = (term999 A _22441 a0 _22442 m).
Proof. exact (MK_COMB (@lem1230197) (@lem1230196 A _22441 a0 _22442 m)). Qed.
Lemma lem1230199 {A : Type'} (R : type1402 A) (_22441 : A) (_22442 : A) : (term696 A R _22441 _22442) = (term696 A R _22441 _22442).
Proof. exact (eq_refl (term696 A R _22441 _22442)). Qed.
Lemma lem1230200 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (_22441 : A) (_22442 : A) : (term991 A a0 m R _22441 _22442) = (term1000 A a0 m R _22441 _22442).
Proof. exact (MK_COMB (@lem1230198 A _22441 a0 _22442 m) (@lem1230199 A R _22441 _22442)). Qed.
Lemma lem1230201 {A : Type'} (a0 : A) (m : list A) (R : type1402 A) (_22441 : A) (_22442 : A) : (term988 A R _22441 a0 _22442 m) = (term1000 A a0 m R _22441 _22442).
Proof. exact (TRANS (@lem1230183 A a0 m R _22441 _22442) (@lem1230200 A a0 m R _22441 _22442)). Qed.
Lemma lem1230203 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : term1001 A a0 x m.
Proof. exact (conj (@lem1230095 A a0) (@lem1230102 A m R a0 x h1)). Qed.
Lemma lem1230205 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1000 A a0 m R _22441 _22442.
Proof. exact (EQ_MP (@lem1230201 A a0 m R _22441 _22442) (@lem1230180 A _22441 _22442 x a0 a1 m R h1)). Qed.
Lemma lem1230206 {A : Type'} (_22441 : A) (_22442 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1000 A a0 m R _22441 _22442.
Proof. exact (@lem1230205 A _22441 _22442 x a0 a1 m R h1). Qed.
Lemma lem1230207 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1002 A m R a0 x.
Proof. exact (@lem1230206 A a0 x x a0 a1 m R h1). Qed.
Lemma lem1230210 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : term696 A R a0 x.
Proof. exact (@lem1230207 A x a0 a1 m R h2 (@lem1230203 A m R a0 x h1)). Qed.
Lemma lem1230211 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : term933 A R a0 x.
Proof. exact (fun h0 : term712 A R a0 x => @lem1230210 A x a0 a1 m R h1 h2). Qed.
Lemma lem1230213 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230214 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term933 A R a0 x) = (term696 A R a0 x).
Proof. exact (@lem1230213 (term696 A R a0 x)). Qed.
Lemma lem1230215 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : term696 A R a0 x.
Proof. exact (EQ_MP (@lem1230214 A R a0 x) (@lem1230211 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1230218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1230220 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term712 A R a0 x) = (term934 A R a0 x).
Proof. exact (@lem1230218 (term696 A R a0 x)). Qed.
Lemma lem1230223 {A : Type'} (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term714 A m R a0 x) : term934 A R a0 x.
Proof. exact (EQ_MP (@lem1230220 A R a0 x) (@lem1228863 A m R a0 x h1)). Qed.
Lemma lem1230226 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : False.
Proof. exact (@lem1230223 A m R a0 x h1 (@lem1230215 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1230227 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : term935.
Proof. exact (fun h0 : ~ False => @lem1230226 A x a0 a1 m R h1 h2). Qed.
Lemma lem1230229 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230230 : term935 = False.
Proof. exact (@lem1230229 False). Qed.
Lemma lem1230231 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term714 A m R a0 x) (h2 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1230230) (@lem1230227 A x a0 a1 m R h1 h2)). Qed.
Lemma lem1230344 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (proj2 (@lem1225599 A x a0 a1 m R h1)). Qed.
Lemma lem1230345 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R a1.
Proof. exact (fun h0 : term253 A R a1 => @lem1230344 A x a0 a1 m R h1). Qed.
Lemma lem1230347 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230348 {A : Type'} (R : type1402 A) (a1 : list A) : (term945 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230347 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230349 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1230348 A R a1) (@lem1230345 A x a0 a1 m R h1)). Qed.
Lemma lem1230351 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (proj1 (@lem1225598 A x a0 a1 m R h1)). Qed.
Lemma lem1230352 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R m.
Proof. exact (fun h0 : term253 A R m => @lem1230351 A x a0 a1 m R h1). Qed.
Lemma lem1230354 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230355 {A : Type'} (R : type1402 A) (m : list A) : (term945 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1230354 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1230356 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (EQ_MP (@lem1230355 A R m) (@lem1230352 A x a0 a1 m R h1)). Qed.
Lemma lem1230359 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (h1). Qed.
Lemma lem1230360 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term1003 A R a1 m.
Proof. exact (fun h0 : term112 A R a1 m => @lem1230359 A R a1 m h1). Qed.
Lemma lem1230362 (p : Prop) : (term1004 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1230363 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term1003 A R a1 m) = (term441 A R a1 m).
Proof. exact (@lem1230362 (term112 A R a1 m)). Qed.
Lemma lem1230364 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (EQ_MP (@lem1230363 A R a1 m) (@lem1230360 A R a1 m h1)). Qed.
Lemma lem1230366 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (proj2 (@lem1225599 A x a0 a1 m R h1)). Qed.
Lemma lem1230367 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R a1.
Proof. exact (fun h0 : term253 A R a1 => @lem1230366 A x a0 a1 m R h1). Qed.
Lemma lem1230369 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230370 {A : Type'} (R : type1402 A) (a1 : list A) : (term945 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230369 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230371 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1230370 A R a1) (@lem1230367 A x a0 a1 m R h1)). Qed.
Lemma lem1230373 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (proj1 (@lem1225598 A x a0 a1 m R h1)). Qed.
Lemma lem1230374 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R m.
Proof. exact (fun h0 : term253 A R m => @lem1230373 A x a0 a1 m R h1). Qed.
Lemma lem1230376 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230377 {A : Type'} (R : type1402 A) (m : list A) : (term945 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1230376 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1230378 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (EQ_MP (@lem1230377 A R m) (@lem1230374 A x a0 a1 m R h1)). Qed.
Lemma lem1230394 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230395 {A : Type'} (R : type1402 A) (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term895 A R x' _22444 a1) = (term1005 A R x' _22444 a1).
Proof. exact (@lem1230394 (term253 A R _22444) (term253 A R a1) (term875 A x' _22444 a1)). Qed.
Lemma lem1230409 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230410 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1006 A R x' _22444 a1) = (term1007 A x' _22444 R a1).
Proof. exact (@lem1230409 (term875 A x' _22444 a1) (term253 A R a1)). Qed.
Lemma lem1230416 {A : Type'} (R : type1402 A) (_22444 : list A) : (term204 A R _22444) = (term204 A R _22444).
Proof. exact (eq_refl (term204 A R _22444)). Qed.
Lemma lem1230417 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1005 A R x' _22444 a1) = (term1008 A x' _22444 R a1).
Proof. exact (MK_COMB (@lem1230416 A R _22444) (@lem1230410 A x' _22444 R a1)). Qed.
Lemma lem1230421 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230422 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1008 A x' _22444 R a1) = (term1009 A x' _22444 R a1).
Proof. exact (@lem1230421 (term875 A x' _22444 a1) (term253 A R _22444) (term253 A R a1)). Qed.
Lemma lem1230438 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1005 A R x' _22444 a1) = (term1009 A x' _22444 R a1).
Proof. exact (TRANS (@lem1230417 A x' _22444 R a1) (@lem1230422 A x' _22444 R a1)). Qed.
Lemma lem1230439 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term895 A R x' _22444 a1) = (term1009 A x' _22444 R a1).
Proof. exact (TRANS (@lem1230395 A R x' _22444 a1) (@lem1230438 A x' _22444 R a1)). Qed.
Lemma lem1230440 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term216 A R a1 _22444) = (term216 A R a1 _22444).
Proof. exact (eq_refl (term216 A R a1 _22444)). Qed.
Lemma lem1230441 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term916 A R x' _22444 a1) = (term1010 A x' _22444 R a1).
Proof. exact (MK_COMB (@lem1230440 A R a1 _22444) (@lem1230439 A x' _22444 R a1)). Qed.
Lemma lem1230445 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230446 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1010 A x' _22444 R a1) = (term1011 A x' _22444 R a1).
Proof. exact (@lem1230445 (term875 A x' _22444 a1) (term112 A R a1 _22444) (term1012 A _22444 R a1)). Qed.
Lemma lem1230472 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term916 A R x' _22444 a1) = (term1011 A x' _22444 R a1).
Proof. exact (TRANS (@lem1230441 A x' _22444 R a1) (@lem1230446 A x' _22444 R a1)). Qed.
Lemma lem1230473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1230474 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1013 A R x' _22444 a1) = (term1014 A x' _22444 R a1).
Proof. exact (MK_COMB (@lem1230473) (@lem1230472 A x' _22444 R a1)). Qed.
Lemma lem1230498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230499 {A : Type'} (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1012 A a1 R _22444) = (term1012 A _22444 R a1).
Proof. exact (@lem1230498 (term253 A R _22444) (term253 A R a1)). Qed.
Lemma lem1230505 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term216 A R a1 _22444) = (term216 A R a1 _22444).
Proof. exact (eq_refl (term216 A R a1 _22444)). Qed.
Lemma lem1230506 {A : Type'} (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1015 A a1 R _22444) = (term1016 A _22444 R a1).
Proof. exact (MK_COMB (@lem1230505 A R a1 _22444) (@lem1230499 A _22444 R a1)). Qed.
Lemma lem1230517 {A : Type'} (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term1017 A x' _22444 a1) = (term1017 A x' _22444 a1).
Proof. exact (eq_refl (term1017 A x' _22444 a1)). Qed.
Lemma lem1230518 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1018 A x' a1 R _22444) = (term1011 A x' _22444 R a1).
Proof. exact (MK_COMB (@lem1230517 A x' _22444 a1) (@lem1230506 A _22444 R a1)). Qed.
Lemma lem1230529 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : ((term916 A R x' _22444 a1) = (term1018 A x' a1 R _22444)) = ((term1011 A x' _22444 R a1) = (term1011 A x' _22444 R a1)).
Proof. exact (MK_COMB (@lem1230474 A x' _22444 R a1) (@lem1230518 A x' _22444 R a1)). Qed.
Lemma lem1230531 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1230532 (x : Prop) : (x = x) = True.
Proof. exact (@lem1230531 Prop x). Qed.
Lemma lem1230533 {A : Type'} (x' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : ((term1011 A x' _22444 R a1) = (term1011 A x' _22444 R a1)) = True.
Proof. exact (@lem1230532 (term1011 A x' _22444 R a1)). Qed.
Lemma lem1230534 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : ((term916 A R x' _22444 a1) = (term1018 A x' a1 R _22444)) = True.
Proof. exact (TRANS (@lem1230529 A x' _22444 R a1) (@lem1230533 A x' _22444 R a1)). Qed.
Lemma lem1230535 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : True = ((term916 A R x' _22444 a1) = (term1018 A x' a1 R _22444)).
Proof. exact (SYM (@lem1230534 A x' a1 R _22444)). Qed.
Lemma lem1230536 {A : Type'} (x' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : (term916 A R x' _22444 a1) = (term1018 A x' a1 R _22444).
Proof. exact (EQ_MP (@lem1230535 A x' a1 R _22444) (@lem0)). Qed.
Lemma lem1230537 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1018 A x' a1 R _22444.
Proof. exact (EQ_MP (@lem1230536 A x' a1 R _22444) (@lem1229049 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1230539 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1230540 {A : Type'} (R : type1402 A) (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term1018 A x' a1 R _22444) = (term1019 A R x' _22444 a1).
Proof. exact (@lem1230539 (term1015 A a1 R _22444) (term875 A x' _22444 a1)). Qed.
Lemma lem1230542 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230543 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1020 A a1 R _22444) = (term1021 A a1 R _22444).
Proof. exact (@lem1230542 (term112 A R a1 _22444) (term1012 A a1 R _22444)). Qed.
Lemma lem1230545 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230546 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1022 A a1 R _22444) = (term1023 A a1 R _22444).
Proof. exact (@lem1230545 (term253 A R a1) (term253 A R _22444)). Qed.
Lemma lem1230548 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230549 {A : Type'} (R : type1402 A) (a1 : list A) : (term1024 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230548 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230551 {A : Type'} (R : type1402 A) (a1 : list A) : (term1025 A R a1) = (term89 A R a1).
Proof. exact (MK_COMB (@lem1230550) (@lem1230549 A R a1)). Qed.
Lemma lem1230553 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230554 {A : Type'} (R : type1402 A) (_22444 : list A) : (term1024 A R _22444) = (@List.ForallOrdPairs A R _22444).
Proof. exact (@lem1230553 (@List.ForallOrdPairs A R _22444)). Qed.
Lemma lem1230555 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1023 A a1 R _22444) = (term1026 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230551 A R a1) (@lem1230554 A R _22444)). Qed.
Lemma lem1230556 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1022 A a1 R _22444) = (term1026 A a1 R _22444).
Proof. exact (TRANS (@lem1230546 A a1 R _22444) (@lem1230555 A a1 R _22444)). Qed.
Lemma lem1230557 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term1027 A R a1 _22444) = (term1027 A R a1 _22444).
Proof. exact (eq_refl (term1027 A R a1 _22444)). Qed.
Lemma lem1230558 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1021 A a1 R _22444) = (term1028 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230557 A R a1 _22444) (@lem1230556 A a1 R _22444)). Qed.
Lemma lem1230559 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1020 A a1 R _22444) = (term1028 A a1 R _22444).
Proof. exact (TRANS (@lem1230543 A a1 R _22444) (@lem1230558 A a1 R _22444)). Qed.
Lemma lem1230560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1230561 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1029 A a1 R _22444) = (term1030 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230560) (@lem1230559 A a1 R _22444)). Qed.
Lemma lem1230562 {A : Type'} (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term875 A x' _22444 a1) = (term875 A x' _22444 a1).
Proof. exact (eq_refl (term875 A x' _22444 a1)). Qed.
Lemma lem1230563 {A : Type'} (R : type1402 A) (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term1019 A R x' _22444 a1) = (term1031 A R x' _22444 a1).
Proof. exact (MK_COMB (@lem1230561 A a1 R _22444) (@lem1230562 A x' _22444 a1)). Qed.
Lemma lem1230564 {A : Type'} (R : type1402 A) (x' : type1141 A) (_22444 : list A) (a1 : list A) : (term1018 A x' a1 R _22444) = (term1031 A R x' _22444 a1).
Proof. exact (TRANS (@lem1230540 A R x' _22444 a1) (@lem1230563 A R x' _22444 a1)). Qed.
Lemma lem1230566 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1026 A a1 R m.
Proof. exact (conj (@lem1230371 A x a0 a1 m R h1) (@lem1230378 A x a0 a1 m R h1)). Qed.
Lemma lem1230567 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term720 A x a0 a1 m R) : term1028 A a1 R m.
Proof. exact (conj (@lem1230364 A R a1 m h1) (@lem1230566 A x a0 a1 m R h2)). Qed.
Lemma lem1230569 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1031 A R x' _22444 a1.
Proof. exact (EQ_MP (@lem1230564 A R x' _22444 a1) (@lem1230537 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1230570 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1031 A R x' _22444 a1.
Proof. exact (@lem1230569 A _22444 x' y' a1 R h1). Qed.
Lemma lem1230571 {A : Type'} (m : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1031 A R x' m a1.
Proof. exact (@lem1230570 A m x' y' a1 R h1). Qed.
Lemma lem1230574 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term875 A x' m a1.
Proof. exact (@lem1230571 A m x' y' a1 R h2 (@lem1230567 A x a0 a1 m R h1 h3)). Qed.
Lemma lem1230575 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1032 A x' m a1.
Proof. exact (fun h0 : term1033 A x' m a1 => @lem1230574 A x' y' x a0 a1 m R h1 h2 h3). Qed.
Lemma lem1230577 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230578 {A : Type'} (x' : type1141 A) (m : list A) (a1 : list A) : (term1032 A x' m a1) = (term875 A x' m a1).
Proof. exact (@lem1230577 (term875 A x' m a1)). Qed.
Lemma lem1230579 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term875 A x' m a1.
Proof. exact (EQ_MP (@lem1230578 A x' m a1) (@lem1230575 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230582 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (h1). Qed.
Lemma lem1230583 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term1003 A R a1 m.
Proof. exact (fun h0 : term112 A R a1 m => @lem1230582 A R a1 m h1). Qed.
Lemma lem1230585 (p : Prop) : (term1004 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1230586 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term1003 A R a1 m) = (term441 A R a1 m).
Proof. exact (@lem1230585 (term112 A R a1 m)). Qed.
Lemma lem1230587 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term441 A R a1 m.
Proof. exact (EQ_MP (@lem1230586 A R a1 m) (@lem1230583 A R a1 m h1)). Qed.
Lemma lem1230589 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (proj2 (@lem1225599 A x a0 a1 m R h1)). Qed.
Lemma lem1230590 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R a1.
Proof. exact (fun h0 : term253 A R a1 => @lem1230589 A x a0 a1 m R h1). Qed.
Lemma lem1230592 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230593 {A : Type'} (R : type1402 A) (a1 : list A) : (term945 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230592 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230594 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1230593 A R a1) (@lem1230590 A x a0 a1 m R h1)). Qed.
Lemma lem1230596 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (proj1 (@lem1225598 A x a0 a1 m R h1)). Qed.
Lemma lem1230597 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term945 A R m.
Proof. exact (fun h0 : term253 A R m => @lem1230596 A x a0 a1 m R h1). Qed.
Lemma lem1230599 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230600 {A : Type'} (R : type1402 A) (m : list A) : (term945 A R m) = (@List.ForallOrdPairs A R m).
Proof. exact (@lem1230599 (@List.ForallOrdPairs A R m)). Qed.
Lemma lem1230601 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : @List.ForallOrdPairs A R m.
Proof. exact (EQ_MP (@lem1230600 A R m) (@lem1230597 A x a0 a1 m R h1)). Qed.
Lemma lem1230617 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230618 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term882 A a1 R x' y' _22444) = (term1034 A a1 R x' y' _22444).
Proof. exact (@lem1230617 (term253 A R _22444) (term253 A R a1) (term750 A R x' y' _22444)). Qed.
Lemma lem1230632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230633 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1035 A a1 R x' y' _22444) = (term1036 A x' y' _22444 R a1).
Proof. exact (@lem1230632 (term750 A R x' y' _22444) (term253 A R a1)). Qed.
Lemma lem1230639 {A : Type'} (R : type1402 A) (_22444 : list A) : (term204 A R _22444) = (term204 A R _22444).
Proof. exact (eq_refl (term204 A R _22444)). Qed.
Lemma lem1230640 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1034 A a1 R x' y' _22444) = (term1037 A x' y' _22444 R a1).
Proof. exact (MK_COMB (@lem1230639 A R _22444) (@lem1230633 A x' y' _22444 R a1)). Qed.
Lemma lem1230644 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230645 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1037 A x' y' _22444 R a1) = (term1038 A x' y' _22444 R a1).
Proof. exact (@lem1230644 (term750 A R x' y' _22444) (term253 A R _22444) (term253 A R a1)). Qed.
Lemma lem1230661 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1034 A a1 R x' y' _22444) = (term1038 A x' y' _22444 R a1).
Proof. exact (TRANS (@lem1230640 A x' y' _22444 R a1) (@lem1230645 A x' y' _22444 R a1)). Qed.
Lemma lem1230662 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term882 A a1 R x' y' _22444) = (term1038 A x' y' _22444 R a1).
Proof. exact (TRANS (@lem1230618 A a1 R x' y' _22444) (@lem1230661 A x' y' _22444 R a1)). Qed.
Lemma lem1230663 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term216 A R a1 _22444) = (term216 A R a1 _22444).
Proof. exact (eq_refl (term216 A R a1 _22444)). Qed.
Lemma lem1230664 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term892 A a1 R x' y' _22444) = (term1039 A x' y' _22444 R a1).
Proof. exact (MK_COMB (@lem1230663 A R a1 _22444) (@lem1230662 A x' y' _22444 R a1)). Qed.
Lemma lem1230675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1230676 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1040 A a1 R x' y' _22444) = (term1041 A x' y' _22444 R a1).
Proof. exact (MK_COMB (@lem1230675) (@lem1230664 A x' y' _22444 R a1)). Qed.
Lemma lem1230680 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230681 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1042 A x' y' a1 R _22444) = (term1043 A x' y' a1 R _22444).
Proof. exact (@lem1230680 (term112 A R a1 _22444) (term750 A R x' y' _22444) (term1012 A a1 R _22444)). Qed.
Lemma lem1230705 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230706 {A : Type'} (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1012 A a1 R _22444) = (term1012 A _22444 R a1).
Proof. exact (@lem1230705 (term253 A R _22444) (term253 A R a1)). Qed.
Lemma lem1230712 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term1044 A R x' y' _22444) = (term1044 A R x' y' _22444).
Proof. exact (eq_refl (term1044 A R x' y' _22444)). Qed.
Lemma lem1230713 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1045 A x' y' a1 R _22444) = (term1038 A x' y' _22444 R a1).
Proof. exact (MK_COMB (@lem1230712 A R x' y' _22444) (@lem1230706 A _22444 R a1)). Qed.
Lemma lem1230724 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term216 A R a1 _22444) = (term216 A R a1 _22444).
Proof. exact (eq_refl (term216 A R a1 _22444)). Qed.
Lemma lem1230725 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1043 A x' y' a1 R _22444) = (term1039 A x' y' _22444 R a1).
Proof. exact (MK_COMB (@lem1230724 A R a1 _22444) (@lem1230713 A x' y' _22444 R a1)). Qed.
Lemma lem1230736 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : (term1042 A x' y' a1 R _22444) = (term1039 A x' y' _22444 R a1).
Proof. exact (TRANS (@lem1230681 A x' y' a1 R _22444) (@lem1230725 A x' y' _22444 R a1)). Qed.
Lemma lem1230737 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : ((term892 A a1 R x' y' _22444) = (term1042 A x' y' a1 R _22444)) = ((term1039 A x' y' _22444 R a1) = (term1039 A x' y' _22444 R a1)).
Proof. exact (MK_COMB (@lem1230676 A x' y' _22444 R a1) (@lem1230736 A x' y' _22444 R a1)). Qed.
Lemma lem1230739 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1230740 (x : Prop) : (x = x) = True.
Proof. exact (@lem1230739 Prop x). Qed.
Lemma lem1230741 {A : Type'} (x' : type1141 A) (y' : type1141 A) (_22444 : list A) (R : type1402 A) (a1 : list A) : ((term1039 A x' y' _22444 R a1) = (term1039 A x' y' _22444 R a1)) = True.
Proof. exact (@lem1230740 (term1039 A x' y' _22444 R a1)). Qed.
Lemma lem1230742 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : ((term892 A a1 R x' y' _22444) = (term1042 A x' y' a1 R _22444)) = True.
Proof. exact (TRANS (@lem1230737 A x' y' _22444 R a1) (@lem1230741 A x' y' _22444 R a1)). Qed.
Lemma lem1230743 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : True = ((term892 A a1 R x' y' _22444) = (term1042 A x' y' a1 R _22444)).
Proof. exact (SYM (@lem1230742 A x' y' a1 R _22444)). Qed.
Lemma lem1230744 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (_22444 : list A) : (term892 A a1 R x' y' _22444) = (term1042 A x' y' a1 R _22444).
Proof. exact (EQ_MP (@lem1230743 A x' y' a1 R _22444) (@lem0)). Qed.
Lemma lem1230745 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1042 A x' y' a1 R _22444.
Proof. exact (EQ_MP (@lem1230744 A x' y' a1 R _22444) (@lem1229035 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1230747 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1230748 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term1042 A x' y' a1 R _22444) = (term1046 A a1 R x' y' _22444).
Proof. exact (@lem1230747 (term1015 A a1 R _22444) (term750 A R x' y' _22444)). Qed.
Lemma lem1230750 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230751 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1020 A a1 R _22444) = (term1021 A a1 R _22444).
Proof. exact (@lem1230750 (term112 A R a1 _22444) (term1012 A a1 R _22444)). Qed.
Lemma lem1230753 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230754 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1022 A a1 R _22444) = (term1023 A a1 R _22444).
Proof. exact (@lem1230753 (term253 A R a1) (term253 A R _22444)). Qed.
Lemma lem1230756 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230757 {A : Type'} (R : type1402 A) (a1 : list A) : (term1024 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230756 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230759 {A : Type'} (R : type1402 A) (a1 : list A) : (term1025 A R a1) = (term89 A R a1).
Proof. exact (MK_COMB (@lem1230758) (@lem1230757 A R a1)). Qed.
Lemma lem1230761 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230762 {A : Type'} (R : type1402 A) (_22444 : list A) : (term1024 A R _22444) = (@List.ForallOrdPairs A R _22444).
Proof. exact (@lem1230761 (@List.ForallOrdPairs A R _22444)). Qed.
Lemma lem1230763 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1023 A a1 R _22444) = (term1026 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230759 A R a1) (@lem1230762 A R _22444)). Qed.
Lemma lem1230764 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1022 A a1 R _22444) = (term1026 A a1 R _22444).
Proof. exact (TRANS (@lem1230754 A a1 R _22444) (@lem1230763 A a1 R _22444)). Qed.
Lemma lem1230765 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term1027 A R a1 _22444) = (term1027 A R a1 _22444).
Proof. exact (eq_refl (term1027 A R a1 _22444)). Qed.
Lemma lem1230766 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1021 A a1 R _22444) = (term1028 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230765 A R a1 _22444) (@lem1230764 A a1 R _22444)). Qed.
Lemma lem1230767 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1020 A a1 R _22444) = (term1028 A a1 R _22444).
Proof. exact (TRANS (@lem1230751 A a1 R _22444) (@lem1230766 A a1 R _22444)). Qed.
Lemma lem1230768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1230769 {A : Type'} (a1 : list A) (R : type1402 A) (_22444 : list A) : (term1029 A a1 R _22444) = (term1030 A a1 R _22444).
Proof. exact (MK_COMB (@lem1230768) (@lem1230767 A a1 R _22444)). Qed.
Lemma lem1230770 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term750 A R x' y' _22444) = (term750 A R x' y' _22444).
Proof. exact (eq_refl (term750 A R x' y' _22444)). Qed.
Lemma lem1230771 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term1046 A a1 R x' y' _22444) = (term1047 A a1 R x' y' _22444).
Proof. exact (MK_COMB (@lem1230769 A a1 R _22444) (@lem1230770 A R x' y' _22444)). Qed.
Lemma lem1230772 {A : Type'} (a1 : list A) (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (_22444 : list A) : (term1042 A x' y' a1 R _22444) = (term1047 A a1 R x' y' _22444).
Proof. exact (TRANS (@lem1230748 A a1 R x' y' _22444) (@lem1230771 A a1 R x' y' _22444)). Qed.
Lemma lem1230774 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1026 A a1 R m.
Proof. exact (conj (@lem1230594 A x a0 a1 m R h1) (@lem1230601 A x a0 a1 m R h1)). Qed.
Lemma lem1230775 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term720 A x a0 a1 m R) : term1028 A a1 R m.
Proof. exact (conj (@lem1230587 A R a1 m h1) (@lem1230774 A x a0 a1 m R h2)). Qed.
Lemma lem1230777 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1047 A a1 R x' y' _22444.
Proof. exact (EQ_MP (@lem1230772 A a1 R x' y' _22444) (@lem1230745 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1230778 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1047 A a1 R x' y' _22444.
Proof. exact (@lem1230777 A _22444 x' y' a1 R h1). Qed.
Lemma lem1230779 {A : Type'} (m : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1047 A a1 R x' y' m.
Proof. exact (@lem1230778 A m x' y' a1 R h1). Qed.
Lemma lem1230782 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term750 A R x' y' m.
Proof. exact (@lem1230779 A m x' y' a1 R h2 (@lem1230775 A x a0 a1 m R h1 h3)). Qed.
Lemma lem1230783 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1048 A R x' y' m.
Proof. exact (fun h0 : term748 A R x' y' m => @lem1230782 A x' y' x a0 a1 m R h1 h2 h3). Qed.
Lemma lem1230785 (p : Prop) : (term1004 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1230786 {A : Type'} (R : type1402 A) (x' : type1141 A) (y' : type1141 A) (m : list A) : (term1048 A R x' y' m) = (term750 A R x' y' m).
Proof. exact (@lem1230785 (term748 A R x' y' m)). Qed.
Lemma lem1230787 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term750 A R x' y' m.
Proof. exact (EQ_MP (@lem1230786 A R x' y' m) (@lem1230783 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230803 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230804 {A : Type'} (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term704 A m R _22448 _22449) = (term924 A R _22448 _22449 m).
Proof. exact (@lem1230803 (term696 A R _22448 _22449) (term455 A _22449 m)). Qed.
Lemma lem1230810 {A : Type'} (_22448 : A) (a1 : list A) : (term703 A _22448 a1) = (term703 A _22448 a1).
Proof. exact (eq_refl (term703 A _22448 a1)). Qed.
Lemma lem1230811 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term913 A a1 m R _22448 _22449) = (term1049 A a1 R _22448 _22449 m).
Proof. exact (MK_COMB (@lem1230810 A _22448 a1) (@lem1230804 A R _22448 _22449 m)). Qed.
Lemma lem1230815 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230816 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term1049 A a1 R _22448 _22449 m) = (term1050 A R _22448 a1 _22449 m).
Proof. exact (@lem1230815 (term696 A R _22448 _22449) (term455 A _22448 a1) (term455 A _22449 m)). Qed.
Lemma lem1230832 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term913 A a1 m R _22448 _22449) = (term1050 A R _22448 a1 _22449 m).
Proof. exact (TRANS (@lem1230811 A a1 R _22448 _22449 m) (@lem1230816 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1230834 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term1051 A a1 m R _22448 _22449) = (term1052 A R _22448 a1 _22449 m).
Proof. exact (MK_COMB (@lem1230833) (@lem1230832 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230838 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230839 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term1053 A m a1 R _22448 _22449) = (term913 A a1 m R _22448 _22449).
Proof. exact (@lem1230838 (term455 A _22448 a1) (term455 A _22449 m) (term696 A R _22448 _22449)). Qed.
Lemma lem1230853 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1230854 {A : Type'} (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term704 A m R _22448 _22449) = (term924 A R _22448 _22449 m).
Proof. exact (@lem1230853 (term696 A R _22448 _22449) (term455 A _22449 m)). Qed.
Lemma lem1230860 {A : Type'} (_22448 : A) (a1 : list A) : (term703 A _22448 a1) = (term703 A _22448 a1).
Proof. exact (eq_refl (term703 A _22448 a1)). Qed.
Lemma lem1230861 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term913 A a1 m R _22448 _22449) = (term1049 A a1 R _22448 _22449 m).
Proof. exact (MK_COMB (@lem1230860 A _22448 a1) (@lem1230854 A R _22448 _22449 m)). Qed.
Lemma lem1230865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1230866 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term1049 A a1 R _22448 _22449 m) = (term1050 A R _22448 a1 _22449 m).
Proof. exact (@lem1230865 (term696 A R _22448 _22449) (term455 A _22448 a1) (term455 A _22449 m)). Qed.
Lemma lem1230882 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term913 A a1 m R _22448 _22449) = (term1050 A R _22448 a1 _22449 m).
Proof. exact (TRANS (@lem1230861 A a1 R _22448 _22449 m) (@lem1230866 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230883 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : (term1053 A m a1 R _22448 _22449) = (term1050 A R _22448 a1 _22449 m).
Proof. exact (TRANS (@lem1230839 A a1 m R _22448 _22449) (@lem1230882 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230884 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : ((term913 A a1 m R _22448 _22449) = (term1053 A m a1 R _22448 _22449)) = ((term1050 A R _22448 a1 _22449 m) = (term1050 A R _22448 a1 _22449 m)).
Proof. exact (MK_COMB (@lem1230834 A R _22448 a1 _22449 m) (@lem1230883 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1230887 (x : Prop) : (x = x) = True.
Proof. exact (@lem1230886 Prop x). Qed.
Lemma lem1230888 {A : Type'} (R : type1402 A) (_22448 : A) (a1 : list A) (_22449 : A) (m : list A) : ((term1050 A R _22448 a1 _22449 m) = (term1050 A R _22448 a1 _22449 m)) = True.
Proof. exact (@lem1230887 (term1050 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230889 {A : Type'} (m : list A) (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : ((term913 A a1 m R _22448 _22449) = (term1053 A m a1 R _22448 _22449)) = True.
Proof. exact (TRANS (@lem1230884 A R _22448 a1 _22449 m) (@lem1230888 A R _22448 a1 _22449 m)). Qed.
Lemma lem1230890 {A : Type'} (m : list A) (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : True = ((term913 A a1 m R _22448 _22449) = (term1053 A m a1 R _22448 _22449)).
Proof. exact (SYM (@lem1230889 A m a1 R _22448 _22449)). Qed.
Lemma lem1230891 {A : Type'} (m : list A) (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term913 A a1 m R _22448 _22449) = (term1053 A m a1 R _22448 _22449).
Proof. exact (EQ_MP (@lem1230890 A m a1 R _22448 _22449) (@lem0)). Qed.
Lemma lem1230892 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1053 A m a1 R _22448 _22449.
Proof. exact (EQ_MP (@lem1230891 A m a1 R _22448 _22449) (@lem1228993 A _22448 _22449 x a0 a1 m R h1)). Qed.
Lemma lem1230894 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1230895 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term1053 A m a1 R _22448 _22449) = (term1054 A a1 R _22448 _22449 m).
Proof. exact (@lem1230894 (term1055 A a1 R _22448 _22449) (term455 A _22449 m)). Qed.
Lemma lem1230897 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230898 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term1056 A a1 R _22448 _22449) = (term1057 A a1 R _22448 _22449).
Proof. exact (@lem1230897 (term455 A _22448 a1) (term696 A R _22448 _22449)). Qed.
Lemma lem1230900 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230901 {A : Type'} (_22448 : A) (a1 : list A) : (term929 A _22448 a1) = (@List.In A _22448 a1).
Proof. exact (@lem1230900 (@List.In A _22448 a1)). Qed.
Lemma lem1230902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230903 {A : Type'} (_22448 : A) (a1 : list A) : (term979 A _22448 a1) = (term713 A _22448 a1).
Proof. exact (MK_COMB (@lem1230902) (@lem1230901 A _22448 a1)). Qed.
Lemma lem1230904 {A : Type'} (R : type1402 A) (_22448 : A) (_22449 : A) : (term712 A R _22448 _22449) = (term712 A R _22448 _22449).
Proof. exact (eq_refl (term712 A R _22448 _22449)). Qed.
Lemma lem1230905 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term1057 A a1 R _22448 _22449) = (term1058 A a1 R _22448 _22449).
Proof. exact (MK_COMB (@lem1230903 A _22448 a1) (@lem1230904 A R _22448 _22449)). Qed.
Lemma lem1230906 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term1056 A a1 R _22448 _22449) = (term1058 A a1 R _22448 _22449).
Proof. exact (TRANS (@lem1230898 A a1 R _22448 _22449) (@lem1230905 A a1 R _22448 _22449)). Qed.
Lemma lem1230907 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1230908 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) : (term1059 A a1 R _22448 _22449) = (term1060 A a1 R _22448 _22449).
Proof. exact (MK_COMB (@lem1230907) (@lem1230906 A a1 R _22448 _22449)). Qed.
Lemma lem1230909 {A : Type'} (_22449 : A) (m : list A) : (term455 A _22449 m) = (term455 A _22449 m).
Proof. exact (eq_refl (term455 A _22449 m)). Qed.
Lemma lem1230910 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term1054 A a1 R _22448 _22449 m) = (term1061 A a1 R _22448 _22449 m).
Proof. exact (MK_COMB (@lem1230908 A a1 R _22448 _22449) (@lem1230909 A _22449 m)). Qed.
Lemma lem1230911 {A : Type'} (a1 : list A) (R : type1402 A) (_22448 : A) (_22449 : A) (m : list A) : (term1053 A m a1 R _22448 _22449) = (term1061 A a1 R _22448 _22449 m).
Proof. exact (TRANS (@lem1230895 A a1 R _22448 _22449 m) (@lem1230910 A a1 R _22448 _22449 m)). Qed.
Lemma lem1230913 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1062 A a1 R x' y' m.
Proof. exact (conj (@lem1230579 A x' y' x a0 a1 m R h1 h2 h3) (@lem1230787 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230915 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1061 A a1 R _22448 _22449 m.
Proof. exact (EQ_MP (@lem1230911 A a1 R _22448 _22449 m) (@lem1230892 A _22448 _22449 x a0 a1 m R h1)). Qed.
Lemma lem1230916 {A : Type'} (_22448 : A) (_22449 : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1061 A a1 R _22448 _22449 m.
Proof. exact (@lem1230915 A _22448 _22449 x a0 a1 m R h1). Qed.
Lemma lem1230917 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term720 A x a0 a1 m R) : term1063 A a1 R x' y' m.
Proof. exact (@lem1230916 A (x' m) (y' m) x a0 a1 m R h1). Qed.
Lemma lem1230920 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1064 A y' m.
Proof. exact (@lem1230917 A x' y' x a0 a1 m R h3 (@lem1230913 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230921 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1065 A y' m.
Proof. exact (fun h0 : term876 A y' m => @lem1230920 A x' y' x a0 a1 m R h1 h2 h3). Qed.
Lemma lem1230923 (p : Prop) : (term1004 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1230924 {A : Type'} (y' : type1141 A) (m : list A) : (term1065 A y' m) = (term1064 A y' m).
Proof. exact (@lem1230923 (term876 A y' m)). Qed.
Lemma lem1230925 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1064 A y' m.
Proof. exact (EQ_MP (@lem1230924 A y' m) (@lem1230921 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230927 (b : Prop) (a : Prop) : (a \/ b) = (term927 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1230928 {A : Type'} (y' : type1141 A) (R : type1402 A) (a1 : list A) (_22444 : list A) : (term917 A a1 R y' _22444) = (term1066 A y' R a1 _22444).
Proof. exact (@lem1230927 (term896 A a1 R y' _22444) (term112 A R a1 _22444)). Qed.
Lemma lem1230930 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230931 {A : Type'} (a1 : list A) (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1067 A a1 R y' _22444) = (term1068 A a1 R y' _22444).
Proof. exact (@lem1230930 (term253 A R a1) (term886 A R y' _22444)). Qed.
Lemma lem1230933 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230934 {A : Type'} (R : type1402 A) (a1 : list A) : (term1024 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1230933 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1230935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230936 {A : Type'} (R : type1402 A) (a1 : list A) : (term1025 A R a1) = (term89 A R a1).
Proof. exact (MK_COMB (@lem1230935) (@lem1230934 A R a1)). Qed.
Lemma lem1230938 (a : Prop) (b : Prop) : (term971 a b) = (term972 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1230939 {A : Type'} (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1069 A R y' _22444) = (term1070 A R y' _22444).
Proof. exact (@lem1230938 (term253 A R _22444) (term876 A y' _22444)). Qed.
Lemma lem1230941 (a : Prop) : (term157 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1230942 {A : Type'} (R : type1402 A) (_22444 : list A) : (term1024 A R _22444) = (@List.ForallOrdPairs A R _22444).
Proof. exact (@lem1230941 (@List.ForallOrdPairs A R _22444)). Qed.
Lemma lem1230943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1230944 {A : Type'} (R : type1402 A) (_22444 : list A) : (term1025 A R _22444) = (term89 A R _22444).
Proof. exact (MK_COMB (@lem1230943) (@lem1230942 A R _22444)). Qed.
Lemma lem1230945 {A : Type'} (y' : type1141 A) (_22444 : list A) : (term1064 A y' _22444) = (term1064 A y' _22444).
Proof. exact (eq_refl (term1064 A y' _22444)). Qed.
Lemma lem1230946 {A : Type'} (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1070 A R y' _22444) = (term1071 A R y' _22444).
Proof. exact (MK_COMB (@lem1230944 A R _22444) (@lem1230945 A y' _22444)). Qed.
Lemma lem1230947 {A : Type'} (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1069 A R y' _22444) = (term1071 A R y' _22444).
Proof. exact (TRANS (@lem1230939 A R y' _22444) (@lem1230946 A R y' _22444)). Qed.
Lemma lem1230948 {A : Type'} (a1 : list A) (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1068 A a1 R y' _22444) = (term1072 A a1 R y' _22444).
Proof. exact (MK_COMB (@lem1230936 A R a1) (@lem1230947 A R y' _22444)). Qed.
Lemma lem1230949 {A : Type'} (a1 : list A) (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1067 A a1 R y' _22444) = (term1072 A a1 R y' _22444).
Proof. exact (TRANS (@lem1230931 A a1 R y' _22444) (@lem1230948 A a1 R y' _22444)). Qed.
Lemma lem1230950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1230951 {A : Type'} (a1 : list A) (R : type1402 A) (y' : type1141 A) (_22444 : list A) : (term1073 A a1 R y' _22444) = (term1074 A a1 R y' _22444).
Proof. exact (MK_COMB (@lem1230950) (@lem1230949 A a1 R y' _22444)). Qed.
Lemma lem1230952 {A : Type'} (R : type1402 A) (a1 : list A) (_22444 : list A) : (term112 A R a1 _22444) = (term112 A R a1 _22444).
Proof. exact (eq_refl (term112 A R a1 _22444)). Qed.
Lemma lem1230953 {A : Type'} (y' : type1141 A) (R : type1402 A) (a1 : list A) (_22444 : list A) : (term1066 A y' R a1 _22444) = (term1075 A y' R a1 _22444).
Proof. exact (MK_COMB (@lem1230951 A a1 R y' _22444) (@lem1230952 A R a1 _22444)). Qed.
Lemma lem1230954 {A : Type'} (y' : type1141 A) (R : type1402 A) (a1 : list A) (_22444 : list A) : (term917 A a1 R y' _22444) = (term1075 A y' R a1 _22444).
Proof. exact (TRANS (@lem1230928 A y' R a1 _22444) (@lem1230953 A y' R a1 _22444)). Qed.
Lemma lem1230956 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1071 A R y' m.
Proof. exact (conj (@lem1230356 A x a0 a1 m R h3) (@lem1230925 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230957 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term1072 A a1 R y' m.
Proof. exact (conj (@lem1230349 A x a0 a1 m R h3) (@lem1230956 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230959 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1075 A y' R a1 _22444.
Proof. exact (EQ_MP (@lem1230954 A y' R a1 _22444) (@lem1229063 A _22444 x' y' a1 R h1)). Qed.
Lemma lem1230960 {A : Type'} (_22444 : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1075 A y' R a1 _22444.
Proof. exact (@lem1230959 A _22444 x' y' a1 R h1). Qed.
Lemma lem1230961 {A : Type'} (m : list A) (x' : type1141 A) (y' : type1141 A) (a1 : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) : term1075 A y' R a1 m.
Proof. exact (@lem1230960 A m x' y' a1 R h1). Qed.
Lemma lem1230964 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term112 A R a1 m.
Proof. exact (@lem1230961 A m x' y' a1 R h2 (@lem1230957 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230965 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) (h2 : term720 A x a0 a1 m R) : term936 A R a1 m.
Proof. exact (fun h0 : term441 A R a1 m => @lem1230964 A x' y' x a0 a1 m R h0 h1 h2). Qed.
Lemma lem1230967 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230968 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term936 A R a1 m) = (term112 A R a1 m).
Proof. exact (@lem1230967 (term112 A R a1 m)). Qed.
Lemma lem1230969 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) (h2 : term720 A x a0 a1 m R) : term112 A R a1 m.
Proof. exact (EQ_MP (@lem1230968 A R a1 m) (@lem1230965 A x' y' x a0 a1 m R h1 h2)). Qed.
Lemma lem1230972 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1230974 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) : (term441 A R a1 m) = (term1076 A R a1 m).
Proof. exact (@lem1230972 (term112 A R a1 m)). Qed.
Lemma lem1230977 {A : Type'} (R : type1402 A) (a1 : list A) (m : list A) (h1 : term441 A R a1 m) : term1076 A R a1 m.
Proof. exact (EQ_MP (@lem1230974 A R a1 m) (@lem1228969 A R a1 m h1)). Qed.
Lemma lem1230980 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : False.
Proof. exact (@lem1230977 A R a1 m h1 (@lem1230969 A x' y' x a0 a1 m R h2 h3)). Qed.
Lemma lem1230981 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : term935.
Proof. exact (fun h0 : ~ False => @lem1230980 A x' y' x a0 a1 m R h1 h2 h3). Qed.
Lemma lem1230983 (p : Prop) : (term923 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1230984 : term935 = False.
Proof. exact (@lem1230983 False). Qed.
Lemma lem1230985 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1230984) (@lem1230981 A x' y' x a0 a1 m R h1 h2 h3)). Qed.
Lemma lem1230986 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem1229533) (@lem1229530 A a1 m R y x a0 h1 h2 h3)). Qed.
Lemma lem1230987 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : (term441 A R a1 m) = False.
Proof. exact (prop_ext (fun h4 : term441 A R a1 m => @lem1230985 A x' y' x a0 a1 m R h1 h2 h3) (fun h4 : False => @lem1228969 A R a1 m h1)). Qed.
Lemma lem1230988 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1230987 A x' y' x a0 a1 m R h1 h2 h3) (@lem1228969 A R a1 m h1)). Qed.
Lemma lem1230989 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : (@List.In A x a1) = False.
Proof. exact (prop_ext (fun h5 : @List.In A x a1 => @lem1229788 A x' y' a0 m R y x a1 h1 h2 h3 h4) (fun h5 : False => @lem1228671 A x a1 h4)). Qed.
Lemma lem1230990 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : False.
Proof. exact (EQ_MP (@lem1230989 A x' y' a0 m R y x a1 h1 h2 h3 h4) (@lem1228671 A x a1 h4)). Qed.
Lemma lem1230991 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem1230986 A a1 m R y x a0 h1 h2 h3) (fun h4 : False => @lem1228581 A x a0 h3)). Qed.
Lemma lem1230992 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem1230991 A a1 m R y x a0 h1 h2 h3) (@lem1228581 A x a0 h3)). Qed.
Lemma lem1230993 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R m) = False.
Proof. exact (prop_ext (fun h4 : term253 A R m => @lem1229458 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1228491 A R m h1)). Qed.
Lemma lem1230994 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1230993 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1228491 A R m h1)). Qed.
Lemma lem1230995 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R a1) = False.
Proof. exact (prop_ext (fun h4 : term253 A R a1 => @lem1229382 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1228405 A R a1 h1)). Qed.
Lemma lem1230996 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1230995 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1228405 A R a1 h1)). Qed.
Lemma lem1230997 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : (term441 A R a1 m) = False.
Proof. exact (prop_ext (fun h4 : term441 A R a1 m => @lem1230988 A x' y' x a0 a1 m R h1 h2 h3) (fun h4 : False => @lem1228078 A R a1 m h1)). Qed.
Lemma lem1230998 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1230997 A x' y' x a0 a1 m R h1 h2 h3) (@lem1228078 A R a1 m h1)). Qed.
Lemma lem1230999 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : (@List.In A x a1) = False.
Proof. exact (prop_ext (fun h5 : @List.In A x a1 => @lem1230990 A x' y' a0 m R y x a1 h1 h2 h3 h4) (fun h5 : False => @lem1227101 A x a1 h4)). Qed.
Lemma lem1231000 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : False.
Proof. exact (EQ_MP (@lem1230999 A x' y' a0 m R y x a1 h1 h2 h3 h4) (@lem1227101 A x a1 h4)). Qed.
Lemma lem1231001 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem1230992 A a1 m R y x a0 h1 h2 h3) (fun h4 : False => @lem1226799 A x a0 h3)). Qed.
Lemma lem1231002 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem1231001 A a1 m R y x a0 h1 h2 h3) (@lem1226799 A x a0 h3)). Qed.
Lemma lem1231003 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R m) = False.
Proof. exact (prop_ext (fun h4 : term253 A R m => @lem1230994 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1226497 A R m h1)). Qed.
Lemma lem1231004 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1231003 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1226497 A R m h1)). Qed.
Lemma lem1231005 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R a1) = False.
Proof. exact (prop_ext (fun h4 : term253 A R a1 => @lem1230996 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1226203 A R a1 h1)). Qed.
Lemma lem1231006 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1231005 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1226203 A R a1 h1)). Qed.
Lemma lem1231007 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : (term441 A R a1 m) = False.
Proof. exact (prop_ext (fun h4 : term441 A R a1 m => @lem1230998 A x' y' x a0 a1 m R h1 h2 h3) (fun h4 : False => @lem1228078 A R a1 m h1)). Qed.
Lemma lem1231008 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term441 A R a1 m) (h2 : term416 A x' y' a1 R) (h3 : term720 A x a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1231007 A x' y' x a0 a1 m R h1 h2 h3) (@lem1228078 A R a1 m h1)). Qed.
Lemma lem1231009 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : (@List.In A x a1) = False.
Proof. exact (prop_ext (fun h5 : @List.In A x a1 => @lem1231000 A x' y' a0 m R y x a1 h1 h2 h3 h4) (fun h5 : False => @lem1227101 A x a1 h4)). Qed.
Lemma lem1231010 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (m : list A) (R : type1402 A) (y : A) (x : A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) (h4 : @List.In A x a1) : False.
Proof. exact (EQ_MP (@lem1231009 A x' y' a0 m R y x a1 h1 h2 h3 h4) (@lem1227101 A x a1 h4)). Qed.
Lemma lem1231011 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : (x = a0) = False.
Proof. exact (prop_ext (fun h4 : x = a0 => @lem1231002 A a1 m R y x a0 h1 h2 h3) (fun h4 : False => @lem1226799 A x a0 h3)). Qed.
Lemma lem1231012 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (y : A) (x : A) (a0 : A) (h1 : term731 A a0 a1 m R x y) (h2 : term722 A a0 a1 m R x y) (h3 : x = a0) : False.
Proof. exact (EQ_MP (@lem1231011 A a1 m R y x a0 h1 h2 h3) (@lem1226799 A x a0 h3)). Qed.
Lemma lem1231013 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R m) = False.
Proof. exact (prop_ext (fun h4 : term253 A R m => @lem1231004 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1226497 A R m h1)). Qed.
Lemma lem1231014 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R m) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1231013 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1226497 A R m h1)). Qed.
Lemma lem1231015 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : (term253 A R a1) = False.
Proof. exact (prop_ext (fun h4 : term253 A R a1 => @lem1231006 A x' y' a0 a1 m R x y h1 h2 h3) (fun h4 : False => @lem1226203 A R a1 h1)). Qed.
Lemma lem1231016 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term253 A R a1) (h2 : term416 A x' y' a1 R) (h3 : term731 A a0 a1 m R x y) : False.
Proof. exact (EQ_MP (@lem1231015 A x' y' a0 a1 m R x y h1 h2 h3) (@lem1226203 A R a1 h1)). Qed.
Lemma lem1231017 {A : Type'} (a1 : list A) (m : list A) (R : type1402 A) (a0 : A) (x : A) (h1 : term720 A x a0 a1 m R) (h2 : term716 A a1 m R a0 x) : False.
Proof. exact (or_elim (@lem1225604 A a1 m R a0 x h2) (fun h0 : term714 A a1 R a0 x => @lem1229975 A x a0 a1 m R h0 h1) (fun h0 : term714 A m R a0 x => @lem1230231 A x a0 a1 m R h0 h1)). Qed.
Lemma lem1231018 {A : Type'} (x' : type1141 A) (y' : type1141 A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) (h2 : term720 A x a0 a1 m R) : False.
Proof. exact (or_elim (@lem1225597 A x a0 a1 m R h2) (fun h0 : term716 A a1 m R a0 x => @lem1231017 A a1 m R a0 x h2 h0) (fun h0 : term441 A R a1 m => @lem1231008 A x' y' x a0 a1 m R h0 h1 h2)). Qed.
Lemma lem1231019 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term722 A a0 a1 m R x y) : False.
Proof. exact (or_elim (@lem1225593 A a0 a1 m R x y h3) (fun h0 : x = a0 => @lem1231012 A a1 m R y x a0 h2 h3 h0) (fun h0 : @List.In A x a1 => @lem1231010 A x' y' a0 m R y x a1 h1 h2 h3 h0)). Qed.
Lemma lem1231020 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term723 A a0 a1 m R x y) : False.
Proof. exact (or_elim (@lem1225583 A a0 a1 m R x y h3) (fun h0 : term253 A R m => @lem1231014 A x' y' a0 a1 m R x y h0 h1 h2) (fun h0 : term722 A a0 a1 m R x y => @lem1231019 A x' y' a0 a1 m R x y h1 h2 h0)). Qed.
Lemma lem1231021 {A : Type'} (x' : type1141 A) (y' : type1141 A) (m : list A) (y : A) (a0 : A) (x : A) (R : type1402 A) (a1 : list A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) (h3 : term724 A a0 x R a1) : False.
Proof. exact (or_elim (@lem1225582 A a0 x R a1 h3) (fun h0 : term714 A a1 R a0 x => @lem1229306 A m y a1 R a0 x h2 h0) (fun h0 : term253 A R a1 => @lem1231016 A x' y' a0 a1 m R x y h0 h1 h2)). Qed.
Lemma lem1231022 {A : Type'} (x' : type1141 A) (y' : type1141 A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (x : A) (y : A) (h1 : term416 A x' y' a1 R) (h2 : term731 A a0 a1 m R x y) : False.
Proof. exact (or_elim (@lem1225576 A a0 a1 m R x y h2) (fun h0 : term724 A a0 x R a1 => @lem1231021 A x' y' m y a0 x R a1 h1 h2 h0) (fun h0 : term723 A a0 a1 m R x y => @lem1231020 A x' y' a0 a1 m R x y h1 h2 h0)). Qed.
Lemma lem1231023 {A : Type'} (x' : type1141 A) (y' : type1141 A) (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term416 A x' y' a1 R) (h2 : term690 A y x a0 a1 m R) : False.
Proof. exact (or_elim (@lem1225413 A y x a0 a1 m R h2) (fun h0 : term731 A a0 a1 m R x y => @lem1231022 A x' y' a0 a1 m R x y h1 h0) (fun h0 : term720 A x a0 a1 m R => @lem1231018 A x' y' x a0 a1 m R h1 h0)). Qed.
Lemma lem1231024 {A : Type'} (x' : type1141 A) (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term419 A x' a1 R) (h2 : term690 A y x a0 a1 m R) : False.
Proof. exact (ex_elim (@lem1225061 A x' a1 R h1) (fun y' : type1141 A => fun h0 : term418 A x' a1 R y' => @lem1231023 A x' y' y x a0 a1 m R h0 h2)). Qed.
Lemma lem1231025 {A : Type'} (y : A) (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term49 A a1 R) (h2 : term690 A y x a0 a1 m R) : False.
Proof. exact (ex_elim (@lem1224150 A a1 R h1) (fun x' : type1141 A => fun h0 : term420 A a1 R x' => @lem1231024 A x' y x a0 a1 m R h0 h2)). Qed.
Lemma lem1231026 {A : Type'} (x : A) (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term49 A a1 R) (h2 : term693 A x a0 a1 m R) : False.
Proof. exact (ex_elim (@lem1225059 A x a0 a1 m R h2) (fun y : A => fun h0 : term692 A x a0 a1 m R y => @lem1231025 A y x a0 a1 m R h1 h0)). Qed.
Lemma lem1231027 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term49 A a1 R) (h2 : term174 A a0 a1 m R) : False.
Proof. exact (ex_elim (@lem1225058 A a0 a1 m R h2) (fun x : A => fun h0 : term694 A a0 a1 m R x => @lem1231026 A x a0 a1 m R h1 h0)). Qed.
Lemma lem1231028 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term49 A a1 R) (h2 : term174 A a0 a1 m R) : (term174 A a0 a1 m R) = False.
Proof. exact (prop_ext (fun h3 : term174 A a0 a1 m R => @lem1231027 A a0 a1 m R h1 h2) (fun h3 : False => @lem1223571 A a0 a1 m R h2)). Qed.
Lemma lem1231029 {A : Type'} (a0 : A) (a1 : list A) (m : list A) (R : type1402 A) (h1 : term49 A a1 R) (h2 : term174 A a0 a1 m R) : False.
Proof. exact (EQ_MP (@lem1231028 A a0 a1 m R h1 h2) (@lem1223571 A a0 a1 m R h2)). Qed.
Lemma lem1231030 {A : Type'} (a0 : A) (m : list A) (a1 : list A) (R : type1402 A) (h1 : term49 A a1 R) : term173 A a0 a1 m R.
Proof. exact (fun h0 : term174 A a0 a1 m R => @lem1231029 A a0 a1 m R h1 h0). Qed.
Lemma lem1231031 {A : Type'} (a0 : A) (m : list A) (a1 : list A) (R : type1402 A) (h1 : term49 A a1 R) : (term113 A a0 R a1 m) = (term140 A a0 a1 m R).
Proof. exact (EQ_MP (@lem1223570 A a0 a1 m R) (@lem1231030 A a0 m a1 R h1)). Qed.
Lemma lem1231036 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (h1 : term49 A a1 R) : term143 A a0 a1 R.
Proof. exact (fun m : list A => @lem1231031 A a0 m a1 R h1). Qed.
Lemma lem1231037 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) : term144 A a0 a1 R.
Proof. exact (fun h0 : term49 A a1 R => @lem1231036 A a0 a1 R h0). Qed.
Lemma lem1231042 {A : Type'} (a0 : A) (R : type1402 A) : term146 A a0 R.
Proof. exact (fun a1 : list A => @lem1231037 A a0 a1 R). Qed.
Lemma lem1231047 {A : Type'} (R : type1402 A) : term148 A R.
Proof. exact (fun a0 : A => @lem1231042 A a0 R). Qed.
Lemma lem1231052 {A : Type'} : term161 A.
Proof. exact (fun R : type1402 A => @lem1231047 A R). Qed.
Lemma lem1231053 {A : Type'} : term160 A.
Proof. exact (EQ_MP (@lem1223565 A) (@lem1231052 A)). Qed.
Lemma lem1231054 {A : Type'} (R : type1402 A) : term1077 A R.
Proof. exact (@lem1231053 A R). Qed.
Lemma lem1231055 {A : Type'} (R : type1402 A) : (term1077 A R) = (term151 A R).
Proof. exact (eq_refl (term1077 A R)). Qed.
Lemma lem1231056 {A : Type'} (R : type1402 A) : term151 A R.
Proof. exact (EQ_MP (@lem1231055 A R) (@lem1231054 A R)). Qed.
Lemma lem1231058 {A : Type'} (R : type1402 A) : term151 A R.
Proof. exact (@lem1223250 A R (@lem1231056 A R)). Qed.
Lemma lem1231059 {A : Type'} (R : type1402 A) (h1 : term152 A R) : False.
Proof. exact (@lem1231058 A R (@lem1223234 A R h1)). Qed.
Lemma lem1231060 {A : Type'} (R : type1402 A) (h1 : term152 A R) : (term152 A R) = False.
Proof. exact (prop_ext (fun h2 : term152 A R => @lem1231059 A R h1) (fun h2 : False => @lem1223234 A R h1)). Qed.
Lemma lem1231061 {A : Type'} (R : type1402 A) (h1 : term152 A R) : False.
Proof. exact (EQ_MP (@lem1231060 A R h1) (@lem1223234 A R h1)). Qed.
Lemma lem1231062 {A : Type'} (R : type1402 A) : term151 A R.
Proof. exact (fun h0 : term152 A R => @lem1231061 A R h0). Qed.
Lemma lem1231063 {A : Type'} (R : type1402 A) : term148 A R.
Proof. exact (EQ_MP (@lem1223233 A R) (@lem1231062 A R)). Qed.
Lemma lem1231064 {A : Type'} (R : type1402 A) : term65 A R.
Proof. exact (EQ_MP (@lem1223229 A R) (@lem1231063 A R)). Qed.
Lemma lem1231065 {A : Type'} (R : type1402 A) : term70 A R.
Proof. exact (@lem1222839 A R (@lem1231064 A R)). Qed.
Lemma lem1231070 {A : Type'} : term1078 A.
Proof. exact (fun R : type1402 A => @lem1231065 A R). Qed.

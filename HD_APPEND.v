Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HD_APPEND_term_abbrevs.
Require Import NOT_CONS_NIL_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095962_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1206725 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1206726 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1206727 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1206726 A h) (@lem1206725 A h)). Qed.
Lemma lem1206728 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem1206727 A h t). Qed.
Lemma lem1206729 {A : Type'} (h : A) (t : list A) : (term2 A h t) = (term3 A h t).
Proof. exact (eq_refl (term2 A h t)). Qed.
Lemma lem1206730 {A : Type'} (h : A) (t : list A) : term3 A h t.
Proof. exact (EQ_MP (@lem1206729 A h t) (@lem1206728 A h t)). Qed.
Lemma lem1206731 {A : Type'} (h : A) (t : list A) : term4 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1206744 {A : Type'} : term5 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1206745 {A : Type'} (h : A) : term6 A h.
Proof. exact (@lem1206744 A h). Qed.
Lemma lem1206746 {A : Type'} (h : A) : (term6 A h) = (term7 A h).
Proof. exact (eq_refl (term6 A h)). Qed.
Lemma lem1206747 {A : Type'} (h : A) : term7 A h.
Proof. exact (EQ_MP (@lem1206746 A h) (@lem1206745 A h)). Qed.
Lemma lem1206748 {A : Type'} (h : A) (t : list A) : term8 A h t.
Proof. exact (@lem1206747 A h t). Qed.
Lemma lem1206749 {A : Type'} (h : A) (t : list A) : (term8 A h t) = (term9 A h t).
Proof. exact (eq_refl (term8 A h t)). Qed.
Lemma lem1206750 {A : Type'} (h : A) (t : list A) : term9 A h t.
Proof. exact (EQ_MP (@lem1206749 A h t) (@lem1206748 A h t)). Qed.
Lemma lem1206751 {A : Type'} (h : A) (t : list A) (l : list A) : term10 A h t l.
Proof. exact (@lem1206750 A h t l). Qed.
Lemma lem1206752 {A : Type'} (h : A) (t : list A) (l : list A) : (term10 A h t l) = ((term11 A h t l) = (term12 A h t l)).
Proof. exact (eq_refl (term10 A h t l)). Qed.
Lemma lem1206754 {A : Type'} : term13 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1206755 {A : Type'} (l : list A) : term14 A l.
Proof. exact (@lem1206754 A l). Qed.
Lemma lem1206756 {A : Type'} (l : list A) : (term14 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term14 A l)). Qed.
Lemma lem1206759 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1206760 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (@lem1206759 A P). Qed.
Lemma lem1206761 {A : Type'} : term16 A.
Proof. exact (@lem1206760 A (term17 A)). Qed.
Lemma lem1206762 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (eq_refl (term18 A)). Qed.
Lemma lem1206763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1206764 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem1206763) (@lem1206762 A)). Qed.
Lemma lem1206765 {A : Type'} (t : list A) : (term22 A t) = (term23 A t).
Proof. exact (eq_refl (term22 A t)). Qed.
Lemma lem1206766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206767 {A : Type'} (t : list A) : (term24 A t) = (term25 A t).
Proof. exact (MK_COMB (@lem1206766) (@lem1206765 A t)). Qed.
Lemma lem1206768 {A : Type'} (h : A) (t : list A) : (term26 A h t) = (term27 A h t).
Proof. exact (eq_refl (term26 A h t)). Qed.
Lemma lem1206769 {A : Type'} (h : A) (t : list A) : (term28 A h t) = (term29 A h t).
Proof. exact (MK_COMB (@lem1206767 A t) (@lem1206768 A h t)). Qed.
Lemma lem1206770 {A : Type'} (h : A) : (term30 A h) = (term31 A h).
Proof. exact (fun_ext (fun t : list A => @lem1206769 A h t)). Qed.
Lemma lem1206771 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1206772 {A : Type'} (h : A) : (term32 A h) = (term33 A h).
Proof. exact (MK_COMB (@lem1206771 A) (@lem1206770 A h)). Qed.
Lemma lem1206773 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun h : A => @lem1206772 A h)). Qed.
Lemma lem1206774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1206775 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem1206774 A) (@lem1206773 A)). Qed.
Lemma lem1206776 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem1206764 A) (@lem1206775 A)). Qed.
Lemma lem1206777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206778 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (MK_COMB (@lem1206777) (@lem1206776 A)). Qed.
Lemma lem1206779 {A : Type'} (l : list A) : (term22 A l) = (term23 A l).
Proof. exact (eq_refl (term22 A l)). Qed.
Lemma lem1206780 {A : Type'} : (term42 A) = (term17 A).
Proof. exact (fun_ext (fun l : list A => @lem1206779 A l)). Qed.
Lemma lem1206781 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1206782 {A : Type'} : (term43 A) = (term44 A).
Proof. exact (MK_COMB (@lem1206781 A) (@lem1206780 A)). Qed.
Lemma lem1206783 {A : Type'} : (term16 A) = (term45 A).
Proof. exact (MK_COMB (@lem1206778 A) (@lem1206782 A)). Qed.
Lemma lem1206784 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem1206783 A) (@lem1206761 A)). Qed.
Lemma lem1206793 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1206756 A l) (@lem1206755 A l)). Qed.
Lemma lem1206794 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1206793 A l). Qed.
Lemma lem1206795 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1206794 A m). Qed.
Lemma lem1206796 {A : Type'} : (@hd A) = (@hd A).
Proof. exact (eq_refl (@hd A)). Qed.
Lemma lem1206797 {A : Type'} (m : list A) : (term46 A m) = (@hd A m).
Proof. exact (MK_COMB (@lem1206796 A) (@lem1206795 A m)). Qed.
Lemma lem1206798 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1206799 {A : Type'} (m : list A) : (term47 A m) = (term48 A m).
Proof. exact (MK_COMB (@lem1206798 A) (@lem1206797 A m)). Qed.
Lemma lem1206801 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term49 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1206802 {A : Type'} (x : list A) (z : A) (y : A) : (term50 A x y z) = y.
Proof. exact (@lem1206801 A (list A) x z y). Qed.
Lemma lem1206803 {A : Type'} (m : list A) : (term51 A m) = (@hd A m).
Proof. exact (@lem1206802 A (@nil A) (@hd A (@nil A)) (@hd A m)). Qed.
Lemma lem1206804 {A : Type'} (m : list A) : ((term46 A m) = (term51 A m)) = ((@hd A m) = (@hd A m)).
Proof. exact (MK_COMB (@lem1206799 A m) (@lem1206803 A m)). Qed.
Lemma lem1206806 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1206806 A x). Qed.
Lemma lem1206808 {A : Type'} (m : list A) : ((@hd A m) = (@hd A m)) = True.
Proof. exact (@lem1206807 A (@hd A m)). Qed.
Lemma lem1206809 {A : Type'} (m : list A) : ((term46 A m) = (term51 A m)) = True.
Proof. exact (TRANS (@lem1206804 A m) (@lem1206808 A m)). Qed.
Lemma lem1206810 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (fun_ext (fun m : list A => @lem1206809 A m)). Qed.
Lemma lem1206811 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1206812 {A : Type'} : (term19 A) = (term54 A).
Proof. exact (MK_COMB (@lem1206811 A) (@lem1206810 A)). Qed.
Lemma lem1206814 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206815 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (@lem1206814 (list A) t). Qed.
Lemma lem1206816 {A : Type'} : (term54 A) = True.
Proof. exact (@lem1206815 A True). Qed.
Lemma lem1206817 {A : Type'} : (term19 A) = True.
Proof. exact (TRANS (@lem1206812 A) (@lem1206816 A)). Qed.
Lemma lem1206818 {A : Type'} : True = (term19 A).
Proof. exact (SYM (@lem1206817 A)). Qed.
Lemma lem1206819 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem1206818 A) (@lem0)). Qed.
Lemma lem1206827 {A : Type'} (h : A) (t : list A) (l : list A) : (term11 A h t l) = (term12 A h t l).
Proof. exact (EQ_MP (@lem1206752 A h t l) (@lem1206751 A h t l)). Qed.
Lemma lem1206828 {A : Type'} (h : A) (t : list A) (l : list A) : (term11 A h t l) = (term12 A h t l).
Proof. exact (@lem1206827 A h t l). Qed.
Lemma lem1206829 {A : Type'} (h : A) (t : list A) (m : list A) : (term11 A h t m) = (term12 A h t m).
Proof. exact (@lem1206828 A h t m). Qed.
Lemma lem1206830 {A : Type'} : (@hd A) = (@hd A).
Proof. exact (eq_refl (@hd A)). Qed.
Lemma lem1206831 {A : Type'} (h : A) (t : list A) (m : list A) : (term57 A h t m) = (term58 A h t m).
Proof. exact (MK_COMB (@lem1206830 A) (@lem1206829 A h t m)). Qed.
Lemma lem1206833 {A : Type'} (t : list A) (h : A) : (term59 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1206834 {A : Type'} (t : list A) (h : A) : (term59 A h t) = h.
Proof. exact (@lem1206833 A t h). Qed.
Lemma lem1206835 {A : Type'} (t : list A) (m : list A) (h : A) : (term58 A h t m) = h.
Proof. exact (@lem1206834 A (@List.app A t m) h). Qed.
Lemma lem1206836 {A : Type'} (t : list A) (m : list A) (h : A) : (term57 A h t m) = h.
Proof. exact (TRANS (@lem1206831 A h t m) (@lem1206835 A t m h)). Qed.
Lemma lem1206837 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1206838 {A : Type'} (t : list A) (m : list A) (h : A) : (term60 A h t m) = (@eq A h).
Proof. exact (MK_COMB (@lem1206837 A) (@lem1206836 A t m h)). Qed.
Lemma lem1206842 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1206731 A h t (@lem1206730 A h t)). Qed.
Lemma lem1206843 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1206842 A h t). Qed.
Lemma lem1206844 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem1206845 {A : Type'} (h : A) (t : list A) : (term61 A h t) = (@COND A False).
Proof. exact (MK_COMB (@lem1206844 A) (@lem1206843 A h t)). Qed.
Lemma lem1206846 {A : Type'} (m : list A) : (@hd A m) = (@hd A m).
Proof. exact (eq_refl (@hd A m)). Qed.
Lemma lem1206847 {A : Type'} (h : A) (t : list A) (m : list A) : (term62 A h t m) = (term63 A m).
Proof. exact (MK_COMB (@lem1206845 A h t) (@lem1206846 A m)). Qed.
Lemma lem1206849 {A : Type'} (t : list A) (h : A) : (term59 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1206850 {A : Type'} (t : list A) (h : A) : (term59 A h t) = h.
Proof. exact (@lem1206849 A t h). Qed.
Lemma lem1206851 {A : Type'} (t : list A) (m : list A) (h : A) : (term64 A m h t) = (term65 A m h).
Proof. exact (MK_COMB (@lem1206847 A h t m) (@lem1206850 A t h)). Qed.
Lemma lem1206853 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1206854 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem1206853 A t1 t2). Qed.
Lemma lem1206855 {A : Type'} (m : list A) (h : A) : (term65 A m h) = h.
Proof. exact (@lem1206854 A (@hd A m) h). Qed.
Lemma lem1206856 {A : Type'} (m : list A) (t : list A) (h : A) : (term64 A m h t) = h.
Proof. exact (TRANS (@lem1206851 A t m h) (@lem1206855 A m h)). Qed.
Lemma lem1206857 {A : Type'} (m : list A) (t : list A) (h : A) : ((term57 A h t m) = (term64 A m h t)) = (h = h).
Proof. exact (MK_COMB (@lem1206838 A t m h) (@lem1206856 A m t h)). Qed.
Lemma lem1206859 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206860 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1206859 A x). Qed.
Lemma lem1206861 {A : Type'} (h : A) : (h = h) = True.
Proof. exact (@lem1206860 A h). Qed.
Lemma lem1206862 {A : Type'} (m : list A) (h : A) (t : list A) : ((term57 A h t m) = (term64 A m h t)) = True.
Proof. exact (TRANS (@lem1206857 A m t h) (@lem1206861 A h)). Qed.
Lemma lem1206863 {A : Type'} (h : A) (t : list A) : (term66 A h t) = (term53 A).
Proof. exact (fun_ext (fun m : list A => @lem1206862 A m h t)). Qed.
Lemma lem1206864 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1206865 {A : Type'} (h : A) (t : list A) : (term27 A h t) = (term54 A).
Proof. exact (MK_COMB (@lem1206864 A) (@lem1206863 A h t)). Qed.
Lemma lem1206867 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206868 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (@lem1206867 (list A) t). Qed.
Lemma lem1206869 {A : Type'} : (term54 A) = True.
Proof. exact (@lem1206868 A True). Qed.
Lemma lem1206870 {A : Type'} (h : A) (t : list A) : (term27 A h t) = True.
Proof. exact (TRANS (@lem1206865 A h t) (@lem1206869 A)). Qed.
Lemma lem1206871 {A : Type'} (h : A) (t : list A) : True = (term27 A h t).
Proof. exact (SYM (@lem1206870 A h t)). Qed.
Lemma lem1206872 {A : Type'} (h : A) (t : list A) : term27 A h t.
Proof. exact (EQ_MP (@lem1206871 A h t) (@lem0)). Qed.
Lemma lem1206873 {A : Type'} (h : A) (t : list A) : term29 A h t.
Proof. exact (fun h0 : term23 A t => @lem1206872 A h t). Qed.
Lemma lem1206878 {A : Type'} (h : A) : term33 A h.
Proof. exact (fun t : list A => @lem1206873 A h t). Qed.
Lemma lem1206883 {A : Type'} : term37 A.
Proof. exact (fun h : A => @lem1206878 A h). Qed.
Lemma lem1206884 {A : Type'} : term39 A.
Proof. exact (conj (@lem1206819 A) (@lem1206883 A)). Qed.
Lemma lem1206885 {A : Type'} : term44 A.
Proof. exact (@lem1206784 A (@lem1206884 A)). Qed.

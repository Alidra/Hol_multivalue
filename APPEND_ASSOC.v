Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_ASSOC_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1111734 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1111735 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1111734 A P). Qed.
Lemma lem1111736 {A : Type'} : term1 A.
Proof. exact (@lem1111735 A (term2 A)). Qed.
Lemma lem1111737 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1111738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1111739 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (MK_COMB (@lem1111738) (@lem1111737 A)). Qed.
Lemma lem1111740 {A : Type'} (t : list A) : (term7 A t) = (term8 A t).
Proof. exact (eq_refl (term7 A t)). Qed.
Lemma lem1111741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111742 {A : Type'} (t : list A) : (term9 A t) = (term10 A t).
Proof. exact (MK_COMB (@lem1111741) (@lem1111740 A t)). Qed.
Lemma lem1111743 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (eq_refl (term11 A h t)). Qed.
Lemma lem1111744 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1111742 A t) (@lem1111743 A h t)). Qed.
Lemma lem1111745 {A : Type'} (h : A) : (term15 A h) = (term16 A h).
Proof. exact (fun_ext (fun t : list A => @lem1111744 A h t)). Qed.
Lemma lem1111746 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111747 {A : Type'} (h : A) : (term17 A h) = (term18 A h).
Proof. exact (MK_COMB (@lem1111746 A) (@lem1111745 A h)). Qed.
Lemma lem1111748 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun h : A => @lem1111747 A h)). Qed.
Lemma lem1111749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1111750 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem1111749 A) (@lem1111748 A)). Qed.
Lemma lem1111751 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem1111739 A) (@lem1111750 A)). Qed.
Lemma lem1111752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1111753 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem1111752) (@lem1111751 A)). Qed.
Lemma lem1111754 {A : Type'} (l : list A) : (term7 A l) = (term8 A l).
Proof. exact (eq_refl (term7 A l)). Qed.
Lemma lem1111755 {A : Type'} : (term27 A) = (term2 A).
Proof. exact (fun_ext (fun l : list A => @lem1111754 A l)). Qed.
Lemma lem1111756 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111757 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem1111756 A) (@lem1111755 A)). Qed.
Lemma lem1111758 {A : Type'} : (term1 A) = (term30 A).
Proof. exact (MK_COMB (@lem1111753 A) (@lem1111757 A)). Qed.
Lemma lem1111759 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem1111758 A) (@lem1111736 A)). Qed.
Lemma lem1111760 {A : Type'} (t : list A) (h1 : term8 A t) : term8 A t.
Proof. exact (h1). Qed.
Lemma lem1111771 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1111772 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1111771 A l). Qed.
Lemma lem1111773 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1111786 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1111773 A l) (@lem1111772 A l)). Qed.
Lemma lem1111787 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1111786 A l). Qed.
Lemma lem1111788 {A : Type'} (m : list A) (n : list A) : (term33 A m n) = (@List.app A m n).
Proof. exact (@lem1111787 A (@List.app A m n)). Qed.
Lemma lem1111789 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111790 {A : Type'} (m : list A) (n : list A) : (term34 A m n) = (term35 A m n).
Proof. exact (MK_COMB (@lem1111789 A) (@lem1111788 A m n)). Qed.
Lemma lem1111792 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1111773 A l) (@lem1111772 A l)). Qed.
Lemma lem1111793 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (@lem1111792 A l). Qed.
Lemma lem1111794 {A : Type'} (m : list A) : (@List.app A (@nil A) m) = m.
Proof. exact (@lem1111793 A m). Qed.
Lemma lem1111795 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1111796 {A : Type'} (m : list A) : (term36 A m) = (@List.app A m).
Proof. exact (MK_COMB (@lem1111795 A) (@lem1111794 A m)). Qed.
Lemma lem1111797 {A : Type'} (n : list A) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1111798 {A : Type'} (m : list A) (n : list A) : (term37 A m n) = (@List.app A m n).
Proof. exact (MK_COMB (@lem1111796 A m) (@lem1111797 A n)). Qed.
Lemma lem1111799 {A : Type'} (m : list A) (n : list A) : ((term33 A m n) = (term37 A m n)) = ((@List.app A m n) = (@List.app A m n)).
Proof. exact (MK_COMB (@lem1111790 A m n) (@lem1111798 A m n)). Qed.
Lemma lem1111801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111802 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1111801 (list A) x). Qed.
Lemma lem1111803 {A : Type'} (m : list A) (n : list A) : ((@List.app A m n) = (@List.app A m n)) = True.
Proof. exact (@lem1111802 A (@List.app A m n)). Qed.
Lemma lem1111804 {A : Type'} (m : list A) (n : list A) : ((term33 A m n) = (term37 A m n)) = True.
Proof. exact (TRANS (@lem1111799 A m n) (@lem1111803 A m n)). Qed.
Lemma lem1111805 {A : Type'} (m : list A) : (term38 A m) = (term39 A).
Proof. exact (fun_ext (fun n : list A => @lem1111804 A m n)). Qed.
Lemma lem1111806 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111807 {A : Type'} (m : list A) : (term40 A m) = (term41 A).
Proof. exact (MK_COMB (@lem1111806 A) (@lem1111805 A m)). Qed.
Lemma lem1111809 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111810 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (@lem1111809 (list A) t). Qed.
Lemma lem1111811 {A : Type'} : (term41 A) = True.
Proof. exact (@lem1111810 A True). Qed.
Lemma lem1111812 {A : Type'} (m : list A) : (term40 A m) = True.
Proof. exact (TRANS (@lem1111807 A m) (@lem1111811 A)). Qed.
Lemma lem1111813 {A : Type'} : (term44 A) = (term39 A).
Proof. exact (fun_ext (fun m : list A => @lem1111812 A m)). Qed.
Lemma lem1111814 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111815 {A : Type'} : (term4 A) = (term41 A).
Proof. exact (MK_COMB (@lem1111814 A) (@lem1111813 A)). Qed.
Lemma lem1111817 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111818 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (@lem1111817 (list A) t). Qed.
Lemma lem1111819 {A : Type'} : (term41 A) = True.
Proof. exact (@lem1111818 A True). Qed.
Lemma lem1111820 {A : Type'} : (term4 A) = True.
Proof. exact (TRANS (@lem1111815 A) (@lem1111819 A)). Qed.
Lemma lem1111821 {A : Type'} : True = (term4 A).
Proof. exact (SYM (@lem1111820 A)). Qed.
Lemma lem1111822 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1111821 A) (@lem0)). Qed.
Lemma lem1111823 {A : Type'} : term45 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1111824 {A : Type'} (h : A) : term46 A h.
Proof. exact (@lem1111823 A h). Qed.
Lemma lem1111825 {A : Type'} (h : A) : (term46 A h) = (term47 A h).
Proof. exact (eq_refl (term46 A h)). Qed.
Lemma lem1111826 {A : Type'} (h : A) : term47 A h.
Proof. exact (EQ_MP (@lem1111825 A h) (@lem1111824 A h)). Qed.
Lemma lem1111827 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (@lem1111826 A h t). Qed.
Lemma lem1111828 {A : Type'} (h : A) (t : list A) : (term48 A h t) = (term49 A h t).
Proof. exact (eq_refl (term48 A h t)). Qed.
Lemma lem1111829 {A : Type'} (h : A) (t : list A) : term49 A h t.
Proof. exact (EQ_MP (@lem1111828 A h t) (@lem1111827 A h t)). Qed.
Lemma lem1111830 {A : Type'} (h : A) (t : list A) (l : list A) : term50 A h t l.
Proof. exact (@lem1111829 A h t l). Qed.
Lemma lem1111831 {A : Type'} (h : A) (t : list A) (l : list A) : (term50 A h t l) = ((term51 A h t l) = (term52 A h t l)).
Proof. exact (eq_refl (term50 A h t l)). Qed.
Lemma lem1111837 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : term53 A t m.
Proof. exact (@lem1111760 A t h1 m). Qed.
Lemma lem1111838 {A : Type'} (t : list A) (m : list A) : (term53 A t m) = (term54 A t m).
Proof. exact (eq_refl (term53 A t m)). Qed.
Lemma lem1111839 {A : Type'} (m : list A) (t : list A) (h1 : term8 A t) : term54 A t m.
Proof. exact (EQ_MP (@lem1111838 A t m) (@lem1111837 A m t h1)). Qed.
Lemma lem1111840 {A : Type'} (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : term55 A t m n.
Proof. exact (@lem1111839 A m t h1 n). Qed.
Lemma lem1111841 {A : Type'} (t : list A) (m : list A) (n : list A) : (term55 A t m n) = ((term56 A t m n) = (term57 A t m n)).
Proof. exact (eq_refl (term55 A t m n)). Qed.
Lemma lem1111854 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (EQ_MP (@lem1111831 A h t l) (@lem1111830 A h t l)). Qed.
Lemma lem1111855 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (@lem1111854 A h t l). Qed.
Lemma lem1111856 {A : Type'} (h : A) (t : list A) (m : list A) (n : list A) : (term58 A h t m n) = (term59 A h t m n).
Proof. exact (@lem1111855 A h t (@List.app A m n)). Qed.
Lemma lem1111858 {A : Type'} (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : (term56 A t m n) = (term57 A t m n).
Proof. exact (EQ_MP (@lem1111841 A t m n) (@lem1111840 A m n t h1)). Qed.
Lemma lem1111859 {A : Type'} (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : (term56 A t m n) = (term57 A t m n).
Proof. exact (@lem1111858 A m n t h1). Qed.
Lemma lem1111860 {A : Type'} (h : A) : (@cons A h) = (@cons A h).
Proof. exact (eq_refl (@cons A h)). Qed.
Lemma lem1111861 {A : Type'} (h : A) (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : (term59 A h t m n) = (term60 A h t m n).
Proof. exact (MK_COMB (@lem1111860 A h) (@lem1111859 A m n t h1)). Qed.
Lemma lem1111862 {A : Type'} (h : A) (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : (term58 A h t m n) = (term60 A h t m n).
Proof. exact (TRANS (@lem1111856 A h t m n) (@lem1111861 A h m n t h1)). Qed.
Lemma lem1111863 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1111864 {A : Type'} (h : A) (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : (term61 A h t m n) = (term62 A h t m n).
Proof. exact (MK_COMB (@lem1111863 A) (@lem1111862 A h m n t h1)). Qed.
Lemma lem1111866 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (EQ_MP (@lem1111831 A h t l) (@lem1111830 A h t l)). Qed.
Lemma lem1111867 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (@lem1111866 A h t l). Qed.
Lemma lem1111868 {A : Type'} (h : A) (t : list A) (m : list A) : (term51 A h t m) = (term52 A h t m).
Proof. exact (@lem1111867 A h t m). Qed.
Lemma lem1111869 {A : Type'} : (@List.app A) = (@List.app A).
Proof. exact (eq_refl (@List.app A)). Qed.
Lemma lem1111870 {A : Type'} (h : A) (t : list A) (m : list A) : (term63 A h t m) = (term64 A h t m).
Proof. exact (MK_COMB (@lem1111869 A) (@lem1111868 A h t m)). Qed.
Lemma lem1111871 {A : Type'} (n : list A) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1111872 {A : Type'} (h : A) (t : list A) (m : list A) (n : list A) : (term65 A h t m n) = (term66 A h t m n).
Proof. exact (MK_COMB (@lem1111870 A h t m) (@lem1111871 A n)). Qed.
Lemma lem1111874 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (EQ_MP (@lem1111831 A h t l) (@lem1111830 A h t l)). Qed.
Lemma lem1111875 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (@lem1111874 A h t l). Qed.
Lemma lem1111876 {A : Type'} (h : A) (t : list A) (m : list A) (n : list A) : (term66 A h t m n) = (term60 A h t m n).
Proof. exact (@lem1111875 A h (@List.app A t m) n). Qed.
Lemma lem1111877 {A : Type'} (h : A) (t : list A) (m : list A) (n : list A) : (term65 A h t m n) = (term60 A h t m n).
Proof. exact (TRANS (@lem1111872 A h t m n) (@lem1111876 A h t m n)). Qed.
Lemma lem1111878 {A : Type'} (h : A) (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : ((term58 A h t m n) = (term65 A h t m n)) = ((term60 A h t m n) = (term60 A h t m n)).
Proof. exact (MK_COMB (@lem1111864 A h m n t h1) (@lem1111877 A h t m n)). Qed.
Lemma lem1111880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1111881 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1111880 (list A) x). Qed.
Lemma lem1111882 {A : Type'} (h : A) (t : list A) (m : list A) (n : list A) : ((term60 A h t m n) = (term60 A h t m n)) = True.
Proof. exact (@lem1111881 A (term60 A h t m n)). Qed.
Lemma lem1111883 {A : Type'} (h : A) (m : list A) (n : list A) (t : list A) (h1 : term8 A t) : ((term58 A h t m n) = (term65 A h t m n)) = True.
Proof. exact (TRANS (@lem1111878 A h m n t h1) (@lem1111882 A h t m n)). Qed.
Lemma lem1111884 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term67 A h t m) = (term39 A).
Proof. exact (fun_ext (fun n : list A => @lem1111883 A h m n t h1)). Qed.
Lemma lem1111885 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111886 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term68 A h t m) = (term41 A).
Proof. exact (MK_COMB (@lem1111885 A) (@lem1111884 A h m t h1)). Qed.
Lemma lem1111888 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111889 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (@lem1111888 (list A) t). Qed.
Lemma lem1111890 {A : Type'} : (term41 A) = True.
Proof. exact (@lem1111889 A True). Qed.
Lemma lem1111891 {A : Type'} (h : A) (m : list A) (t : list A) (h1 : term8 A t) : (term68 A h t m) = True.
Proof. exact (TRANS (@lem1111886 A h m t h1) (@lem1111890 A)). Qed.
Lemma lem1111892 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term69 A h t) = (term39 A).
Proof. exact (fun_ext (fun m : list A => @lem1111891 A h m t h1)). Qed.
Lemma lem1111893 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1111894 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = (term41 A).
Proof. exact (MK_COMB (@lem1111893 A) (@lem1111892 A h t h1)). Qed.
Lemma lem1111896 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1111897 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (@lem1111896 (list A) t). Qed.
Lemma lem1111898 {A : Type'} : (term41 A) = True.
Proof. exact (@lem1111897 A True). Qed.
Lemma lem1111899 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : (term12 A h t) = True.
Proof. exact (TRANS (@lem1111894 A h t h1) (@lem1111898 A)). Qed.
Lemma lem1111900 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : True = (term12 A h t).
Proof. exact (SYM (@lem1111899 A h t h1)). Qed.
Lemma lem1111901 {A : Type'} (h : A) (t : list A) (h1 : term8 A t) : term12 A h t.
Proof. exact (EQ_MP (@lem1111900 A h t h1) (@lem0)). Qed.
Lemma lem1111902 {A : Type'} (h : A) (t : list A) : term14 A h t.
Proof. exact (fun h0 : term8 A t => @lem1111901 A h t h0). Qed.
Lemma lem1111907 {A : Type'} (h : A) : term18 A h.
Proof. exact (fun t : list A => @lem1111902 A h t). Qed.
Lemma lem1111912 {A : Type'} : term22 A.
Proof. exact (fun h : A => @lem1111907 A h). Qed.
Lemma lem1111913 {A : Type'} : term24 A.
Proof. exact (conj (@lem1111822 A) (@lem1111912 A)). Qed.
Lemma lem1111914 {A : Type'} : term29 A.
Proof. exact (@lem1111759 A (@lem1111913 A)). Qed.

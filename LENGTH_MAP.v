Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_MAP_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm1097797_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1116760 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1116761 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1116760 A P). Qed.
Lemma lem1116762 {A B : Type'} : term1 A B.
Proof. exact (@lem1116761 A (term2 A B)). Qed.
Lemma lem1116763 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (eq_refl (term3 A B)). Qed.
Lemma lem1116764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116765 {A B : Type'} : (term5 A B) = (term6 A B).
Proof. exact (MK_COMB (@lem1116764) (@lem1116763 A B)). Qed.
Lemma lem1116766 {A B : Type'} (t : list A) : (term7 A B t) = (term8 A B t).
Proof. exact (eq_refl (term7 A B t)). Qed.
Lemma lem1116767 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116768 {A B : Type'} (t : list A) : (term9 A B t) = (term10 A B t).
Proof. exact (MK_COMB (@lem1116767) (@lem1116766 A B t)). Qed.
Lemma lem1116769 {A B : Type'} (h : A) (t : list A) : (term11 A B h t) = (term12 A B h t).
Proof. exact (eq_refl (term11 A B h t)). Qed.
Lemma lem1116770 {A B : Type'} (h : A) (t : list A) : (term13 A B h t) = (term14 A B h t).
Proof. exact (MK_COMB (@lem1116768 A B t) (@lem1116769 A B h t)). Qed.
Lemma lem1116771 {A B : Type'} (h : A) : (term15 A B h) = (term16 A B h).
Proof. exact (fun_ext (fun t : list A => @lem1116770 A B h t)). Qed.
Lemma lem1116772 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116773 {A B : Type'} (h : A) : (term17 A B h) = (term18 A B h).
Proof. exact (MK_COMB (@lem1116772 A) (@lem1116771 A B h)). Qed.
Lemma lem1116774 {A B : Type'} : (term19 A B) = (term20 A B).
Proof. exact (fun_ext (fun h : A => @lem1116773 A B h)). Qed.
Lemma lem1116775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1116776 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem1116775 A) (@lem1116774 A B)). Qed.
Lemma lem1116777 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem1116765 A B) (@lem1116776 A B)). Qed.
Lemma lem1116778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116779 {A B : Type'} : (term25 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem1116778) (@lem1116777 A B)). Qed.
Lemma lem1116780 {A B : Type'} (l : list A) : (term7 A B l) = (term8 A B l).
Proof. exact (eq_refl (term7 A B l)). Qed.
Lemma lem1116781 {A B : Type'} : (term27 A B) = (term2 A B).
Proof. exact (fun_ext (fun l : list A => @lem1116780 A B l)). Qed.
Lemma lem1116782 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1116783 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem1116782 A) (@lem1116781 A B)). Qed.
Lemma lem1116784 {A B : Type'} : (term1 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem1116779 A B) (@lem1116783 A B)). Qed.
Lemma lem1116785 {A B : Type'} : term30 A B.
Proof. exact (EQ_MP (@lem1116784 A B) (@lem1116762 A B)). Qed.
Lemma lem1116786 {A B : Type'} (t : list A) (h1 : term8 A B t) : term8 A B t.
Proof. exact (h1). Qed.
Lemma lem1116805 {A B : Type'} : term31 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1116806 {A B : Type'} (f : A -> B) : term32 A B f.
Proof. exact (@lem1116805 A B f). Qed.
Lemma lem1116807 {A B : Type'} (f : A -> B) : (term32 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term32 A B f)). Qed.
Lemma lem1116816 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1116807 A B f) (@lem1116806 A B f)). Qed.
Lemma lem1116817 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (@lem1116816 A B f). Qed.
Lemma lem1116818 {B : Type'} : (@List.length B) = (@List.length B).
Proof. exact (eq_refl (@List.length B)). Qed.
Lemma lem1116819 {A B : Type'} (f : A -> B) : (term33 A B f) = (@List.length B (@nil B)).
Proof. exact (MK_COMB (@lem1116818 B) (@lem1116817 A B f)). Qed.
Lemma lem1116821 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1116822 {B : Type'} : (@List.length B (@nil B)) = (NUMERAL 0).
Proof. exact (@lem1116821 B). Qed.
Lemma lem1116823 {A B : Type'} (f : A -> B) : (term33 A B f) = (NUMERAL 0).
Proof. exact (TRANS (@lem1116819 A B f) (@lem1116822 B)). Qed.
Lemma lem1116824 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1116825 {A B : Type'} (f : A -> B) : (term34 A B f) = term35.
Proof. exact (MK_COMB (@lem1116824) (@lem1116823 A B f)). Qed.
Lemma lem1116827 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1116828 {A B : Type'} (f : A -> B) : ((term33 A B f) = (@List.length A (@nil A))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1116825 A B f) (@lem1116827 A)). Qed.
Lemma lem1116830 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116831 (x : nat) : (x = x) = True.
Proof. exact (@lem1116830 nat x). Qed.
Lemma lem1116832 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1116831 (NUMERAL 0)). Qed.
Lemma lem1116833 {A B : Type'} (f : A -> B) : ((term33 A B f) = (@List.length A (@nil A))) = True.
Proof. exact (TRANS (@lem1116828 A B f) (@lem1116832)). Qed.
Lemma lem1116834 {A B : Type'} : (term36 A B) = (term37 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1116833 A B f)). Qed.
Lemma lem1116835 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1116836 {A B : Type'} : (term4 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem1116835 A B) (@lem1116834 A B)). Qed.
Lemma lem1116838 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116839 {A B : Type'} (t : Prop) : (term40 A B t) = t.
Proof. exact (@lem1116838 (A -> B) t). Qed.
Lemma lem1116840 {A B : Type'} : (term38 A B) = True.
Proof. exact (@lem1116839 A B True). Qed.
Lemma lem1116841 {A B : Type'} : (term4 A B) = True.
Proof. exact (TRANS (@lem1116836 A B) (@lem1116840 A B)). Qed.
Lemma lem1116842 {A B : Type'} : True = (term4 A B).
Proof. exact (SYM (@lem1116841 A B)). Qed.
Lemma lem1116843 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem1116842 A B) (@lem0)). Qed.
Lemma lem1116844 {A : Type'} : term41 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1116845 {A : Type'} (h : A) : term42 A h.
Proof. exact (@lem1116844 A h). Qed.
Lemma lem1116846 {A : Type'} (h : A) : (term42 A h) = (term43 A h).
Proof. exact (eq_refl (term42 A h)). Qed.
Lemma lem1116847 {A : Type'} (h : A) : term43 A h.
Proof. exact (EQ_MP (@lem1116846 A h) (@lem1116845 A h)). Qed.
Lemma lem1116848 {A : Type'} (h : A) (t : list A) : term44 A h t.
Proof. exact (@lem1116847 A h t). Qed.
Lemma lem1116849 {A : Type'} (h : A) (t : list A) : (term44 A h t) = ((term45 A h t) = (term46 A t)).
Proof. exact (eq_refl (term44 A h t)). Qed.
Lemma lem1116852 {A B : Type'} : term47 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1116853 {A B : Type'} (f : A -> B) : term48 A B f.
Proof. exact (@lem1116852 A B f). Qed.
Lemma lem1116854 {A B : Type'} (f : A -> B) : (term48 A B f) = (term49 A B f).
Proof. exact (eq_refl (term48 A B f)). Qed.
Lemma lem1116855 {A B : Type'} (f : A -> B) : term49 A B f.
Proof. exact (EQ_MP (@lem1116854 A B f) (@lem1116853 A B f)). Qed.
Lemma lem1116856 {A B : Type'} (f : A -> B) (h : A) : term50 A B f h.
Proof. exact (@lem1116855 A B f h). Qed.
Lemma lem1116857 {A B : Type'} (h : A) (f : A -> B) : (term50 A B f h) = (term51 A B h f).
Proof. exact (eq_refl (term50 A B f h)). Qed.
Lemma lem1116858 {A B : Type'} (h : A) (f : A -> B) : term51 A B h f.
Proof. exact (EQ_MP (@lem1116857 A B h f) (@lem1116856 A B f h)). Qed.
Lemma lem1116859 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term52 A B h f t.
Proof. exact (@lem1116858 A B h f t). Qed.
Lemma lem1116860 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term52 A B h f t) = ((term53 A B f h t) = (term54 A B h f t)).
Proof. exact (eq_refl (term52 A B h f t)). Qed.
Lemma lem1116866 {A B : Type'} (f : A -> B) (t : list A) (h1 : term8 A B t) : term55 A B t f.
Proof. exact (@lem1116786 A B t h1 f). Qed.
Lemma lem1116867 {A B : Type'} (f : A -> B) (t : list A) : (term55 A B t f) = ((term56 A B f t) = (@List.length A t)).
Proof. exact (eq_refl (term55 A B t f)). Qed.
Lemma lem1116876 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term53 A B f h t) = (term54 A B h f t).
Proof. exact (EQ_MP (@lem1116860 A B h f t) (@lem1116859 A B h f t)). Qed.
Lemma lem1116877 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term53 A B f h t) = (term54 A B h f t).
Proof. exact (@lem1116876 A B h f t). Qed.
Lemma lem1116878 {B : Type'} : (@List.length B) = (@List.length B).
Proof. exact (eq_refl (@List.length B)). Qed.
Lemma lem1116879 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term57 A B f h t) = (term58 A B h f t).
Proof. exact (MK_COMB (@lem1116878 B) (@lem1116877 A B h f t)). Qed.
Lemma lem1116881 {A : Type'} (h : A) (t : list A) : (term45 A h t) = (term46 A t).
Proof. exact (EQ_MP (@lem1116849 A h t) (@lem1116848 A h t)). Qed.
Lemma lem1116882 {B : Type'} (h : B) (t : list B) : (term45 B h t) = (term46 B t).
Proof. exact (@lem1116881 B h t). Qed.
Lemma lem1116883 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term58 A B h f t) = (term59 A B f t).
Proof. exact (@lem1116882 B (f h) (@List.map A B f t)). Qed.
Lemma lem1116885 {A B : Type'} (f : A -> B) (t : list A) (h1 : term8 A B t) : (term56 A B f t) = (@List.length A t).
Proof. exact (EQ_MP (@lem1116867 A B f t) (@lem1116866 A B f t h1)). Qed.
Lemma lem1116886 {A B : Type'} (f : A -> B) (t : list A) (h1 : term8 A B t) : (term56 A B f t) = (@List.length A t).
Proof. exact (@lem1116885 A B f t h1). Qed.
Lemma lem1116887 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1116888 {A B : Type'} (f : A -> B) (t : list A) (h1 : term8 A B t) : (term59 A B f t) = (term46 A t).
Proof. exact (MK_COMB (@lem1116887) (@lem1116886 A B f t h1)). Qed.
Lemma lem1116889 {A B : Type'} (h : A) (f : A -> B) (t : list A) (h1 : term8 A B t) : (term58 A B h f t) = (term46 A t).
Proof. exact (TRANS (@lem1116883 A B h f t) (@lem1116888 A B f t h1)). Qed.
Lemma lem1116890 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h1 : term8 A B t) : (term57 A B f h t) = (term46 A t).
Proof. exact (TRANS (@lem1116879 A B h f t) (@lem1116889 A B h f t h1)). Qed.
Lemma lem1116891 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1116892 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h1 : term8 A B t) : (term60 A B f h t) = (term61 A t).
Proof. exact (MK_COMB (@lem1116891) (@lem1116890 A B f h t h1)). Qed.
Lemma lem1116894 {A : Type'} (h : A) (t : list A) : (term45 A h t) = (term46 A t).
Proof. exact (EQ_MP (@lem1116849 A h t) (@lem1116848 A h t)). Qed.
Lemma lem1116895 {A : Type'} (h : A) (t : list A) : (term45 A h t) = (term46 A t).
Proof. exact (@lem1116894 A h t). Qed.
Lemma lem1116896 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h1 : term8 A B t) : ((term57 A B f h t) = (term45 A h t)) = ((term46 A t) = (term46 A t)).
Proof. exact (MK_COMB (@lem1116892 A B f h t h1) (@lem1116895 A h t)). Qed.
Lemma lem1116898 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116899 (x : nat) : (x = x) = True.
Proof. exact (@lem1116898 nat x). Qed.
Lemma lem1116900 {A : Type'} (t : list A) : ((term46 A t) = (term46 A t)) = True.
Proof. exact (@lem1116899 (term46 A t)). Qed.
Lemma lem1116901 {A B : Type'} (f : A -> B) (h : A) (t : list A) (h1 : term8 A B t) : ((term57 A B f h t) = (term45 A h t)) = True.
Proof. exact (TRANS (@lem1116896 A B f h t h1) (@lem1116900 A t)). Qed.
Lemma lem1116902 {A B : Type'} (h : A) (t : list A) (h1 : term8 A B t) : (term62 A B h t) = (term37 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem1116901 A B f h t h1)). Qed.
Lemma lem1116903 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem1116904 {A B : Type'} (h : A) (t : list A) (h1 : term8 A B t) : (term12 A B h t) = (term38 A B).
Proof. exact (MK_COMB (@lem1116903 A B) (@lem1116902 A B h t h1)). Qed.
Lemma lem1116906 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1116907 {A B : Type'} (t : Prop) : (term40 A B t) = t.
Proof. exact (@lem1116906 (A -> B) t). Qed.
Lemma lem1116908 {A B : Type'} : (term38 A B) = True.
Proof. exact (@lem1116907 A B True). Qed.
Lemma lem1116909 {A B : Type'} (h : A) (t : list A) (h1 : term8 A B t) : (term12 A B h t) = True.
Proof. exact (TRANS (@lem1116904 A B h t h1) (@lem1116908 A B)). Qed.
Lemma lem1116910 {A B : Type'} (h : A) (t : list A) (h1 : term8 A B t) : True = (term12 A B h t).
Proof. exact (SYM (@lem1116909 A B h t h1)). Qed.
Lemma lem1116911 {A B : Type'} (h : A) (t : list A) (h1 : term8 A B t) : term12 A B h t.
Proof. exact (EQ_MP (@lem1116910 A B h t h1) (@lem0)). Qed.
Lemma lem1116912 {A B : Type'} (h : A) (t : list A) : term14 A B h t.
Proof. exact (fun h0 : term8 A B t => @lem1116911 A B h t h0). Qed.
Lemma lem1116917 {A B : Type'} (h : A) : term18 A B h.
Proof. exact (fun t : list A => @lem1116912 A B h t). Qed.
Lemma lem1116922 {A B : Type'} : term22 A B.
Proof. exact (fun h : A => @lem1116917 A B h). Qed.
Lemma lem1116923 {A B : Type'} : term24 A B.
Proof. exact (conj (@lem1116843 A B) (@lem1116922 A B)). Qed.
Lemma lem1116924 {A B : Type'} : term29 A B.
Proof. exact (@lem1116785 A B (@lem1116923 A B)). Qed.

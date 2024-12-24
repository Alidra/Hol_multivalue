Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1482981_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_abs_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1482761 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1482762 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1482763 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1482762 y) (@lem1482761 y)). Qed.
Lemma lem1482764 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1482763 y x). Qed.
Lemma lem1482765 (y : real) (x : real) : (term2 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1482767 (y : real) : term3 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1482768 (y : real) : (term3 y) = (term4 y).
Proof. exact (eq_refl (term3 y)). Qed.
Lemma lem1482769 (y : real) : term4 y.
Proof. exact (EQ_MP (@lem1482768 y) (@lem1482767 y)). Qed.
Lemma lem1482770 (y : real) (x : real) : term5 y x.
Proof. exact (@lem1482769 y x). Qed.
Lemma lem1482771 (y : real) (x : real) : (term5 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term5 y x)). Qed.
Lemma lem1482773 (x : real) : term6 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1482774 (x : real) : (term6 x) = ((real_abs x) = (term7 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1482779 (x : real) : (real_abs x) = (term7 x).
Proof. exact (EQ_MP (@lem1482774 x) (@lem1482773 x)). Qed.
Lemma lem1482780 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1482781 (P : real -> Prop) (x : real) : (term8 P x) = (term9 P x).
Proof. exact (MK_COMB (@lem1482780 P) (@lem1482779 x)). Qed.
Lemma lem1482782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1482783 (P : real -> Prop) (x : real) : (term10 P x) = (term11 P x).
Proof. exact (MK_COMB (@lem1482782) (@lem1482781 P x)). Qed.
Lemma lem1482789 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1482765 y x) (@lem1482764 y x)). Qed.
Lemma lem1482790 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1482789 term14 x). Qed.
Lemma lem1482791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1482792 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1482791) (@lem1482790 x)). Qed.
Lemma lem1482793 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1482794 (P : real -> Prop) (x : real) : (term17 P x) = (term18 P x).
Proof. exact (MK_COMB (@lem1482792 x) (@lem1482793 P x)). Qed.
Lemma lem1482797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1482798 (P : real -> Prop) (x : real) : (term19 P x) = (term20 P x).
Proof. exact (MK_COMB (@lem1482797) (@lem1482794 P x)). Qed.
Lemma lem1482802 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1482771 y x) (@lem1482770 y x)). Qed.
Lemma lem1482803 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1482802 x term14). Qed.
Lemma lem1482804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1482805 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1482804) (@lem1482803 x)). Qed.
Lemma lem1482806 (P : real -> Prop) (x : real) : (term25 P x) = (term25 P x).
Proof. exact (eq_refl (term25 P x)). Qed.
Lemma lem1482807 (P : real -> Prop) (x : real) : (term26 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem1482805 x) (@lem1482806 P x)). Qed.
Lemma lem1482810 (P : real -> Prop) (x : real) : (term28 P x) = (term29 P x).
Proof. exact (MK_COMB (@lem1482798 P x) (@lem1482807 P x)). Qed.
Lemma lem1482813 (P : real -> Prop) (x : real) : ((term8 P x) = (term28 P x)) = ((term9 P x) = (term29 P x)).
Proof. exact (MK_COMB (@lem1482783 P x) (@lem1482810 P x)). Qed.
Lemma lem1482816 (P : real -> Prop) (x : real) : ((term9 P x) = (term29 P x)) = ((term8 P x) = (term28 P x)).
Proof. exact (SYM (@lem1482813 P x)). Qed.
Lemma lem1482817 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term30 _476 _475 _474 _477) = (term31 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1482818 (_474 : real) (_475 : Prop) (P : real -> Prop) (x : real) (_477 : real) : (term32 P x _475 _474 _477) = (term33 _474 _475 P x _477).
Proof. exact (@lem1482817 _474 _475 (term34 P x) _477). Qed.
Lemma lem1482819 (P : real -> Prop) (x : real) : (term35 P x) = (term36 P x).
Proof. exact (@lem1482818 x (term13 x) P x (real_neg x)). Qed.
Lemma lem1482820 (P : real -> Prop) (x : real) : (term37 P x) = ((term25 P x) = (term29 P x)).
Proof. exact (eq_refl (term37 P x)). Qed.
Lemma lem1482821 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1482822 (P : real -> Prop) (x : real) : (term39 P x) = (term40 P x).
Proof. exact (MK_COMB (@lem1482821 x) (@lem1482820 P x)). Qed.
Lemma lem1482823 (P : real -> Prop) (x : real) : (term41 P x) = ((P x) = (term29 P x)).
Proof. exact (eq_refl (term41 P x)). Qed.
Lemma lem1482824 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1482825 (P : real -> Prop) (x : real) : (term43 P x) = (term44 P x).
Proof. exact (MK_COMB (@lem1482824 x) (@lem1482823 P x)). Qed.
Lemma lem1482826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1482827 (P : real -> Prop) (x : real) : (term45 P x) = (term46 P x).
Proof. exact (MK_COMB (@lem1482826) (@lem1482825 P x)). Qed.
Lemma lem1482828 (P : real -> Prop) (x : real) : (term36 P x) = (term47 P x).
Proof. exact (MK_COMB (@lem1482827 P x) (@lem1482822 P x)). Qed.
Lemma lem1482829 (P : real -> Prop) (x : real) : (term35 P x) = ((term9 P x) = (term29 P x)).
Proof. exact (eq_refl (term35 P x)). Qed.
Lemma lem1482830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1482831 (P : real -> Prop) (x : real) : (term48 P x) = (term49 P x).
Proof. exact (MK_COMB (@lem1482830) (@lem1482829 P x)). Qed.
Lemma lem1482832 (P : real -> Prop) (x : real) : ((term35 P x) = (term36 P x)) = (((term9 P x) = (term29 P x)) = (term47 P x)).
Proof. exact (MK_COMB (@lem1482831 P x) (@lem1482828 P x)). Qed.
Lemma lem1482833 (P : real -> Prop) (x : real) : ((term9 P x) = (term29 P x)) = (term47 P x).
Proof. exact (EQ_MP (@lem1482832 P x) (@lem1482819 P x)). Qed.
Lemma lem1482834 (P : real -> Prop) (x : real) : (term47 P x) = ((term9 P x) = (term29 P x)).
Proof. exact (SYM (@lem1482833 P x)). Qed.
Lemma lem1482835 (x : real) (h1 : term13 x) : term13 x.
Proof. exact (h1). Qed.
Lemma lem1482836 (x : real) : (term13 x) = ((term13 x) = True).
Proof. exact (@lem7 (term13 x)). Qed.
Lemma lem1482837 (x : real) (h1 : term13 x) : (term13 x) = True.
Proof. exact (EQ_MP (@lem1482836 x) (@lem1482835 x h1)). Qed.
Lemma lem1482838 (P : real -> Prop) (x : real) : (term50 P x) = (term50 P x).
Proof. exact (eq_refl (term50 P x)). Qed.
Lemma lem1482839 (P : real -> Prop) (x : real) (h1 : term13 x) : (term51 P x) = (term52 P x).
Proof. exact (MK_COMB (@lem1482838 P x) (@lem1482837 x h1)). Qed.
Lemma lem1482840 (P : real -> Prop) (x : real) : (term52 P x) = ((P x) = (term53 P x)).
Proof. exact (eq_refl (term52 P x)). Qed.
Lemma lem1482841 (P : real -> Prop) (x : real) : (term54 P x) = (term54 P x).
Proof. exact (eq_refl (term54 P x)). Qed.
Lemma lem1482842 (P : real -> Prop) (x : real) : ((term51 P x) = (term52 P x)) = ((term51 P x) = ((P x) = (term53 P x))).
Proof. exact (MK_COMB (@lem1482841 P x) (@lem1482840 P x)). Qed.
Lemma lem1482843 (P : real -> Prop) (x : real) : (term51 P x) = ((P x) = (term29 P x)).
Proof. exact (eq_refl (term51 P x)). Qed.
Lemma lem1482844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1482845 (P : real -> Prop) (x : real) : (term54 P x) = (term55 P x).
Proof. exact (MK_COMB (@lem1482844) (@lem1482843 P x)). Qed.
Lemma lem1482846 (P : real -> Prop) (x : real) : ((P x) = (term53 P x)) = ((P x) = (term53 P x)).
Proof. exact (eq_refl ((P x) = (term53 P x))). Qed.
Lemma lem1482847 (P : real -> Prop) (x : real) : ((term51 P x) = ((P x) = (term53 P x))) = (((P x) = (term29 P x)) = ((P x) = (term53 P x))).
Proof. exact (MK_COMB (@lem1482845 P x) (@lem1482846 P x)). Qed.
Lemma lem1482848 (P : real -> Prop) (x : real) : ((term51 P x) = (term52 P x)) = (((P x) = (term29 P x)) = ((P x) = (term53 P x))).
Proof. exact (TRANS (@lem1482842 P x) (@lem1482847 P x)). Qed.
Lemma lem1482849 (P : real -> Prop) (x : real) (h1 : term13 x) : ((P x) = (term29 P x)) = ((P x) = (term53 P x)).
Proof. exact (EQ_MP (@lem1482848 P x) (@lem1482839 P x h1)). Qed.
Lemma lem1482850 (P : real -> Prop) (x : real) (h1 : term13 x) : ((P x) = (term53 P x)) = ((P x) = (term29 P x)).
Proof. exact (SYM (@lem1482849 P x h1)). Qed.
Lemma lem1482851 (x : real) (h1 : term56 x) : term56 x.
Proof. exact (h1). Qed.
Lemma lem1482852 (x : real) : term57 x.
Proof. exact (@lem82 (term13 x)). Qed.
Lemma lem1482853 (x : real) (h1 : term56 x) : (term13 x) = False.
Proof. exact (@lem1482852 x (@lem1482851 x h1)). Qed.
Lemma lem1482854 (P : real -> Prop) (x : real) : (term58 P x) = (term58 P x).
Proof. exact (eq_refl (term58 P x)). Qed.
Lemma lem1482855 (P : real -> Prop) (x : real) (h1 : term56 x) : (term59 P x) = (term60 P x).
Proof. exact (MK_COMB (@lem1482854 P x) (@lem1482853 x h1)). Qed.
Lemma lem1482856 (P : real -> Prop) (x : real) : (term60 P x) = ((term25 P x) = (term61 P x)).
Proof. exact (eq_refl (term60 P x)). Qed.
Lemma lem1482857 (P : real -> Prop) (x : real) : (term62 P x) = (term62 P x).
Proof. exact (eq_refl (term62 P x)). Qed.
Lemma lem1482858 (P : real -> Prop) (x : real) : ((term59 P x) = (term60 P x)) = ((term59 P x) = ((term25 P x) = (term61 P x))).
Proof. exact (MK_COMB (@lem1482857 P x) (@lem1482856 P x)). Qed.
Lemma lem1482859 (P : real -> Prop) (x : real) : (term59 P x) = ((term25 P x) = (term29 P x)).
Proof. exact (eq_refl (term59 P x)). Qed.
Lemma lem1482860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1482861 (P : real -> Prop) (x : real) : (term62 P x) = (term63 P x).
Proof. exact (MK_COMB (@lem1482860) (@lem1482859 P x)). Qed.
Lemma lem1482862 (P : real -> Prop) (x : real) : ((term25 P x) = (term61 P x)) = ((term25 P x) = (term61 P x)).
Proof. exact (eq_refl ((term25 P x) = (term61 P x))). Qed.
Lemma lem1482863 (P : real -> Prop) (x : real) : ((term59 P x) = ((term25 P x) = (term61 P x))) = (((term25 P x) = (term29 P x)) = ((term25 P x) = (term61 P x))).
Proof. exact (MK_COMB (@lem1482861 P x) (@lem1482862 P x)). Qed.
Lemma lem1482864 (P : real -> Prop) (x : real) : ((term59 P x) = (term60 P x)) = (((term25 P x) = (term29 P x)) = ((term25 P x) = (term61 P x))).
Proof. exact (TRANS (@lem1482858 P x) (@lem1482863 P x)). Qed.
Lemma lem1482865 (P : real -> Prop) (x : real) (h1 : term56 x) : ((term25 P x) = (term29 P x)) = ((term25 P x) = (term61 P x)).
Proof. exact (EQ_MP (@lem1482864 P x) (@lem1482855 P x h1)). Qed.
Lemma lem1482866 (P : real -> Prop) (x : real) (h1 : term56 x) : ((term25 P x) = (term61 P x)) = ((term25 P x) = (term29 P x)).
Proof. exact (SYM (@lem1482865 P x h1)). Qed.
Lemma lem1482867 (y : real) : term64 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1482868 (y : real) : (term64 y) = (term65 y).
Proof. exact (eq_refl (term64 y)). Qed.
Lemma lem1482869 (y : real) : term65 y.
Proof. exact (EQ_MP (@lem1482868 y) (@lem1482867 y)). Qed.
Lemma lem1482870 (y : real) (x : real) : term66 y x.
Proof. exact (@lem1482869 y x). Qed.
Lemma lem1482871 (y : real) (x : real) : (term66 y x) = ((real_lt x y) = (term67 y x)).
Proof. exact (eq_refl (term66 y x)). Qed.
Lemma lem1482873 (x : real) : (term13 x) = ((term13 x) = True).
Proof. exact (@lem7 (term13 x)). Qed.
Lemma lem1482880 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1482881 (P : real -> Prop) (x : real) : (term68 P x) = (P x).
Proof. exact (@lem1482880 (P x)). Qed.
Lemma lem1482882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1482883 (P : real -> Prop) (x : real) : (term69 P x) = (term70 P x).
Proof. exact (MK_COMB (@lem1482882) (@lem1482881 P x)). Qed.
Lemma lem1482887 (y : real) (x : real) : (real_lt x y) = (term67 y x).
Proof. exact (EQ_MP (@lem1482871 y x) (@lem1482870 y x)). Qed.
Lemma lem1482888 (x : real) : (term22 x) = (term56 x).
Proof. exact (@lem1482887 term14 x). Qed.
Lemma lem1482890 (x : real) (h1 : term13 x) : (term13 x) = True.
Proof. exact (EQ_MP (@lem1482873 x) (@lem1482835 x h1)). Qed.
Lemma lem1482891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1482892 (x : real) (h1 : term13 x) : (term56 x) = (~ True).
Proof. exact (MK_COMB (@lem1482891) (@lem1482890 x h1)). Qed.
Lemma lem1482894 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1482895 (x : real) (h1 : term13 x) : (term56 x) = False.
Proof. exact (TRANS (@lem1482892 x h1) (@lem1482894)). Qed.
Lemma lem1482896 (x : real) (h1 : term13 x) : (term22 x) = False.
Proof. exact (TRANS (@lem1482888 x) (@lem1482895 x h1)). Qed.
Lemma lem1482897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1482898 (x : real) (h1 : term13 x) : (term24 x) = (and False).
Proof. exact (MK_COMB (@lem1482897) (@lem1482896 x h1)). Qed.
Lemma lem1482899 (P : real -> Prop) (x : real) : (term25 P x) = (term25 P x).
Proof. exact (eq_refl (term25 P x)). Qed.
Lemma lem1482900 (P : real -> Prop) (x : real) (h1 : term13 x) : (term27 P x) = (term71 P x).
Proof. exact (MK_COMB (@lem1482898 x h1) (@lem1482899 P x)). Qed.
Lemma lem1482902 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1482903 (P : real -> Prop) (x : real) : (term71 P x) = False.
Proof. exact (@lem1482902 (term25 P x)). Qed.
Lemma lem1482904 (P : real -> Prop) (x : real) (h1 : term13 x) : (term27 P x) = False.
Proof. exact (TRANS (@lem1482900 P x h1) (@lem1482903 P x)). Qed.
Lemma lem1482905 (P : real -> Prop) (x : real) (h1 : term13 x) : (term53 P x) = (term72 P x).
Proof. exact (MK_COMB (@lem1482883 P x) (@lem1482904 P x h1)). Qed.
Lemma lem1482907 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1482908 (P : real -> Prop) (x : real) : (term72 P x) = (P x).
Proof. exact (@lem1482907 (P x)). Qed.
Lemma lem1482909 (P : real -> Prop) (x : real) (h1 : term13 x) : (term53 P x) = (P x).
Proof. exact (TRANS (@lem1482905 P x h1) (@lem1482908 P x)). Qed.
Lemma lem1482910 (P : real -> Prop) (x : real) : (term73 P x) = (term73 P x).
Proof. exact (eq_refl (term73 P x)). Qed.
Lemma lem1482911 (P : real -> Prop) (x : real) (h1 : term13 x) : ((P x) = (term53 P x)) = ((P x) = (P x)).
Proof. exact (MK_COMB (@lem1482910 P x) (@lem1482909 P x h1)). Qed.
Lemma lem1482913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1482914 (x : Prop) : (x = x) = True.
Proof. exact (@lem1482913 Prop x). Qed.
Lemma lem1482915 (P : real -> Prop) (x : real) : ((P x) = (P x)) = True.
Proof. exact (@lem1482914 (P x)). Qed.
Lemma lem1482916 (P : real -> Prop) (x : real) (h1 : term13 x) : ((P x) = (term53 P x)) = True.
Proof. exact (TRANS (@lem1482911 P x h1) (@lem1482915 P x)). Qed.
Lemma lem1482917 (P : real -> Prop) (x : real) (h1 : term13 x) : True = ((P x) = (term53 P x)).
Proof. exact (SYM (@lem1482916 P x h1)). Qed.
Lemma lem1482918 (P : real -> Prop) (x : real) (h1 : term13 x) : (P x) = (term53 P x).
Proof. exact (EQ_MP (@lem1482917 P x h1) (@lem0)). Qed.
Lemma lem1482919 (y : real) : term64 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1482920 (y : real) : (term64 y) = (term65 y).
Proof. exact (eq_refl (term64 y)). Qed.
Lemma lem1482921 (y : real) : term65 y.
Proof. exact (EQ_MP (@lem1482920 y) (@lem1482919 y)). Qed.
Lemma lem1482922 (y : real) (x : real) : term66 y x.
Proof. exact (@lem1482921 y x). Qed.
Lemma lem1482923 (y : real) (x : real) : (term66 y x) = ((real_lt x y) = (term67 y x)).
Proof. exact (eq_refl (term66 y x)). Qed.
Lemma lem1482925 (x : real) : term57 x.
Proof. exact (@lem82 (term13 x)). Qed.
Lemma lem1482932 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1482933 (P : real -> Prop) (x : real) : (term74 P x) = False.
Proof. exact (@lem1482932 (P x)). Qed.
Lemma lem1482934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1482935 (P : real -> Prop) (x : real) : (term75 P x) = (or False).
Proof. exact (MK_COMB (@lem1482934) (@lem1482933 P x)). Qed.
Lemma lem1482939 (y : real) (x : real) : (real_lt x y) = (term67 y x).
Proof. exact (EQ_MP (@lem1482923 y x) (@lem1482922 y x)). Qed.
Lemma lem1482940 (x : real) : (term22 x) = (term56 x).
Proof. exact (@lem1482939 term14 x). Qed.
Lemma lem1482942 (x : real) (h1 : term56 x) : (term13 x) = False.
Proof. exact (@lem1482925 x (@lem1482851 x h1)). Qed.
Lemma lem1482943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1482944 (x : real) (h1 : term56 x) : (term56 x) = (~ False).
Proof. exact (MK_COMB (@lem1482943) (@lem1482942 x h1)). Qed.
Lemma lem1482946 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1482947 (x : real) (h1 : term56 x) : (term56 x) = True.
Proof. exact (TRANS (@lem1482944 x h1) (@lem1482946)). Qed.
Lemma lem1482948 (x : real) (h1 : term56 x) : (term22 x) = True.
Proof. exact (TRANS (@lem1482940 x) (@lem1482947 x h1)). Qed.
Lemma lem1482949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1482950 (x : real) (h1 : term56 x) : (term24 x) = (and True).
Proof. exact (MK_COMB (@lem1482949) (@lem1482948 x h1)). Qed.
Lemma lem1482951 (P : real -> Prop) (x : real) : (term25 P x) = (term25 P x).
Proof. exact (eq_refl (term25 P x)). Qed.
Lemma lem1482952 (P : real -> Prop) (x : real) (h1 : term56 x) : (term27 P x) = (term76 P x).
Proof. exact (MK_COMB (@lem1482950 x h1) (@lem1482951 P x)). Qed.
Lemma lem1482954 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1482955 (P : real -> Prop) (x : real) : (term76 P x) = (term25 P x).
Proof. exact (@lem1482954 (term25 P x)). Qed.
Lemma lem1482956 (P : real -> Prop) (x : real) (h1 : term56 x) : (term27 P x) = (term25 P x).
Proof. exact (TRANS (@lem1482952 P x h1) (@lem1482955 P x)). Qed.
Lemma lem1482957 (P : real -> Prop) (x : real) (h1 : term56 x) : (term61 P x) = (term77 P x).
Proof. exact (MK_COMB (@lem1482935 P x) (@lem1482956 P x h1)). Qed.
Lemma lem1482959 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1482960 (P : real -> Prop) (x : real) : (term77 P x) = (term25 P x).
Proof. exact (@lem1482959 (term25 P x)). Qed.
Lemma lem1482961 (P : real -> Prop) (x : real) (h1 : term56 x) : (term61 P x) = (term25 P x).
Proof. exact (TRANS (@lem1482957 P x h1) (@lem1482960 P x)). Qed.
Lemma lem1482962 (P : real -> Prop) (x : real) : (term78 P x) = (term78 P x).
Proof. exact (eq_refl (term78 P x)). Qed.
Lemma lem1482963 (P : real -> Prop) (x : real) (h1 : term56 x) : ((term25 P x) = (term61 P x)) = ((term25 P x) = (term25 P x)).
Proof. exact (MK_COMB (@lem1482962 P x) (@lem1482961 P x h1)). Qed.
Lemma lem1482965 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1482966 (x : Prop) : (x = x) = True.
Proof. exact (@lem1482965 Prop x). Qed.
Lemma lem1482967 (P : real -> Prop) (x : real) : ((term25 P x) = (term25 P x)) = True.
Proof. exact (@lem1482966 (term25 P x)). Qed.
Lemma lem1482968 (P : real -> Prop) (x : real) (h1 : term56 x) : ((term25 P x) = (term61 P x)) = True.
Proof. exact (TRANS (@lem1482963 P x h1) (@lem1482967 P x)). Qed.
Lemma lem1482969 (P : real -> Prop) (x : real) (h1 : term56 x) : True = ((term25 P x) = (term61 P x)).
Proof. exact (SYM (@lem1482968 P x h1)). Qed.
Lemma lem1482970 (P : real -> Prop) (x : real) (h1 : term56 x) : (term25 P x) = (term61 P x).
Proof. exact (EQ_MP (@lem1482969 P x h1) (@lem0)). Qed.
Lemma lem1482971 (P : real -> Prop) (x : real) (h1 : term56 x) : (term25 P x) = (term29 P x).
Proof. exact (EQ_MP (@lem1482866 P x h1) (@lem1482970 P x h1)). Qed.
Lemma lem1482972 (P : real -> Prop) (x : real) (h1 : term56 x) : (term56 x) = ((term25 P x) = (term29 P x)).
Proof. exact (prop_ext (fun h2 : term56 x => @lem1482971 P x h1) (fun h2 : (term25 P x) = (term29 P x) => @lem1482851 x h1)). Qed.
Lemma lem1482973 (P : real -> Prop) (x : real) (h1 : term56 x) : (term25 P x) = (term29 P x).
Proof. exact (EQ_MP (@lem1482972 P x h1) (@lem1482851 x h1)). Qed.
Lemma lem1482974 (P : real -> Prop) (x : real) : term40 P x.
Proof. exact (fun h0 : term56 x => @lem1482973 P x h0). Qed.
Lemma lem1482975 (P : real -> Prop) (x : real) (h1 : term13 x) : (P x) = (term29 P x).
Proof. exact (EQ_MP (@lem1482850 P x h1) (@lem1482918 P x h1)). Qed.
Lemma lem1482976 (P : real -> Prop) (x : real) (h1 : term13 x) : (term13 x) = ((P x) = (term29 P x)).
Proof. exact (prop_ext (fun h2 : term13 x => @lem1482975 P x h1) (fun h2 : (P x) = (term29 P x) => @lem1482835 x h1)). Qed.
Lemma lem1482977 (P : real -> Prop) (x : real) (h1 : term13 x) : (P x) = (term29 P x).
Proof. exact (EQ_MP (@lem1482976 P x h1) (@lem1482835 x h1)). Qed.
Lemma lem1482978 (P : real -> Prop) (x : real) : term44 P x.
Proof. exact (fun h0 : term13 x => @lem1482977 P x h0). Qed.
Lemma lem1482979 (P : real -> Prop) (x : real) : term47 P x.
Proof. exact (conj (@lem1482978 P x) (@lem1482974 P x)). Qed.
Lemma lem1482980 (P : real -> Prop) (x : real) : (term9 P x) = (term29 P x).
Proof. exact (EQ_MP (@lem1482834 P x) (@lem1482979 P x)). Qed.
Lemma lem1482981 (P : real -> Prop) (x : real) : (term8 P x) = (term28 P x).
Proof. exact (EQ_MP (@lem1482816 P x) (@lem1482980 P x)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RDIV_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_LDIV_EQ_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1628778 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (term0 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1628779 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (real_lt y x) = (term0 x y).
Proof. exact (SYM (@lem1628778 y x h1)). Qed.
Lemma lem1628780 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (real_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1628781 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (term0 x y) = (real_lt y x).
Proof. exact (SYM (@lem1628780 x y h1)). Qed.
Lemma lem1628782 (x : real) (y : real) : ((term0 x y) = (real_lt y x)) = ((real_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_lt y x) => @lem1628779 y x h1) (fun h1 : (real_lt y x) = (term0 x y) => @lem1628781 x y h1)). Qed.
Lemma lem1628783 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1628782 x y)). Qed.
Lemma lem1628784 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628785 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1628784) (@lem1628783 x)). Qed.
Lemma lem1628786 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1628785 x)). Qed.
Lemma lem1628787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628788 : term7 = term8.
Proof. exact (MK_COMB (@lem1628787) (@lem1628786)). Qed.
Lemma lem1628789 : term8.
Proof. exact (EQ_MP (@lem1628788) (@lem1495933)). Qed.
Lemma lem1628790 (x : real) : term9 x.
Proof. exact (@lem1628775 x). Qed.
Lemma lem1628791 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1628792 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1628791 x) (@lem1628790 x)). Qed.
Lemma lem1628793 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1628792 x y). Qed.
Lemma lem1628794 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1628795 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1628794 x y) (@lem1628793 x y)). Qed.
Lemma lem1628796 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1628795 x y z). Qed.
Lemma lem1628797 (x : real) (y : real) (z : real) : (term13 x y z) = (term14 x y z).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1628798 (x : real) (y : real) (z : real) : term14 x y z.
Proof. exact (EQ_MP (@lem1628797 x y z) (@lem1628796 x y z)). Qed.
Lemma lem1628799 (z : real) (h1 : term15 z) : term15 z.
Proof. exact (h1). Qed.
Lemma lem1628800 (x : real) (y : real) (z : real) (h1 : term15 z) : (term16 x z y) = (term17 x y z).
Proof. exact (@lem1628798 x y z (@lem1628799 z h1)). Qed.
Lemma lem1628806 (x : real) : term18 x.
Proof. exact (@lem1628789 x). Qed.
Lemma lem1628807 (x : real) : (term18 x) = (term4 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1628808 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1628807 x) (@lem1628806 x)). Qed.
Lemma lem1628809 (x : real) (y : real) : term19 x y.
Proof. exact (@lem1628808 x y). Qed.
Lemma lem1628810 (x : real) (y : real) : (term19 x y) = ((real_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1628827 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1628828 (p : Prop) (q : Prop) (p' : Prop) : term21 p q p'.
Proof. exact (fun q' : Prop => @lem1628827 p q p' q'). Qed.
Lemma lem1628829 (p : Prop) (q : Prop) : term22 p q.
Proof. exact (fun p' : Prop => @lem1628828 p q p'). Qed.
Lemma lem1628830 (x : real) (z : real) (y : real) : term23 x z y.
Proof. exact (@lem1628829 (term15 z) ((term24 x y z) = (term25 x z y))). Qed.
Lemma lem1628831 (x : real) (z : real) (y : real) (p' : Prop) : term26 x z y p'.
Proof. exact (@lem1628830 x z y p'). Qed.
Lemma lem1628832 (x : real) (z : real) (y : real) (p' : Prop) : (term26 x z y p') = (term27 x z y p').
Proof. exact (eq_refl (term26 x z y p')). Qed.
Lemma lem1628833 (x : real) (z : real) (y : real) (p' : Prop) : term27 x z y p'.
Proof. exact (EQ_MP (@lem1628832 x z y p') (@lem1628831 x z y p')). Qed.
Lemma lem1628834 (x : real) (z : real) (y : real) (p' : Prop) (q' : Prop) : term28 x z y p' q'.
Proof. exact (@lem1628833 x z y p' q'). Qed.
Lemma lem1628835 (x : real) (z : real) (y : real) (p' : Prop) (q' : Prop) : (term28 x z y p' q') = (term29 x z y p' q').
Proof. exact (eq_refl (term28 x z y p' q')). Qed.
Lemma lem1628836 (x : real) (z : real) (y : real) (p' : Prop) (q' : Prop) : term29 x z y p' q'.
Proof. exact (EQ_MP (@lem1628835 x z y p' q') (@lem1628834 x z y p' q')). Qed.
Lemma lem1628838 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628810 x y) (@lem1628809 x y)). Qed.
Lemma lem1628839 (z : real) : (term15 z) = (term30 z).
Proof. exact (@lem1628838 z term31). Qed.
Lemma lem1628840 (x : real) (y : real) (z : real) (q' : Prop) : term32 x y z q'.
Proof. exact (@lem1628836 x z y (term30 z) q'). Qed.
Lemma lem1628841 (x : real) (y : real) (z : real) (q' : Prop) : term33 x y z q'.
Proof. exact (@lem1628840 x y z q' (@lem1628839 z)). Qed.
Lemma lem1628842 (z : real) (h1 : term30 z) : term30 z.
Proof. exact (h1). Qed.
Lemma lem1628843 (z : real) : term34 z.
Proof. exact (@lem82 (term35 z)). Qed.
Lemma lem1628848 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628810 x y) (@lem1628809 x y)). Qed.
Lemma lem1628849 (y : real) (z : real) (x : real) : (term24 x y z) = (term36 y z x).
Proof. exact (@lem1628848 (real_div y z) x). Qed.
Lemma lem1628851 (x : real) (y : real) (z : real) : term14 x y z.
Proof. exact (fun h0 : term15 z => @lem1628800 x y z h0). Qed.
Lemma lem1628852 (y : real) (x : real) (z : real) : term14 y x z.
Proof. exact (@lem1628851 y x z). Qed.
Lemma lem1628854 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628810 x y) (@lem1628809 x y)). Qed.
Lemma lem1628855 (z : real) : (term15 z) = (term30 z).
Proof. exact (@lem1628854 z term31). Qed.
Lemma lem1628857 (z : real) (h1 : term30 z) : (term35 z) = False.
Proof. exact (@lem1628843 z (@lem1628842 z h1)). Qed.
Lemma lem1628858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1628859 (z : real) (h1 : term30 z) : (term30 z) = (~ False).
Proof. exact (MK_COMB (@lem1628858) (@lem1628857 z h1)). Qed.
Lemma lem1628861 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1628862 (z : real) (h1 : term30 z) : (term30 z) = True.
Proof. exact (TRANS (@lem1628859 z h1) (@lem1628861)). Qed.
Lemma lem1628863 (z : real) (h1 : term30 z) : (term15 z) = True.
Proof. exact (TRANS (@lem1628855 z) (@lem1628862 z h1)). Qed.
Lemma lem1628864 (z : real) (h1 : term30 z) : True = (term15 z).
Proof. exact (SYM (@lem1628863 z h1)). Qed.
Lemma lem1628865 (z : real) (h1 : term30 z) : term15 z.
Proof. exact (EQ_MP (@lem1628864 z h1) (@lem0)). Qed.
Lemma lem1628866 (y : real) (x : real) (z : real) (h1 : term30 z) : (term16 y z x) = (term17 y x z).
Proof. exact (@lem1628852 y x z (@lem1628865 z h1)). Qed.
Lemma lem1628867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1628868 (y : real) (x : real) (z : real) (h1 : term30 z) : (term36 y z x) = (term37 y x z).
Proof. exact (MK_COMB (@lem1628867) (@lem1628866 y x z h1)). Qed.
Lemma lem1628869 (y : real) (x : real) (z : real) (h1 : term30 z) : (term24 x y z) = (term37 y x z).
Proof. exact (TRANS (@lem1628849 y z x) (@lem1628868 y x z h1)). Qed.
Lemma lem1628870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1628871 (y : real) (x : real) (z : real) (h1 : term30 z) : (term38 x y z) = (term39 y x z).
Proof. exact (MK_COMB (@lem1628870) (@lem1628869 y x z h1)). Qed.
Lemma lem1628873 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1628810 x y) (@lem1628809 x y)). Qed.
Lemma lem1628874 (y : real) (x : real) (z : real) : (term25 x z y) = (term37 y x z).
Proof. exact (@lem1628873 y (real_mul x z)). Qed.
Lemma lem1628875 (y : real) (x : real) (z : real) (h1 : term30 z) : ((term24 x y z) = (term25 x z y)) = ((term37 y x z) = (term37 y x z)).
Proof. exact (MK_COMB (@lem1628871 y x z h1) (@lem1628874 y x z)). Qed.
Lemma lem1628877 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1628878 (x : Prop) : (x = x) = True.
Proof. exact (@lem1628877 Prop x). Qed.
Lemma lem1628879 (y : real) (x : real) (z : real) : ((term37 y x z) = (term37 y x z)) = True.
Proof. exact (@lem1628878 (term37 y x z)). Qed.
Lemma lem1628880 (x : real) (y : real) (z : real) (h1 : term30 z) : ((term24 x y z) = (term25 x z y)) = True.
Proof. exact (TRANS (@lem1628875 y x z h1) (@lem1628879 y x z)). Qed.
Lemma lem1628881 (x : real) (z : real) (y : real) : term40 x z y.
Proof. exact (fun h0 : term30 z => @lem1628880 x y z h0). Qed.
Lemma lem1628882 (x : real) (y : real) (z : real) : term41 x y z.
Proof. exact (@lem1628841 x y z True). Qed.
Lemma lem1628883 (x : real) (y : real) (z : real) : (term42 x z y) = (term43 z).
Proof. exact (@lem1628882 x y z (@lem1628881 x z y)). Qed.
Lemma lem1628885 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1628886 (z : real) : (term43 z) = True.
Proof. exact (@lem1628885 (term30 z)). Qed.
Lemma lem1628887 (x : real) (z : real) (y : real) : (term42 x z y) = True.
Proof. exact (TRANS (@lem1628883 x y z) (@lem1628886 z)). Qed.
Lemma lem1628888 (x : real) (y : real) : (term44 x y) = term45.
Proof. exact (fun_ext (fun z : real => @lem1628887 x z y)). Qed.
Lemma lem1628889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628890 (x : real) (y : real) : (term46 x y) = term47.
Proof. exact (MK_COMB (@lem1628889) (@lem1628888 x y)). Qed.
Lemma lem1628892 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1628893 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1628892 real t). Qed.
Lemma lem1628894 : term47 = True.
Proof. exact (@lem1628893 True). Qed.
Lemma lem1628895 (x : real) (y : real) : (term46 x y) = True.
Proof. exact (TRANS (@lem1628890 x y) (@lem1628894)). Qed.
Lemma lem1628896 (x : real) : (term50 x) = term45.
Proof. exact (fun_ext (fun y : real => @lem1628895 x y)). Qed.
Lemma lem1628897 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628898 (x : real) : (term51 x) = term47.
Proof. exact (MK_COMB (@lem1628897) (@lem1628896 x)). Qed.
Lemma lem1628900 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1628901 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1628900 real t). Qed.
Lemma lem1628902 : term47 = True.
Proof. exact (@lem1628901 True). Qed.
Lemma lem1628903 (x : real) : (term51 x) = True.
Proof. exact (TRANS (@lem1628898 x) (@lem1628902)). Qed.
Lemma lem1628904 : term52 = term45.
Proof. exact (fun_ext (fun x : real => @lem1628903 x)). Qed.
Lemma lem1628905 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628906 : term53 = term47.
Proof. exact (MK_COMB (@lem1628905) (@lem1628904)). Qed.
Lemma lem1628908 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1628909 (t : Prop) : (term49 t) = t.
Proof. exact (@lem1628908 real t). Qed.
Lemma lem1628910 : term47 = True.
Proof. exact (@lem1628909 True). Qed.
Lemma lem1628911 : term53 = True.
Proof. exact (TRANS (@lem1628906) (@lem1628910)). Qed.
Lemma lem1628912 : True = term53.
Proof. exact (SYM (@lem1628911)). Qed.
Lemma lem1628913 : term53.
Proof. exact (EQ_MP (@lem1628912) (@lem0)). Qed.

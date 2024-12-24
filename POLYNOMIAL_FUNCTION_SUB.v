Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_SUB_term_abbrevs.
Require Import POLYNOMIAL_FUNCTION_ADD_spec.
Require Import POLYNOMIAL_FUNCTION_NEG_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7567722 (p : real -> real) : term0 p.
Proof. exact (@lem7567170 p). Qed.
Lemma lem7567723 (p : real -> real) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem7567724 (p : real -> real) : term1 p.
Proof. exact (EQ_MP (@lem7567723 p) (@lem7567722 p)). Qed.
Lemma lem7567725 (p : real -> real) (q : real -> real) : term2 p q.
Proof. exact (@lem7567724 p q). Qed.
Lemma lem7567726 (p : real -> real) (q : real -> real) : (term2 p q) = (term3 p q).
Proof. exact (eq_refl (term2 p q)). Qed.
Lemma lem7567727 (p : real -> real) (q : real -> real) : term3 p q.
Proof. exact (EQ_MP (@lem7567726 p q) (@lem7567725 p q)). Qed.
Lemma lem7567728 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem7567729 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term5 p q.
Proof. exact (@lem7567727 p q (@lem7567728 p q h1)). Qed.
Lemma lem7567730 (p : real -> real) (q : real -> real) : (term5 p q) = ((term5 p q) = True).
Proof. exact (@lem7 (term5 p q)). Qed.
Lemma lem7567731 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term5 p q) = True.
Proof. exact (EQ_MP (@lem7567730 p q) (@lem7567729 p q h1)). Qed.
Lemma lem7567737 (p : real -> real) : term6 p.
Proof. exact (@lem7567721 p). Qed.
Lemma lem7567738 (p : real -> real) : (term6 p) = ((term7 p) = (polynomial_function p)).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem7567740 (x : real) : term8 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem7567741 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem7567742 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem7567741 x) (@lem7567740 x)). Qed.
Lemma lem7567743 (x : real) (y : real) : term10 x y.
Proof. exact (@lem7567742 x y). Qed.
Lemma lem7567744 (x : real) (y : real) : (term10 x y) = ((real_sub x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem7567757 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term12 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7567758 (p : Prop) (q : Prop) (p' : Prop) : term13 p q p'.
Proof. exact (fun q' : Prop => @lem7567757 p q p' q'). Qed.
Lemma lem7567759 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (fun p' : Prop => @lem7567758 p q p'). Qed.
Lemma lem7567760 (p : real -> real) (q : real -> real) : term15 p q.
Proof. exact (@lem7567759 (term4 p q) (term16 p q)). Qed.
Lemma lem7567761 (p : real -> real) (q : real -> real) (p' : Prop) : term17 p q p'.
Proof. exact (@lem7567760 p q p'). Qed.
Lemma lem7567762 (p : real -> real) (q : real -> real) (p' : Prop) : (term17 p q p') = (term18 p q p').
Proof. exact (eq_refl (term17 p q p')). Qed.
Lemma lem7567763 (p : real -> real) (q : real -> real) (p' : Prop) : term18 p q p'.
Proof. exact (EQ_MP (@lem7567762 p q p') (@lem7567761 p q p')). Qed.
Lemma lem7567764 (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (@lem7567763 p q p' q'). Qed.
Lemma lem7567765 (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : (term19 p q p' q') = (term20 p q p' q').
Proof. exact (eq_refl (term19 p q p' q')). Qed.
Lemma lem7567766 (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : term20 p q p' q'.
Proof. exact (EQ_MP (@lem7567765 p q p' q') (@lem7567764 p q p' q')). Qed.
Lemma lem7567769 (p : real -> real) (q : real -> real) : (term4 p q) = (term4 p q).
Proof. exact (eq_refl (term4 p q)). Qed.
Lemma lem7567770 (p : real -> real) (q : real -> real) (q' : Prop) : term21 p q q'.
Proof. exact (@lem7567766 p q (term4 p q) q'). Qed.
Lemma lem7567771 (p : real -> real) (q : real -> real) (q' : Prop) : term22 p q q'.
Proof. exact (@lem7567770 p q q' (@lem7567769 p q)). Qed.
Lemma lem7567772 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem7567773 (p : real -> real) (q : real -> real) (h1 : term4 p q) : polynomial_function q.
Proof. exact (proj2 (@lem7567772 p q h1)). Qed.
Lemma lem7567774 (q : real -> real) : (polynomial_function q) = ((polynomial_function q) = True).
Proof. exact (@lem7 (polynomial_function q)). Qed.
Lemma lem7567776 (p : real -> real) (q : real -> real) (h1 : term4 p q) : polynomial_function p.
Proof. exact (proj1 (@lem7567772 p q h1)). Qed.
Lemma lem7567777 (p : real -> real) : (polynomial_function p) = ((polynomial_function p) = True).
Proof. exact (@lem7 (polynomial_function p)). Qed.
Lemma lem7567780 (x : real) (y : real) : (real_sub x y) = (term11 x y).
Proof. exact (EQ_MP (@lem7567744 x y) (@lem7567743 x y)). Qed.
Lemma lem7567781 (p : real -> real) (q : real -> real) (x : real) : (term23 p q x) = (term24 p q x).
Proof. exact (@lem7567780 (p x) (q x)). Qed.
Lemma lem7567782 (p : real -> real) (q : real -> real) : (term25 p q) = (term26 p q).
Proof. exact (fun_ext (fun x : real => @lem7567781 p q x)). Qed.
Lemma lem7567783 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7567784 (p : real -> real) (q : real -> real) : (term16 p q) = (term27 p q).
Proof. exact (MK_COMB (@lem7567783) (@lem7567782 p q)). Qed.
Lemma lem7567786 (p : real -> real) (q : real -> real) : term28 p q.
Proof. exact (fun h0 : term4 p q => @lem7567731 p q h0). Qed.
Lemma lem7567787 (p : real -> real) (q : real -> real) : term29 p q.
Proof. exact (@lem7567786 p (term30 q)). Qed.
Lemma lem7567788 (q : real -> real) (x : real) : (term31 q x) = (term32 q x).
Proof. exact (eq_refl (term31 q x)). Qed.
Lemma lem7567789 (p : real -> real) (x : real) : (term33 p x) = (term33 p x).
Proof. exact (eq_refl (term33 p x)). Qed.
Lemma lem7567790 (p : real -> real) (q : real -> real) (x : real) : (term34 p q x) = (term24 p q x).
Proof. exact (MK_COMB (@lem7567789 p x) (@lem7567788 q x)). Qed.
Lemma lem7567791 (p : real -> real) (q : real -> real) : (term35 p q) = (term26 p q).
Proof. exact (fun_ext (fun x : real => @lem7567790 p q x)). Qed.
Lemma lem7567792 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7567793 (p : real -> real) (q : real -> real) : (term36 p q) = (term27 p q).
Proof. exact (MK_COMB (@lem7567792) (@lem7567791 p q)). Qed.
Lemma lem7567794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7567795 (p : real -> real) (q : real -> real) : (term37 p q) = (term38 p q).
Proof. exact (MK_COMB (@lem7567794) (@lem7567793 p q)). Qed.
Lemma lem7567796 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7567797 (p : real -> real) (q : real -> real) : ((term36 p q) = True) = ((term27 p q) = True).
Proof. exact (MK_COMB (@lem7567795 p q) (@lem7567796)). Qed.
Lemma lem7567798 (p : real -> real) (q : real -> real) : (term39 p q) = (term39 p q).
Proof. exact (eq_refl (term39 p q)). Qed.
Lemma lem7567799 (p : real -> real) (q : real -> real) : (term29 p q) = (term40 p q).
Proof. exact (MK_COMB (@lem7567798 p q) (@lem7567797 p q)). Qed.
Lemma lem7567800 (p : real -> real) (q : real -> real) : term40 p q.
Proof. exact (EQ_MP (@lem7567799 p q) (@lem7567787 p q)). Qed.
Lemma lem7567804 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (polynomial_function p) = True.
Proof. exact (EQ_MP (@lem7567777 p) (@lem7567776 p q h1)). Qed.
Lemma lem7567805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7567806 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term41 p) = (and True).
Proof. exact (MK_COMB (@lem7567805) (@lem7567804 p q h1)). Qed.
Lemma lem7567808 (p : real -> real) : (term7 p) = (polynomial_function p).
Proof. exact (EQ_MP (@lem7567738 p) (@lem7567737 p)). Qed.
Lemma lem7567809 (q : real -> real) : (term7 q) = (polynomial_function q).
Proof. exact (@lem7567808 q). Qed.
Lemma lem7567811 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (polynomial_function q) = True.
Proof. exact (EQ_MP (@lem7567774 q) (@lem7567773 p q h1)). Qed.
Lemma lem7567812 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term7 q) = True.
Proof. exact (TRANS (@lem7567809 q) (@lem7567811 p q h1)). Qed.
Lemma lem7567813 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term42 p q) = (True /\ True).
Proof. exact (MK_COMB (@lem7567806 p q h1) (@lem7567812 p q h1)). Qed.
Lemma lem7567815 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7567816 : (True /\ True) = True.
Proof. exact (@lem7567815 True). Qed.
Lemma lem7567817 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term42 p q) = True.
Proof. exact (TRANS (@lem7567813 p q h1) (@lem7567816)). Qed.
Lemma lem7567818 (p : real -> real) (q : real -> real) (h1 : term4 p q) : True = (term42 p q).
Proof. exact (SYM (@lem7567817 p q h1)). Qed.
Lemma lem7567819 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term42 p q.
Proof. exact (EQ_MP (@lem7567818 p q h1) (@lem0)). Qed.
Lemma lem7567820 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term27 p q) = True.
Proof. exact (@lem7567800 p q (@lem7567819 p q h1)). Qed.
Lemma lem7567821 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term16 p q) = True.
Proof. exact (TRANS (@lem7567784 p q) (@lem7567820 p q h1)). Qed.
Lemma lem7567822 (p : real -> real) (q : real -> real) : term43 p q.
Proof. exact (fun h0 : term4 p q => @lem7567821 p q h0). Qed.
Lemma lem7567823 (p : real -> real) (q : real -> real) : term44 p q.
Proof. exact (@lem7567771 p q True). Qed.
Lemma lem7567824 (p : real -> real) (q : real -> real) : (term45 p q) = (term46 p q).
Proof. exact (@lem7567823 p q (@lem7567822 p q)). Qed.
Lemma lem7567826 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7567827 (p : real -> real) (q : real -> real) : (term46 p q) = True.
Proof. exact (@lem7567826 (term4 p q)). Qed.
Lemma lem7567828 (p : real -> real) (q : real -> real) : (term45 p q) = True.
Proof. exact (TRANS (@lem7567824 p q) (@lem7567827 p q)). Qed.
Lemma lem7567829 (p : real -> real) : (term47 p) = term48.
Proof. exact (fun_ext (fun q : real -> real => @lem7567828 p q)). Qed.
Lemma lem7567830 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7567831 (p : real -> real) : (term49 p) = term50.
Proof. exact (MK_COMB (@lem7567830) (@lem7567829 p)). Qed.
Lemma lem7567833 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7567834 (t : Prop) : (term52 t) = t.
Proof. exact (@lem7567833 (real -> real) t). Qed.
Lemma lem7567835 : term50 = True.
Proof. exact (@lem7567834 True). Qed.
Lemma lem7567836 (p : real -> real) : (term49 p) = True.
Proof. exact (TRANS (@lem7567831 p) (@lem7567835)). Qed.
Lemma lem7567837 : term53 = term48.
Proof. exact (fun_ext (fun p : real -> real => @lem7567836 p)). Qed.
Lemma lem7567838 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7567839 : term54 = term50.
Proof. exact (MK_COMB (@lem7567838) (@lem7567837)). Qed.
Lemma lem7567841 {A : Type'} (t : Prop) : (term51 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7567842 (t : Prop) : (term52 t) = t.
Proof. exact (@lem7567841 (real -> real) t). Qed.
Lemma lem7567843 : term50 = True.
Proof. exact (@lem7567842 True). Qed.
Lemma lem7567844 : term54 = True.
Proof. exact (TRANS (@lem7567839) (@lem7567843)). Qed.
Lemma lem7567845 : True = term54.
Proof. exact (SYM (@lem7567844)). Qed.
Lemma lem7567846 : term54.
Proof. exact (EQ_MP (@lem7567845) (@lem0)). Qed.

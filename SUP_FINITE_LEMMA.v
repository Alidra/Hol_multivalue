Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_FINITE_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5136701 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5136702 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5136703 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5136702 t1) (@lem5136701 t1)). Qed.
Lemma lem5136704 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5136703 t1 t2). Qed.
Lemma lem5136705 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5136706 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5136705 t1 t2) (@lem5136704 t1 t2)). Qed.
Lemma lem5136707 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5136706 t1 t2 t3). Qed.
Lemma lem5136708 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5136709 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5136708 t1 t2 t3) (@lem5136707 t1 t2 t3)). Qed.
Lemma lem5136710 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5136709 t1 t2 t3)). Qed.
Lemma lem5136712 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term7 A s) = (term8 A s).
Proof. exact (h1). Qed.
Lemma lem5136713 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term8 A s) = (term7 A s).
Proof. exact (SYM (@lem5136712 A s h1)). Qed.
Lemma lem5136714 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term8 A s) = (term7 A s).
Proof. exact (h1). Qed.
Lemma lem5136715 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term7 A s) = (term8 A s).
Proof. exact (SYM (@lem5136714 A s h1)). Qed.
Lemma lem5136716 {A : Type'} (s : A -> Prop) : ((term7 A s) = (term8 A s)) = ((term8 A s) = (term7 A s)).
Proof. exact (prop_ext (fun h1 : (term7 A s) = (term8 A s) => @lem5136713 A s h1) (fun h1 : (term8 A s) = (term7 A s) => @lem5136715 A s h1)). Qed.
Lemma lem5136717 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5136716 A s)). Qed.
Lemma lem5136718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5136719 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem5136718 A) (@lem5136717 A)). Qed.
Lemma lem5136720 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem5136719 A) (@lem3216368 A)). Qed.
Lemma lem5136721 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem5136720 A s). Qed.
Lemma lem5136722 {A : Type'} (s : A -> Prop) : (term13 A s) = ((term8 A s) = (term7 A s)).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem5136724 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5136725 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem5136726 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem5136725 A x) (@lem5136724 A x)). Qed.
Lemma lem5136727 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem5136726 A x y). Qed.
Lemma lem5136728 {A : Type'} (y : A) (x : A) : (term16 A x y) = (term17 A y x).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem5136729 {A : Type'} (y : A) (x : A) : term17 A y x.
Proof. exact (EQ_MP (@lem5136728 A y x) (@lem5136727 A x y)). Qed.
Lemma lem5136730 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term18 A y x s.
Proof. exact (@lem5136729 A y x s). Qed.
Lemma lem5136731 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term18 A y x s) = ((term19 A x y s) = (term20 A y x s)).
Proof. exact (eq_refl (term18 A y x s)). Qed.
Lemma lem5136733 {A : Type'} (x : A) : term21 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5136734 {A : Type'} (x : A) : (term21 A x) = (term22 A x).
Proof. exact (eq_refl (term21 A x)). Qed.
Lemma lem5136735 {A : Type'} (x : A) : term22 A x.
Proof. exact (EQ_MP (@lem5136734 A x) (@lem5136733 A x)). Qed.
Lemma lem5136736 {A : Type'} (x : A) (s : A -> Prop) : term23 A x s.
Proof. exact (@lem5136735 A x s). Qed.
Lemma lem5136737 {A : Type'} (x : A) (s : A -> Prop) : (term23 A x s) = (term24 A x s).
Proof. exact (eq_refl (term23 A x s)). Qed.
Lemma lem5136738 {A : Type'} (x : A) (s : A -> Prop) : term24 A x s.
Proof. exact (EQ_MP (@lem5136737 A x s) (@lem5136736 A x s)). Qed.
Lemma lem5136739 {A : Type'} (x : A) (s : A -> Prop) : term25 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5136752 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem5136753 {A : Type'} (P : type686 A) (h1 : term26 A) : term27 A P.
Proof. exact (@lem5136752 A h1 P). Qed.
Lemma lem5136754 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem5136755 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (EQ_MP (@lem5136754 A P) (@lem5136753 A P h1)). Qed.
Lemma lem5136756 {A : Type'} (P : type686 A) (h1 : term29 A P) : term29 A P.
Proof. exact (h1). Qed.
Lemma lem5136757 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem5136755 A P h1 (@lem5136756 A P h2)). Qed.
Lemma lem5136758 {A : Type'} (P : type686 A) (h1 : term29 A P) : term31 A P.
Proof. exact (fun h0 : term26 A => @lem5136757 A P h0 h1). Qed.
Lemma lem5136759 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem5136760 {A : Type'} (P : type686 A) (h1 : term26 A) (h2 : term29 A P) : term30 A P.
Proof. exact (@lem5136758 A P h2 (@lem5136759 A h1)). Qed.
Lemma lem5136761 {A : Type'} (P : type686 A) (h1 : term26 A) : term28 A P.
Proof. exact (fun h0 : term29 A P => @lem5136760 A P h1 h0). Qed.
Lemma lem5136762 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (fun P : type686 A => @lem5136761 A P h1). Qed.
Lemma lem5136763 {A : Type'} : term32 A.
Proof. exact (fun h0 : term26 A => @lem5136762 A h0). Qed.
Lemma lem5136764 {A : Type'} : term26 A.
Proof. exact (@lem5136763 A (@lem3558722 A)). Qed.
Lemma lem5136765 {A : Type'} (P : type686 A) : term27 A P.
Proof. exact (@lem5136764 A P). Qed.
Lemma lem5136766 {A : Type'} (P : type686 A) : (term27 A P) = (term28 A P).
Proof. exact (eq_refl (term27 A P)). Qed.
Lemma lem5136773 (p : Prop) (q : Prop) (r : Prop) : (term33 p q r) = (term34 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5136774 (s : real -> Prop) : (term35 s) = (term36 s).
Proof. exact (@lem5136773 (@FINITE real s) (term37 s) (term38 s)). Qed.
Lemma lem5136793 : term39 = term40.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136774 s)). Qed.
Lemma lem5136794 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136795 : term41 = term42.
Proof. exact (MK_COMB (@lem5136794) (@lem5136793)). Qed.
Lemma lem5136800 : term42 = term41.
Proof. exact (SYM (@lem5136795)). Qed.
Lemma lem5136802 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (EQ_MP (@lem5136766 A P) (@lem5136765 A P)). Qed.
Lemma lem5136803 (P : type1022) : term43 P.
Proof. exact (@lem5136802 real P). Qed.
Lemma lem5136804 : term44.
Proof. exact (@lem5136803 term45). Qed.
Lemma lem5136805 : term46 = term47.
Proof. exact (eq_refl term46). Qed.
Lemma lem5136806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136807 : term48 = term49.
Proof. exact (MK_COMB (@lem5136806) (@lem5136805)). Qed.
Lemma lem5136808 (s : real -> Prop) : (term50 s) = (term51 s).
Proof. exact (eq_refl (term50 s)). Qed.
Lemma lem5136809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136810 (s : real -> Prop) : (term52 s) = (term53 s).
Proof. exact (MK_COMB (@lem5136809) (@lem5136808 s)). Qed.
Lemma lem5136811 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5136812 (x : real) (s : real -> Prop) : (term55 x s) = (term56 x s).
Proof. exact (MK_COMB (@lem5136810 s) (@lem5136811 x s)). Qed.
Lemma lem5136813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136814 (x : real) (s : real -> Prop) : (term57 x s) = (term58 x s).
Proof. exact (MK_COMB (@lem5136813) (@lem5136812 x s)). Qed.
Lemma lem5136815 (x : real) (s : real -> Prop) : (term59 x s) = (term60 x s).
Proof. exact (eq_refl (term59 x s)). Qed.
Lemma lem5136816 (x : real) (s : real -> Prop) : (term61 x s) = (term62 x s).
Proof. exact (MK_COMB (@lem5136814 x s) (@lem5136815 x s)). Qed.
Lemma lem5136817 (x : real) : (term63 x) = (term64 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136816 x s)). Qed.
Lemma lem5136818 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136819 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem5136818) (@lem5136817 x)). Qed.
Lemma lem5136820 : term67 = term68.
Proof. exact (fun_ext (fun x : real => @lem5136819 x)). Qed.
Lemma lem5136821 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136822 : term69 = term70.
Proof. exact (MK_COMB (@lem5136821) (@lem5136820)). Qed.
Lemma lem5136823 : term71 = term72.
Proof. exact (MK_COMB (@lem5136807) (@lem5136822)). Qed.
Lemma lem5136824 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136825 : term73 = term74.
Proof. exact (MK_COMB (@lem5136824) (@lem5136823)). Qed.
Lemma lem5136826 (s : real -> Prop) : (term50 s) = (term51 s).
Proof. exact (eq_refl (term50 s)). Qed.
Lemma lem5136827 (s : real -> Prop) : (term75 s) = (term75 s).
Proof. exact (eq_refl (term75 s)). Qed.
Lemma lem5136828 (s : real -> Prop) : (term76 s) = (term36 s).
Proof. exact (MK_COMB (@lem5136827 s) (@lem5136826 s)). Qed.
Lemma lem5136829 : term77 = term40.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136828 s)). Qed.
Lemma lem5136830 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136831 : term78 = term42.
Proof. exact (MK_COMB (@lem5136830) (@lem5136829)). Qed.
Lemma lem5136832 : term44 = term79.
Proof. exact (MK_COMB (@lem5136825) (@lem5136831)). Qed.
Lemma lem5136833 : term79.
Proof. exact (EQ_MP (@lem5136832) (@lem5136804)). Qed.
Lemma lem5136839 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5136840 (x : real -> Prop) : (x = x) = True.
Proof. exact (@lem5136839 (real -> Prop) x). Qed.
Lemma lem5136841 : ((@EMPTY real) = (@EMPTY real)) = True.
Proof. exact (@lem5136840 (@EMPTY real)). Qed.
Lemma lem5136842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5136843 : term80 = (~ True).
Proof. exact (MK_COMB (@lem5136842) (@lem5136841)). Qed.
Lemma lem5136845 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5136846 : term80 = False.
Proof. exact (TRANS (@lem5136843) (@lem5136845)). Qed.
Lemma lem5136847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136848 : term81 = (imp False).
Proof. exact (MK_COMB (@lem5136847) (@lem5136846)). Qed.
Lemma lem5136861 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem5136862 : term47 = term83.
Proof. exact (MK_COMB (@lem5136848) (@lem5136861)). Qed.
Lemma lem5136864 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5136865 : term83 = True.
Proof. exact (@lem5136864 term82). Qed.
Lemma lem5136866 : term47 = True.
Proof. exact (TRANS (@lem5136862) (@lem5136865)). Qed.
Lemma lem5136867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136868 : term49 = (and True).
Proof. exact (MK_COMB (@lem5136867) (@lem5136866)). Qed.
Lemma lem5136902 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5136739 A x s (@lem5136738 A x s)). Qed.
Lemma lem5136903 (x : real) (s : real -> Prop) : ((@INSERT real x s) = (@EMPTY real)) = False.
Proof. exact (@lem5136902 real x s). Qed.
Lemma lem5136904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5136905 (x : real) (s : real -> Prop) : (term84 x s) = (~ False).
Proof. exact (MK_COMB (@lem5136904) (@lem5136903 x s)). Qed.
Lemma lem5136907 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5136908 (x : real) (s : real -> Prop) : (term84 x s) = True.
Proof. exact (TRANS (@lem5136905 x s) (@lem5136907)). Qed.
Lemma lem5136909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136910 (x : real) (s : real -> Prop) : (term85 x s) = (imp True).
Proof. exact (MK_COMB (@lem5136909) (@lem5136908 x s)). Qed.
Lemma lem5136918 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem5136731 A y x s) (@lem5136730 A y x s)). Qed.
Lemma lem5136919 (y : real) (x : real) (s : real -> Prop) : (term86 x y s) = (term87 y x s).
Proof. exact (@lem5136918 real y x s). Qed.
Lemma lem5136920 (x : real) (b : real) (s : real -> Prop) : (term86 b x s) = (term87 x b s).
Proof. exact (@lem5136919 x b s). Qed.
Lemma lem5136925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5136926 (x : real) (b : real) (s : real -> Prop) : (term88 b x s) = (term89 x b s).
Proof. exact (MK_COMB (@lem5136925) (@lem5136920 x b s)). Qed.
Lemma lem5136934 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem5136731 A y x s) (@lem5136730 A y x s)). Qed.
Lemma lem5136935 (y : real) (x : real) (s : real -> Prop) : (term86 x y s) = (term87 y x s).
Proof. exact (@lem5136934 real y x s). Qed.
Lemma lem5136936 (x : real) (x' : real) (s : real -> Prop) : (term86 x' x s) = (term87 x x' s).
Proof. exact (@lem5136935 x x' s). Qed.
Lemma lem5136941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5136942 (x : real) (x' : real) (s : real -> Prop) : (term90 x' x s) = (term91 x x' s).
Proof. exact (MK_COMB (@lem5136941) (@lem5136936 x x' s)). Qed.
Lemma lem5136943 (x' : real) (b : real) : (real_le x' b) = (real_le x' b).
Proof. exact (eq_refl (real_le x' b)). Qed.
Lemma lem5136944 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term92 x s x' b) = (term93 x s x' b).
Proof. exact (MK_COMB (@lem5136942 x x' s) (@lem5136943 x' b)). Qed.
Lemma lem5136947 (x : real) (s : real -> Prop) (b : real) : (term94 x s b) = (term95 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5136944 x s x' b)). Qed.
Lemma lem5136948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5136949 (x : real) (s : real -> Prop) (b : real) : (term96 x s b) = (term97 x s b).
Proof. exact (MK_COMB (@lem5136948) (@lem5136947 x s b)). Qed.
Lemma lem5136954 (x : real) (s : real -> Prop) (b : real) : (term98 x s b) = (term99 x s b).
Proof. exact (MK_COMB (@lem5136926 x b s) (@lem5136949 x s b)). Qed.
Lemma lem5136957 (x : real) (s : real -> Prop) : (term100 x s) = (term101 x s).
Proof. exact (fun_ext (fun b : real => @lem5136954 x s b)). Qed.
Lemma lem5136958 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5136959 (x : real) (s : real -> Prop) : (term102 x s) = (term103 x s).
Proof. exact (MK_COMB (@lem5136958) (@lem5136957 x s)). Qed.
Lemma lem5136964 (x : real) (s : real -> Prop) : (term60 x s) = (term104 x s).
Proof. exact (MK_COMB (@lem5136910 x s) (@lem5136959 x s)). Qed.
Lemma lem5136966 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5136967 (x : real) (s : real -> Prop) : (term104 x s) = (term103 x s).
Proof. exact (@lem5136966 (term103 x s)). Qed.
Lemma lem5136988 (x : real) (s : real -> Prop) : (term60 x s) = (term103 x s).
Proof. exact (TRANS (@lem5136964 x s) (@lem5136967 x s)). Qed.
Lemma lem5136989 (x : real) (s : real -> Prop) : (term58 x s) = (term58 x s).
Proof. exact (eq_refl (term58 x s)). Qed.
Lemma lem5136990 (x : real) (s : real -> Prop) : (term62 x s) = (term105 x s).
Proof. exact (MK_COMB (@lem5136989 x s) (@lem5136988 x s)). Qed.
Lemma lem5136993 (x : real) : (term64 x) = (term106 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5136990 x s)). Qed.
Lemma lem5136994 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5136995 (x : real) : (term66 x) = (term107 x).
Proof. exact (MK_COMB (@lem5136994) (@lem5136993 x)). Qed.
Lemma lem5137000 : term68 = term108.
Proof. exact (fun_ext (fun x : real => @lem5136995 x)). Qed.
Lemma lem5137001 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137002 : term70 = term109.
Proof. exact (MK_COMB (@lem5137001) (@lem5137000)). Qed.
Lemma lem5137007 : term72 = term110.
Proof. exact (MK_COMB (@lem5136868) (@lem5137002)). Qed.
Lemma lem5137009 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5137010 : term110 = term109.
Proof. exact (@lem5137009 term109). Qed.
Lemma lem5137061 : term72 = term109.
Proof. exact (TRANS (@lem5137007) (@lem5137010)). Qed.
Lemma lem5137062 : term109 = term72.
Proof. exact (SYM (@lem5137061)). Qed.
Lemma lem5137078 {A : Type'} (s : A -> Prop) : (term8 A s) = (term7 A s).
Proof. exact (EQ_MP (@lem5136722 A s) (@lem5136721 A s)). Qed.
Lemma lem5137079 (s : real -> Prop) : (term37 s) = (term111 s).
Proof. exact (@lem5137078 real s). Qed.
Lemma lem5137084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137085 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (MK_COMB (@lem5137084) (@lem5137079 s)). Qed.
Lemma lem5137098 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5137099 (s : real -> Prop) : (term51 s) = (term114 s).
Proof. exact (MK_COMB (@lem5137085 s) (@lem5137098 s)). Qed.
Lemma lem5137102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137103 (s : real -> Prop) : (term53 s) = (term115 s).
Proof. exact (MK_COMB (@lem5137102) (@lem5137099 s)). Qed.
Lemma lem5137106 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5137107 (x : real) (s : real -> Prop) : (term56 x s) = (term116 x s).
Proof. exact (MK_COMB (@lem5137103 s) (@lem5137106 x s)). Qed.
Lemma lem5137110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137111 (x : real) (s : real -> Prop) : (term58 x s) = (term117 x s).
Proof. exact (MK_COMB (@lem5137110) (@lem5137107 x s)). Qed.
Lemma lem5137132 (x : real) (s : real -> Prop) : (term103 x s) = (term103 x s).
Proof. exact (eq_refl (term103 x s)). Qed.
Lemma lem5137133 (x : real) (s : real -> Prop) : (term105 x s) = (term118 x s).
Proof. exact (MK_COMB (@lem5137111 x s) (@lem5137132 x s)). Qed.
Lemma lem5137136 (x : real) : (term106 x) = (term119 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5137133 x s)). Qed.
Lemma lem5137137 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5137138 (x : real) : (term107 x) = (term120 x).
Proof. exact (MK_COMB (@lem5137137) (@lem5137136 x)). Qed.
Lemma lem5137143 : term108 = term121.
Proof. exact (fun_ext (fun x : real => @lem5137138 x)). Qed.
Lemma lem5137144 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137145 : term109 = term122.
Proof. exact (MK_COMB (@lem5137144) (@lem5137143)). Qed.
Lemma lem5137150 : term122 = term109.
Proof. exact (SYM (@lem5137145)). Qed.
Lemma lem5137152 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5137153 : term122 = term124.
Proof. exact (@lem5137152 term122). Qed.
Lemma lem5137154 : term124 = term122.
Proof. exact (SYM (@lem5137153)). Qed.
Lemma lem5137155 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem5137158 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem5137159 : term127.
Proof. exact (fun h0 : term126 => @lem5137158 h0). Qed.
Lemma lem5137160 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5137161 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem5137162 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem5137160 h2 (@lem5137161 h1)). Qed.
Lemma lem5137163 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem5137162 h1 h0). Qed.
Lemma lem5137164 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem5137165 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem5137163 h1 (@lem5137164 h2)). Qed.
Lemma lem5137166 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem5137165 h0 h1). Qed.
Lemma lem5137167 : term129.
Proof. exact (fun h0 : term127 => @lem5137166 h0). Qed.
Lemma lem5137170 : term127.
Proof. exact (@lem5137167 (@lem5137159)). Qed.
Lemma lem5137328 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5137329 : term130 = term131.
Proof. exact (@lem5137328 term132). Qed.
Lemma lem5137384 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5137385 : term134 = term135.
Proof. exact (MK_COMB (@lem5137384) (@lem5137329)). Qed.
Lemma lem5137388 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem5137395 : term126 = term137.
Proof. exact (MK_COMB (@lem5137388) (@lem5137385)). Qed.
Lemma lem5137400 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5137401 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5137400 y x)). Qed.
Lemma lem5137402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137403 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5137402) (@lem5137401 x)). Qed.
Lemma lem5137404 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5137403 x)). Qed.
Lemma lem5137405 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137406 : term132 = term132.
Proof. exact (MK_COMB (@lem5137405) (@lem5137404)). Qed.
Lemma lem5137407 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137408 : term131 = term131.
Proof. exact (MK_COMB (@lem5137407) (@lem5137406)). Qed.
Lemma lem5137417 (y : real) (x : real) (z : real) : (term142 y x z) = (term142 y x z).
Proof. exact (eq_refl (term142 y x z)). Qed.
Lemma lem5137418 (y : real) (x : real) : (term143 y x) = (term143 y x).
Proof. exact (fun_ext (fun z : real => @lem5137417 y x z)). Qed.
Lemma lem5137419 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137420 (y : real) (x : real) : (term144 y x) = (term144 y x).
Proof. exact (MK_COMB (@lem5137419) (@lem5137418 y x)). Qed.
Lemma lem5137421 (x : real) : (term145 x) = (term145 x).
Proof. exact (fun_ext (fun y : real => @lem5137420 y x)). Qed.
Lemma lem5137422 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137423 (x : real) : (term146 x) = (term146 x).
Proof. exact (MK_COMB (@lem5137422) (@lem5137421 x)). Qed.
Lemma lem5137424 : term147 = term147.
Proof. exact (fun_ext (fun x : real => @lem5137423 x)). Qed.
Lemma lem5137425 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137426 : term148 = term148.
Proof. exact (MK_COMB (@lem5137425) (@lem5137424)). Qed.
Lemma lem5137427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137428 : term133 = term133.
Proof. exact (MK_COMB (@lem5137427) (@lem5137426)). Qed.
Lemma lem5137429 : term135 = term135.
Proof. exact (MK_COMB (@lem5137428) (@lem5137408)). Qed.
Lemma lem5137438 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term93 x s x' b) = (term93 x s x' b).
Proof. exact (eq_refl (term93 x s x' b)). Qed.
Lemma lem5137439 (x : real) (s : real -> Prop) (b : real) : (term95 x s b) = (term95 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5137438 x s x' b)). Qed.
Lemma lem5137440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137441 (x : real) (s : real -> Prop) (b : real) : (term97 x s b) = (term97 x s b).
Proof. exact (MK_COMB (@lem5137440) (@lem5137439 x s b)). Qed.
Lemma lem5137448 (x : real) (b : real) (s : real -> Prop) : (term89 x b s) = (term89 x b s).
Proof. exact (eq_refl (term89 x b s)). Qed.
Lemma lem5137449 (x : real) (s : real -> Prop) (b : real) : (term99 x s b) = (term99 x s b).
Proof. exact (MK_COMB (@lem5137448 x b s) (@lem5137441 x s b)). Qed.
Lemma lem5137450 (x : real) (s : real -> Prop) : (term101 x s) = (term101 x s).
Proof. exact (fun_ext (fun b : real => @lem5137449 x s b)). Qed.
Lemma lem5137451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137452 (x : real) (s : real -> Prop) : (term103 x s) = (term103 x s).
Proof. exact (MK_COMB (@lem5137451) (@lem5137450 x s)). Qed.
Lemma lem5137459 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5137464 (s : real -> Prop) (x : real) (b : real) : (term149 s x b) = (term149 s x b).
Proof. exact (eq_refl (term149 s x b)). Qed.
Lemma lem5137465 (s : real -> Prop) (b : real) : (term150 s b) = (term150 s b).
Proof. exact (fun_ext (fun x : real => @lem5137464 s x b)). Qed.
Lemma lem5137466 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137467 (s : real -> Prop) (b : real) : (term151 s b) = (term151 s b).
Proof. exact (MK_COMB (@lem5137466) (@lem5137465 s b)). Qed.
Lemma lem5137470 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5137471 (s : real -> Prop) (b : real) : (term153 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5137470 b s) (@lem5137467 s b)). Qed.
Lemma lem5137472 (s : real -> Prop) : (term154 s) = (term154 s).
Proof. exact (fun_ext (fun b : real => @lem5137471 s b)). Qed.
Lemma lem5137473 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137474 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5137473) (@lem5137472 s)). Qed.
Lemma lem5137475 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5137476 (s : real -> Prop) : (term155 s) = (term155 s).
Proof. exact (fun_ext (fun x : real => @lem5137475 x s)). Qed.
Lemma lem5137477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137478 (s : real -> Prop) : (term111 s) = (term111 s).
Proof. exact (MK_COMB (@lem5137477) (@lem5137476 s)). Qed.
Lemma lem5137479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137480 (s : real -> Prop) : (term113 s) = (term113 s).
Proof. exact (MK_COMB (@lem5137479) (@lem5137478 s)). Qed.
Lemma lem5137481 (s : real -> Prop) : (term114 s) = (term114 s).
Proof. exact (MK_COMB (@lem5137480 s) (@lem5137474 s)). Qed.
Lemma lem5137482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137483 (s : real -> Prop) : (term115 s) = (term115 s).
Proof. exact (MK_COMB (@lem5137482) (@lem5137481 s)). Qed.
Lemma lem5137484 (x : real) (s : real -> Prop) : (term116 x s) = (term116 x s).
Proof. exact (MK_COMB (@lem5137483 s) (@lem5137459 x s)). Qed.
Lemma lem5137485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137486 (x : real) (s : real -> Prop) : (term117 x s) = (term117 x s).
Proof. exact (MK_COMB (@lem5137485) (@lem5137484 x s)). Qed.
Lemma lem5137487 (x : real) (s : real -> Prop) : (term118 x s) = (term118 x s).
Proof. exact (MK_COMB (@lem5137486 x s) (@lem5137452 x s)). Qed.
Lemma lem5137488 (x : real) : (term119 x) = (term119 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5137487 x s)). Qed.
Lemma lem5137489 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5137490 (x : real) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem5137489) (@lem5137488 x)). Qed.
Lemma lem5137491 : term121 = term121.
Proof. exact (fun_ext (fun x : real => @lem5137490 x)). Qed.
Lemma lem5137492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137493 : term122 = term122.
Proof. exact (MK_COMB (@lem5137492) (@lem5137491)). Qed.
Lemma lem5137494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137495 : term125 = term125.
Proof. exact (MK_COMB (@lem5137494) (@lem5137493)). Qed.
Lemma lem5137496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5137497 : term136 = term136.
Proof. exact (MK_COMB (@lem5137496) (@lem5137495)). Qed.
Lemma lem5137498 : term137 = term137.
Proof. exact (MK_COMB (@lem5137497) (@lem5137429)). Qed.
Lemma lem5137603 : term126 = term137.
Proof. exact (TRANS (@lem5137395) (@lem5137498)). Qed.
Lemma lem5137604 : term137 = term126.
Proof. exact (SYM (@lem5137603)). Qed.
Lemma lem5137605 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem5137606 (h1 : term148) : term148.
Proof. exact (h1). Qed.
Lemma lem5137607 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5137609 (P : real -> Prop) : (term156 P) = (term157 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5137610 (s : real -> Prop) : (term158 s) = (term159 s).
Proof. exact (@lem5137609 (term155 s)). Qed.
Lemma lem5137611 (x : real) (s : real -> Prop) : (term160 s x) = (@IN real x s).
Proof. exact (eq_refl (term160 s x)). Qed.
Lemma lem5137612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137614 (x : real) (s : real -> Prop) : (term161 s x) = (term162 x s).
Proof. exact (MK_COMB (@lem5137612) (@lem5137611 x s)). Qed.
Lemma lem5137615 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5137614 x s)). Qed.
Lemma lem5137616 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137617 (s : real -> Prop) : (term159 s) = (term165 s).
Proof. exact (MK_COMB (@lem5137616) (@lem5137615 s)). Qed.
Lemma lem5137618 (s : real -> Prop) : (term158 s) = (term165 s).
Proof. exact (TRANS (@lem5137610 s) (@lem5137617 s)). Qed.
Lemma lem5137626 (s : real -> Prop) (x : real) (b : real) : (term149 s x b) = (term166 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5137627 (s : real -> Prop) (b : real) : (term150 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5137626 s x b)). Qed.
Lemma lem5137628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137629 (s : real -> Prop) (b : real) : (term151 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5137628) (@lem5137627 s b)). Qed.
Lemma lem5137631 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5137632 (s : real -> Prop) (b : real) : (term153 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5137631 b s) (@lem5137629 s b)). Qed.
Lemma lem5137633 (s : real -> Prop) : (term154 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5137632 s b)). Qed.
Lemma lem5137634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137635 (s : real -> Prop) : (term38 s) = (term171 s).
Proof. exact (MK_COMB (@lem5137634) (@lem5137633 s)). Qed.
Lemma lem5137636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5137637 (s : real -> Prop) : (term172 s) = (term173 s).
Proof. exact (MK_COMB (@lem5137636) (@lem5137618 s)). Qed.
Lemma lem5137638 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (MK_COMB (@lem5137637 s) (@lem5137635 s)). Qed.
Lemma lem5137639 (s : real -> Prop) : (term114 s) = (term174 s).
Proof. exact (@lem17265 (term111 s) (term38 s)). Qed.
Lemma lem5137640 (s : real -> Prop) : (term114 s) = (term175 s).
Proof. exact (TRANS (@lem5137639 s) (@lem5137638 s)). Qed.
Lemma lem5137645 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5137646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137647 (s : real -> Prop) : (term115 s) = (term176 s).
Proof. exact (MK_COMB (@lem5137646) (@lem5137640 s)). Qed.
Lemma lem5137648 (x : real) (s : real -> Prop) : (term116 x s) = (term177 x s).
Proof. exact (MK_COMB (@lem5137647 s) (@lem5137645 x s)). Qed.
Lemma lem5137655 (x : real) (b : real) (s : real -> Prop) : (term178 x b s) = (term179 x b s).
Proof. exact (@lem17160 (b = x) (@IN real b s)). Qed.
Lemma lem5137666 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term180 x s x' b) = (term181 x s x' b).
Proof. exact (@lem17362 (term87 x x' s) (real_le x' b)). Qed.
Lemma lem5137667 (P : real -> Prop) : (term182 P) = (term183 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5137668 (x : real) (s : real -> Prop) (b : real) : (term184 x s b) = (term185 x s b).
Proof. exact (@lem5137667 (term95 x s b)). Qed.
Lemma lem5137669 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term186 x s b x') = (term93 x s x' b).
Proof. exact (eq_refl (term186 x s b x')). Qed.
Lemma lem5137670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137671 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term187 x s b x') = (term180 x s x' b).
Proof. exact (MK_COMB (@lem5137670) (@lem5137669 x s x' b)). Qed.
Lemma lem5137672 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term187 x s b x') = (term181 x s x' b).
Proof. exact (TRANS (@lem5137671 x s x' b) (@lem5137666 x s x' b)). Qed.
Lemma lem5137673 (x : real) (s : real -> Prop) (b : real) : (term188 x s b) = (term189 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5137672 x s x' b)). Qed.
Lemma lem5137674 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137675 (x : real) (s : real -> Prop) (b : real) : (term185 x s b) = (term190 x s b).
Proof. exact (MK_COMB (@lem5137674) (@lem5137673 x s b)). Qed.
Lemma lem5137676 (x : real) (s : real -> Prop) (b : real) : (term184 x s b) = (term190 x s b).
Proof. exact (TRANS (@lem5137668 x s b) (@lem5137675 x s b)). Qed.
Lemma lem5137677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5137678 (x : real) (b : real) (s : real -> Prop) : (term191 x b s) = (term192 x b s).
Proof. exact (MK_COMB (@lem5137677) (@lem5137655 x b s)). Qed.
Lemma lem5137679 (x : real) (s : real -> Prop) (b : real) : (term193 x s b) = (term194 x s b).
Proof. exact (MK_COMB (@lem5137678 x b s) (@lem5137676 x s b)). Qed.
Lemma lem5137680 (x : real) (s : real -> Prop) (b : real) : (term195 x s b) = (term193 x s b).
Proof. exact (@lem17045 (term87 x b s) (term97 x s b)). Qed.
Lemma lem5137681 (x : real) (s : real -> Prop) (b : real) : (term195 x s b) = (term194 x s b).
Proof. exact (TRANS (@lem5137680 x s b) (@lem5137679 x s b)). Qed.
Lemma lem5137682 (P : real -> Prop) : (term156 P) = (term157 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5137683 (x : real) (s : real -> Prop) : (term196 x s) = (term197 x s).
Proof. exact (@lem5137682 (term101 x s)). Qed.
Lemma lem5137684 (x : real) (s : real -> Prop) (b : real) : (term198 x s b) = (term99 x s b).
Proof. exact (eq_refl (term198 x s b)). Qed.
Lemma lem5137685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137686 (x : real) (s : real -> Prop) (b : real) : (term199 x s b) = (term195 x s b).
Proof. exact (MK_COMB (@lem5137685) (@lem5137684 x s b)). Qed.
Lemma lem5137687 (x : real) (s : real -> Prop) (b : real) : (term199 x s b) = (term194 x s b).
Proof. exact (TRANS (@lem5137686 x s b) (@lem5137681 x s b)). Qed.
Lemma lem5137688 (x : real) (s : real -> Prop) : (term200 x s) = (term201 x s).
Proof. exact (fun_ext (fun b : real => @lem5137687 x s b)). Qed.
Lemma lem5137689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5137690 (x : real) (s : real -> Prop) : (term197 x s) = (term202 x s).
Proof. exact (MK_COMB (@lem5137689) (@lem5137688 x s)). Qed.
Lemma lem5137691 (x : real) (s : real -> Prop) : (term196 x s) = (term202 x s).
Proof. exact (TRANS (@lem5137683 x s) (@lem5137690 x s)). Qed.
Lemma lem5137692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137693 (x : real) (s : real -> Prop) : (term203 x s) = (term204 x s).
Proof. exact (MK_COMB (@lem5137692) (@lem5137648 x s)). Qed.
Lemma lem5137694 (x : real) (s : real -> Prop) : (term205 x s) = (term206 x s).
Proof. exact (MK_COMB (@lem5137693 x s) (@lem5137691 x s)). Qed.
Lemma lem5137695 (x : real) (s : real -> Prop) : (term207 x s) = (term205 x s).
Proof. exact (@lem17362 (term116 x s) (term103 x s)). Qed.
Lemma lem5137696 (x : real) (s : real -> Prop) : (term207 x s) = (term206 x s).
Proof. exact (TRANS (@lem5137695 x s) (@lem5137694 x s)). Qed.
Lemma lem5137697 (P : type1022) : (term208 P) = (term209 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5137698 (x : real) : (term210 x) = (term211 x).
Proof. exact (@lem5137697 (term119 x)). Qed.
Lemma lem5137699 (x : real) (s : real -> Prop) : (term212 x s) = (term118 x s).
Proof. exact (eq_refl (term212 x s)). Qed.
Lemma lem5137700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137701 (x : real) (s : real -> Prop) : (term213 x s) = (term207 x s).
Proof. exact (MK_COMB (@lem5137700) (@lem5137699 x s)). Qed.
Lemma lem5137702 (x : real) (s : real -> Prop) : (term213 x s) = (term206 x s).
Proof. exact (TRANS (@lem5137701 x s) (@lem5137696 x s)). Qed.
Lemma lem5137703 (x : real) : (term214 x) = (term215 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5137702 x s)). Qed.
Lemma lem5137704 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5137705 (x : real) : (term211 x) = (term216 x).
Proof. exact (MK_COMB (@lem5137704) (@lem5137703 x)). Qed.
Lemma lem5137706 (x : real) : (term210 x) = (term216 x).
Proof. exact (TRANS (@lem5137698 x) (@lem5137705 x)). Qed.
Lemma lem5137707 (P : real -> Prop) : (term182 P) = (term183 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5137708 : term125 = term217.
Proof. exact (@lem5137707 term121). Qed.
Lemma lem5137709 (x : real) : (term218 x) = (term120 x).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem5137710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5137711 (x : real) : (term219 x) = (term210 x).
Proof. exact (MK_COMB (@lem5137710) (@lem5137709 x)). Qed.
Lemma lem5137712 (x : real) : (term219 x) = (term216 x).
Proof. exact (TRANS (@lem5137711 x) (@lem5137706 x)). Qed.
Lemma lem5137713 : term220 = term221.
Proof. exact (fun_ext (fun x : real => @lem5137712 x)). Qed.
Lemma lem5137714 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137715 : term217 = term222.
Proof. exact (MK_COMB (@lem5137714) (@lem5137713)). Qed.
Lemma lem5137716 : term125 = term222.
Proof. exact (TRANS (@lem5137708) (@lem5137715)). Qed.
Lemma lem5137967 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5137968 (P : Prop) (Q : real -> Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem5137967 real P Q). Qed.
Lemma lem5137969 (s : real -> Prop) : (term227 s) = (term228 s).
Proof. exact (@lem5137968 (term165 s) (term170 s)). Qed.
Lemma lem5137970 (s : real -> Prop) (b : real) : (term229 s b) = (term169 s b).
Proof. exact (eq_refl (term229 s b)). Qed.
Lemma lem5137971 (s : real -> Prop) : (term230 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5137970 s b)). Qed.
Lemma lem5137972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137973 (s : real -> Prop) : (term231 s) = (term171 s).
Proof. exact (MK_COMB (@lem5137972) (@lem5137971 s)). Qed.
Lemma lem5137974 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (eq_refl (term173 s)). Qed.
Lemma lem5137975 (s : real -> Prop) : (term227 s) = (term175 s).
Proof. exact (MK_COMB (@lem5137974 s) (@lem5137973 s)). Qed.
Lemma lem5137976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5137977 (s : real -> Prop) : (term232 s) = (term233 s).
Proof. exact (MK_COMB (@lem5137976) (@lem5137975 s)). Qed.
Lemma lem5137978 (s : real -> Prop) (b : real) : (term229 s b) = (term169 s b).
Proof. exact (eq_refl (term229 s b)). Qed.
Lemma lem5137979 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (eq_refl (term173 s)). Qed.
Lemma lem5137980 (s : real -> Prop) (b : real) : (term234 s b) = (term235 s b).
Proof. exact (MK_COMB (@lem5137979 s) (@lem5137978 s b)). Qed.
Lemma lem5137981 (s : real -> Prop) : (term236 s) = (term237 s).
Proof. exact (fun_ext (fun b : real => @lem5137980 s b)). Qed.
Lemma lem5137982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137983 (s : real -> Prop) : (term228 s) = (term238 s).
Proof. exact (MK_COMB (@lem5137982) (@lem5137981 s)). Qed.
Lemma lem5137984 (s : real -> Prop) : ((term227 s) = (term228 s)) = ((term175 s) = (term238 s)).
Proof. exact (MK_COMB (@lem5137977 s) (@lem5137983 s)). Qed.
Lemma lem5137985 (s : real -> Prop) : (term175 s) = (term238 s).
Proof. exact (EQ_MP (@lem5137984 s) (@lem5137969 s)). Qed.
Lemma lem5137986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137987 (s : real -> Prop) : (term176 s) = (term239 s).
Proof. exact (MK_COMB (@lem5137986) (@lem5137985 s)). Qed.
Lemma lem5137988 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5137989 (x : real) (s : real -> Prop) : (term177 x s) = (term240 x s).
Proof. exact (MK_COMB (@lem5137987 s) (@lem5137988 x s)). Qed.
Lemma lem5137991 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5137992 (P : real -> Prop) (Q : Prop) : (term243 P Q) = (term244 P Q).
Proof. exact (@lem5137991 real P Q). Qed.
Lemma lem5137993 (x : real) (s : real -> Prop) : (term245 x s) = (term246 x s).
Proof. exact (@lem5137992 (term237 s) (term54 x s)). Qed.
Lemma lem5137994 (s : real -> Prop) (b : real) : (term247 s b) = (term235 s b).
Proof. exact (eq_refl (term247 s b)). Qed.
Lemma lem5137995 (s : real -> Prop) : (term248 s) = (term237 s).
Proof. exact (fun_ext (fun b : real => @lem5137994 s b)). Qed.
Lemma lem5137996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5137997 (s : real -> Prop) : (term249 s) = (term238 s).
Proof. exact (MK_COMB (@lem5137996) (@lem5137995 s)). Qed.
Lemma lem5137998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5137999 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5137998) (@lem5137997 s)). Qed.
Lemma lem5138000 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5138001 (x : real) (s : real -> Prop) : (term245 x s) = (term240 x s).
Proof. exact (MK_COMB (@lem5137999 s) (@lem5138000 x s)). Qed.
Lemma lem5138002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138003 (x : real) (s : real -> Prop) : (term251 x s) = (term252 x s).
Proof. exact (MK_COMB (@lem5138002) (@lem5138001 x s)). Qed.
Lemma lem5138004 (s : real -> Prop) (b : real) : (term247 s b) = (term235 s b).
Proof. exact (eq_refl (term247 s b)). Qed.
Lemma lem5138005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138006 (s : real -> Prop) (b : real) : (term253 s b) = (term254 s b).
Proof. exact (MK_COMB (@lem5138005) (@lem5138004 s b)). Qed.
Lemma lem5138007 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5138008 (b : real) (x : real) (s : real -> Prop) : (term255 b x s) = (term256 b x s).
Proof. exact (MK_COMB (@lem5138006 s b) (@lem5138007 x s)). Qed.
Lemma lem5138009 (x : real) (s : real -> Prop) : (term257 x s) = (term258 x s).
Proof. exact (fun_ext (fun b : real => @lem5138008 b x s)). Qed.
Lemma lem5138010 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138011 (x : real) (s : real -> Prop) : (term246 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem5138010) (@lem5138009 x s)). Qed.
Lemma lem5138012 (x : real) (s : real -> Prop) : ((term245 x s) = (term246 x s)) = ((term240 x s) = (term259 x s)).
Proof. exact (MK_COMB (@lem5138003 x s) (@lem5138011 x s)). Qed.
Lemma lem5138013 (x : real) (s : real -> Prop) : (term240 x s) = (term259 x s).
Proof. exact (EQ_MP (@lem5138012 x s) (@lem5137993 x s)). Qed.
Lemma lem5138014 (x : real) (s : real -> Prop) : (term177 x s) = (term259 x s).
Proof. exact (TRANS (@lem5137989 x s) (@lem5138013 x s)). Qed.
Lemma lem5138015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138016 (x : real) (s : real -> Prop) : (term204 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5138015) (@lem5138014 x s)). Qed.
Lemma lem5138018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5138019 (P : Prop) (Q : real -> Prop) : (term225 P Q) = (term226 P Q).
Proof. exact (@lem5138018 real P Q). Qed.
Lemma lem5138020 (x : real) (s : real -> Prop) (b : real) : (term261 x s b) = (term262 x s b).
Proof. exact (@lem5138019 (term179 x b s) (term189 x s b)). Qed.
Lemma lem5138021 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term263 x s b x') = (term181 x s x' b).
Proof. exact (eq_refl (term263 x s b x')). Qed.
Lemma lem5138022 (x : real) (s : real -> Prop) (b : real) : (term264 x s b) = (term189 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5138021 x s x' b)). Qed.
Lemma lem5138023 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138024 (x : real) (s : real -> Prop) (b : real) : (term265 x s b) = (term190 x s b).
Proof. exact (MK_COMB (@lem5138023) (@lem5138022 x s b)). Qed.
Lemma lem5138025 (x : real) (b : real) (s : real -> Prop) : (term192 x b s) = (term192 x b s).
Proof. exact (eq_refl (term192 x b s)). Qed.
Lemma lem5138026 (x : real) (s : real -> Prop) (b : real) : (term261 x s b) = (term194 x s b).
Proof. exact (MK_COMB (@lem5138025 x b s) (@lem5138024 x s b)). Qed.
Lemma lem5138027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138028 (x : real) (s : real -> Prop) (b : real) : (term266 x s b) = (term267 x s b).
Proof. exact (MK_COMB (@lem5138027) (@lem5138026 x s b)). Qed.
Lemma lem5138029 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term263 x s b x') = (term181 x s x' b).
Proof. exact (eq_refl (term263 x s b x')). Qed.
Lemma lem5138030 (x : real) (b : real) (s : real -> Prop) : (term192 x b s) = (term192 x b s).
Proof. exact (eq_refl (term192 x b s)). Qed.
Lemma lem5138031 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term268 x s b x') = (term269 x s x' b).
Proof. exact (MK_COMB (@lem5138030 x b s) (@lem5138029 x s x' b)). Qed.
Lemma lem5138032 (x : real) (s : real -> Prop) (b : real) : (term270 x s b) = (term271 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5138031 x s x' b)). Qed.
Lemma lem5138033 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138034 (x : real) (s : real -> Prop) (b : real) : (term262 x s b) = (term272 x s b).
Proof. exact (MK_COMB (@lem5138033) (@lem5138032 x s b)). Qed.
Lemma lem5138035 (x : real) (s : real -> Prop) (b : real) : ((term261 x s b) = (term262 x s b)) = ((term194 x s b) = (term272 x s b)).
Proof. exact (MK_COMB (@lem5138028 x s b) (@lem5138034 x s b)). Qed.
Lemma lem5138036 (x : real) (s : real -> Prop) (b : real) : (term194 x s b) = (term272 x s b).
Proof. exact (EQ_MP (@lem5138035 x s b) (@lem5138020 x s b)). Qed.
Lemma lem5138037 (x : real) (s : real -> Prop) : (term201 x s) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5138036 x s b)). Qed.
Lemma lem5138038 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138039 (x : real) (s : real -> Prop) : (term202 x s) = (term274 x s).
Proof. exact (MK_COMB (@lem5138038) (@lem5138037 x s)). Qed.
Lemma lem5138041 {A B : Type'} (P : type1413 A B) : (term275 A B P) = (term276 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5138042 (P : type1626) : (term277 P) = (term278 P).
Proof. exact (@lem5138041 real real P). Qed.
Lemma lem5138043 (x : real) (s : real -> Prop) : (term279 x s) = (term280 x s).
Proof. exact (@lem5138042 (term281 x s)). Qed.
Lemma lem5138044 (x : real) (s : real -> Prop) (b : real) : (term282 x s b) = (term271 x s b).
Proof. exact (eq_refl (term282 x s b)). Qed.
Lemma lem5138045 (x' : real) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem5138046 (x : real) (s : real -> Prop) (b : real) (x' : real) : (term283 x s b x') = (term284 x s b x').
Proof. exact (MK_COMB (@lem5138044 x s b) (@lem5138045 x')). Qed.
Lemma lem5138047 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term284 x s b x') = (term269 x s x' b).
Proof. exact (eq_refl (term284 x s b x')). Qed.
Lemma lem5138048 (x : real) (s : real -> Prop) (x' : real) (b : real) : (term283 x s b x') = (term269 x s x' b).
Proof. exact (TRANS (@lem5138046 x s b x') (@lem5138047 x s x' b)). Qed.
Lemma lem5138049 (x : real) (s : real -> Prop) (b : real) : (term285 x s b) = (term271 x s b).
Proof. exact (fun_ext (fun x' : real => @lem5138048 x s x' b)). Qed.
Lemma lem5138050 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138051 (x : real) (s : real -> Prop) (b : real) : (term286 x s b) = (term272 x s b).
Proof. exact (MK_COMB (@lem5138050) (@lem5138049 x s b)). Qed.
Lemma lem5138052 (x : real) (s : real -> Prop) : (term287 x s) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5138051 x s b)). Qed.
Lemma lem5138053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138054 (x : real) (s : real -> Prop) : (term279 x s) = (term274 x s).
Proof. exact (MK_COMB (@lem5138053) (@lem5138052 x s)). Qed.
Lemma lem5138055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138056 (x : real) (s : real -> Prop) : (term288 x s) = (term289 x s).
Proof. exact (MK_COMB (@lem5138055) (@lem5138054 x s)). Qed.
Lemma lem5138057 (x : real) (s : real -> Prop) (b : real) : (term282 x s b) = (term271 x s b).
Proof. exact (eq_refl (term282 x s b)). Qed.
Lemma lem5138058 (x' : real -> real) (b : real) : (x' b) = (x' b).
Proof. exact (eq_refl (x' b)). Qed.
Lemma lem5138059 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term290 x s x' b) = (term291 x s x' b).
Proof. exact (MK_COMB (@lem5138057 x s b) (@lem5138058 x' b)). Qed.
Lemma lem5138060 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term291 x s x' b) = (term292 x s x' b).
Proof. exact (eq_refl (term291 x s x' b)). Qed.
Lemma lem5138061 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term290 x s x' b) = (term292 x s x' b).
Proof. exact (TRANS (@lem5138059 x s x' b) (@lem5138060 x s x' b)). Qed.
Lemma lem5138062 (x : real) (s : real -> Prop) (x' : real -> real) : (term293 x s x') = (term294 x s x').
Proof. exact (fun_ext (fun b : real => @lem5138061 x s x' b)). Qed.
Lemma lem5138063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138064 (x : real) (s : real -> Prop) (x' : real -> real) : (term295 x s x') = (term296 x s x').
Proof. exact (MK_COMB (@lem5138063) (@lem5138062 x s x')). Qed.
Lemma lem5138065 (x : real) (s : real -> Prop) : (term297 x s) = (term298 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5138064 x s x')). Qed.
Lemma lem5138066 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5138067 (x : real) (s : real -> Prop) : (term280 x s) = (term299 x s).
Proof. exact (MK_COMB (@lem5138066) (@lem5138065 x s)). Qed.
Lemma lem5138068 (x : real) (s : real -> Prop) : ((term279 x s) = (term280 x s)) = ((term274 x s) = (term299 x s)).
Proof. exact (MK_COMB (@lem5138056 x s) (@lem5138067 x s)). Qed.
Lemma lem5138069 (x : real) (s : real -> Prop) : (term274 x s) = (term299 x s).
Proof. exact (EQ_MP (@lem5138068 x s) (@lem5138043 x s)). Qed.
Lemma lem5138070 (x : real) (s : real -> Prop) : (term202 x s) = (term299 x s).
Proof. exact (TRANS (@lem5138039 x s) (@lem5138069 x s)). Qed.
Lemma lem5138071 (x : real) (s : real -> Prop) : (term206 x s) = (term300 x s).
Proof. exact (MK_COMB (@lem5138016 x s) (@lem5138070 x s)). Qed.
Lemma lem5138073 {A : Type'} (P : A -> Prop) (Q : Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5138074 (P : real -> Prop) (Q : Prop) : (term243 P Q) = (term244 P Q).
Proof. exact (@lem5138073 real P Q). Qed.
Lemma lem5138075 (x : real) (s : real -> Prop) : (term301 x s) = (term302 x s).
Proof. exact (@lem5138074 (term258 x s) (term299 x s)). Qed.
Lemma lem5138076 (b : real) (x : real) (s : real -> Prop) : (term303 x s b) = (term256 b x s).
Proof. exact (eq_refl (term303 x s b)). Qed.
Lemma lem5138077 (x : real) (s : real -> Prop) : (term304 x s) = (term258 x s).
Proof. exact (fun_ext (fun b : real => @lem5138076 b x s)). Qed.
Lemma lem5138078 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138079 (x : real) (s : real -> Prop) : (term305 x s) = (term259 x s).
Proof. exact (MK_COMB (@lem5138078) (@lem5138077 x s)). Qed.
Lemma lem5138080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138081 (x : real) (s : real -> Prop) : (term306 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5138080) (@lem5138079 x s)). Qed.
Lemma lem5138082 (x : real) (s : real -> Prop) : (term299 x s) = (term299 x s).
Proof. exact (eq_refl (term299 x s)). Qed.
Lemma lem5138083 (x : real) (s : real -> Prop) : (term301 x s) = (term300 x s).
Proof. exact (MK_COMB (@lem5138081 x s) (@lem5138082 x s)). Qed.
Lemma lem5138084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138085 (x : real) (s : real -> Prop) : (term307 x s) = (term308 x s).
Proof. exact (MK_COMB (@lem5138084) (@lem5138083 x s)). Qed.
Lemma lem5138086 (b : real) (x : real) (s : real -> Prop) : (term303 x s b) = (term256 b x s).
Proof. exact (eq_refl (term303 x s b)). Qed.
Lemma lem5138087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138088 (b : real) (x : real) (s : real -> Prop) : (term309 x s b) = (term310 b x s).
Proof. exact (MK_COMB (@lem5138087) (@lem5138086 b x s)). Qed.
Lemma lem5138089 (x : real) (s : real -> Prop) : (term299 x s) = (term299 x s).
Proof. exact (eq_refl (term299 x s)). Qed.
Lemma lem5138090 (b : real) (x : real) (s : real -> Prop) : (term311 b x s) = (term312 b x s).
Proof. exact (MK_COMB (@lem5138088 b x s) (@lem5138089 x s)). Qed.
Lemma lem5138091 (x : real) (s : real -> Prop) : (term313 x s) = (term314 x s).
Proof. exact (fun_ext (fun b : real => @lem5138090 b x s)). Qed.
Lemma lem5138092 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138093 (x : real) (s : real -> Prop) : (term302 x s) = (term315 x s).
Proof. exact (MK_COMB (@lem5138092) (@lem5138091 x s)). Qed.
Lemma lem5138094 (x : real) (s : real -> Prop) : ((term301 x s) = (term302 x s)) = ((term300 x s) = (term315 x s)).
Proof. exact (MK_COMB (@lem5138085 x s) (@lem5138093 x s)). Qed.
Lemma lem5138095 (x : real) (s : real -> Prop) : (term300 x s) = (term315 x s).
Proof. exact (EQ_MP (@lem5138094 x s) (@lem5138075 x s)). Qed.
Lemma lem5138097 {A : Type'} (P : Prop) (Q : A -> Prop) : (term316 A P Q) = (term317 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5138098 (P : Prop) (Q : type1028) : (term318 P Q) = (term319 P Q).
Proof. exact (@lem5138097 (real -> real) P Q). Qed.
Lemma lem5138099 (b : real) (x : real) (s : real -> Prop) : (term320 b x s) = (term321 b x s).
Proof. exact (@lem5138098 (term256 b x s) (term298 x s)). Qed.
Lemma lem5138100 (x : real) (s : real -> Prop) (x' : real -> real) : (term322 x s x') = (term296 x s x').
Proof. exact (eq_refl (term322 x s x')). Qed.
Lemma lem5138101 (x : real) (s : real -> Prop) : (term323 x s) = (term298 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5138100 x s x')). Qed.
Lemma lem5138102 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5138103 (x : real) (s : real -> Prop) : (term324 x s) = (term299 x s).
Proof. exact (MK_COMB (@lem5138102) (@lem5138101 x s)). Qed.
Lemma lem5138104 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (eq_refl (term310 b x s)). Qed.
Lemma lem5138105 (b : real) (x : real) (s : real -> Prop) : (term320 b x s) = (term312 b x s).
Proof. exact (MK_COMB (@lem5138104 b x s) (@lem5138103 x s)). Qed.
Lemma lem5138106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138107 (b : real) (x : real) (s : real -> Prop) : (term325 b x s) = (term326 b x s).
Proof. exact (MK_COMB (@lem5138106) (@lem5138105 b x s)). Qed.
Lemma lem5138108 (x : real) (s : real -> Prop) (x' : real -> real) : (term322 x s x') = (term296 x s x').
Proof. exact (eq_refl (term322 x s x')). Qed.
Lemma lem5138109 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (eq_refl (term310 b x s)). Qed.
Lemma lem5138110 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) : (term327 b x s x') = (term328 b x s x').
Proof. exact (MK_COMB (@lem5138109 b x s) (@lem5138108 x s x')). Qed.
Lemma lem5138111 (b : real) (x : real) (s : real -> Prop) : (term329 b x s) = (term330 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5138110 b x s x')). Qed.
Lemma lem5138112 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5138113 (b : real) (x : real) (s : real -> Prop) : (term321 b x s) = (term331 b x s).
Proof. exact (MK_COMB (@lem5138112) (@lem5138111 b x s)). Qed.
Lemma lem5138114 (b : real) (x : real) (s : real -> Prop) : ((term320 b x s) = (term321 b x s)) = ((term312 b x s) = (term331 b x s)).
Proof. exact (MK_COMB (@lem5138107 b x s) (@lem5138113 b x s)). Qed.
Lemma lem5138115 (b : real) (x : real) (s : real -> Prop) : (term312 b x s) = (term331 b x s).
Proof. exact (EQ_MP (@lem5138114 b x s) (@lem5138099 b x s)). Qed.
Lemma lem5138116 (x : real) (s : real -> Prop) : (term314 x s) = (term332 x s).
Proof. exact (fun_ext (fun b : real => @lem5138115 b x s)). Qed.
Lemma lem5138117 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138118 (x : real) (s : real -> Prop) : (term315 x s) = (term333 x s).
Proof. exact (MK_COMB (@lem5138117) (@lem5138116 x s)). Qed.
Lemma lem5138119 (x : real) (s : real -> Prop) : (term300 x s) = (term333 x s).
Proof. exact (TRANS (@lem5138095 x s) (@lem5138118 x s)). Qed.
Lemma lem5138120 (x : real) (s : real -> Prop) : (term206 x s) = (term333 x s).
Proof. exact (TRANS (@lem5138071 x s) (@lem5138119 x s)). Qed.
Lemma lem5138121 (x : real) : (term215 x) = (term334 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5138120 x s)). Qed.
Lemma lem5138122 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5138123 (x : real) : (term216 x) = (term335 x).
Proof. exact (MK_COMB (@lem5138122) (@lem5138121 x)). Qed.
Lemma lem5138124 : term221 = term336.
Proof. exact (fun_ext (fun x : real => @lem5138123 x)). Qed.
Lemma lem5138125 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5138127 : term222 = term337.
Proof. exact (MK_COMB (@lem5138125) (@lem5138124)). Qed.
Lemma lem5138128 : term125 = term337.
Proof. exact (TRANS (@lem5137716) (@lem5138127)). Qed.
Lemma lem5138129 (h1 : term125) : term337.
Proof. exact (EQ_MP (@lem5138128) (@lem5137605 h1)). Qed.
Lemma lem5138136 (x : real) (y : real) (z : real) : (term338 x y z) = (term339 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5138137 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5138138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5138139 (x : real) (y : real) (z : real) : (term340 x y z) = (term341 x y z).
Proof. exact (MK_COMB (@lem5138138) (@lem5138136 x y z)). Qed.
Lemma lem5138140 (y : real) (x : real) (z : real) : (term342 y x z) = (term343 y x z).
Proof. exact (MK_COMB (@lem5138139 x y z) (@lem5138137 x z)). Qed.
Lemma lem5138141 (y : real) (x : real) (z : real) : (term142 y x z) = (term342 y x z).
Proof. exact (@lem17265 (term344 x y z) (real_le x z)). Qed.
Lemma lem5138142 (y : real) (x : real) (z : real) : (term142 y x z) = (term343 y x z).
Proof. exact (TRANS (@lem5138141 y x z) (@lem5138140 y x z)). Qed.
Lemma lem5138143 (y : real) (x : real) : (term143 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5138142 y x z)). Qed.
Lemma lem5138144 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138145 (y : real) (x : real) : (term144 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5138144) (@lem5138143 y x)). Qed.
Lemma lem5138146 (x : real) : (term145 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5138145 y x)). Qed.
Lemma lem5138147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138148 (x : real) : (term146 x) = (term348 x).
Proof. exact (MK_COMB (@lem5138147) (@lem5138146 x)). Qed.
Lemma lem5138149 : term147 = term349.
Proof. exact (fun_ext (fun x : real => @lem5138148 x)). Qed.
Lemma lem5138150 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138211 : term148 = term350.
Proof. exact (MK_COMB (@lem5138150) (@lem5138149)). Qed.
Lemma lem5138212 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5138211) (@lem5137606 h1)). Qed.
Lemma lem5138217 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5138218 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5138217 y x)). Qed.
Lemma lem5138219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138220 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5138219) (@lem5138218 x)). Qed.
Lemma lem5138221 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5138220 x)). Qed.
Lemma lem5138222 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138279 : term132 = term132.
Proof. exact (MK_COMB (@lem5138222) (@lem5138221)). Qed.
Lemma lem5138280 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5138279) (@lem5137607 h1)). Qed.
Lemma lem5138281 (x : real) (h1 : term335 x) : term335 x.
Proof. exact (h1). Qed.
Lemma lem5138282 (x : real) (s : real -> Prop) (h1 : term333 x s) : term333 x s.
Proof. exact (h1). Qed.
Lemma lem5138283 (b : real) (x : real) (s : real -> Prop) (h1 : term331 b x s) : term331 b x s.
Proof. exact (h1). Qed.
Lemma lem5138284 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term328 b x s x'.
Proof. exact (h1). Qed.
Lemma lem5138309 (y : real) (x : real) (z : real) : (term343 y x z) = (term343 y x z).
Proof. exact (eq_refl (term343 y x z)). Qed.
Lemma lem5138310 (y : real) (x : real) : (term345 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5138309 y x z)). Qed.
Lemma lem5138311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138312 (y : real) (x : real) : (term346 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5138311) (@lem5138310 y x)). Qed.
Lemma lem5138313 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5138312 y x)). Qed.
Lemma lem5138314 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138315 (x : real) : (term348 x) = (term348 x).
Proof. exact (MK_COMB (@lem5138314) (@lem5138313 x)). Qed.
Lemma lem5138316 : term349 = term349.
Proof. exact (fun_ext (fun x : real => @lem5138315 x)). Qed.
Lemma lem5138317 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138318 : term350 = term350.
Proof. exact (MK_COMB (@lem5138317) (@lem5138316)). Qed.
Lemma lem5138319 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5138318) (@lem5138212 h1)). Qed.
Lemma lem5138332 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5138333 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5138332 y x)). Qed.
Lemma lem5138334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138335 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5138334) (@lem5138333 x)). Qed.
Lemma lem5138336 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5138335 x)). Qed.
Lemma lem5138337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138338 : term132 = term132.
Proof. exact (MK_COMB (@lem5138337) (@lem5138336)). Qed.
Lemma lem5138339 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5138338) (@lem5138280 h1)). Qed.
Lemma lem5138388 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term292 x s x' b).
Proof. exact (eq_refl (term292 x s x' b)). Qed.
Lemma lem5138389 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term294 x s x').
Proof. exact (fun_ext (fun b : real => @lem5138388 x s x' b)). Qed.
Lemma lem5138390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138391 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term296 x s x').
Proof. exact (MK_COMB (@lem5138390) (@lem5138389 x s x')). Qed.
Lemma lem5138404 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5138419 (s : real -> Prop) (x : real) (b : real) : (term166 s x b) = (term166 s x b).
Proof. exact (eq_refl (term166 s x b)). Qed.
Lemma lem5138420 (s : real -> Prop) (b : real) : (term167 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5138419 s x b)). Qed.
Lemma lem5138421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138422 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5138421) (@lem5138420 s b)). Qed.
Lemma lem5138429 (b : real) (s : real -> Prop) : (term152 b s) = (term152 b s).
Proof. exact (eq_refl (term152 b s)). Qed.
Lemma lem5138430 (s : real -> Prop) (b : real) : (term169 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5138429 b s) (@lem5138422 s b)). Qed.
Lemma lem5138437 (x : real) (s : real -> Prop) : (term162 x s) = (term162 x s).
Proof. exact (eq_refl (term162 x s)). Qed.
Lemma lem5138438 (s : real -> Prop) : (term164 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5138437 x s)). Qed.
Lemma lem5138439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138440 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5138439) (@lem5138438 s)). Qed.
Lemma lem5138441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5138442 (s : real -> Prop) : (term173 s) = (term173 s).
Proof. exact (MK_COMB (@lem5138441) (@lem5138440 s)). Qed.
Lemma lem5138443 (s : real -> Prop) (b : real) : (term235 s b) = (term235 s b).
Proof. exact (MK_COMB (@lem5138442 s) (@lem5138430 s b)). Qed.
Lemma lem5138444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138445 (s : real -> Prop) (b : real) : (term254 s b) = (term254 s b).
Proof. exact (MK_COMB (@lem5138444) (@lem5138443 s b)). Qed.
Lemma lem5138446 (b : real) (x : real) (s : real -> Prop) : (term256 b x s) = (term256 b x s).
Proof. exact (MK_COMB (@lem5138445 s b) (@lem5138404 x s)). Qed.
Lemma lem5138447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138448 (b : real) (x : real) (s : real -> Prop) : (term310 b x s) = (term310 b x s).
Proof. exact (MK_COMB (@lem5138447) (@lem5138446 b x s)). Qed.
Lemma lem5138449 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) : (term328 b x s x') = (term328 b x s x').
Proof. exact (MK_COMB (@lem5138448 b x s) (@lem5138391 x s x')). Qed.
Lemma lem5138450 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term328 b x s x'.
Proof. exact (EQ_MP (@lem5138449 b x s x') (@lem5138284 b x s x' h1)). Qed.
Lemma lem5138451 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term296 x s x'.
Proof. exact (proj2 (@lem5138450 b x s x' h1)). Qed.
Lemma lem5138452 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term256 b x s.
Proof. exact (proj1 (@lem5138450 b x s x' h1)). Qed.
Lemma lem5138454 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term235 s b.
Proof. exact (proj1 (@lem5138452 b x s x' h1)). Qed.
Lemma lem5138457 (s : real -> Prop) (h1 : term165 s) : term165 s.
Proof. exact (h1). Qed.
Lemma lem5138458 (s : real -> Prop) (b : real) (h1 : term169 s b) : term169 s b.
Proof. exact (h1). Qed.
Lemma lem5138459 (s : real -> Prop) (b : real) (h1 : term169 s b) : term168 s b.
Proof. exact (proj2 (@lem5138458 s b h1)). Qed.
Lemma lem5138493 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5138494 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5138493 y x)). Qed.
Lemma lem5138495 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138496 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5138495) (@lem5138494 x)). Qed.
Lemma lem5138497 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5138496 x)). Qed.
Lemma lem5138498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138500 : term132 = term132.
Proof. exact (MK_COMB (@lem5138498) (@lem5138497)). Qed.
Lemma lem5138501 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5138500) (@lem5138339 h1)). Qed.
Lemma lem5138522 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term351 x s x' b).
Proof. exact (@lem19490 (term352 x x' b s) (term179 x b s) (term353 x' b)). Qed.
Lemma lem5138529 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term354 x s x' b) = (term355 x s x' b).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term353 x' b)). Qed.
Lemma lem5138536 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term357 x x' b s) = (term358 x x' b s).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term352 x x' b s)). Qed.
Lemma lem5138537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138538 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term359 x x' b s) = (term360 x x' b s).
Proof. exact (MK_COMB (@lem5138537) (@lem5138536 x x' b s)). Qed.
Lemma lem5138539 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term351 x s x' b) = (term361 x s x' b).
Proof. exact (MK_COMB (@lem5138538 x x' b s) (@lem5138529 x s x' b)). Qed.
Lemma lem5138541 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term361 x s x' b).
Proof. exact (TRANS (@lem5138522 x s x' b) (@lem5138539 x s x' b)). Qed.
Lemma lem5138542 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun b : real => @lem5138541 x s x' b)). Qed.
Lemma lem5138543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138545 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term363 x s x').
Proof. exact (MK_COMB (@lem5138543) (@lem5138542 x s x')). Qed.
Lemma lem5138546 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term363 x s x'.
Proof. exact (EQ_MP (@lem5138545 x s x') (@lem5138451 b x s x' h1)). Qed.
Lemma lem5138556 (x : real) (s : real -> Prop) : (term162 x s) = (term162 x s).
Proof. exact (eq_refl (term162 x s)). Qed.
Lemma lem5138557 (s : real -> Prop) : (term164 s) = (term164 s).
Proof. exact (fun_ext (fun x : real => @lem5138556 x s)). Qed.
Lemma lem5138558 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138560 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5138558) (@lem5138557 s)). Qed.
Lemma lem5138561 (s : real -> Prop) (h1 : term165 s) : term165 s.
Proof. exact (EQ_MP (@lem5138560 s) (@lem5138457 s h1)). Qed.
Lemma lem5138575 (y : real) (x : real) (z : real) : (term343 y x z) = (term343 y x z).
Proof. exact (eq_refl (term343 y x z)). Qed.
Lemma lem5138576 (y : real) (x : real) : (term345 y x) = (term345 y x).
Proof. exact (fun_ext (fun z : real => @lem5138575 y x z)). Qed.
Lemma lem5138577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138578 (y : real) (x : real) : (term346 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem5138577) (@lem5138576 y x)). Qed.
Lemma lem5138579 (x : real) : (term347 x) = (term347 x).
Proof. exact (fun_ext (fun y : real => @lem5138578 y x)). Qed.
Lemma lem5138580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138581 (x : real) : (term348 x) = (term348 x).
Proof. exact (MK_COMB (@lem5138580) (@lem5138579 x)). Qed.
Lemma lem5138582 : term349 = term349.
Proof. exact (fun_ext (fun x : real => @lem5138581 x)). Qed.
Lemma lem5138583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138585 : term350 = term350.
Proof. exact (MK_COMB (@lem5138583) (@lem5138582)). Qed.
Lemma lem5138586 (h1 : term148) : term350.
Proof. exact (EQ_MP (@lem5138585) (@lem5138319 h1)). Qed.
Lemma lem5138594 (y : real) (x : real) : (term138 y x) = (term138 y x).
Proof. exact (eq_refl (term138 y x)). Qed.
Lemma lem5138595 (x : real) : (term139 x) = (term139 x).
Proof. exact (fun_ext (fun y : real => @lem5138594 y x)). Qed.
Lemma lem5138596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138597 (x : real) : (term140 x) = (term140 x).
Proof. exact (MK_COMB (@lem5138596) (@lem5138595 x)). Qed.
Lemma lem5138598 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem5138597 x)). Qed.
Lemma lem5138599 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138601 : term132 = term132.
Proof. exact (MK_COMB (@lem5138599) (@lem5138598)). Qed.
Lemma lem5138602 (h1 : term132) : term132.
Proof. exact (EQ_MP (@lem5138601) (@lem5138339 h1)). Qed.
Lemma lem5138623 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term351 x s x' b).
Proof. exact (@lem19490 (term352 x x' b s) (term179 x b s) (term353 x' b)). Qed.
Lemma lem5138630 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term354 x s x' b) = (term355 x s x' b).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term353 x' b)). Qed.
Lemma lem5138637 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term357 x x' b s) = (term358 x x' b s).
Proof. exact (@lem19699 (term356 b x) (term162 b s) (term352 x x' b s)). Qed.
Lemma lem5138638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5138639 (x : real) (x' : real -> real) (b : real) (s : real -> Prop) : (term359 x x' b s) = (term360 x x' b s).
Proof. exact (MK_COMB (@lem5138638) (@lem5138637 x x' b s)). Qed.
Lemma lem5138640 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term351 x s x' b) = (term361 x s x' b).
Proof. exact (MK_COMB (@lem5138639 x x' b s) (@lem5138630 x s x' b)). Qed.
Lemma lem5138642 (x : real) (s : real -> Prop) (x' : real -> real) (b : real) : (term292 x s x' b) = (term361 x s x' b).
Proof. exact (TRANS (@lem5138623 x s x' b) (@lem5138640 x s x' b)). Qed.
Lemma lem5138643 (x : real) (s : real -> Prop) (x' : real -> real) : (term294 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun b : real => @lem5138642 x s x' b)). Qed.
Lemma lem5138644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138646 (x : real) (s : real -> Prop) (x' : real -> real) : (term296 x s x') = (term363 x s x').
Proof. exact (MK_COMB (@lem5138644) (@lem5138643 x s x')). Qed.
Lemma lem5138647 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term363 x s x'.
Proof. exact (EQ_MP (@lem5138646 x s x') (@lem5138451 b x s x' h1)). Qed.
Lemma lem5138667 (s : real -> Prop) (x : real) (b : real) : (term166 s x b) = (term166 s x b).
Proof. exact (eq_refl (term166 s x b)). Qed.
Lemma lem5138668 (s : real -> Prop) (b : real) : (term167 s b) = (term167 s b).
Proof. exact (fun_ext (fun x : real => @lem5138667 s x b)). Qed.
Lemma lem5138669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5138671 (s : real -> Prop) (b : real) : (term168 s b) = (term168 s b).
Proof. exact (MK_COMB (@lem5138669) (@lem5138668 s b)). Qed.
Lemma lem5138672 (s : real -> Prop) (b : real) (h1 : term169 s b) : term168 s b.
Proof. exact (EQ_MP (@lem5138671 s b) (@lem5138459 s b h1)). Qed.
Lemma lem5138682 (_67085 : real) (h1 : term132) : term364 _67085.
Proof. exact (@lem5138501 h1 _67085). Qed.
Lemma lem5138683 (_67085 : real) : (term364 _67085) = (term140 _67085).
Proof. exact (eq_refl (term364 _67085)). Qed.
Lemma lem5138684 (_67085 : real) (h1 : term132) : term140 _67085.
Proof. exact (EQ_MP (@lem5138683 _67085) (@lem5138682 _67085 h1)). Qed.
Lemma lem5138685 (_67085 : real) (_67086 : real) (h1 : term132) : term365 _67085 _67086.
Proof. exact (@lem5138684 _67085 h1 _67086). Qed.
Lemma lem5138686 (_67086 : real) (_67085 : real) : (term365 _67085 _67086) = (term138 _67086 _67085).
Proof. exact (eq_refl (term365 _67085 _67086)). Qed.
Lemma lem5138688 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term366 x s x' _67087.
Proof. exact (@lem5138546 b x s x' h1 _67087). Qed.
Lemma lem5138689 (x : real) (s : real -> Prop) (x' : real -> real) (_67087 : real) : (term366 x s x' _67087) = (term361 x s x' _67087).
Proof. exact (eq_refl (term366 x s x' _67087)). Qed.
Lemma lem5138690 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term361 x s x' _67087.
Proof. exact (EQ_MP (@lem5138689 x s x' _67087) (@lem5138688 _67087 b x s x' h1)). Qed.
Lemma lem5138691 (_67088 : real) (s : real -> Prop) (h1 : term165 s) : term367 s _67088.
Proof. exact (@lem5138561 s h1 _67088). Qed.
Lemma lem5138692 (_67088 : real) (s : real -> Prop) : (term367 s _67088) = (term162 _67088 s).
Proof. exact (eq_refl (term367 s _67088)). Qed.
Lemma lem5138694 (_67089 : real) (h1 : term148) : term368 _67089.
Proof. exact (@lem5138586 h1 _67089). Qed.
Lemma lem5138695 (_67089 : real) : (term368 _67089) = (term348 _67089).
Proof. exact (eq_refl (term368 _67089)). Qed.
Lemma lem5138696 (_67089 : real) (h1 : term148) : term348 _67089.
Proof. exact (EQ_MP (@lem5138695 _67089) (@lem5138694 _67089 h1)). Qed.
Lemma lem5138697 (_67089 : real) (_67090 : real) (h1 : term148) : term369 _67089 _67090.
Proof. exact (@lem5138696 _67089 h1 _67090). Qed.
Lemma lem5138698 (_67090 : real) (_67089 : real) : (term369 _67089 _67090) = (term346 _67090 _67089).
Proof. exact (eq_refl (term369 _67089 _67090)). Qed.
Lemma lem5138699 (_67090 : real) (_67089 : real) (h1 : term148) : term346 _67090 _67089.
Proof. exact (EQ_MP (@lem5138698 _67090 _67089) (@lem5138697 _67089 _67090 h1)). Qed.
Lemma lem5138700 (_67090 : real) (_67089 : real) (_67091 : real) (h1 : term148) : term370 _67090 _67089 _67091.
Proof. exact (@lem5138699 _67090 _67089 h1 _67091). Qed.
Lemma lem5138701 (_67090 : real) (_67089 : real) (_67091 : real) : (term370 _67090 _67089 _67091) = (term343 _67090 _67089 _67091).
Proof. exact (eq_refl (term370 _67090 _67089 _67091)). Qed.
Lemma lem5138702 (_67090 : real) (_67089 : real) (_67091 : real) (h1 : term148) : term343 _67090 _67089 _67091.
Proof. exact (EQ_MP (@lem5138701 _67090 _67089 _67091) (@lem5138700 _67090 _67089 _67091 h1)). Qed.
Lemma lem5138703 (_67092 : real) (h1 : term132) : term364 _67092.
Proof. exact (@lem5138602 h1 _67092). Qed.
Lemma lem5138704 (_67092 : real) : (term364 _67092) = (term140 _67092).
Proof. exact (eq_refl (term364 _67092)). Qed.
Lemma lem5138705 (_67092 : real) (h1 : term132) : term140 _67092.
Proof. exact (EQ_MP (@lem5138704 _67092) (@lem5138703 _67092 h1)). Qed.
Lemma lem5138706 (_67092 : real) (_67093 : real) (h1 : term132) : term365 _67092 _67093.
Proof. exact (@lem5138705 _67092 h1 _67093). Qed.
Lemma lem5138707 (_67093 : real) (_67092 : real) : (term365 _67092 _67093) = (term138 _67093 _67092).
Proof. exact (eq_refl (term365 _67092 _67093)). Qed.
Lemma lem5138709 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term366 x s x' _67094.
Proof. exact (@lem5138647 b x s x' h1 _67094). Qed.
Lemma lem5138710 (x : real) (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term366 x s x' _67094) = (term361 x s x' _67094).
Proof. exact (eq_refl (term366 x s x' _67094)). Qed.
Lemma lem5138711 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term361 x s x' _67094.
Proof. exact (EQ_MP (@lem5138710 x s x' _67094) (@lem5138709 _67094 b x s x' h1)). Qed.
Lemma lem5138712 (_67095 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term371 s b _67095.
Proof. exact (@lem5138672 s b h1 _67095). Qed.
Lemma lem5138713 (s : real -> Prop) (_67095 : real) (b : real) : (term371 s b _67095) = (term166 s _67095 b).
Proof. exact (eq_refl (term371 s b _67095)). Qed.
Lemma lem5138715 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term355 x s x' _67087.
Proof. exact (proj2 (@lem5138690 _67087 b x s x' h1)). Qed.
Lemma lem5138716 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term358 x x' _67087 s.
Proof. exact (proj1 (@lem5138690 _67087 b x s x' h1)). Qed.
Lemma lem5138721 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term355 x s x' _67094.
Proof. exact (proj2 (@lem5138711 _67094 b x s x' h1)). Qed.
Lemma lem5138722 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term358 x x' _67094 s.
Proof. exact (proj1 (@lem5138711 _67094 b x s x' h1)). Qed.
Lemma lem5138744 (_67086 : real) (_67085 : real) (h1 : term132) : term138 _67086 _67085.
Proof. exact (EQ_MP (@lem5138686 _67086 _67085) (@lem5138685 _67085 _67086 h1)). Qed.
Lemma lem5138756 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term372 x x' _67087.
Proof. exact (proj1 (@lem5138715 _67087 b x s x' h1)). Qed.
Lemma lem5138772 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term373 x x' _67087 s.
Proof. exact (proj1 (@lem5138716 _67087 b x s x' h1)). Qed.
Lemma lem5138793 (_67090 : real) (_67089 : real) (_67091 : real) : (term343 _67090 _67089 _67091) = (term374 _67090 _67089 _67091).
Proof. exact (@lem5136710 (term375 _67089 _67090) (term375 _67090 _67091) (real_le _67089 _67091)). Qed.
Lemma lem5138794 (_67090 : real) (_67089 : real) (_67091 : real) (h1 : term148) : term374 _67090 _67089 _67091.
Proof. exact (EQ_MP (@lem5138793 _67090 _67089 _67091) (@lem5138702 _67090 _67089 _67091 h1)). Qed.
Lemma lem5138800 (_67093 : real) (_67092 : real) (h1 : term132) : term138 _67093 _67092.
Proof. exact (EQ_MP (@lem5138707 _67093 _67092) (@lem5138706 _67092 _67093 h1)). Qed.
Lemma lem5138812 (_67095 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term166 s _67095 b.
Proof. exact (EQ_MP (@lem5138713 s _67095 b) (@lem5138712 _67095 s b h1)). Qed.
Lemma lem5138818 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term372 x x' _67094.
Proof. exact (proj1 (@lem5138721 _67094 b x s x' h1)). Qed.
Lemma lem5138824 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term376 s x' _67094.
Proof. exact (proj2 (@lem5138721 _67094 b x s x' h1)). Qed.
Lemma lem5138834 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term373 x x' _67094 s.
Proof. exact (proj1 (@lem5138722 _67094 b x s x' h1)). Qed.
Lemma lem5138844 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term377 x x' _67094 s.
Proof. exact (proj2 (@lem5138722 _67094 b x s x' h1)). Qed.
Lemma lem5138876 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5138877 (_67102 : real) (_67104 : real) (h1 : _67102 = _67104) : _67102 = _67104.
Proof. exact (h1). Qed.
Lemma lem5138878 (_67103 : real) (_67105 : real) (h1 : _67103 = _67105) : _67103 = _67105.
Proof. exact (h1). Qed.
Lemma lem5138879 (_67102 : real) (_67104 : real) (h1 : _67102 = _67104) : (real_le _67102) = (real_le _67104).
Proof. exact (MK_COMB (@lem5138876) (@lem5138877 _67102 _67104 h1)). Qed.
Lemma lem5138880 (_67102 : real) (_67104 : real) (_67103 : real) (_67105 : real) (h1 : _67102 = _67104) (h2 : _67103 = _67105) : (real_le _67102 _67103) = (real_le _67104 _67105).
Proof. exact (MK_COMB (@lem5138879 _67102 _67104 h1) (@lem5138878 _67103 _67105 h2)). Qed.
Lemma lem5138882 (b : Prop) (a : Prop) : term378 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5138883 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : term379 _67104 _67105 _67102 _67103.
Proof. exact (@lem5138882 (real_le _67104 _67105) (real_le _67102 _67103)). Qed.
Lemma lem5138884 (_67102 : real) (_67104 : real) (_67103 : real) (_67105 : real) (h1 : _67102 = _67104) (h2 : _67103 = _67105) : term380 _67104 _67105 _67102 _67103.
Proof. exact (@lem5138883 _67104 _67105 _67102 _67103 (@lem5138880 _67102 _67104 _67103 _67105 h1 h2)). Qed.
Lemma lem5138885 (_67105 : real) (_67103 : real) (_67102 : real) (_67104 : real) (h1 : _67102 = _67104) : term381 _67104 _67105 _67102 _67103.
Proof. exact (fun h0 : _67103 = _67105 => @lem5138884 _67102 _67104 _67103 _67105 h1 h0). Qed.
Lemma lem5138887 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5138888 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term381 _67104 _67105 _67102 _67103) = (term383 _67104 _67105 _67102 _67103).
Proof. exact (@lem5138887 (_67103 = _67105) (term380 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5138889 (_67105 : real) (_67103 : real) (_67102 : real) (_67104 : real) (h1 : _67102 = _67104) : term383 _67104 _67105 _67102 _67103.
Proof. exact (EQ_MP (@lem5138888 _67104 _67105 _67102 _67103) (@lem5138885 _67105 _67103 _67102 _67104 h1)). Qed.
Lemma lem5138890 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : term384 _67104 _67105 _67102 _67103.
Proof. exact (fun h0 : _67102 = _67104 => @lem5138889 _67105 _67103 _67102 _67104 h0). Qed.
Lemma lem5138892 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5138893 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term384 _67104 _67105 _67102 _67103) = (term385 _67104 _67105 _67102 _67103).
Proof. exact (@lem5138892 (_67102 = _67104) (term383 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5138894 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : term385 _67104 _67105 _67102 _67103.
Proof. exact (EQ_MP (@lem5138893 _67104 _67105 _67102 _67103) (@lem5138890 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5138908 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5138909 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5138908 x). Qed.
Lemma lem5138911 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5138912 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5138911 (x = x)). Qed.
Lemma lem5138913 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5138912 x) (@lem5138909 x)). Qed.
Lemma lem5138915 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5138916 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5138915 (x' x)). Qed.
Lemma lem5138917 (x' : real -> real) (x : real) : term389 x' x.
Proof. exact (fun h0 : term390 x' x => @lem5138916 x' x). Qed.
Lemma lem5138919 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5138920 (x' : real -> real) (x : real) : (term389 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5138919 ((x' x) = (x' x))). Qed.
Lemma lem5138921 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5138920 x' x) (@lem5138917 x' x)). Qed.
Lemma lem5138923 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5138924 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5138923 x). Qed.
Lemma lem5138926 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5138927 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5138926 (x = x)). Qed.
Lemma lem5138928 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5138927 x) (@lem5138924 x)). Qed.
Lemma lem5138930 (_67088 : real) (s : real -> Prop) (h1 : term165 s) : term162 _67088 s.
Proof. exact (EQ_MP (@lem5138692 _67088 s) (@lem5138691 _67088 s h1)). Qed.
Lemma lem5138931 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term391 x' x s.
Proof. exact (@lem5138930 (x' x) s h1). Qed.
Lemma lem5138932 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term392 x' x s.
Proof. exact (fun h0 : term393 x' x s => @lem5138931 x' x s h1). Qed.
Lemma lem5138934 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5138935 (x' : real -> real) (x : real) (s : real -> Prop) : (term392 x' x s) = (term391 x' x s).
Proof. exact (@lem5138934 (term393 x' x s)). Qed.
Lemma lem5138936 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term391 x' x s.
Proof. exact (EQ_MP (@lem5138935 x' x s) (@lem5138932 x' x s h1)). Qed.
Lemma lem5138942 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5138943 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term373 x x' _67087 s) = (term395 x x' _67087 s).
Proof. exact (@lem5138942 ((x' _67087) = x) (term356 _67087 x) (term393 x' _67087 s)). Qed.
Lemma lem5138959 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5138960 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term396 x x' _67087 s) = (term397 x' s _67087 x).
Proof. exact (@lem5138959 (term393 x' _67087 s) (term356 _67087 x)). Qed.
Lemma lem5138968 (x' : real -> real) (_67087 : real) (x : real) : (term398 x' _67087 x) = (term398 x' _67087 x).
Proof. exact (eq_refl (term398 x' _67087 x)). Qed.
Lemma lem5138969 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term395 x x' _67087 s) = (term399 x' s _67087 x).
Proof. exact (MK_COMB (@lem5138968 x' _67087 x) (@lem5138960 x' s _67087 x)). Qed.
Lemma lem5138980 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term373 x x' _67087 s) = (term399 x' s _67087 x).
Proof. exact (TRANS (@lem5138943 x x' _67087 s) (@lem5138969 x' s _67087 x)). Qed.
Lemma lem5138981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5138982 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term400 x x' _67087 s) = (term401 x' s _67087 x).
Proof. exact (MK_COMB (@lem5138981) (@lem5138980 x' s _67087 x)). Qed.
Lemma lem5138998 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5138999 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term396 x x' _67087 s) = (term397 x' s _67087 x).
Proof. exact (@lem5138998 (term393 x' _67087 s) (term356 _67087 x)). Qed.
Lemma lem5139007 (x' : real -> real) (_67087 : real) (x : real) : (term398 x' _67087 x) = (term398 x' _67087 x).
Proof. exact (eq_refl (term398 x' _67087 x)). Qed.
Lemma lem5139008 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : (term395 x x' _67087 s) = (term399 x' s _67087 x).
Proof. exact (MK_COMB (@lem5139007 x' _67087 x) (@lem5138999 x' s _67087 x)). Qed.
Lemma lem5139019 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : ((term373 x x' _67087 s) = (term395 x x' _67087 s)) = ((term399 x' s _67087 x) = (term399 x' s _67087 x)).
Proof. exact (MK_COMB (@lem5138982 x' s _67087 x) (@lem5139008 x' s _67087 x)). Qed.
Lemma lem5139021 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139022 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139021 Prop x). Qed.
Lemma lem5139023 (x' : real -> real) (s : real -> Prop) (_67087 : real) (x : real) : ((term399 x' s _67087 x) = (term399 x' s _67087 x)) = True.
Proof. exact (@lem5139022 (term399 x' s _67087 x)). Qed.
Lemma lem5139024 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : ((term373 x x' _67087 s) = (term395 x x' _67087 s)) = True.
Proof. exact (TRANS (@lem5139019 x' s _67087 x) (@lem5139023 x' s _67087 x)). Qed.
Lemma lem5139025 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : True = ((term373 x x' _67087 s) = (term395 x x' _67087 s)).
Proof. exact (SYM (@lem5139024 x x' _67087 s)). Qed.
Lemma lem5139026 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term373 x x' _67087 s) = (term395 x x' _67087 s).
Proof. exact (EQ_MP (@lem5139025 x x' _67087 s) (@lem0)). Qed.
Lemma lem5139027 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term395 x x' _67087 s.
Proof. exact (EQ_MP (@lem5139026 x x' _67087 s) (@lem5138772 _67087 b x s x' h1)). Qed.
Lemma lem5139029 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139030 (s : real -> Prop) (x' : real -> real) (_67087 : real) (x : real) : (term395 x x' _67087 s) = (term403 s x' _67087 x).
Proof. exact (@lem5139029 (term396 x x' _67087 s) ((x' _67087) = x)). Qed.
Lemma lem5139032 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139033 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term406 x x' _67087 s) = (term407 x x' _67087 s).
Proof. exact (@lem5139032 (term356 _67087 x) (term393 x' _67087 s)). Qed.
Lemma lem5139035 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139036 (_67087 : real) (x : real) : (term409 _67087 x) = (_67087 = x).
Proof. exact (@lem5139035 (_67087 = x)). Qed.
Lemma lem5139037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139038 (_67087 : real) (x : real) : (term410 _67087 x) = (term411 _67087 x).
Proof. exact (MK_COMB (@lem5139037) (@lem5139036 _67087 x)). Qed.
Lemma lem5139039 (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term391 x' _67087 s) = (term391 x' _67087 s).
Proof. exact (eq_refl (term391 x' _67087 s)). Qed.
Lemma lem5139040 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term407 x x' _67087 s) = (term412 x x' _67087 s).
Proof. exact (MK_COMB (@lem5139038 _67087 x) (@lem5139039 x' _67087 s)). Qed.
Lemma lem5139041 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term406 x x' _67087 s) = (term412 x x' _67087 s).
Proof. exact (TRANS (@lem5139033 x x' _67087 s) (@lem5139040 x x' _67087 s)). Qed.
Lemma lem5139042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139043 (x : real) (x' : real -> real) (_67087 : real) (s : real -> Prop) : (term413 x x' _67087 s) = (term414 x x' _67087 s).
Proof. exact (MK_COMB (@lem5139042) (@lem5139041 x x' _67087 s)). Qed.
Lemma lem5139044 (x' : real -> real) (_67087 : real) (x : real) : ((x' _67087) = x) = ((x' _67087) = x).
Proof. exact (eq_refl ((x' _67087) = x)). Qed.
Lemma lem5139045 (s : real -> Prop) (x' : real -> real) (_67087 : real) (x : real) : (term403 s x' _67087 x) = (term415 s x' _67087 x).
Proof. exact (MK_COMB (@lem5139043 x x' _67087 s) (@lem5139044 x' _67087 x)). Qed.
Lemma lem5139046 (s : real -> Prop) (x' : real -> real) (_67087 : real) (x : real) : (term395 x x' _67087 s) = (term415 s x' _67087 x).
Proof. exact (TRANS (@lem5139030 s x' _67087 x) (@lem5139045 s x' _67087 x)). Qed.
Lemma lem5139048 (x' : real -> real) (x : real) (s : real -> Prop) (h1 : term165 s) : term416 x' x s.
Proof. exact (conj (@lem5138928 x) (@lem5138936 x' x s h1)). Qed.
Lemma lem5139050 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term415 s x' _67087 x.
Proof. exact (EQ_MP (@lem5139046 s x' _67087 x) (@lem5139027 _67087 b x s x' h1)). Qed.
Lemma lem5139051 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term417 s x' x.
Proof. exact (@lem5139050 x b x s x' h1). Qed.
Lemma lem5139054 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : (x' x) = x.
Proof. exact (@lem5139051 b x s x' h2 (@lem5139048 x' x s h1)). Qed.
Lemma lem5139055 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : term418 x' x.
Proof. exact (fun h0 : term419 x' x => @lem5139054 b x s x' h1 h2). Qed.
Lemma lem5139057 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139058 (x' : real -> real) (x : real) : (term418 x' x) = ((x' x) = x).
Proof. exact (@lem5139057 ((x' x) = x)). Qed.
Lemma lem5139059 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term165 s) (h2 : term328 b x s x') : (x' x) = x.
Proof. exact (EQ_MP (@lem5139058 x' x) (@lem5139055 b x s x' h1 h2)). Qed.
Lemma lem5139062 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (h1). Qed.
Lemma lem5139063 (x' : real -> real) (x : real) (h1 : term420 x' x) : term421 x' x.
Proof. exact (fun h0 : term422 x' x => @lem5139062 x' x h1). Qed.
Lemma lem5139065 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139066 (x' : real -> real) (x : real) : (term421 x' x) = (term420 x' x).
Proof. exact (@lem5139065 (term422 x' x)). Qed.
Lemma lem5139067 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (EQ_MP (@lem5139066 x' x) (@lem5139063 x' x h1)). Qed.
Lemma lem5139078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139079 (_67086 : real) (_67085 : real) : (term138 _67085 _67086) = (term138 _67086 _67085).
Proof. exact (@lem5139078 (real_le _67085 _67086) (real_le _67086 _67085)). Qed.
Lemma lem5139085 (_67086 : real) (_67085 : real) : (term423 _67086 _67085) = (term423 _67086 _67085).
Proof. exact (eq_refl (term423 _67086 _67085)). Qed.
Lemma lem5139086 (_67086 : real) (_67085 : real) : ((term138 _67086 _67085) = (term138 _67085 _67086)) = ((term138 _67086 _67085) = (term138 _67086 _67085)).
Proof. exact (MK_COMB (@lem5139085 _67086 _67085) (@lem5139079 _67086 _67085)). Qed.
Lemma lem5139088 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139089 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139088 Prop x). Qed.
Lemma lem5139090 (_67086 : real) (_67085 : real) : ((term138 _67086 _67085) = (term138 _67086 _67085)) = True.
Proof. exact (@lem5139089 (term138 _67086 _67085)). Qed.
Lemma lem5139091 (_67085 : real) (_67086 : real) : ((term138 _67086 _67085) = (term138 _67085 _67086)) = True.
Proof. exact (TRANS (@lem5139086 _67086 _67085) (@lem5139090 _67086 _67085)). Qed.
Lemma lem5139092 (_67085 : real) (_67086 : real) : True = ((term138 _67086 _67085) = (term138 _67085 _67086)).
Proof. exact (SYM (@lem5139091 _67085 _67086)). Qed.
Lemma lem5139093 (_67085 : real) (_67086 : real) : (term138 _67086 _67085) = (term138 _67085 _67086).
Proof. exact (EQ_MP (@lem5139092 _67085 _67086) (@lem0)). Qed.
Lemma lem5139094 (_67085 : real) (_67086 : real) (h1 : term132) : term138 _67085 _67086.
Proof. exact (EQ_MP (@lem5139093 _67085 _67086) (@lem5138744 _67086 _67085 h1)). Qed.
Lemma lem5139096 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139099 (_67086 : real) (_67085 : real) : (term138 _67085 _67086) = (term424 _67086 _67085).
Proof. exact (@lem5139096 (real_le _67085 _67086) (real_le _67086 _67085)). Qed.
Lemma lem5139102 (_67086 : real) (_67085 : real) (h1 : term132) : term424 _67086 _67085.
Proof. exact (EQ_MP (@lem5139099 _67086 _67085) (@lem5139094 _67085 _67086 h1)). Qed.
Lemma lem5139103 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (@lem5139102 (x' x) (x' x) h1). Qed.
Lemma lem5139106 (x' : real -> real) (x : real) (h1 : term132) (h2 : term420 x' x) : term422 x' x.
Proof. exact (@lem5139103 x' x h1 (@lem5139067 x' x h2)). Qed.
Lemma lem5139107 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (fun h0 : term420 x' x => @lem5139106 x' x h1 h0). Qed.
Lemma lem5139109 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139110 (x' : real -> real) (x : real) : (term425 x' x) = (term422 x' x).
Proof. exact (@lem5139109 (term422 x' x)). Qed.
Lemma lem5139111 (x' : real -> real) (x : real) (h1 : term132) : term422 x' x.
Proof. exact (EQ_MP (@lem5139110 x' x) (@lem5139107 x' x h1)). Qed.
Lemma lem5139129 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139130 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term383 _67104 _67105 _67102 _67103) = (term426 _67104 _67105 _67102 _67103).
Proof. exact (@lem5139129 (real_le _67104 _67105) (term356 _67103 _67105) (term375 _67102 _67103)). Qed.
Lemma lem5139148 (_67102 : real) (_67104 : real) : (term427 _67102 _67104) = (term427 _67102 _67104).
Proof. exact (eq_refl (term427 _67102 _67104)). Qed.
Lemma lem5139149 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term385 _67104 _67105 _67102 _67103) = (term428 _67104 _67105 _67102 _67103).
Proof. exact (MK_COMB (@lem5139148 _67102 _67104) (@lem5139130 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139153 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139154 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term428 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103).
Proof. exact (@lem5139153 (real_le _67104 _67105) (term356 _67102 _67104) (term430 _67105 _67102 _67103)). Qed.
Lemma lem5139184 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term385 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103).
Proof. exact (TRANS (@lem5139149 _67104 _67105 _67102 _67103) (@lem5139154 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5139186 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term431 _67104 _67105 _67102 _67103) = (term432 _67104 _67105 _67102 _67103).
Proof. exact (MK_COMB (@lem5139185) (@lem5139184 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139216 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term429 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103).
Proof. exact (eq_refl (term429 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139217 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : ((term385 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103)) = ((term429 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103)).
Proof. exact (MK_COMB (@lem5139186 _67104 _67105 _67102 _67103) (@lem5139216 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139219 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139220 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139219 Prop x). Qed.
Lemma lem5139221 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : ((term429 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103)) = True.
Proof. exact (@lem5139220 (term429 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139222 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : ((term385 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103)) = True.
Proof. exact (TRANS (@lem5139217 _67104 _67105 _67102 _67103) (@lem5139221 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139223 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : True = ((term385 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103)).
Proof. exact (SYM (@lem5139222 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139224 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term385 _67104 _67105 _67102 _67103) = (term429 _67104 _67105 _67102 _67103).
Proof. exact (EQ_MP (@lem5139223 _67104 _67105 _67102 _67103) (@lem0)). Qed.
Lemma lem5139225 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : term429 _67104 _67105 _67102 _67103.
Proof. exact (EQ_MP (@lem5139224 _67104 _67105 _67102 _67103) (@lem5138894 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139227 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139228 (_67102 : real) (_67103 : real) (_67104 : real) (_67105 : real) : (term429 _67104 _67105 _67102 _67103) = (term433 _67102 _67103 _67104 _67105).
Proof. exact (@lem5139227 (term434 _67104 _67105 _67102 _67103) (real_le _67104 _67105)). Qed.
Lemma lem5139230 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139231 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term435 _67104 _67105 _67102 _67103) = (term436 _67104 _67105 _67102 _67103).
Proof. exact (@lem5139230 (term356 _67102 _67104) (term430 _67105 _67102 _67103)). Qed.
Lemma lem5139233 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139234 (_67102 : real) (_67104 : real) : (term409 _67102 _67104) = (_67102 = _67104).
Proof. exact (@lem5139233 (_67102 = _67104)). Qed.
Lemma lem5139235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139236 (_67102 : real) (_67104 : real) : (term410 _67102 _67104) = (term411 _67102 _67104).
Proof. exact (MK_COMB (@lem5139235) (@lem5139234 _67102 _67104)). Qed.
Lemma lem5139238 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139239 (_67105 : real) (_67102 : real) (_67103 : real) : (term437 _67105 _67102 _67103) = (term438 _67105 _67102 _67103).
Proof. exact (@lem5139238 (term356 _67103 _67105) (term375 _67102 _67103)). Qed.
Lemma lem5139241 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139242 (_67103 : real) (_67105 : real) : (term409 _67103 _67105) = (_67103 = _67105).
Proof. exact (@lem5139241 (_67103 = _67105)). Qed.
Lemma lem5139243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139244 (_67103 : real) (_67105 : real) : (term410 _67103 _67105) = (term411 _67103 _67105).
Proof. exact (MK_COMB (@lem5139243) (@lem5139242 _67103 _67105)). Qed.
Lemma lem5139246 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139247 (_67102 : real) (_67103 : real) : (term439 _67102 _67103) = (real_le _67102 _67103).
Proof. exact (@lem5139246 (real_le _67102 _67103)). Qed.
Lemma lem5139248 (_67105 : real) (_67102 : real) (_67103 : real) : (term438 _67105 _67102 _67103) = (term440 _67105 _67102 _67103).
Proof. exact (MK_COMB (@lem5139244 _67103 _67105) (@lem5139247 _67102 _67103)). Qed.
Lemma lem5139249 (_67105 : real) (_67102 : real) (_67103 : real) : (term437 _67105 _67102 _67103) = (term440 _67105 _67102 _67103).
Proof. exact (TRANS (@lem5139239 _67105 _67102 _67103) (@lem5139248 _67105 _67102 _67103)). Qed.
Lemma lem5139250 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term436 _67104 _67105 _67102 _67103) = (term441 _67104 _67105 _67102 _67103).
Proof. exact (MK_COMB (@lem5139236 _67102 _67104) (@lem5139249 _67105 _67102 _67103)). Qed.
Lemma lem5139251 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term435 _67104 _67105 _67102 _67103) = (term441 _67104 _67105 _67102 _67103).
Proof. exact (TRANS (@lem5139231 _67104 _67105 _67102 _67103) (@lem5139250 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139253 (_67104 : real) (_67105 : real) (_67102 : real) (_67103 : real) : (term442 _67104 _67105 _67102 _67103) = (term443 _67104 _67105 _67102 _67103).
Proof. exact (MK_COMB (@lem5139252) (@lem5139251 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139254 (_67104 : real) (_67105 : real) : (real_le _67104 _67105) = (real_le _67104 _67105).
Proof. exact (eq_refl (real_le _67104 _67105)). Qed.
Lemma lem5139255 (_67102 : real) (_67103 : real) (_67104 : real) (_67105 : real) : (term433 _67102 _67103 _67104 _67105) = (term444 _67102 _67103 _67104 _67105).
Proof. exact (MK_COMB (@lem5139253 _67104 _67105 _67102 _67103) (@lem5139254 _67104 _67105)). Qed.
Lemma lem5139256 (_67102 : real) (_67103 : real) (_67104 : real) (_67105 : real) : (term429 _67104 _67105 _67102 _67103) = (term444 _67102 _67103 _67104 _67105).
Proof. exact (TRANS (@lem5139228 _67102 _67103 _67104 _67105) (@lem5139255 _67102 _67103 _67104 _67105)). Qed.
Lemma lem5139258 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term445 x' x.
Proof. exact (conj (@lem5139059 b x s x' h2 h3) (@lem5139111 x' x h1)). Qed.
Lemma lem5139259 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term446 x' x.
Proof. exact (conj (@lem5138921 x' x) (@lem5139258 b x s x' h1 h2 h3)). Qed.
Lemma lem5139261 (_67102 : real) (_67103 : real) (_67104 : real) (_67105 : real) : term444 _67102 _67103 _67104 _67105.
Proof. exact (EQ_MP (@lem5139256 _67102 _67103 _67104 _67105) (@lem5139225 _67104 _67105 _67102 _67103)). Qed.
Lemma lem5139262 (x' : real -> real) (x : real) : term447 x' x.
Proof. exact (@lem5139261 (x' x) (x' x) (x' x) x). Qed.
Lemma lem5139265 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term448 x' x.
Proof. exact (@lem5139262 x' x (@lem5139259 b x s x' h1 h2 h3)). Qed.
Lemma lem5139266 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term449 x' x.
Proof. exact (fun h0 : term353 x' x => @lem5139265 b x s x' h1 h2 h3). Qed.
Lemma lem5139268 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139269 (x' : real -> real) (x : real) : (term449 x' x) = (term448 x' x).
Proof. exact (@lem5139268 (term448 x' x)). Qed.
Lemma lem5139270 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term448 x' x.
Proof. exact (EQ_MP (@lem5139269 x' x) (@lem5139266 b x s x' h1 h2 h3)). Qed.
Lemma lem5139272 (a : Prop) (b : Prop) : (term450 a b) = (term451 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5139273 (x : real) (x' : real -> real) (_67087 : real) : (term372 x x' _67087) = (term452 x x' _67087).
Proof. exact (@lem5139272 (_67087 = x) (term448 x' _67087)). Qed.
Lemma lem5139275 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5139276 (x : real) (x' : real -> real) (_67087 : real) : (term452 x x' _67087) = (term453 x x' _67087).
Proof. exact (@lem5139275 (term454 x x' _67087)). Qed.
Lemma lem5139277 (x : real) (x' : real -> real) (_67087 : real) : (term372 x x' _67087) = (term453 x x' _67087).
Proof. exact (TRANS (@lem5139273 x x' _67087) (@lem5139276 x x' _67087)). Qed.
Lemma lem5139279 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term455 x' x.
Proof. exact (conj (@lem5138913 x) (@lem5139270 b x s x' h1 h2 h3)). Qed.
Lemma lem5139281 (_67087 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term453 x x' _67087.
Proof. exact (EQ_MP (@lem5139277 x x' _67087) (@lem5138756 _67087 b x s x' h1)). Qed.
Lemma lem5139282 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term456 x' x.
Proof. exact (@lem5139281 x b x s x' h1). Qed.
Lemma lem5139285 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (@lem5139282 b x s x' h3 (@lem5139279 b x s x' h1 h2 h3)). Qed.
Lemma lem5139286 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term457.
Proof. exact (fun h0 : ~ False => @lem5139285 b x s x' h1 h2 h3). Qed.
Lemma lem5139288 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139289 : term457 = False.
Proof. exact (@lem5139288 False). Qed.
Lemma lem5139290 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5139289) (@lem5139286 b x s x' h1 h2 h3)). Qed.
Lemma lem5139322 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5139323 (_67114 : real) (_67116 : real) (h1 : _67114 = _67116) : _67114 = _67116.
Proof. exact (h1). Qed.
Lemma lem5139324 (_67115 : real) (_67117 : real) (h1 : _67115 = _67117) : _67115 = _67117.
Proof. exact (h1). Qed.
Lemma lem5139325 (_67114 : real) (_67116 : real) (h1 : _67114 = _67116) : (real_le _67114) = (real_le _67116).
Proof. exact (MK_COMB (@lem5139322) (@lem5139323 _67114 _67116 h1)). Qed.
Lemma lem5139326 (_67114 : real) (_67116 : real) (_67115 : real) (_67117 : real) (h1 : _67114 = _67116) (h2 : _67115 = _67117) : (real_le _67114 _67115) = (real_le _67116 _67117).
Proof. exact (MK_COMB (@lem5139325 _67114 _67116 h1) (@lem5139324 _67115 _67117 h2)). Qed.
Lemma lem5139328 (b : Prop) (a : Prop) : term378 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5139329 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : term379 _67116 _67117 _67114 _67115.
Proof. exact (@lem5139328 (real_le _67116 _67117) (real_le _67114 _67115)). Qed.
Lemma lem5139330 (_67114 : real) (_67116 : real) (_67115 : real) (_67117 : real) (h1 : _67114 = _67116) (h2 : _67115 = _67117) : term380 _67116 _67117 _67114 _67115.
Proof. exact (@lem5139329 _67116 _67117 _67114 _67115 (@lem5139326 _67114 _67116 _67115 _67117 h1 h2)). Qed.
Lemma lem5139331 (_67117 : real) (_67115 : real) (_67114 : real) (_67116 : real) (h1 : _67114 = _67116) : term381 _67116 _67117 _67114 _67115.
Proof. exact (fun h0 : _67115 = _67117 => @lem5139330 _67114 _67116 _67115 _67117 h1 h0). Qed.
Lemma lem5139333 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5139334 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term381 _67116 _67117 _67114 _67115) = (term383 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139333 (_67115 = _67117) (term380 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139335 (_67117 : real) (_67115 : real) (_67114 : real) (_67116 : real) (h1 : _67114 = _67116) : term383 _67116 _67117 _67114 _67115.
Proof. exact (EQ_MP (@lem5139334 _67116 _67117 _67114 _67115) (@lem5139331 _67117 _67115 _67114 _67116 h1)). Qed.
Lemma lem5139336 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : term384 _67116 _67117 _67114 _67115.
Proof. exact (fun h0 : _67114 = _67116 => @lem5139335 _67117 _67115 _67114 _67116 h0). Qed.
Lemma lem5139338 (a : Prop) (b : Prop) : (a -> b) = (term382 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5139339 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term384 _67116 _67117 _67114 _67115) = (term385 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139338 (_67114 = _67116) (term383 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139340 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : term385 _67116 _67117 _67114 _67115.
Proof. exact (EQ_MP (@lem5139339 _67116 _67117 _67114 _67115) (@lem5139336 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139354 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5139355 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5139354 x). Qed.
Lemma lem5139357 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139358 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5139357 (x = x)). Qed.
Lemma lem5139359 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5139358 x) (@lem5139355 x)). Qed.
Lemma lem5139361 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5139362 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5139361 (x' x)). Qed.
Lemma lem5139363 (x' : real -> real) (x : real) : term389 x' x.
Proof. exact (fun h0 : term390 x' x => @lem5139362 x' x). Qed.
Lemma lem5139365 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139366 (x' : real -> real) (x : real) : (term389 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5139365 ((x' x) = (x' x))). Qed.
Lemma lem5139367 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5139366 x' x) (@lem5139363 x' x)). Qed.
Lemma lem5139369 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5138458 s b h1)). Qed.
Lemma lem5139370 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5139369 s b h1). Qed.
Lemma lem5139372 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139373 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5139372 (@IN real b s)). Qed.
Lemma lem5139374 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5139373 b s) (@lem5139370 s b h1)). Qed.
Lemma lem5139376 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5138458 s b h1)). Qed.
Lemma lem5139377 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5139376 s b h1). Qed.
Lemma lem5139379 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139380 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5139379 (@IN real b s)). Qed.
Lemma lem5139381 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5139380 b s) (@lem5139377 s b h1)). Qed.
Lemma lem5139392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139393 (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term459 x' _67094 s) = (term376 s x' _67094).
Proof. exact (@lem5139392 (term162 _67094 s) (term353 x' _67094)). Qed.
Lemma lem5139399 (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term460 s x' _67094) = (term460 s x' _67094).
Proof. exact (eq_refl (term460 s x' _67094)). Qed.
Lemma lem5139400 (s : real -> Prop) (x' : real -> real) (_67094 : real) : ((term376 s x' _67094) = (term459 x' _67094 s)) = ((term376 s x' _67094) = (term376 s x' _67094)).
Proof. exact (MK_COMB (@lem5139399 s x' _67094) (@lem5139393 s x' _67094)). Qed.
Lemma lem5139402 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139403 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139402 Prop x). Qed.
Lemma lem5139404 (s : real -> Prop) (x' : real -> real) (_67094 : real) : ((term376 s x' _67094) = (term376 s x' _67094)) = True.
Proof. exact (@lem5139403 (term376 s x' _67094)). Qed.
Lemma lem5139405 (x' : real -> real) (_67094 : real) (s : real -> Prop) : ((term376 s x' _67094) = (term459 x' _67094 s)) = True.
Proof. exact (TRANS (@lem5139400 s x' _67094) (@lem5139404 s x' _67094)). Qed.
Lemma lem5139406 (x' : real -> real) (_67094 : real) (s : real -> Prop) : True = ((term376 s x' _67094) = (term459 x' _67094 s)).
Proof. exact (SYM (@lem5139405 x' _67094 s)). Qed.
Lemma lem5139407 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term376 s x' _67094) = (term459 x' _67094 s).
Proof. exact (EQ_MP (@lem5139406 x' _67094 s) (@lem0)). Qed.
Lemma lem5139408 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term459 x' _67094 s.
Proof. exact (EQ_MP (@lem5139407 x' _67094 s) (@lem5138824 _67094 b x s x' h1)). Qed.
Lemma lem5139410 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139411 (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term459 x' _67094 s) = (term461 s x' _67094).
Proof. exact (@lem5139410 (term162 _67094 s) (term353 x' _67094)). Qed.
Lemma lem5139413 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139414 (_67094 : real) (s : real -> Prop) : (term462 _67094 s) = (@IN real _67094 s).
Proof. exact (@lem5139413 (@IN real _67094 s)). Qed.
Lemma lem5139415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139416 (_67094 : real) (s : real -> Prop) : (term463 _67094 s) = (term464 _67094 s).
Proof. exact (MK_COMB (@lem5139415) (@lem5139414 _67094 s)). Qed.
Lemma lem5139417 (x' : real -> real) (_67094 : real) : (term353 x' _67094) = (term353 x' _67094).
Proof. exact (eq_refl (term353 x' _67094)). Qed.
Lemma lem5139418 (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term461 s x' _67094) = (term465 s x' _67094).
Proof. exact (MK_COMB (@lem5139416 _67094 s) (@lem5139417 x' _67094)). Qed.
Lemma lem5139419 (s : real -> Prop) (x' : real -> real) (_67094 : real) : (term459 x' _67094 s) = (term465 s x' _67094).
Proof. exact (TRANS (@lem5139411 s x' _67094) (@lem5139418 s x' _67094)). Qed.
Lemma lem5139422 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' _67094.
Proof. exact (EQ_MP (@lem5139419 s x' _67094) (@lem5139408 _67094 b x s x' h1)). Qed.
Lemma lem5139423 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' b.
Proof. exact (@lem5139422 b b x s x' h1). Qed.
Lemma lem5139426 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (@lem5139423 b x s x' h1 (@lem5139381 s b h2)). Qed.
Lemma lem5139427 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term466 x' b.
Proof. exact (fun h0 : term448 x' b => @lem5139426 x x' s b h1 h2). Qed.
Lemma lem5139429 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139430 (x' : real -> real) (b : real) : (term466 x' b) = (term353 x' b).
Proof. exact (@lem5139429 (term448 x' b)). Qed.
Lemma lem5139431 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (EQ_MP (@lem5139430 x' b) (@lem5139427 x x' s b h1 h2)). Qed.
Lemma lem5139433 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139436 (b : real) (_67095 : real) (s : real -> Prop) : (term166 s _67095 b) = (term467 b _67095 s).
Proof. exact (@lem5139433 (real_le _67095 b) (term162 _67095 s)). Qed.
Lemma lem5139439 (_67095 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term467 b _67095 s.
Proof. exact (EQ_MP (@lem5139436 b _67095 s) (@lem5138812 _67095 s b h1)). Qed.
Lemma lem5139440 (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term468 x' b s.
Proof. exact (@lem5139439 (x' b) s b h1). Qed.
Lemma lem5139443 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term391 x' b s.
Proof. exact (@lem5139440 x' s b h2 (@lem5139431 x x' s b h1 h2)). Qed.
Lemma lem5139444 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term392 x' b s.
Proof. exact (fun h0 : term393 x' b s => @lem5139443 x x' s b h1 h2). Qed.
Lemma lem5139446 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139447 (x' : real -> real) (b : real) (s : real -> Prop) : (term392 x' b s) = (term391 x' b s).
Proof. exact (@lem5139446 (term393 x' b s)). Qed.
Lemma lem5139448 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term391 x' b s.
Proof. exact (EQ_MP (@lem5139447 x' b s) (@lem5139444 x x' s b h1 h2)). Qed.
Lemma lem5139454 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139455 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term377 x x' _67094 s) = (term469 x x' _67094 s).
Proof. exact (@lem5139454 ((x' _67094) = x) (term162 _67094 s) (term393 x' _67094 s)). Qed.
Lemma lem5139471 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139472 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term470 x' _67094 s) = (term471 x' _67094 s).
Proof. exact (@lem5139471 (term393 x' _67094 s) (term162 _67094 s)). Qed.
Lemma lem5139478 (x' : real -> real) (_67094 : real) (x : real) : (term398 x' _67094 x) = (term398 x' _67094 x).
Proof. exact (eq_refl (term398 x' _67094 x)). Qed.
Lemma lem5139479 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term469 x x' _67094 s) = (term472 x x' _67094 s).
Proof. exact (MK_COMB (@lem5139478 x' _67094 x) (@lem5139472 x' _67094 s)). Qed.
Lemma lem5139490 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term377 x x' _67094 s) = (term472 x x' _67094 s).
Proof. exact (TRANS (@lem5139455 x x' _67094 s) (@lem5139479 x x' _67094 s)). Qed.
Lemma lem5139491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5139492 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term473 x x' _67094 s) = (term474 x x' _67094 s).
Proof. exact (MK_COMB (@lem5139491) (@lem5139490 x x' _67094 s)). Qed.
Lemma lem5139508 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139509 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term470 x' _67094 s) = (term471 x' _67094 s).
Proof. exact (@lem5139508 (term393 x' _67094 s) (term162 _67094 s)). Qed.
Lemma lem5139515 (x' : real -> real) (_67094 : real) (x : real) : (term398 x' _67094 x) = (term398 x' _67094 x).
Proof. exact (eq_refl (term398 x' _67094 x)). Qed.
Lemma lem5139516 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term469 x x' _67094 s) = (term472 x x' _67094 s).
Proof. exact (MK_COMB (@lem5139515 x' _67094 x) (@lem5139509 x' _67094 s)). Qed.
Lemma lem5139527 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : ((term377 x x' _67094 s) = (term469 x x' _67094 s)) = ((term472 x x' _67094 s) = (term472 x x' _67094 s)).
Proof. exact (MK_COMB (@lem5139492 x x' _67094 s) (@lem5139516 x x' _67094 s)). Qed.
Lemma lem5139529 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139530 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139529 Prop x). Qed.
Lemma lem5139531 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : ((term472 x x' _67094 s) = (term472 x x' _67094 s)) = True.
Proof. exact (@lem5139530 (term472 x x' _67094 s)). Qed.
Lemma lem5139532 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : ((term377 x x' _67094 s) = (term469 x x' _67094 s)) = True.
Proof. exact (TRANS (@lem5139527 x x' _67094 s) (@lem5139531 x x' _67094 s)). Qed.
Lemma lem5139533 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : True = ((term377 x x' _67094 s) = (term469 x x' _67094 s)).
Proof. exact (SYM (@lem5139532 x x' _67094 s)). Qed.
Lemma lem5139534 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term377 x x' _67094 s) = (term469 x x' _67094 s).
Proof. exact (EQ_MP (@lem5139533 x x' _67094 s) (@lem0)). Qed.
Lemma lem5139535 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term469 x x' _67094 s.
Proof. exact (EQ_MP (@lem5139534 x x' _67094 s) (@lem5138844 _67094 b x s x' h1)). Qed.
Lemma lem5139537 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139538 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : (term469 x x' _67094 s) = (term475 s x' _67094 x).
Proof. exact (@lem5139537 (term470 x' _67094 s) ((x' _67094) = x)). Qed.
Lemma lem5139540 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139541 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term476 x' _67094 s) = (term477 x' _67094 s).
Proof. exact (@lem5139540 (term162 _67094 s) (term393 x' _67094 s)). Qed.
Lemma lem5139543 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139544 (_67094 : real) (s : real -> Prop) : (term462 _67094 s) = (@IN real _67094 s).
Proof. exact (@lem5139543 (@IN real _67094 s)). Qed.
Lemma lem5139545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139546 (_67094 : real) (s : real -> Prop) : (term478 _67094 s) = (term152 _67094 s).
Proof. exact (MK_COMB (@lem5139545) (@lem5139544 _67094 s)). Qed.
Lemma lem5139547 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term391 x' _67094 s) = (term391 x' _67094 s).
Proof. exact (eq_refl (term391 x' _67094 s)). Qed.
Lemma lem5139548 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term477 x' _67094 s) = (term479 x' _67094 s).
Proof. exact (MK_COMB (@lem5139546 _67094 s) (@lem5139547 x' _67094 s)). Qed.
Lemma lem5139549 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term476 x' _67094 s) = (term479 x' _67094 s).
Proof. exact (TRANS (@lem5139541 x' _67094 s) (@lem5139548 x' _67094 s)). Qed.
Lemma lem5139550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139551 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term480 x' _67094 s) = (term481 x' _67094 s).
Proof. exact (MK_COMB (@lem5139550) (@lem5139549 x' _67094 s)). Qed.
Lemma lem5139552 (x' : real -> real) (_67094 : real) (x : real) : ((x' _67094) = x) = ((x' _67094) = x).
Proof. exact (eq_refl ((x' _67094) = x)). Qed.
Lemma lem5139553 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : (term475 s x' _67094 x) = (term482 s x' _67094 x).
Proof. exact (MK_COMB (@lem5139551 x' _67094 s) (@lem5139552 x' _67094 x)). Qed.
Lemma lem5139554 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : (term469 x x' _67094 s) = (term482 s x' _67094 x).
Proof. exact (TRANS (@lem5139538 s x' _67094 x) (@lem5139553 s x' _67094 x)). Qed.
Lemma lem5139556 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term479 x' b s.
Proof. exact (conj (@lem5139374 s b h2) (@lem5139448 x x' s b h1 h2)). Qed.
Lemma lem5139558 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term482 s x' _67094 x.
Proof. exact (EQ_MP (@lem5139554 s x' _67094 x) (@lem5139535 _67094 b x s x' h1)). Qed.
Lemma lem5139559 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term482 s x' b x.
Proof. exact (@lem5139558 b b x s x' h1). Qed.
Lemma lem5139562 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : (x' b) = x.
Proof. exact (@lem5139559 b x s x' h1 (@lem5139556 x x' s b h1 h2)). Qed.
Lemma lem5139563 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term483 x' b x.
Proof. exact (fun h0 : term484 x' b x => @lem5139562 x x' s b h1 h2). Qed.
Lemma lem5139565 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139566 (x' : real -> real) (b : real) (x : real) : (term483 x' b x) = ((x' b) = x).
Proof. exact (@lem5139565 ((x' b) = x)). Qed.
Lemma lem5139567 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : (x' b) = x.
Proof. exact (EQ_MP (@lem5139566 x' b x) (@lem5139563 x x' s b h1 h2)). Qed.
Lemma lem5139569 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5139570 (x : real) : term386 x.
Proof. exact (fun h0 : term387 x => @lem5139569 x). Qed.
Lemma lem5139572 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139573 (x : real) : (term386 x) = (x = x).
Proof. exact (@lem5139572 (x = x)). Qed.
Lemma lem5139574 (x : real) : x = x.
Proof. exact (EQ_MP (@lem5139573 x) (@lem5139570 x)). Qed.
Lemma lem5139576 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5139577 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (@lem5139576 (x' x)). Qed.
Lemma lem5139578 (x' : real -> real) (x : real) : term389 x' x.
Proof. exact (fun h0 : term390 x' x => @lem5139577 x' x). Qed.
Lemma lem5139580 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139581 (x' : real -> real) (x : real) : (term389 x' x) = ((x' x) = (x' x)).
Proof. exact (@lem5139580 ((x' x) = (x' x))). Qed.
Lemma lem5139582 (x' : real -> real) (x : real) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem5139581 x' x) (@lem5139578 x' x)). Qed.
Lemma lem5139585 (x' : real -> real) (x : real) (h1 : term353 x' x) : term353 x' x.
Proof. exact (h1). Qed.
Lemma lem5139586 (x' : real -> real) (x : real) (h1 : term353 x' x) : term466 x' x.
Proof. exact (fun h0 : term448 x' x => @lem5139585 x' x h1). Qed.
Lemma lem5139588 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139589 (x' : real -> real) (x : real) : (term466 x' x) = (term353 x' x).
Proof. exact (@lem5139588 (term448 x' x)). Qed.
Lemma lem5139590 (x' : real -> real) (x : real) (h1 : term353 x' x) : term353 x' x.
Proof. exact (EQ_MP (@lem5139589 x' x) (@lem5139586 x' x h1)). Qed.
Lemma lem5139593 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (h1). Qed.
Lemma lem5139594 (x' : real -> real) (x : real) (h1 : term420 x' x) : term421 x' x.
Proof. exact (fun h0 : term422 x' x => @lem5139593 x' x h1). Qed.
Lemma lem5139596 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139597 (x' : real -> real) (x : real) : (term421 x' x) = (term420 x' x).
Proof. exact (@lem5139596 (term422 x' x)). Qed.
Lemma lem5139598 (x' : real -> real) (x : real) (h1 : term420 x' x) : term420 x' x.
Proof. exact (EQ_MP (@lem5139597 x' x) (@lem5139594 x' x h1)). Qed.
Lemma lem5139609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139610 (_67093 : real) (_67092 : real) : (term138 _67092 _67093) = (term138 _67093 _67092).
Proof. exact (@lem5139609 (real_le _67092 _67093) (real_le _67093 _67092)). Qed.
Lemma lem5139616 (_67093 : real) (_67092 : real) : (term423 _67093 _67092) = (term423 _67093 _67092).
Proof. exact (eq_refl (term423 _67093 _67092)). Qed.
Lemma lem5139617 (_67093 : real) (_67092 : real) : ((term138 _67093 _67092) = (term138 _67092 _67093)) = ((term138 _67093 _67092) = (term138 _67093 _67092)).
Proof. exact (MK_COMB (@lem5139616 _67093 _67092) (@lem5139610 _67093 _67092)). Qed.
Lemma lem5139619 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139620 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139619 Prop x). Qed.
Lemma lem5139621 (_67093 : real) (_67092 : real) : ((term138 _67093 _67092) = (term138 _67093 _67092)) = True.
Proof. exact (@lem5139620 (term138 _67093 _67092)). Qed.
Lemma lem5139622 (_67092 : real) (_67093 : real) : ((term138 _67093 _67092) = (term138 _67092 _67093)) = True.
Proof. exact (TRANS (@lem5139617 _67093 _67092) (@lem5139621 _67093 _67092)). Qed.
Lemma lem5139623 (_67092 : real) (_67093 : real) : True = ((term138 _67093 _67092) = (term138 _67092 _67093)).
Proof. exact (SYM (@lem5139622 _67092 _67093)). Qed.
Lemma lem5139624 (_67092 : real) (_67093 : real) : (term138 _67093 _67092) = (term138 _67092 _67093).
Proof. exact (EQ_MP (@lem5139623 _67092 _67093) (@lem0)). Qed.
Lemma lem5139625 (_67092 : real) (_67093 : real) (h1 : term132) : term138 _67092 _67093.
Proof. exact (EQ_MP (@lem5139624 _67092 _67093) (@lem5138800 _67093 _67092 h1)). Qed.
Lemma lem5139627 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139630 (_67093 : real) (_67092 : real) : (term138 _67092 _67093) = (term424 _67093 _67092).
Proof. exact (@lem5139627 (real_le _67092 _67093) (real_le _67093 _67092)). Qed.
Lemma lem5139633 (_67093 : real) (_67092 : real) (h1 : term132) : term424 _67093 _67092.
Proof. exact (EQ_MP (@lem5139630 _67093 _67092) (@lem5139625 _67092 _67093 h1)). Qed.
Lemma lem5139634 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (@lem5139633 (x' x) (x' x) h1). Qed.
Lemma lem5139637 (x' : real -> real) (x : real) (h1 : term132) (h2 : term420 x' x) : term422 x' x.
Proof. exact (@lem5139634 x' x h1 (@lem5139598 x' x h2)). Qed.
Lemma lem5139638 (x' : real -> real) (x : real) (h1 : term132) : term425 x' x.
Proof. exact (fun h0 : term420 x' x => @lem5139637 x' x h1 h0). Qed.
Lemma lem5139640 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139641 (x' : real -> real) (x : real) : (term425 x' x) = (term422 x' x).
Proof. exact (@lem5139640 (term422 x' x)). Qed.
Lemma lem5139642 (x' : real -> real) (x : real) (h1 : term132) : term422 x' x.
Proof. exact (EQ_MP (@lem5139641 x' x) (@lem5139638 x' x h1)). Qed.
Lemma lem5139660 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139661 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term383 _67116 _67117 _67114 _67115) = (term426 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139660 (real_le _67116 _67117) (term356 _67115 _67117) (term375 _67114 _67115)). Qed.
Lemma lem5139679 (_67114 : real) (_67116 : real) : (term427 _67114 _67116) = (term427 _67114 _67116).
Proof. exact (eq_refl (term427 _67114 _67116)). Qed.
Lemma lem5139680 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term428 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139679 _67114 _67116) (@lem5139661 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139684 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139685 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term428 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139684 (real_le _67116 _67117) (term356 _67114 _67116) (term430 _67117 _67114 _67115)). Qed.
Lemma lem5139715 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5139680 _67116 _67117 _67114 _67115) (@lem5139685 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5139717 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term431 _67116 _67117 _67114 _67115) = (term432 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139716) (@lem5139715 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139721 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139722 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term485 _67116 _67117 _67114 _67115) = (term385 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139721 (term356 _67114 _67116) (term356 _67115 _67117) (term380 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139738 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139739 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term383 _67116 _67117 _67114 _67115) = (term426 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139738 (real_le _67116 _67117) (term356 _67115 _67117) (term375 _67114 _67115)). Qed.
Lemma lem5139757 (_67114 : real) (_67116 : real) : (term427 _67114 _67116) = (term427 _67114 _67116).
Proof. exact (eq_refl (term427 _67114 _67116)). Qed.
Lemma lem5139758 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term428 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139757 _67114 _67116) (@lem5139739 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139762 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139763 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term428 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139762 (real_le _67116 _67117) (term356 _67114 _67116) (term430 _67117 _67114 _67115)). Qed.
Lemma lem5139793 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5139758 _67116 _67117 _67114 _67115) (@lem5139763 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139794 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term485 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5139722 _67116 _67117 _67114 _67115) (@lem5139793 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139795 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term385 _67116 _67117 _67114 _67115) = (term485 _67116 _67117 _67114 _67115)) = ((term429 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)).
Proof. exact (MK_COMB (@lem5139717 _67116 _67117 _67114 _67115) (@lem5139794 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139797 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139798 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139797 Prop x). Qed.
Lemma lem5139799 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term429 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)) = True.
Proof. exact (@lem5139798 (term429 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139800 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term385 _67116 _67117 _67114 _67115) = (term485 _67116 _67117 _67114 _67115)) = True.
Proof. exact (TRANS (@lem5139795 _67116 _67117 _67114 _67115) (@lem5139799 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139801 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : True = ((term385 _67116 _67117 _67114 _67115) = (term485 _67116 _67117 _67114 _67115)).
Proof. exact (SYM (@lem5139800 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139802 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term485 _67116 _67117 _67114 _67115).
Proof. exact (EQ_MP (@lem5139801 _67116 _67117 _67114 _67115) (@lem0)). Qed.
Lemma lem5139803 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : term485 _67116 _67117 _67114 _67115.
Proof. exact (EQ_MP (@lem5139802 _67116 _67117 _67114 _67115) (@lem5139340 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139805 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139806 (_67116 : real) (_67114 : real) (_67115 : real) (_67117 : real) : (term485 _67116 _67117 _67114 _67115) = (term486 _67116 _67114 _67115 _67117).
Proof. exact (@lem5139805 (term487 _67116 _67117 _67114 _67115) (term356 _67115 _67117)). Qed.
Lemma lem5139808 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139809 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term488 _67116 _67117 _67114 _67115) = (term489 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139808 (term356 _67114 _67116) (term380 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139811 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139812 (_67114 : real) (_67116 : real) : (term409 _67114 _67116) = (_67114 = _67116).
Proof. exact (@lem5139811 (_67114 = _67116)). Qed.
Lemma lem5139813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139814 (_67114 : real) (_67116 : real) : (term410 _67114 _67116) = (term411 _67114 _67116).
Proof. exact (MK_COMB (@lem5139813) (@lem5139812 _67114 _67116)). Qed.
Lemma lem5139816 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139817 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term490 _67116 _67117 _67114 _67115) = (term491 _67116 _67117 _67114 _67115).
Proof. exact (@lem5139816 (real_le _67116 _67117) (term375 _67114 _67115)). Qed.
Lemma lem5139819 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139820 (_67114 : real) (_67115 : real) : (term439 _67114 _67115) = (real_le _67114 _67115).
Proof. exact (@lem5139819 (real_le _67114 _67115)). Qed.
Lemma lem5139821 (_67116 : real) (_67117 : real) : (term492 _67116 _67117) = (term492 _67116 _67117).
Proof. exact (eq_refl (term492 _67116 _67117)). Qed.
Lemma lem5139822 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term491 _67116 _67117 _67114 _67115) = (term493 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139821 _67116 _67117) (@lem5139820 _67114 _67115)). Qed.
Lemma lem5139823 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term490 _67116 _67117 _67114 _67115) = (term493 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5139817 _67116 _67117 _67114 _67115) (@lem5139822 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139824 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term489 _67116 _67117 _67114 _67115) = (term494 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139814 _67114 _67116) (@lem5139823 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139825 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term488 _67116 _67117 _67114 _67115) = (term494 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5139809 _67116 _67117 _67114 _67115) (@lem5139824 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139827 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term495 _67116 _67117 _67114 _67115) = (term496 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5139826) (@lem5139825 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139828 (_67115 : real) (_67117 : real) : (term356 _67115 _67117) = (term356 _67115 _67117).
Proof. exact (eq_refl (term356 _67115 _67117)). Qed.
Lemma lem5139829 (_67116 : real) (_67114 : real) (_67115 : real) (_67117 : real) : (term486 _67116 _67114 _67115 _67117) = (term497 _67116 _67114 _67115 _67117).
Proof. exact (MK_COMB (@lem5139827 _67116 _67117 _67114 _67115) (@lem5139828 _67115 _67117)). Qed.
Lemma lem5139830 (_67116 : real) (_67114 : real) (_67115 : real) (_67117 : real) : (term485 _67116 _67117 _67114 _67115) = (term497 _67116 _67114 _67115 _67117).
Proof. exact (TRANS (@lem5139806 _67116 _67114 _67115 _67117) (@lem5139829 _67116 _67114 _67115 _67117)). Qed.
Lemma lem5139832 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term498 x' x.
Proof. exact (conj (@lem5139590 x' x h2) (@lem5139642 x' x h1)). Qed.
Lemma lem5139833 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term499 x' x.
Proof. exact (conj (@lem5139582 x' x) (@lem5139832 x' x h1 h2)). Qed.
Lemma lem5139835 (_67116 : real) (_67114 : real) (_67115 : real) (_67117 : real) : term497 _67116 _67114 _67115 _67117.
Proof. exact (EQ_MP (@lem5139830 _67116 _67114 _67115 _67117) (@lem5139803 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5139836 (x' : real -> real) (x : real) : term500 x' x.
Proof. exact (@lem5139835 (x' x) (x' x) (x' x) x). Qed.
Lemma lem5139839 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term419 x' x.
Proof. exact (@lem5139836 x' x (@lem5139833 x' x h1 h2)). Qed.
Lemma lem5139840 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term501 x' x.
Proof. exact (fun h0 : (x' x) = x => @lem5139839 x' x h1 h2). Qed.
Lemma lem5139842 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5139843 (x' : real -> real) (x : real) : (term501 x' x) = (term419 x' x).
Proof. exact (@lem5139842 ((x' x) = x)). Qed.
Lemma lem5139844 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term419 x' x.
Proof. exact (EQ_MP (@lem5139843 x' x) (@lem5139840 x' x h1 h2)). Qed.
Lemma lem5139850 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139851 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term373 x x' _67094 s) = (term395 x x' _67094 s).
Proof. exact (@lem5139850 ((x' _67094) = x) (term356 _67094 x) (term393 x' _67094 s)). Qed.
Lemma lem5139867 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139868 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term396 x x' _67094 s) = (term397 x' s _67094 x).
Proof. exact (@lem5139867 (term393 x' _67094 s) (term356 _67094 x)). Qed.
Lemma lem5139876 (x' : real -> real) (_67094 : real) (x : real) : (term398 x' _67094 x) = (term398 x' _67094 x).
Proof. exact (eq_refl (term398 x' _67094 x)). Qed.
Lemma lem5139877 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term395 x x' _67094 s) = (term399 x' s _67094 x).
Proof. exact (MK_COMB (@lem5139876 x' _67094 x) (@lem5139868 x' s _67094 x)). Qed.
Lemma lem5139888 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term373 x x' _67094 s) = (term399 x' s _67094 x).
Proof. exact (TRANS (@lem5139851 x x' _67094 s) (@lem5139877 x' s _67094 x)). Qed.
Lemma lem5139889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5139890 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term400 x x' _67094 s) = (term401 x' s _67094 x).
Proof. exact (MK_COMB (@lem5139889) (@lem5139888 x' s _67094 x)). Qed.
Lemma lem5139904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139905 (x' : real -> real) (_67094 : real) (x : real) : (term502 x' _67094 x) = (term503 x' _67094 x).
Proof. exact (@lem5139904 ((x' _67094) = x) (term356 _67094 x)). Qed.
Lemma lem5139915 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term504 x' _67094 s) = (term504 x' _67094 s).
Proof. exact (eq_refl (term504 x' _67094 s)). Qed.
Lemma lem5139916 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : (term505 s x' _67094 x) = (term506 s x' _67094 x).
Proof. exact (MK_COMB (@lem5139915 x' _67094 s) (@lem5139905 x' _67094 x)). Qed.
Lemma lem5139920 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5139921 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term506 s x' _67094 x) = (term399 x' s _67094 x).
Proof. exact (@lem5139920 ((x' _67094) = x) (term393 x' _67094 s) (term356 _67094 x)). Qed.
Lemma lem5139941 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : (term505 s x' _67094 x) = (term399 x' s _67094 x).
Proof. exact (TRANS (@lem5139916 s x' _67094 x) (@lem5139921 x' s _67094 x)). Qed.
Lemma lem5139942 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : ((term373 x x' _67094 s) = (term505 s x' _67094 x)) = ((term399 x' s _67094 x) = (term399 x' s _67094 x)).
Proof. exact (MK_COMB (@lem5139890 x' s _67094 x) (@lem5139941 x' s _67094 x)). Qed.
Lemma lem5139944 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5139945 (x : Prop) : (x = x) = True.
Proof. exact (@lem5139944 Prop x). Qed.
Lemma lem5139946 (x' : real -> real) (s : real -> Prop) (_67094 : real) (x : real) : ((term399 x' s _67094 x) = (term399 x' s _67094 x)) = True.
Proof. exact (@lem5139945 (term399 x' s _67094 x)). Qed.
Lemma lem5139947 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : ((term373 x x' _67094 s) = (term505 s x' _67094 x)) = True.
Proof. exact (TRANS (@lem5139942 x' s _67094 x) (@lem5139946 x' s _67094 x)). Qed.
Lemma lem5139948 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : True = ((term373 x x' _67094 s) = (term505 s x' _67094 x)).
Proof. exact (SYM (@lem5139947 s x' _67094 x)). Qed.
Lemma lem5139949 (s : real -> Prop) (x' : real -> real) (_67094 : real) (x : real) : (term373 x x' _67094 s) = (term505 s x' _67094 x).
Proof. exact (EQ_MP (@lem5139948 s x' _67094 x) (@lem0)). Qed.
Lemma lem5139950 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term505 s x' _67094 x.
Proof. exact (EQ_MP (@lem5139949 s x' _67094 x) (@lem5138834 _67094 b x s x' h1)). Qed.
Lemma lem5139952 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5139953 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term505 s x' _67094 x) = (term507 x x' _67094 s).
Proof. exact (@lem5139952 (term502 x' _67094 x) (term393 x' _67094 s)). Qed.
Lemma lem5139955 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5139956 (x' : real -> real) (_67094 : real) (x : real) : (term508 x' _67094 x) = (term509 x' _67094 x).
Proof. exact (@lem5139955 (term356 _67094 x) ((x' _67094) = x)). Qed.
Lemma lem5139958 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5139959 (_67094 : real) (x : real) : (term409 _67094 x) = (_67094 = x).
Proof. exact (@lem5139958 (_67094 = x)). Qed.
Lemma lem5139960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5139961 (_67094 : real) (x : real) : (term410 _67094 x) = (term411 _67094 x).
Proof. exact (MK_COMB (@lem5139960) (@lem5139959 _67094 x)). Qed.
Lemma lem5139962 (x' : real -> real) (_67094 : real) (x : real) : (term484 x' _67094 x) = (term484 x' _67094 x).
Proof. exact (eq_refl (term484 x' _67094 x)). Qed.
Lemma lem5139963 (x' : real -> real) (_67094 : real) (x : real) : (term509 x' _67094 x) = (term510 x' _67094 x).
Proof. exact (MK_COMB (@lem5139961 _67094 x) (@lem5139962 x' _67094 x)). Qed.
Lemma lem5139964 (x' : real -> real) (_67094 : real) (x : real) : (term508 x' _67094 x) = (term510 x' _67094 x).
Proof. exact (TRANS (@lem5139956 x' _67094 x) (@lem5139963 x' _67094 x)). Qed.
Lemma lem5139965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5139966 (x' : real -> real) (_67094 : real) (x : real) : (term511 x' _67094 x) = (term512 x' _67094 x).
Proof. exact (MK_COMB (@lem5139965) (@lem5139964 x' _67094 x)). Qed.
Lemma lem5139967 (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term393 x' _67094 s) = (term393 x' _67094 s).
Proof. exact (eq_refl (term393 x' _67094 s)). Qed.
Lemma lem5139968 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term507 x x' _67094 s) = (term513 x x' _67094 s).
Proof. exact (MK_COMB (@lem5139966 x' _67094 x) (@lem5139967 x' _67094 s)). Qed.
Lemma lem5139969 (x : real) (x' : real -> real) (_67094 : real) (s : real -> Prop) : (term505 s x' _67094 x) = (term513 x x' _67094 s).
Proof. exact (TRANS (@lem5139953 x x' _67094 s) (@lem5139968 x x' _67094 s)). Qed.
Lemma lem5139971 (x' : real -> real) (x : real) (h1 : term132) (h2 : term353 x' x) : term514 x' x.
Proof. exact (conj (@lem5139574 x) (@lem5139844 x' x h1 h2)). Qed.
Lemma lem5139973 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term513 x x' _67094 s.
Proof. exact (EQ_MP (@lem5139969 x x' _67094 s) (@lem5139950 _67094 b x s x' h1)). Qed.
Lemma lem5139974 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term515 x' x s.
Proof. exact (@lem5139973 x b x s x' h1). Qed.
Lemma lem5139977 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term393 x' x s.
Proof. exact (@lem5139974 b x s x' h3 (@lem5139971 x' x h1 h2)). Qed.
Lemma lem5139978 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term516 x' x s.
Proof. exact (fun h0 : term391 x' x s => @lem5139977 b x s x' h1 h2 h3). Qed.
Lemma lem5139980 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5139981 (x' : real -> real) (x : real) (s : real -> Prop) : (term516 x' x s) = (term393 x' x s).
Proof. exact (@lem5139980 (term393 x' x s)). Qed.
Lemma lem5139982 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') : term393 x' x s.
Proof. exact (EQ_MP (@lem5139981 x' x s) (@lem5139978 b x s x' h1 h2 h3)). Qed.
Lemma lem5139988 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5139989 (b : real) (_67095 : real) (s : real -> Prop) : (term166 s _67095 b) = (term517 b _67095 s).
Proof. exact (@lem5139988 (real_le _67095 b) (term162 _67095 s)). Qed.
Lemma lem5139995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5139996 (b : real) (_67095 : real) (s : real -> Prop) : (term518 s _67095 b) = (term519 b _67095 s).
Proof. exact (MK_COMB (@lem5139995) (@lem5139989 b _67095 s)). Qed.
Lemma lem5140002 (b : real) (_67095 : real) (s : real -> Prop) : (term517 b _67095 s) = (term517 b _67095 s).
Proof. exact (eq_refl (term517 b _67095 s)). Qed.
Lemma lem5140003 (b : real) (_67095 : real) (s : real -> Prop) : ((term166 s _67095 b) = (term517 b _67095 s)) = ((term517 b _67095 s) = (term517 b _67095 s)).
Proof. exact (MK_COMB (@lem5139996 b _67095 s) (@lem5140002 b _67095 s)). Qed.
Lemma lem5140005 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5140006 (x : Prop) : (x = x) = True.
Proof. exact (@lem5140005 Prop x). Qed.
Lemma lem5140007 (b : real) (_67095 : real) (s : real -> Prop) : ((term517 b _67095 s) = (term517 b _67095 s)) = True.
Proof. exact (@lem5140006 (term517 b _67095 s)). Qed.
Lemma lem5140008 (b : real) (_67095 : real) (s : real -> Prop) : ((term166 s _67095 b) = (term517 b _67095 s)) = True.
Proof. exact (TRANS (@lem5140003 b _67095 s) (@lem5140007 b _67095 s)). Qed.
Lemma lem5140009 (b : real) (_67095 : real) (s : real -> Prop) : True = ((term166 s _67095 b) = (term517 b _67095 s)).
Proof. exact (SYM (@lem5140008 b _67095 s)). Qed.
Lemma lem5140010 (b : real) (_67095 : real) (s : real -> Prop) : (term166 s _67095 b) = (term517 b _67095 s).
Proof. exact (EQ_MP (@lem5140009 b _67095 s) (@lem0)). Qed.
Lemma lem5140011 (_67095 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term517 b _67095 s.
Proof. exact (EQ_MP (@lem5140010 b _67095 s) (@lem5138812 _67095 s b h1)). Qed.
Lemma lem5140013 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5140014 (s : real -> Prop) (_67095 : real) (b : real) : (term517 b _67095 s) = (term520 s _67095 b).
Proof. exact (@lem5140013 (term162 _67095 s) (real_le _67095 b)). Qed.
Lemma lem5140016 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5140017 (_67095 : real) (s : real -> Prop) : (term462 _67095 s) = (@IN real _67095 s).
Proof. exact (@lem5140016 (@IN real _67095 s)). Qed.
Lemma lem5140018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140019 (_67095 : real) (s : real -> Prop) : (term463 _67095 s) = (term464 _67095 s).
Proof. exact (MK_COMB (@lem5140018) (@lem5140017 _67095 s)). Qed.
Lemma lem5140020 (_67095 : real) (b : real) : (real_le _67095 b) = (real_le _67095 b).
Proof. exact (eq_refl (real_le _67095 b)). Qed.
Lemma lem5140021 (s : real -> Prop) (_67095 : real) (b : real) : (term520 s _67095 b) = (term149 s _67095 b).
Proof. exact (MK_COMB (@lem5140019 _67095 s) (@lem5140020 _67095 b)). Qed.
Lemma lem5140022 (s : real -> Prop) (_67095 : real) (b : real) : (term517 b _67095 s) = (term149 s _67095 b).
Proof. exact (TRANS (@lem5140014 s _67095 b) (@lem5140021 s _67095 b)). Qed.
Lemma lem5140025 (_67095 : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term149 s _67095 b.
Proof. exact (EQ_MP (@lem5140022 s _67095 b) (@lem5140011 _67095 s b h1)). Qed.
Lemma lem5140026 (x' : real -> real) (x : real) (s : real -> Prop) (b : real) (h1 : term169 s b) : term521 s x' x b.
Proof. exact (@lem5140025 (x' x) s b h1). Qed.
Lemma lem5140029 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term522 x' x b.
Proof. exact (@lem5140026 x' x s b h4 (@lem5139982 b x s x' h1 h2 h3)). Qed.
Lemma lem5140030 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term523 x' x b.
Proof. exact (fun h0 : term524 x' x b => @lem5140029 x x' s b h1 h2 h3 h4). Qed.
Lemma lem5140032 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5140033 (x' : real -> real) (x : real) (b : real) : (term523 x' x b) = (term522 x' x b).
Proof. exact (@lem5140032 (term522 x' x b)). Qed.
Lemma lem5140034 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term522 x' x b.
Proof. exact (EQ_MP (@lem5140033 x' x b) (@lem5140030 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5140036 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (proj1 (@lem5138458 s b h1)). Qed.
Lemma lem5140037 (s : real -> Prop) (b : real) (h1 : term169 s b) : term458 b s.
Proof. exact (fun h0 : term162 b s => @lem5140036 s b h1). Qed.
Lemma lem5140039 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5140040 (b : real) (s : real -> Prop) : (term458 b s) = (@IN real b s).
Proof. exact (@lem5140039 (@IN real b s)). Qed.
Lemma lem5140041 (s : real -> Prop) (b : real) (h1 : term169 s b) : @IN real b s.
Proof. exact (EQ_MP (@lem5140040 b s) (@lem5140037 s b h1)). Qed.
Lemma lem5140043 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' _67094.
Proof. exact (EQ_MP (@lem5139419 s x' _67094) (@lem5139408 _67094 b x s x' h1)). Qed.
Lemma lem5140044 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term465 s x' b.
Proof. exact (@lem5140043 b b x s x' h1). Qed.
Lemma lem5140047 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (@lem5140044 b x s x' h1 (@lem5140041 s b h2)). Qed.
Lemma lem5140048 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term466 x' b.
Proof. exact (fun h0 : term448 x' b => @lem5140047 x x' s b h1 h2). Qed.
Lemma lem5140050 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5140051 (x' : real -> real) (b : real) : (term466 x' b) = (term353 x' b).
Proof. exact (@lem5140050 (term448 x' b)). Qed.
Lemma lem5140052 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term328 b x s x') (h2 : term169 s b) : term353 x' b.
Proof. exact (EQ_MP (@lem5140051 x' b) (@lem5140048 x x' s b h1 h2)). Qed.
Lemma lem5140054 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5140055 (_67091 : real) (_67089 : real) (_67090 : real) : (term374 _67090 _67089 _67091) = (term525 _67091 _67089 _67090).
Proof. exact (@lem5140054 (term526 _67090 _67089 _67091) (term375 _67089 _67090)). Qed.
Lemma lem5140057 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5140058 (_67090 : real) (_67089 : real) (_67091 : real) : (term527 _67090 _67089 _67091) = (term528 _67090 _67089 _67091).
Proof. exact (@lem5140057 (term375 _67090 _67091) (real_le _67089 _67091)). Qed.
Lemma lem5140060 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5140061 (_67090 : real) (_67091 : real) : (term439 _67090 _67091) = (real_le _67090 _67091).
Proof. exact (@lem5140060 (real_le _67090 _67091)). Qed.
Lemma lem5140062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5140063 (_67090 : real) (_67091 : real) : (term529 _67090 _67091) = (term530 _67090 _67091).
Proof. exact (MK_COMB (@lem5140062) (@lem5140061 _67090 _67091)). Qed.
Lemma lem5140064 (_67089 : real) (_67091 : real) : (term375 _67089 _67091) = (term375 _67089 _67091).
Proof. exact (eq_refl (term375 _67089 _67091)). Qed.
Lemma lem5140065 (_67090 : real) (_67089 : real) (_67091 : real) : (term528 _67090 _67089 _67091) = (term531 _67090 _67089 _67091).
Proof. exact (MK_COMB (@lem5140063 _67090 _67091) (@lem5140064 _67089 _67091)). Qed.
Lemma lem5140066 (_67090 : real) (_67089 : real) (_67091 : real) : (term527 _67090 _67089 _67091) = (term531 _67090 _67089 _67091).
Proof. exact (TRANS (@lem5140058 _67090 _67089 _67091) (@lem5140065 _67090 _67089 _67091)). Qed.
Lemma lem5140067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140068 (_67090 : real) (_67089 : real) (_67091 : real) : (term532 _67090 _67089 _67091) = (term533 _67090 _67089 _67091).
Proof. exact (MK_COMB (@lem5140067) (@lem5140066 _67090 _67089 _67091)). Qed.
Lemma lem5140069 (_67089 : real) (_67090 : real) : (term375 _67089 _67090) = (term375 _67089 _67090).
Proof. exact (eq_refl (term375 _67089 _67090)). Qed.
Lemma lem5140070 (_67091 : real) (_67089 : real) (_67090 : real) : (term525 _67091 _67089 _67090) = (term534 _67091 _67089 _67090).
Proof. exact (MK_COMB (@lem5140068 _67090 _67089 _67091) (@lem5140069 _67089 _67090)). Qed.
Lemma lem5140071 (_67091 : real) (_67089 : real) (_67090 : real) : (term374 _67090 _67089 _67091) = (term534 _67091 _67089 _67090).
Proof. exact (TRANS (@lem5140055 _67091 _67089 _67090) (@lem5140070 _67091 _67089 _67090)). Qed.
Lemma lem5140073 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term132) (h2 : term353 x' x) (h3 : term328 b x s x') (h4 : term169 s b) : term535 x x' b.
Proof. exact (conj (@lem5140034 x x' s b h1 h2 h3 h4) (@lem5140052 x x' s b h3 h4)). Qed.
Lemma lem5140075 (_67091 : real) (_67089 : real) (_67090 : real) (h1 : term148) : term534 _67091 _67089 _67090.
Proof. exact (EQ_MP (@lem5140071 _67091 _67089 _67090) (@lem5138794 _67090 _67089 _67091 h1)). Qed.
Lemma lem5140076 (b : real) (x' : real -> real) (x : real) (h1 : term148) : term536 b x' x.
Proof. exact (@lem5140075 b (x' b) (x' x) h1). Qed.
Lemma lem5140079 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term537 b x' x.
Proof. exact (@lem5140076 b x' x h1 (@lem5140073 x x' s b h2 h3 h4 h5)). Qed.
Lemma lem5140080 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term538 b x' x.
Proof. exact (fun h0 : term539 b x' x => @lem5140079 x x' s b h1 h2 h3 h4 h5). Qed.
Lemma lem5140082 (p : Prop) : (term394 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5140083 (b : real) (x' : real -> real) (x : real) : (term538 b x' x) = (term537 b x' x).
Proof. exact (@lem5140082 (term539 b x' x)). Qed.
Lemma lem5140084 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term537 b x' x.
Proof. exact (EQ_MP (@lem5140083 b x' x) (@lem5140080 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140086 (_67093 : real) (_67092 : real) (h1 : term132) : term424 _67093 _67092.
Proof. exact (EQ_MP (@lem5139630 _67093 _67092) (@lem5139625 _67092 _67093 h1)). Qed.
Lemma lem5140087 (x : real) (x' : real -> real) (b : real) (h1 : term132) : term540 x x' b.
Proof. exact (@lem5140086 (x' x) (x' b) h1). Qed.
Lemma lem5140090 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term539 x x' b.
Proof. exact (@lem5140087 x x' b h2 (@lem5140084 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140091 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term541 x x' b.
Proof. exact (fun h0 : term537 x x' b => @lem5140090 x x' s b h1 h2 h3 h4 h5). Qed.
Lemma lem5140093 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5140094 (x : real) (x' : real -> real) (b : real) : (term541 x x' b) = (term539 x x' b).
Proof. exact (@lem5140093 (term539 x x' b)). Qed.
Lemma lem5140095 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term539 x x' b.
Proof. exact (EQ_MP (@lem5140094 x x' b) (@lem5140091 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140113 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5140114 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term383 _67116 _67117 _67114 _67115) = (term426 _67116 _67117 _67114 _67115).
Proof. exact (@lem5140113 (real_le _67116 _67117) (term356 _67115 _67117) (term375 _67114 _67115)). Qed.
Lemma lem5140132 (_67114 : real) (_67116 : real) : (term427 _67114 _67116) = (term427 _67114 _67116).
Proof. exact (eq_refl (term427 _67114 _67116)). Qed.
Lemma lem5140133 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term428 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5140132 _67114 _67116) (@lem5140114 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5140138 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term428 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (@lem5140137 (real_le _67116 _67117) (term356 _67114 _67116) (term430 _67117 _67114 _67115)). Qed.
Lemma lem5140168 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5140133 _67116 _67117 _67114 _67115) (@lem5140138 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5140170 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term431 _67116 _67117 _67114 _67115) = (term432 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5140169) (@lem5140168 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140200 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term429 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (eq_refl (term429 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140201 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)) = ((term429 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)).
Proof. exact (MK_COMB (@lem5140170 _67116 _67117 _67114 _67115) (@lem5140200 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5140204 (x : Prop) : (x = x) = True.
Proof. exact (@lem5140203 Prop x). Qed.
Lemma lem5140205 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term429 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)) = True.
Proof. exact (@lem5140204 (term429 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140206 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : ((term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)) = True.
Proof. exact (TRANS (@lem5140201 _67116 _67117 _67114 _67115) (@lem5140205 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140207 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : True = ((term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115)).
Proof. exact (SYM (@lem5140206 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140208 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term385 _67116 _67117 _67114 _67115) = (term429 _67116 _67117 _67114 _67115).
Proof. exact (EQ_MP (@lem5140207 _67116 _67117 _67114 _67115) (@lem0)). Qed.
Lemma lem5140209 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : term429 _67116 _67117 _67114 _67115.
Proof. exact (EQ_MP (@lem5140208 _67116 _67117 _67114 _67115) (@lem5139340 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140211 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5140212 (_67114 : real) (_67115 : real) (_67116 : real) (_67117 : real) : (term429 _67116 _67117 _67114 _67115) = (term433 _67114 _67115 _67116 _67117).
Proof. exact (@lem5140211 (term434 _67116 _67117 _67114 _67115) (real_le _67116 _67117)). Qed.
Lemma lem5140214 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5140215 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term435 _67116 _67117 _67114 _67115) = (term436 _67116 _67117 _67114 _67115).
Proof. exact (@lem5140214 (term356 _67114 _67116) (term430 _67117 _67114 _67115)). Qed.
Lemma lem5140217 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5140218 (_67114 : real) (_67116 : real) : (term409 _67114 _67116) = (_67114 = _67116).
Proof. exact (@lem5140217 (_67114 = _67116)). Qed.
Lemma lem5140219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5140220 (_67114 : real) (_67116 : real) : (term410 _67114 _67116) = (term411 _67114 _67116).
Proof. exact (MK_COMB (@lem5140219) (@lem5140218 _67114 _67116)). Qed.
Lemma lem5140222 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5140223 (_67117 : real) (_67114 : real) (_67115 : real) : (term437 _67117 _67114 _67115) = (term438 _67117 _67114 _67115).
Proof. exact (@lem5140222 (term356 _67115 _67117) (term375 _67114 _67115)). Qed.
Lemma lem5140225 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5140226 (_67115 : real) (_67117 : real) : (term409 _67115 _67117) = (_67115 = _67117).
Proof. exact (@lem5140225 (_67115 = _67117)). Qed.
Lemma lem5140227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5140228 (_67115 : real) (_67117 : real) : (term410 _67115 _67117) = (term411 _67115 _67117).
Proof. exact (MK_COMB (@lem5140227) (@lem5140226 _67115 _67117)). Qed.
Lemma lem5140230 (a : Prop) : (term408 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5140231 (_67114 : real) (_67115 : real) : (term439 _67114 _67115) = (real_le _67114 _67115).
Proof. exact (@lem5140230 (real_le _67114 _67115)). Qed.
Lemma lem5140232 (_67117 : real) (_67114 : real) (_67115 : real) : (term438 _67117 _67114 _67115) = (term440 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5140228 _67115 _67117) (@lem5140231 _67114 _67115)). Qed.
Lemma lem5140233 (_67117 : real) (_67114 : real) (_67115 : real) : (term437 _67117 _67114 _67115) = (term440 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5140223 _67117 _67114 _67115) (@lem5140232 _67117 _67114 _67115)). Qed.
Lemma lem5140234 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term436 _67116 _67117 _67114 _67115) = (term441 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5140220 _67114 _67116) (@lem5140233 _67117 _67114 _67115)). Qed.
Lemma lem5140235 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term435 _67116 _67117 _67114 _67115) = (term441 _67116 _67117 _67114 _67115).
Proof. exact (TRANS (@lem5140215 _67116 _67117 _67114 _67115) (@lem5140234 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140237 (_67116 : real) (_67117 : real) (_67114 : real) (_67115 : real) : (term442 _67116 _67117 _67114 _67115) = (term443 _67116 _67117 _67114 _67115).
Proof. exact (MK_COMB (@lem5140236) (@lem5140235 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140238 (_67116 : real) (_67117 : real) : (real_le _67116 _67117) = (real_le _67116 _67117).
Proof. exact (eq_refl (real_le _67116 _67117)). Qed.
Lemma lem5140239 (_67114 : real) (_67115 : real) (_67116 : real) (_67117 : real) : (term433 _67114 _67115 _67116 _67117) = (term444 _67114 _67115 _67116 _67117).
Proof. exact (MK_COMB (@lem5140237 _67116 _67117 _67114 _67115) (@lem5140238 _67116 _67117)). Qed.
Lemma lem5140240 (_67114 : real) (_67115 : real) (_67116 : real) (_67117 : real) : (term429 _67116 _67117 _67114 _67115) = (term444 _67114 _67115 _67116 _67117).
Proof. exact (TRANS (@lem5140212 _67114 _67115 _67116 _67117) (@lem5140239 _67114 _67115 _67116 _67117)). Qed.
Lemma lem5140242 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term542 x x' b.
Proof. exact (conj (@lem5139567 x x' s b h4 h5) (@lem5140095 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140243 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term543 x x' b.
Proof. exact (conj (@lem5139367 x' x) (@lem5140242 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140245 (_67114 : real) (_67115 : real) (_67116 : real) (_67117 : real) : term444 _67114 _67115 _67116 _67117.
Proof. exact (EQ_MP (@lem5140240 _67114 _67115 _67116 _67117) (@lem5140209 _67116 _67117 _67114 _67115)). Qed.
Lemma lem5140246 (b : real) (x' : real -> real) (x : real) : term544 b x' x.
Proof. exact (@lem5140245 (x' x) (x' b) (x' x) x). Qed.
Lemma lem5140249 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term353 x' x) (h4 : term328 b x s x') (h5 : term169 s b) : term448 x' x.
Proof. exact (@lem5140246 b x' x (@lem5140243 x x' s b h1 h2 h3 h4 h5)). Qed.
Lemma lem5140250 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term449 x' x.
Proof. exact (fun h0 : term353 x' x => @lem5140249 x x' s b h1 h2 h0 h3 h4). Qed.
Lemma lem5140252 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5140253 (x' : real -> real) (x : real) : (term449 x' x) = (term448 x' x).
Proof. exact (@lem5140252 (term448 x' x)). Qed.
Lemma lem5140254 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term448 x' x.
Proof. exact (EQ_MP (@lem5140253 x' x) (@lem5140250 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5140256 (a : Prop) (b : Prop) : (term450 a b) = (term451 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5140257 (x : real) (x' : real -> real) (_67094 : real) : (term372 x x' _67094) = (term452 x x' _67094).
Proof. exact (@lem5140256 (_67094 = x) (term448 x' _67094)). Qed.
Lemma lem5140259 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5140260 (x : real) (x' : real -> real) (_67094 : real) : (term452 x x' _67094) = (term453 x x' _67094).
Proof. exact (@lem5140259 (term454 x x' _67094)). Qed.
Lemma lem5140261 (x : real) (x' : real -> real) (_67094 : real) : (term372 x x' _67094) = (term453 x x' _67094).
Proof. exact (TRANS (@lem5140257 x x' _67094) (@lem5140260 x x' _67094)). Qed.
Lemma lem5140263 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term455 x' x.
Proof. exact (conj (@lem5139359 x) (@lem5140254 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5140265 (_67094 : real) (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term453 x x' _67094.
Proof. exact (EQ_MP (@lem5140261 x x' _67094) (@lem5138818 _67094 b x s x' h1)). Qed.
Lemma lem5140266 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term328 b x s x') : term456 x' x.
Proof. exact (@lem5140265 x b x s x' h1). Qed.
Lemma lem5140269 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (@lem5140266 b x s x' h3 (@lem5140263 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5140270 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term457.
Proof. exact (fun h0 : ~ False => @lem5140269 x x' s b h1 h2 h3 h4). Qed.
Lemma lem5140272 (p : Prop) : (term388 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5140273 : term457 = False.
Proof. exact (@lem5140272 False). Qed.
Lemma lem5140274 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (EQ_MP (@lem5140273) (@lem5140270 x x' s b h1 h2 h3 h4)). Qed.
Lemma lem5140275 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : term132 = False.
Proof. exact (prop_ext (fun h5 : term132 => @lem5140274 x x' s b h1 h2 h3 h4) (fun h5 : False => @lem5138602 h2)). Qed.
Lemma lem5140276 (x : real) (x' : real -> real) (s : real -> Prop) (b : real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') (h4 : term169 s b) : False.
Proof. exact (EQ_MP (@lem5140275 x x' s b h1 h2 h3 h4) (@lem5138602 h2)). Qed.
Lemma lem5140277 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : (term165 s) = False.
Proof. exact (prop_ext (fun h4 : term165 s => @lem5139290 b x s x' h1 h2 h3) (fun h4 : False => @lem5138561 s h2)). Qed.
Lemma lem5140278 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5140277 b x s x' h1 h2 h3) (@lem5138561 s h2)). Qed.
Lemma lem5140279 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5140278 b x s x' h1 h2 h3) (fun h4 : False => @lem5138501 h1)). Qed.
Lemma lem5140280 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term132) (h2 : term165 s) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5140279 b x s x' h1 h2 h3) (@lem5138501 h1)). Qed.
Lemma lem5140281 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (or_elim (@lem5138454 b x s x' h3) (fun h0 : term165 s => @lem5140280 b x s x' h2 h0 h3) (fun h0 : term169 s b => @lem5140276 x x' s b h1 h2 h3 h0)). Qed.
Lemma lem5140282 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : (term328 b x s x') = False.
Proof. exact (prop_ext (fun h4 : term328 b x s x' => @lem5140281 b x s x' h1 h2 h3) (fun h4 : False => @lem5138450 b x s x' h3)). Qed.
Lemma lem5140283 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5140282 b x s x' h1 h2 h3) (@lem5138450 b x s x' h3)). Qed.
Lemma lem5140284 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5140283 b x s x' h1 h2 h3) (fun h4 : False => @lem5138339 h2)). Qed.
Lemma lem5140285 (b : real) (x : real) (s : real -> Prop) (x' : real -> real) (h1 : term148) (h2 : term132) (h3 : term328 b x s x') : False.
Proof. exact (EQ_MP (@lem5140284 b x s x' h1 h2 h3) (@lem5138339 h2)). Qed.
Lemma lem5140286 (b : real) (x : real) (s : real -> Prop) (h1 : term148) (h2 : term132) (h3 : term331 b x s) : False.
Proof. exact (ex_elim (@lem5138283 b x s h3) (fun x' : real -> real => fun h0 : term330 b x s x' => @lem5140285 b x s x' h1 h2 h0)). Qed.
Lemma lem5140287 (x : real) (s : real -> Prop) (h1 : term148) (h2 : term132) (h3 : term333 x s) : False.
Proof. exact (ex_elim (@lem5138282 x s h3) (fun b : real => fun h0 : term332 x s b => @lem5140286 b x s h1 h2 h0)). Qed.
Lemma lem5140288 (x : real) (h1 : term148) (h2 : term132) (h3 : term335 x) : False.
Proof. exact (ex_elim (@lem5138281 x h3) (fun s : real -> Prop => fun h0 : term334 x s => @lem5140287 x s h1 h2 h0)). Qed.
Lemma lem5140289 (h1 : term148) (h2 : term132) (h3 : term125) : False.
Proof. exact (ex_elim (@lem5138129 h3) (fun x : real => fun h0 : term336 x => @lem5140288 x h1 h2 h0)). Qed.
Lemma lem5140290 (h1 : term148) (h2 : term132) (h3 : term125) : term132 = False.
Proof. exact (prop_ext (fun h4 : term132 => @lem5140289 h1 h2 h3) (fun h4 : False => @lem5138280 h2)). Qed.
Lemma lem5140291 (h1 : term148) (h2 : term132) (h3 : term125) : False.
Proof. exact (EQ_MP (@lem5140290 h1 h2 h3) (@lem5138280 h2)). Qed.
Lemma lem5140292 (h1 : term148) (h2 : term125) : term130.
Proof. exact (fun h0 : term132 => @lem5140291 h1 h0 h2). Qed.
Lemma lem5140293 : term130 = term131.
Proof. exact (@lem69 term132). Qed.
Lemma lem5140294 (h1 : term148) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem5140293) (@lem5140292 h1 h2)). Qed.
Lemma lem5140295 (h1 : term125) : term135.
Proof. exact (fun h0 : term148 => @lem5140294 h0 h1). Qed.
Lemma lem5140296 : term137.
Proof. exact (fun h0 : term125 => @lem5140295 h0). Qed.
Lemma lem5140297 : term126.
Proof. exact (EQ_MP (@lem5137604) (@lem5140296)). Qed.
Lemma lem5140299 : term126.
Proof. exact (@lem5137170 (@lem5140297)). Qed.
Lemma lem5140300 (h1 : term125) : term134.
Proof. exact (@lem5140299 (@lem5137155 h1)). Qed.
Lemma lem5140301 (h1 : term125) : term130.
Proof. exact (@lem5140300 h1 (@lem1339577)). Qed.
Lemma lem5140302 (h1 : term125) : False.
Proof. exact (@lem5140301 h1 (@lem1339697)). Qed.
Lemma lem5140303 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem5140302 h1) (fun h2 : False => @lem5137155 h1)). Qed.
Lemma lem5140304 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem5140303 h1) (@lem5137155 h1)). Qed.
Lemma lem5140305 : term124.
Proof. exact (fun h0 : term125 => @lem5140304 h0). Qed.
Lemma lem5140306 : term122.
Proof. exact (EQ_MP (@lem5137154) (@lem5140305)). Qed.
Lemma lem5140307 : term109.
Proof. exact (EQ_MP (@lem5137150) (@lem5140306)). Qed.
Lemma lem5140308 : term72.
Proof. exact (EQ_MP (@lem5137062) (@lem5140307)). Qed.
Lemma lem5140309 : term42.
Proof. exact (@lem5136833 (@lem5140308)). Qed.
Lemma lem5140310 : term41.
Proof. exact (EQ_MP (@lem5136800) (@lem5140309)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_TRIPLE_term_abbrevs.
Require Import LAMBDA_TRIPLE_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem51712 {A B C D : Type'} (f : type1198 A B C D) : term0 A B C D f.
Proof. exact (@lem51711 A B C D f). Qed.
Lemma lem51713 {A B C D : Type'} (f : type1198 A B C D) : (term0 A B C D f) = ((term1 A B C D f) = (term2 A B C D f)).
Proof. exact (eq_refl (term0 A B C D f)). Qed.
Lemma lem51744 {A B C D : Type'} (f : type1198 A B C D) : (term1 A B C D f) = (term2 A B C D f).
Proof. exact (EQ_MP (@lem51713 A B C D f) (@lem51712 A B C D f)). Qed.
Lemma lem51745 {A B C D : Type'} (f : type1198 A B C D) : (term1 A B C D f) = (term2 A B C D f).
Proof. exact (@lem51744 A B C D f). Qed.
Lemma lem51746 {A B C D : Type'} (f : type1407 A B C D) : (term3 A B C D f) = (term4 A B C D f).
Proof. exact (@lem51745 A B C D (term5 A B C D f)). Qed.
Lemma lem51747 {A B C D : Type'} (f : type1407 A B C D) (t : type1656 A B C) : (term6 A B C D f t) = (term7 A B C D f t).
Proof. exact (eq_refl (term6 A B C D f t)). Qed.
Lemma lem51748 {A B C D : Type'} (f : type1407 A B C D) : (term3 A B C D f) = (term5 A B C D f).
Proof. exact (fun_ext (fun t : type1656 A B C => @lem51747 A B C D f t)). Qed.
Lemma lem51749 {A B C D : Type'} : (@eq ((prod A (prod B C)) -> D)) = (@eq ((prod A (prod B C)) -> D)).
Proof. exact (eq_refl (@eq ((prod A (prod B C)) -> D))). Qed.
Lemma lem51750 {A B C D : Type'} (f : type1407 A B C D) : (term8 A B C D f) = (term9 A B C D f).
Proof. exact (MK_COMB (@lem51749 A B C D) (@lem51748 A B C D f)). Qed.
Lemma lem51751 {A B C D : Type'} (f : type1407 A B C D) (x : A) (y : B) (z : C) : (term10 A B C D f x y z) = (term11 A B C D f x y z).
Proof. exact (eq_refl (term10 A B C D f x y z)). Qed.
Lemma lem51752 {A B C D : Type'} (f' : type1198 A B C D) (x : A) (y : B) (z : C) : (term12 A B C D f' x y z) = (term12 A B C D f' x y z).
Proof. exact (eq_refl (term12 A B C D f' x y z)). Qed.
Lemma lem51753 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) (z : C) : (term13 A B C D f' f x y z) = (term14 A B C D f' f x y z).
Proof. exact (MK_COMB (@lem51752 A B C D f' x y z) (@lem51751 A B C D f x y z)). Qed.
Lemma lem51754 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) : (term15 A B C D f' f x y) = (term16 A B C D f' f x y).
Proof. exact (fun_ext (fun z : C => @lem51753 A B C D f' f x y z)). Qed.
Lemma lem51755 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem51756 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) : (term17 A B C D f' f x y) = (term18 A B C D f' f x y).
Proof. exact (MK_COMB (@lem51755 C) (@lem51754 A B C D f' f x y)). Qed.
Lemma lem51757 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) : (term19 A B C D f' f x) = (term20 A B C D f' f x).
Proof. exact (fun_ext (fun y : B => @lem51756 A B C D f' f x y)). Qed.
Lemma lem51758 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51759 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) : (term21 A B C D f' f x) = (term22 A B C D f' f x).
Proof. exact (MK_COMB (@lem51758 B) (@lem51757 A B C D f' f x)). Qed.
Lemma lem51760 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) : (term23 A B C D f' f) = (term24 A B C D f' f).
Proof. exact (fun_ext (fun x : A => @lem51759 A B C D f' f x)). Qed.
Lemma lem51761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51762 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) : (term25 A B C D f' f) = (term26 A B C D f' f).
Proof. exact (MK_COMB (@lem51761 A) (@lem51760 A B C D f' f)). Qed.
Lemma lem51763 {A B C D : Type'} (f : type1407 A B C D) : (term27 A B C D f) = (term28 A B C D f).
Proof. exact (fun_ext (fun f' : type1198 A B C D => @lem51762 A B C D f' f)). Qed.
Lemma lem51764 {A B C D : Type'} : (@GABS ((prod A (prod B C)) -> D)) = (@GABS ((prod A (prod B C)) -> D)).
Proof. exact (eq_refl (@GABS ((prod A (prod B C)) -> D))). Qed.
Lemma lem51765 {A B C D : Type'} (f : type1407 A B C D) : (term4 A B C D f) = (term29 A B C D f).
Proof. exact (MK_COMB (@lem51764 A B C D) (@lem51763 A B C D f)). Qed.
Lemma lem51766 {A B C D : Type'} (f : type1407 A B C D) : ((term3 A B C D f) = (term4 A B C D f)) = ((term5 A B C D f) = (term29 A B C D f)).
Proof. exact (MK_COMB (@lem51750 A B C D f) (@lem51765 A B C D f)). Qed.
Lemma lem51767 {A B C D : Type'} (f : type1407 A B C D) : (term5 A B C D f) = (term29 A B C D f).
Proof. exact (EQ_MP (@lem51766 A B C D f) (@lem51746 A B C D f)). Qed.
Lemma lem51789 {A B : Type'} (y : B) (x : A) : (term30 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem51790 {A B C : Type'} (y : prod B C) (x : A) : (term31 A B C x y) = x.
Proof. exact (@lem51789 A (prod B C) y x). Qed.
Lemma lem51791 {A B C : Type'} (y : B) (z : C) (x : A) : (term32 A B C x y z) = x.
Proof. exact (@lem51790 A B C (@pair B C y z) x). Qed.
Lemma lem51792 {A B C D : Type'} (f : type1407 A B C D) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem51793 {A B C D : Type'} (y : B) (z : C) (f : type1407 A B C D) (x : A) : (term33 A B C D f x y z) = (f x).
Proof. exact (MK_COMB (@lem51792 A B C D f) (@lem51791 A B C y z x)). Qed.
Lemma lem51795 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem51796 {A B C : Type'} (x : A) (y : prod B C) : (term35 A B C x y) = y.
Proof. exact (@lem51795 A (prod B C) x y). Qed.
Lemma lem51797 {A B C : Type'} (x : A) (y : B) (z : C) : (term36 A B C x y z) = (@pair B C y z).
Proof. exact (@lem51796 A B C x (@pair B C y z)). Qed.
Lemma lem51798 {B C : Type'} : (@fst B C) = (@fst B C).
Proof. exact (eq_refl (@fst B C)). Qed.
Lemma lem51799 {A B C : Type'} (x : A) (y : B) (z : C) : (term37 A B C x y z) = (term30 B C y z).
Proof. exact (MK_COMB (@lem51798 B C) (@lem51797 A B C x y z)). Qed.
Lemma lem51801 {A B : Type'} (y : B) (x : A) : (term30 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem51802 {B C : Type'} (y : C) (x : B) : (term30 B C x y) = x.
Proof. exact (@lem51801 B C y x). Qed.
Lemma lem51803 {B C : Type'} (z : C) (y : B) : (term30 B C y z) = y.
Proof. exact (@lem51802 B C z y). Qed.
Lemma lem51804 {A B C : Type'} (x : A) (z : C) (y : B) : (term37 A B C x y z) = y.
Proof. exact (TRANS (@lem51799 A B C x y z) (@lem51803 B C z y)). Qed.
Lemma lem51805 {A B C D : Type'} (z : C) (f : type1407 A B C D) (x : A) (y : B) : (term38 A B C D f x y z) = (f x y).
Proof. exact (MK_COMB (@lem51793 A B C D y z f x) (@lem51804 A B C x z y)). Qed.
Lemma lem51807 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem51808 {A B C : Type'} (x : A) (y : prod B C) : (term35 A B C x y) = y.
Proof. exact (@lem51807 A (prod B C) x y). Qed.
Lemma lem51809 {A B C : Type'} (x : A) (y : B) (z : C) : (term36 A B C x y z) = (@pair B C y z).
Proof. exact (@lem51808 A B C x (@pair B C y z)). Qed.
Lemma lem51810 {B C : Type'} : (@snd B C) = (@snd B C).
Proof. exact (eq_refl (@snd B C)). Qed.
Lemma lem51811 {A B C : Type'} (x : A) (y : B) (z : C) : (term39 A B C x y z) = (term34 B C y z).
Proof. exact (MK_COMB (@lem51810 B C) (@lem51809 A B C x y z)). Qed.
Lemma lem51813 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem51814 {B C : Type'} (x : B) (y : C) : (term34 B C x y) = y.
Proof. exact (@lem51813 B C x y). Qed.
Lemma lem51815 {B C : Type'} (y : B) (z : C) : (term34 B C y z) = z.
Proof. exact (@lem51814 B C y z). Qed.
Lemma lem51816 {A B C : Type'} (x : A) (y : B) (z : C) : (term39 A B C x y z) = z.
Proof. exact (TRANS (@lem51811 A B C x y z) (@lem51815 B C y z)). Qed.
Lemma lem51817 {A B C D : Type'} (f : type1407 A B C D) (x : A) (y : B) (z : C) : (term11 A B C D f x y z) = (f x y z).
Proof. exact (MK_COMB (@lem51805 A B C D z f x y) (@lem51816 A B C x y z)). Qed.
Lemma lem51818 {A B C D : Type'} (f' : type1198 A B C D) (x : A) (y : B) (z : C) : (term12 A B C D f' x y z) = (term12 A B C D f' x y z).
Proof. exact (eq_refl (term12 A B C D f' x y z)). Qed.
Lemma lem51819 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) (z : C) : (term14 A B C D f' f x y z) = (term40 A B C D f' f x y z).
Proof. exact (MK_COMB (@lem51818 A B C D f' x y z) (@lem51817 A B C D f x y z)). Qed.
Lemma lem51820 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) : (term16 A B C D f' f x y) = (term41 A B C D f' f x y).
Proof. exact (fun_ext (fun z : C => @lem51819 A B C D f' f x y z)). Qed.
Lemma lem51823 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem51824 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) (y : B) : (term18 A B C D f' f x y) = (term42 A B C D f' f x y).
Proof. exact (MK_COMB (@lem51823 C) (@lem51820 A B C D f' f x y)). Qed.
Lemma lem51829 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) : (term20 A B C D f' f x) = (term43 A B C D f' f x).
Proof. exact (fun_ext (fun y : B => @lem51824 A B C D f' f x y)). Qed.
Lemma lem51832 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51833 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) (x : A) : (term22 A B C D f' f x) = (term44 A B C D f' f x).
Proof. exact (MK_COMB (@lem51832 B) (@lem51829 A B C D f' f x)). Qed.
Lemma lem51838 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) : (term24 A B C D f' f) = (term45 A B C D f' f).
Proof. exact (fun_ext (fun x : A => @lem51833 A B C D f' f x)). Qed.
Lemma lem51841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51842 {A B C D : Type'} (f' : type1198 A B C D) (f : type1407 A B C D) : (term26 A B C D f' f) = (term46 A B C D f' f).
Proof. exact (MK_COMB (@lem51841 A) (@lem51838 A B C D f' f)). Qed.
Lemma lem51847 {A B C D : Type'} (f : type1407 A B C D) : (term28 A B C D f) = (term47 A B C D f).
Proof. exact (fun_ext (fun f' : type1198 A B C D => @lem51842 A B C D f' f)). Qed.
Lemma lem51850 {A B C D : Type'} : (@GABS ((prod A (prod B C)) -> D)) = (@GABS ((prod A (prod B C)) -> D)).
Proof. exact (eq_refl (@GABS ((prod A (prod B C)) -> D))). Qed.
Lemma lem51851 {A B C D : Type'} (f : type1407 A B C D) : (term29 A B C D f) = (term48 A B C D f).
Proof. exact (MK_COMB (@lem51850 A B C D) (@lem51847 A B C D f)). Qed.
Lemma lem51852 {A B C D : Type'} (f : type1407 A B C D) : (term5 A B C D f) = (term48 A B C D f).
Proof. exact (TRANS (@lem51767 A B C D f) (@lem51851 A B C D f)). Qed.
Lemma lem51853 {A B C D : Type'} (f : type1407 A B C D) : (term49 A B C D f) = (term49 A B C D f).
Proof. exact (eq_refl (term49 A B C D f)). Qed.
Lemma lem51854 {A B C D : Type'} (f : type1407 A B C D) : ((term48 A B C D f) = (term5 A B C D f)) = ((term48 A B C D f) = (term48 A B C D f)).
Proof. exact (MK_COMB (@lem51853 A B C D f) (@lem51852 A B C D f)). Qed.
Lemma lem51856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem51857 {A B C D : Type'} (x : type1198 A B C D) : (x = x) = True.
Proof. exact (@lem51856 (type1198 A B C D) x). Qed.
Lemma lem51858 {A B C D : Type'} (f : type1407 A B C D) : ((term48 A B C D f) = (term48 A B C D f)) = True.
Proof. exact (@lem51857 A B C D (term48 A B C D f)). Qed.
Lemma lem51861 {A B C D : Type'} (f : type1407 A B C D) : (term50 A B C D f) = (term50 A B C D f).
Proof. exact (eq_refl (term50 A B C D f)). Qed.
Lemma lem51862 {A B C D : Type'} (f : type1407 A B C D) : (term50 A B C D f) = (((term48 A B C D f) = (term48 A B C D f)) = True).
Proof. exact (eq_refl (term50 A B C D f)). Qed.
Lemma lem51863 {A B C D : Type'} (f : type1407 A B C D) : (term51 A B C D f) = (term51 A B C D f).
Proof. exact (eq_refl (term51 A B C D f)). Qed.
Lemma lem51864 {A B C D : Type'} (f : type1407 A B C D) : ((term50 A B C D f) = (term50 A B C D f)) = ((term50 A B C D f) = (((term48 A B C D f) = (term48 A B C D f)) = True)).
Proof. exact (MK_COMB (@lem51863 A B C D f) (@lem51862 A B C D f)). Qed.
Lemma lem51865 {A B C D : Type'} (f : type1407 A B C D) : (term50 A B C D f) = (((term48 A B C D f) = (term48 A B C D f)) = True).
Proof. exact (eq_refl (term50 A B C D f)). Qed.
Lemma lem51866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem51867 {A B C D : Type'} (f : type1407 A B C D) : (term51 A B C D f) = (term52 A B C D f).
Proof. exact (MK_COMB (@lem51866) (@lem51865 A B C D f)). Qed.
Lemma lem51868 {A B C D : Type'} (f : type1407 A B C D) : (((term48 A B C D f) = (term48 A B C D f)) = True) = (((term48 A B C D f) = (term48 A B C D f)) = True).
Proof. exact (eq_refl (((term48 A B C D f) = (term48 A B C D f)) = True)). Qed.
Lemma lem51869 {A B C D : Type'} (f : type1407 A B C D) : ((term50 A B C D f) = (((term48 A B C D f) = (term48 A B C D f)) = True)) = ((((term48 A B C D f) = (term48 A B C D f)) = True) = (((term48 A B C D f) = (term48 A B C D f)) = True)).
Proof. exact (MK_COMB (@lem51867 A B C D f) (@lem51868 A B C D f)). Qed.
Lemma lem51870 {A B C D : Type'} (f : type1407 A B C D) : ((term50 A B C D f) = (term50 A B C D f)) = ((((term48 A B C D f) = (term48 A B C D f)) = True) = (((term48 A B C D f) = (term48 A B C D f)) = True)).
Proof. exact (TRANS (@lem51864 A B C D f) (@lem51869 A B C D f)). Qed.
Lemma lem51871 {A B C D : Type'} (f : type1407 A B C D) : (((term48 A B C D f) = (term48 A B C D f)) = True) = (((term48 A B C D f) = (term48 A B C D f)) = True).
Proof. exact (EQ_MP (@lem51870 A B C D f) (@lem51861 A B C D f)). Qed.
Lemma lem51872 {A B C D : Type'} (f : type1407 A B C D) : ((term48 A B C D f) = (term48 A B C D f)) = True.
Proof. exact (EQ_MP (@lem51871 A B C D f) (@lem51858 A B C D f)). Qed.
Lemma lem51873 {A B C D : Type'} (f : type1407 A B C D) : ((term48 A B C D f) = (term5 A B C D f)) = True.
Proof. exact (TRANS (@lem51854 A B C D f) (@lem51872 A B C D f)). Qed.
Lemma lem51874 {A B C D : Type'} : (term53 A B C D) = (term54 A B C D).
Proof. exact (fun_ext (fun f : type1407 A B C D => @lem51873 A B C D f)). Qed.
Lemma lem51877 {A B C D : Type'} : (@all (A -> B -> C -> D)) = (@all (A -> B -> C -> D)).
Proof. exact (eq_refl (@all (A -> B -> C -> D))). Qed.
Lemma lem51878 {A B C D : Type'} : (term55 A B C D) = (term56 A B C D).
Proof. exact (MK_COMB (@lem51877 A B C D) (@lem51874 A B C D)). Qed.
Lemma lem51880 {A : Type'} (t : Prop) : (term57 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51881 {A B C D : Type'} (t : Prop) : (term58 A B C D t) = t.
Proof. exact (@lem51880 (type1407 A B C D) t). Qed.
Lemma lem51882 {A B C D : Type'} : (term56 A B C D) = True.
Proof. exact (@lem51881 A B C D True). Qed.
Lemma lem51883 {A B C D : Type'} : (term55 A B C D) = True.
Proof. exact (TRANS (@lem51878 A B C D) (@lem51882 A B C D)). Qed.
Lemma lem51884 {A B C D : Type'} : True = (term55 A B C D).
Proof. exact (SYM (@lem51883 A B C D)). Qed.
Lemma lem51885 {A B C D : Type'} : term55 A B C D.
Proof. exact (EQ_MP (@lem51884 A B C D) (@lem0)). Qed.

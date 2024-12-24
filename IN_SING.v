Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_SING_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem3205804 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3205805 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3205806 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3205805 A x) (@lem3205804 A x)). Qed.
Lemma lem3205807 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3205809 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3205810 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem3205811 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem3205810 A x) (@lem3205809 A x)). Qed.
Lemma lem3205812 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem3205811 A x y). Qed.
Lemma lem3205813 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem3205814 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem3205813 A y x) (@lem3205812 A x y)). Qed.
Lemma lem3205815 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem3205814 A y x s). Qed.
Lemma lem3205816 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem3205829 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3205816 A y x s) (@lem3205815 A y x s)). Qed.
Lemma lem3205830 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (@lem3205829 A y x s). Qed.
Lemma lem3205831 {A : Type'} (y : A) (x : A) : (term10 A x y) = (term11 A y x).
Proof. exact (@lem3205830 A y x (@EMPTY A)). Qed.
Lemma lem3205837 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3205807 A x (@lem3205806 A x)). Qed.
Lemma lem3205838 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3205837 A x). Qed.
Lemma lem3205839 {A : Type'} (x : A) (y : A) : (term12 A x y) = (term12 A x y).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem3205840 {A : Type'} (x : A) (y : A) : (term11 A y x) = (term13 A x y).
Proof. exact (MK_COMB (@lem3205839 A x y) (@lem3205838 A x)). Qed.
Lemma lem3205842 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3205843 {A : Type'} (x : A) (y : A) : (term13 A x y) = (x = y).
Proof. exact (@lem3205842 (x = y)). Qed.
Lemma lem3205846 {A : Type'} (x : A) (y : A) : (term11 A y x) = (x = y).
Proof. exact (TRANS (@lem3205840 A x y) (@lem3205843 A x y)). Qed.
Lemma lem3205847 {A : Type'} (x : A) (y : A) : (term10 A x y) = (x = y).
Proof. exact (TRANS (@lem3205831 A y x) (@lem3205846 A x y)). Qed.
Lemma lem3205848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205849 {A : Type'} (x : A) (y : A) : (term14 A x y) = (term15 A x y).
Proof. exact (MK_COMB (@lem3205848) (@lem3205847 A x y)). Qed.
Lemma lem3205852 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3205853 {A : Type'} (x : A) (y : A) : ((term10 A x y) = (x = y)) = ((x = y) = (x = y)).
Proof. exact (MK_COMB (@lem3205849 A x y) (@lem3205852 A x y)). Qed.
Lemma lem3205855 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205856 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205855 Prop x). Qed.
Lemma lem3205857 {A : Type'} (x : A) (y : A) : ((x = y) = (x = y)) = True.
Proof. exact (@lem3205856 (x = y)). Qed.
Lemma lem3205858 {A : Type'} (x : A) (y : A) : ((term10 A x y) = (x = y)) = True.
Proof. exact (TRANS (@lem3205853 A x y) (@lem3205857 A x y)). Qed.
Lemma lem3205859 {A : Type'} (x : A) : (term16 A x) = (term17 A).
Proof. exact (fun_ext (fun y : A => @lem3205858 A x y)). Qed.
Lemma lem3205860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205861 {A : Type'} (x : A) : (term18 A x) = (term19 A).
Proof. exact (MK_COMB (@lem3205860 A) (@lem3205859 A x)). Qed.
Lemma lem3205863 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205864 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem3205863 A t). Qed.
Lemma lem3205865 {A : Type'} : (term19 A) = True.
Proof. exact (@lem3205864 A True). Qed.
Lemma lem3205866 {A : Type'} (x : A) : (term18 A x) = True.
Proof. exact (TRANS (@lem3205861 A x) (@lem3205865 A)). Qed.
Lemma lem3205867 {A : Type'} : (term21 A) = (term17 A).
Proof. exact (fun_ext (fun x : A => @lem3205866 A x)). Qed.
Lemma lem3205868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205869 {A : Type'} : (term22 A) = (term19 A).
Proof. exact (MK_COMB (@lem3205868 A) (@lem3205867 A)). Qed.
Lemma lem3205871 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205872 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem3205871 A t). Qed.
Lemma lem3205873 {A : Type'} : (term19 A) = True.
Proof. exact (@lem3205872 A True). Qed.
Lemma lem3205874 {A : Type'} : (term22 A) = True.
Proof. exact (TRANS (@lem3205869 A) (@lem3205873 A)). Qed.
Lemma lem3205875 {A : Type'} : True = (term22 A).
Proof. exact (SYM (@lem3205874 A)). Qed.
Lemma lem3205876 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem3205875 A) (@lem0)). Qed.

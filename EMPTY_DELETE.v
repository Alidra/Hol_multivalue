Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_DELETE_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3306779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3306780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3306779 A s t). Qed.
Lemma lem3306781 {A : Type'} (x : A) : ((@DELETE A (@EMPTY A) x) = (@EMPTY A)) = (term1 A x).
Proof. exact (@lem3306780 A (@DELETE A (@EMPTY A) x) (@EMPTY A)). Qed.
Lemma lem3306790 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem3306781 A x)). Qed.
Lemma lem3306791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306792 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3306791 A) (@lem3306790 A)). Qed.
Lemma lem3306797 {A : Type'} : (term5 A) = (term4 A).
Proof. exact (SYM (@lem3306792 A)). Qed.
Lemma lem3306809 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term6 A x s y) = (term7 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3306810 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term6 A x s y) = (term7 A s x y).
Proof. exact (@lem3306809 A s x y). Qed.
Lemma lem3306811 {A : Type'} (x' : A) (x : A) : (term8 A x' x) = (term9 A x' x).
Proof. exact (@lem3306810 A (@EMPTY A) x' x). Qed.
Lemma lem3306815 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3306816 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3306815 A x). Qed.
Lemma lem3306817 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3306816 A x'). Qed.
Lemma lem3306818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3306819 {A : Type'} (x' : A) : (term10 A x') = (and False).
Proof. exact (MK_COMB (@lem3306818) (@lem3306817 A x')). Qed.
Lemma lem3306822 {A : Type'} (x' : A) (x : A) : (term11 A x' x) = (term11 A x' x).
Proof. exact (eq_refl (term11 A x' x)). Qed.
Lemma lem3306823 {A : Type'} (x' : A) (x : A) : (term9 A x' x) = (term12 A x' x).
Proof. exact (MK_COMB (@lem3306819 A x') (@lem3306822 A x' x)). Qed.
Lemma lem3306825 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3306826 {A : Type'} (x' : A) (x : A) : (term12 A x' x) = False.
Proof. exact (@lem3306825 (term11 A x' x)). Qed.
Lemma lem3306827 {A : Type'} (x' : A) (x : A) : (term9 A x' x) = False.
Proof. exact (TRANS (@lem3306823 A x' x) (@lem3306826 A x' x)). Qed.
Lemma lem3306828 {A : Type'} (x' : A) (x : A) : (term8 A x' x) = False.
Proof. exact (TRANS (@lem3306811 A x' x) (@lem3306827 A x' x)). Qed.
Lemma lem3306829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3306830 {A : Type'} (x' : A) (x : A) : (term13 A x' x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3306829) (@lem3306828 A x' x)). Qed.
Lemma lem3306832 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3306833 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3306832 A x). Qed.
Lemma lem3306834 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3306833 A x'). Qed.
Lemma lem3306835 {A : Type'} (x : A) (x' : A) : ((term8 A x' x) = (@IN A x' (@EMPTY A))) = (False = False).
Proof. exact (MK_COMB (@lem3306830 A x' x) (@lem3306834 A x')). Qed.
Lemma lem3306837 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3306838 : (False = False) = (~ False).
Proof. exact (@lem3306837 False). Qed.
Lemma lem3306840 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3306841 : (False = False) = True.
Proof. exact (TRANS (@lem3306838) (@lem3306840)). Qed.
Lemma lem3306842 {A : Type'} (x : A) (x' : A) : ((term8 A x' x) = (@IN A x' (@EMPTY A))) = True.
Proof. exact (TRANS (@lem3306835 A x x') (@lem3306841)). Qed.
Lemma lem3306843 {A : Type'} (x : A) : (term14 A x) = (term15 A).
Proof. exact (fun_ext (fun x' : A => @lem3306842 A x x')). Qed.
Lemma lem3306844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306845 {A : Type'} (x : A) : (term1 A x) = (term16 A).
Proof. exact (MK_COMB (@lem3306844 A) (@lem3306843 A x)). Qed.
Lemma lem3306847 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3306848 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem3306847 A t). Qed.
Lemma lem3306849 {A : Type'} : (term16 A) = True.
Proof. exact (@lem3306848 A True). Qed.
Lemma lem3306850 {A : Type'} (x : A) : (term1 A x) = True.
Proof. exact (TRANS (@lem3306845 A x) (@lem3306849 A)). Qed.
Lemma lem3306851 {A : Type'} : (term3 A) = (term15 A).
Proof. exact (fun_ext (fun x : A => @lem3306850 A x)). Qed.
Lemma lem3306852 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3306853 {A : Type'} : (term5 A) = (term16 A).
Proof. exact (MK_COMB (@lem3306852 A) (@lem3306851 A)). Qed.
Lemma lem3306855 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3306856 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem3306855 A t). Qed.
Lemma lem3306857 {A : Type'} : (term16 A) = True.
Proof. exact (@lem3306856 A True). Qed.
Lemma lem3306858 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3306853 A) (@lem3306857 A)). Qed.
Lemma lem3306859 {A : Type'} : True = (term5 A).
Proof. exact (SYM (@lem3306858 A)). Qed.
Lemma lem3306860 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3306859 A) (@lem0)). Qed.
Lemma lem3306861 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3306797 A) (@lem3306860 A)). Qed.

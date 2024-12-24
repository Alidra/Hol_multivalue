Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_IMAGE_term_abbrevs.
Require Import IN_UNIV_spec.
Require Import SUBSET_UNIV_spec.
Require Import SURJECTIVE_ON_IMAGE_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem5042708 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem5042709 {A : Type'} (s : A -> Prop) : (term0 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5042710 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem5042709 A s) (@lem5042708 A s)). Qed.
Lemma lem5042711 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem5042713 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem5042714 {A : Type'} (x : A) : (term1 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem5042715 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem5042714 A x) (@lem5042713 A x)). Qed.
Lemma lem5042716 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem5042718 {A B : Type'} : term2 A B.
Proof. exact (@lem5042707 A B). Qed.
Lemma lem5042719 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem5042718 A B f). Qed.
Lemma lem5042720 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem5042721 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem5042720 A B f) (@lem5042719 A B f)). Qed.
Lemma lem5042722 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem5042721 A B f (@UNIV A)). Qed.
Lemma lem5042723 {A B : Type'} (f : A -> B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem5042724 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (EQ_MP (@lem5042723 A B f) (@lem5042722 A B f)). Qed.
Lemma lem5042725 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem5042724 A B f (@UNIV B)). Qed.
Lemma lem5042726 {A B : Type'} (f : A -> B) : (term7 A B f) = ((term8 A B f) = (term9 A B f)).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem5042727 {A B : Type'} (f : A -> B) : (term8 A B f) = (term9 A B f).
Proof. exact (EQ_MP (@lem5042726 A B f) (@lem5042725 A B f)). Qed.
Lemma lem5042741 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5042711 A s) (@lem5042710 A s)). Qed.
Lemma lem5042742 {B : Type'} (s : B -> Prop) : (@SUBSET B s (@UNIV B)) = True.
Proof. exact (@lem5042741 B s). Qed.
Lemma lem5042743 {B : Type'} (t : B -> Prop) : (@SUBSET B t (@UNIV B)) = True.
Proof. exact (@lem5042742 B t). Qed.
Lemma lem5042744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042745 {B : Type'} (t : B -> Prop) : (term10 B t) = (imp True).
Proof. exact (MK_COMB (@lem5042744) (@lem5042743 B t)). Qed.
Lemma lem5042753 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5042711 A s) (@lem5042710 A s)). Qed.
Lemma lem5042754 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (@lem5042753 A s). Qed.
Lemma lem5042755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042756 {A : Type'} (s : A -> Prop) : (term11 A s) = (and True).
Proof. exact (MK_COMB (@lem5042755) (@lem5042754 A s)). Qed.
Lemma lem5042759 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : ((@IMAGE A B f s) = t) = ((@IMAGE A B f s) = t).
Proof. exact (eq_refl ((@IMAGE A B f s) = t)). Qed.
Lemma lem5042760 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term12 A B f s t) = (term13 A B f s t).
Proof. exact (MK_COMB (@lem5042756 A s) (@lem5042759 A B f s t)). Qed.
Lemma lem5042762 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5042763 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term13 A B f s t) = ((@IMAGE A B f s) = t).
Proof. exact (@lem5042762 ((@IMAGE A B f s) = t)). Qed.
Lemma lem5042766 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term12 A B f s t) = ((@IMAGE A B f s) = t).
Proof. exact (TRANS (@lem5042760 A B f s t) (@lem5042763 A B f s t)). Qed.
Lemma lem5042767 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term14 A B f t) = (term15 A B f t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5042766 A B f s t)). Qed.
Lemma lem5042768 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5042769 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term16 A B f t) = (term17 A B f t).
Proof. exact (MK_COMB (@lem5042768 A) (@lem5042767 A B f t)). Qed.
Lemma lem5042774 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term18 A B f t) = (term19 A B f t).
Proof. exact (MK_COMB (@lem5042745 B t) (@lem5042769 A B f t)). Qed.
Lemma lem5042776 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5042777 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term19 A B f t) = (term17 A B f t).
Proof. exact (@lem5042776 (term17 A B f t)). Qed.
Lemma lem5042784 {A B : Type'} (f : A -> B) (t : B -> Prop) : (term18 A B f t) = (term17 A B f t).
Proof. exact (TRANS (@lem5042774 A B f t) (@lem5042777 A B f t)). Qed.
Lemma lem5042785 {A B : Type'} (f : A -> B) : (term20 A B f) = (term21 A B f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5042784 A B f t)). Qed.
Lemma lem5042786 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5042787 {A B : Type'} (f : A -> B) : (term8 A B f) = (term22 A B f).
Proof. exact (MK_COMB (@lem5042786 B) (@lem5042785 A B f)). Qed.
Lemma lem5042792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5042793 {A B : Type'} (f : A -> B) : (term23 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem5042792) (@lem5042787 A B f)). Qed.
Lemma lem5042801 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5042716 A x) (@lem5042715 A x)). Qed.
Lemma lem5042802 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem5042801 B x). Qed.
Lemma lem5042803 {B : Type'} (y : B) : (@IN B y (@UNIV B)) = True.
Proof. exact (@lem5042802 B y). Qed.
Lemma lem5042804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042805 {B : Type'} (y : B) : (term25 B y) = (imp True).
Proof. exact (MK_COMB (@lem5042804) (@lem5042803 B y)). Qed.
Lemma lem5042813 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5042716 A x) (@lem5042715 A x)). Qed.
Lemma lem5042814 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5042813 A x). Qed.
Lemma lem5042815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5042816 {A : Type'} (x : A) : (term26 A x) = (and True).
Proof. exact (MK_COMB (@lem5042815) (@lem5042814 A x)). Qed.
Lemma lem5042819 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem5042820 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term27 A B f x y) = (term28 A B f x y).
Proof. exact (MK_COMB (@lem5042816 A x) (@lem5042819 A B f x y)). Qed.
Lemma lem5042822 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5042823 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term28 A B f x y) = ((f x) = y).
Proof. exact (@lem5042822 ((f x) = y)). Qed.
Lemma lem5042826 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term27 A B f x y) = ((f x) = y).
Proof. exact (TRANS (@lem5042820 A B f x y) (@lem5042823 A B f x y)). Qed.
Lemma lem5042827 {A B : Type'} (f : A -> B) (y : B) : (term29 A B f y) = (term30 A B f y).
Proof. exact (fun_ext (fun x : A => @lem5042826 A B f x y)). Qed.
Lemma lem5042828 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5042829 {A B : Type'} (f : A -> B) (y : B) : (term31 A B f y) = (term32 A B f y).
Proof. exact (MK_COMB (@lem5042828 A) (@lem5042827 A B f y)). Qed.
Lemma lem5042834 {A B : Type'} (f : A -> B) (y : B) : (term33 A B f y) = (term34 A B f y).
Proof. exact (MK_COMB (@lem5042805 B y) (@lem5042829 A B f y)). Qed.
Lemma lem5042836 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5042837 {A B : Type'} (f : A -> B) (y : B) : (term34 A B f y) = (term32 A B f y).
Proof. exact (@lem5042836 (term32 A B f y)). Qed.
Lemma lem5042844 {A B : Type'} (f : A -> B) (y : B) : (term33 A B f y) = (term32 A B f y).
Proof. exact (TRANS (@lem5042834 A B f y) (@lem5042837 A B f y)). Qed.
Lemma lem5042845 {A B : Type'} (f : A -> B) : (term35 A B f) = (term36 A B f).
Proof. exact (fun_ext (fun y : B => @lem5042844 A B f y)). Qed.
Lemma lem5042846 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5042847 {A B : Type'} (f : A -> B) : (term9 A B f) = (term37 A B f).
Proof. exact (MK_COMB (@lem5042846 B) (@lem5042845 A B f)). Qed.
Lemma lem5042852 {A B : Type'} (f : A -> B) : ((term8 A B f) = (term9 A B f)) = ((term22 A B f) = (term37 A B f)).
Proof. exact (MK_COMB (@lem5042793 A B f) (@lem5042847 A B f)). Qed.
Lemma lem5042855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5042856 {A B : Type'} (f : A -> B) : (term38 A B f) = (term39 A B f).
Proof. exact (MK_COMB (@lem5042855) (@lem5042852 A B f)). Qed.
Lemma lem5042879 {A B : Type'} (f : A -> B) : ((term22 A B f) = (term37 A B f)) = ((term22 A B f) = (term37 A B f)).
Proof. exact (eq_refl ((term22 A B f) = (term37 A B f))). Qed.
Lemma lem5042880 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (MK_COMB (@lem5042856 A B f) (@lem5042879 A B f)). Qed.
Lemma lem5042884 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5042885 {A B : Type'} (f : A -> B) : (term41 A B f) = True.
Proof. exact (@lem5042884 ((term22 A B f) = (term37 A B f))). Qed.
Lemma lem5042886 {A B : Type'} (f : A -> B) : (term40 A B f) = True.
Proof. exact (TRANS (@lem5042880 A B f) (@lem5042885 A B f)). Qed.
Lemma lem5042887 {A B : Type'} (f : A -> B) : True = (term40 A B f).
Proof. exact (SYM (@lem5042886 A B f)). Qed.
Lemma lem5042888 {A B : Type'} (f : A -> B) : term40 A B f.
Proof. exact (EQ_MP (@lem5042887 A B f) (@lem0)). Qed.
Lemma lem5042889 {A B : Type'} (f : A -> B) : (term22 A B f) = (term37 A B f).
Proof. exact (@lem5042888 A B f (@lem5042727 A B f)). Qed.
Lemma lem5042894 {A B : Type'} : term42 A B.
Proof. exact (fun f : A -> B => @lem5042889 A B f). Qed.

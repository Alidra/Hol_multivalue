Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_IN_EMPTY_term_abbrevs.
Require Import IN_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm3185606_spec.
Require Import thm3185620_spec.
Lemma lem3204728 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem3181151 A P). Qed.
Lemma lem3204729 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3204730 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3204729 A P) (@lem3204728 A P)). Qed.
Lemma lem3204731 {A : Type'} (P : A -> Prop) (x : A) : term2 A P x.
Proof. exact (@lem3204730 A P x). Qed.
Lemma lem3204732 {A : Type'} (P : A -> Prop) (x : A) : (term2 A P x) = ((@IN A x P) = (P x)).
Proof. exact (eq_refl (term2 A P x)). Qed.
Lemma lem3204739 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3204732 A P x) (@lem3204731 A P x)). Qed.
Lemma lem3204740 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3204739 A P x). Qed.
Lemma lem3204741 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@EMPTY A x).
Proof. exact (@lem3204740 A (@EMPTY A) x). Qed.
Lemma lem3204743 {A : Type'} : (@EMPTY A) = (term3 A).
Proof. exact (TRANS (@lem3185606 A) (@lem3185620 A)). Qed.
Lemma lem3204744 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3204745 {A : Type'} (x : A) : (@EMPTY A x) = (term4 A x).
Proof. exact (MK_COMB (@lem3204743 A) (@lem3204744 A x)). Qed.
Lemma lem3204747 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3204748 {A : Type'} (f : A -> Prop) (y : A) : (term6 A f y) = (f y).
Proof. exact (@lem3204747 A Prop f y). Qed.
Lemma lem3204749 {A : Type'} (x : A) : (term7 A x) = (term4 A x).
Proof. exact (@lem3204748 A (term3 A) x). Qed.
Lemma lem3204750 {A : Type'} (x : A) : (term4 A x) = False.
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3204751 {A : Type'} : (term8 A) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem3204750 A x)). Qed.
Lemma lem3204752 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3204753 {A : Type'} (x : A) : (term7 A x) = (term4 A x).
Proof. exact (MK_COMB (@lem3204751 A) (@lem3204752 A x)). Qed.
Lemma lem3204754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3204755 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (MK_COMB (@lem3204754) (@lem3204753 A x)). Qed.
Lemma lem3204756 {A : Type'} (x : A) : (term4 A x) = False.
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3204757 {A : Type'} (x : A) : ((term7 A x) = (term4 A x)) = ((term4 A x) = False).
Proof. exact (MK_COMB (@lem3204755 A x) (@lem3204756 A x)). Qed.
Lemma lem3204758 {A : Type'} (x : A) : (term4 A x) = False.
Proof. exact (EQ_MP (@lem3204757 A x) (@lem3204749 A x)). Qed.
Lemma lem3204759 {A : Type'} (x : A) : (@EMPTY A x) = False.
Proof. exact (TRANS (@lem3204745 A x) (@lem3204758 A x)). Qed.
Lemma lem3204760 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (TRANS (@lem3204741 A x) (@lem3204759 A x)). Qed.
Lemma lem3204761 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3204762 {A : Type'} (x : A) : (term11 A x) = (~ False).
Proof. exact (MK_COMB (@lem3204761) (@lem3204760 A x)). Qed.
Lemma lem3204764 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3204765 {A : Type'} (x : A) : (term11 A x) = True.
Proof. exact (TRANS (@lem3204762 A x) (@lem3204764)). Qed.
Lemma lem3204766 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun x : A => @lem3204765 A x)). Qed.
Lemma lem3204767 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3204768 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3204767 A) (@lem3204766 A)). Qed.
Lemma lem3204770 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3204771 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (@lem3204770 A t). Qed.
Lemma lem3204772 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3204771 A True). Qed.
Lemma lem3204773 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3204768 A) (@lem3204772 A)). Qed.
Lemma lem3204774 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3204773 A)). Qed.
Lemma lem3204775 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3204774 A) (@lem0)). Qed.

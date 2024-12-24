Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import option_INJ_term_abbrevs.
Require Import thm0_spec.
Require Import thm1073843_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1074715 {A : Type'} (a : A) : term0 A a.
Proof. exact (@lem1073843 A a). Qed.
Lemma lem1074716 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem1074717 {A : Type'} (a : A) : term1 A a.
Proof. exact (EQ_MP (@lem1074716 A a) (@lem1074715 A a)). Qed.
Lemma lem1074718 {A : Type'} (a : A) (a' : A) : term2 A a a'.
Proof. exact (@lem1074717 A a a'). Qed.
Lemma lem1074719 {A : Type'} (a : A) (a' : A) : (term2 A a a') = (((@Some A a) = (@Some A a')) = (a = a')).
Proof. exact (eq_refl (term2 A a a')). Qed.
Lemma lem1074732 {A : Type'} (a : A) (a' : A) : ((@Some A a) = (@Some A a')) = (a = a').
Proof. exact (EQ_MP (@lem1074719 A a a') (@lem1074718 A a a')). Qed.
Lemma lem1074733 {A : Type'} (a : A) (a' : A) : ((@Some A a) = (@Some A a')) = (a = a').
Proof. exact (@lem1074732 A a a'). Qed.
Lemma lem1074734 {A : Type'} (a : A) (b : A) : ((@Some A a) = (@Some A b)) = (a = b).
Proof. exact (@lem1074733 A a b). Qed.
Lemma lem1074737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1074738 {A : Type'} (a : A) (b : A) : (term3 A a b) = (term4 A a b).
Proof. exact (MK_COMB (@lem1074737) (@lem1074734 A a b)). Qed.
Lemma lem1074741 {A : Type'} (a : A) (b : A) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem1074742 {A : Type'} (a : A) (b : A) : (((@Some A a) = (@Some A b)) = (a = b)) = ((a = b) = (a = b)).
Proof. exact (MK_COMB (@lem1074738 A a b) (@lem1074741 A a b)). Qed.
Lemma lem1074744 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1074745 (x : Prop) : (x = x) = True.
Proof. exact (@lem1074744 Prop x). Qed.
Lemma lem1074746 {A : Type'} (a : A) (b : A) : ((a = b) = (a = b)) = True.
Proof. exact (@lem1074745 (a = b)). Qed.
Lemma lem1074747 {A : Type'} (a : A) (b : A) : (((@Some A a) = (@Some A b)) = (a = b)) = True.
Proof. exact (TRANS (@lem1074742 A a b) (@lem1074746 A a b)). Qed.
Lemma lem1074748 {A : Type'} (a : A) : (term5 A a) = (term6 A).
Proof. exact (fun_ext (fun b : A => @lem1074747 A a b)). Qed.
Lemma lem1074749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1074750 {A : Type'} (a : A) : (term1 A a) = (term7 A).
Proof. exact (MK_COMB (@lem1074749 A) (@lem1074748 A a)). Qed.
Lemma lem1074752 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1074753 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem1074752 A t). Qed.
Lemma lem1074754 {A : Type'} : (term7 A) = True.
Proof. exact (@lem1074753 A True). Qed.
Lemma lem1074755 {A : Type'} (a : A) : (term1 A a) = True.
Proof. exact (TRANS (@lem1074750 A a) (@lem1074754 A)). Qed.
Lemma lem1074756 {A : Type'} : (term9 A) = (term6 A).
Proof. exact (fun_ext (fun a : A => @lem1074755 A a)). Qed.
Lemma lem1074757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1074758 {A : Type'} : (term10 A) = (term7 A).
Proof. exact (MK_COMB (@lem1074757 A) (@lem1074756 A)). Qed.
Lemma lem1074760 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1074761 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem1074760 A t). Qed.
Lemma lem1074762 {A : Type'} : (term7 A) = True.
Proof. exact (@lem1074761 A True). Qed.
Lemma lem1074763 {A : Type'} : (term10 A) = True.
Proof. exact (TRANS (@lem1074758 A) (@lem1074762 A)). Qed.
Lemma lem1074764 {A : Type'} : True = (term10 A).
Proof. exact (SYM (@lem1074763 A)). Qed.
Lemma lem1074765 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem1074764 A) (@lem0)). Qed.

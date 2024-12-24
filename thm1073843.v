Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073843_term_abbrevs.
Require Import option_RECURSION_spec.
Require Import thm32_spec.
Lemma lem1073768 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (h1). Qed.
Lemma lem1073769 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : term1 A _17544 a.
Proof. exact (@lem1073768 A _17544 h1 a). Qed.
Lemma lem1073770 {A : Type'} (_17544 : type1158 A) (a : A) : (term1 A _17544 a) = ((term2 A _17544 a) = a).
Proof. exact (eq_refl (term1 A _17544 a)). Qed.
Lemma lem1073771 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : (term2 A _17544 a) = a.
Proof. exact (EQ_MP (@lem1073770 A _17544 a) (@lem1073769 A a _17544 h1)). Qed.
Lemma lem1073772 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (fun a : A => @lem1073771 A a _17544 h1). Qed.
Lemma lem1073773 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (h1). Qed.
Lemma lem1073774 {A : Type'} (_17544 : type1158 A) : (term0 A _17544) = (term0 A _17544).
Proof. exact (prop_ext (fun h1 : term0 A _17544 => @lem1073772 A _17544 h1) (fun h1 : term0 A _17544 => @lem1073773 A _17544 h1)). Qed.
Lemma lem1073775 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (EQ_MP (@lem1073774 A _17544) (@lem1073773 A _17544 h1)). Qed.
Lemma lem1073776 {A Z : Type'} (NONE' : Z) : term3 A Z NONE'.
Proof. exact (@lem1070449 A Z NONE'). Qed.
Lemma lem1073777 {A Z : Type'} (NONE' : Z) : (term3 A Z NONE') = (term4 A Z NONE').
Proof. exact (eq_refl (term3 A Z NONE')). Qed.
Lemma lem1073778 {A Z : Type'} (NONE' : Z) : term4 A Z NONE'.
Proof. exact (EQ_MP (@lem1073777 A Z NONE') (@lem1073776 A Z NONE')). Qed.
Lemma lem1073779 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term5 A Z NONE' SOME'.
Proof. exact (@lem1073778 A Z NONE' SOME'). Qed.
Lemma lem1073780 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term5 A Z NONE' SOME') = (term6 A Z NONE' SOME').
Proof. exact (eq_refl (term5 A Z NONE' SOME')). Qed.
Lemma lem1073781 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term6 A Z NONE' SOME'.
Proof. exact (EQ_MP (@lem1073780 A Z NONE' SOME') (@lem1073779 A Z NONE' SOME')). Qed.
Lemma lem1073782 {A : Type'} (NONE' : A) (SOME' : A -> A) : term7 A NONE' SOME'.
Proof. exact (@lem1073781 A A NONE' SOME'). Qed.
Lemma lem1073783 {A : Type'} (NONE' : A) : term8 A NONE'.
Proof. exact (@lem1073782 A NONE' (term9 A)). Qed.
Lemma lem1073784 {A : Type'} (a : A) : (term10 A a) = a.
Proof. exact (eq_refl (term10 A a)). Qed.
Lemma lem1073785 {A : Type'} (fn : type1158 A) (a : A) : (term11 A fn a) = (term11 A fn a).
Proof. exact (eq_refl (term11 A fn a)). Qed.
Lemma lem1073786 {A : Type'} (fn : type1158 A) (a : A) : ((term2 A fn a) = (term10 A a)) = ((term2 A fn a) = a).
Proof. exact (MK_COMB (@lem1073785 A fn a) (@lem1073784 A a)). Qed.
Lemma lem1073787 {A : Type'} (fn : type1158 A) : (term12 A fn) = (term13 A fn).
Proof. exact (fun_ext (fun a : A => @lem1073786 A fn a)). Qed.
Lemma lem1073788 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073789 {A : Type'} (fn : type1158 A) : (term14 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1073788 A) (@lem1073787 A fn)). Qed.
Lemma lem1073790 {A : Type'} (fn : type1158 A) (NONE' : A) : (term15 A fn NONE') = (term15 A fn NONE').
Proof. exact (eq_refl (term15 A fn NONE')). Qed.
Lemma lem1073791 {A : Type'} (NONE' : A) (fn : type1158 A) : (term16 A NONE' fn) = (term17 A NONE' fn).
Proof. exact (MK_COMB (@lem1073790 A fn NONE') (@lem1073789 A fn)). Qed.
Lemma lem1073792 {A : Type'} (NONE' : A) : (term18 A NONE') = (term19 A NONE').
Proof. exact (fun_ext (fun fn : type1158 A => @lem1073791 A NONE' fn)). Qed.
Lemma lem1073793 {A : Type'} : (@ex ((option A) -> A)) = (@ex ((option A) -> A)).
Proof. exact (eq_refl (@ex ((option A) -> A))). Qed.
Lemma lem1073794 {A : Type'} (NONE' : A) : (term8 A NONE') = (term20 A NONE').
Proof. exact (MK_COMB (@lem1073793 A) (@lem1073792 A NONE')). Qed.
Lemma lem1073795 {A : Type'} (NONE' : A) : term20 A NONE'.
Proof. exact (EQ_MP (@lem1073794 A NONE') (@lem1073783 A NONE')). Qed.
Lemma lem1073796 {A : Type'} (NONE' : A) (_17544 : type1158 A) (h1 : term17 A NONE' _17544) : term17 A NONE' _17544.
Proof. exact (h1). Qed.
Lemma lem1073797 {A : Type'} (NONE' : A) (_17544 : type1158 A) (h1 : term17 A NONE' _17544) : term0 A _17544.
Proof. exact (proj2 (@lem1073796 A NONE' _17544 h1)). Qed.
Lemma lem1073799 {A : Type'} (NONE' : A) (_17544 : type1158 A) (h1 : term17 A NONE' _17544) : term21 A.
Proof. exact (ex_intro (term22 A) _17544 (@lem1073797 A NONE' _17544 h1)). Qed.
Lemma lem1073800 {A : Type'} (NONE' : A) (h1 : term20 A NONE') : term20 A NONE'.
Proof. exact (h1). Qed.
Lemma lem1073801 {A : Type'} (NONE' : A) (h1 : term20 A NONE') : term21 A.
Proof. exact (ex_elim (@lem1073800 A NONE' h1) (fun _17544 : type1158 A => fun h0 : term19 A NONE' _17544 => @lem1073799 A NONE' _17544 h0)). Qed.
Lemma lem1073802 {A : Type'} (NONE' : A) : (term20 A NONE') = (term21 A).
Proof. exact (prop_ext (fun h1 : term20 A NONE' => @lem1073801 A NONE' h1) (fun h1 : term21 A => @lem1073795 A NONE')). Qed.
Lemma lem1073803 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073802 A (@el A)) (@lem1073795 A (@el A))). Qed.
Lemma lem1073804 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term21 A.
Proof. exact (ex_intro (term22 A) _17544 (@lem1073775 A _17544 h1)). Qed.
Lemma lem1073805 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073806 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (ex_elim (@lem1073805 A h1) (fun _17544 : type1158 A => fun h0 : term22 A _17544 => @lem1073804 A _17544 h0)). Qed.
Lemma lem1073807 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073806 A h1) (fun h1 : term21 A => @lem1073803 A)). Qed.
Lemma lem1073808 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073807 A) (@lem1073803 A)). Qed.
Lemma lem1073811 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (h1). Qed.
Lemma lem1073812 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term21 A.
Proof. exact (ex_intro (term22 A) _17544 (@lem1073811 A _17544 h1)). Qed.
Lemma lem1073813 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073814 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (ex_elim (@lem1073813 A h1) (fun _17544 : type1158 A => fun h0 : term22 A _17544 => @lem1073812 A _17544 h0)). Qed.
Lemma lem1073815 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073814 A h1) (fun h1 : term21 A => @lem1073808 A)). Qed.
Lemma lem1073816 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073815 A) (@lem1073808 A)). Qed.
Lemma lem1073817 {A : Type'} (a : A) (a' : A) (h1 : (@Some A a) = (@Some A a')) : (@Some A a) = (@Some A a').
Proof. exact (h1). Qed.
Lemma lem1073818 {A : Type'} (_17544 : type1158 A) : _17544 = _17544.
Proof. exact (eq_refl _17544). Qed.
Lemma lem1073819 {A : Type'} (_17544 : type1158 A) (a : A) (a' : A) (h1 : (@Some A a) = (@Some A a')) : (term2 A _17544 a) = (term2 A _17544 a').
Proof. exact (MK_COMB (@lem1073818 A _17544) (@lem1073817 A a a' h1)). Qed.
Lemma lem1073820 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term0 A _17544.
Proof. exact (h1). Qed.
Lemma lem1073821 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : term1 A _17544 a.
Proof. exact (@lem1073820 A _17544 h1 a). Qed.
Lemma lem1073822 {A : Type'} (_17544 : type1158 A) (a : A) : (term1 A _17544 a) = ((term2 A _17544 a) = a).
Proof. exact (eq_refl (term1 A _17544 a)). Qed.
Lemma lem1073823 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : (term2 A _17544 a) = a.
Proof. exact (EQ_MP (@lem1073822 A _17544 a) (@lem1073821 A a _17544 h1)). Qed.
Lemma lem1073824 {A : Type'} (a' : A) (_17544 : type1158 A) (h1 : term0 A _17544) : (term2 A _17544 a') = a'.
Proof. exact (@lem1073823 A a' _17544 h1). Qed.
Lemma lem1073825 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : a = (term2 A _17544 a).
Proof. exact (SYM (@lem1073823 A a _17544 h1)). Qed.
Lemma lem1073826 {A : Type'} (_17544 : type1158 A) (a : A) (a' : A) (h1 : term0 A _17544) (h2 : (@Some A a) = (@Some A a')) : a = (term2 A _17544 a').
Proof. exact (TRANS (@lem1073825 A a _17544 h1) (@lem1073819 A _17544 a a' h2)). Qed.
Lemma lem1073829 {A : Type'} (_17544 : type1158 A) (a : A) (a' : A) (h1 : term0 A _17544) (h2 : (@Some A a) = (@Some A a')) : a = a'.
Proof. exact (TRANS (@lem1073826 A _17544 a a' h1 h2) (@lem1073824 A a' _17544 h1)). Qed.
Lemma lem1073830 {A : Type'} : (@Some A) = (@Some A).
Proof. exact (eq_refl (@Some A)). Qed.
Lemma lem1073831 {A : Type'} (a : A) (a' : A) (h1 : a = a') : a = a'.
Proof. exact (h1). Qed.
Lemma lem1073832 {A : Type'} (a : A) (a' : A) (h1 : a = a') : (@Some A a) = (@Some A a').
Proof. exact (MK_COMB (@lem1073830 A) (@lem1073831 A a a' h1)). Qed.
Lemma lem1073833 {A : Type'} (a : A) (a' : A) : term23 A a a'.
Proof. exact (fun h0 : a = a' => @lem1073832 A a a' h0). Qed.
Lemma lem1073834 {A : Type'} (a : A) (a' : A) (_17544 : type1158 A) (h1 : term0 A _17544) : term24 A a a'.
Proof. exact (fun h0 : (@Some A a) = (@Some A a') => @lem1073829 A _17544 a a' h1 h0). Qed.
Lemma lem1073835 {A : Type'} (a : A) (a' : A) (_17544 : type1158 A) (h1 : term0 A _17544) : term25 A a a'.
Proof. exact (conj (@lem1073834 A a a' _17544 h1) (@lem1073833 A a a')). Qed.
Lemma lem1073836 {A : Type'} (a : A) (a' : A) : (term25 A a a') = (((@Some A a) = (@Some A a')) = (a = a')).
Proof. exact (@lem32 ((@Some A a) = (@Some A a')) (a = a')). Qed.
Lemma lem1073837 {A : Type'} (a : A) (a' : A) (_17544 : type1158 A) (h1 : term0 A _17544) : ((@Some A a) = (@Some A a')) = (a = a').
Proof. exact (EQ_MP (@lem1073836 A a a') (@lem1073835 A a a' _17544 h1)). Qed.
Lemma lem1073838 {A : Type'} (a : A) (_17544 : type1158 A) (h1 : term0 A _17544) : term26 A a.
Proof. exact (fun a' : A => @lem1073837 A a a' _17544 h1). Qed.
Lemma lem1073839 {A : Type'} (_17544 : type1158 A) (h1 : term0 A _17544) : term27 A.
Proof. exact (fun a : A => @lem1073838 A a _17544 h1). Qed.
Lemma lem1073840 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073841 {A : Type'} (h1 : term21 A) : term27 A.
Proof. exact (ex_elim (@lem1073840 A h1) (fun _17544 : type1158 A => fun h0 : term22 A _17544 => @lem1073839 A _17544 h0)). Qed.
Lemma lem1073842 {A : Type'} : (term21 A) = (term27 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073841 A h1) (fun h1 : term27 A => @lem1073816 A)). Qed.
Lemma lem1073843 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem1073842 A) (@lem1073816 A)). Qed.

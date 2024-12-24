Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import sum_RECURSION_term_abbrevs.
Require Import CONSTR_REC_spec.
Require Import FST_spec.
Require Import SND_spec.
Require Import thm1066561_spec.
Require Import thm1066562_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm1066938_spec.
Require Import thm1066989_spec.
Require Import thm1066993_spec.
Require Import thm1067676_spec.
Require Import thm1067682_spec.
Require Import thm9102_spec.
Lemma lem1067806 {A B Z : Type'} (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : fn = (term0 A B Z fn').
Proof. exact (h1). Qed.
Lemma lem1067807 {A B Z : Type'} (a : A) (INL' : type1431 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term3 A B Z fn' INL' a).
Proof. exact (MK_COMB (@lem1067806 A B Z fn fn' h2) (@lem1067676 A B a INL' h1)). Qed.
Lemma lem1067808 {A B Z : Type'} (a : B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INR' = (term4 A B)) (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term6 A B Z fn' INR' a).
Proof. exact (MK_COMB (@lem1067806 A B Z fn fn' h2) (@lem1067682 A B a INR' h1)). Qed.
Lemma lem1067809 {A B Z : Type'} (fn : type1332 A B Z) (INL' : type1431 A B) (a : A) : (term3 A B Z fn INL' a) = (term7 A B Z fn INL' a).
Proof. exact (eq_refl (term3 A B Z fn INL' a)). Qed.
Lemma lem1067810 {A B Z : Type'} (a : A) (INL' : type1431 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term7 A B Z fn' INL' a).
Proof. exact (TRANS (@lem1067807 A B Z a INL' fn fn' h1 h2) (@lem1067809 A B Z fn' INL' a)). Qed.
Lemma lem1067811 {A B Z : Type'} (fn : type1332 A B Z) (INR' : type1479 A B) (a : B) : (term6 A B Z fn INR' a) = (term8 A B Z fn INR' a).
Proof. exact (eq_refl (term6 A B Z fn INR' a)). Qed.
Lemma lem1067812 {A B Z : Type'} (a : B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INR' = (term4 A B)) (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term8 A B Z fn' INR' a).
Proof. exact (TRANS (@lem1067808 A B Z a INR' fn fn' h1 h2) (@lem1067811 A B Z fn' INR' a)). Qed.
Lemma lem1067820 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term10 A B sum' INR'.
Proof. exact (proj2 (@lem1066938 A B sum' INL' INR' h1)). Qed.
Lemma lem1067821 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term11 A B sum' INL'.
Proof. exact (proj1 (@lem1066938 A B sum' INL' INR' h1)). Qed.
Lemma lem1067822 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term12 A B sum' INL' a.
Proof. exact (@lem1067821 A B sum' INL' INR' h1 a). Qed.
Lemma lem1067823 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term12 A B sum' INL' a) = (term13 A B sum' INL' a).
Proof. exact (eq_refl (term12 A B sum' INL' a)). Qed.
Lemma lem1067826 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term13 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1067823 A B sum' INL' a) (@lem1067822 A B a sum' INL' INR' h1)). Qed.
Lemma lem1067827 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term13 A B sum' INL' a.
Proof. exact (@lem1067826 A B a sum' INL' INR' h1). Qed.
Lemma lem1067829 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (sum' r) = ((term14 A B r) = r).
Proof. exact (TRANS (@lem1066993 A B r sum' INL' INR' h1 h2 h3) (@lem1066989 A B r)). Qed.
Lemma lem1067830 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (sum' r) = ((term14 A B r) = r).
Proof. exact (@lem1067829 A B r sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067831 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term13 A B sum' INL' a) = ((term15 A B INL' a) = (INL' a)).
Proof. exact (@lem1067830 A B (INL' a) sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067832 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term15 A B INL' a) = (INL' a).
Proof. exact (EQ_MP (@lem1067831 A B a sum' INL' INR' h1 h2 h3) (@lem1067827 A B a sum' INL' INR' h3)). Qed.
Lemma lem1067833 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term16 A B sum' INR' a.
Proof. exact (@lem1067820 A B sum' INL' INR' h1 a). Qed.
Lemma lem1067834 {A B : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : B) : (term16 A B sum' INR' a) = (term17 A B sum' INR' a).
Proof. exact (eq_refl (term16 A B sum' INR' a)). Qed.
Lemma lem1067837 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term17 A B sum' INR' a.
Proof. exact (EQ_MP (@lem1067834 A B sum' INR' a) (@lem1067833 A B a sum' INL' INR' h1)). Qed.
Lemma lem1067838 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term9 A B INL' INR')) : term17 A B sum' INR' a.
Proof. exact (@lem1067837 A B a sum' INL' INR' h1). Qed.
Lemma lem1067840 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (sum' r) = ((term14 A B r) = r).
Proof. exact (TRANS (@lem1066993 A B r sum' INL' INR' h1 h2 h3) (@lem1066989 A B r)). Qed.
Lemma lem1067841 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (sum' r) = ((term14 A B r) = r).
Proof. exact (@lem1067840 A B r sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067842 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term17 A B sum' INR' a) = ((term18 A B INR' a) = (INR' a)).
Proof. exact (@lem1067841 A B (INR' a) sum' INL' INR' h1 h2 h3). Qed.
Lemma lem1067843 {A B : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term18 A B INR' a) = (INR' a).
Proof. exact (EQ_MP (@lem1067842 A B a sum' INL' INR' h1 h2 h3) (@lem1067838 A B a sum' INL' INR' h3)). Qed.
Lemma lem1067844 {A B Z : Type'} (fn : type1332 A B Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1067845 {A B Z : Type'} (fn : type1332 A B Z) (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term7 A B Z fn INL' a) = (term19 A B Z fn INL' a).
Proof. exact (MK_COMB (@lem1067844 A B Z fn) (@lem1067832 A B a sum' INL' INR' h1 h2 h3)). Qed.
Lemma lem1067846 {A B Z : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) (h4 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term19 A B Z fn' INL' a).
Proof. exact (TRANS (@lem1067810 A B Z a INL' fn fn' h1 h4) (@lem1067845 A B Z fn' a sum' INL' INR' h1 h2 h3)). Qed.
Lemma lem1067847 {A B Z : Type'} (fn : type1332 A B Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1067848 {A B Z : Type'} (fn : type1332 A B Z) (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) : (term8 A B Z fn INR' a) = (term20 A B Z fn INR' a).
Proof. exact (MK_COMB (@lem1067847 A B Z fn) (@lem1067843 A B a sum' INL' INR' h1 h2 h3)). Qed.
Lemma lem1067849 {A B Z : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) (h4 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term20 A B Z fn' INR' a).
Proof. exact (TRANS (@lem1067812 A B Z a INR' fn fn' h2 h4) (@lem1067848 A B Z fn' a sum' INL' INR' h1 h2 h3)). Qed.
Lemma lem1067850 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : INL' = (term1 A B).
Proof. exact (h1). Qed.
Lemma lem1067851 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1067852 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : (INL' a) = (term21 A B a).
Proof. exact (MK_COMB (@lem1067850 A B INL' h1) (@lem1067851 A a)). Qed.
Lemma lem1067853 {A B : Type'} (a : A) : (term21 A B a) = (term22 A B a).
Proof. exact (eq_refl (term21 A B a)). Qed.
Lemma lem1067854 {A B : Type'} (INL' : type1431 A B) (a : A) : (term23 A B INL' a) = (term23 A B INL' a).
Proof. exact (eq_refl (term23 A B INL' a)). Qed.
Lemma lem1067855 {A B : Type'} (INL' : type1431 A B) (a : A) : ((INL' a) = (term21 A B a)) = ((INL' a) = (term22 A B a)).
Proof. exact (MK_COMB (@lem1067854 A B INL' a) (@lem1067853 A B a)). Qed.
Lemma lem1067856 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : (INL' a) = (term22 A B a).
Proof. exact (EQ_MP (@lem1067855 A B INL' a) (@lem1067852 A B a INL' h1)). Qed.
Lemma lem1067857 {A B Z : Type'} (fn : type1332 A B Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1067858 {A B Z : Type'} (fn : type1332 A B Z) (a : A) (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : (term19 A B Z fn INL' a) = (term24 A B Z fn a).
Proof. exact (MK_COMB (@lem1067857 A B Z fn) (@lem1067856 A B a INL' h1)). Qed.
Lemma lem1067859 {A B Z : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) (h4 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term24 A B Z fn' a).
Proof. exact (TRANS (@lem1067846 A B Z a sum' INL' INR' fn fn' h1 h2 h3 h4) (@lem1067858 A B Z fn' a INL' h1)). Qed.
Lemma lem1067860 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term4 A B)) : INR' = (term4 A B).
Proof. exact (h1). Qed.
Lemma lem1067861 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1067862 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term4 A B)) : (INR' a) = (term25 A B a).
Proof. exact (MK_COMB (@lem1067860 A B INR' h1) (@lem1067861 B a)). Qed.
Lemma lem1067863 {A B : Type'} (a : B) : (term25 A B a) = (term26 A B a).
Proof. exact (eq_refl (term25 A B a)). Qed.
Lemma lem1067864 {A B : Type'} (INR' : type1479 A B) (a : B) : (term27 A B INR' a) = (term27 A B INR' a).
Proof. exact (eq_refl (term27 A B INR' a)). Qed.
Lemma lem1067865 {A B : Type'} (INR' : type1479 A B) (a : B) : ((INR' a) = (term25 A B a)) = ((INR' a) = (term26 A B a)).
Proof. exact (MK_COMB (@lem1067864 A B INR' a) (@lem1067863 A B a)). Qed.
Lemma lem1067866 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term4 A B)) : (INR' a) = (term26 A B a).
Proof. exact (EQ_MP (@lem1067865 A B INR' a) (@lem1067862 A B a INR' h1)). Qed.
Lemma lem1067867 {A B Z : Type'} (fn : type1332 A B Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1067868 {A B Z : Type'} (fn : type1332 A B Z) (a : B) (INR' : type1479 A B) (h1 : INR' = (term4 A B)) : (term20 A B Z fn INR' a) = (term28 A B Z fn a).
Proof. exact (MK_COMB (@lem1067867 A B Z fn) (@lem1067866 A B a INR' h1)). Qed.
Lemma lem1067869 {A B Z : Type'} (a : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) (h4 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term28 A B Z fn' a).
Proof. exact (TRANS (@lem1067849 A B Z a sum' INL' INR' fn fn' h1 h2 h3 h4) (@lem1067868 A B Z fn' a INR' h2)). Qed.
Lemma lem1067870 {A B Z : Type'} (a : A) (a' : B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : sum' = (term9 A B INL' INR')) (h4 : fn = (term0 A B Z fn')) : term29 A B Z a fn fn' a'.
Proof. exact (conj (@lem1067859 A B Z a sum' INL' INR' fn fn' h1 h2 h3 h4) (@lem1067869 A B Z a' sum' INL' INR' fn fn' h1 h2 h3 h4)). Qed.
Lemma lem1067871 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (INL' : type1431 A B) (INR' : type1479 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : INR' = (term4 A B)) (h3 : fn = (term0 A B Z fn')) : term30 A B Z sum' INL' INR' a fn fn' a'.
Proof. exact (fun h0 : sum' = (term9 A B INL' INR') => @lem1067870 A B Z a a' sum' INL' INR' fn fn' h1 h2 h0 h3). Qed.
Lemma lem1067872 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (eq_refl (term4 A B)). Qed.
Lemma lem1067873 {A B Z : Type'} (sum' : type1333 A B) (INR' : type1479 A B) (a : A) (a' : B) (INL' : type1431 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : fn = (term0 A B Z fn')) : term31 A B Z sum' INL' INR' a fn fn' a'.
Proof. exact (fun h0 : INR' = (term4 A B) => @lem1067871 A B Z sum' a a' INL' INR' fn fn' h1 h0 h2). Qed.
Lemma lem1067874 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (INL' : type1431 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : fn = (term0 A B Z fn')) : term32 A B Z sum' INL' a fn fn' a'.
Proof. exact (@lem1067873 A B Z sum' (term4 A B) a a' INL' fn fn' h1 h2). Qed.
Lemma lem1067875 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (INL' : type1431 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : INL' = (term1 A B)) (h2 : fn = (term0 A B Z fn')) : term33 A B Z sum' INL' a fn fn' a'.
Proof. exact (@lem1067874 A B Z sum' a a' INL' fn fn' h1 h2 (@lem1067872 A B)). Qed.
Lemma lem1067876 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (eq_refl (term1 A B)). Qed.
Lemma lem1067877 {A B Z : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term34 A B Z sum' INL' a fn fn' a'.
Proof. exact (fun h0 : INL' = (term1 A B) => @lem1067875 A B Z sum' a a' INL' fn fn' h0 h1). Qed.
Lemma lem1067878 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term35 A B Z sum' a fn fn' a'.
Proof. exact (@lem1067877 A B Z sum' (term1 A B) a a' fn fn' h1). Qed.
Lemma lem1067879 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term36 A B Z sum' a fn fn' a'.
Proof. exact (@lem1067878 A B Z sum' a a' fn fn' h1 (@lem1067876 A B)). Qed.
Lemma lem1067880 {A B : Type'} (sum' : type1333 A B) (h1 : sum' = (term37 A B)) : sum' = (term37 A B).
Proof. exact (h1). Qed.
Lemma lem1067881 {A B Z : Type'} (a : A) (a' : B) (sum' : type1333 A B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : sum' = (term37 A B)) (h2 : fn = (term0 A B Z fn')) : term29 A B Z a fn fn' a'.
Proof. exact (@lem1067879 A B Z sum' a a' fn fn' h2 (@lem1067880 A B sum' h1)). Qed.
Lemma lem1067882 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (eq_refl (term37 A B)). Qed.
Lemma lem1067883 {A B Z : Type'} (sum' : type1333 A B) (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term36 A B Z sum' a fn fn' a'.
Proof. exact (fun h0 : sum' = (term37 A B) => @lem1067881 A B Z a a' sum' fn fn' h0 h1). Qed.
Lemma lem1067884 {A B Z : Type'} (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term38 A B Z a fn fn' a'.
Proof. exact (@lem1067883 A B Z (term37 A B) a a' fn fn' h1). Qed.
Lemma lem1067885 {A B Z : Type'} (a : A) (a' : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : term29 A B Z a fn fn' a'.
Proof. exact (@lem1067884 A B Z a a' fn fn' h1 (@lem1067882 A B)). Qed.
Lemma lem1067900 {A B Z : Type'} : term39 A B Z.
Proof. exact (@lem1065430 (prod A B) Z). Qed.
Lemma lem1067901 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term40 A B Z INL' INR'.
Proof. exact (@lem1067900 A B Z (term41 A B Z INL' INR')). Qed.
Lemma lem1067902 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term40 A B Z INL' INR') = (term42 A B Z INL' INR').
Proof. exact (eq_refl (term40 A B Z INL' INR')). Qed.
Lemma lem1067903 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term42 A B Z INL' INR'.
Proof. exact (EQ_MP (@lem1067902 A B Z INL' INR') (@lem1067901 A B Z INL' INR')). Qed.
Lemma lem1067904 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term43 A B Z INL' INR' fn.
Proof. exact (h1). Qed.
Lemma lem1067905 {A B Z : Type'} (c : nat) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term44 A B Z INL' INR' fn c.
Proof. exact (@lem1067904 A B Z INL' INR' fn h1 c). Qed.
Lemma lem1067906 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (c : nat) (fn : type1332 A B Z) : (term44 A B Z INL' INR' fn c) = (term45 A B Z INL' INR' c fn).
Proof. exact (eq_refl (term44 A B Z INL' INR' fn c)). Qed.
Lemma lem1067907 {A B Z : Type'} (c : nat) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term45 A B Z INL' INR' c fn.
Proof. exact (EQ_MP (@lem1067906 A B Z INL' INR' c fn) (@lem1067905 A B Z c INL' INR' fn h1)). Qed.
Lemma lem1067908 {A B Z : Type'} (c : nat) (i : prod A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term46 A B Z INL' INR' c fn i.
Proof. exact (@lem1067907 A B Z c INL' INR' fn h1 i). Qed.
Lemma lem1067909 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (c : nat) (i : prod A B) (fn : type1332 A B Z) : (term46 A B Z INL' INR' c fn i) = (term47 A B Z INL' INR' c i fn).
Proof. exact (eq_refl (term46 A B Z INL' INR' c fn i)). Qed.
Lemma lem1067910 {A B Z : Type'} (c : nat) (i : prod A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term47 A B Z INL' INR' c i fn.
Proof. exact (EQ_MP (@lem1067909 A B Z INL' INR' c i fn) (@lem1067908 A B Z c i INL' INR' fn h1)). Qed.
Lemma lem1067911 {A B Z : Type'} (c : nat) (i : prod A B) (r : type1612 A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term48 A B Z INL' INR' c i fn r.
Proof. exact (@lem1067910 A B Z c i INL' INR' fn h1 r). Qed.
Lemma lem1067912 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (c : nat) (i : prod A B) (fn : type1332 A B Z) (r : type1612 A B) : (term48 A B Z INL' INR' c i fn r) = ((term49 A B Z fn c i r) = (term50 A B Z INL' INR' c i fn r)).
Proof. exact (eq_refl (term48 A B Z INL' INR' c i fn r)). Qed.
Lemma lem1067945 {A B : Type'} (x : A) : term51 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1067946 {A B : Type'} (x : A) : (term51 A B x) = (term52 A B x).
Proof. exact (eq_refl (term51 A B x)). Qed.
Lemma lem1067947 {A B : Type'} (x : A) : term52 A B x.
Proof. exact (EQ_MP (@lem1067946 A B x) (@lem1067945 A B x)). Qed.
Lemma lem1067948 {A B : Type'} (x : A) (y : B) : term53 A B x y.
Proof. exact (@lem1067947 A B x y). Qed.
Lemma lem1067949 {A B : Type'} (x : A) (y : B) : (term53 A B x y) = ((term54 A B x y) = y).
Proof. exact (eq_refl (term53 A B x y)). Qed.
Lemma lem1067951 {A B : Type'} (x : A) : term55 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1067952 {A B : Type'} (x : A) : (term55 A B x) = (term56 A B x).
Proof. exact (eq_refl (term55 A B x)). Qed.
Lemma lem1067953 {A B : Type'} (x : A) : term56 A B x.
Proof. exact (EQ_MP (@lem1067952 A B x) (@lem1067951 A B x)). Qed.
Lemma lem1067954 {A B : Type'} (x : A) (y : B) : term57 A B x y.
Proof. exact (@lem1067953 A B x y). Qed.
Lemma lem1067955 {A B : Type'} (y : B) (x : A) : (term57 A B x y) = ((term58 A B x y) = x).
Proof. exact (eq_refl (term57 A B x y)). Qed.
Lemma lem1067957 {A B Z : Type'} (a : B) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term28 A B Z fn' a).
Proof. exact (proj2 (@lem1067885 A B Z (@el A) a fn fn' h1)). Qed.
Lemma lem1067958 {A B Z : Type'} (a : A) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term24 A B Z fn' a).
Proof. exact (proj1 (@lem1067885 A B Z a (@el B) fn fn' h1)). Qed.
Lemma lem1067960 {A B Z : Type'} (c : nat) (i : prod A B) (r : type1612 A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term49 A B Z fn c i r) = (term50 A B Z INL' INR' c i fn r).
Proof. exact (EQ_MP (@lem1067912 A B Z INL' INR' c i fn r) (@lem1067911 A B Z c i r INL' INR' fn h1)). Qed.
Lemma lem1067961 {A B Z : Type'} (c : nat) (i : prod A B) (r : type1612 A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term49 A B Z fn c i r) = (term50 A B Z INL' INR' c i fn r).
Proof. exact (@lem1067960 A B Z c i r INL' INR' fn h1). Qed.
Lemma lem1067962 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term24 A B Z fn a) = (term59 A B Z INL' INR' a fn).
Proof. exact (@lem1067961 A B Z (NUMERAL 0) (term60 A B a) (term61 A B) INL' INR' fn h1). Qed.
Lemma lem1067963 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term59 A B Z INL' INR' a fn').
Proof. exact (TRANS (@lem1067958 A B Z a fn fn' h2) (@lem1067962 A B Z a INL' INR' fn' h1)). Qed.
Lemma lem1067965 {A : Type'} (f : nat -> A) (a : A) : (term62 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1067966 {A B Z : Type'} (f : type1588 A B Z) (a : type1203 A B Z) : (term63 A B Z a f) = a.
Proof. exact (@lem1067965 (type1203 A B Z) f a). Qed.
Lemma lem1067969 {A B Z : Type'} (INR' : B -> Z) (INL' : A -> Z) : (term64 A B Z INL' INR') = (term65 A B Z INL').
Proof. exact (@lem1067966 A B Z (term66 A B Z INR') (term65 A B Z INL')). Qed.
Lemma lem1067970 {A B : Type'} (a : A) : (term60 A B a) = (term60 A B a).
Proof. exact (eq_refl (term60 A B a)). Qed.
Lemma lem1067971 {A B Z : Type'} (INR' : B -> Z) (INL' : A -> Z) (a : A) : (term67 A B Z INL' INR' a) = (term68 A B Z INL' a).
Proof. exact (MK_COMB (@lem1067969 A B Z INR' INL') (@lem1067970 A B a)). Qed.
Lemma lem1067972 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (eq_refl (term61 A B)). Qed.
Lemma lem1067973 {A B Z : Type'} (INR' : B -> Z) (INL' : A -> Z) (a : A) : (term69 A B Z INL' INR' a) = (term70 A B Z INL' a).
Proof. exact (MK_COMB (@lem1067971 A B Z INR' INL' a) (@lem1067972 A B)). Qed.
Lemma lem1067974 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1067975 {A B Z : Type'} (INR' : B -> Z) (INL' : A -> Z) (a : A) (fn : type1332 A B Z) : (term59 A B Z INL' INR' a fn) = (term72 A B Z INL' a fn).
Proof. exact (MK_COMB (@lem1067973 A B Z INR' INL' a) (@lem1067974 A B Z fn)). Qed.
Lemma lem1067976 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term72 A B Z INL' a fn').
Proof. exact (TRANS (@lem1067963 A B Z a INL' INR' fn fn' h1 h2) (@lem1067975 A B Z INR' INL' a fn')). Qed.
Lemma lem1067977 {A B Z : Type'} (INL' : A -> Z) (a : A) : (term68 A B Z INL' a) = (term73 A B Z INL' a).
Proof. exact (eq_refl (term68 A B Z INL' a)). Qed.
Lemma lem1067978 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (eq_refl (term61 A B)). Qed.
Lemma lem1067979 {A B Z : Type'} (INL' : A -> Z) (a : A) : (term70 A B Z INL' a) = (term74 A B Z INL' a).
Proof. exact (MK_COMB (@lem1067977 A B Z INL' a) (@lem1067978 A B)). Qed.
Lemma lem1067980 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1067981 {A B Z : Type'} (INL' : A -> Z) (a : A) (fn : type1332 A B Z) : (term72 A B Z INL' a fn) = (term75 A B Z INL' a fn).
Proof. exact (MK_COMB (@lem1067979 A B Z INL' a) (@lem1067980 A B Z fn)). Qed.
Lemma lem1067982 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term75 A B Z INL' a fn').
Proof. exact (TRANS (@lem1067976 A B Z a INL' INR' fn fn' h1 h2) (@lem1067981 A B Z INL' a fn')). Qed.
Lemma lem1067983 {A B Z : Type'} (INL' : A -> Z) (a : A) : (term74 A B Z INL' a) = (term76 A B Z INL' a).
Proof. exact (eq_refl (term74 A B Z INL' a)). Qed.
Lemma lem1067984 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1067985 {A B Z : Type'} (INL' : A -> Z) (a : A) (fn : type1332 A B Z) : (term75 A B Z INL' a fn) = (term77 A B Z INL' a fn).
Proof. exact (MK_COMB (@lem1067983 A B Z INL' a) (@lem1067984 A B Z fn)). Qed.
Lemma lem1067986 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term77 A B Z INL' a fn').
Proof. exact (TRANS (@lem1067982 A B Z a INL' INR' fn fn' h1 h2) (@lem1067985 A B Z INL' a fn')). Qed.
Lemma lem1067987 {A B Z : Type'} (fn : type1332 A B Z) (INL' : A -> Z) (a : A) : (term77 A B Z INL' a fn) = (term78 A B Z INL' a).
Proof. exact (eq_refl (term77 A B Z INL' a fn)). Qed.
Lemma lem1067988 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (term78 A B Z INL' a).
Proof. exact (TRANS (@lem1067986 A B Z a INL' INR' fn fn' h1 h2) (@lem1067987 A B Z fn' INL' a)). Qed.
Lemma lem1067990 {A B : Type'} (y : B) (x : A) : (term58 A B x y) = x.
Proof. exact (EQ_MP (@lem1067955 A B y x) (@lem1067954 A B x y)). Qed.
Lemma lem1067991 {A B : Type'} (y : B) (x : A) : (term58 A B x y) = x.
Proof. exact (@lem1067990 A B y x). Qed.
Lemma lem1067992 {A B : Type'} (a : A) : (term79 A B a) = a.
Proof. exact (@lem1067991 A B (term80 B) a). Qed.
Lemma lem1067993 {A Z : Type'} (INL' : A -> Z) : INL' = INL'.
Proof. exact (eq_refl INL'). Qed.
Lemma lem1067994 {A B Z : Type'} (INL' : A -> Z) (a : A) : (term78 A B Z INL' a) = (INL' a).
Proof. exact (MK_COMB (@lem1067993 A Z INL') (@lem1067992 A B a)). Qed.
Lemma lem1067995 {A B Z : Type'} (fn : type9 A B Z) (a : A) : (term81 A B Z fn a) = (term81 A B Z fn a).
Proof. exact (eq_refl (term81 A B Z fn a)). Qed.
Lemma lem1067996 {A B Z : Type'} (fn : type9 A B Z) (INL' : A -> Z) (a : A) : ((term2 A B Z fn a) = (term78 A B Z INL' a)) = ((term2 A B Z fn a) = (INL' a)).
Proof. exact (MK_COMB (@lem1067995 A B Z fn a) (@lem1067994 A B Z INL' a)). Qed.
Lemma lem1067997 {A B Z : Type'} (a : A) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term2 A B Z fn a) = (INL' a).
Proof. exact (EQ_MP (@lem1067996 A B Z fn INL' a) (@lem1067988 A B Z a INL' INR' fn fn' h1 h2)). Qed.
Lemma lem1067998 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : term82 A B Z fn INL'.
Proof. exact (fun a : A => @lem1067997 A B Z a INL' INR' fn fn' h1 h2). Qed.
Lemma lem1068000 {A B Z : Type'} (c : nat) (i : prod A B) (r : type1612 A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term49 A B Z fn c i r) = (term50 A B Z INL' INR' c i fn r).
Proof. exact (EQ_MP (@lem1067912 A B Z INL' INR' c i fn r) (@lem1067911 A B Z c i r INL' INR' fn h1)). Qed.
Lemma lem1068001 {A B Z : Type'} (c : nat) (i : prod A B) (r : type1612 A B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term49 A B Z fn c i r) = (term50 A B Z INL' INR' c i fn r).
Proof. exact (@lem1068000 A B Z c i r INL' INR' fn h1). Qed.
Lemma lem1068002 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : (term28 A B Z fn a) = (term83 A B Z INL' INR' a fn).
Proof. exact (@lem1068001 A B Z term84 (term85 A B a) (term61 A B) INL' INR' fn h1). Qed.
Lemma lem1068003 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term83 A B Z INL' INR' a fn').
Proof. exact (TRANS (@lem1067957 A B Z a fn fn' h2) (@lem1068002 A B Z a INL' INR' fn' h1)). Qed.
Lemma lem1068005 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term86 A a f n) = (f n).
Proof. exact (EQ_MP (@lem1066562 A a f n) (@lem1066561 A a f n)). Qed.
Lemma lem1068006 {A B Z : Type'} (a : type1203 A B Z) (f : type1588 A B Z) (n : nat) : (term87 A B Z a f n) = (f n).
Proof. exact (@lem1068005 (type1203 A B Z) a f n). Qed.
Lemma lem1068007 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term88 A B Z INL' INR') = (term89 A B Z INR').
Proof. exact (@lem1068006 A B Z (term65 A B Z INL') (term66 A B Z INR') (NUMERAL 0)). Qed.
Lemma lem1068009 {A : Type'} (f : nat -> A) (a : A) : (term62 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1068010 {A B Z : Type'} (f : type1588 A B Z) (a : type1203 A B Z) : (term63 A B Z a f) = a.
Proof. exact (@lem1068009 (type1203 A B Z) f a). Qed.
Lemma lem1068013 {A B Z : Type'} (INR' : B -> Z) : (term89 A B Z INR') = (term90 A B Z INR').
Proof. exact (@lem1068010 A B Z (@FNIL ((prod A B) -> (nat -> recspace (prod A B)) -> (nat -> Z) -> Z)) (term90 A B Z INR')). Qed.
Lemma lem1068014 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term88 A B Z INL' INR') = (term90 A B Z INR').
Proof. exact (TRANS (@lem1068007 A B Z INL' INR') (@lem1068013 A B Z INR')). Qed.
Lemma lem1068015 {A B : Type'} (a : B) : (term85 A B a) = (term85 A B a).
Proof. exact (eq_refl (term85 A B a)). Qed.
Lemma lem1068016 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (a : B) : (term91 A B Z INL' INR' a) = (term92 A B Z INR' a).
Proof. exact (MK_COMB (@lem1068014 A B Z INL' INR') (@lem1068015 A B a)). Qed.
Lemma lem1068017 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (eq_refl (term61 A B)). Qed.
Lemma lem1068018 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (a : B) : (term93 A B Z INL' INR' a) = (term94 A B Z INR' a).
Proof. exact (MK_COMB (@lem1068016 A B Z INL' INR' a) (@lem1068017 A B)). Qed.
Lemma lem1068019 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1068020 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (a : B) (fn : type1332 A B Z) : (term83 A B Z INL' INR' a fn) = (term95 A B Z INR' a fn).
Proof. exact (MK_COMB (@lem1068018 A B Z INL' INR' a) (@lem1068019 A B Z fn)). Qed.
Lemma lem1068021 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term95 A B Z INR' a fn').
Proof. exact (TRANS (@lem1068003 A B Z a INL' INR' fn fn' h1 h2) (@lem1068020 A B Z INL' INR' a fn')). Qed.
Lemma lem1068022 {A B Z : Type'} (INR' : B -> Z) (a : B) : (term92 A B Z INR' a) = (term96 A B Z INR' a).
Proof. exact (eq_refl (term92 A B Z INR' a)). Qed.
Lemma lem1068023 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (eq_refl (term61 A B)). Qed.
Lemma lem1068024 {A B Z : Type'} (INR' : B -> Z) (a : B) : (term94 A B Z INR' a) = (term97 A B Z INR' a).
Proof. exact (MK_COMB (@lem1068022 A B Z INR' a) (@lem1068023 A B)). Qed.
Lemma lem1068025 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1068026 {A B Z : Type'} (INR' : B -> Z) (a : B) (fn : type1332 A B Z) : (term95 A B Z INR' a fn) = (term98 A B Z INR' a fn).
Proof. exact (MK_COMB (@lem1068024 A B Z INR' a) (@lem1068025 A B Z fn)). Qed.
Lemma lem1068027 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term98 A B Z INR' a fn').
Proof. exact (TRANS (@lem1068021 A B Z a INL' INR' fn fn' h1 h2) (@lem1068026 A B Z INR' a fn')). Qed.
Lemma lem1068028 {A B Z : Type'} (INR' : B -> Z) (a : B) : (term97 A B Z INR' a) = (term99 A B Z INR' a).
Proof. exact (eq_refl (term97 A B Z INR' a)). Qed.
Lemma lem1068029 {A B Z : Type'} (fn : type1332 A B Z) : (term71 A B Z fn) = (term71 A B Z fn).
Proof. exact (eq_refl (term71 A B Z fn)). Qed.
Lemma lem1068030 {A B Z : Type'} (INR' : B -> Z) (a : B) (fn : type1332 A B Z) : (term98 A B Z INR' a fn) = (term100 A B Z INR' a fn).
Proof. exact (MK_COMB (@lem1068028 A B Z INR' a) (@lem1068029 A B Z fn)). Qed.
Lemma lem1068031 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term100 A B Z INR' a fn').
Proof. exact (TRANS (@lem1068027 A B Z a INL' INR' fn fn' h1 h2) (@lem1068030 A B Z INR' a fn')). Qed.
Lemma lem1068032 {A B Z : Type'} (fn : type1332 A B Z) (INR' : B -> Z) (a : B) : (term100 A B Z INR' a fn) = (term101 A B Z INR' a).
Proof. exact (eq_refl (term100 A B Z INR' a fn)). Qed.
Lemma lem1068033 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (term101 A B Z INR' a).
Proof. exact (TRANS (@lem1068031 A B Z a INL' INR' fn fn' h1 h2) (@lem1068032 A B Z fn' INR' a)). Qed.
Lemma lem1068035 {A B : Type'} (x : A) (y : B) : (term54 A B x y) = y.
Proof. exact (EQ_MP (@lem1067949 A B x y) (@lem1067948 A B x y)). Qed.
Lemma lem1068036 {A B : Type'} (x : A) (y : B) : (term54 A B x y) = y.
Proof. exact (@lem1068035 A B x y). Qed.
Lemma lem1068037 {A B : Type'} (a : B) : (term102 A B a) = a.
Proof. exact (@lem1068036 A B (term80 A) a). Qed.
Lemma lem1068038 {B Z : Type'} (INR' : B -> Z) : INR' = INR'.
Proof. exact (eq_refl INR'). Qed.
Lemma lem1068039 {A B Z : Type'} (INR' : B -> Z) (a : B) : (term101 A B Z INR' a) = (INR' a).
Proof. exact (MK_COMB (@lem1068038 B Z INR') (@lem1068037 A B a)). Qed.
Lemma lem1068040 {A B Z : Type'} (fn : type9 A B Z) (a : B) : (term103 A B Z fn a) = (term103 A B Z fn a).
Proof. exact (eq_refl (term103 A B Z fn a)). Qed.
Lemma lem1068041 {A B Z : Type'} (fn : type9 A B Z) (INR' : B -> Z) (a : B) : ((term5 A B Z fn a) = (term101 A B Z INR' a)) = ((term5 A B Z fn a) = (INR' a)).
Proof. exact (MK_COMB (@lem1068040 A B Z fn a) (@lem1068039 A B Z INR' a)). Qed.
Lemma lem1068042 {A B Z : Type'} (a : B) (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : (term5 A B Z fn a) = (INR' a).
Proof. exact (EQ_MP (@lem1068041 A B Z fn INR' a) (@lem1068033 A B Z a INL' INR' fn fn' h1 h2)). Qed.
Lemma lem1068043 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : term104 A B Z fn INR'.
Proof. exact (fun a : B => @lem1068042 A B Z a INL' INR' fn fn' h1 h2). Qed.
Lemma lem1068044 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : term105 A B Z INL' fn INR'.
Proof. exact (conj (@lem1067998 A B Z INL' INR' fn fn' h1 h2) (@lem1068043 A B Z INL' INR' fn fn' h1 h2)). Qed.
Lemma lem1068045 {A B Z : Type'} (INL' : A -> Z) (fn : type9 A B Z) (INR' : B -> Z) : (term106 A B Z INL' INR' fn) = (term105 A B Z INL' fn INR').
Proof. exact (eq_refl (term106 A B Z INL' INR' fn)). Qed.
Lemma lem1068046 {A B Z : Type'} : term107 A B Z.
Proof. exact (@lem9102 (type9 A B Z)). Qed.
Lemma lem1068047 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term108 A B Z INL' INR'.
Proof. exact (@lem1068046 A B Z (term109 A B Z INL' INR')). Qed.
Lemma lem1068048 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term108 A B Z INL' INR') = (term110 A B Z INL' INR').
Proof. exact (eq_refl (term108 A B Z INL' INR')). Qed.
Lemma lem1068049 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term110 A B Z INL' INR'.
Proof. exact (EQ_MP (@lem1068048 A B Z INL' INR') (@lem1068047 A B Z INL' INR')). Qed.
Lemma lem1068050 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) : term111 A B Z INL' INR' fn.
Proof. exact (@lem1068049 A B Z INL' INR' (term0 A B Z fn)). Qed.
Lemma lem1068051 {A B Z : Type'} (fn : type1332 A B Z) (INL' : A -> Z) (INR' : B -> Z) : (term111 A B Z INL' INR' fn) = (term112 A B Z fn INL' INR').
Proof. exact (eq_refl (term111 A B Z INL' INR' fn)). Qed.
Lemma lem1068052 {A B Z : Type'} (fn : type1332 A B Z) (INL' : A -> Z) (INR' : B -> Z) : term112 A B Z fn INL' INR'.
Proof. exact (EQ_MP (@lem1068051 A B Z fn INL' INR') (@lem1068050 A B Z INL' INR' fn)). Qed.
Lemma lem1068053 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) : (term105 A B Z INL' fn INR') = (term106 A B Z INL' INR' fn).
Proof. exact (SYM (@lem1068045 A B Z INL' fn INR')). Qed.
Lemma lem1068054 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type9 A B Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') (h2 : fn = (term0 A B Z fn')) : term106 A B Z INL' INR' fn.
Proof. exact (EQ_MP (@lem1068053 A B Z INL' INR' fn) (@lem1068044 A B Z INL' INR' fn fn' h1 h2)). Qed.
Lemma lem1068055 {A B Z : Type'} (fn : type9 A B Z) (INL' : A -> Z) (INR' : B -> Z) (fn' : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn') : term113 A B Z fn' INL' INR' fn.
Proof. exact (fun h0 : fn = (term0 A B Z fn') => @lem1068054 A B Z INL' INR' fn fn' h1 h0). Qed.
Lemma lem1068056 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term114 A B Z fn INL' INR'.
Proof. exact (fun fn' : type9 A B Z => @lem1068055 A B Z fn' INL' INR' fn h1). Qed.
Lemma lem1068057 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) (fn : type1332 A B Z) (h1 : term43 A B Z INL' INR' fn) : term115 A B Z INL' INR'.
Proof. exact (@lem1068052 A B Z fn INL' INR' (@lem1068056 A B Z INL' INR' fn h1)). Qed.
Lemma lem1068058 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term115 A B Z INL' INR'.
Proof. exact (ex_elim (@lem1067903 A B Z INL' INR') (fun fn : type1332 A B Z => fun h0 : term116 A B Z INL' INR' fn => @lem1068057 A B Z INL' INR' fn h0)). Qed.
Lemma lem1068059 {A B Z : Type'} (INL' : A -> Z) : term117 A B Z INL'.
Proof. exact (fun INR' : B -> Z => @lem1068058 A B Z INL' INR'). Qed.
Lemma lem1068060 {A B Z : Type'} : term118 A B Z.
Proof. exact (fun INL' : A -> Z => @lem1068059 A B Z INL'). Qed.

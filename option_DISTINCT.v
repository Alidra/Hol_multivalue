Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import option_DISTINCT_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1073760_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm82_spec.
Lemma lem1074676 {A : Type'} (a' : A) : term0 A a'.
Proof. exact (@lem1073760 A a'). Qed.
Lemma lem1074677 {A : Type'} (a' : A) : (term0 A a') = (term1 A a').
Proof. exact (eq_refl (term0 A a')). Qed.
Lemma lem1074678 {A : Type'} (a' : A) : term1 A a'.
Proof. exact (EQ_MP (@lem1074677 A a') (@lem1074676 A a')). Qed.
Lemma lem1074682 {A : Type'} (a' : A) (h1 : (@None A) = (@Some A a')) : (@None A) = (@Some A a').
Proof. exact (h1). Qed.
Lemma lem1074683 {A : Type'} (a' : A) (h1 : (@None A) = (@Some A a')) : (@Some A a') = (@None A).
Proof. exact (SYM (@lem1074682 A a' h1)). Qed.
Lemma lem1074684 {A : Type'} (a' : A) (h1 : (@Some A a') = (@None A)) : (@Some A a') = (@None A).
Proof. exact (h1). Qed.
Lemma lem1074685 {A : Type'} (a' : A) (h1 : (@Some A a') = (@None A)) : (@None A) = (@Some A a').
Proof. exact (SYM (@lem1074684 A a' h1)). Qed.
Lemma lem1074686 {A : Type'} (a' : A) : ((@None A) = (@Some A a')) = ((@Some A a') = (@None A)).
Proof. exact (prop_ext (fun h1 : (@None A) = (@Some A a') => @lem1074683 A a' h1) (fun h1 : (@Some A a') = (@None A) => @lem1074685 A a' h1)). Qed.
Lemma lem1074687 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1074688 {A : Type'} (a' : A) : (term1 A a') = (term2 A a').
Proof. exact (MK_COMB (@lem1074687) (@lem1074686 A a')). Qed.
Lemma lem1074689 {A : Type'} (a' : A) : term2 A a'.
Proof. exact (EQ_MP (@lem1074688 A a') (@lem1074678 A a')). Qed.
Lemma lem1074690 {A : Type'} (a' : A) : term3 A a'.
Proof. exact (@lem82 ((@Some A a') = (@None A))). Qed.
Lemma lem1074697 {A : Type'} (a' : A) : ((@Some A a') = (@None A)) = False.
Proof. exact (@lem1074690 A a' (@lem1074689 A a')). Qed.
Lemma lem1074698 {A : Type'} (a' : A) : ((@Some A a') = (@None A)) = False.
Proof. exact (@lem1074697 A a'). Qed.
Lemma lem1074699 {A : Type'} (a : A) : ((@Some A a) = (@None A)) = False.
Proof. exact (@lem1074698 A a). Qed.
Lemma lem1074700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1074701 {A : Type'} (a : A) : (term2 A a) = (~ False).
Proof. exact (MK_COMB (@lem1074700) (@lem1074699 A a)). Qed.
Lemma lem1074703 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1074704 {A : Type'} (a : A) : (term2 A a) = True.
Proof. exact (TRANS (@lem1074701 A a) (@lem1074703)). Qed.
Lemma lem1074705 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem1074704 A a)). Qed.
Lemma lem1074706 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1074707 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem1074706 A) (@lem1074705 A)). Qed.
Lemma lem1074709 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1074710 {A : Type'} (t : Prop) : (term8 A t) = t.
Proof. exact (@lem1074709 A t). Qed.
Lemma lem1074711 {A : Type'} : (term7 A) = True.
Proof. exact (@lem1074710 A True). Qed.
Lemma lem1074712 {A : Type'} : (term6 A) = True.
Proof. exact (TRANS (@lem1074707 A) (@lem1074711 A)). Qed.
Lemma lem1074713 {A : Type'} : True = (term6 A).
Proof. exact (SYM (@lem1074712 A)). Qed.
Lemma lem1074714 {A : Type'} : term6 A.
Proof. exact (EQ_MP (@lem1074713 A) (@lem0)). Qed.

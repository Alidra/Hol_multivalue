Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COMPONENT_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Lemma lem3271992 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term0 A x y s) = (term1 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3271993 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term0 A x y s) = (term1 A y x s).
Proof. exact (@lem3271992 A y x s). Qed.
Lemma lem3271994 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term3 A x s).
Proof. exact (@lem3271993 A x x s). Qed.
Lemma lem3271998 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3271999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3271998 A x). Qed.
Lemma lem3272000 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3272001 {A : Type'} (x : A) : (term4 A x) = (or True).
Proof. exact (MK_COMB (@lem3272000) (@lem3271999 A x)). Qed.
Lemma lem3272003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3272004 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3272003 A P x). Qed.
Lemma lem3272005 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3272004 A s x). Qed.
Lemma lem3272006 {A : Type'} (s : A -> Prop) (x : A) : (term3 A x s) = (term5 A s x).
Proof. exact (MK_COMB (@lem3272001 A x) (@lem3272005 A s x)). Qed.
Lemma lem3272008 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3272009 {A : Type'} (s : A -> Prop) (x : A) : (term5 A s x) = True.
Proof. exact (@lem3272008 (s x)). Qed.
Lemma lem3272010 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = True.
Proof. exact (TRANS (@lem3272006 A s x) (@lem3272009 A s x)). Qed.
Lemma lem3272011 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = True.
Proof. exact (TRANS (@lem3271994 A x s) (@lem3272010 A x s)). Qed.
Lemma lem3272012 {A : Type'} (x : A) : (term6 A x) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3272011 A x s)). Qed.
Lemma lem3272013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3272014 {A : Type'} (x : A) : (term8 A x) = (term9 A).
Proof. exact (MK_COMB (@lem3272013 A) (@lem3272012 A x)). Qed.
Lemma lem3272016 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3272017 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem3272016 (A -> Prop) t). Qed.
Lemma lem3272018 {A : Type'} : (term9 A) = True.
Proof. exact (@lem3272017 A True). Qed.
Lemma lem3272019 {A : Type'} (x : A) : (term8 A x) = True.
Proof. exact (TRANS (@lem3272014 A x) (@lem3272018 A)). Qed.
Lemma lem3272020 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun x : A => @lem3272019 A x)). Qed.
Lemma lem3272021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3272022 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3272021 A) (@lem3272020 A)). Qed.
Lemma lem3272024 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3272025 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (@lem3272024 A t). Qed.
Lemma lem3272026 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3272025 A True). Qed.
Lemma lem3272027 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3272022 A) (@lem3272026 A)). Qed.
Lemma lem3272028 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3272027 A)). Qed.
Lemma lem3272030 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3272028 A) (@lem0)). Qed.

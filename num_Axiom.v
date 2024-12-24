Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_Axiom_term_abbrevs.
Require Import thm0_spec.
Require Import thm75360_spec.
Require Import thm75559_spec.
Lemma lem75588 : 0 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem75559) (@lem0)). Qed.
Lemma lem75589 {A : Type'} (fn : nat -> A) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem75590 {A : Type'} (fn : nat -> A) : (fn 0) = (term0 A fn).
Proof. exact (MK_COMB (@lem75589 A fn) (@lem75588)). Qed.
Lemma lem75591 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem75592 {A : Type'} (fn : nat -> A) : (term1 A fn) = (term2 A fn).
Proof. exact (MK_COMB (@lem75591 A) (@lem75590 A fn)). Qed.
Lemma lem75593 {A : Type'} (e : A) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem75594 {A : Type'} (fn : nat -> A) (e : A) : ((fn 0) = e) = ((term0 A fn) = e).
Proof. exact (MK_COMB (@lem75592 A fn) (@lem75593 A e)). Qed.
Lemma lem75595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem75596 {A : Type'} (fn : nat -> A) (e : A) : (term3 A fn e) = (term4 A fn e).
Proof. exact (MK_COMB (@lem75595) (@lem75594 A fn e)). Qed.
Lemma lem75597 {A : Type'} (f : type1423 A) (fn : nat -> A) : (term5 A f fn) = (term5 A f fn).
Proof. exact (eq_refl (term5 A f fn)). Qed.
Lemma lem75598 {A : Type'} (e : A) (f : type1423 A) (fn : nat -> A) : (term6 A e f fn) = (term7 A e f fn).
Proof. exact (MK_COMB (@lem75596 A fn e) (@lem75597 A f fn)). Qed.
Lemma lem75599 {A : Type'} (e : A) (f : type1423 A) : (term8 A e f) = (term9 A e f).
Proof. exact (fun_ext (fun fn : nat -> A => @lem75598 A e f fn)). Qed.
Lemma lem75600 {A : Type'} : (@ex1 (nat -> A)) = (@ex1 (nat -> A)).
Proof. exact (eq_refl (@ex1 (nat -> A))). Qed.
Lemma lem75601 {A : Type'} (e : A) (f : type1423 A) : (term10 A e f) = (term11 A e f).
Proof. exact (MK_COMB (@lem75600 A) (@lem75599 A e f)). Qed.
Lemma lem75602 {A : Type'} (e : A) : (term12 A e) = (term13 A e).
Proof. exact (fun_ext (fun f : type1423 A => @lem75601 A e f)). Qed.
Lemma lem75603 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem75604 {A : Type'} (e : A) : (term14 A e) = (term15 A e).
Proof. exact (MK_COMB (@lem75603 A) (@lem75602 A e)). Qed.
Lemma lem75605 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun e : A => @lem75604 A e)). Qed.
Lemma lem75606 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem75607 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem75606 A) (@lem75605 A)). Qed.
Lemma lem75608 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem75607 A) (@lem75360 A)). Qed.

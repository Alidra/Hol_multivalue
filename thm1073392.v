Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073392_term_abbrevs.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1073381 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1073382 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1073381 a). Qed.
Lemma lem1073383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1073384 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (MK_COMB (@lem1073383) (@lem1073382 a)). Qed.
Lemma lem1073385 (a : Prop) : (~ a) = (~ a).
Proof. exact (eq_refl (~ a)). Qed.
Lemma lem1073386 (a : Prop) : ((a -> False) = (~ a)) = ((~ a) = (~ a)).
Proof. exact (MK_COMB (@lem1073384 a) (@lem1073385 a)). Qed.
Lemma lem1073388 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1073389 (x : Prop) : (x = x) = True.
Proof. exact (@lem1073388 Prop x). Qed.
Lemma lem1073390 (a : Prop) : ((~ a) = (~ a)) = True.
Proof. exact (@lem1073389 (~ a)). Qed.
Lemma lem1073391 (a : Prop) : ((a -> False) = (~ a)) = True.
Proof. exact (TRANS (@lem1073386 a) (@lem1073390 a)). Qed.
Lemma lem1073392 (a : Prop) : True = ((a -> False) = (~ a)).
Proof. exact (SYM (@lem1073391 a)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18916_term_abbrevs.
Require Import OR_EXISTS_THM_spec.
Lemma lem18913 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5488 A P). Qed.
Lemma lem18914 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18915 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18914 A P) (@lem18913 A P)). Qed.
Lemma lem18916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18915 A P Q). Qed.

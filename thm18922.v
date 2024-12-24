Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18922_term_abbrevs.
Require Import LEFT_AND_EXISTS_THM_spec.
Lemma lem18919 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5881 A P). Qed.
Lemma lem18920 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18921 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18920 A P) (@lem18919 A P)). Qed.
Lemma lem18922 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem18921 A P Q). Qed.

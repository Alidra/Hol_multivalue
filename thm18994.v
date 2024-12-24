Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18994_term_abbrevs.
Require Import LEFT_OR_EXISTS_THM_spec.
Lemma lem18991 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5550 A P). Qed.
Lemma lem18992 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18993 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18992 A P) (@lem18991 A P)). Qed.
Lemma lem18994 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem18993 A P Q). Qed.

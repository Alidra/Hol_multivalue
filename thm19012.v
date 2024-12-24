Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19012_term_abbrevs.
Require Import LEFT_OR_FORALL_THM_spec.
Lemma lem19009 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem11733 A P). Qed.
Lemma lem19010 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem19011 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem19010 A P) (@lem19009 A P)). Qed.
Lemma lem19012 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem19011 A P Q). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19018_term_abbrevs.
Require Import RIGHT_AND_FORALL_THM_spec.
Lemma lem19015 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5348 A P). Qed.
Lemma lem19016 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem19017 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem19016 A P) (@lem19015 A P)). Qed.
Lemma lem19018 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem19017 A P Q). Qed.

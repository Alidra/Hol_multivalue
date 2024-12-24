Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19024_term_abbrevs.
Require Import LEFT_AND_FORALL_THM_spec.
Lemma lem19021 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5247 A P). Qed.
Lemma lem19022 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem19023 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem19022 A P) (@lem19021 A P)). Qed.
Lemma lem19024 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem19023 A P Q). Qed.

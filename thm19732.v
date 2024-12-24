Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19732_term_abbrevs.
Require Import SELECT_AX_spec.
Lemma lem19729 {A : Type'} : term0 A.
Proof. exact (@lem9221 A). Qed.
Lemma lem19730 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem19729 A P). Qed.
Lemma lem19731 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem19732 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem19731 A P) (@lem19730 A P)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19030_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Lemma lem19027 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem19028 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem19029 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem19028 A P) (@lem19027 A P)). Qed.
Lemma lem19030 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem19029 A P Q). Qed.

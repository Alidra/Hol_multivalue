Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19006_term_abbrevs.
Require Import RIGHT_OR_FORALL_THM_spec.
Lemma lem19003 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem11766 A P). Qed.
Lemma lem19004 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem19005 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem19004 A P) (@lem19003 A P)). Qed.
Lemma lem19006 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem19005 A P Q). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16451_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Lemma lem16448 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem16449 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem16450 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem16449 A P) (@lem16448 A P)). Qed.
Lemma lem16451 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem16450 A P Q). Qed.

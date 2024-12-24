Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16439_term_abbrevs.
Require Import LEFT_EXISTS_AND_THM_spec.
Lemma lem16436 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5682 A P). Qed.
Lemma lem16437 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem16438 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem16437 A P) (@lem16436 A P)). Qed.
Lemma lem16439 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem16438 A P Q). Qed.

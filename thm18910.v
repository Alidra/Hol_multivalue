Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18910_term_abbrevs.
Require Import RIGHT_OR_EXISTS_THM_spec.
Lemma lem18907 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5612 A P). Qed.
Lemma lem18908 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18909 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18908 A P) (@lem18907 A P)). Qed.
Lemma lem18910 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18909 A P Q). Qed.

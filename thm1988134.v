Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988134_term_abbrevs.
Require Import LEFT_AND_EXISTS_THM_spec.
Lemma lem1988131 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5881 A P). Qed.
Lemma lem1988132 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem1988133 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem1988132 A P) (@lem1988131 A P)). Qed.
Lemma lem1988134 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem1988133 A P Q). Qed.

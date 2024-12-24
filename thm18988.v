Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18988_term_abbrevs.
Require Import RIGHT_OR_EXISTS_THM_spec.
Lemma lem18985 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5612 A P). Qed.
Lemma lem18986 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18987 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18986 A P) (@lem18985 A P)). Qed.
Lemma lem18988 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18987 A P Q). Qed.

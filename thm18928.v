Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18928_term_abbrevs.
Require Import RIGHT_AND_EXISTS_THM_spec.
Lemma lem18925 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5950 A P). Qed.
Lemma lem18926 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18927 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18926 A P) (@lem18925 A P)). Qed.
Lemma lem18928 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18927 A P Q). Qed.

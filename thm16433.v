Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16433_term_abbrevs.
Require Import RIGHT_EXISTS_AND_THM_spec.
Lemma lem16430 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem16431 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem16432 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem16431 A P) (@lem16430 A P)). Qed.
Lemma lem16433 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem16432 A P Q). Qed.

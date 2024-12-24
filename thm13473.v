Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm13473_term_abbrevs.
Require Import COND_ELIM_THM_spec.
Lemma lem13473 {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13472 A _474 _475 _476 _477). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18940_term_abbrevs.
Require Import RIGHT_FORALL_OR_THM_spec.
Lemma lem18937 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem11700 A P). Qed.
Lemma lem18938 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18939 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18938 A P) (@lem18937 A P)). Qed.
Lemma lem18940 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18939 A P Q). Qed.

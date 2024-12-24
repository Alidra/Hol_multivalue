Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16421_term_abbrevs.
Require Import RIGHT_FORALL_OR_THM_spec.
Lemma lem16418 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem11700 A P). Qed.
Lemma lem16419 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem16420 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem16419 A P) (@lem16418 A P)). Qed.
Lemma lem16421 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem16420 A P Q). Qed.

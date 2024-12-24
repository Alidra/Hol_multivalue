Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18952_term_abbrevs.
Require Import FORALL_AND_THM_spec.
Lemma lem18949 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem18950 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18951 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18950 A P) (@lem18949 A P)). Qed.
Lemma lem18952 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem18951 A P Q). Qed.

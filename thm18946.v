Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18946_term_abbrevs.
Require Import LEFT_FORALL_OR_THM_spec.
Lemma lem18943 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem11454 A P). Qed.
Lemma lem18944 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18945 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18944 A P) (@lem18943 A P)). Qed.
Lemma lem18946 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem18945 A P Q). Qed.

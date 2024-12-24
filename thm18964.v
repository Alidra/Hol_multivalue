Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18964_term_abbrevs.
Require Import LEFT_EXISTS_AND_THM_spec.
Lemma lem18961 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5682 A P). Qed.
Lemma lem18962 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem18963 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem18962 A P) (@lem18961 A P)). Qed.
Lemma lem18964 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem18963 A P Q). Qed.

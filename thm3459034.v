Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459034_term_abbrevs.
Require Import EXTENSION_spec.
Lemma lem3459031 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3459032 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3459033 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3459032 A s) (@lem3459031 A s)). Qed.
Lemma lem3459034 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3459033 A s t). Qed.

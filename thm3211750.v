Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211750_term_abbrevs.
Require Import SUBSET_spec.
Lemma lem3211747 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem3211748 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211749 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211748 A s) (@lem3211747 A s)). Qed.
Lemma lem3211750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211749 A s t). Qed.

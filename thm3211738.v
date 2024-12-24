Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211738_term_abbrevs.
Require Import DISJOINT_spec.
Lemma lem3211735 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem3211736 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211737 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211736 A s) (@lem3211735 A s)). Qed.
Lemma lem3211738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211737 A s t). Qed.

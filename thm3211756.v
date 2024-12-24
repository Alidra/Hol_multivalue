Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211756_term_abbrevs.
Require Import EXTENSION_spec.
Lemma lem3211753 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3211754 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211755 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211754 A s) (@lem3211753 A s)). Qed.
Lemma lem3211756 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211755 A s t). Qed.

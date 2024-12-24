Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400787_term_abbrevs.
Require Import EXTENSION_spec.
Lemma lem5400784 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5400785 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5400786 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem5400785 A s) (@lem5400784 A s)). Qed.
Lemma lem5400787 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem5400786 A s t). Qed.

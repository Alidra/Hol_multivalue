Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211719_term_abbrevs.
Require Import IN_UNION_spec.
Lemma lem3211713 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3211714 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211715 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211714 A s) (@lem3211713 A s)). Qed.
Lemma lem3211716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211715 A s t). Qed.
Lemma lem3211717 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3211718 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3211717 A s t) (@lem3211716 A s t)). Qed.
Lemma lem3211719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3211718 A s t x). Qed.

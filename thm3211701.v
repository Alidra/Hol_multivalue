Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211701_term_abbrevs.
Require Import IN_DIFF_spec.
Lemma lem3211695 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem3211696 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211697 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211696 A s) (@lem3211695 A s)). Qed.
Lemma lem3211698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211697 A s t). Qed.
Lemma lem3211699 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3211700 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3211699 A s t) (@lem3211698 A s t)). Qed.
Lemma lem3211701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3211700 A s t x). Qed.

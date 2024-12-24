Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211692_term_abbrevs.
Require Import IN_INSERT_spec.
Lemma lem3211686 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3211687 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3211688 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3211687 A x) (@lem3211686 A x)). Qed.
Lemma lem3211689 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3211688 A x y). Qed.
Lemma lem3211690 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3211691 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem3211690 A y x) (@lem3211689 A x y)). Qed.
Lemma lem3211692 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem3211691 A y x s). Qed.

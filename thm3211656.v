Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211656_term_abbrevs.
Require Import IN_IMAGE_spec.
Lemma lem3211650 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3211651 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem3211652 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem3211651 A B y) (@lem3211650 A B y)). Qed.
Lemma lem3211653 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem3211652 A B y s). Qed.
Lemma lem3211654 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem3211655 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem3211654 A B y s) (@lem3211653 A B y s)). Qed.
Lemma lem3211656 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem3211655 A B y s f). Qed.

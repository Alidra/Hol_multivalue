Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211710_term_abbrevs.
Require Import IN_INTER_spec.
Lemma lem3211704 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem3211705 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211706 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211705 A s) (@lem3211704 A s)). Qed.
Lemma lem3211707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211706 A s t). Qed.
Lemma lem3211708 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3211709 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3211708 A s t) (@lem3211707 A s t)). Qed.
Lemma lem3211710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3211709 A s t x). Qed.

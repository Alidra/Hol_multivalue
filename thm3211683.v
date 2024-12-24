Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211683_term_abbrevs.
Require Import IN_DELETE_spec.
Lemma lem3211677 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3211678 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211679 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211678 A s) (@lem3211677 A s)). Qed.
Lemma lem3211680 {A : Type'} (s : A -> Prop) (x : A) : term2 A s x.
Proof. exact (@lem3211679 A s x). Qed.
Lemma lem3211681 {A : Type'} (s : A -> Prop) (x : A) : (term2 A s x) = (term3 A s x).
Proof. exact (eq_refl (term2 A s x)). Qed.
Lemma lem3211682 {A : Type'} (s : A -> Prop) (x : A) : term3 A s x.
Proof. exact (EQ_MP (@lem3211681 A s x) (@lem3211680 A s x)). Qed.
Lemma lem3211683 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term4 A s x y.
Proof. exact (@lem3211682 A s x y). Qed.

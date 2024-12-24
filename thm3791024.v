Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3791024_term_abbrevs.
Require Import thm3790998_spec.
Lemma lem3791012 {A B : Type'} (b : B) : term0 A B b.
Proof. exact (@lem3790998 A B b). Qed.
Lemma lem3791013 {A B : Type'} (b : B) : (term0 A B b) = (term1 A B b).
Proof. exact (eq_refl (term0 A B b)). Qed.
Lemma lem3791014 {A B : Type'} (b : B) : term1 A B b.
Proof. exact (EQ_MP (@lem3791013 A B b) (@lem3791012 A B b)). Qed.
Lemma lem3791015 {A B : Type'} (b : B) (s : A -> Prop) : term2 A B b s.
Proof. exact (@lem3791014 A B b s). Qed.
Lemma lem3791016 {A B : Type'} (b : B) (s : A -> Prop) : (term2 A B b s) = (term3 A B b s).
Proof. exact (eq_refl (term2 A B b s)). Qed.
Lemma lem3791017 {A B : Type'} (b : B) (s : A -> Prop) : term3 A B b s.
Proof. exact (EQ_MP (@lem3791016 A B b s) (@lem3791015 A B b s)). Qed.
Lemma lem3791018 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) : term4 A B b s n.
Proof. exact (@lem3791017 A B b s n). Qed.
Lemma lem3791019 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) : (term4 A B b s n) = (term5 A B b s n).
Proof. exact (eq_refl (term4 A B b s n)). Qed.
Lemma lem3791020 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) : term5 A B b s n.
Proof. exact (EQ_MP (@lem3791019 A B b s n) (@lem3791018 A B b s n)). Qed.
Lemma lem3791021 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) : term6 A B b s n a.
Proof. exact (@lem3791020 A B b s n a). Qed.
Lemma lem3791022 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) : (term6 A B b s n a) = (term7 A B b s n a).
Proof. exact (eq_refl (term6 A B b s n a)). Qed.
Lemma lem3791023 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) : term7 A B b s n a.
Proof. exact (EQ_MP (@lem3791022 A B b s n a) (@lem3791021 A B b s n a)). Qed.
Lemma lem3791024 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : term8 A B b s n a f.
Proof. exact (@lem3791023 A B b s n a f). Qed.

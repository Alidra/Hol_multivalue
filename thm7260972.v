Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260972_term_abbrevs.
Require Import thm7260959_spec.
Require Import thm7260960_spec.
Lemma lem7260970 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term0 _132349 f s g.
Proof. exact (EQ_MP (@lem7260960 _132349 f s g) (@lem7260959 _132349 f s g)). Qed.
Lemma lem7260971 (f : nat -> real) (s : nat -> Prop) (g : nat -> real) : term1 f s g.
Proof. exact (@lem7260970 nat f s g). Qed.
Lemma lem7260972 (f : nat -> real) (a : nat) (b : nat) (g : nat -> real) : term2 f a b g.
Proof. exact (@lem7260971 (term3 f) (dotdot a b) g). Qed.

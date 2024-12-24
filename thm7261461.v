Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261461_term_abbrevs.
Require Import thm7261442_spec.
Lemma lem7261452 (f : nat -> real) : term0 f.
Proof. exact (@lem7261442 f). Qed.
Lemma lem7261453 (f : nat -> real) : (term0 f) = (term1 f).
Proof. exact (eq_refl (term0 f)). Qed.
Lemma lem7261454 (f : nat -> real) : term1 f.
Proof. exact (EQ_MP (@lem7261453 f) (@lem7261452 f)). Qed.
Lemma lem7261455 (f : nat -> real) (g : nat -> real) : term2 f g.
Proof. exact (@lem7261454 f g). Qed.
Lemma lem7261456 (f : nat -> real) (g : nat -> real) : (term2 f g) = (term3 f g).
Proof. exact (eq_refl (term2 f g)). Qed.
Lemma lem7261457 (f : nat -> real) (g : nat -> real) : term3 f g.
Proof. exact (EQ_MP (@lem7261456 f g) (@lem7261455 f g)). Qed.
Lemma lem7261458 (f : nat -> real) (g : nat -> real) (a : nat) : term4 f g a.
Proof. exact (@lem7261457 f g a). Qed.
Lemma lem7261459 (f : nat -> real) (a : nat) (g : nat -> real) : (term4 f g a) = (term5 f a g).
Proof. exact (eq_refl (term4 f g a)). Qed.
Lemma lem7261460 (f : nat -> real) (a : nat) (g : nat -> real) : term5 f a g.
Proof. exact (EQ_MP (@lem7261459 f a g) (@lem7261458 f g a)). Qed.
Lemma lem7261461 (f : nat -> real) (a : nat) (g : nat -> real) (b : nat) : term6 f a g b.
Proof. exact (@lem7261460 f a g b). Qed.

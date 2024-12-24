Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261462_term_abbrevs.
Lemma lem7261462 (f : nat -> real) (a : nat) (b : nat) (g : nat -> real) : (term0 f a g b) = (term1 f a b g).
Proof. exact (eq_refl (term0 f a g b)). Qed.

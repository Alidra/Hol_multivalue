Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260963_term_abbrevs.
Lemma lem7260963 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term0 a b f g) : term0 a b f g.
Proof. exact (h1). Qed.

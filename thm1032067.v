Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032067_term_abbrevs.
Require Import thm1032065_spec.
Lemma lem1032067 (ly : nat) (rx : nat) (lx : nat) (ry : nat) (b : nat) (a : nat) (c : nat) (d : nat) (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term0 ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem1032065 ly rx lx ry b a c d p y z x q)). Qed.
Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483467_term_abbrevs.
Require Import thm1483465_spec.
Lemma lem1483467 (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem1483465 ly rx lx ry b a c d p y z x q)). Qed.
Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982722_term_abbrevs.
Require Import thm1982720_spec.
Lemma lem1982722 (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem1982720 ly rx lx ry b a c d p y z x q)). Qed.
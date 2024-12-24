Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982714_term_abbrevs.
Require Import thm1982712_spec.
Lemma lem1982714 (m : real) (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 m ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem1982712 m ly rx lx ry b a c d p y z x q)). Qed.

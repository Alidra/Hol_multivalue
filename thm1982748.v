Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982748_term_abbrevs.
Require Import thm1982746_spec.
Lemma lem1982748 (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem1982746 rx lx ry b a c d p y z x q)). Qed.

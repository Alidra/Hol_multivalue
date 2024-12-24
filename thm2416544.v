Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416544_term_abbrevs.
Require Import thm2416542_spec.
Lemma lem2416544 (ly : int) (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat) : term0 ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem2416542 ly rx lx ry b a c d p y z x q)). Qed.

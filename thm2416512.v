Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416512_term_abbrevs.
Require Import thm2416510_spec.
Lemma lem2416512 (m : int) (ly : int) (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat) : term0 m ly rx lx ry b a c d p y z x q.
Proof. exact (proj2 (@lem2416510 m ly rx lx ry b a c d p y z x q)). Qed.
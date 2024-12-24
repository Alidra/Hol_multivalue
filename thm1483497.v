Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483497_term_abbrevs.
Require Import thm1483495_spec.
Lemma lem1483497 (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem1483495 p y z x q)). Qed.

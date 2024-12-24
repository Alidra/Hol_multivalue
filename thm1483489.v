Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483489_term_abbrevs.
Require Import thm1483487_spec.
Lemma lem1483489 (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem1483487 (@el real) (@el real) (@el real) p y z x q)). Qed.

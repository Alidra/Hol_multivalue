Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483501_term_abbrevs.
Require Import thm1483499_spec.
Lemma lem1483501 (y : real) (z : real) (x : real) (q : nat) : term0 y z x q.
Proof. exact (proj2 (@lem1483499 (@el nat) y z x q)). Qed.

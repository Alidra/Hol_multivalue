Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483505_term_abbrevs.
Require Import thm1483503_spec.
Lemma lem1483505 (y : real) (z : real) (x : real) (q : nat) : term0 y z x q.
Proof. exact (proj2 (@lem1483503 y z x q)). Qed.

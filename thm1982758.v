Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982758_term_abbrevs.
Require Import thm1982756_spec.
Lemma lem1982758 (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 a c d p y z x q.
Proof. exact (proj2 (@lem1982756 (@el real) a c d p y z x q)). Qed.

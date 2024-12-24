Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483477_term_abbrevs.
Require Import thm1483475_spec.
Lemma lem1483477 (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 b a c d p y z x q.
Proof. exact (proj2 (@lem1483475 (@el real) (@el real) (@el real) b a c d p y z x q)). Qed.

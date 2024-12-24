Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982764_term_abbrevs.
Require Import thm1982762_spec.
Lemma lem1982764 (p : nat) (y : real) (z : real) (x : real) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem1982762 p y z x q)). Qed.

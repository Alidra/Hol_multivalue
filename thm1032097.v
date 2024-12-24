Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032097_term_abbrevs.
Require Import thm1032095_spec.
Lemma lem1032097 (a : nat) (c : nat) (d : nat) (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term0 a c d p y z x q.
Proof. exact (proj2 (@lem1032095 a c d p y z x q)). Qed.

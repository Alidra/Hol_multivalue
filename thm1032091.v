Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032091_term_abbrevs.
Require Import thm1032089_spec.
Lemma lem1032091 (b : nat) (a : nat) (c : nat) (d : nat) (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term0 b a c d p y z x q.
Proof. exact (proj2 (@lem1032089 b a c d p y z x q)). Qed.

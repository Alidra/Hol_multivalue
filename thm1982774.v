Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1982774_term_abbrevs.
Require Import thm1982772_spec.
Lemma lem1982774 (y : real) (z : real) (x : real) (q : nat) : term0 y z x q.
Proof. exact (proj2 (@lem1982772 (@el nat) y z x q)). Qed.

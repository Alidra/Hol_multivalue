Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416560_term_abbrevs.
Require Import thm2416558_spec.
Lemma lem2416560 (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat) : term0 a c d p y z x q.
Proof. exact (proj2 (@lem2416558 (@el int) a c d p y z x q)). Qed.
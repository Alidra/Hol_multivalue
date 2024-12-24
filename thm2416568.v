Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416568_term_abbrevs.
Require Import thm2416566_spec.
Lemma lem2416568 (p : nat) (y : int) (z : int) (x : int) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem2416566 p y z x q)). Qed.

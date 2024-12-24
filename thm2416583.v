Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416583_term_abbrevs.
Require Import thm2416572_spec.
Lemma lem2416574 (p : nat) (y : int) (z : int) (x : int) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem2416572 p y z x q)). Qed.
Lemma lem2416576 (y : int) (z : int) (x : int) (q : nat) : term1 y z x q.
Proof. exact (proj2 (@lem2416574 (@el nat) y z x q)). Qed.
Lemma lem2416578 (y : int) (z : int) (x : int) (q : nat) : term2 y z x q.
Proof. exact (proj2 (@lem2416576 y z x q)). Qed.
Lemma lem2416580 (y : int) (z : int) (x : int) (q : nat) : term3 y z x q.
Proof. exact (proj2 (@lem2416578 y z x q)). Qed.
Lemma lem2416583 (y : int) (x : int) (z : int) : (term4 x y z) = (term5 y x z).
Proof. exact (proj1 (@lem2416580 y z x (@el nat))). Qed.

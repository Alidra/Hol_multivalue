Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247415_term_abbrevs.
Lemma lem1247415 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term0 p d d') = (Nat.add p d'')) : (term0 p d d') = (Nat.add p d'').
Proof. exact (h1). Qed.

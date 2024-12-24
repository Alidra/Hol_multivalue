Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248167_term_abbrevs.
Lemma lem1248167 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : (term0 p d n) = (term0 p q d').
Proof. exact (h1). Qed.

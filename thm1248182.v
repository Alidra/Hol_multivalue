Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248182_term_abbrevs.
Lemma lem1248182 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term0 p d n d')) : (Nat.add p q) = (term0 p d n d').
Proof. exact (h1). Qed.

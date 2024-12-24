Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247628_term_abbrevs.
Lemma lem1247628 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : (Nat.add p q) = (term0 m n d).
Proof. exact (h1). Qed.

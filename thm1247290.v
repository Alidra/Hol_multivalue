Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem1247290 (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : (Nat.add p d) = (Nat.add n d').
Proof. exact (h1). Qed.

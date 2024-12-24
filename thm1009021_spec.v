Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1009021 : forall (p : nat) (m : nat) (n : nat) (a : nat), ((Nat.pow m n) = p) -> ((Nat.mul p p) = a) -> (Nat.pow m (BIT0 n)) = a.

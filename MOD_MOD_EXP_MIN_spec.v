Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem235568 : forall x : nat, forall p : nat, forall m : nat, forall n : nat, (Nat.modulo (Nat.modulo x (Nat.pow p m)) (Nat.pow p n)) = (Nat.modulo x (Nat.pow p (Nat.min m n))).

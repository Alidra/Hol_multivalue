Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1263160 : forall x : nadd, exists A : nat, exists B : nat, forall n : nat, Peano.le (dest_nadd x n) (Nat.add (Nat.mul A n) B).

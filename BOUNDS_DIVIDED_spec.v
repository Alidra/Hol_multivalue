Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1261317 : forall P : nat -> nat, (exists B : nat, forall n : nat, Peano.le (P n) B) = (exists A : nat, exists B : nat, forall n : nat, Peano.le (Nat.mul n (P n)) (Nat.add (Nat.mul A n) B)).

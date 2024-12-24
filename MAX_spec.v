Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem90708 : forall m : nat, forall n : nat, (Nat.max m n) = (@COND nat (Peano.le m n) n m).

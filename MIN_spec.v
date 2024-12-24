Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem90961 : forall m : nat, forall n : nat, (Nat.min m n) = (@COND nat (Peano.le m n) m n).

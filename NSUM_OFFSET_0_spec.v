Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7048892 : forall f : nat -> nat, forall m : nat, forall n : nat, (Peano.le m n) -> (@nsum nat (dotdot m n) f) = (@nsum nat (dotdot (NUMERAL 0) (Nat.sub n m)) (fun i : nat => f (Nat.add i m))).

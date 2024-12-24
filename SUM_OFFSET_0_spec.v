Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7223337 : forall f : nat -> real, forall m : nat, forall n : nat, (Peano.le m n) -> (@sum nat (dotdot m n) f) = (@sum nat (dotdot (NUMERAL 0) (Nat.sub n m)) (fun i : nat => f (Nat.add i m))).

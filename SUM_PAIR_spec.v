Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7226452 : forall f : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0)))) f) = (@sum nat (dotdot m n) (fun i : nat => real_add (f (Nat.mul (NUMERAL (BIT0 (BIT1 0))) i)) (f (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) i) (NUMERAL (BIT1 0)))))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6220935 : forall {_123774 : Type'}, forall op : _123774 -> _123774 -> _123774, (@monoidal _123774 op) -> forall f : nat -> _123774, forall m : nat, forall n : nat, (@iterate _123774 nat op (dotdot (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0)))) f) = (@iterate _123774 nat op (dotdot m n) (fun i : nat => op (f (Nat.mul (NUMERAL (BIT0 (BIT1 0))) i)) (f (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) i) (NUMERAL (BIT1 0)))))).

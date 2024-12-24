Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem216054 : forall a : nat, forall b : nat, forall c : nat, forall d : nat, ((~ (b = (NUMERAL 0))) /\ (Peano.lt (Nat.mul b c) (Nat.mul (Nat.add a (NUMERAL (BIT1 0))) d))) -> Peano.le (Nat.div c d) (Nat.div a b).

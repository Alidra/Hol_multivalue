Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem218367 : forall a : nat, forall b : nat, forall c : nat, forall d : nat, ((Peano.lt (Nat.mul b c) (Nat.mul (Nat.add a (NUMERAL (BIT1 0))) d)) /\ (Peano.lt (Nat.mul a d) (Nat.mul (Nat.add c (NUMERAL (BIT1 0))) b))) -> (Nat.div a b) = (Nat.div c d).

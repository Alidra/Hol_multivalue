Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1046224 : (forall a : nat, forall b : nat, forall c : nat, forall d : nat, ((~ (a = b)) /\ (~ (c = d))) = (~ ((Nat.add (Nat.mul a c) (Nat.mul b d)) = (Nat.add (Nat.mul a d) (Nat.mul b c))))) /\ (forall n : nat, forall a : nat, forall b : nat, forall c : nat, forall d : nat, (~ (n = (NUMERAL 0))) -> ((a = b) /\ (~ (c = d))) -> ~ ((Nat.add a (Nat.mul n c)) = (Nat.add b (Nat.mul n d)))).

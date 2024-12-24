Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1046225 : forall n : nat, forall a : nat, forall b : nat, forall c : nat, forall d : nat, (~ (n = (NUMERAL 0))) -> ((a = b) /\ (~ (c = d))) -> ~ ((Nat.add a (Nat.mul n c)) = (Nat.add b (Nat.mul n d))).

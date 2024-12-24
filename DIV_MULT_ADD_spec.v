Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem209601 : (forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul a n) b) n) = (Nat.add a (Nat.div b n))) /\ ((forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div (Nat.add (Nat.mul n a) b) n) = (Nat.add a (Nat.div b n))) /\ ((forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div (Nat.add b (Nat.mul a n)) n) = (Nat.add (Nat.div b n) a)) /\ (forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> (Nat.div (Nat.add b (Nat.mul n a)) n) = (Nat.add (Nat.div b n) a)))).

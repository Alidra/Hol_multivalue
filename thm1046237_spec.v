Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1046237 : forall (a : nat) (d : nat) (b : nat) (c : nat), ((fun d' : nat => ((~ (a = b)) /\ (~ (c = d'))) = (~ ((Nat.add (Nat.mul a c) (Nat.mul b d')) = (Nat.add (Nat.mul a d') (Nat.mul b c))))) d) = (((~ (a = b)) /\ (~ (c = d))) = (~ ((Nat.add (Nat.mul a c) (Nat.mul b d)) = (Nat.add (Nat.mul a d) (Nat.mul b c))))).

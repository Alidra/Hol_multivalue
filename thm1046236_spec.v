Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1046236 : forall (a : nat) (b : nat) (c : nat) (d : nat), (fun d' : nat => ((~ (a = b)) /\ (~ (c = d'))) = (~ ((Nat.add (Nat.mul a c) (Nat.mul b d')) = (Nat.add (Nat.mul a d') (Nat.mul b c))))) d.

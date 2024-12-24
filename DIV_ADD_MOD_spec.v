Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem210482 : forall a : nat, forall b : nat, forall n : nat, (~ (n = (NUMERAL 0))) -> ((Nat.modulo (Nat.add a b) n) = (Nat.add (Nat.modulo a n) (Nat.modulo b n))) = ((Nat.div (Nat.add a b) n) = (Nat.add (Nat.div a n) (Nat.div b n))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3111295 : forall d : nat, forall a : nat, forall b : nat, ((num_divides d a) \/ (num_divides d b)) -> (Nat.div (Nat.add a b) d) = (Nat.add (Nat.div a d) (Nat.div b d)).

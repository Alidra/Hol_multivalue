Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem220350 : forall m : nat, forall n : nat, forall p : nat, (Nat.div (Nat.div m n) p) = (Nat.div m (Nat.mul n p)).

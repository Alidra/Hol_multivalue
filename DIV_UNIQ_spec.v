Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem169759 : forall m : nat, forall n : nat, forall q : nat, forall r : nat, ((m = (Nat.add (Nat.mul q n) r)) /\ (Peano.lt r n)) -> (Nat.div m n) = q.
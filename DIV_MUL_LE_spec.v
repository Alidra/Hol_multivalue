Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem178720 : forall m : nat, forall n : nat, Peano.le (Nat.mul n (Nat.div m n)) m.

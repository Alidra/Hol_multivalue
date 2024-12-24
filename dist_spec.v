Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1244710 : forall n : nat, forall m : nat, (dist (@pair nat nat m n)) = (Nat.add (Nat.sub m n) (Nat.sub n m)).

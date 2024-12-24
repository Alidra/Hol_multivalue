Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247338 : forall (d : nat) (d' : nat) (n : nat) (p : nat), (forall d'' : nat, ((n = (Nat.add p d'')) -> Peano.le d (Nat.add d' d'')) /\ ((p = (Nat.add n d'')) -> Peano.le d (Nat.add d' d''))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n p)))).

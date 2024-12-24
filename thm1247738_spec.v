Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247738 : forall (d : nat) (d' : nat) (n : nat) (q : nat), (forall d'' : nat, ((n = (Nat.add q d'')) -> Peano.le d (Nat.add d' d'')) /\ ((q = (Nat.add n d'')) -> Peano.le d (Nat.add d' d''))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n q)))).

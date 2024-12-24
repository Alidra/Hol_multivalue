Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247414 : forall (d : nat) (d' : nat) (p : nat), (forall d'' : nat, (((Nat.add (Nat.add p d) d') = (Nat.add p d'')) -> Peano.le d (Nat.add d' d'')) /\ ((p = (Nat.add (Nat.add (Nat.add p d) d') d'')) -> Peano.le d (Nat.add d' d''))) = (Peano.le d (Nat.add d' (dist (@pair nat nat (Nat.add (Nat.add p d) d') p)))).

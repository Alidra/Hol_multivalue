Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247512 : forall (n : nat) (d' : nat) (d : nat), (forall d'' : nat, ((n = (Nat.add (Nat.add (Nat.add n d') d) d'')) -> Peano.le d (Nat.add d' d'')) /\ (((Nat.add (Nat.add n d') d) = (Nat.add n d'')) -> Peano.le d (Nat.add d' d''))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add (Nat.add n d') d))))).

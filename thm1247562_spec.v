Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247562 : forall (d' : nat) (m : nat) (d : nat), (forall d'' : nat, (((Nat.add m d') = (Nat.add (Nat.add m d) d'')) -> Peano.le d (Nat.add d' d'')) /\ (((Nat.add m d) = (Nat.add (Nat.add m d') d'')) -> Peano.le d (Nat.add d' d''))) = (Peano.le d (Nat.add d' (dist (@pair nat nat (Nat.add m d') (Nat.add m d))))).

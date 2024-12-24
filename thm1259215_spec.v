Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259215 : forall (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat), ((Nat.add m (Nat.add q d'')) = (Nat.add (Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) q) d')) -> False.

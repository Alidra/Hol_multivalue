Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259212 : forall (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat), ((Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add n d'')) = (Nat.add (Nat.add m n) d')) -> False.

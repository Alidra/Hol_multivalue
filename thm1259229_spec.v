Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259229 : forall (m : nat) (d' : nat) (d''' : nat) (d'' : nat), ((Nat.add m d') = (Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) d'')) -> False.

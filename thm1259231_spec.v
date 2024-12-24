Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259231 : forall (n : nat) (d' : nat) (d''' : nat) (d'' : nat), (n = (Nat.add (Nat.add (Nat.add n d') (Nat.add (Nat.add d' d'') (S d'''))) d'')) -> False.

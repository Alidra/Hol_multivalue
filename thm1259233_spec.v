Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259233 : forall (d''' : nat) (d' : nat) (p : nat) (d'' : nat), ((Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) d') = (Nat.add p d'')) -> False.

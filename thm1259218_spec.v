Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259218 : forall (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat), ((Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) n) = (Nat.add (Nat.add p (Nat.add n d'')) d')) -> False.

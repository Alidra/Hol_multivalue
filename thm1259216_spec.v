Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259216 : forall (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat), ((Nat.add p (Nat.add n d'')) = (Nat.add (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) n) d')) -> False.

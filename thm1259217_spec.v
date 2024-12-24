Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259217 : forall (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat), ((Nat.add p q) = (Nat.add (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add q d'')) d')) -> False.

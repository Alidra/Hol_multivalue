Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259232 : forall (p : nat) (d''' : nat) (d' : nat) (d'' : nat), (p = (Nat.add (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) d') d'')) -> False.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1252523 : forall (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat), (((Nat.add d'' (Nat.add d'' (S d'''))) = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add p d') n) = (Nat.add (Nat.add p (Nat.add n d'')) (Nat.add (Nat.add d' d'') (S d''')))) -> False).

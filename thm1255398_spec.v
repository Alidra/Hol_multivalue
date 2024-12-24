Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1255398 : forall (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat), (((Nat.add (S d''') (Nat.add d'' d'')) = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add q d'')) = (Nat.add (Nat.add p q) d')) -> False).

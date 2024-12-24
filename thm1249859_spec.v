Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249859 : forall (d''' : nat) (p : nat) (d'' : nat) (d' : nat), (((S d''') = (NUMERAL 0)) -> False) = (((Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) = (Nat.add (Nat.add p d'') d')) -> False).

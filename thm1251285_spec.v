Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1251285 : forall (d' : nat) (d''' : nat) (n : nat) (d'' : nat), (((Nat.add (S d''') (Nat.add d' d')) = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add n d') (Nat.add (Nat.add d' d'') (S d'''))) = (Nat.add n d'')) -> False).
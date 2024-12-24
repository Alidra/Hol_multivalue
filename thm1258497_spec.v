Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1258497 : forall (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat), (((Nat.add (S d''') (Nat.add d'' d'')) = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add n d'')) = (Nat.add (Nat.add m n) d')) -> False).

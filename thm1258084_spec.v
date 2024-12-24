Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1258084 : forall (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat), (((S d''') = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) q) = (Nat.add (Nat.add m (Nat.add q d'')) d')) -> False).

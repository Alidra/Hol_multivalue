Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1251719 : forall (d''' : nat) (m : nat) (d' : nat) (d'' : nat), (((S d''') = (NUMERAL 0)) -> False) = (((Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) = (Nat.add (Nat.add m d') d'')) -> False).

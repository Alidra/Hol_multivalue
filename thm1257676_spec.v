Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1257676 : forall (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat), (((Nat.add d'' (Nat.add d'' (Nat.add d' (Nat.add d' (S d'''))))) = (NUMERAL 0)) -> False) = (((Nat.add m n) = (Nat.add (Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) (Nat.add n d'')) d')) -> False).

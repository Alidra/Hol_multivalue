Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1251039 : forall (n : nat) (d' : nat) (d''' : nat) (d'' : nat), (((Nat.add d'' (Nat.add d'' (Nat.add d' (Nat.add d' (S d'''))))) = (NUMERAL 0)) -> False) = ((n = (Nat.add (Nat.add (Nat.add n d') (Nat.add (Nat.add d' d'') (S d'''))) d'')) -> False).

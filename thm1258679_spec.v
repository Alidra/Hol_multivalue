Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1258679 : forall (d''' : nat) (d' : nat), ((Nat.add (S d''') (Nat.add d' d')) = (NUMERAL 0)) -> False.

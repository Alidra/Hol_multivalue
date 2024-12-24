Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259125 : forall (d' : nat) (d''' : nat), ((Nat.add d' (Nat.add d' (S d'''))) = (NUMERAL 0)) -> False.

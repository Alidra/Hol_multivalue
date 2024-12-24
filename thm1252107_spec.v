Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1252107 : forall (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat), (((S d''') = (NUMERAL 0)) -> False) = (((Nat.add (Nat.add p d') (Nat.add q d'')) = (Nat.add (Nat.add p q) (Nat.add (Nat.add d' d'') (S d''')))) -> False).

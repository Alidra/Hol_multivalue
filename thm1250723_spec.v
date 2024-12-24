Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1250723 : forall (p : nat) (d''' : nat) (d' : nat) (d'' : nat), (((Nat.add d'' (Nat.add d'' (Nat.add d' (Nat.add d' (S d'''))))) = (NUMERAL 0)) -> False) = ((p = (Nat.add (Nat.add (Nat.add p (Nat.add (Nat.add d' d'') (S d'''))) d') d'')) -> False).

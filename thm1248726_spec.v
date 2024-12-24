Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248726 : forall (d : nat) (d' : nat) (d'' : nat), (~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d''')))) = (Peano.le d (Nat.add d' d'')).

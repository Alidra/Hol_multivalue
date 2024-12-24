Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259369 : forall (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (Nat.add (Nat.add p d) d') = (Nat.add p d'')), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

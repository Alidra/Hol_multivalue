Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259364 : forall (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (Nat.add (Nat.add (Nat.add p d) d') d'')), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

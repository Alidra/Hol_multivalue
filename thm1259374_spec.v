Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259374 : forall (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

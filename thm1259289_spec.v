Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259289 : forall (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add p q) = (Nat.add (Nat.add (Nat.add p d) n) d')), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

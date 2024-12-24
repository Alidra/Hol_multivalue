Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259222 : forall (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat), ((Nat.add p (Nat.add n d'')) = (Nat.add (Nat.add (Nat.add p d') n) (Nat.add (Nat.add d' d'') (S d''')))) -> False.

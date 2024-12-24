Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249137 : forall (d''' : nat) (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : (Nat.add m d') = (Nat.add (Nat.add m d) d'')), (Nat.add m d') = (Nat.add (Nat.add m (Nat.add (Nat.add d' d'') (S d'''))) d'').

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259220 : forall (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat), ((Nat.add (Nat.add m d') (Nat.add n d'')) = (Nat.add (Nat.add m n) (Nat.add (Nat.add d' d'') (S d''')))) -> False.

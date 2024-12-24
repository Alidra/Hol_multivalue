Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259264 : forall (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add (Nat.add m d) q) = (Nat.add (Nat.add m n) d')), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

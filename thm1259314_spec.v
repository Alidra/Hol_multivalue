Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259314 : forall (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (Nat.add (Nat.add m n) d)), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

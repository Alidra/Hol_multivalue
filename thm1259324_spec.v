Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259324 : forall (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (Nat.add (Nat.add p q) d)), ~ (exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))).

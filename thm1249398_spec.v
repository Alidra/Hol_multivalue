Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249398 : forall (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (Nat.add (Nat.add d' d'') (S d'''))) (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (Nat.add (Nat.add m n) d)), (Nat.add (Nat.add m d') (Nat.add n d'')) = (Nat.add (Nat.add m n) (Nat.add (Nat.add d' d'') (S d'''))).

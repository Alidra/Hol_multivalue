Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1249254 : forall (d : nat) (d' : nat) (d'' : nat) (h1 : exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d'''))), exists d''' : nat, d = (Nat.add (Nat.add d' d'') (S d''')).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1269692 : forall x : nadd, forall y : nadd, (nadd_le x y) = (exists B : nat, forall n : nat, Peano.le (dest_nadd x n) (Nat.add (dest_nadd y n) B)).

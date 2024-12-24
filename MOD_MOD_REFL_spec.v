Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem183010 : forall m : nat, forall n : nat, (Nat.modulo (Nat.modulo m n) n) = (Nat.modulo m n).

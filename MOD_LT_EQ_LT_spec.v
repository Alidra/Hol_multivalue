Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem168233 : forall m : nat, forall n : nat, (Peano.lt (Nat.modulo m n) n) = (Peano.lt (NUMERAL 0) n).

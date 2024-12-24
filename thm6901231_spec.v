Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6901231 : (@ε nat (fun x : nat => forall y : nat, ((Nat.mul x y) = y) /\ ((Nat.mul y x) = y))) = (NUMERAL (BIT1 0)).

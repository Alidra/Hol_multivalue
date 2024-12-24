Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6921992 : (@ε nat (fun x : nat => forall y : nat, ((Nat.add x y) = y) /\ ((Nat.add y x) = y))) = (NUMERAL 0).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem102215 : forall m : nat, forall n : nat, (Peano.lt (NUMERAL 0) (Nat.mul m n)) = ((Peano.lt (NUMERAL 0) m) /\ (Peano.lt (NUMERAL 0) n)).

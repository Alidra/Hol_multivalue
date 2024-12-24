Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem134538 : forall n : nat, (exists k : nat, exists m : nat, (Coq.Arith.PeanoNat.Nat.Odd m) /\ (n = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) k) m))) = (~ (n = (NUMERAL 0))).

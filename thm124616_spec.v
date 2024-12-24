Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem124616 : ((Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)) = False) /\ (forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (S n)) = (~ (Coq.Arith.PeanoNat.Nat.Odd n))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem128115 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.mul m n)) = ((Coq.Arith.PeanoNat.Nat.Odd m) /\ (Coq.Arith.PeanoNat.Nat.Odd n)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem128321 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.pow m n)) = ((Coq.Arith.PeanoNat.Nat.Odd m) \/ (n = (NUMERAL 0))).

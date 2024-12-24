Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem126297 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.pow m n)) = ((Coq.Arith.PeanoNat.Nat.Even m) /\ (~ (n = (NUMERAL 0)))).

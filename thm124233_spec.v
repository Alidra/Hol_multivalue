Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem124233 : ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = True) /\ (forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (S n)) = (~ (Coq.Arith.PeanoNat.Nat.Even n))).

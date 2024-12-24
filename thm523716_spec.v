Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523716 : ((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 n)) = True) /\ (forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 n)) = False)).

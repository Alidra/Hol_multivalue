Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem204674 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo m n)) = (Coq.Arith.PeanoNat.Nat.Odd m).

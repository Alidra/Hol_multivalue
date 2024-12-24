Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem124909 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) \/ (Coq.Arith.PeanoNat.Nat.Odd n).

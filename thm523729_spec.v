Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523729 : forall (n : nat), ((fun n' : nat => (Coq.Arith.PeanoNat.Nat.Even (NUMERAL n')) = (Coq.Arith.PeanoNat.Nat.Even n')) n) = ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL n)) = (Coq.Arith.PeanoNat.Nat.Even n)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem125496 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add m n)) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).

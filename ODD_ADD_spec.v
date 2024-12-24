Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem127895 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.add m n)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd m) = (Coq.Arith.PeanoNat.Nat.Odd n))).

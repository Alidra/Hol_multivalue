Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem145380 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.sub m n)) = ((Peano.le m n) \/ ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).

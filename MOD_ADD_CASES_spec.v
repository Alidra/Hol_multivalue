Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem177911 : forall m : nat, forall n : nat, forall p : nat, ((Peano.lt m p) /\ (Peano.lt n p)) -> (Nat.modulo (Nat.add m n) p) = (@COND nat (Peano.lt (Nat.add m n) p) (Nat.add m n) (Nat.sub (Nat.add m n) p)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem155916 : forall m : nat, forall n : nat, @COND Prop (n = (NUMERAL 0)) (((Nat.div m n) = (NUMERAL 0)) /\ ((Nat.modulo m n) = m)) ((m = (Nat.add (Nat.mul (Nat.div m n) n) (Nat.modulo m n))) /\ (Peano.lt (Nat.modulo m n) n)).

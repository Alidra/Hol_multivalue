Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem189310 : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL 0))) -> (Peano.lt n (Nat.div b a)) = (Peano.le (Nat.mul a (Nat.add n (NUMERAL (BIT1 0)))) b).

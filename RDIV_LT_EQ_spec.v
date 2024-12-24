Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem188986 : forall a : nat, forall b : nat, forall n : nat, (~ (a = (NUMERAL 0))) -> (Peano.lt (Nat.div b a) n) = (Peano.lt b (Nat.mul a n)).

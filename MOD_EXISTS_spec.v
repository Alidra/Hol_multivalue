Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem186864 : forall m : nat, forall n : nat, (exists q : nat, m = (Nat.mul n q)) = (@COND Prop (n = (NUMERAL 0)) (m = (NUMERAL 0)) ((Nat.modulo m n) = (NUMERAL 0))).

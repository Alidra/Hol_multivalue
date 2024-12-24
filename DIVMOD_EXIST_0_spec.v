Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem155064 : forall m : nat, forall n : nat, exists q : nat, exists r : nat, @COND Prop (n = (NUMERAL 0)) ((q = (NUMERAL 0)) /\ (r = m)) ((m = (Nat.add (Nat.mul q n) r)) /\ (Peano.lt r n)).

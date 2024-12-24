Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047063 : forall f : nat -> nat, forall m : nat, forall n : nat, (Peano.lt n m) -> (@nsum nat (dotdot m n) f) = (NUMERAL 0).

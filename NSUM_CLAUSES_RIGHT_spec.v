Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7052394 : forall f : nat -> nat, forall m : nat, forall n : nat, ((Peano.lt (NUMERAL 0) n) /\ (Peano.le m n)) -> (@nsum nat (dotdot m n) f) = (Nat.add (@nsum nat (dotdot m (Nat.sub n (NUMERAL (BIT1 0)))) f) (f n)).

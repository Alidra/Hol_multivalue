Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7048325 : forall f : nat -> nat, forall m : nat, forall n : nat, forall p : nat, (Peano.le m (Nat.add n (NUMERAL (BIT1 0)))) -> (@nsum nat (dotdot m (Nat.add n p)) f) = (Nat.add (@nsum nat (dotdot m n) f) (@nsum nat (dotdot (Nat.add n (NUMERAL (BIT1 0))) (Nat.add n p)) f)).

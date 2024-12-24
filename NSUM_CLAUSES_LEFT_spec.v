Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7052037 : forall f : nat -> nat, forall m : nat, forall n : nat, (Peano.le m n) -> (@nsum nat (dotdot m n) f) = (Nat.add (f m) (@nsum nat (dotdot (Nat.add m (NUMERAL (BIT1 0))) n) f)).

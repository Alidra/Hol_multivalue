Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7226008 : forall f : nat -> real, forall m : nat, forall n : nat, (Peano.le m n) -> (@sum nat (dotdot m n) f) = (real_add (f m) (@sum nat (dotdot (Nat.add m (NUMERAL (BIT1 0))) n) f)).

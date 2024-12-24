Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5357842 : forall m : nat, forall n : nat, (Peano.le m n) -> (@INSERT nat m (dotdot (Nat.add m (NUMERAL (BIT1 0))) n)) = (dotdot m n).

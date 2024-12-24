Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5371007 : forall m : nat, forall n : nat, (Peano.le m n) -> (@INSERT nat n (dotdot m (Nat.sub n (NUMERAL (BIT1 0))))) = (dotdot m n).

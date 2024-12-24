Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5336704 : forall m : nat, forall p : nat, forall n : nat, ((Peano.le m (Nat.add p (NUMERAL (BIT1 0)))) /\ (Peano.le p n)) -> (@UNION nat (dotdot m p) (dotdot (Nat.add p (NUMERAL (BIT1 0))) n)) = (dotdot m n).

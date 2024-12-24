Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5351259 : forall m : nat, forall p : nat, forall n : nat, ((Peano.le m p) /\ (Peano.le p (Nat.add n (NUMERAL (BIT1 0))))) -> (@UNION nat (dotdot m (Nat.sub p (NUMERAL (BIT1 0)))) (dotdot p n)) = (dotdot m n).

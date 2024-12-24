Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem181826 : forall m : nat, forall n : nat, ((Peano.lt (NUMERAL 0) m) /\ (Peano.le m n)) -> Peano.le (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.modulo n m)) n.

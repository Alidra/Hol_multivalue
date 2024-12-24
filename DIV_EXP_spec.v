Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem238173 : forall m : nat, forall n : nat, forall p : nat, (~ (m = (NUMERAL 0))) -> (Nat.div (Nat.pow m n) (Nat.pow m p)) = (@COND nat (Peano.le p n) (Nat.pow m (Nat.sub n p)) (@COND nat (m = (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)) (NUMERAL 0))).

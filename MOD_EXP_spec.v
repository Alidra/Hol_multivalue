Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem238172 : forall m : nat, forall n : nat, forall p : nat, (~ (m = (NUMERAL 0))) -> (Nat.modulo (Nat.pow m n) (Nat.pow m p)) = (@COND nat ((Peano.le p n) \/ (m = (NUMERAL (BIT1 0)))) (NUMERAL 0) (Nat.pow m n)).

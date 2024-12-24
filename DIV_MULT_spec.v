Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem170527 : forall m : nat, forall n : nat, (~ (m = (NUMERAL 0))) -> (Nat.div (Nat.mul m n) m) = n.

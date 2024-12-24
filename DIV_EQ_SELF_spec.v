Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem199825 : forall m : nat, forall n : nat, ((Nat.div m n) = m) = ((m = (NUMERAL 0)) \/ (n = (NUMERAL (BIT1 0)))).

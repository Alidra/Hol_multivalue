Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem87446 : forall n : nat, (Nat.pow (NUMERAL 0) n) = (@COND nat (n = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).

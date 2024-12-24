Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5397152 : forall n : nat, (@CARD nat (dotdot (NUMERAL (BIT1 0)) n)) = n.

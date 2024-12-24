Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem84996 : forall n : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) = (Nat.add n n).

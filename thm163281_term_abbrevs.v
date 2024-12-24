Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term1 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))))) -> False.

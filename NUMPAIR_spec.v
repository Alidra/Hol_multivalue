Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1046874 : forall x : nat, forall y : nat, (NUMPAIR x y) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y) (NUMERAL (BIT1 0)))).

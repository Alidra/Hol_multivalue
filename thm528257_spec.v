Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem528257 : (Nat.add (BIT1 0) (BIT1 (BIT1 0))) = (BIT0 (S (Nat.add 0 (BIT1 0)))).
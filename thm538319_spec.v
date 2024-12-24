Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem538319 : (Nat.add (BIT0 (BIT0 (BIT1 0))) (BIT0 (BIT1 0))) = (BIT0 (Nat.add (BIT0 (BIT1 0)) (BIT1 0))).

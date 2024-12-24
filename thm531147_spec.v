Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem531147 : (Nat.add (BIT0 (BIT1 0)) (BIT1 0)) = (BIT1 (Nat.add (BIT1 0) 0)).

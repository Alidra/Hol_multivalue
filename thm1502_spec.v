Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1502 : (((~ False) -> True) /\ (True -> ~ False)) = ((~ False) = True).

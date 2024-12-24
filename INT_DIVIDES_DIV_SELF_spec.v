Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2730195 : forall n : int, forall d : int, (int_divides d n) -> int_divides (div n d) n.

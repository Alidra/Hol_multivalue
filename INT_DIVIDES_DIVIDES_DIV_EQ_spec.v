Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2741943 : forall n : int, forall d : int, forall e : int, ((int_divides d n) /\ (int_divides e (div n d))) = (int_divides (int_mul d e) n).

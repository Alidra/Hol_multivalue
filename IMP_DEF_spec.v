Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9 : imp = (fun p : Prop => fun q : Prop => (p /\ q) = p).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1 : True = ((fun p : Prop => p) = (fun p : Prop => p)).

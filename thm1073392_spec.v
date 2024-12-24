Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073392 : forall (a : Prop), True = ((a -> False) = (~ a)).

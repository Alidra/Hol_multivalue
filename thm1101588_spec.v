Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1101588 : forall {_25328 : Type'} (P : _25328 -> Prop), ((fun P' : _25328 -> Prop => (@EX _25328 P' (@nil _25328)) = False) P) = ((@EX _25328 P (@nil _25328)) = False).

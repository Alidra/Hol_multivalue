Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem57695 : forall {A : Type'} (t : A), ((fun t' : A => (@LET_END A t') = t') t) = ((@LET_END A t) = t).

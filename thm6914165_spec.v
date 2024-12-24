Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6914165 : forall {_126338 : Type'}, (@isum _126338) = (@iterate int _126338 int_add).

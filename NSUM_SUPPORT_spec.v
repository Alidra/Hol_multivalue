Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6930330 : forall {_126695 : Type'}, forall f : _126695 -> nat, forall s : _126695 -> Prop, (@nsum _126695 (@support _126695 nat Nat.add f s) f) = (@nsum _126695 s f).

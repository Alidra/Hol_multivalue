Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183048 : forall {_83031 : Type'}, forall P : Prop, forall v : _83031, forall t : _83031, (@SETSPEC _83031 v P t) = (P /\ (v = t)).

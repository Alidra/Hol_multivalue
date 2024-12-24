Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3366870 : forall {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop), ((@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481)) /\ ((@IMAGE _87477 _87481 f (@INSERT _87477 x s)) = (@INSERT _87481 (f x) (@IMAGE _87477 _87481 f s))).

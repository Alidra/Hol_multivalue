Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3794808 : forall {_98584 _98585 : Type'}, forall f : _98585 -> _98584 -> _98584, forall b : _98584, forall s : _98585 -> Prop, forall a : _98584, (@FINREC _98585 _98584 f b s a (S (NUMERAL 0))) = (exists x : _98585, (s = (@INSERT _98585 x (@EMPTY _98585))) /\ (a = (f x b))).

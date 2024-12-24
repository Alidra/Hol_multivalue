Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3322101 : forall {_86801 : Type'}, (forall x : _86801, (@IN _86801 x (@UNIONS _86801 (@EMPTY (_86801 -> Prop)))) = (@IN _86801 x (@EMPTY _86801))) = ((@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801)).

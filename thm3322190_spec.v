Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3322190 : forall {_86807 : Type'} (s : _86807 -> Prop), (forall x : _86807, (@IN _86807 x (@UNIONS _86807 (@INSERT (_86807 -> Prop) s (@EMPTY (_86807 -> Prop))))) = (@IN _86807 x s)) = ((@UNIONS _86807 (@INSERT (_86807 -> Prop) s (@EMPTY (_86807 -> Prop)))) = s).

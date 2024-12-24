Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3358011 : forall {_87274 : Type'} (s : _87274 -> Prop) (u : (_87274 -> Prop) -> Prop), forall x : _87274, (@IN _87274 x (@INTERS _87274 (@INSERT (_87274 -> Prop) s u))) = (@IN _87274 x (@INTER _87274 s (@INTERS _87274 u))).

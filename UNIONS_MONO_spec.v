Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3348272 : forall {_87154 : Type'} (s : (_87154 -> Prop) -> Prop) (t : (_87154 -> Prop) -> Prop), (forall x : _87154 -> Prop, (@IN (_87154 -> Prop) x s) -> exists y : _87154 -> Prop, (@IN (_87154 -> Prop) y t) /\ (@SUBSET _87154 x y)) -> @SUBSET _87154 (@UNIONS _87154 s) (@UNIONS _87154 t).

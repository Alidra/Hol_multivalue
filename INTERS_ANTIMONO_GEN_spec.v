Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3364896 : forall {_87451 : Type'}, forall s : (_87451 -> Prop) -> Prop, forall t : (_87451 -> Prop) -> Prop, (forall y : _87451 -> Prop, (@IN (_87451 -> Prop) y t) -> exists x : _87451 -> Prop, (@IN (_87451 -> Prop) x s) /\ (@SUBSET _87451 x y)) -> @SUBSET _87451 (@INTERS _87451 s) (@INTERS _87451 t).

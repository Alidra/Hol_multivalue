Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3359672 : forall {_87290 : Type'}, forall s : _87290 -> Prop, forall f : (_87290 -> Prop) -> Prop, (@SUBSET _87290 s (@INTERS _87290 f)) = (forall t : _87290 -> Prop, (@IN (_87290 -> Prop) t f) -> @SUBSET _87290 s t).

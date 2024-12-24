Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3362368 : forall {_87386 : Type'}, forall f : (_87386 -> Prop) -> Prop, forall g : (_87386 -> Prop) -> Prop, (@SUBSET (_87386 -> Prop) g f) -> @SUBSET _87386 (@INTERS _87386 f) (@INTERS _87386 g).

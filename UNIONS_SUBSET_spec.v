Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3342997 : forall {_87042 : Type'}, forall f : (_87042 -> Prop) -> Prop, forall t : _87042 -> Prop, (@SUBSET _87042 (@UNIONS _87042 f) t) = (forall s : _87042 -> Prop, (@IN (_87042 -> Prop) s f) -> @SUBSET _87042 s t).

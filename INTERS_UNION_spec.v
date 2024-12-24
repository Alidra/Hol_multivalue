Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3346931 : forall {_87123 : Type'}, forall s : (_87123 -> Prop) -> Prop, forall t : (_87123 -> Prop) -> Prop, (@INTERS _87123 (@UNION (_87123 -> Prop) s t)) = (@INTER _87123 (@INTERS _87123 s) (@INTERS _87123 t)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3343813 : forall {_87075 : Type'}, forall f : (_87075 -> Prop) -> Prop, forall g : (_87075 -> Prop) -> Prop, (@SUBSET (_87075 -> Prop) f g) -> @SUBSET _87075 (@UNIONS _87075 f) (@UNIONS _87075 g).

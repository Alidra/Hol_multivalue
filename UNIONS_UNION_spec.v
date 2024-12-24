Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3345333 : forall {_87099 : Type'}, forall s : (_87099 -> Prop) -> Prop, forall t : (_87099 -> Prop) -> Prop, (@UNIONS _87099 (@UNION (_87099 -> Prop) s t)) = (@UNION _87099 (@UNIONS _87099 s) (@UNIONS _87099 t)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3354612 : forall {_87226 : Type'}, forall s : (_87226 -> Prop) -> Prop, (@UNIONS _87226 (@DELETE (_87226 -> Prop) s (@EMPTY _87226))) = (@UNIONS _87226 s).

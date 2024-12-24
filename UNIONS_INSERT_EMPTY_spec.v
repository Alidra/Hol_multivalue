Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3352566 : forall {_87210 : Type'}, forall s : (_87210 -> Prop) -> Prop, (@UNIONS _87210 (@INSERT (_87210 -> Prop) (@EMPTY _87210) s)) = (@UNIONS _87210 s).

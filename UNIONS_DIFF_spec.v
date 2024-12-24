Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3474654 : forall {_90144 : Type'}, forall s : (_90144 -> Prop) -> Prop, forall t : _90144 -> Prop, (@DIFF _90144 (@UNIONS _90144 s) t) = (@UNIONS _90144 (@GSPEC (_90144 -> Prop) (fun GEN_PVAR_67 : _90144 -> Prop => exists x : _90144 -> Prop, @SETSPEC (_90144 -> Prop) GEN_PVAR_67 (@IN (_90144 -> Prop) x s) (@DIFF _90144 x t)))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3477701 : forall {_90228 : Type'}, forall u : _90228 -> Prop, forall s : (_90228 -> Prop) -> Prop, (~ (s = (@EMPTY (_90228 -> Prop)))) -> (@DIFF _90228 u (@UNIONS _90228 s)) = (@INTERS _90228 (@GSPEC (_90228 -> Prop) (fun GEN_PVAR_69 : _90228 -> Prop => exists t : _90228 -> Prop, @SETSPEC (_90228 -> Prop) GEN_PVAR_69 (@IN (_90228 -> Prop) t s) (@DIFF _90228 u t)))).

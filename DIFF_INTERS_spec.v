Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3471961 : forall {_90037 : Type'}, forall u : _90037 -> Prop, forall s : (_90037 -> Prop) -> Prop, (@DIFF _90037 u (@INTERS _90037 s)) = (@UNIONS _90037 (@GSPEC (_90037 -> Prop) (fun GEN_PVAR_64 : _90037 -> Prop => exists t : _90037 -> Prop, @SETSPEC (_90037 -> Prop) GEN_PVAR_64 (@IN (_90037 -> Prop) t s) (@DIFF _90037 u t)))).

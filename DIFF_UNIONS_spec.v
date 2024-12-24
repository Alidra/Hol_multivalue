Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3476157 : forall {_90184 : Type'}, forall u : _90184 -> Prop, forall s : (_90184 -> Prop) -> Prop, (@DIFF _90184 u (@UNIONS _90184 s)) = (@INTER _90184 u (@INTERS _90184 (@GSPEC (_90184 -> Prop) (fun GEN_PVAR_68 : _90184 -> Prop => exists t : _90184 -> Prop, @SETSPEC (_90184 -> Prop) GEN_PVAR_68 (@IN (_90184 -> Prop) t s) (@DIFF _90184 u t))))).

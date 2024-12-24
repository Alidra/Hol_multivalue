Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3472199 : forall {_90072 : Type'}, forall s : (_90072 -> Prop) -> Prop, (@INTERS _90072 s) = (@DIFF _90072 (@UNIV _90072) (@UNIONS _90072 (@GSPEC (_90072 -> Prop) (fun GEN_PVAR_65 : _90072 -> Prop => exists t : _90072 -> Prop, @SETSPEC (_90072 -> Prop) GEN_PVAR_65 (@IN (_90072 -> Prop) t s) (@DIFF _90072 (@UNIV _90072) t))))).

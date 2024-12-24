Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3473248 : forall {_90107 : Type'}, forall s : (_90107 -> Prop) -> Prop, (@UNIONS _90107 s) = (@DIFF _90107 (@UNIV _90107) (@INTERS _90107 (@GSPEC (_90107 -> Prop) (fun GEN_PVAR_66 : _90107 -> Prop => exists t : _90107 -> Prop, @SETSPEC (_90107 -> Prop) GEN_PVAR_66 (@IN (_90107 -> Prop) t s) (@DIFF _90107 (@UNIV _90107) t))))).

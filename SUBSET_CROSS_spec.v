Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4339138 : forall {_104190 _104196 : Type'}, forall s : _104190 -> Prop, forall t : _104196 -> Prop, forall s' : _104190 -> Prop, forall t' : _104196 -> Prop, (@SUBSET (prod _104190 _104196) (@CROSS _104196 _104190 s t) (@CROSS _104196 _104190 s' t')) = ((s = (@EMPTY _104190)) \/ ((t = (@EMPTY _104196)) \/ ((@SUBSET _104190 s s') /\ (@SUBSET _104196 t t')))).

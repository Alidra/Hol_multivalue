Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4339269 : forall {_104241 _104242 : Type'}, forall s : _104241 -> Prop, forall t : _104242 -> Prop, forall s' : _104241 -> Prop, forall t' : _104242 -> Prop, ((@SUBSET _104241 s s') /\ (@SUBSET _104242 t t')) -> @SUBSET (prod _104241 _104242) (@CROSS _104242 _104241 s t) (@CROSS _104242 _104241 s' t').

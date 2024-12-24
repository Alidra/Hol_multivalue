Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3694570 : forall {_93870 _93890 : Type'}, forall P : (_93890 -> Prop) -> Prop, forall f : _93870 -> _93890, forall s : _93870 -> Prop, (forall t : _93890 -> Prop, ((@FINITE _93890 t) /\ (@SUBSET _93890 t (@IMAGE _93870 _93890 f s))) -> P t) = (forall t : _93870 -> Prop, ((@FINITE _93870 t) /\ (@SUBSET _93870 t s)) -> P (@IMAGE _93870 _93890 f t)).

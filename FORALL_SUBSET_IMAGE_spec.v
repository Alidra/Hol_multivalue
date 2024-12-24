Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3648775 : forall {_93408 _93424 : Type'}, forall P : (_93424 -> Prop) -> Prop, forall f : _93408 -> _93424, forall s : _93408 -> Prop, (forall t : _93424 -> Prop, (@SUBSET _93424 t (@IMAGE _93408 _93424 f s)) -> P t) = (forall t : _93408 -> Prop, (@SUBSET _93408 t s) -> P (@IMAGE _93408 _93424 f t)).

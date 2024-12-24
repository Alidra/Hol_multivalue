Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5719676 : forall {_119887 _119901 : Type'}, forall op : _119887 -> _119887 -> _119887, forall f : _119901 -> _119887, forall s : _119901 -> Prop, (forall x : _119901, (@IN _119901 x s) -> (f x) = (@neutral _119887 op)) = ((@support _119901 _119887 op f s) = (@EMPTY _119901)).

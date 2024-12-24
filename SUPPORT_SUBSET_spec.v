Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5719798 : forall {_119921 _119922 : Type'}, forall op : _119921 -> _119921 -> _119921, forall f : _119922 -> _119921, forall s : _119922 -> Prop, @SUBSET _119922 (@support _119922 _119921 op f s) s.

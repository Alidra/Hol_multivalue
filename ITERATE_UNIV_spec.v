Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6963073 : forall {_127673 _127692 : Type'}, forall op : _127673 -> _127673 -> _127673, (@monoidal _127673 op) -> forall f : _127692 -> _127673, forall s : _127692 -> Prop, (@SUBSET _127692 (@support _127692 _127673 op f (@UNIV _127692)) s) -> (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f).

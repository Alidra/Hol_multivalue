Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5738118 : forall {_120327 _120333 : Type'}, forall op : _120327 -> _120327 -> _120327, forall f : _120333 -> _120327, forall s : _120333 -> Prop, (@iterate _120327 _120333 op s f) = (@COND _120327 (@FINITE _120333 (@support _120333 _120327 op f s)) (@iterate _120327 _120333 op (@support _120333 _120327 op f s) f) (@neutral _120327 op)).

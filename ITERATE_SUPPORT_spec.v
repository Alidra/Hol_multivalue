Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5737860 : forall {_120296 _120308 : Type'}, forall op : _120296 -> _120296 -> _120296, forall f : _120308 -> _120296, forall s : _120308 -> Prop, (@iterate _120296 _120308 op (@support _120308 _120296 op f s) f) = (@iterate _120296 _120308 op s f).

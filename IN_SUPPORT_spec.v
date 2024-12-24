Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5718201 : forall {_119826 _119829 : Type'}, forall op : _119826 -> _119826 -> _119826, forall f : _119829 -> _119826, forall x : _119829, forall s : _119829 -> Prop, (@IN _119829 x (@support _119829 _119826 op f s)) = ((@IN _119829 x s) /\ (~ ((f x) = (@neutral _119826 op)))).

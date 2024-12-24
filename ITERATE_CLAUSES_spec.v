Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5753565 : forall {_120477 _120519 _120521 : Type'}, forall op : _120519 -> _120519 -> _120519, (@monoidal _120519 op) -> (forall f : _120477 -> _120519, (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)) /\ (forall f : _120521 -> _120519, forall x : _120521, forall s : _120521 -> Prop, (@FINITE _120521 s) -> (@iterate _120519 _120521 op (@INSERT _120521 x s) f) = (@COND _120519 (@IN _120521 x s) (@iterate _120519 _120521 op s f) (op (f x) (@iterate _120519 _120521 op s f)))).

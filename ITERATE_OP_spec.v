Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6013661 : forall {_122572 _122573 : Type'}, forall op : _122573 -> _122573 -> _122573, (@monoidal _122573 op) -> forall f : _122572 -> _122573, forall g : _122572 -> _122573, forall s : _122572 -> Prop, (@FINITE _122572 s) -> (@iterate _122573 _122572 op s (fun x : _122572 => op (f x) (g x))) = (op (@iterate _122573 _122572 op s f) (@iterate _122573 _122572 op s g)).

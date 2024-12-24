Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7068796 : forall {_131713 : Type'}, forall f : _131713 -> real, forall g : _131713 -> real, forall s : _131713 -> Prop, (@FINITE _131713 s) -> (@sum _131713 s (fun x : _131713 => real_add (f x) (g x))) = (real_add (@sum _131713 s f) (@sum _131713 s g)).

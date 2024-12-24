Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261440 : forall {_137613 : Type'}, forall f : _137613 -> real, forall g : _137613 -> real, forall s : _137613 -> Prop, (forall x : _137613, (@IN _137613 x s) -> (f x) = (g x)) -> (@sum _137613 s (fun i : _137613 => f i)) = (@sum _137613 s g).

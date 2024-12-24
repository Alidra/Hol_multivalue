Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261449 : forall {_137613 : Type'} (f : _137613 -> real) (g : _137613 -> real) (s : _137613 -> Prop), (fun s' : _137613 -> Prop => (forall x : _137613, (@IN _137613 x s') -> (f x) = (g x)) -> (@sum _137613 s' (fun i : _137613 => f i)) = (@sum _137613 s' g)) s.

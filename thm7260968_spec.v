Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7260968 : forall {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real), (forall x : _137613, (@IN _137613 x s) -> ((fun i : _137613 => f i) x) = (g x)) -> (@sum _137613 s (fun i : _137613 => f i)) = (@sum _137613 s g).

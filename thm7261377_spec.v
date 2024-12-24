Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261377 : forall {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : forall x : _137613, (@IN _137613 x s) -> (f x) = (g x)), (@sum _137613 s (fun i : _137613 => f i)) = (@sum _137613 s g).

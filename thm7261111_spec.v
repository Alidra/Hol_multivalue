Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7261111 : forall {_137613 : Type'} (s : _137613 -> Prop) (f : _137613 -> real) (g : _137613 -> real) (h1 : forall x : _137613, (@IN _137613 x s) -> (f x) = (g x)), forall x : _137613, (@IN _137613 x s) -> ((fun i : _137613 => f i) x) = (g x).

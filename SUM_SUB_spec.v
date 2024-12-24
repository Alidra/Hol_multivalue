Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7071000 : forall {_132039 : Type'}, forall f : _132039 -> real, forall g : _132039 -> real, forall s : _132039 -> Prop, (@FINITE _132039 s) -> (@sum _132039 s (fun x : _132039 => real_sub (f x) (g x))) = (real_sub (@sum _132039 s f) (@sum _132039 s g)).

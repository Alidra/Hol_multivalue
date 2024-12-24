Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6930477 : forall {_126729 : Type'}, forall f : _126729 -> nat, forall g : _126729 -> nat, forall s : _126729 -> Prop, (@FINITE _126729 s) -> (@nsum _126729 s (fun x : _126729 => Nat.add (f x) (g x))) = (Nat.add (@nsum _126729 s f) (@nsum _126729 s g)).

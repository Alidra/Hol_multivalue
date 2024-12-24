Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6932066 : forall {A : Type'}, forall f : A -> nat, forall c : nat, forall s : A -> Prop, (@nsum A s (fun x : A => Nat.mul c (f x))) = (Nat.mul c (@nsum A s f)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7070368 : forall {A : Type'}, forall f : A -> real, forall c : real, forall s : A -> Prop, (@sum A s (fun x : A => real_mul (f x) c)) = (real_mul (@sum A s f) c).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6932170 : forall {A : Type'}, forall f : A -> nat, forall c : nat, forall s : A -> Prop, (@nsum A s (fun x : A => Nat.mul (f x) c)) = (Nat.mul (@nsum A s f) c).

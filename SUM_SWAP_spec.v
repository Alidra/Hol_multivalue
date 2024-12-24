Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7124408 : forall {A B : Type'}, forall f : A -> B -> real, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@FINITE B t)) -> (@sum A s (fun i : A => @sum B t (f i))) = (@sum B t (fun j : B => @sum A s (fun i : A => f i j))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6961567 : forall {A B : Type'}, forall f : A -> B -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@FINITE B t)) -> (@nsum A s (fun i : A => @nsum B t (f i))) = (@nsum B t (fun j : B => @nsum A s (fun i : A => f i j))).

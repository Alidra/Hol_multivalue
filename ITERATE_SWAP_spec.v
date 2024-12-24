Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6113745 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B -> C, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@FINITE B t)) -> (@iterate C A op s (fun i : A => @iterate C B op t (f i))) = (@iterate C B op t (fun j : B => @iterate C A op s (fun i : A => f i j))).

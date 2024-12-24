Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6007453 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A s) /\ ((@FINITE A t) /\ (forall x : A, (@IN A x (@INTER A s t)) -> (f x) = (@neutral B op)))) -> (@iterate B A op (@UNION A s t) f) = (op (@iterate B A op s f) (@iterate B A op t f)).

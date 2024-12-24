Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6184258 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@FINITE A (@support A B op f s)) /\ (@FINITE A (@support A B op g s))) -> (@iterate B A op s (fun x : A => op (f x) (g x))) = (op (@iterate B A op s f) (@iterate B A op s g)).

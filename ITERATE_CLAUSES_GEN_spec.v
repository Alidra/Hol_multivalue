Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5753234 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> (forall f : A -> B, (@iterate B A op (@EMPTY A) f) = (@neutral B op)) /\ (forall f : A -> B, forall x : A, forall s : A -> Prop, (@FINITE A (@support A B op f s)) -> (@iterate B A op (@INSERT A x s) f) = (@COND B (@IN A x s) (@iterate B A op s f) (op (f x) (@iterate B A op s f)))).

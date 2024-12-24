Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6000071 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall s : A -> Prop, forall t : B -> Prop, forall f : A -> C, forall g : B -> C, forall h : A -> B, forall k : B -> A, ((forall y : B, (@IN B y t) -> (@IN A (k y) s) /\ ((h (k y)) = y)) /\ (forall x : A, (@IN A x s) -> (@IN B (h x) t) /\ (((k (h x)) = x) /\ ((g (h x)) = (f x))))) -> (@iterate C A op s f) = (@iterate C B op t g).

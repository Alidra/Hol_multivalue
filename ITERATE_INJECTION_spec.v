Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6003902 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((p x) = (p y)))) -> x = y))) -> (@iterate B A op s (@o A A B f p)) = (@iterate B A op s f).

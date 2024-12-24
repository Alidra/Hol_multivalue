Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5947359 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@iterate B A op s f) = (@iterate B A op s (@o A A B f p)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7017950 : forall {A : Type'}, forall f : A -> nat, forall p : A -> A, forall s : A -> Prop, ((forall x : A, (@IN A x s) -> @IN A (p x) s) /\ (forall y : A, (@IN A y s) -> @ex1 A (fun x : A => (@IN A x s) /\ ((p x) = y)))) -> (@nsum A s f) = (@nsum A s (@o A A nat f p)).

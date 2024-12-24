Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5824997 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, forall a : A, ((@FINITE A s) /\ (@IN A a s)) -> (op (f a) (@iterate B A op (@DELETE A s a) f)) = (@iterate B A op s f).

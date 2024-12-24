Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3790997 : forall {A B : Type'}, (forall f : A -> B -> B, forall s : A -> Prop, forall a : B, forall b : B, (@FINREC A B f b s a (NUMERAL 0)) = ((s = (@EMPTY A)) /\ (a = b))) /\ (forall b : B, forall s : A -> Prop, forall n : nat, forall a : B, forall f : A -> B -> B, (@FINREC A B f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((@FINREC A B f b (@DELETE A s x) c n) /\ (a = (f x c))))).

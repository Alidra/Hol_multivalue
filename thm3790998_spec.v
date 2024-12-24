Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3790998 : forall {A B : Type'}, forall b : B, forall s : A -> Prop, forall n : nat, forall a : B, forall f : A -> B -> B, (@FINREC A B f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((@FINREC A B f b (@DELETE A s x) c n) /\ (a = (f x c)))).

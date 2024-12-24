Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3791027 : forall {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : A -> B -> B), ((@FINREC A B f b s a (NUMERAL 0)) = ((s = (@EMPTY A)) /\ (a = b))) /\ ((@FINREC A B f b s a (S n)) = (exists x : A, exists c : B, (@IN A x s) /\ ((@FINREC A B f b (@DELETE A s x) c n) /\ (a = (f x c))))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3845383 : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@FINITE A s) -> (@CARD A (@DELETE A s x)) = (@COND nat (@IN A x s) (Nat.sub (@CARD A s) (NUMERAL (BIT1 0))) (@CARD A s)).

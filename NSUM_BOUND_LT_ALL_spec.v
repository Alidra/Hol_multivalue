Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6980150 : forall {_128066 : Type'}, forall s : _128066 -> Prop, forall f : _128066 -> nat, forall b : nat, ((@FINITE _128066 s) /\ ((~ (s = (@EMPTY _128066))) /\ (forall x : _128066, (@IN _128066 x s) -> Peano.lt (f x) b))) -> Peano.lt (@nsum _128066 s f) (Nat.mul (@CARD _128066 s) b).

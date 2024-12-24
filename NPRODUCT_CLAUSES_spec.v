Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6903343 : forall {_126132 _126171 : Type'}, (forall f : _126132 -> nat, (@nproduct _126132 (@EMPTY _126132) f) = (NUMERAL (BIT1 0))) /\ (forall x : _126171, forall f : _126171 -> nat, forall s : _126171 -> Prop, (@FINITE _126171 s) -> (@nproduct _126171 (@INSERT _126171 x s) f) = (@COND nat (@IN _126171 x s) (@nproduct _126171 s f) (Nat.mul (f x) (@nproduct _126171 s f)))).

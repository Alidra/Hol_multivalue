Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6912941 : forall {_126288 _126329 : Type'}, (forall f : _126288 -> real, (@product _126288 (@EMPTY _126288) f) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall x : _126329, forall f : _126329 -> real, forall s : _126329 -> Prop, (@FINITE _126329 s) -> (@product _126329 (@INSERT _126329 x s) f) = (@COND real (@IN _126329 x s) (@product _126329 s f) (real_mul (f x) (@product _126329 s f)))).

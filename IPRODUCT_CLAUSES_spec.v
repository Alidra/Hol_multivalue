Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6908823 : forall {_126209 _126250 : Type'}, (forall f : _126209 -> int, (@iproduct _126209 (@EMPTY _126209) f) = (int_of_num (NUMERAL (BIT1 0)))) /\ (forall x : _126250, forall f : _126250 -> int, forall s : _126250 -> Prop, (@FINITE _126250 s) -> (@iproduct _126250 (@INSERT _126250 x s) f) = (@COND int (@IN _126250 x s) (@iproduct _126250 s f) (int_mul (f x) (@iproduct _126250 s f)))).

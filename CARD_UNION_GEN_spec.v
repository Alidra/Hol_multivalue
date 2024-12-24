Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3947439 : forall {_101385 : Type'}, forall s : _101385 -> Prop, forall t : _101385 -> Prop, ((@FINITE _101385 s) /\ (@FINITE _101385 t)) -> (@CARD _101385 (@UNION _101385 s t)) = (Nat.sub (Nat.add (@CARD _101385 s) (@CARD _101385 t)) (@CARD _101385 (@INTER _101385 s t))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3969598 : forall {_101466 : Type'}, forall s : _101466 -> Prop, forall t : _101466 -> Prop, ((@FINITE _101466 s) /\ (@FINITE _101466 t)) -> ((@CARD _101466 (@UNION _101466 s t)) = (Nat.add (@CARD _101466 s) (@CARD _101466 t))) = ((@INTER _101466 s t) = (@EMPTY _101466)).

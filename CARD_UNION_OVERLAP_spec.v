Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3971264 : forall {_101508 : Type'}, forall s : _101508 -> Prop, forall t : _101508 -> Prop, ((@FINITE _101508 s) /\ ((@FINITE _101508 t) /\ (Peano.lt (@CARD _101508 (@UNION _101508 s t)) (Nat.add (@CARD _101508 s) (@CARD _101508 t))))) -> ~ ((@INTER _101508 s t) = (@EMPTY _101508)).

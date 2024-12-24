Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem38926 : forall {Absty Repty : Type'} (R : Repty -> Repty -> Prop) (dest : Absty -> Repty -> Prop) (mk : (Repty -> Prop) -> Absty) (h1 : (forall x : Repty, R x x) /\ ((forall x : Repty, forall y : Repty, (R x y) = (R y x)) /\ ((forall x : Repty, forall y : Repty, forall z : Repty, ((R x y) /\ (R y z)) -> R x z) /\ ((forall a : Absty, (mk (dest a)) = a) /\ (forall r : Repty -> Prop, (exists x : Repty, r = (R x)) = ((dest (mk r)) = r)))))), (forall x : Repty, forall y : Repty, (R x y) = ((mk (R x)) = (mk (R y)))) /\ ((forall P : Absty -> Prop, (forall x : Repty, P (mk (R x))) = (forall x : Absty, P x)) /\ ((forall P : Absty -> Prop, (exists x : Repty, P (mk (R x))) = (exists x : Absty, P x)) /\ (forall x : Absty, (mk (R (@ε Repty (dest x)))) = x))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3892937 : forall {_100554 : Type'} (b : _100554) (a : _100554) (cs : _100554 -> Prop) (P : Prop), (((~ (@IN _100554 a (@INSERT _100554 b (@EMPTY _100554)))) /\ P) = ((~ (a = b)) /\ P)) /\ (((~ (@IN _100554 a (@INSERT _100554 b cs))) /\ P) = ((~ (a = b)) /\ ((~ (@IN _100554 a cs)) /\ P))).

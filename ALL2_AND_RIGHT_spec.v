Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1129352 : forall {_26588 _26589 : Type'}, forall l : list _26589, forall m : list _26588, forall P : _26589 -> Prop, forall Q : _26589 -> _26588 -> Prop, (@ALL2 _26589 _26588 (fun x : _26589 => fun y : _26588 => (P x) /\ (Q x y)) l m) = ((@List.Forall _26589 P l) /\ (@ALL2 _26589 _26588 Q l m)).

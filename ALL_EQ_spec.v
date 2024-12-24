Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1124075 : forall {_26443 : Type'} (R : _26443 -> Prop) (P : _26443 -> Prop) (Q : _26443 -> Prop), forall l : list _26443, ((@List.Forall _26443 R l) /\ (forall x : _26443, (R x) -> (P x) = (Q x))) -> (@List.Forall _26443 P l) = (@List.Forall _26443 Q l).

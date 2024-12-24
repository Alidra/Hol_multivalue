Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1123316 : forall {_26340 : Type'}, forall P : _26340 -> Prop, forall Q : _26340 -> Prop, forall l : list _26340, ((forall x : _26340, ((@List.In _26340 x l) /\ (P x)) -> Q x) /\ (@List.Forall _26340 P l)) -> @List.Forall _26340 Q l.

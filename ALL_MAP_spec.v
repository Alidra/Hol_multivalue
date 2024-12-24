Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1123794 : forall {_26411 _26412 : Type'}, forall P : _26412 -> Prop, forall f : _26411 -> _26412, forall l : list _26411, (@List.Forall _26412 P (@List.map _26411 _26412 f l)) = (@List.Forall _26411 (@o _26411 _26412 Prop P f) l).

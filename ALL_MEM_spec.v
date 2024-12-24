Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1138070 : forall {_26777 : Type'}, forall P : _26777 -> Prop, forall l : list _26777, (forall x : _26777, (@List.In _26777 x l) -> P x) = (@List.Forall _26777 P l).

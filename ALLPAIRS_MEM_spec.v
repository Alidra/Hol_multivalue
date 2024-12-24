Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1181594 : forall {_27494 _27495 : Type'}, forall P : _27495 -> _27494 -> Prop, forall l : list _27495, forall m : list _27494, (forall x : _27495, forall y : _27494, ((@List.In _27495 x l) /\ (@List.In _27494 y m)) -> P x y) = (@ALLPAIRS _27494 _27495 P l m).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1128211 : forall {_26486 _26497 : Type'} (f : _26486 -> _26497), forall l : list _26486, forall m : list _26486, (@ALL2 _26486 _26486 (fun x : _26486 => fun y : _26486 => (f x) = (f y)) l m) -> (@List.map _26486 _26497 f l) = (@List.map _26486 _26497 f m).

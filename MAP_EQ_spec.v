Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1120972 : forall {_26299 _26310 : Type'}, forall f : _26299 -> _26310, forall g : _26299 -> _26310, forall l : list _26299, (@List.Forall _26299 (fun x : _26299 => (f x) = (g x)) l) -> (@List.map _26299 _26310 f l) = (@List.map _26299 _26310 g l).

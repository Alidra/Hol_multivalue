Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1128657 : forall {_26546 : Type'}, forall l : list _26546, forall f : _26546 -> _26546, (@List.Forall _26546 (fun x : _26546 => (f x) = x) l) -> (@List.map _26546 _26546 f l) = l.

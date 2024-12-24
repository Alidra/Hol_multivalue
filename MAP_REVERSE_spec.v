Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1207671 : forall {_28392 _28394 : Type'}, forall f : _28394 -> _28392, forall l : list _28394, (@List.rev _28392 (@List.map _28394 _28392 f l)) = (@List.map _28394 _28392 f (@List.rev _28394 l)).

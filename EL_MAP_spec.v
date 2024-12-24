Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1207492 : forall {_28366 _28367 : Type'}, forall f : _28367 -> _28366, forall n : nat, forall l : list _28367, (Peano.lt n (@List.length _28367 l)) -> (@EL _28366 n (@List.map _28367 _28366 f l)) = (f (@EL _28367 n l)).

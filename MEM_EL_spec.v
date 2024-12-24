Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1160771 : forall {_27264 : Type'}, forall l : list _27264, forall n : nat, (Peano.lt n (@List.length _27264 l)) -> @List.In _27264 (@EL _27264 n l) l.

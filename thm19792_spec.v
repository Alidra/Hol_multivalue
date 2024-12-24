Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem19792 : forall {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571), True = ((s = (fun x : _3575 => t x)) = (forall x : _3575, (s x) = (t x))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105052 : forall {_25498 _25501 _25508 : Type'} (f : _25501 -> _25508 -> _25498) (l : list _25508), (fun l' : list _25508 => (@MAP2 _25498 _25501 _25508 f (@nil _25501) l') = (@nil _25498)) l.

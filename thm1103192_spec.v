Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1103192 : forall {_25376 : Type'} (x : _25376), ((fun x' : _25376 => (@List.In _25376 x' (@nil _25376)) = False) x) = ((@List.In _25376 x (@nil _25376)) = False).
Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1094866 : forall {A : Type'} (t : list A) (h : A), ((fun h' : A => (@hd A (@cons A h' t)) = h') h) = ((@hd A (@cons A h t)) = h).

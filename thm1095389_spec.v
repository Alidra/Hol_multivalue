Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1095389 : forall {A : Type'} (h : A) (t : list A), ((fun t' : list A => (@tl A (@cons A h t')) = t') t) = ((@tl A (@cons A h t)) = t).

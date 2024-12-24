Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1098348 : forall {A : Type'} (h : A) (t : list A), ((fun t' : list A => (@LAST A (@cons A h t')) = (@COND A (t' = (@nil A)) h (@LAST A t'))) t) = ((@LAST A (@cons A h t)) = (@COND A (t = (@nil A)) h (@LAST A t))).

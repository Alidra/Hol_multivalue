Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1117066 : forall {A : Type'}, forall l : list A, ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).

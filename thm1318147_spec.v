Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318147 : forall (x : nadd) (y : nadd), ((hreal_le (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y))) = (nadd_le x y)) = ((nadd_le x y) = (hreal_le (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y)))).

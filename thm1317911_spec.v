Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1317911 : forall (x : nadd) (y : nadd), ((hreal_add (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y))) = (mk_hreal (nadd_eq (nadd_add x y)))) = ((mk_hreal (nadd_eq (nadd_add x y))) = (hreal_add (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y)))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318035 : forall (x : nadd) (y : nadd), ((hreal_mul (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y))) = (mk_hreal (nadd_eq (nadd_mul x y)))) = ((mk_hreal (nadd_eq (nadd_mul x y))) = (hreal_mul (mk_hreal (nadd_eq x)) (mk_hreal (nadd_eq y)))).

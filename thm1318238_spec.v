Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318238 : forall (x : nadd), ((hreal_inv (mk_hreal (nadd_eq x))) = (mk_hreal (nadd_eq (nadd_inv x)))) = ((mk_hreal (nadd_eq (nadd_inv x))) = (hreal_inv (mk_hreal (nadd_eq x)))).
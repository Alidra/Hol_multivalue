Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318766 : forall (x : nadd) (y : nadd), (fun y' : nadd => (nadd_eq x y') = ((mk_hreal (nadd_eq x)) = (mk_hreal (nadd_eq y')))) y.

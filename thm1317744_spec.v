Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1317744 : forall (r : nadd -> Prop), (exists x : nadd, r = (nadd_eq x)) = ((dest_hreal (mk_hreal r)) = r).

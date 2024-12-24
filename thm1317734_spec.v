Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1317734 : forall (x : nadd), (fun s : nadd -> Prop => exists x' : nadd, s = (nadd_eq x')) (nadd_eq x).

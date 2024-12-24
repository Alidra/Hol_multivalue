Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337483 : forall (x : prod hreal hreal), (fun s : (prod hreal hreal) -> Prop => exists x' : prod hreal hreal, s = (treal_eq x')) (treal_eq x).

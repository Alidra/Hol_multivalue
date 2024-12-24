Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6910091 : forall {A : Type'} (P : A -> Prop) (x : A), (fun x' : A => (forall y : A, (P y) = (y = x')) -> (@ε A P) = x') x.

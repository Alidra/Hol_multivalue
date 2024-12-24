Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6931080 : forall {A : Type'}, forall s : A -> Prop, (@nsum A s (fun n : A => NUMERAL 0)) = (NUMERAL 0).

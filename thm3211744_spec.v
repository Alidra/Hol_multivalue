Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211744 : forall {A : Type'} (s : A -> Prop) (t : A -> Prop), (fun t' : A -> Prop => (@PSUBSET A s t') = ((@SUBSET A s t') /\ (~ (s = t')))) t.

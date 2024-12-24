Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3203700 : forall {A : Type'}, forall s : A -> Prop, (@CHOICE A s) = (@ε A (fun x : A => @IN A x s)).

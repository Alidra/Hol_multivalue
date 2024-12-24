Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211692 : forall {A : Type'} (y : A) (x : A) (s : A -> Prop), (fun s' : A -> Prop => (@IN A x (@INSERT A y s')) = ((x = y) \/ (@IN A x s'))) s.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7637147 : forall {A : Type'} (s : A -> Prop), ((fun s' : A -> Prop => (@dimindex A s') = (@dimindex A (@UNIV A))) s) = ((@dimindex A s) = (@dimindex A (@UNIV A))).

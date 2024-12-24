Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6889194 : forall {A K : Type'}, forall op : A -> A -> A, forall ltle : K -> K -> Prop, (@monoidal A op) -> (@iterato A K (@UNIV A) (@neutral A op) op ltle) = (@iterate A K op).

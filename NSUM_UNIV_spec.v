Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6962209 : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@SUBSET A (@support A nat Nat.add f (@UNIV A)) s) -> (@nsum A s f) = (@nsum A (@UNIV A) f).

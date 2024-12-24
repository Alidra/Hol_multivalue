Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1110674 : forall {A : Type'} (r : A -> A -> Prop), (@List.ForallOrdPairs A r (@nil A)) = True.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1110673 : forall {A : Type'} (r : A -> A -> Prop), ((fun r' : A -> A -> Prop => (@List.ForallOrdPairs A r' (@nil A)) = True) r) = ((@List.ForallOrdPairs A r (@nil A)) = True).

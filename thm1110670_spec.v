Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1110670 : forall {A : Type'}, forall h : A, forall r : A -> A -> Prop, forall t : list A, (@List.ForallOrdPairs A r (@cons A h t)) = ((@List.Forall A (r h) t) /\ (@List.ForallOrdPairs A r t)).
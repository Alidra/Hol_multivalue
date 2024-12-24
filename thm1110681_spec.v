Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1110681 : forall {A : Type'} (h : A) (r : A -> A -> Prop) (t : list A), (fun t' : list A => (@List.ForallOrdPairs A r (@cons A h t')) = ((@List.Forall A (r h) t') /\ (@List.ForallOrdPairs A r t'))) t.

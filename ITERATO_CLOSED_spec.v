Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6875679 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall P : A -> Prop, ((P neut) /\ ((forall x : A, forall y : A, ((P x) /\ (P y)) -> P (op x y)) /\ (forall i : K, ((@IN K i k) /\ ((@IN A (f i) dom) /\ (~ ((f i) = neut)))) -> P (f i)))) -> P (@iterato A K dom neut op ltle k f).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6861305 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, forall g : K -> A, (forall i : K, (@IN K i k) -> (f i) = (g i)) -> (@iterato A K dom neut op ltle k f) = (@iterato A K dom neut op ltle k g).

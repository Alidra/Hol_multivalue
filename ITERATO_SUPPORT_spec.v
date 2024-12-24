Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6449238 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_268 : K => exists i : K, @SETSPEC K GEN_PVAR_268 ((@IN K i k) /\ (@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) i)) f) = (@iterato A K dom neut op ltle k f).

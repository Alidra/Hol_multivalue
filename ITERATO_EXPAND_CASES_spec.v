Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6449478 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall k : K -> Prop, forall f : K -> A, (@iterato A K dom neut op ltle k f) = (@COND A (@FINITE K (@GSPEC K (fun GEN_PVAR_269 : K => exists i : K, @SETSPEC K GEN_PVAR_269 ((@IN K i k) /\ (@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) i))) (@iterato A K dom neut op ltle (@GSPEC K (fun GEN_PVAR_270 : K => exists i : K, @SETSPEC K GEN_PVAR_270 ((@IN K i k) /\ (@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) i)) f) neut).

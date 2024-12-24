Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6790065 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut) /\ (forall k : K -> Prop, ((@FINITE K (@GSPEC K (fun GEN_PVAR_274 : K => exists i : K, @SETSPEC K GEN_PVAR_274 ((@IN K i k) /\ (@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) i))) /\ (~ ((@GSPEC K (fun GEN_PVAR_275 : K => exists i : K, @SETSPEC K GEN_PVAR_275 ((@IN K i k) /\ (@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) i)) = (@EMPTY K)))) -> exists i : K, (@IN K i k) /\ ((@IN A (f i) (@DIFF A dom (@INSERT A neut (@EMPTY A)))) /\ ((@iterato A K dom neut op ltle k f) = (op (f i) (@iterato A K dom neut op ltle (@DELETE K k i) f))))).

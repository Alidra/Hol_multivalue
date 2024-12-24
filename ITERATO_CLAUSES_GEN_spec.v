Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6774661 : forall {A K : Type'}, forall dom : A -> Prop, forall neut : A, forall op : A -> A -> A, forall ltle : K -> K -> Prop, forall f : K -> A, ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut) /\ (forall i : K, forall k : K -> Prop, ((@FINITE K (@GSPEC K (fun GEN_PVAR_272 : K => exists j : K, @SETSPEC K GEN_PVAR_272 ((@IN K j k) /\ (@IN A (f j) (@DIFF A dom (@INSERT A neut (@EMPTY A))))) j))) /\ ((forall j : K, (@IN K j k) -> (i = j) \/ ((ltle i j) \/ (ltle j i))) /\ (forall j : K, ((ltle j i) /\ ((@IN K j k) /\ (@IN A (f j) (@DIFF A dom (@INSERT A neut (@EMPTY A)))))) -> j = i))) -> (@iterato A K dom neut op ltle (@INSERT K i k) f) = (@COND A ((@IN A (f i) dom) -> ((f i) = neut) \/ (@IN K i k)) (@iterato A K dom neut op ltle k f) (op (f i) (@iterato A K dom neut op ltle k f)))).

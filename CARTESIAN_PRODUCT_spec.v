Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4403516 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_141 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_141 (forall i : K, @IN A (f i) (@COND (A -> Prop) (@IN K i k) (s i) (@INSERT A (@ARB A) (@EMPTY A)))) f)).

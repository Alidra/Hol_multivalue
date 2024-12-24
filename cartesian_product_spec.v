Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4399444 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@cartesian_product A K k s) = (@GSPEC (K -> A) (fun GEN_PVAR_140 : K -> A => exists f : K -> A, @SETSPEC (K -> A) GEN_PVAR_140 ((@EXTENSIONAL K A k f) /\ (forall i : K, (@IN K i k) -> @IN A (f i) (s i))) f)).

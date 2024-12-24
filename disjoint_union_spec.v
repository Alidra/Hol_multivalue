Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4464464 : forall {A K : Type'}, forall k : K -> Prop, forall s : K -> A -> Prop, (@disjoint_union A K k s) = (@GSPEC (prod K A) (fun GEN_PVAR_143 : prod K A => exists i : K, exists x : A, @SETSPEC (prod K A) GEN_PVAR_143 ((@IN K i k) /\ (@IN A x (s i))) (@pair K A i x))).

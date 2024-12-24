Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4620674 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, forall k : A -> B, ((@FINITE A s) /\ (@FINITE B t)) -> @FINITE (A -> B) (@GSPEC (A -> B) (fun GEN_PVAR_178 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_178 ((@SUBSET B (@IMAGE A B f s) t) /\ (@SUBSET A (@GSPEC A (fun GEN_PVAR_177 : A => exists x : A, @SETSPEC A GEN_PVAR_177 (~ ((f x) = (k x))) x)) s)) f)).

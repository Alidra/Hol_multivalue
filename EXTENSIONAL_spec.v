Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4382798 : forall {A B : Type'}, forall s : A -> Prop, (@EXTENSIONAL A B s) = (@GSPEC (A -> B) (fun GEN_PVAR_139 : A -> B => exists f : A -> B, @SETSPEC (A -> B) GEN_PVAR_139 (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)) f)).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3465953 : forall {A : Type'}, forall s : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_63 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_63 (@IN A x s) (@INSERT A x (@EMPTY A))))) = s.

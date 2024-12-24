Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3465181 : forall {A : Type'}, forall P : A -> Prop, (@UNIONS A (@GSPEC (A -> Prop) (fun GEN_PVAR_61 : A -> Prop => exists x : A, @SETSPEC (A -> Prop) GEN_PVAR_61 (P x) (@INSERT A x (@EMPTY A))))) = (@GSPEC A (fun GEN_PVAR_62 : A => exists x : A, @SETSPEC A GEN_PVAR_62 (P x) x)).

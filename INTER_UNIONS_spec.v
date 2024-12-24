Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3341279 : forall {_86990 _87026 : Type'}, (forall s : (_86990 -> Prop) -> Prop, forall t : _86990 -> Prop, (@INTER _86990 (@UNIONS _86990 s) t) = (@UNIONS _86990 (@GSPEC (_86990 -> Prop) (fun GEN_PVAR_21 : _86990 -> Prop => exists x : _86990 -> Prop, @SETSPEC (_86990 -> Prop) GEN_PVAR_21 (@IN (_86990 -> Prop) x s) (@INTER _86990 x t))))) /\ (forall s : (_87026 -> Prop) -> Prop, forall t : _87026 -> Prop, (@INTER _87026 t (@UNIONS _87026 s)) = (@UNIONS _87026 (@GSPEC (_87026 -> Prop) (fun GEN_PVAR_22 : _87026 -> Prop => exists x : _87026 -> Prop, @SETSPEC (_87026 -> Prop) GEN_PVAR_22 (@IN (_87026 -> Prop) x s) (@INTER _87026 t x))))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6160738 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall s : A -> Prop, forall P : A -> Prop, forall f : A -> B, forall g : A -> B, (@FINITE A s) -> (@iterate B A op s (fun x : A => @COND B (P x) (f x) (g x))) = (op (@iterate B A op (@GSPEC A (fun GEN_PVAR_248 : A => exists x : A, @SETSPEC A GEN_PVAR_248 ((@IN A x s) /\ (P x)) x)) f) (@iterate B A op (@GSPEC A (fun GEN_PVAR_249 : A => exists x : A, @SETSPEC A GEN_PVAR_249 ((@IN A x s) /\ (~ (P x))) x)) g)).

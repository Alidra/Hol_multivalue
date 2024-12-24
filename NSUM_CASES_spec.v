Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7028681 : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> nat, forall g : A -> nat, (@FINITE A s) -> (@nsum A s (fun x : A => @COND nat (P x) (f x) (g x))) = (Nat.add (@nsum A (@GSPEC A (fun GEN_PVAR_301 : A => exists x : A, @SETSPEC A GEN_PVAR_301 ((@IN A x s) /\ (P x)) x)) f) (@nsum A (@GSPEC A (fun GEN_PVAR_302 : A => exists x : A, @SETSPEC A GEN_PVAR_302 ((@IN A x s) /\ (~ (P x))) x)) g)).

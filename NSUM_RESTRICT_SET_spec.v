Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6990944 : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall f : A -> nat, (@nsum A (@GSPEC A (fun GEN_PVAR_287 : A => exists x : A, @SETSPEC A GEN_PVAR_287 ((@IN A x s) /\ (P x)) x)) f) = (@nsum A s (fun x : A => @COND nat (P x) (f x) (NUMERAL 0))).

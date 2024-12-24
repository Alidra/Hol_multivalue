Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6992800 : forall {A B : Type'}, forall R : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> nat, ((@FINITE A s) /\ ((@FINITE B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_291 : A => exists i : A, @SETSPEC A GEN_PVAR_291 ((@IN A i s) /\ (R i j)) i))) = (k j)))) -> (@nsum A s (fun i : A => @CARD B (@GSPEC B (fun GEN_PVAR_292 : B => exists j : B, @SETSPEC B GEN_PVAR_292 ((@IN B j t) /\ (R i j)) j)))) = (@nsum B t (fun i : B => k i)).

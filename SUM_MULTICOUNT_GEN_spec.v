Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7158866 : forall {A B : Type'}, forall R : A -> B -> Prop, forall s : A -> Prop, forall t : B -> Prop, forall k : B -> nat, ((@FINITE A s) /\ ((@FINITE B t) /\ (forall j : B, (@IN B j t) -> (@CARD A (@GSPEC A (fun GEN_PVAR_320 : A => exists i : A, @SETSPEC A GEN_PVAR_320 ((@IN A i s) /\ (R i j)) i))) = (k j)))) -> (@sum A s (fun i : A => real_of_num (@CARD B (@GSPEC B (fun GEN_PVAR_321 : B => exists j : B, @SETSPEC B GEN_PVAR_321 ((@IN B j t) /\ (R i j)) j))))) = (@sum B t (fun i : B => real_of_num (k i))).

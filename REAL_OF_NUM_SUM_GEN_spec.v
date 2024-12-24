Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7210021 : forall {A : Type'}, forall f : A -> nat, forall s : A -> Prop, (@FINITE A (@GSPEC A (fun GEN_PVAR_333 : A => exists i : A, @SETSPEC A GEN_PVAR_333 ((@IN A i s) /\ (~ ((f i) = (NUMERAL 0)))) i))) -> (real_of_num (@nsum A s f)) = (@sum A s (fun x : A => real_of_num (f x))).

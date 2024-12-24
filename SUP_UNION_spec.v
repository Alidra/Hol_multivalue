Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5197251 : forall s : real -> Prop, forall t : real -> Prop, ((~ (s = (@EMPTY real))) /\ ((~ (t = (@EMPTY real))) /\ ((exists b : real, forall x : real, (@IN real x s) -> real_le x b) /\ (exists c : real, forall x : real, (@IN real x t) -> real_le x c)))) -> (sup (@UNION real s t)) = (real_max (sup s) (sup t)).

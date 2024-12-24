Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5133933 : forall s : real -> Prop, (sup s) = (@ε real (fun a : real => (forall x : real, (@IN real x s) -> real_le x a) /\ (forall b : real, (forall x : real, (@IN real x s) -> real_le x b) -> real_le a b))).

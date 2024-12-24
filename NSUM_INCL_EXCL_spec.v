Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6930107 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> nat, ((@FINITE A s) /\ (@FINITE A t)) -> (Nat.add (@nsum A s f) (@nsum A t f)) = (Nat.add (@nsum A (@UNION A s t) f) (@nsum A (@INTER A s t) f)).

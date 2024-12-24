Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7053438 : forall {A : Type'}, forall f : A -> nat, forall n : nat, forall s : A -> Prop, (@FINITE A s) -> (Nat.modulo (@nsum A s f) n) = (Nat.modulo (@nsum A s (fun i : A => Nat.modulo (f i) n)) n).

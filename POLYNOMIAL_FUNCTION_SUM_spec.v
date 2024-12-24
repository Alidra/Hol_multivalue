Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7581711 : forall {A : Type'}, forall s : A -> Prop, forall p : real -> A -> real, ((@FINITE A s) /\ (forall i : A, (@IN A i s) -> polynomial_function (fun x : real => p x i))) -> polynomial_function (fun x : real => @sum A s (p x)).

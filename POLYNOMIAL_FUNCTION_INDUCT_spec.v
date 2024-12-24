Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7586372 : forall P : (real -> real) -> Prop, ((P (fun x : real => x)) /\ ((forall c : real, P (fun x : real => c)) /\ ((forall p : real -> real, forall q : real -> real, ((P p) /\ (P q)) -> P (fun x : real => real_add (p x) (q x))) /\ (forall p : real -> real, forall q : real -> real, ((P p) /\ (P q)) -> P (fun x : real => real_mul (p x) (q x)))))) -> forall p : real -> real, (polynomial_function p) -> P p.

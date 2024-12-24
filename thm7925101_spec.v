Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7925101 : forall {A : Type'} (tybit0' : (recspace (finite_sum A A)) -> Prop) (_103783' : (finite_sum A A) -> recspace (finite_sum A A)) (h1 : tybit0' = (fun a : recspace (finite_sum A A) => forall tybit0'' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = (_103783' a'')) -> tybit0'' a') -> tybit0'' a)), forall tybit0'' : (recspace (finite_sum A A)) -> Prop, (forall a : finite_sum A A, tybit0'' (_103783' a)) -> forall a : recspace (finite_sum A A), (tybit0' a) -> tybit0'' a.

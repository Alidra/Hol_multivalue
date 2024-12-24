Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1338105 : forall (P : real -> Prop), (fun P' : real -> Prop => (forall x : prod hreal hreal, P' (mk_real (treal_eq x))) = (forall x : real, P' x)) P.

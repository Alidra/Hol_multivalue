Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8356518 : forall {A B D P Q : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall e : P -> D, forall pat : Q -> D, forall q : P -> Q -> Prop, forall arg : P -> Q -> A, ((forall f : A -> B, forall a : P, forall t : Q, forall u : Q, ((p f a) /\ (((pat t) = (e a)) /\ ((q a t) /\ (((pat u) = (e a)) /\ (q a u))))) -> (arg a t) = (arg a u)) /\ (forall f : A -> B, forall a : P, forall t : Q, ((p f a) /\ ((q a t) /\ ((pat t) = (e a)))) -> forall y : A, (lt2 y (arg a t)) -> lt2 y (s a))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @_MATCH D B (e x) (fun u : D => fun v : B => exists t : Q, _GUARDED_PATTERN (@GEQ D (pat t) u) (q x t) (@GEQ B (f (arg x t)) v))).

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8094644 : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall s : P -> A, forall p : (A -> B) -> P -> Prop, forall t : (A -> B) -> P -> B, (@tailadmissible A B P lt2 p s t) = (exists P' : (A -> B) -> P -> Prop, exists G : (A -> B) -> P -> A, exists H : (A -> B) -> P -> B, (forall f : A -> B, forall a : P, forall y : A, ((P' f a) /\ (lt2 y (G f a))) -> lt2 y (s a)) /\ ((forall f : A -> B, forall g : A -> B, forall a : P, (forall z : A, (lt2 z (s a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) /\ (((G f a) = (G g a)) /\ ((H f a) = (H g a)))) /\ (forall f : A -> B, forall a : P, (p f a) -> (t f a) = (@COND B (P' f a) (f (G f a)) (H f a))))).

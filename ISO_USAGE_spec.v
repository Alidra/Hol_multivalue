Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1079952 : forall {_24632 _24635 : Type'} (g : _24632 -> _24635) (f : _24635 -> _24632), (@ExtensionalityFacts.is_inverse _24635 _24632 f g) -> (forall P : _24635 -> Prop, (forall x : _24635, P x) = (forall x : _24632, P (g x))) /\ ((forall P : _24635 -> Prop, (exists x : _24635, P x) = (exists x : _24632, P (g x))) /\ (forall a : _24635, forall b : _24632, (a = (g b)) = ((f a) = b))).

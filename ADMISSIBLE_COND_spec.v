Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8136186 : forall {_144006 _144007 _144038 _144063 P : Type'}, forall lt2 : _144007 -> _144006 -> Prop, forall p : (_144007 -> _144038) -> P -> Prop, forall P' : (_144007 -> _144038) -> P -> Prop, forall s : P -> _144006, forall h : (_144007 -> _144038) -> P -> _144063, forall k : (_144007 -> _144038) -> P -> _144063, ((@admissible _144006 _144038 _144007 Prop P lt2 p s P') /\ ((@admissible _144006 _144038 _144007 _144063 P lt2 (fun f : _144007 -> _144038 => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@admissible _144006 _144038 _144007 _144063 P lt2 (fun f : _144007 -> _144038 => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @admissible _144006 _144038 _144007 _144063 P lt2 p s (fun f : _144007 -> _144038 => fun x : P => @COND _144063 (P' f x) (h f x) (k f x)).

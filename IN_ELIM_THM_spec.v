Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184752 : forall {_83064 _83095 _83123 _83152 _83169 : Type'}, (forall P : (Prop -> _83064 -> Prop) -> Prop, forall x : _83064, (@IN _83064 x (@GSPEC _83064 (fun v : _83064 => P (@SETSPEC _83064 v)))) = (P (fun p : Prop => fun t : _83064 => p /\ (x = t)))) /\ ((forall p : _83095 -> Prop, forall x : _83095, (@IN _83095 x (@GSPEC _83095 (fun v : _83095 => exists y : _83095, @SETSPEC _83095 v (p y) y))) = (p x)) /\ ((forall P : (Prop -> _83123 -> Prop) -> Prop, forall x : _83123, (@GSPEC _83123 (fun v : _83123 => P (@SETSPEC _83123 v)) x) = (P (fun p : Prop => fun t : _83123 => p /\ (x = t)))) /\ ((forall p : _83152 -> Prop, forall x : _83152, (@GSPEC _83152 (fun v : _83152 => exists y : _83152, @SETSPEC _83152 v (p y) y) x) = (p x)) /\ (forall p : _83169 -> Prop, forall x : _83169, (@IN _83169 x (fun y : _83169 => p y)) = (p x))))).

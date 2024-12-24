Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem510983 : forall {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : _17371 -> _17370 -> Prop), ((~ ((forall x : _17371, (P x) -> forall y : _17370, Q x y) = (forall y : _17370, forall x : _17371, (P x) -> Q x y))) -> False) = ((forall x : _17371, (P x) -> forall y : _17370, Q x y) = (forall y : _17370, forall x : _17371, (P x) -> Q x y)).

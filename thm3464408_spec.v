Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3464408 : forall {_89711 _89725 : Type'}, (forall P : _89725 -> Prop, forall f : _89725 -> _89711 -> Prop, (@INTERS _89711 (@GSPEC (_89711 -> Prop) (fun GEN_PVAR_55 : _89711 -> Prop => exists x : _89725, @SETSPEC (_89711 -> Prop) GEN_PVAR_55 (P x) (f x)))) = (@GSPEC _89711 (fun GEN_PVAR_56 : _89711 => exists a : _89711, @SETSPEC _89711 GEN_PVAR_56 (forall x : _89725, (P x) -> @IN _89711 a (f x)) a))) = (forall P : _89725 -> Prop, forall f : _89725 -> _89711 -> Prop, (@INTERS _89711 (@GSPEC (_89711 -> Prop) (fun GEN_PVAR_55 : _89711 -> Prop => exists x : _89725, @SETSPEC (_89711 -> Prop) GEN_PVAR_55 (P x) (f x)))) = (@GSPEC _89711 (fun GEN_PVAR_56 : _89711 => exists a : _89711, @SETSPEC _89711 GEN_PVAR_56 (forall x : _89725, (P x) -> @IN _89711 a (f x)) a))).

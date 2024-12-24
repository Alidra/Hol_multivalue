Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8440918 : forall {_147009 _147011 _147015 : Type'} (lt2 : _147009 -> _147009 -> Prop) (s : _147015 -> _147009) (t : (_147009 -> _147011) -> _147015 -> _147011), (@superadmissible _147009 _147011 _147015 lt2 (fun f : _147009 -> _147011 => fun x : _147015 => True) s t) = (@tailadmissible _147009 _147011 _147015 lt2 (fun f : _147009 -> _147011 => fun x : _147015 => True) s t).

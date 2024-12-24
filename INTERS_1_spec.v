Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3355404 : forall {_87240 : Type'} (s : _87240 -> Prop), (@INTERS _87240 (@INSERT (_87240 -> Prop) s (@EMPTY (_87240 -> Prop)))) = s.

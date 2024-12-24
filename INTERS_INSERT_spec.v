Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3358012 : forall {_87274 : Type'} (s : _87274 -> Prop) (u : (_87274 -> Prop) -> Prop), (@INTERS _87274 (@INSERT (_87274 -> Prop) s u)) = (@INTER _87274 s (@INTERS _87274 u)).

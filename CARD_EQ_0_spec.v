Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3854502 : forall {_99911 : Type'}, forall s : _99911 -> Prop, (@FINITE _99911 s) -> ((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911)).

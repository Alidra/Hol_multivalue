Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6991992 : forall {_128422 : Type'}, forall s : _128422 -> Prop, (@FINITE _128422 s) -> (@CARD _128422 s) = (@nsum _128422 s (fun x : _128422 => NUMERAL (BIT1 0))).

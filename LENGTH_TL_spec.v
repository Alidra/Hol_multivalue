Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1203798 : forall {_28117 : Type'}, forall l : list _28117, (~ (l = (@nil _28117))) -> (@List.length _28117 (@tl _28117 l)) = (Nat.sub (@List.length _28117 l) (NUMERAL (BIT1 0))).

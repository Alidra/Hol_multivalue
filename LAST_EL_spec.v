Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1206724 : forall {_28274 : Type'}, forall l : list _28274, (~ (l = (@nil _28274))) -> (@LAST _28274 l) = (@EL _28274 (Nat.sub (@List.length _28274 l) (NUMERAL (BIT1 0))) l).

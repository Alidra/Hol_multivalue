Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1206100 : forall {_28223 : Type'} (l : list _28223), forall n : nat, (@EL _28223 n (@tl _28223 l)) = (@EL _28223 (Nat.add n (NUMERAL (BIT1 0))) l).

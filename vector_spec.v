Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8001314 : forall {A N : Type'}, forall l : list A, (@vector A N l) = (@lambda A N (fun i : nat => @EL A (Nat.sub i (NUMERAL (BIT1 0))) l)).

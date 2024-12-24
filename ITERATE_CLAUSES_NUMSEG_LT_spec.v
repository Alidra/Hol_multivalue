Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6194987 : forall {_123501 : Type'} (f : nat -> _123501), forall op : _123501 -> _123501 -> _123501, (@monoidal _123501 op) -> ((@iterate _123501 nat op (@GSPEC nat (fun GEN_PVAR_254 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_254 (Peano.lt i (NUMERAL 0)) i)) f) = (@neutral _123501 op)) /\ (forall k : nat, (@iterate _123501 nat op (@GSPEC nat (fun GEN_PVAR_255 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_255 (Peano.lt i (S k)) i)) f) = (op (@iterate _123501 nat op (@GSPEC nat (fun GEN_PVAR_256 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_256 (Peano.lt i k) i)) f) (f k))).

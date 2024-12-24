Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6198343 : forall {_123593 : Type'} (f : nat -> _123593), forall op : _123593 -> _123593 -> _123593, (@monoidal _123593 op) -> ((@iterate _123593 nat op (@GSPEC nat (fun GEN_PVAR_257 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_257 (Peano.le i (NUMERAL 0)) i)) f) = (f (NUMERAL 0))) /\ (forall k : nat, (@iterate _123593 nat op (@GSPEC nat (fun GEN_PVAR_258 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_258 (Peano.le i (S k)) i)) f) = (op (@iterate _123593 nat op (@GSPEC nat (fun GEN_PVAR_259 : nat => exists i : nat, @SETSPEC nat GEN_PVAR_259 (Peano.le i k) i)) f) (f (S k)))).

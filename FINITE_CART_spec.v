Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7989574 : forall {A N : Type'}, forall P : nat -> A -> Prop, (forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex N (@UNIV N)))) -> @FINITE A (@GSPEC A (fun GEN_PVAR_358 : A => exists x : A, @SETSPEC A GEN_PVAR_358 (P i x) x))) -> @FINITE (cart A N) (@GSPEC (cart A N) (fun GEN_PVAR_359 : cart A N => exists v : cart A N, @SETSPEC (cart A N) GEN_PVAR_359 (forall i : nat, ((Peano.le (NUMERAL (BIT1 0)) i) /\ (Peano.le i (@dimindex N (@UNIV N)))) -> P i (@dollar A N v i)) v)).

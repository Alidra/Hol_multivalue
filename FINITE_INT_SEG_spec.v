Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5710351 : (forall l : int, forall r : int, @FINITE int (@GSPEC int (fun GEN_PVAR_233 : int => exists x : int, @SETSPEC int GEN_PVAR_233 ((int_le l x) /\ (int_le x r)) x))) /\ ((forall l : int, forall r : int, @FINITE int (@GSPEC int (fun GEN_PVAR_234 : int => exists x : int, @SETSPEC int GEN_PVAR_234 ((int_le l x) /\ (int_lt x r)) x))) /\ ((forall l : int, forall r : int, @FINITE int (@GSPEC int (fun GEN_PVAR_235 : int => exists x : int, @SETSPEC int GEN_PVAR_235 ((int_lt l x) /\ (int_le x r)) x))) /\ (forall l : int, forall r : int, @FINITE int (@GSPEC int (fun GEN_PVAR_236 : int => exists x : int, @SETSPEC int GEN_PVAR_236 ((int_lt l x) /\ (int_lt x r)) x))))).

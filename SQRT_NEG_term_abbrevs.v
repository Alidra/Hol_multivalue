Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False).
Definition term6 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) x0.
Definition term54 (x0 : real) := @eq real (real_neg (real_sgn x0)).
Definition term43 := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0)))).
Definition term8 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term38 (x0 : real) := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term49 (x0 : real) := @eq real (real_pow (real_neg (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term37 (x0 : real) := real_pow (real_neg (sqrt x0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term28 := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term25 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1.
Definition term5 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True.
Definition term9 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term32 (x0 : real) := real_neg (real_sgn (sqrt x0)).
Definition term41 := Coq.Arith.PeanoNat.Nat.Even (BIT0 (BIT1 0)).
Definition term56 (x0 : real) := sqrt (real_neg x0).
Definition term21 := forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term46 (x0 : real) := @COND real True (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term52 (x0 : real) := ((real_neg (real_sgn (sqrt x0))) = (real_neg (real_sgn x0))) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term45 (x0 : real) := @COND real (Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term29 (x0 : real) := (((real_sgn (real_neg (sqrt x0))) = (real_sgn (real_neg x0))) /\ ((real_pow (real_neg (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_neg x0)))) -> (sqrt (real_neg x0)) = (real_neg (sqrt x0)).
Definition term1 (x0 : real) := ((real_sgn (sqrt x0)) = (real_sgn x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_neg y0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow y0 y1) (real_neg (real_pow y0 y1)))) x0.
Definition term35 (x0 : real) := and ((real_sgn (real_neg (sqrt x0))) = (real_sgn (real_neg x0))).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0) x1.
Definition term20 (x0 : real) := real_neg (real_sgn x0).
Definition term50 (x0 : real) := @eq real (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term14 (x0 : real) := forall y0 : nat, (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term18 (x0 : real) := (fun y0 : real => (real_sgn (real_neg y0)) = (real_neg (real_sgn y0))) x0.
Definition term51 (x0 : real) := ((real_sgn (real_neg (sqrt x0))) = (real_sgn (real_neg x0))) /\ ((real_pow (real_neg (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_neg x0))).
Definition term0 (x0 : real) := (fun y0 : real => ((real_sgn (sqrt y0)) = (real_sgn y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) x0.
Definition term17 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term55 (x0 : real) := @eq real (real_abs x0).
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) x0.
Definition term34 (x0 : real) := @eq real (real_neg (real_sgn (sqrt x0))).
Definition term23 (x0 : real) := forall y0 : real, (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0.
Definition term11 (x0 : real) := (fun y0 : real => (real_abs (real_neg y0)) = (real_abs y0)) x0.
Definition term39 := NUMERAL (BIT0 (BIT1 0)).
Definition term15 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1.
Definition term16 (x0 : real) (x1 : nat) := real_pow (real_neg x0) x1.
Definition term53 (x0 : real) := real_sgn (sqrt x0).
Definition term44 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term7 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (BIT0 x0).
Definition term30 (x0 : real) := real_neg (sqrt x0).
Definition term19 (x0 : real) := real_sgn (real_neg x0).
Definition term40 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0))).
Definition term42 := BIT0 (BIT1 0).
Definition term2 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False))).
Definition term48 (x0 : real) := @COND real True (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term36 (x0 : real) := and ((real_neg (real_sgn (sqrt x0))) = (real_neg (real_sgn x0))).
Definition term57 := forall y0 : real, (sqrt (real_neg y0)) = (real_neg (sqrt y0)).
Definition term12 (x0 : real) := real_abs (real_neg x0).
Definition term47 (x0 : real) := real_neg (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term26 (x0 : real) (x1 : real) := ((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1)).
Definition term31 (x0 : real) := real_sgn (real_neg (sqrt x0)).
Definition term27 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> (sqrt x0) = x1.
Definition term10 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (NUMERAL x0).
Definition term33 (x0 : real) := @eq real (real_sgn (real_neg (sqrt x0))).
Definition term3 := ((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False)).
